"""LLM-guided synthesis with verification-as-ranking and a CEGIS-style repair loop (paper: LLM-Guided Synthesis)."""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Optional, Protocol

from .checker import Checker, Diag
from .contracts import DEFAULT_CONTRACTS, Contract, check_contracts, trace_safety
from .effects import Cap, Effect
from .interp import Interpreter, RuntimeViolation, TraceEntry
from .sim import Handler, HandlerError, SimEnv, SimHandler
from .syntax import Expr, ParseError, Ty, parse_program

W_TC, W_CV, W_RP, W_COST = 10.0, 5.0, 3.0, 1.0  # score weights from the paper (Multi-Candidate Generation and Ranking)
K_CANDIDATES, N_MAX = 5, 3


@dataclass(frozen=True)
class Spec:
    """Synthesis specification S = (kappa, eps_max, Phi)."""
    caps: frozenset[Cap]
    max_effect: Effect
    contracts: dict[str, Contract] = field(default_factory=lambda: dict(DEFAULT_CONTRACTS))
    incident: str = ""


class LLMClient(Protocol):
    """The only role an LLM plays: propose programs (JSON ASTs) and repair them from feedback."""
    def generate(self, spec: Spec, k: int) -> list[str]: ...
    def repair(self, spec: Spec, program: str, report: list[str], hint: str) -> str: ...


@dataclass
class Verdict:
    source: str
    expr: Optional[Expr] = None
    ty: Optional[Ty] = None
    effect: Optional[Effect] = None
    diags: list[Diag] = field(default_factory=list)
    violations: list[str] = field(default_factory=list)  # contract violations and replay failures
    replay_trace: list[TraceEntry] = field(default_factory=list)
    replay_healthy: bool = False
    contract_score: float = 0.0

    @property
    def accepted(self) -> bool:
        return self.expr is not None and not self.diags and not self.violations

    @property
    def report(self) -> list[str]:
        return [str(d) for d in self.diags] + self.violations

    @property
    def score(self) -> float:
        cost = 0.1 * len(self.replay_trace) + (0.5 * self.effect.risk if self.effect else 0)
        return (W_TC * (not self.diags) + W_CV * self.contract_score
                + W_RP * self.replay_healthy - W_COST * cost)


def verify(spec: Spec, env: SimEnv, source: str,
           make_handler: Callable[[SimEnv], Handler] = SimHandler) -> Verdict:
    """Static check, then replay on a snapshot of the world and check the runtime contracts."""
    try:
        expr = parse_program(source)
    except ParseError as ex:
        return Verdict(source, diags=[Diag("E-PARSE", str(ex), "<program>")])
    res = Checker(spec.caps, spec.max_effect).check_program(expr)
    v = Verdict(source, expr, res.ty, res.effect, res.diags)
    if res.diags:
        return v
    world = env.snapshot()
    it = Interpreter(make_handler(world), spec.caps)
    try:
        it.run(expr)
    except (RuntimeViolation, HandlerError) as ex:
        v.violations.append(f"replay failure: {ex}")
    v.replay_trace, v.replay_healthy = it.trace, world.healthy
    found = check_contracts(it.trace, spec.contracts)
    v.violations += [m for msgs in found.values() for m in msgs]
    v.contract_score = sum(not m for m in found.values()) / max(len(found), 1)
    return v


HINTS = {
    "E-PARSE": "emit a well-formed JSON AST using only known nodes and capabilities",
    "E-CAP": "that capability is not granted; use a granted capability or escalate via require_approval",
    "E-APPROVAL": "wrap the Disruptive expression in require_approval, or choose a lower-risk action",
    "E-RISK": "the effect exceeds the permitted maximum; replace the high-risk action",
    "E-LEAK": "thread the rollback token through every path: return it or rollback it",
    "E-AFFINE": "the token may be consumed twice; consume it at most once on every path",
    "phi_causal": "observe, hypothesize and validate before act, on the same target",
    "phi_postcheck": "observe the target again after act to confirm recovery",
}


def hint_for(report: list[str]) -> str:
    """Step 2 of the repair loop: turn the first failure into a natural-language hint."""
    for line in report:
        key = line[1:line.index("]")] if line.startswith("[") else line.split(":")[0]
        if key in HINTS:
            return HINTS[key]
    return "fix the reported problem"


@dataclass
class SynthResult:
    accepted: Optional[Verdict]
    rounds: int
    history: list[list[Verdict]]


def synthesize(llm: LLMClient, spec: Spec, env: SimEnv, k: int = K_CANDIDATES, n_max: int = N_MAX,
               log: Callable[[str], None] = lambda s: None) -> SynthResult:
    """Generate k candidates; while none verifies, repair each from its own feedback (<= n_max rounds)."""
    sources = llm.generate(spec, k)
    history: list[list[Verdict]] = []
    for rnd in range(n_max + 1):
        log(f"\n=== round {rnd}: {'initial candidates' if rnd == 0 else 'repaired candidates'} ===")
        verdicts = [verify(spec, env, s) for s in sources]
        history.append(verdicts)
        for i, v in enumerate(verdicts):
            log(f"-- candidate {i}: {'ACCEPTED' if v.accepted else 'REJECTED'}"
                + (f"  type={v.ty} effect={v.effect} score={v.score:.2f}" if v.expr else ""))
            for line in v.report:
                log(f"     {line}")
        accepted = [v for v in verdicts if v.accepted]
        if accepted:
            best = max(accepted, key=lambda v: v.score)  # first of equals wins
            log(f"\n{len(accepted)} candidate(s) verified; highest score {best.score:.2f} selected.")
            return SynthResult(best, rnd, history)
        if rnd == n_max:
            break
        log("no candidate verified -> repair: failure report + hint go back to the LLM")
        sources = []
        for i, v in enumerate(verdicts):
            hint = hint_for(v.report)
            log(f"   candidate {i} hint: {hint}")
            sources.append(llm.repair(spec, v.source, v.report, hint))
    return SynthResult(None, n_max, history)


def execute(spec: Spec, env: SimEnv, program: Expr,
            approver: Callable[[Expr], bool] = lambda e: False) -> tuple[object, list[TraceEntry], list[str]]:
    """Run a verified program under the live handler (same program, different handler)."""
    it = Interpreter(SimHandler(env), spec.caps, approver)
    value = it.run(program)
    return value, it.trace, trace_safety(it.trace, spec.caps)

