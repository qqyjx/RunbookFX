"""End-to-end demo:  python -m runbookfx.demo

Synthetic incident: high p99 latency of `api` caused by a full log volume. A deterministic mock LLM
proposes runbooks, the checker + replay reject unsafe ones with feedback, and the first verified
runbook is executed in the simulator.
"""
from __future__ import annotations

from typing import Any

from .effects import Cap, Effect, Risk
from .interp import TraceEntry
from .mock_llm import MockLLM
from .sim import SimEnv, SimHandler
from .synth import Spec, execute, synthesize
from .syntax import show

GRANTED = frozenset({Cap.READ_LOGS, Cap.READ_METRICS, Cap.READ_TRACES, Cap.LOG_ROTATE, Cap.PURGE_VOLUME})


def make_spec() -> Spec:
    """kappa grants reads, log rotation and (dangerous) volume purge; eps_max = SafeChange, 1 rollback."""
    return Spec(GRANTED, Effect(Risk.SAFE_CHANGE, frozenset(Cap), 1),
                incident="p99 latency of service 'api' above SLO (synthetic toy incident)")


class UnhelpfulHandler(SimHandler):
    """A different well-formed handler: the action 'works' but metrics never improve."""

    def observe(self, cap: Cap, target: str, key: str) -> Any:
        v = super().observe(cap, target, key)
        return 97.0 if key == "disk_used_pct" and self.env.disk_used_pct < 95 else v


def show_trace(trace: list[TraceEntry]) -> None:
    for t in trace:
        print("   ", t)


def main() -> None:
    spec, env = make_spec(), SimEnv()
    print("RunbookFX toy demo (everything below is simulated and synthetic)")
    print(f"incident : {spec.incident}")
    print(f"granted  : {sorted(c.value for c in spec.caps)}")
    print(f"eps_max  : risk<={spec.max_effect.risk.name}, rollback obligations<={spec.max_effect.n}")
    print(f"world    : {env.summary()}")

    result = synthesize(MockLLM(), spec, env, log=print)
    if result.accepted is None:
        print("\nno verified runbook within the round bound; nothing is executed (abstain).")
        return
    v = result.accepted
    print(f"\n=== accepted runbook (round {result.rounds}) ===")
    print(show(v.expr))
    print(f"type   : {v.ty}\neffect : {v.effect}   well-formed (I1-I4): {v.effect.wf}")

    print("\n=== execute under the live handler ===")
    value, trace, problems = execute(spec, env, v.expr)
    show_trace(trace)
    print(f"result : {value}")
    print(f"world  : {env.summary()}   healthy={env.healthy}")
    print(f"trace safety problems: {problems or 'none'}")

    print("\n=== same program, different handler (recovery check fails -> rollback) ===")
    from .interp import Interpreter
    other = SimEnv()
    it = Interpreter(UnhelpfulHandler(other), spec.caps)
    value = it.run(v.expr)
    show_trace(it.trace)
    print(f"result : {value}")
    print(f"world  : {other.summary()}   (disk restored by rollback)")


if __name__ == "__main__":
    main()
