"""Runtime contracts: predicates over the audit trace, checked on the replay run (paper: LLM-Guided Synthesis, Runtime contracts)."""
from __future__ import annotations

from typing import Callable

from .interp import TraceEntry

Contract = Callable[[list[TraceEntry]], list[str]]


def phi_causal(trace: list[TraceEntry]) -> list[str]:
    """Every act is preceded by an observe on the same target and a hypothesize/validate(true) pair."""
    out = []
    for i, t in enumerate(trace):
        if t.kind != "act":
            continue
        before = trace[:i]
        if not any(b.kind == "observe" and b.target == t.target for b in before):
            out.append(f"phi_causal: act[{t.cap.value}] on '{t.target}' (step {t.step}) has no "
                       f"preceding observe on '{t.target}'")
        hyp = [b.step for b in before if b.kind == "hypothesize"]
        if not any(b.kind == "validate" and b.detail.endswith("True") and hyp and b.step > hyp[0]
                   for b in before):
            out.append(f"phi_causal: act[{t.cap.value}] on '{t.target}' (step {t.step}) is not "
                       "preceded by hypothesize followed by a successful validate")
    return out


def phi_postcheck(trace: list[TraceEntry]) -> list[str]:
    """Every act is followed by an observe on the same target (recovery check)."""
    return [f"phi_postcheck: act[{t.cap.value}] on '{t.target}' (step {t.step}) is never re-observed"
            for i, t in enumerate(trace) if t.kind == "act"
            and not any(a.kind == "observe" and a.target == t.target for a in trace[i + 1:])]


DEFAULT_CONTRACTS: dict[str, Contract] = {"phi_causal": phi_causal, "phi_postcheck": phi_postcheck}


def check_contracts(trace: list[TraceEntry], contracts: dict[str, Contract] = DEFAULT_CONTRACTS
                    ) -> dict[str, list[str]]:
    """Violations per contract name (empty list = satisfied)."""
    return {name: c(trace) for name, c in contracts.items()}


def trace_safety(trace: list[TraceEntry], caps: frozenset) -> list[str]:
    """Trace-level view of the safety theorems: no unauthorized action; at most one rollback per act."""
    out = [f"unauthorized {t.kind}[{t.cap.value}] at step {t.step}"
           for t in trace if t.cap is not None and t.cap not in caps]
    acts = sum(t.kind == "act" for t in trace)
    rolls = sum(t.kind == "rollback" for t in trace)
    if rolls > acts:
        out.append(f"{rolls} rollbacks for {acts} acts (a token was consumed twice)")
    return out
