"""Deterministic mock LLM. No network, no randomness; implements the `LLMClient` protocol.

It drafts programs from a small `Plan` and repairs a plan by reading the first line of the
feedback report. Round 0 deliberately contains unsafe or flawed candidates.
"""
from __future__ import annotations

import json
from dataclasses import dataclass, replace

from .effects import Cap
from .synth import Spec
from .syntax import (Act, Branch, Ctor, Expr, Guard, Hypothesize, Let, LetPair, Lit, Observe,
                     RequireApproval, Rollback, Threshold, Validate, Var, to_json)

HOST = "api-host"


@dataclass(frozen=True)
class Plan:
    diagnose: bool = True      # observe + hypothesize before acting
    validate: bool = True      # fresh observation checked by `validate` in the guard
    cap: Cap = Cap.LOG_ROTATE  # mitigation capability
    gate: bool = False         # wrap in require_approval
    tok_mode: str = "ok"          # "ok" | "leak" | "double"
    traces: bool = False       # extra read_traces evidence (costs one more step)


def _target(cap: Cap) -> tuple[str, str, str, float]:
    """(target, action, post-check series, threshold) of a mitigation capability."""
    if cap is Cap.KUBECTL_RESTART:
        return "api", "restart", "p99_latency_ms", 500.0
    return HOST, "rotate" if cap is Cap.LOG_ROTATE else "purge", "disk_used_pct", 80.0


def build(p: Plan) -> Expr:
    """Draft the runbook for a plan (the 'LLM output')."""
    tgt, action, series, limit = _target(p.cap)
    recovered = Threshold(Observe(Cap.READ_METRICS, tgt, series), "<", limit)
    if p.tok_mode == "leak":
        arms = (("true", Ctor("Success", Var("res"))), ("false", Ctor("Failure", Lit("not recovered"))))
    else:
        undo = Rollback(Var("tok"))
        if p.tok_mode == "double":
            undo = Let("_", undo, Rollback(Var("tok")))
        arms = (("true", Ctor("Success", Var("tok"))),
                ("false", Let("_", undo, Ctor("Failure", Lit("not recovered")))))
    body: Expr = LetPair("res", "tok", Act(p.cap, tgt, action), Branch(recovered, arms))
    if not p.diagnose:
        prog: Expr = Guard(Lit(True), body)
    else:
        disk = Observe(Cap.READ_METRICS, HOST, "disk_used_pct")
        evidence = [Var("m"), Var("l")] + ([Var("t")] if p.traces else [])
        cond: Expr = Threshold(Var("m"), ">", 90.0)
        if p.validate:
            cond = Validate(Var("h"), Threshold(disk, ">", 90.0))
        prog = Guard(cond, body)
        prog = Let("h", Hypothesize("log_volume_full", tuple(evidence)), prog)
        if p.traces:
            prog = Let("t", Observe(Cap.READ_TRACES, "api", "slowest_dependency"), prog)
        prog = Let("l", Observe(Cap.READ_LOGS, HOST, "errors"), prog)
        prog = Let("m", disk, prog)
    return RequireApproval(prog) if p.gate else prog


class MockLLM:
    """Scripted proposals plus rule-based repair; remembers which plan produced which program."""

    def __init__(self) -> None:
        self._plans: dict[str, Plan] = {}

    def _emit(self, plan: Plan) -> str:
        text = json.dumps(to_json(build(plan)), sort_keys=True)
        self._plans[text] = plan
        return text

    def generate(self, spec: Spec, k: int) -> list[str]:
        drafts = [
            Plan(diagnose=False, cap=Cap.KUBECTL_RESTART),  # act first, capability not granted
            Plan(cap=Cap.PURGE_VOLUME),  # Disruptive, no approval gate
            Plan(tok_mode="leak", traces=True),  # rollback token never consumed
            Plan(validate=False),  # skips validate (contract)
            Plan(tok_mode="double"),  # token consumed twice
        ]
        return [self._emit(p) for p in drafts[:k]]

    def repair(self, spec: Spec, program: str, report: list[str], hint: str) -> str:
        plan = self._plans.get(program, Plan())
        first = report[0] if report else ""
        if first.startswith("[E-CAP]") or first.startswith("[E-RISK]"):
            plan = replace(plan, cap=Cap.LOG_ROTATE, gate=False)       # fall back to a reversible action
        elif first.startswith("[E-APPROVAL]"):
            plan = replace(plan, gate=True)
        elif first.startswith(("[E-LEAK]", "[E-AFFINE]")):
            plan = replace(plan, tok_mode="ok")
        elif first.startswith("phi_causal"):
            plan = replace(plan, diagnose=True, validate=True)
        return self._emit(plan)
