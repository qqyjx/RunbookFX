"""Big-step interpreter with an audit trace (paper: Operational Semantics, Audit Trace)."""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable, Optional

from .effects import Cap
from .sim import Handler, TransientError
from .syntax import (Act, Branch, Ctor, Expr, Guard, Hypothesize, Let, LetPair, Lit, MkPair, Observe,
                     RequireApproval, Retry, Rollback, Threshold, Validate, Var)


class RuntimeViolation(RuntimeError):
    """A safety property the type system rules out was about to be broken at run time."""


class UnauthorizedAction(RuntimeViolation):
    pass


class TokenError(RuntimeViolation):
    pass


class ApprovalDenied(RuntimeViolation):
    pass


@dataclass
class Token:
    """Affine rollback token holding the compensating action's data."""
    cap: Cap
    target: str
    undo: Any
    consumed: bool = False

    def __repr__(self) -> str:
        return f"<token {self.cap.value}@{self.target} consumed={self.consumed}>"


@dataclass
class TraceEntry:
    step: int
    kind: str  # observe | act | rollback | hypothesize | validate | approve
    cap: Optional[Cap]
    target: str
    detail: str

    def __str__(self) -> str:
        c = f"[{self.cap.value}] " if self.cap else ""
        return f"{self.step:>2} {self.kind:<12} {c}{self.target} {self.detail}".rstrip()


class Interpreter:
    """Runs a program under a handler; records every effectful step in `trace`."""

    def __init__(self, handler: Handler, caps: frozenset[Cap],
                 approver: Callable[[Expr], bool] = lambda e: False):
        self.h, self.caps, self.approver = handler, caps, approver
        self.trace: list[TraceEntry] = []

    def _log(self, kind: str, cap: Optional[Cap], target: str, detail: str = "") -> None:
        self.trace.append(TraceEntry(len(self.trace), kind, cap, target, detail))

    def run(self, e: Expr, env: Optional[dict] = None) -> Any:
        env = env or {}
        if isinstance(e, Lit):
            return e.value
        if isinstance(e, Var):
            return env[e.name]
        if isinstance(e, Let):
            return self.run(e.body, {**env, e.name: self.run(e.bound, env)})
        if isinstance(e, LetPair):
            a, b = self.run(e.bound, env)
            return self.run(e.body, {**env, e.fst: a, e.snd: b})
        if isinstance(e, MkPair):
            return (self.run(e.fst, env), self.run(e.snd, env))
        if isinstance(e, Observe):
            self._need(e.cap)
            v = self.h.observe(e.cap, e.target, e.key)
            self._log("observe", e.cap, e.target, f"{e.key} -> {v if not isinstance(v, list) else f'{len(v)} lines'}")
            return v
        if isinstance(e, Act):
            self._need(e.cap)
            res, undo = self.h.act(e.cap, e.target, e.action)
            self._log("act", e.cap, e.target, f"{e.action} -> {res}")
            return (res, Token(e.cap, e.target, undo))
        if isinstance(e, Threshold):
            v = self.run(e.arg, env)
            return v < e.value if e.op == "<" else v > e.value
        if isinstance(e, Guard):
            return ("Some", self.run(e.body, env)) if self.run(e.cond, env) else None
        if isinstance(e, Branch):
            s = self.run(e.scrut, env)
            return self.run(dict(e.arms)["true" if s else "false"], env)
        if isinstance(e, Retry):
            for attempt in range(e.n):
                try:
                    return self.run(e.body, env)
                except TransientError:
                    if attempt == e.n - 1:
                        raise
        if isinstance(e, Rollback):
            tok = self.run(e.token, env)
            if tok.consumed:
                raise TokenError(f"rollback token for {tok.cap.value} on {tok.target} used twice")
            tok.consumed = True
            self.h.rollback(tok.undo)
            self._log("rollback", tok.cap, tok.target, "restored")
            return None
        if isinstance(e, RequireApproval):
            ok = self.approver(e.body)
            self._log("approve", None, "", "granted" if ok else "denied")
            if not ok:
                raise ApprovalDenied("approval gate denied")
            return self.run(e.body, env)
        if isinstance(e, Hypothesize):
            for ev in e.evidence:
                self.run(ev, env)
            self._log("hypothesize", None, "", e.label)
            return ("hyp", e.label)
        if isinstance(e, Validate):
            _, label = self.run(e.hyp, env)
            ok = bool(self.run(e.check, env))
            self._log("validate", None, "", f"{label}: {ok}")
            return ok
        if isinstance(e, Ctor):
            return (e.tag, self.run(e.arg, env))
        raise TypeError(e)

    def _need(self, cap: Cap) -> None:
        if cap not in self.caps:
            raise UnauthorizedAction(f"{cap.value} not granted")
