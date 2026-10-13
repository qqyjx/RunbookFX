"""Type-and-effect checker:  Gamma_u; Gamma_a; kappa |- e : tau |> eps  (paper: Type and Effect System).

Differences from the declarative rules are listed in README ("Simplifications"). Affine
variables (rollback tokens) are threaded through the derivation instead of split up front;
an unconsumed token is an error, as in the paper's synthesis pipeline (Affine Rollback Resource Management).
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional

from .effects import BOT, Cap, Effect, Risk
from .syntax import (ACT_RESULT, BOOL, ERR, HYP, LOGS, METRIC, OBSERVE_TYPE, OUTCOME, STRING, TOKEN,
                     TRACES, UNIT, Act, Branch, Ctor, Expr, Guard, Hypothesize, Let, LetPair, Lit,
                     MkPair, Observe, OptTy, PairTy, RequireApproval, Retry, Rollback, Threshold, Ty,
                     Validate, Var, show)


@dataclass(frozen=True)
class Diag:
    """A localized verification failure: code, message, and the offending site."""
    code: str
    message: str
    site: str

    def __str__(self) -> str:
        return f"[{self.code}] {self.message} (at: {self.site})"


@dataclass
class Result:
    ty: Ty
    effect: Effect
    diags: list[Diag] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return not self.diags


@dataclass(frozen=True)
class Live:
    """Affine variables still available: on some path (maybe) / on every path (definite)."""
    maybe: frozenset[str] = frozenset()
    definite: frozenset[str] = frozenset()

    def add(self, x: str) -> "Live":
        return Live(self.maybe | {x}, self.definite | {x})

    def drop(self, x: str) -> "Live":
        return Live(self.maybe - {x}, self.definite - {x})

    def merge(self, other: "Live") -> "Live":
        return Live(self.maybe | other.maybe, self.definite & other.definite)


@dataclass(frozen=True)
class Env:
    gu: dict  # unrestricted bindings: name -> type
    aff: frozenset  # names of affine (RollbackToken) bindings


class Checker:
    """Checks a program against capabilities kappa and an optional maximum effect eps_max."""

    def __init__(self, caps: frozenset[Cap], max_effect: Optional[Effect] = None):
        self.caps, self.max_effect = caps, max_effect
        self.diags: list[Diag] = []

    def check_program(self, e: Expr) -> Result:
        self.diags = []
        ty, eff, _ = self._infer(e, Env({}, frozenset()), Live())
        if eff.risk == Risk.DISRUPTIVE and not isinstance(e, RequireApproval):
            self._err("E-APPROVAL", "top-level effect is Disruptive but the program is not "
                      "wrapped in require_approval", "<program>")
        if not eff.wf:
            self._err("E-WF", "ill-formed effect grade: " + "; ".join(eff.violations()), "<program>")
        if self.max_effect is not None and not eff.leq(self.max_effect):
            self._err("E-RISK", f"effect {eff} exceeds the permitted maximum: "
                      + "; ".join(eff.excess(self.max_effect)), "<program>")
        return Result(ty, eff, list(self.diags))

    # -- helpers ---------------------------------------------------------------------------------
    def _err(self, code: str, msg: str, at: "Expr | str") -> None:
        site = at if isinstance(at, str) else show(at).split("\n")[0]
        self.diags.append(Diag(code, msg, site if len(site) < 70 else site[:67] + "..."))

    def _expect(self, got: Ty, want: Ty, what: str, at: Expr) -> None:
        if got != ERR and got != want:
            self._err("E-TYPE", f"{what}: expected {want}, got {got}", at)

    def _bind(self, env: Env, live: Live, name: str, ty: Ty) -> tuple[Env, Live]:
        if ty == TOKEN:
            return Env(env.gu, env.aff | {name}), live.add(name)
        return Env({**env.gu, name: ty}, env.aff), live

    def _scope_end(self, names: list[str], tys: list[Ty], live: Live, at: Expr) -> Live:
        for n, t in zip(names, tys):
            if t == TOKEN:
                if n in live.maybe:
                    self._err("E-LEAK", f"rollback token '{n}' is not consumed on every path "
                              "(rollback it or return it)", at)
                live = live.drop(n)
        return live

    # -- the typing rules --------------------------------------------------------------------------
    def _infer(self, e: Expr, env: Env, live: Live) -> tuple[Ty, Effect, Live]:
        if isinstance(e, Lit):
            v = e.value
            ty = UNIT if v is None else BOOL if isinstance(v, bool) else STRING if isinstance(v, str) else "Number"
            return ty, BOT, live
        if isinstance(e, Var):
            if e.name in env.aff:
                if e.name not in live.definite:
                    self._err("E-AFFINE", f"rollback token '{e.name}' is used after it may already "
                              "have been consumed", e)
                return TOKEN, BOT, live.drop(e.name)
            if e.name in env.gu:
                return env.gu[e.name], BOT, live
            self._err("E-SCOPE", f"unbound variable '{e.name}'", e)
            return ERR, BOT, live
        if isinstance(e, Let):
            t1, e1, l1 = self._infer(e.bound, env, live)
            env2, l1 = self._bind(env, l1, e.name, t1)
            t2, e2, l2 = self._infer(e.body, env2, l1)
            return t2, e1.join(e2), self._scope_end([e.name], [t1], l2, e)
        if isinstance(e, LetPair):
            t1, e1, l1 = self._infer(e.bound, env, live)
            if isinstance(t1, PairTy):
                ta, tb = t1.fst, t1.snd
            else:
                if t1 != ERR:
                    self._err("E-TYPE", f"let-pair: expected a pair, got {t1}", e)
                ta = tb = ERR
            env2, l1 = self._bind(env, l1, e.fst, ta)
            env2, l1 = self._bind(env2, l1, e.snd, tb)
            t2, e2, l2 = self._infer(e.body, env2, l1)
            return t2, e1.join(e2), self._scope_end([e.fst, e.snd], [ta, tb], l2, e)
        if isinstance(e, MkPair):
            ta, ea, l1 = self._infer(e.fst, env, live)
            tb, eb, l2 = self._infer(e.snd, env, l1)
            return PairTy(ta, tb), ea.join(eb), l2
        if isinstance(e, Observe):
            ty = OBSERVE_TYPE.get(e.cap)
            if ty is None:
                self._err("E-TYPE", f"observe needs a read capability, got {e.cap.value}", e)
                ty = ERR
            if e.cap not in self.caps:
                self._err("E-CAP", f"capability {e.cap.value} is not granted", e)
            return ty, Effect(Risk.READ_ONLY, frozenset({e.cap}), 0), live
        if isinstance(e, Act):
            if e.cap.risk == Risk.READ_ONLY:
                self._err("E-TYPE", f"act needs a mutation capability, got {e.cap.value}", e)
            if e.cap not in self.caps:
                self._err("E-CAP", f"capability {e.cap.value} is not granted", e)
            return PairTy(ACT_RESULT, TOKEN), Effect(e.cap.risk, frozenset({e.cap}), 1), live
        if isinstance(e, Threshold):
            t, eff, l1 = self._infer(e.arg, env, live)
            self._expect(t, METRIC, "threshold test", e)
            if e.op not in ("<", ">"):
                self._err("E-TYPE", f"unknown comparison '{e.op}'", e)
            return BOOL, eff, l1
        if isinstance(e, Guard):
            tc, ec, l1 = self._infer(e.cond, env, live)
            self._expect(tc, BOOL, "guard condition", e)
            tb, eb, l2 = self._infer(e.body, env, l1)
            return OptTy(tb), ec.join(eb), l2.merge(l1)  # the body may be skipped
        if isinstance(e, Branch):
            ts, es, l1 = self._infer(e.scrut, env, live)
            self._expect(ts, BOOL, "branch scrutinee", e)
            if sorted(p for p, _ in e.arms) != ["false", "true"]:
                self._err("E-TYPE", "branch must have exactly the arms 'true' and 'false'", e)
            ty: Ty = ERR
            alt: Optional[Effect] = None
            out: Optional[Live] = None
            for _, arm in e.arms:
                ta, ea, la = self._infer(arm, env, l1)
                if ty != ERR and ta != ERR and ta != ty:
                    self._err("E-TYPE", f"branch arms differ: {ty} vs {ta}", e)
                ty = ty if ty != ERR else ta
                alt = ea if alt is None else alt.alt(ea)
                out = la if out is None else out.merge(la)
            return ty, es.join(alt or BOT), out or l1
        if isinstance(e, Retry):
            if e.n < 1:
                self._err("E-TYPE", "retry bound must be at least 1", e)
            tb, eb, _ = self._infer(e.body, Env(env.gu, frozenset()), Live())  # empty affine context
            return tb, eb.scale(max(e.n, 1)), live
        if isinstance(e, Rollback):
            t, eff, l1 = self._infer(e.token, env, live)
            self._expect(t, TOKEN, "rollback argument", e)
            return UNIT, eff.join(Effect(Risk.SAFE_CHANGE, frozenset(), 0)), l1
        if isinstance(e, RequireApproval):
            t, eff, l1 = self._infer(e.body, env, live)
            if eff.risk != Risk.DISRUPTIVE:
                self._err("E-APPROVAL", "require_approval wraps a non-Disruptive expression "
                          f"(risk {eff.risk.name})", e)
            return t, eff, l1
        if isinstance(e, Hypothesize):
            eff = BOT
            for ev in e.evidence:
                t, ee, live = self._infer(ev, env, live)
                if t not in (LOGS, METRIC, TRACES, ERR):
                    self._err("E-TYPE", f"hypothesize: evidence must be telemetry, got {t}", e)
                eff = eff.join(ee)
            return HYP, eff, live
        if isinstance(e, Validate):
            th, eh, l1 = self._infer(e.hyp, env, live)
            tc, ec, l2 = self._infer(e.check, env, l1)
            self._expect(th, HYP, "validate: first argument", e)
            self._expect(tc, BOOL, "validate: check", e)
            return BOOL, eh.join(ec), l2
        if isinstance(e, Ctor):
            if e.tag not in ("Success", "Failure"):
                self._err("E-TYPE", f"unknown constructor '{e.tag}'", e)
            _, eff, l1 = self._infer(e.arg, env, live)
            return OUTCOME, eff, l1
        raise TypeError(e)
