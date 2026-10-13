"""Core syntax of the RunbookFX DSL (paper: Core Syntax figure, monomorphic fragment): AST, JSON codec, printer.

The mock LLM emits programs as JSON ASTs, as in the paper (Synthesis Representation); `from_json` rejects malformed ones.
"""
from __future__ import annotations

import json
from dataclasses import dataclass, fields
from typing import Any, Union

from .effects import Cap

# ---- types -------------------------------------------------------------------------------------
UNIT, BOOL, STRING = "Unit", "Bool", "String"
LOGS, METRIC, TRACES = "LogStream", "MetricSeries", "TraceGraph"
HYP, ACT_RESULT, OUTCOME, TOKEN = "Hypothesis", "ActResult", "Outcome", "RollbackToken"
ERR = "<error>"  # absorbing type after a reported error; unifies with everything


@dataclass(frozen=True)
class PairTy:
    fst: "Ty"
    snd: "Ty"

    def __str__(self) -> str:
        return f"({self.fst} x {self.snd})"


@dataclass(frozen=True)
class OptTy:
    inner: "Ty"

    def __str__(self) -> str:
        return f"Option {self.inner}"


Ty = Union[str, PairTy, OptTy]
OBSERVE_TYPE = {Cap.READ_LOGS: LOGS, Cap.READ_METRICS: METRIC, Cap.READ_TRACES: TRACES}


# ---- expressions -------------------------------------------------------------------------------
class Expr:
    """Base class of all AST nodes."""


@dataclass(frozen=True)
class Lit(Expr):
    value: Union[None, bool, str, int, float]


@dataclass(frozen=True)
class Var(Expr):
    name: str


@dataclass(frozen=True)
class Let(Expr):
    name: str
    bound: Expr
    body: Expr


@dataclass(frozen=True)
class LetPair(Expr):
    """let (fst, snd) = bound in body; destructures the pair returned by act."""
    fst: str
    snd: str
    bound: Expr
    body: Expr


@dataclass(frozen=True)
class MkPair(Expr):
    fst: Expr
    snd: Expr


@dataclass(frozen=True)
class Observe(Expr):
    """observe_c: read-only telemetry query on `target` (`key` selects the series)."""
    cap: Cap
    target: str
    key: str


@dataclass(frozen=True)
class Act(Expr):
    """act_c: state-changing operation; returns ActResult x RollbackToken."""
    cap: Cap
    target: str
    action: str


@dataclass(frozen=True)
class Threshold(Expr):
    """Bool test on a MetricSeries: arg `op` value, with op in {'<', '>'}."""
    arg: Expr
    op: str
    value: float


@dataclass(frozen=True)
class Guard(Expr):
    cond: Expr
    body: Expr


@dataclass(frozen=True)
class Branch(Expr):
    """branch on a Bool; arms are (pattern, expr) with patterns 'true' and 'false'."""
    scrut: Expr
    arms: tuple[tuple[str, Expr], ...]


@dataclass(frozen=True)
class Retry(Expr):
    n: int
    body: Expr


@dataclass(frozen=True)
class Rollback(Expr):
    token: Expr


@dataclass(frozen=True)
class RequireApproval(Expr):
    body: Expr


@dataclass(frozen=True)
class Hypothesize(Expr):
    label: str
    evidence: tuple[Expr, ...]


@dataclass(frozen=True)
class Validate(Expr):
    hyp: Expr
    check: Expr


@dataclass(frozen=True)
class Ctor(Expr):
    """Success/Failure constructor of the Outcome type (paper Listing 1)."""
    tag: str
    arg: Expr


NODES = {c.__name__: c for c in (Lit, Var, Let, LetPair, MkPair, Observe, Act, Threshold, Guard,
                                 Branch, Retry, Rollback, RequireApproval, Hypothesize, Validate, Ctor)}


# ---- JSON codec --------------------------------------------------------------------------------
def to_json(e: Expr) -> dict[str, Any]:
    """AST -> JSON-able dict."""
    def enc(v: Any) -> Any:
        if isinstance(v, Expr):
            return to_json(v)
        if isinstance(v, Cap):
            return v.value
        if isinstance(v, tuple):
            return [enc(x) for x in v]
        return v
    return {"node": type(e).__name__, **{f.name: enc(getattr(e, f.name)) for f in fields(e)}}


class ParseError(ValueError):
    """The candidate is not a well-formed AST (rejected before type checking)."""


def from_json(obj: Any) -> Expr:
    """JSON dict -> AST. Raises ParseError on any structural problem."""
    if not isinstance(obj, dict) or obj.get("node") not in NODES:
        raise ParseError(f"unknown or missing node tag: {str(obj)[:60]}")
    cls = NODES[obj["node"]]
    kwargs: dict[str, Any] = {}
    for f in fields(cls):
        if f.name not in obj:
            raise ParseError(f"{cls.__name__}: missing field '{f.name}'")
        v = obj[f.name]
        if f.name == "cap":
            try:
                v = Cap(v)
            except ValueError:
                raise ParseError(f"unknown capability {v!r}") from None
        elif f.name == "arms":
            v = tuple((str(p), from_json(x)) for p, x in v)
        elif f.name == "evidence":
            v = tuple(from_json(x) for x in v)
        elif isinstance(v, dict):
            v = from_json(v)
        kwargs[f.name] = v
    return cls(**kwargs)


def parse_program(text: str) -> Expr:
    """Parse a JSON string produced by an LLM."""
    try:
        return from_json(json.loads(text))
    except json.JSONDecodeError as ex:
        raise ParseError(f"invalid JSON: {ex}") from None


# ---- pretty printer ----------------------------------------------------------------------------
def show(e: Expr, ind: int = 0) -> str:
    """Render a program in a surface syntax close to the paper's listing."""
    pad = "  " * ind
    if isinstance(e, Lit):
        return "()" if e.value is None else json.dumps(e.value)
    if isinstance(e, Var):
        return e.name
    if isinstance(e, Let):
        return f"let {e.name} = {show(e.bound, ind)}\n{pad}{show(e.body, ind)}"
    if isinstance(e, LetPair):
        return f"let ({e.fst}, {e.snd}) = {show(e.bound, ind)}\n{pad}{show(e.body, ind)}"
    if isinstance(e, MkPair):
        return f"({show(e.fst)}, {show(e.snd)})"
    if isinstance(e, Observe):
        return f"observe[{e.cap.value}] {e.target}.{e.key}"
    if isinstance(e, Act):
        return f"act[{e.cap.value}] {e.target}.{e.action}"
    if isinstance(e, Threshold):
        return f"({show(e.arg)} {e.op} {e.value:g})"
    if isinstance(e, Guard):
        return f"guard {show(e.cond, ind)} (do\n{pad}  {show(e.body, ind + 1)})"
    if isinstance(e, Branch):
        arms = "".join(f"\n{pad}  | {p} => {show(a, ind + 2)}" for p, a in e.arms)
        return f"branch {show(e.scrut)}{arms}"
    if isinstance(e, Retry):
        return f"retry {e.n} (do\n{pad}  {show(e.body, ind + 1)})"
    if isinstance(e, Rollback):
        return f"rollback {show(e.token)}"
    if isinstance(e, RequireApproval):
        return f"require_approval (do\n{pad}  {show(e.body, ind + 1)})"
    if isinstance(e, Hypothesize):
        return f"hypothesize {e.label!r} [{', '.join(show(x) for x in e.evidence)}]"
    if isinstance(e, Validate):
        return f"validate {show(e.hyp)} {show(e.check)}"
    if isinstance(e, Ctor):
        return f"{e.tag} {show(e.arg)}"
    raise TypeError(e)
