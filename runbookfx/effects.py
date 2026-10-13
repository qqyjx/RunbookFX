"""Product effect algebra Risk x Cap-sets x N with interaction axioms I1-I4 (paper: Parametric Effect Algebra)."""
from __future__ import annotations

from dataclasses import dataclass
from enum import Enum, IntEnum


class Risk(IntEnum):
    """Three-element risk lattice: ReadOnly <= SafeChange <= Disruptive."""
    READ_ONLY = 0
    SAFE_CHANGE = 1
    DISRUPTIVE = 2


class Cap(Enum):
    """Capabilities. The first three read, the rest mutate (the paper lists more, `...`)."""
    READ_LOGS = "read_logs"
    READ_METRICS = "read_metrics"
    READ_TRACES = "read_traces"
    KUBECTL_RESTART = "kubectl_restart"
    LOG_ROTATE = "log_rotate"          # demo-specific, SafeChange
    PURGE_VOLUME = "purge_volume"      # demo-specific, Disruptive (deletes data)

    @property
    def risk(self) -> Risk:
        """risk(c): minimum risk level of the capability."""
        if self in (Cap.READ_LOGS, Cap.READ_METRICS, Cap.READ_TRACES):
            return Risk.READ_ONLY
        return Risk.DISRUPTIVE if self is Cap.PURGE_VOLUME else Risk.SAFE_CHANGE


@dataclass(frozen=True)
class Effect:
    """Effect grade (r, k, n): risk, capabilities exercised, rollback obligations."""
    risk: Risk = Risk.READ_ONLY
    caps: frozenset[Cap] = frozenset()
    n: int = 0

    def join(self, other: "Effect") -> "Effect":
        """Monoid operation (sequencing): risk join, cap union, resources SUM."""
        return Effect(max(self.risk, other.risk), self.caps | other.caps, self.n + other.n)

    def alt(self, other: "Effect") -> "Effect":
        """Lattice join over alternative branches: resources take the MAX."""
        return Effect(max(self.risk, other.risk), self.caps | other.caps, max(self.n, other.n))

    def scale(self, times: int) -> "Effect":
        """Effect of running a body up to `times` times (bounded retry)."""
        return Effect(self.risk, self.caps, self.n * times)

    def leq(self, other: "Effect") -> bool:
        """Componentwise order."""
        return self.risk <= other.risk and self.caps <= other.caps and self.n <= other.n

    def excess(self, other: "Effect") -> list[str]:
        """Components of self that exceed `other` (empty list iff self.leq(other))."""
        out = []
        if self.risk > other.risk:
            out.append(f"risk {self.risk.name} > {other.risk.name}")
        if self.n > other.n:
            out.append(f"rollback obligations {self.n} > {other.n}")
        if not self.caps <= other.caps:
            out.append("capabilities " + ",".join(sorted(c.value for c in self.caps - other.caps)))
        return out

    def violations(self) -> list[str]:
        """Interaction axioms I1-I4 that this grade breaks (empty list = well-formed)."""
        out = []
        if self.risk == Risk.READ_ONLY and self.n != 0:
            out.append("I1: ReadOnly with rollback obligations")
        if self.risk == Risk.DISRUPTIVE and not self.caps:
            out.append("I2: Disruptive without a capability witness")
        if self.n > 0 and self.risk < Risk.SAFE_CHANGE:
            out.append("I3: rollback obligations without mutation risk")
        for c in sorted(self.caps, key=lambda c: c.value):
            if c.risk > self.risk:
                out.append(f"I4: capability {c.value} has risk above {self.risk.name}")
        return out

    @property
    def wf(self) -> bool:
        return not self.violations()

    def __str__(self) -> str:
        caps = ",".join(sorted(c.value for c in self.caps))
        return f"({self.risk.name}, {{{caps}}}, {self.n})"


BOT = Effect()
