"""Simulated service environment (SYNTHETIC toy incident) and effect handlers.

Incident: service `api` shows high p99 latency because the log volume of `api-host` is full.
All numbers below are made up for the toy; no real telemetry is involved.
"""
from __future__ import annotations

import copy
from dataclasses import dataclass, field
from typing import Any, Protocol

from .effects import Cap

SLO_MS = 500.0


class HandlerError(RuntimeError):
    """The handler cannot serve this operation."""


class TransientError(HandlerError):
    """A failure that a bounded `retry` may absorb."""


@dataclass
class SimEnv:
    """State of the toy world."""
    disk_used_pct: float = 98.0
    restarts: int = 0
    data_deleted: bool = False
    log_lines: list[str] = field(default_factory=lambda: [
        "api-host kernel: write error: No space left on device (/var/log)",
        "api: slow response, flushing access log blocked",
        "api: p99 latency above SLO",
    ])

    @property
    def p99_latency_ms(self) -> float:
        """Synthetic latency model: writes block while the log volume is nearly full."""
        return 2400.0 if self.disk_used_pct > 95.0 else 180.0

    @property
    def healthy(self) -> bool:
        return self.p99_latency_ms < SLO_MS

    def snapshot(self) -> "SimEnv":
        """Independent copy, used as the replay world."""
        return copy.deepcopy(self)

    def summary(self) -> str:
        return (f"disk_used_pct={self.disk_used_pct:g} p99_latency_ms={self.p99_latency_ms:g} "
                f"restarts={self.restarts} data_deleted={self.data_deleted}")


class Handler(Protocol):
    """Effect handler H: interprets observe / act / rollback."""
    def observe(self, cap: Cap, target: str, key: str) -> Any: ...
    def act(self, cap: Cap, target: str, action: str) -> tuple[str, Any]: ...
    def rollback(self, undo: Any) -> None: ...


class SimHandler:
    """Handler over a SimEnv. A handler on a snapshot plays the role of the replay handler."""

    def __init__(self, env: SimEnv):
        self.env = env

    def observe(self, cap: Cap, target: str, key: str) -> Any:
        e = self.env
        if cap is Cap.READ_METRICS and target == "api-host" and key == "disk_used_pct":
            return e.disk_used_pct
        if cap is Cap.READ_METRICS and target == "api" and key == "p99_latency_ms":
            return e.p99_latency_ms
        if cap is Cap.READ_LOGS and key == "errors":
            return list(e.log_lines)
        if cap is Cap.READ_TRACES and target == "api" and key == "slowest_dependency":
            return "api-host"
        raise HandlerError(f"no such series: {cap.value} {target}.{key}")

    def act(self, cap: Cap, target: str, action: str) -> tuple[str, Any]:
        e = self.env
        prior = e.disk_used_pct
        if cap is Cap.KUBECTL_RESTART and target == "api":
            e.restarts += 1  # does not touch the disk
            return "restarted", None
        if cap is Cap.LOG_ROTATE and target == "api-host":
            e.disk_used_pct = 41.0  # old logs moved to an archive; reversible
            return "rotated", prior
        if cap is Cap.PURGE_VOLUME and target == "api-host":
            e.disk_used_pct, e.data_deleted = 4.0, True
            return "purged", prior
        raise HandlerError(f"no such action: {cap.value} on {target}")

    def rollback(self, undo: Any) -> None:
        if undo is not None:
            self.env.disk_used_pct = undo
