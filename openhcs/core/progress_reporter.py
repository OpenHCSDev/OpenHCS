"""Progress reporter for ZMQ execution updates."""

from __future__ import annotations

import time
from typing import Any, Callable, Dict


def _noop(_payload: Dict[str, Any]) -> None:
    return None


_PROGRESS_EMITTER: Callable[[Dict[str, Any]], None] = _noop
_PROGRESS_CONTEXT: Dict[str, Any] = {}


def set_progress_emitter(
    emitter: Callable[[Dict[str, Any]], None], context: Dict[str, Any]
) -> None:
    global _PROGRESS_EMITTER
    global _PROGRESS_CONTEXT
    _PROGRESS_EMITTER = emitter
    _PROGRESS_CONTEXT = context


def clear_progress_emitter() -> None:
    global _PROGRESS_EMITTER
    global _PROGRESS_CONTEXT
    _PROGRESS_EMITTER = _noop
    _PROGRESS_CONTEXT = {}


def emit_progress(payload: Dict[str, Any]) -> None:
    data = dict(_PROGRESS_CONTEXT)
    data.update(payload)
    data["type"] = "progress"
    data["timestamp"] = time.time()
    _PROGRESS_EMITTER(data)
