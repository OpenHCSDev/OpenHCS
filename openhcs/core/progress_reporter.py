"""Progress reporter for ZMQ execution updates.

Converts application-specific progress to generic TaskProgress format.
"""

from __future__ import annotations

import logging
import os
import time
from typing import Any, Callable, Dict

from zmqruntime.messages import MessageFields, validate_progress_payload

logger = logging.getLogger(__name__)


def _noop(_payload: Dict[str, Any]) -> None:
    return None


_PROGRESS_EMITTER: Callable[[Dict[str, Any]], None] = _noop
_PROGRESS_CONTEXT: Dict[str, Any] = {}


def set_progress_emitter(
    emitter: Callable[[Dict[str, Any]], None], context: Dict[str, Any]
) -> None:
    global _PROGRESS_EMITTER
    global _PROGRESS_CONTEXT
    if emitter is None:
        raise ValueError("progress emitter cannot be None")
    if not isinstance(context, dict):
        raise TypeError("progress context must be a dict")
    if MessageFields.EXECUTION_ID not in context:
        raise KeyError("progress context missing execution_id")
    if MessageFields.PLATE_ID not in context:
        raise KeyError("progress context missing plate_id")
    execution_id = context[MessageFields.EXECUTION_ID]
    plate_id = context[MessageFields.PLATE_ID]
    if not isinstance(execution_id, str) or not execution_id:
        raise TypeError("progress context execution_id must be a non-empty string")
    if not isinstance(plate_id, str) or not plate_id:
        raise TypeError("progress context plate_id must be a non-empty string")
    _PROGRESS_EMITTER = emitter
    _PROGRESS_CONTEXT = context


def clear_progress_emitter() -> None:
    global _PROGRESS_EMITTER
    global _PROGRESS_CONTEXT
    _PROGRESS_EMITTER = _noop
    _PROGRESS_CONTEXT = {}


def _to_generic_progress(data: Dict[str, Any], context: Dict[str, Any]) -> Dict[str, Any]:
    """Convert application-specific progress to generic TaskProgress format.

    Passes through app-specific phase/status values directly - no conversion.
    The receiving end (progress_state.py) handles the app-specific values.
    """
    # DEBUG: Log input data
    has_total_wells_before = 'total_wells' in data
    if has_total_wells_before:
        logger.info(f"_to_generic_progress: input has total_wells={data.get('total_wells')}, keys={list(data.keys())}")

    # Start with data - passes through EVERYTHING including phase/status as-is
    result = dict(data)

    # Inject context fields
    result["task_id"] = context[MessageFields.EXECUTION_ID]
    result["plate_id"] = context[MessageFields.PLATE_ID]

    # Add infrastructure fields
    result["type"] = "progress"
    result["timestamp"] = time.time()
    result["pid"] = os.getpid()

    # DEBUG: Log output
    has_total_wells_after = 'total_wells' in result
    if has_total_wells_before or has_total_wells_after:
        logger.info(f"_to_generic_progress: output has total_wells={result.get('total_wells')}, keys={list(result.keys())}")

    return result


def emit_progress(payload: Dict[str, Any]) -> None:
    # Convert to generic format
    generic_payload = _to_generic_progress(payload, _PROGRESS_CONTEXT)

    try:
        validate_progress_payload(generic_payload)
    except Exception:
        logger.exception(
            "PROGRESS_DEBUG: validate_progress_payload failed for payload: %s", generic_payload
        )
        raise

    logger.info(
        f"Progress emit: phase={payload.get('phase')}, step={payload.get('step')}, axis={generic_payload.get('axis_id')}, "
        f"plate_id={generic_payload.get('plate_id')}, keys={list(generic_payload.keys())}, "
        f"emitter={'set' if _PROGRESS_EMITTER is not _noop else 'unset'}"
    )
    _PROGRESS_EMITTER(generic_payload)
