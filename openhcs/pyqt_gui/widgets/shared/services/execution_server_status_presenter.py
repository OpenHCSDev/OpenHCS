"""Execution-server status line presenter for batch workflow UI."""

from __future__ import annotations

from dataclasses import dataclass
from typing import List

from openhcs.core.progress.projection import ExecutionRuntimeProjection
from pyqt_reactive.services import (
    ExecutionServerInfo,
)


@dataclass(frozen=True)
class ExecutionServerStatusView:
    """Rendered status text for plate-manager status bar."""

    text: str


class ExecutionServerStatusPresenter:
    """Build status text from runtime projection + optional server snapshot."""

    def build_status_text(
        self,
        *,
        projection: ExecutionRuntimeProjection,
        server_info: ExecutionServerInfo | None,
    ) -> ExecutionServerStatusView:
        plate_count = len(projection.by_plate_latest)
        if plate_count == 0:
            return ExecutionServerStatusView(text="Ready")

        parts: List[str] = []
        if projection.compiling_count > 0:
            parts.append(f"⏳ {projection.compiling_count} compiling")
        if projection.executing_count > 0:
            parts.append(f"⚙️ {projection.executing_count} executing")
        if projection.compiled_count > 0:
            parts.append(f"✓ {projection.compiled_count} compiled")
        if projection.complete_count > 0:
            parts.append(f"✅ {projection.complete_count} complete")
        if projection.failed_count > 0:
            parts.append(f"❌ {projection.failed_count} failed")

        if server_info is not None:
            if server_info.compile_status is not None:
                parts.append(f"srv:{server_info.compile_status.status_text}")
            if server_info.running_executions:
                parts.append(f"srv_run:{len(server_info.running_executions)}")
            if server_info.queued_executions:
                parts.append(f"srv_q:{len(server_info.queued_executions)}")

        status_text = ", ".join(parts) if parts else "idle"
        return ExecutionServerStatusView(
            text=(
                f"Server: {status_text} | "
                f"{plate_count} plates | avg {projection.overall_percent:.1f}%"
            )
        )
