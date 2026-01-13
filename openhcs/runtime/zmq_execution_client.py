"""OpenHCS execution client built on zmqruntime ExecutionClient."""
from __future__ import annotations

import logging
import subprocess
import sys
import threading
import time
from pathlib import Path
from typing import Any

from zmqruntime.execution import ExecutionClient

from zmqruntime.transport import coerce_transport_mode
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG

logger = logging.getLogger(__name__)


class OpenHCSExecutionClient(ExecutionClient):
    """ZMQ client for OpenHCS pipeline execution with progress streaming."""

    def __init__(
        self,
        port: int = OPENHCS_ZMQ_CONFIG.default_port,
        host: str = "localhost",
        persistent: bool = True,
        progress_callback=None,
        transport_mode=None,
    ):
        super().__init__(
            port,
            host,
            persistent,
            progress_callback=progress_callback,
            transport_mode=coerce_transport_mode(transport_mode),
            config=OPENHCS_ZMQ_CONFIG,
        )

    def serialize_task(self, task: Any, config: Any = None) -> dict:
        from openhcs.debug.pickle_to_python import generate_complete_pipeline_steps_code, generate_config_code
        from openhcs.core.config import GlobalPipelineConfig, PipelineConfig

        plate_id = task.get("plate_id")
        pipeline_steps = task.get("pipeline_steps")
        global_config = task.get("global_config")
        pipeline_config = task.get("pipeline_config")
        config_params = task.get("config_params")

        pipeline_code = generate_complete_pipeline_steps_code(pipeline_steps, clean_mode=True)
        request = {"type": "execute", "plate_id": str(plate_id), "pipeline_code": pipeline_code}
        if config_params:
            request["config_params"] = config_params
        else:
            request["config_code"] = generate_config_code(global_config, GlobalPipelineConfig, clean_mode=True)
            if pipeline_config:
                request["pipeline_config_code"] = generate_config_code(pipeline_config, PipelineConfig, clean_mode=True)
        return request

    def submit_pipeline(self, plate_id, pipeline_steps, global_config, pipeline_config=None, config_params=None):
        task = {
            "plate_id": plate_id,
            "pipeline_steps": pipeline_steps,
            "global_config": global_config,
            "pipeline_config": pipeline_config,
            "config_params": config_params,
        }
        return self.submit_execution(task)

    def execute_pipeline(self, plate_id, pipeline_steps, global_config, pipeline_config=None, config_params=None):
        response = self.submit_pipeline(plate_id, pipeline_steps, global_config, pipeline_config, config_params)
        if response.get("status") == "accepted":
            execution_id = response.get("execution_id")
            return self.wait_for_completion(execution_id)
        return response

    def get_status(self, execution_id=None):
        return self.poll_status(execution_id)

    def _spawn_server_process(self):
        import os
        import glob

        log_dir = Path.home() / ".local" / "share" / "openhcs" / "logs"
        log_dir.mkdir(parents=True, exist_ok=True)
        log_file_path = log_dir / f"openhcs_zmq_server_port_{self.port}_{int(time.time() * 1000000)}.log"
        cmd = [sys.executable, "-m", "openhcs.runtime.zmq_execution_server_launcher", "--port", str(self.port)]
        if self.persistent:
            cmd.append("--persistent")
        cmd.extend(["--log-file-path", str(log_file_path)])
        cmd.extend(["--transport-mode", self.transport_mode.value])

        env = os.environ.copy()
        site_packages = (
            Path(sys.executable).parent.parent
            / "lib"
            / f"python{sys.version_info.major}.{sys.version_info.minor}"
            / "site-packages"
        )
        nvidia_lib_pattern = str(site_packages / "nvidia" / "*" / "lib")
        venv_nvidia_libs = [p for p in glob.glob(nvidia_lib_pattern) if os.path.isdir(p)]

        if venv_nvidia_libs:
            existing_ld_path = env.get("LD_LIBRARY_PATH", "")
            nvidia_paths = ":".join(venv_nvidia_libs)
            env["LD_LIBRARY_PATH"] = f"{nvidia_paths}:{existing_ld_path}" if existing_ld_path else nvidia_paths

        return subprocess.Popen(
            cmd,
            stdout=open(log_file_path, "w"),
            stderr=subprocess.STDOUT,
            start_new_session=self.persistent,
            env=env,
        )

    def send_data(self, data):
        pass

    def __enter__(self):
        self.connect()
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.disconnect()


ZMQExecutionClient = OpenHCSExecutionClient
