"""ZMQ Execution Client - location-transparent pipeline execution."""

import logging
import subprocess
import sys
import time
import threading
import json
import zmq
import pickle
from pathlib import Path
from openhcs.runtime.zmq_base import ZMQClient
from openhcs.core.config import TransportMode
from openhcs.constants.constants import DEFAULT_EXECUTION_SERVER_PORT

logger = logging.getLogger(__name__)


class ZMQExecutionClient(ZMQClient):
    """ZMQ client for OpenHCS pipeline execution with progress streaming."""

    def __init__(self, port=DEFAULT_EXECUTION_SERVER_PORT, host='localhost', persistent=True, progress_callback=None, transport_mode=None):
        super().__init__(port, host, persistent, transport_mode)
        self.progress_callback = progress_callback
        self._progress_thread = None
        self._progress_stop_event = threading.Event()

    def _start_progress_listener(self):
        if self._progress_thread and self._progress_thread.is_alive():
            logger.info("🎧 Progress listener already running")
            return
        if not self.progress_callback:
            logger.info("🎧 No progress callback, skipping listener")
            return
        logger.info("🎧 Starting progress listener thread")
        self._progress_stop_event.clear()
        self._progress_thread = threading.Thread(target=self._progress_listener_loop, daemon=True)
        self._progress_thread.start()
        logger.info("🎧 Progress listener thread started")

    def _stop_progress_listener(self):
        if not self._progress_thread:
            return
        self._progress_stop_event.set()
        if self._progress_thread.is_alive():
            self._progress_thread.join(timeout=2)
        self._progress_thread = None

    def _progress_listener_loop(self):
        logger.info("🎧 Progress listener loop started")
        try:
            message_count = 0
            while not self._progress_stop_event.is_set():
                if not self.data_socket:
                    time.sleep(0.1)
                    continue
                try:
                    message = self.data_socket.recv_string(zmq.NOBLOCK)
                    message_count += 1
                    logger.debug(f"🎧 Received message #{message_count}: {message[:100]}")
                    try:
                        data = json.loads(message)
                        if self.progress_callback and data.get('type') == 'progress':
                            logger.debug(f"🎧 Calling progress callback for: {data.get('well_id')}")
                            try:
                                self.progress_callback(data)
                            except Exception as e:
                                logger.warning(f"🎧 Progress callback error: {e}")
                    except json.JSONDecodeError as e:
                        logger.warning(f"🎧 JSON decode error: {e}")
                except zmq.Again:
                    time.sleep(0.05)
                except Exception as e:
                    logger.warning(f"🎧 Progress listener error: {e}")
                    time.sleep(0.1)
        except Exception as e:
            logger.error(f"🎧 Progress listener loop crashed: {e}", exc_info=True)
        finally:
            logger.info("🎧 Progress listener loop exited")

    def submit_pipeline(self, plate_id, pipeline_steps, global_config, pipeline_config=None, config_params=None):
        """
        Submit pipeline for execution and return immediately (non-blocking).

        Use this for UI applications where you want to submit and return immediately,
        then monitor progress via progress_callback or poll status manually.

        Args:
            plate_id: Plate identifier
            pipeline_steps: List of pipeline steps
            global_config: GlobalPipelineConfig instance
            pipeline_config: Optional PipelineConfig instance
            config_params: Optional config parameters dict

        Returns:
            dict with 'status' and 'execution_id' if accepted, or error info
        """
        if not self._connected and not self.connect():
            raise RuntimeError("Failed to connect to execution server")
        if self.progress_callback:
            self._start_progress_listener()
        from openhcs.debug.pickle_to_python import generate_complete_pipeline_steps_code, generate_config_code
        from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
        logger.info("🔌 CLIENT: Generating pipeline code...")
        pipeline_code = generate_complete_pipeline_steps_code(pipeline_steps, clean_mode=True)
        request = {'type': 'execute', 'plate_id': str(plate_id), 'pipeline_code': pipeline_code}
        if config_params:
            request['config_params'] = config_params
        else:
            request['config_code'] = generate_config_code(global_config, GlobalPipelineConfig, clean_mode=True)
            if pipeline_config:
                request['pipeline_config_code'] = generate_config_code(pipeline_config, PipelineConfig, clean_mode=True)
        logger.info("🔌 CLIENT: Sending execute request...")
        response = self._send_control_request(request)
        logger.info(f"🔌 CLIENT: Got response: {response.get('status')}")
        return response

    def wait_for_completion(self, execution_id, poll_interval=0.5, max_consecutive_errors=5):
        """
        Block and wait for execution to complete (blocking).

        Use this for CLI/script applications where you want to wait for results.
        For UI applications, use submit_pipeline() and monitor via progress_callback.

        Args:
            execution_id: Execution ID from submit_pipeline()
            poll_interval: Seconds between status polls (default: 0.5)
            max_consecutive_errors: Max consecutive errors before giving up (default: 5)

        Returns:
            dict with 'status' ('complete', 'error', 'cancelled') and results/error info
        """
        logger.info(f"🔌 CLIENT: Waiting for execution {execution_id} to complete...")
        consecutive_errors = 0
        poll_count = 0

        while True:
            time.sleep(poll_interval)
            poll_count += 1

            try:
                logger.info(f"🔌 CLIENT: Status poll #{poll_count} for execution {execution_id}")
                status_response = self.get_status(execution_id)
                logger.info(f"🔌 CLIENT: Status response: {status_response}")
                consecutive_errors = 0  # Reset error counter on success

                if status_response.get('status') == 'ok':
                    execution = status_response.get('execution', {})
                    exec_status = execution.get('status')
                    logger.info(f"🔌 CLIENT: Execution status: {exec_status}")
                    if exec_status == 'complete':
                        logger.info("🔌 CLIENT: Execution complete, returning results")
                        return {'status': 'complete', 'execution_id': execution_id, 'results': execution.get('results_summary', {})}
                    elif exec_status == 'failed':
                        logger.info("🔌 CLIENT: Execution failed")
                        return {'status': 'error', 'execution_id': execution_id, 'message': execution.get('error')}
                    elif exec_status == 'cancelled':
                        logger.info("🔌 CLIENT: Execution cancelled")
                        return {'status': 'cancelled', 'execution_id': execution_id, 'message': 'Execution was cancelled'}
                elif status_response.get('status') == 'error':
                    # Server returned error status
                    error_msg = status_response.get('message', 'Unknown error')
                    logger.warning(f"Status check returned error: {error_msg}")
                    return {'status': 'error', 'execution_id': execution_id, 'message': error_msg}

            except Exception as e:
                # Handle ZMQ errors, connection issues, etc.
                consecutive_errors += 1
                logger.warning(f"Error checking execution status (attempt {consecutive_errors}/{max_consecutive_errors}): {e}")

                if consecutive_errors >= max_consecutive_errors:
                    # Too many consecutive errors - assume execution failed or was cancelled
                    logger.error(f"Failed to get execution status after {max_consecutive_errors} attempts, assuming execution was cancelled")
                    return {'status': 'cancelled', 'execution_id': execution_id,
                           'message': f'Lost connection to server (workers may have been killed)'}

                # Wait a bit longer before retrying after error
                time.sleep(1.0)

    def execute_pipeline(self, plate_id, pipeline_steps, global_config, pipeline_config=None, config_params=None):
        """
        Submit pipeline and wait for completion (blocking - for backward compatibility).

        This is the legacy blocking API. For UI applications, use submit_pipeline() instead.

        Args:
            plate_id: Plate identifier
            pipeline_steps: List of pipeline steps
            global_config: GlobalPipelineConfig instance
            pipeline_config: Optional PipelineConfig instance
            config_params: Optional config parameters dict

        Returns:
            dict with execution results (blocks until complete)
        """
        response = self.submit_pipeline(plate_id, pipeline_steps, global_config, pipeline_config, config_params)
        if response.get('status') == 'accepted':
            execution_id = response.get('execution_id')
            return self.wait_for_completion(execution_id)
        return response

    def get_status(self, execution_id=None):
        request = {'type': 'status'}
        if execution_id:
            request['execution_id'] = execution_id
        return self._send_control_request(request)

    def cancel_execution(self, execution_id):
        return self._send_control_request({'type': 'cancel', 'execution_id': execution_id})

    def ping(self):
        try:
            pong = self.get_server_info()
            return pong.get('type') == 'pong' and pong.get('ready')
        except:
            return False

    def get_server_info(self):
        try:
            if not self._connected and not self.connect():
                return {'status': 'error', 'message': 'Not connected'}
            ctx = zmq.Context()
            sock = ctx.socket(zmq.REQ)
            sock.setsockopt(zmq.LINGER, 0)
            sock.setsockopt(zmq.RCVTIMEO, 1000)
            sock.connect(f"tcp://{self.host}:{self.control_port}")
            sock.send(pickle.dumps({'type': 'ping'}))
            response = pickle.loads(sock.recv())
            sock.close()
            ctx.term()
            return response
        except:
            return {'status': 'error', 'message': 'Failed'}

    def _send_control_request(self, request, timeout_ms=5000):
        """
        Send a control request to the server.

        Args:
            request: Request dictionary to send
            timeout_ms: Timeout in milliseconds (default: 5000)

        Returns:
            Response dictionary from server

        Raises:
            Exception: If request fails or times out
        """
        from openhcs.runtime.zmq_base import get_zmq_transport_url
        ctx = zmq.Context()
        sock = ctx.socket(zmq.REQ)
        sock.setsockopt(zmq.LINGER, 0)
        sock.setsockopt(zmq.RCVTIMEO, timeout_ms)  # Set receive timeout
        control_url = get_zmq_transport_url(self.control_port, self.transport_mode, self.host)
        sock.connect(control_url)
        try:
            sock.send(pickle.dumps(request))
            response = sock.recv()
            return pickle.loads(response)
        except zmq.Again:
            # Timeout - server didn't respond
            raise TimeoutError(f"Server did not respond to {request.get('type')} request within {timeout_ms}ms")
        finally:
            sock.close()
            ctx.term()

    def _spawn_server_process(self):
        from pathlib import Path
        import time
        log_dir = Path.home() / ".local" / "share" / "openhcs" / "logs"
        log_dir.mkdir(parents=True, exist_ok=True)
        log_file_path = log_dir / f"openhcs_zmq_server_port_{self.port}_{int(time.time() * 1000000)}.log"
        cmd = [sys.executable, '-m', 'openhcs.runtime.zmq_execution_server_launcher', '--port', str(self.port)]
        if self.persistent:
            cmd.append('--persistent')
        cmd.extend(['--log-file-path', str(log_file_path)])
        cmd.extend(['--transport-mode', self.transport_mode.value])
        return subprocess.Popen(cmd, stdout=open(log_file_path, 'w'), stderr=subprocess.STDOUT, start_new_session=self.persistent)

    def disconnect(self):
        self._stop_progress_listener()
        super().disconnect()

    def send_data(self, data):
        pass

    def __enter__(self):
        self.connect()
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.disconnect()

