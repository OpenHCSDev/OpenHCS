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

logger = logging.getLogger(__name__)


class ZMQExecutionClient(ZMQClient):
    """ZMQ client for OpenHCS pipeline execution with progress streaming."""

    def __init__(self, port=7777, host='localhost', persistent=True, progress_callback=None):
        super().__init__(port, host, persistent)
        self.progress_callback = progress_callback
        self._progress_thread = None
        self._progress_stop_event = threading.Event()

    def _start_progress_listener(self):
        if self._progress_thread and self._progress_thread.is_alive():
            return
        if not self.progress_callback:
            return
        self._progress_stop_event.clear()
        self._progress_thread = threading.Thread(target=self._progress_listener_loop, daemon=True)
        self._progress_thread.start()

    def _stop_progress_listener(self):
        if not self._progress_thread:
            return
        self._progress_stop_event.set()
        if self._progress_thread.is_alive():
            self._progress_thread.join(timeout=2)
        self._progress_thread = None

    def _progress_listener_loop(self):
        try:
            while not self._progress_stop_event.is_set():
                if not self.data_socket:
                    time.sleep(0.1)
                    continue
                try:
                    message = self.data_socket.recv_string(zmq.NOBLOCK)
                    try:
                        data = json.loads(message)
                        if self.progress_callback and data.get('type') == 'progress':
                            try:
                                self.progress_callback(data)
                            except:
                                pass
                    except json.JSONDecodeError:
                        pass
                except zmq.Again:
                    time.sleep(0.05)
                except:
                    time.sleep(0.1)
        except:
            pass

    def execute_pipeline(self, plate_id, pipeline_steps, global_config, pipeline_config=None, config_params=None):
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
        if response.get('status') == 'accepted':
            execution_id = response.get('execution_id')
            logger.info(f"🔌 CLIENT: Execution accepted, ID={execution_id}, starting status polling...")
            consecutive_errors = 0
            max_consecutive_errors = 5
            poll_count = 0

            while True:
                time.sleep(0.5)
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

        logger.info(f"🔌 CLIENT: Returning response: {response}")
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
        ctx = zmq.Context()
        sock = ctx.socket(zmq.REQ)
        sock.setsockopt(zmq.LINGER, 0)
        sock.setsockopt(zmq.RCVTIMEO, timeout_ms)  # Set receive timeout
        sock.connect(f"tcp://{self.host}:{self.control_port}")
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

