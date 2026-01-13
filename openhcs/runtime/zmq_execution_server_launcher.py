#!/usr/bin/env python3
"""
ZMQ Execution Server Launcher

Standalone script for spawning ZMQ execution server processes.
"""
from __future__ import annotations

import argparse
import logging
import signal
import sys
import time

from zmqruntime.config import TransportMode
from zmqruntime.transport import get_default_transport_mode

from openhcs.runtime.zmq_execution_server import OpenHCSExecutionServer

# Set up logging
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
)
logger = logging.getLogger(__name__)


def main():
    """Main entry point for server launcher."""
    from openhcs.constants.constants import DEFAULT_EXECUTION_SERVER_PORT, CONTROL_PORT_OFFSET

    default_mode = get_default_transport_mode()
    default_mode_str = "tcp" if default_mode == TransportMode.TCP else "ipc"

    parser = argparse.ArgumentParser(description="ZMQ Execution Server Launcher")
    parser.add_argument(
        "--port",
        type=int,
        default=DEFAULT_EXECUTION_SERVER_PORT,
        help=f"Data port (control port will be port + {CONTROL_PORT_OFFSET})",
    )
    parser.add_argument("--host", type=str, default="*", help="Host to bind to (default: * for all interfaces)")
    parser.add_argument("--persistent", action="store_true", help="Run as persistent server (detached)")
    parser.add_argument("--log-file-path", type=str, default=None, help="Path to server log file (for client discovery)")
    parser.add_argument(
        "--transport-mode",
        type=str,
        default=default_mode_str,
        choices=["ipc", "tcp"],
        help=f"Transport mode (default: {default_mode_str} for this platform)",
    )

    args = parser.parse_args()

    transport_mode = TransportMode.IPC if args.transport_mode == "ipc" else TransportMode.TCP

    logger.info("=" * 60)
    logger.info("ZMQ Execution Server")
    logger.info("=" * 60)
    logger.info("Port: %s (control: %s)", args.port, args.port + 1000)
    logger.info("Host: %s", args.host)
    logger.info("Transport mode: %s", transport_mode.value)
    logger.info("Persistent: %s", args.persistent)
    if args.log_file_path:
        logger.info("Log file: %s", args.log_file_path)
    logger.info("=" * 60)

    server = OpenHCSExecutionServer(
        port=args.port,
        host=args.host,
        log_file_path=args.log_file_path,
        transport_mode=transport_mode,
    )

    def signal_handler(sig, frame):
        logger.info("\nShutting down server...")
        server.stop()
        sys.exit(0)

    signal.signal(signal.SIGINT, signal_handler)
    signal.signal(signal.SIGTERM, signal_handler)

    server.start()
    server.start_time = time.time()

    logger.info("Server ready - waiting for requests...")

    try:
        while server.is_running():
            server.process_messages()
            time.sleep(0.01)
    except KeyboardInterrupt:
        logger.info("\nReceived interrupt signal")
    finally:
        server.stop()
        logger.info("Server stopped")


if __name__ == "__main__":
    main()
