#!/usr/bin/env python3
"""
ZMQ Execution Server Launcher

Standalone script for spawning ZMQ execution server processes.

Usage:
    python -m openhcs.runtime.zmq_execution_server_launcher --port 7777 --persistent
    python -m openhcs.runtime.zmq_execution_server_launcher --port 7777  # non-persistent
"""

import argparse
import logging
import signal
import sys
import time
from openhcs.runtime.zmq_execution_server import ZMQExecutionServer

# Set up logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)


def main():
    """Main entry point for server launcher."""
    parser = argparse.ArgumentParser(description='ZMQ Execution Server Launcher')
    parser.add_argument('--port', type=int, default=7777, help='Data port (control port will be port + 1000)')
    parser.add_argument('--host', type=str, default='*', help='Host to bind to (default: * for all interfaces)')
    parser.add_argument('--persistent', action='store_true', help='Run as persistent server (detached)')
    parser.add_argument('--log-file-path', type=str, default=None, help='Path to server log file (for client discovery)')

    args = parser.parse_args()

    logger.info("=" * 60)
    logger.info("ZMQ Execution Server")
    logger.info("=" * 60)
    logger.info(f"Port: {args.port} (control: {args.port + 1000})")
    logger.info(f"Host: {args.host}")
    logger.info(f"Persistent: {args.persistent}")
    if args.log_file_path:
        logger.info(f"Log file: {args.log_file_path}")
    logger.info("=" * 60)

    # Create server
    server = ZMQExecutionServer(port=args.port, host=args.host, log_file_path=args.log_file_path)
    
    # Set up signal handlers for graceful shutdown
    def signal_handler(sig, frame):
        logger.info("\nShutting down server...")
        server.stop()
        sys.exit(0)
    
    signal.signal(signal.SIGINT, signal_handler)
    signal.signal(signal.SIGTERM, signal_handler)
    
    # Start server
    server.start()
    server.start_time = time.time()
    
    logger.info("Server ready - waiting for requests...")
    
    # Run message loop
    try:
        while server.is_running():
            server.process_messages()
            time.sleep(0.01)  # Small delay to avoid busy loop
    except KeyboardInterrupt:
        logger.info("\nReceived interrupt signal")
    finally:
        server.stop()
        logger.info("Server stopped")


if __name__ == '__main__':
    main()

