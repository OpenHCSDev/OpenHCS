"""OpenHCS-specific ZMQ configuration for zmqruntime."""
from __future__ import annotations

from zmqruntime import ZMQConfig
from openhcs.constants.constants import (
    CONTROL_PORT_OFFSET,
    DEFAULT_EXECUTION_SERVER_PORT,
    IPC_SOCKET_DIR_NAME,
    IPC_SOCKET_EXTENSION,
    IPC_SOCKET_PREFIX,
)

OPENHCS_ZMQ_CONFIG = ZMQConfig(
    control_port_offset=CONTROL_PORT_OFFSET,
    default_port=DEFAULT_EXECUTION_SERVER_PORT,
    ipc_socket_dir=IPC_SOCKET_DIR_NAME,
    ipc_socket_prefix=IPC_SOCKET_PREFIX,
    ipc_socket_extension=IPC_SOCKET_EXTENSION,
    shared_ack_port=7555,
    app_name="openhcs",
)
