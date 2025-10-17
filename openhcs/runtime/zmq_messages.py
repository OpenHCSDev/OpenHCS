"""ZMQ Message Type System - enum dispatch and structured messages."""

import logging
from enum import Enum
from dataclasses import dataclass

logger = logging.getLogger(__name__)


class MessageFields:
    TYPE = "type"
    PLATE_ID = "plate_id"
    PIPELINE_CODE = "pipeline_code"
    CONFIG_PARAMS = "config_params"
    CONFIG_CODE = "config_code"
    PIPELINE_CONFIG_CODE = "pipeline_config_code"
    CLIENT_ADDRESS = "client_address"
    EXECUTION_ID = "execution_id"
    START_TIME = "start_time"
    END_TIME = "end_time"
    ELAPSED = "elapsed"
    STATUS = "status"
    ERROR = "error"
    MESSAGE = "message"
    PORT = "port"
    CONTROL_PORT = "control_port"
    READY = "ready"
    SERVER = "server"
    LOG_FILE_PATH = "log_file_path"
    ACTIVE_EXECUTIONS = "active_executions"
    RUNNING_EXECUTIONS = "running_executions"
    WORKERS = "workers"
    WORKERS_KILLED = "workers_killed"
    UPTIME = "uptime"
    EXECUTIONS = "executions"
    WELL_COUNT = "well_count"
    WELLS = "wells"
    RESULTS_SUMMARY = "results_summary"
    WELL_ID = "well_id"
    STEP = "step"
    TIMESTAMP = "timestamp"
    # Acknowledgment message fields
    IMAGE_ID = "image_id"
    VIEWER_PORT = "viewer_port"
    VIEWER_TYPE = "viewer_type"
    # ROI message fields
    ROIS = "rois"
    LAYER_NAME = "layer_name"
    SHAPES = "shapes"
    COORDINATES = "coordinates"
    METADATA = "metadata"


class ControlMessageType(Enum):
    PING = "ping"
    EXECUTE = "execute"
    STATUS = "status"
    CANCEL = "cancel"
    SHUTDOWN = "shutdown"
    FORCE_SHUTDOWN = "force_shutdown"

    def get_handler_method(self):
        return {
            ControlMessageType.EXECUTE: "_handle_execute",
            ControlMessageType.STATUS: "_handle_status",
            ControlMessageType.CANCEL: "_handle_cancel",
            ControlMessageType.SHUTDOWN: "_handle_shutdown",
            ControlMessageType.FORCE_SHUTDOWN: "_handle_force_shutdown",
        }[self]

    def dispatch(self, server, message):
        return getattr(server, self.get_handler_method())(message)


class ResponseType(Enum):
    PONG = "pong"
    ACCEPTED = "accepted"
    OK = "ok"
    ERROR = "error"
    SHUTDOWN_ACK = "shutdown_ack"


class ExecutionStatus(Enum):
    RUNNING = "running"
    COMPLETE = "complete"
    COMPLETED = "completed"
    FAILED = "failed"
    CANCELLED = "cancelled"
    ACCEPTED = "accepted"


class SocketType(Enum):
    PUB = "PUB"
    SUB = "SUB"
    REQ = "REQ"
    REP = "REP"

    @classmethod
    def from_zmq_constant(cls, zmq_const):
        import zmq
        return {zmq.PUB: cls.PUB, zmq.SUB: cls.SUB, zmq.REQ: cls.REQ, zmq.REP: cls.REP}.get(zmq_const, cls.PUB)

    def get_display_name(self):
        return self.value


@dataclass(frozen=True)
class ExecuteRequest:
    plate_id: str
    pipeline_code: str
    config_params: dict = None
    config_code: str = None
    pipeline_config_code: str = None
    client_address: str = None

    def validate(self):
        if not self.plate_id:
            return "Missing required field: plate_id"
        if not self.pipeline_code:
            return "Missing required field: pipeline_code"
        if self.config_params is None and self.config_code is None:
            return "Missing config: provide either config_params or config_code"
        return None

    def to_dict(self):
        result = {MessageFields.TYPE: ControlMessageType.EXECUTE.value, MessageFields.PLATE_ID: self.plate_id, MessageFields.PIPELINE_CODE: self.pipeline_code}
        if self.config_params is not None:
            result[MessageFields.CONFIG_PARAMS] = self.config_params
        if self.config_code is not None:
            result[MessageFields.CONFIG_CODE] = self.config_code
        if self.pipeline_config_code is not None:
            result[MessageFields.PIPELINE_CONFIG_CODE] = self.pipeline_config_code
        if self.client_address is not None:
            result[MessageFields.CLIENT_ADDRESS] = self.client_address
        return result

    @classmethod
    def from_dict(cls, data):
        return cls(plate_id=data[MessageFields.PLATE_ID], pipeline_code=data[MessageFields.PIPELINE_CODE],
                  config_params=data.get(MessageFields.CONFIG_PARAMS), config_code=data.get(MessageFields.CONFIG_CODE),
                  pipeline_config_code=data.get(MessageFields.PIPELINE_CONFIG_CODE), client_address=data.get(MessageFields.CLIENT_ADDRESS))


@dataclass(frozen=True)
class ExecuteResponse:
    status: ResponseType
    execution_id: str = None
    message: str = None
    error: str = None

    def to_dict(self):
        result = {MessageFields.STATUS: self.status.value}
        if self.execution_id is not None:
            result[MessageFields.EXECUTION_ID] = self.execution_id
        if self.message is not None:
            result[MessageFields.MESSAGE] = self.message
        if self.error is not None:
            result[MessageFields.ERROR] = self.error
        return result


@dataclass(frozen=True)
class StatusRequest:
    execution_id: str = None

    def to_dict(self):
        result = {MessageFields.TYPE: ControlMessageType.STATUS.value}
        if self.execution_id is not None:
            result[MessageFields.EXECUTION_ID] = self.execution_id
        return result

    @classmethod
    def from_dict(cls, data):
        return cls(execution_id=data.get(MessageFields.EXECUTION_ID))


@dataclass(frozen=True)
class CancelRequest:
    execution_id: str

    def validate(self):
        return "Missing execution_id" if not self.execution_id else None

    def to_dict(self):
        return {MessageFields.TYPE: ControlMessageType.CANCEL.value, MessageFields.EXECUTION_ID: self.execution_id}

    @classmethod
    def from_dict(cls, data):
        return cls(execution_id=data[MessageFields.EXECUTION_ID])


@dataclass(frozen=True)
class PongResponse:
    port: int
    control_port: int
    ready: bool
    server: str
    log_file_path: str = None
    active_executions: int = None
    running_executions: list = None
    workers: list = None
    uptime: float = None

    def to_dict(self):
        result = {MessageFields.TYPE: ResponseType.PONG.value, MessageFields.PORT: self.port,
                 MessageFields.CONTROL_PORT: self.control_port, MessageFields.READY: self.ready, MessageFields.SERVER: self.server}
        if self.log_file_path is not None:
            result[MessageFields.LOG_FILE_PATH] = self.log_file_path
        if self.active_executions is not None:
            result[MessageFields.ACTIVE_EXECUTIONS] = self.active_executions
        if self.running_executions is not None:
            result[MessageFields.RUNNING_EXECUTIONS] = self.running_executions
        if self.workers is not None:
            result[MessageFields.WORKERS] = self.workers
        if self.uptime is not None:
            result[MessageFields.UPTIME] = self.uptime
        return result


@dataclass(frozen=True)
class ProgressUpdate:
    well_id: str
    step: str
    status: str
    timestamp: float

    def to_dict(self):
        return {MessageFields.TYPE: "progress", MessageFields.WELL_ID: self.well_id,
                MessageFields.STEP: self.step, MessageFields.STATUS: self.status, MessageFields.TIMESTAMP: self.timestamp}


@dataclass(frozen=True)
class ImageAck:
    """Acknowledgment message sent by viewers after processing an image.

    Sent via PUSH socket from viewer to shared ack port (7555).
    Used to track real-time queue depth and show progress like '3/10 images processed'.
    """
    image_id: str          # UUID of the processed image
    viewer_port: int       # Port of the viewer that processed it (for routing)
    viewer_type: str       # 'napari' or 'fiji'
    status: str = 'success'  # 'success', 'error', etc.
    timestamp: float = None  # When it was processed
    error: str = None      # Error message if status='error'

    def to_dict(self):
        result = {
            MessageFields.TYPE: "image_ack",
            MessageFields.IMAGE_ID: self.image_id,
            MessageFields.VIEWER_PORT: self.viewer_port,
            MessageFields.VIEWER_TYPE: self.viewer_type,
            MessageFields.STATUS: self.status
        }
        if self.timestamp is not None:
            result[MessageFields.TIMESTAMP] = self.timestamp
        if self.error is not None:
            result[MessageFields.ERROR] = self.error
        return result

    @classmethod
    def from_dict(cls, data):
        return cls(
            image_id=data[MessageFields.IMAGE_ID],
            viewer_port=data[MessageFields.VIEWER_PORT],
            viewer_type=data[MessageFields.VIEWER_TYPE],
            status=data.get(MessageFields.STATUS, 'success'),
            timestamp=data.get(MessageFields.TIMESTAMP),
            error=data.get(MessageFields.ERROR)
        )

@dataclass(frozen=True)
class ROIMessage:
    """Message for streaming ROIs to viewers (Napari/Fiji).

    Sent via ZMQ to viewer servers to display ROIs in real-time.
    """
    rois: list  # List of ROI dictionaries with shapes and metadata
    layer_name: str = "ROIs"  # Name of the layer/overlay

    def to_dict(self):
        return {
            MessageFields.TYPE: "rois",
            MessageFields.ROIS: self.rois,
            MessageFields.LAYER_NAME: self.layer_name
        }

    @classmethod
    def from_dict(cls, data):
        return cls(
            rois=data[MessageFields.ROIS],
            layer_name=data.get(MessageFields.LAYER_NAME, "ROIs")
        )


@dataclass(frozen=True)
class ShapesMessage:
    """Message for Napari shapes layer.

    Napari-specific format for displaying polygon/ellipse shapes.
    """
    shapes: list  # List of shape dictionaries with type, coordinates, metadata
    layer_name: str = "ROIs"

    def to_dict(self):
        return {
            MessageFields.TYPE: "shapes",
            MessageFields.SHAPES: self.shapes,
            MessageFields.LAYER_NAME: self.layer_name
        }

    @classmethod
    def from_dict(cls, data):
        return cls(
            shapes=data[MessageFields.SHAPES],
            layer_name=data.get(MessageFields.LAYER_NAME, "ROIs")
        )


