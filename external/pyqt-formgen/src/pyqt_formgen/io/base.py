"""Protocols for IO backends."""

from typing import Protocol, Any, Iterable


class DataSink(Protocol):
    """Protocol for storage backends."""

    def load(self, file_path: Any, **kwargs) -> Any:
        ...

    def save(self, data: Any, output_path: Any, **kwargs) -> None:
        ...

    def load_batch(self, file_paths: Iterable[Any], **kwargs) -> list[Any]:
        ...

    def save_batch(self, data_list: Iterable[Any], output_paths: Iterable[Any], **kwargs) -> None:
        ...

