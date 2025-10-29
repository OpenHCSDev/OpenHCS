"""Auto-unpack dataclass fields to instance attributes."""
from dataclasses import fields as dataclass_fields
from typing import Any, Dict, Optional


def unpack_to_self(target: Any, source: Any, field_mapping: Optional[Dict[str, str]] = None, prefix: str = "") -> None:
    """Auto-unpack dataclass fields to instance attributes with optional renaming/prefix."""
    for field in dataclass_fields(source):
        src_name = field.name
        tgt_name = next((k for k, v in (field_mapping or {}).items() if v == src_name), f"{prefix}{src_name}")
        setattr(target, tgt_name, getattr(source, src_name))

