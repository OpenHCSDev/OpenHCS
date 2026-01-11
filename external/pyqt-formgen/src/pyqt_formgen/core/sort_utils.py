"""Sorting utilities."""

import re
from typing import Iterable, List, TypeVar

T = TypeVar("T")


def natural_sort(items: Iterable[T]) -> List[T]:
    """Return a naturally sorted list for human-friendly ordering."""
    def sort_key(value: T):
        parts = re.split(r"(\\d+)", str(value))
        return [int(p) if p.isdigit() else p.lower() for p in parts]

    return sorted(list(items), key=sort_key)

