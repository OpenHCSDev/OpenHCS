"""
Helpers for generating stable scope tokens for ObjectState hierarchy nodes.

Used to avoid cross-window collisions when multiple child editors share the
same scope prefix (e.g., steps, nested functions).
"""

from __future__ import annotations

import logging
from typing import Iterable, Optional, Any, Set

logger = logging.getLogger(__name__)


class ScopeTokenGenerator:
    """Generate unique, human-readable scope tokens with an optional attribute store.

    - If attr_name is provided and the target object allows attribute assignment,
      tokens are persisted on the object (e.g., FunctionStep._pipeline_scope_token).
    - Tracks seen tokens to avoid collisions when objects already carry tokens
      (e.g., after deserialization).
    """

    def __init__(self, prefix: str, attr_name: Optional[str] = None):
        self.prefix = prefix
        self.attr_name = attr_name
        self._counter: int = 0
        self._used_tokens: Set[str] = set()

    # ---------- Seeding ----------
    def seed_from_tokens(self, tokens: Iterable[str]) -> None:
        """Prime the generator with existing tokens (keeps counter ahead of them)."""
        for token in tokens or []:
            if not token:
                continue
            self._register_existing(token)

    def seed_from_objects(self, objects: Iterable[Any]) -> None:
        """Seed from objects that may already carry tokens on attr_name."""
        if not self.attr_name:
            return
        for obj in objects or []:
            try:
                token = getattr(obj, self.attr_name, None)
            except Exception:
                token = None
            if token:
                self._register_existing(token)

    # ---------- Public API ----------
    def ensure(self, obj: Optional[Any] = None) -> str:
        """Return an existing token on obj or generate a new one."""
        existing = self._get_existing(obj)
        if existing:
            self._register_existing(existing)
            return existing

        token = self._generate_new()
        self._attach(obj, token)
        return token

    def transfer(self, source: Any, target: Any) -> str:
        """Copy source token to target (or generate a new one for target)."""
        token = self._get_existing(source)
        if not token:
            token = self.ensure(target)
            return token

        self._register_existing(token)
        self._attach(target, token)
        return token

    def normalize(self, objects: Iterable[Any]) -> None:
        """Ensure every object in a list has a token."""
        for obj in objects or []:
            self.ensure(obj)

    # ---------- Internals ----------
    def _get_existing(self, obj: Optional[Any]) -> Optional[str]:
        if obj is None or not self.attr_name:
            return None
        try:
            token = getattr(obj, self.attr_name, None)
        except Exception:
            token = None
        return token

    def _attach(self, obj: Optional[Any], token: str) -> None:
        if obj is None or not self.attr_name:
            return
        try:
            setattr(obj, self.attr_name, token)
        except Exception as exc:  # pragma: no cover - best-effort
            logger.debug(f"ScopeTokenGenerator: could not attach token to {obj}: {exc}")

    def _register_existing(self, token: str) -> None:
        if token in self._used_tokens:
            return
        self._used_tokens.add(token)
        self._bump_counter(token)

    def _bump_counter(self, token: str) -> None:
        prefix = f"{self.prefix}_"
        if token.startswith(prefix):
            suffix = token[len(prefix) :]
            if suffix.isdigit():
                self._counter = max(self._counter, int(suffix) + 1)

    def _generate_new(self) -> str:
        token = f"{self.prefix}_{self._counter}"
        while token in self._used_tokens:
            self._counter += 1
            token = f"{self.prefix}_{self._counter}"
        self._used_tokens.add(token)
        self._counter += 1
        return token
