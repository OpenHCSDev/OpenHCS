"""
Helpers for generating stable scope tokens for ObjectState hierarchy nodes.

Used to avoid cross-window collisions when multiple child editors share the
same scope prefix (e.g., steps, nested functions).
"""

from __future__ import annotations

import logging
from typing import Iterable, Optional, Any, Set, Sequence

logger = logging.getLogger(__name__)


class ScopeTokenGenerator:
    """Generate unique, human-readable scope tokens with an optional attribute store.

    - If attr_name is provided and the target object allows attribute assignment,
      tokens are persisted on the object (e.g., FunctionStep._scope_token).
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


class ScopeTokenService:
    """Registry of ScopeTokenGenerators keyed by (parent_scope, prefix).

    Token assigned on creation, stable across reordering.
    Prefix derived from object type for readability.

    Usage:
        ScopeTokenService.build_scope_id(plate_path, step)   # → "plate::step_0"
        ScopeTokenService.build_scope_id(step_scope, func)   # → "plate::step_0::func_0"
    """
    _generators: dict[tuple[str, str], ScopeTokenGenerator] = {}

    @classmethod
    def _get_prefix(cls, obj: object) -> str:
        """Derive prefix from object type (lowercase)."""
        return type(obj).__name__.lower()

    @classmethod
    def _normalize_scope(cls, scope) -> str:
        """Normalize scope to string. Enforces the invariant: scope keys are always strings."""
        return str(scope) if scope is not None else ""

    @classmethod
    def get_generator(cls, parent_scope, prefix: str) -> ScopeTokenGenerator:
        parent_scope = cls._normalize_scope(parent_scope)
        key = (parent_scope, prefix)
        if key not in cls._generators:
            cls._generators[key] = ScopeTokenGenerator(prefix, '_scope_token')
            logger.debug(f"🔑 ScopeTokenService: Created generator for parent_scope={parent_scope}, prefix={prefix}")
        return cls._generators[key]

    @classmethod
    def ensure_token(cls, parent_scope, obj: object) -> str:
        parent_scope = cls._normalize_scope(parent_scope)
        prefix = cls._get_prefix(obj)
        return cls.get_generator(parent_scope, prefix).ensure(obj)

    # PERFORMANCE: Cache scope_id strings per (parent_scope, object_id)
    _scope_id_cache: dict[tuple[str, int], str] = {}

    @classmethod
    def build_scope_id(cls, parent_scope, obj: object) -> str:
        parent_scope = cls._normalize_scope(parent_scope)
        # PERFORMANCE: Check cache first
        cache_key = (parent_scope, id(obj))
        if cache_key in cls._scope_id_cache:
            return cls._scope_id_cache[cache_key]

        token = cls.ensure_token(parent_scope, obj)
        result = f"{parent_scope}::{token}"
        cls._scope_id_cache[cache_key] = result
        logger.debug(f"🔑 ScopeTokenService.build_scope_id: {result} for {type(obj).__name__}")
        return result

    @classmethod
    def seed_from_objects(cls, parent_scope, objects: Sequence[object]) -> None:
        """Seed generators from existing objects (preserves their tokens)."""
        if not objects:
            return
        parent_scope = cls._normalize_scope(parent_scope)
        # Group by type prefix
        by_prefix: dict[str, list[object]] = {}
        for obj in objects:
            prefix = cls._get_prefix(obj)
            by_prefix.setdefault(prefix, []).append(obj)
        # Seed each generator
        for prefix, objs in by_prefix.items():
            cls.get_generator(parent_scope, prefix).seed_from_objects(objs)

    @classmethod
    def clear_scope(cls, parent_scope) -> None:
        """Clear all generators for a parent scope (and nested children)."""
        parent_scope = cls._normalize_scope(parent_scope)
        keys_to_remove = [k for k in cls._generators if k[0].startswith(parent_scope)]
        for key in keys_to_remove:
            del cls._generators[key]

        # PERFORMANCE: Also clear scope_id cache for this scope
        cache_keys_to_remove = [k for k in cls._scope_id_cache if k[0].startswith(parent_scope)]
        for key in cache_keys_to_remove:
            del cls._scope_id_cache[key]

        if keys_to_remove:
            logger.debug(f"🔑 ScopeTokenService: Cleared {len(keys_to_remove)} generators for {parent_scope}")
