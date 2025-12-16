"""
Snapshot and Timeline dataclasses for git-like time-travel history.

This module provides typed data structures for the ObjectStateRegistry's
time-travel system, replacing the tuple-based implementation.

Design Philosophy: Correct by Construction
- No Optional fields for required data
- Immutable snapshots (frozen dataclass)
- UUID-based identity for snapshots
- Direct attribute access (no getattr fallbacks)
"""

from dataclasses import dataclass, field
from typing import Dict, Optional, List
import uuid
import time


@dataclass(frozen=True)
class StateSnapshot:
    """Immutable snapshot of a single ObjectState's data.

    Captures the resolved values, parameters, and provenance at a point in time.
    No object references - data only for serializability.
    """
    saved_resolved: Dict
    live_resolved: Dict
    parameters: Dict  # Current concrete values
    saved_parameters: Dict  # Concrete values at last save (for concrete dirty detection)
    provenance: Dict


@dataclass(frozen=True)
class Snapshot:
    """Immutable snapshot of ALL ObjectStates at a point in time.
    
    Analogous to a git commit - captures the entire system state.
    """
    id: str  # UUID string
    timestamp: float
    label: str
    triggering_scope: Optional[str]  # scope_id that triggered the snapshot
    parent_id: Optional[str]  # UUID of parent snapshot (None for root)
    all_states: Dict[str, StateSnapshot]  # scope_id → StateSnapshot
    
    @classmethod
    def create(
        cls,
        label: str,
        all_states: Dict[str, StateSnapshot],
        triggering_scope: Optional[str] = None,
        parent_id: Optional[str] = None,
    ) -> 'Snapshot':
        """Create a new snapshot with auto-generated ID and timestamp."""
        return cls(
            id=str(uuid.uuid4()),
            timestamp=time.time(),
            label=label,
            triggering_scope=triggering_scope,
            parent_id=parent_id,
            all_states=all_states,
        )
    
    def to_dict(self) -> Dict:
        """Export to JSON-serializable dict."""
        return {
            'id': self.id,
            'timestamp': self.timestamp,
            'label': self.label,
            'triggering_scope': self.triggering_scope,
            'parent_id': self.parent_id,
            'states': {
                scope_id: {
                    'saved_resolved': ss.saved_resolved,
                    'live_resolved': ss.live_resolved,
                    'parameters': ss.parameters,
                    'saved_parameters': ss.saved_parameters,
                    'provenance': ss.provenance,
                }
                for scope_id, ss in self.all_states.items()
            }
        }
    
    @classmethod
    def from_dict(cls, data: Dict) -> 'Snapshot':
        """Import from dict (e.g., loaded from JSON)."""
        all_states = {
            scope_id: StateSnapshot(
                saved_resolved=state_data['saved_resolved'],
                live_resolved=state_data['live_resolved'],
                parameters=state_data['parameters'],
                saved_parameters=state_data.get('saved_parameters', state_data['parameters']),  # Fallback for old snapshots
                provenance=state_data['provenance'],
            )
            for scope_id, state_data in data['states'].items()
        }
        return cls(
            id=data['id'],
            timestamp=data['timestamp'],
            label=data['label'],
            triggering_scope=data['triggering_scope'],
            parent_id=data['parent_id'],
            all_states=all_states,
        )


@dataclass
class Timeline:
    """Named branch of history - analogous to a git branch.
    
    Points to a head snapshot and tracks its base (branch point).
    """
    name: str
    head_id: str  # UUID of current head snapshot
    base_id: str  # UUID of snapshot this timeline branched from
    created_at: float = field(default_factory=time.time)
    description: str = ""
    
    def to_dict(self) -> Dict:
        """Export to JSON-serializable dict."""
        return {
            'name': self.name,
            'head_id': self.head_id,
            'base_id': self.base_id,
            'created_at': self.created_at,
            'description': self.description,
        }
    
    @classmethod
    def from_dict(cls, data: Dict) -> 'Timeline':
        """Import from dict."""
        return cls(
            name=data['name'],
            head_id=data['head_id'],
            base_id=data['base_id'],
            created_at=data['created_at'],
            description=data['description'],
        )

