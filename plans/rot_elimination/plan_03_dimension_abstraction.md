# plan_03_dimension_abstraction.md
## Component: Fiji Viewer Dimension Abstraction

### Objective
Eliminate the 103 references to `channel_components`, `slice_components`, `frame_components` triplication in `fiji_viewer_server.py`. Replace with ONE generic dimension abstraction.

### Findings

**Current Rot — Same Pattern 6+ Times:**

```python
# Pattern appears at lines 778-780, 798-800, 909-911, 1078-1096, 1199-1215, 1342+
c_key = tuple(meta[comp] for comp in channel_components) if channel_components else ()
z_key = tuple(meta[comp] for comp in slice_components) if slice_components else ()
t_key = tuple(meta[comp] for comp in frame_components) if frame_components else ()
```

```python
# Pattern appears at lines 1078-1102
if channel_components and channel_values:
    current_channel = imp.getChannel()
    if 0 < current_channel <= len(channel_values):
        channel_tuple = channel_values[current_channel - 1]
        for comp_idx, comp_name in enumerate(channel_components):
            # ...
if slice_components and slice_values:  # SAME PATTERN
if frame_components and frame_values:  # SAME PATTERN
```

**Method Signatures Are Unreadable:**
```python
def _add_slices_to_existing_hyperstack(
    self, existing_imp, new_images: List[Dict[str, Any]],
    window_key: str, 
    channel_components: List[str],     # ← Dimension 1
    slice_components: List[str],       # ← Dimension 2  
    frame_components: List[str],       # ← Dimension 3
    display_config_dict: Dict[str, Any],
    channel_values: List[tuple] = None,  # ← Dimension 1 values
    slice_values: List[tuple] = None,    # ← Dimension 2 values
    frame_values: List[tuple] = None,    # ← Dimension 3 values
):
```

Six parallel parameters for three dimensions!

### Plan

**Phase 1: Dimension Dataclass**

```python
@dataclass
class HyperstackDimension:
    """A single dimension of a hyperstack (channel, slice, or frame)."""
    name: str  # "channel", "slice", or "frame"
    components: List[str]  # Component names mapped to this dimension
    values: List[tuple]  # Unique value tuples for this dimension
    
    def build_key(self, metadata: Dict[str, Any]) -> tuple:
        """Build coordinate key from metadata."""
        return tuple(metadata[comp] for comp in self.components) if self.components else ()
    
    def get_index(self, metadata: Dict[str, Any]) -> int:
        """Get 0-based index for metadata coordinates."""
        key = self.build_key(metadata)
        try:
            return self.values.index(key)
        except ValueError:
            return -1
```

**Phase 2: Dimension Container**

```python
@dataclass  
class HyperstackDimensions:
    """All three dimensions of a hyperstack."""
    channel: HyperstackDimension
    slice: HyperstackDimension
    frame: HyperstackDimension
    
    def build_coord_key(self, metadata: Dict[str, Any]) -> Tuple[tuple, tuple, tuple]:
        """Build full (C, Z, T) coordinate key."""
        return (
            self.channel.build_key(metadata),
            self.slice.build_key(metadata),
            self.frame.build_key(metadata),
        )
    
    def __iter__(self):
        """Iterate over dimensions for generic processing."""
        return iter([self.channel, self.slice, self.frame])
```

**Phase 3: Simplify Method Signatures**

```python
# BEFORE: 6 parameters for dimensions
def _add_slices_to_existing_hyperstack(
    self, existing_imp, new_images,
    window_key, channel_components, slice_components, frame_components,
    display_config_dict, channel_values, slice_values, frame_values
):

# AFTER: 1 parameter
def _add_slices_to_existing_hyperstack(
    self, existing_imp, new_images,
    window_key, dimensions: HyperstackDimensions,
    display_config_dict
):
```

**Phase 4: Replace Triplicated Logic**

```python
# BEFORE: Same pattern 3x
c_key = tuple(meta[comp] for comp in channel_components) if channel_components else ()
z_key = tuple(meta[comp] for comp in slice_components) if slice_components else ()
t_key = tuple(meta[comp] for comp in frame_components) if frame_components else ()

# AFTER: Generic
c_key, z_key, t_key = dimensions.build_coord_key(meta)
```

```python
# BEFORE: Same pattern 3x
if channel_components and channel_values:
    current = imp.getChannel()
    # ... 8 lines of logic ...
if slice_components and slice_values:
    current = imp.getSlice()
    # ... 8 lines of logic ...
if frame_components and frame_values:
    current = imp.getFrame()
    # ... 8 lines of logic ...

# AFTER: Generic loop
dimension_getters = {
    'channel': imp.getChannel,
    'slice': imp.getSlice,
    'frame': imp.getFrame,
}
for dim in dimensions:
    if dim.components and dim.values:
        current = dimension_getters[dim.name]()
        if 0 < current <= len(dim.values):
            # ... 4 lines of generic logic ...
```

### Structural Properties

- **No triplication** — Each dimension pattern appears exactly once
- **Single source of truth** — `HyperstackDimension` defines dimension behavior
- **Generic iteration** — Loop over dimensions instead of copy-paste
- **Readable signatures** — `dimensions: HyperstackDimensions` replaces 6 parameters

### Cleanup — DELETE ALL OF THIS

**Patterns to DELETE from `fiji_viewer_server.py` (103 occurrences):**
```python
# DELETE all 6+ copies of this:
c_key = tuple(meta[comp] for comp in channel_components) if channel_components else ()
z_key = tuple(meta[comp] for comp in slice_components) if slice_components else ()
t_key = tuple(meta[comp] for comp in frame_components) if frame_components else ()

# DELETE all 6+ copies of this:
if channel_components and channel_values:
    current = imp.getChannel()
    # ... logic ...
if slice_components and slice_values:
    current = imp.getSlice()
    # ... logic ...
if frame_components and frame_values:
    current = imp.getFrame()
    # ... logic ...
```

**Parameters to DELETE from method signatures:**
```python
# DELETE these 6 separate parameters:
channel_components: List[str], slice_components: List[str], frame_components: List[str],
channel_values: List[tuple], slice_values: List[tuple], frame_values: List[tuple]

# REPLACE with 1 parameter:
dimensions: HyperstackDimensions
```

**No wrappers. No backwards compatibility.**
- All triplicated patterns → replaced by single generic implementation
- All 6-parameter signatures → replaced by 1 `dimensions` parameter
- If internal code uses the old patterns, it breaks — update to use `HyperstackDimensions`

### Implementation Draft

(After smell loop approval)

