# Performance Bottleneck Analysis: Why is Widget Creation Slow?

## Executive Summary

**The "baseline" is slow because:**
1. We're using **magicgui** to create widgets, which does heavy introspection (~30-40ms per widget)
2. We're creating **entire nested form hierarchies**, not just individual widgets
3. The **"Analyze form structure" phase (493ms)** is the biggest bottleneck - recursive analysis isn't cached

## Detailed Breakdown

### Question 1: Why can't widgets be cached before first load?

**Answer: They CAN be! We should pre-cache at module import time.**

Currently, caching only happens after the first widget is created. We could:

```python
# In openhcs/core/config.py at module level:
def _precache_config_types():
    """Pre-cache all config type analysis at import time."""
    from openhcs.ui.shared.parameter_form_cache import get_parameter_analysis_cache
    from openhcs.ui.shared.unified_parameter_analyzer import UnifiedParameterAnalyzer
    
    cache = get_parameter_analysis_cache()
    
    # Cache all config types
    config_types = [
        GlobalPipelineConfig,
        PipelineConfig,
        WellFilterConfig,
        ZarrConfig,
        VFSConfig,
        PathPlanningConfig,
        StepMaterializationConfig,
        # ... all other config types
    ]
    
    for config_type in config_types:
        UnifiedParameterAnalyzer.analyze(config_type)
        # This populates the cache before any UI is created

# Call at module level
_precache_config_types()
```

**Impact**: First load would be as fast as second load (~200ms instead of 1300ms)

### Question 2: Why is it 60ms per field?

**Answer: magicgui is slow. Each widget creation involves:**

1. **magicgui.create_widget()**: ~30-40ms
   - Type introspection
   - Annotation parsing
   - Widget type resolution
   - Signal setup
   - Style application

2. **Our wrapper code**: ~20-30ms
   - Container creation (QWidget + QHBoxLayout)
   - LabelWithHelp creation (label + help button)
   - Reset button creation
   - Signal connections
   - Placeholder behavior setup

**Total: ~60ms per field**

For WellFilterConfig with 2 fields:
- 2 fields × 60ms = 120ms
- Plus GroupBox wrapper: ~20ms
- **Total: ~140ms** ✓ (matches observed 141ms)

## The Real Bottleneck: "Analyze Form Structure" (493ms)

This is where `ParameterFormService.analyze_parameters()` recursively analyzes nested dataclasses:

```python
def analyze_parameters(...):
    for param_name, param_type in parameter_types.items():
        # ... 
        if param_info.is_nested:
            # SLOW: Calls UnifiedParameterAnalyzer.analyze() for each nested config
            nested_param_info = UnifiedParameterAnalyzer.analyze(current_value)
            
            # SLOW: Recursively analyzes nested structure
            nested_structure = self.analyze_parameters(
                nested_params, nested_types, nested_field_id, ...
            )
```

**Why is it slow even with caching?**
- The `FormStructure` result itself isn't cached, only the `UnifiedParameterAnalyzer` results
- Recursive calls to `analyze_parameters()` rebuild the structure every time
- Each recursion does type checking, field extraction, etc.

## Solutions

### Solution 1: Pre-cache at Import Time (Easy Win)

**Impact**: 1300ms → 200ms first load
**Effort**: Low
**Implementation**:

```python
# openhcs/core/config.py
_CONFIG_TYPES_TO_PRECACHE = [
    GlobalPipelineConfig, PipelineConfig, WellFilterConfig,
    ZarrConfig, VFSConfig, PathPlanningConfig, StepMaterializationConfig,
    StepWellFilterConfig, NapariStreamingConfig, FijiStreamingConfig,
    # ... all config types
]

def _precache_all_configs():
    """Pre-cache analysis for all config types at import time."""
    from openhcs.ui.shared.unified_parameter_analyzer import UnifiedParameterAnalyzer
    for config_type in _CONFIG_TYPES_TO_PRECACHE:
        try:
            UnifiedParameterAnalyzer.analyze(config_type)
        except Exception:
            pass  # Ignore errors during pre-caching

# Call at module level (runs once at import)
_precache_all_configs()
```

### Solution 2: Cache FormStructure Results (Medium Win)

**Impact**: 493ms → ~50ms for "Analyze form structure"
**Effort**: Medium
**Implementation**:

```python
# openhcs/ui/shared/parameter_form_cache.py

class FormStructureCache:
    """Cache complete FormStructure results."""
    
    def __init__(self):
        self._cache: Dict[Tuple[int, str], FormStructure] = {}
    
    def get_cache_key(self, dataclass_type: Type, field_id: str) -> Tuple[int, str]:
        return (id(dataclass_type), field_id)
    
    def get(self, dataclass_type: Type, field_id: str) -> Optional[FormStructure]:
        return self._cache.get(self.get_cache_key(dataclass_type, field_id))
    
    def set(self, dataclass_type: Type, field_id: str, structure: FormStructure):
        self._cache[self.get_cache_key(dataclass_type, field_id)] = structure

# In ParameterFormService.analyze_parameters():
def analyze_parameters(self, parameters, parameter_types, field_id, ...):
    # Check cache first
    cache_key = (id(parent_dataclass_type), field_id)
    cached = _form_structure_cache.get(parent_dataclass_type, field_id)
    if cached is not None:
        return cached
    
    # ... existing analysis code ...
    
    # Cache result
    _form_structure_cache.set(parent_dataclass_type, field_id, structure)
    return structure
```

### Solution 3: Replace magicgui with Direct Widget Creation (Big Win)

**Impact**: 60ms → ~10ms per field (6x faster)
**Effort**: High
**Implementation**:

Replace magicgui with direct Qt widget creation:

```python
# Instead of:
widget = create_widget(annotation=resolved_type, value=magicgui_value)

# Use direct creation:
DIRECT_WIDGET_CREATORS = {
    int: lambda value: NoScrollSpinBox(value=value or 0),
    float: lambda value: NoScrollDoubleSpinBox(value=value or 0.0),
    str: lambda value: NoneAwareLineEdit(value=value),
    bool: lambda value: NoneAwareCheckBox(checked=value or False),
    Path: lambda value: EnhancedPathWidget(path=value),
}

def create_widget_direct(param_type: Type, value: Any) -> QWidget:
    creator = DIRECT_WIDGET_CREATORS.get(param_type)
    if creator:
        return creator(value)
    # Fallback to magicgui for complex types
    return create_widget(annotation=param_type, value=value)
```

### Solution 4: Lazy Widget Creation (Biggest Win)

**Impact**: Only create widgets for visible sections
**Effort**: Very High
**Implementation**:

Only create widgets when GroupBox is expanded:

```python
class LazyGroupBox(QGroupBox):
    """GroupBox that only creates child widgets when expanded."""
    
    def __init__(self, widget_factory: Callable):
        super().__init__()
        self._widget_factory = widget_factory
        self._widgets_created = False
        self.toggled.connect(self._on_toggled)
    
    def _on_toggled(self, checked: bool):
        if checked and not self._widgets_created:
            # Create widgets on first expand
            widget = self._widget_factory()
            self.layout().addWidget(widget)
            self._widgets_created = True
```

## Recommended Implementation Order

1. **Pre-cache at import time** (Easy, 6x speedup on first load)
2. **Cache FormStructure results** (Medium, 10x speedup on analysis phase)
3. **Replace magicgui for simple types** (High effort, 6x speedup on widget creation)
4. **Lazy widget creation** (Very high effort, only create what's visible)

## Expected Results

### Current Performance:
- First load: 1346ms
- Second load: 228ms

### After Solution 1 (Pre-caching):
- First load: ~250ms (same as second load)
- Second load: ~228ms

### After Solutions 1 + 2 (Pre-caching + FormStructure cache):
- First load: ~100ms
- Second load: ~80ms

### After Solutions 1 + 2 + 3 (+ Direct widget creation):
- First load: ~50ms
- Second load: ~40ms

### After All Solutions (+ Lazy creation):
- First load: ~20ms (only visible widgets)
- Expand nested section: ~10ms per section

