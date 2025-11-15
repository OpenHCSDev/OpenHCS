# plan_01_dynamic_function_registration.md
## Component: Dynamic Function Registration via Code Editor

### Objective
Enable users to define custom processing functions directly in the code editor and have them automatically registered in the OpenHCS function registry, making them immediately available in function selector dialogs and usable in pipeline steps.

### Plan

#### 1. Create Custom Function Template System
**File**: `openhcs/processing/custom_functions/templates.py` (new)

Create a template system that provides starter code for custom functions:
- Default template with `@numpy` decorator
- Templates for each memory type (`@cupy`, `@torch`, etc.)
- Include proper imports and docstring examples
- Show signature requirements (first param must be `image`)
- Include example of special outputs (optional return values)

**Template structure**:
```python
NUMPY_TEMPLATE = """from openhcs.core.memory.decorators import numpy

@numpy
def my_custom_function(image, param1=1.0, param2=2.0):
    \"\"\"
    Custom image processing function.
    
    Args:
        image: Input image (3D numpy array)
        param1: First parameter
        param2: Second parameter
        
    Returns:
        Processed image (3D numpy array)
    \"\"\"
    # Your processing code here
    # Example: simple scaling
    return image * param1 + param2
"""
```

#### 2. Create Custom Function Manager Service
**File**: `openhcs/processing/custom_functions/manager.py` (new)

Implement a service to manage custom function lifecycle:
- **Register function from code**: Execute code, extract decorated functions, call `register_function()`
- **Validate function**: Check for required attributes (`input_memory_type`, `output_memory_type`)
- **Persist to disk**: Save custom functions to `~/.local/share/openhcs/custom_functions/`
- **Load on startup**: Auto-load all custom functions from storage directory
- **List custom functions**: Return all registered custom functions
- **Delete custom function**: Remove from registry and delete file

**Key methods**:
```python
class CustomFunctionManager:
    def __init__(self):
        self.storage_dir = get_data_file_path("custom_functions")
        self.storage_dir.mkdir(parents=True, exist_ok=True)
    
    def register_from_code(self, code: str, persist: bool = True) -> List[Callable]:
        """Execute code and register all decorated functions found."""
        
    def load_all_custom_functions(self) -> int:
        """Load all .py files from storage directory."""
        
    def delete_custom_function(self, func_name: str) -> bool:
        """Remove function from registry and delete file."""
        
    def list_custom_functions(self) -> List[Dict[str, Any]]:
        """Return metadata for all custom functions."""
```

**Implementation details**:
- Use `exec()` with controlled namespace containing all decorators
- Scan namespace after exec for functions with memory type attributes
- Call `openhcs.processing.func_registry.register_function()` for each
- Save code to `~/.local/share/openhcs/custom_functions/<function_name>.py`
- Clear `RegistryService._metadata_cache` and `FunctionSelectorDialog._metadata_cache` after registration

#### 3. Add "Custom Function" Button to Function Selector Dialog
**File**: `openhcs/pyqt_gui/dialogs/function_selector_dialog.py`

Modify `FunctionSelectorDialog.setup_ui()`:
- Add "Custom Function" button next to "Select" and "Cancel" buttons
- Connect to `self.action_create_custom_function()`
- Button should be always enabled (not dependent on selection)

**Button layout** (in `setup_ui()` method around line 450):
```python
button_layout = QHBoxLayout()
button_layout.addStretch()

# Add Custom Function button
custom_btn = QPushButton("Custom Function")
button_layout.addWidget(custom_btn)

self.select_btn = QPushButton("Select")
self.select_btn.setEnabled(False)
self.select_btn.setDefault(True)
button_layout.addWidget(self.select_btn)

cancel_btn = QPushButton("Cancel")
button_layout.addWidget(cancel_btn)

button_layout.addStretch()
layout.addLayout(button_layout)
```

**Connect signal**:
```python
custom_btn.clicked.connect(self.action_create_custom_function)
```

#### 4. Implement Custom Function Creation Workflow
**File**: `openhcs/pyqt_gui/dialogs/function_selector_dialog.py`

Add method `action_create_custom_function()`:
- Create `CustomFunctionManager` instance
- Get template from template system (default: numpy)
- Open code editor with template
- Callback validates and registers function
- Refresh function list on success

**Implementation**:
```python
def action_create_custom_function(self):
    """Open code editor to create custom function."""
    from openhcs.processing.custom_functions.templates import get_default_template
    from openhcs.processing.custom_functions.manager import CustomFunctionManager
    from openhcs.pyqt_gui.services.simple_code_editor import SimpleCodeEditorService
    
    manager = CustomFunctionManager()
    template = get_default_template()
    
    editor_service = SimpleCodeEditorService(self)
    
    def handle_custom_function_code(edited_code: str):
        """Callback to register custom function."""
        try:
            # Register function(s) from code
            registered_funcs = manager.register_from_code(edited_code, persist=True)
            
            if not registered_funcs:
                raise ValueError("No valid functions found in code. "
                               "Functions must be decorated with @numpy, @cupy, etc.")
            
            # Clear caches to force refresh
            FunctionSelectorDialog.clear_metadata_cache()
            
            # Reload function data
            self._load_function_data()
            self.populate_module_tree()
            self.populate_function_table()
            
            # Show success message
            func_names = [f.__name__ for f in registered_funcs]
            from PyQt6.QtWidgets import QMessageBox
            QMessageBox.information(
                self,
                "Success",
                f"Registered {len(registered_funcs)} custom function(s):\n" + 
                "\n".join(f"  • {name}" for name in func_names)
            )
            
        except Exception as e:
            # Re-raise so code editor shows error and keeps dialog open
            raise
    
    editor_service.edit_code(
        initial_content=template,
        title="Create Custom Function",
        callback=handle_custom_function_code,
        use_external=False
    )
```

#### 5. Auto-load Custom Functions on Startup
**File**: `openhcs/processing/func_registry.py`

Modify `_auto_initialize_registry()` to load custom functions after standard registry initialization:

**Add after line 255** (after RegistryService loading):
```python
# Phase 2: Load custom functions from user storage
try:
    from openhcs.processing.custom_functions.manager import CustomFunctionManager
    manager = CustomFunctionManager()
    num_loaded = manager.load_all_custom_functions()
    if num_loaded > 0:
        logger.info(f"Loaded {num_loaded} custom functions from storage")
except Exception as e:
    logger.warning(f"Failed to load custom functions: {e}")
```

#### 6. Add Custom Function Management UI (Optional Enhancement)
**File**: `openhcs/pyqt_gui/dialogs/custom_function_manager_dialog.py` (new)

Create a dialog to manage custom functions:
- List all custom functions with metadata
- Edit existing custom function (opens code editor)
- Delete custom function
- Export/import custom functions

This is optional and can be added later. For MVP, just having the "Custom Function" button in the selector is sufficient.

### Findings

#### Existing Infrastructure (Verified)

1. **Function Registry** (`openhcs/processing/func_registry.py`):
   - `register_function(func, backend=None)` - public API exists (line 412)
   - Validates `input_memory_type` and `output_memory_type` attributes (line 433-446)
   - Thread-safe with `_registry_lock` (line 428)
   - Auto-initializes if needed (line 430-431)
   - Registers to `FUNC_REGISTRY[registry_name]` (line 454)

2. **Memory Type Decorators** (`openhcs/core/memory/decorators.py`):
   - Auto-generated for all memory types: `numpy`, `cupy`, `torch`, `tensorflow`, `jax`, `pyclesperanto` (line 372-375)
   - Each decorator adds `input_memory_type` and `output_memory_type` attributes (line 346-349)
   - Include dtype preservation, GPU stream management, OOM recovery (line 352-356)
   - Available in global namespace after import

3. **Code Editor** (`openhcs/pyqt_gui/services/simple_code_editor.py`):
   - `SimpleCodeEditorService.edit_code()` method exists (line 51-70)
   - Executes callback with edited content (line 849-853)
   - Error handling with line number extraction (line 856-872)
   - Keeps dialog open on error for user to fix (line 874-876)
   - QScintilla support with syntax highlighting (line 79-84)

4. **Registry Service** (`openhcs/processing/backends/lib_registry/registry_service.py`):
   - `RegistryService.get_all_functions_with_metadata()` - returns Dict[str, FunctionMetadata] (line 26)
   - `RegistryService.clear_metadata_cache()` - clears cache (line 71-74)
   - Uses composite keys: `"backend:function_name"` (line 57)
   - Caches in `_metadata_cache` class variable (line 23)

5. **Function Selector Dialog** (`openhcs/pyqt_gui/dialogs/function_selector_dialog.py`):
   - `FunctionSelectorDialog._metadata_cache` - class-level cache (line 117)
   - `FunctionSelectorDialog.clear_metadata_cache()` - clears both caches (line 358-362)
   - `_load_function_data()` - loads from RegistryService (line 149-195)
   - `populate_module_tree()` - rebuilds tree view (line 197-208)
   - `populate_function_table()` - rebuilds table view (line 489-529)
   - Button layout in `setup_ui()` around line 450-463

6. **XDG Paths** (`openhcs/core/xdg_paths.py`):
   - `get_data_file_path(filename)` - returns Path in `~/.local/share/openhcs/` (line 240-261)
   - Auto-creates directories (line 27-29)
   - Handles migration from legacy locations (line 252-259)

7. **FunctionMetadata Structure** (`openhcs/processing/backends/lib_registry/unified_registry.py`):
   - Frozen dataclass with fields: `name`, `func`, `contract`, `registry`, `module`, `doc`, `tags`, `original_name` (line 70-82)
   - `get_memory_type()` method returns actual backend (line 84-100)
   - `get_registry_name()` method returns registry source

#### Execution Pattern (Verified)

The code editor already uses `exec()` pattern in multiple places:
- `openhcs/runtime/execution_server.py` line 290: `exec(pipeline_code, namespace)`
- `openhcs/runtime/zmq_execution_server.py` line 274: `exec(pipeline_code, namespace)`
- `openhcs/pyqt_gui/widgets/pipeline_editor.py` line 730: `exec(edited_code, namespace)`
- `openhcs/pyqt_gui/widgets/function_list_editor.py` line 402: `exec(edited_code, namespace)`

Pattern is consistent:
1. Create empty namespace dict
2. Execute code with `exec(code, namespace)`
3. Extract expected variable from namespace (e.g., `namespace['pipeline_steps']`)
4. Validate and use the result

### Implementation Draft

(Code will be added here after plan approval via smell loop)

