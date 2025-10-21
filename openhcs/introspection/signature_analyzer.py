# File: openhcs/introspection/signature_analyzer.py

import ast
import inspect
import dataclasses
import re
from typing import Any, Dict, Callable, get_type_hints, NamedTuple, Union, Optional, Type
from dataclasses import dataclass

# Lazy imports for OpenHCS-specific type resolution (optional dependency)
# These are only imported when needed for type hint resolution
_lazy_module = None
_config_module = None


def _get_openhcs_modules():
    """Lazy-load OpenHCS-specific modules for type resolution."""
    global _lazy_module, _config_module
    if _lazy_module is None:
        try:
            import openhcs.config_framework.lazy_factory as lazy_module
            import openhcs.core.config as config_module
            _lazy_module = lazy_module
            _config_module = config_module
        except ImportError:
            # If OpenHCS modules aren't available, return empty dicts
            _lazy_module = type('EmptyModule', (), {})()
            _config_module = type('EmptyModule', (), {})()
    return _lazy_module, _config_module


@dataclass(frozen=True)
class AnalysisConstants:
    """Constants for signature analysis to eliminate magic strings."""
    INIT_METHOD_SUFFIX: str = ".__init__"
    SELF_PARAM: str = "self"
    CLS_PARAM: str = "cls"
    DUNDER_PREFIX: str = "__"
    DUNDER_SUFFIX: str = "__"


# Create constants instance for use throughout the module
CONSTANTS = AnalysisConstants()


class ParameterInfo(NamedTuple):
    """Information about a parameter."""
    name: str
    param_type: type
    default_value: Any
    is_required: bool
    description: Optional[str] = None  # Add parameter description from docstring

class DocstringInfo(NamedTuple):
    """Information extracted from a docstring."""
    summary: Optional[str] = None  # First line or brief description
    description: Optional[str] = None  # Full description
    parameters: Dict[str, str] = None  # Parameter name -> description mapping
    returns: Optional[str] = None  # Return value description
    examples: Optional[str] = None  # Usage examples

class DocstringExtractor:
    """Extract structured information from docstrings."""

    @staticmethod
    def extract(target: Union[Callable, type]) -> DocstringInfo:
        """Extract docstring information from function or class.

        Args:
            target: Function, method, or class to extract docstring from

        Returns:
            DocstringInfo with parsed docstring components
        """
        if not target:
            return DocstringInfo()

        # ENHANCEMENT: Handle lazy dataclasses by extracting from their base class
        actual_target = DocstringExtractor._resolve_lazy_target(target)

        docstring = inspect.getdoc(actual_target)
        if not docstring:
            return DocstringInfo()

        # Try AST-based parsing first for better accuracy
        try:
            return DocstringExtractor._parse_docstring_ast(actual_target, docstring)
        except Exception:
            # Fall back to regex-based parsing
            return DocstringExtractor._parse_docstring(docstring)

    @staticmethod
    def _resolve_lazy_target(target: Union[Callable, type]) -> Union[Callable, type]:
        """Resolve lazy dataclass to its base class for docstring extraction.

        Lazy dataclasses are dynamically created and may not have proper docstrings.
        This method attempts to find the original base class that the lazy class
        was created from.
        """
        if not hasattr(target, '__name__'):
            return target

        # Check if this looks like a lazy dataclass (starts with "Lazy")
        if target.__name__.startswith('Lazy'):
            # Try to find the base class in the MRO
            for base in getattr(target, '__mro__', []):
                if base != target and base.__name__ != 'object':
                    # Found a base class that's not the lazy class itself
                    if not base.__name__.startswith('Lazy'):
                        return base

        return target

    @staticmethod
    def _parse_docstring_ast(target: Union[Callable, type], docstring: str) -> DocstringInfo:
        """Parse docstring using AST for more accurate extraction.

        This method uses AST to parse the source code and extract docstring
        information more accurately, especially for complex multiline descriptions.
        """
        try:
            # Get source code
            source = inspect.getsource(target)
            tree = ast.parse(source)

            # Find the function/class node
            for node in ast.walk(tree):
                if isinstance(node, (ast.FunctionDef, ast.ClassDef)):
                    if ast.get_docstring(node) == docstring:
                        return DocstringExtractor._parse_ast_docstring(node, docstring)

            # Fallback to regex parsing if AST parsing fails
            return DocstringExtractor._parse_docstring(docstring)

        except Exception:
            # Fallback to regex parsing
            return DocstringExtractor._parse_docstring(docstring)

    @staticmethod
    def _parse_ast_docstring(node: Union[ast.FunctionDef, ast.ClassDef], docstring: str) -> DocstringInfo:
        """Parse docstring from AST node with enhanced multiline support."""
        # For now, use the improved regex parser
        # This can be extended later with more sophisticated AST-based parsing
        return DocstringExtractor._parse_docstring(docstring)

    @staticmethod
    def _parse_docstring(docstring: str) -> DocstringInfo:
        """Parse a docstring into structured components with improved multiline support.

        Supports multiple docstring formats:
        - Google style (Args:, Returns:, Examples:)
        - NumPy style (Parameters, Returns, Examples)
        - Sphinx style (:param name:, :returns:)
        - Simple format (just description)

        Uses improved parsing for multiline parameter descriptions that continues
        until a blank line or new parameter/section is encountered.
        """
        lines = docstring.strip().split('\n')

        summary = None
        description_lines = []
        parameters = {}
        returns = None
        examples = None

        current_section = 'description'
        current_param = None
        current_param_lines = []

        def _finalize_current_param():
            """Finalize the current parameter description."""
            if current_param and current_param_lines:
                param_desc = '\n'.join(current_param_lines).strip()
                parameters[current_param] = param_desc
            
        for i, line in enumerate(lines):
            original_line = line
            line = line.strip()

            # Handle both Google/Sphinx style (with colons) and NumPy style (without colons)
            if line.lower() in ('args:', 'arguments:', 'parameters:'):
                _finalize_current_param()
                current_param = None
                current_param_lines = []
                current_section = 'parameters'
                if i + 1 < len(lines) and lines[i+1].strip().startswith('---'): # Skip NumPy style separator
                    continue
                continue
            elif line.lower() in ('args', 'arguments', 'parameters') and i + 1 < len(lines) and lines[i+1].strip().startswith('-'):
                # NumPy-style section headers (without colons, followed by dashes)
                _finalize_current_param()
                current_param = None
                current_param_lines = []
                current_section = 'parameters'
                continue
            elif line.lower() in ('returns:', 'return:'):
                _finalize_current_param()
                current_param = None
                current_param_lines = []
                current_section = 'returns'
                if i + 1 < len(lines) and lines[i+1].strip().startswith('---'): # Skip NumPy style separator
                    continue
                continue
            elif line.lower() in ('returns', 'return') and i + 1 < len(lines) and lines[i+1].strip().startswith('-'):
                # NumPy-style returns section
                _finalize_current_param()
                current_param = None
                current_param_lines = []
                current_section = 'returns'
                continue
            elif line.lower() in ('examples:', 'example:'):
                _finalize_current_param()
                current_param = None
                current_param_lines = []
                current_section = 'examples'
                if i + 1 < len(lines) and lines[i+1].strip().startswith('---'): # Skip NumPy style separator
                    continue
                continue
            elif line.lower() in ('examples', 'example') and i + 1 < len(lines) and lines[i+1].strip().startswith('-'):
                # NumPy-style examples section
                _finalize_current_param()
                current_param = None
                current_param_lines = []
                current_section = 'examples'
                continue

            if current_section == 'description':
                if not summary and line:
                    summary = line
                else:
                    description_lines.append(original_line) # Keep original indentation

            elif current_section == 'parameters':
                # Enhanced parameter parsing to handle multiple formats
                param_match_google = re.match(r'^(\w+):\s*(.+)', line)
                param_match_sphinx = re.match(r'^:param\s+(\w+):\s*(.+)', line)
                param_match_numpy = re.match(r'^(\w+)\s*:\s*(.+)', line)
                # New: Handle pyclesperanto-style inline parameters (param_name: type description)
                param_match_inline = re.match(r'^(\w+):\s*(\w+(?:\[.*?\])?|\w+(?:\s*\|\s*\w+)*)\s+(.+)', line)
                # New: Handle parameters that start with bullet points or dashes
                param_match_bullet = re.match(r'^[-•*]\s*(\w+):\s*(.+)', line)

                if param_match_google or param_match_sphinx or param_match_numpy or param_match_inline or param_match_bullet:
                    _finalize_current_param()

                    if param_match_google:
                        param_name, param_desc = param_match_google.groups()
                    elif param_match_sphinx:
                        param_name, param_desc = param_match_sphinx.groups()
                    elif param_match_numpy:
                        param_name, param_desc = param_match_numpy.groups()
                    elif param_match_inline:
                        param_name, param_type, param_desc = param_match_inline.groups()
                        param_desc = f"{param_type} - {param_desc}"  # Include type in description
                    elif param_match_bullet:
                        param_name, param_desc = param_match_bullet.groups()

                    current_param = param_name
                    current_param_lines = [param_desc.strip()]
                elif current_param and (original_line.startswith('    ') or original_line.startswith('\t')):
                    # Indented continuation line
                    current_param_lines.append(line)
                elif not line:
                    _finalize_current_param()
                    current_param = None
                    current_param_lines = []
                elif current_param:
                    # Non-indented continuation line (part of the same block)
                    current_param_lines.append(line)
                else:
                    # Try to parse inline parameter definitions in a single block
                    # This handles cases where parameters are listed without clear separation
                    inline_params = DocstringExtractor._parse_inline_parameters(line)
                    for param_name, param_desc in inline_params.items():
                        parameters[param_name] = param_desc
            
            elif current_section == 'returns':
                if returns is None:
                    returns = line
                else:
                    returns += '\n' + line
            
            elif current_section == 'examples':
                if examples is None:
                    examples = line
                else:
                    examples += '\n' + line

        _finalize_current_param()

        description = '\n'.join(description_lines).strip()
        if description == summary:
            description = None

        return DocstringInfo(
            summary=summary,
            description=description,
            parameters=parameters or {},
            returns=returns,
            examples=examples
        )

    @staticmethod
    def _parse_inline_parameters(line: str) -> Dict[str, str]:
        """Parse parameters from a single line containing multiple parameter definitions.

        Handles formats like:
        - "input_image: Image Input image to process. footprint: Image Structuring element..."
        - "param1: type1 description1. param2: type2 description2."
        """
        parameters = {}

        import re

        # Strategy: Use a flexible pattern that works with the pyclesperanto format
        # Pattern matches: param_name: everything up to the next param_name: or end of string
        param_pattern = r'(\w+):\s*([^:]*?)(?=\s+\w+:|$)'
        matches = re.findall(param_pattern, line)

        for param_name, param_desc in matches:
            if param_desc.strip():
                # Clean up the description (remove trailing periods, extra whitespace)
                clean_desc = param_desc.strip().rstrip('.')
                parameters[param_name] = clean_desc

        return parameters


class SignatureAnalyzer:
    """Universal analyzer for extracting parameter information from any target."""

    # Class-level cache for field documentation to avoid re-parsing
    _field_docs_cache = {}

    # Class-level cache for dataclass analysis results to avoid expensive AST parsing
    _dataclass_analysis_cache = {}
    
    @staticmethod
    def analyze(target: Union[Callable, Type, object], skip_first_param: Optional[bool] = None) -> Dict[str, ParameterInfo]:
        """Extract parameter information from any target: function, constructor, dataclass, or instance.

        Args:
            target: Function, constructor, dataclass type, or dataclass instance
            skip_first_param: Whether to skip the first parameter (after self/cls).
                            If None, auto-detects based on context:
                            - False for step constructors (all params are configuration)
                            - True for image processing functions (first param is image data)

        Returns:
            Dict mapping parameter names to ParameterInfo
        """
        if not target:
            return {}

        # Dispatch based on target type
        if inspect.isclass(target):
            if dataclasses.is_dataclass(target):
                return SignatureAnalyzer._analyze_dataclass(target)
            else:
                # Try to analyze constructor
                return SignatureAnalyzer._analyze_callable(target.__init__, skip_first_param)
        elif dataclasses.is_dataclass(target):
            # Instance of dataclass
            return SignatureAnalyzer._analyze_dataclass_instance(target)
        else:
            # Function, method, or other callable
            return SignatureAnalyzer._analyze_callable(target, skip_first_param)
    
    @staticmethod
    def _analyze_callable(callable_obj: Callable, skip_first_param: Optional[bool] = None) -> Dict[str, ParameterInfo]:
        """Extract parameter information from callable signature.

        Args:
            callable_obj: The callable to analyze
            skip_first_param: Whether to skip the first parameter (after self/cls).
                            If None, auto-detects based on context.
        """
        sig = inspect.signature(callable_obj)
        # Build comprehensive namespace for forward reference resolution
        # Start with function's globals (which contain the actual types), then add our modules as fallback
        lazy_module, config_module = _get_openhcs_modules()
        globalns = {
            **vars(lazy_module),
            **vars(config_module),
            **getattr(callable_obj, '__globals__', {})
        }

        # For OpenHCS functions, prioritize the function's actual module globals
        if hasattr(callable_obj, '__module__') and callable_obj.__module__:
            try:
                import sys
                actual_module = sys.modules.get(callable_obj.__module__)
                if actual_module:
                    # Function's module globals should take precedence for type resolution
                    globalns = {
                        **vars(lazy_module),
                        **vars(config_module),
                        **vars(actual_module)  # This overwrites with the actual module types
                    }
            except Exception:
                pass  # Fall back to original globalns

        import logging
        logger = logging.getLogger(__name__)

        try:
            type_hints = get_type_hints(callable_obj, globalns=globalns)
            logger.debug(f"🔍 SIG ANALYZER: get_type_hints succeeded for {callable_obj.__name__}: {type_hints}")
        except (NameError, AttributeError) as e:
            # If type hint resolution fails, try with just the function's original globals
            try:
                type_hints = get_type_hints(callable_obj, globalns=getattr(callable_obj, '__globals__', {}))
                logger.debug(f"🔍 SIG ANALYZER: get_type_hints with __globals__ succeeded for {callable_obj.__name__}: {type_hints}")
            except:
                # If that still fails, fall back to __annotations__ directly
                # This is critical for functions where type hints were added via docstring parsing
                # (e.g., cucim functions where _enhance_annotations_from_docstring added types)
                type_hints = getattr(callable_obj, '__annotations__', {})
                logger.debug(f"🔍 SIG ANALYZER: Fell back to __annotations__ for {callable_obj.__name__}: {type_hints}")
        except Exception as ex:
            # For any other type hint resolution errors, fall back to __annotations__
            # This ensures we don't lose type information that was added programmatically
            type_hints = getattr(callable_obj, '__annotations__', {})
            logger.debug(f"🔍 SIG ANALYZER: Exception {ex}, fell back to __annotations__ for {callable_obj.__name__}: {type_hints}")



        # Extract docstring information (with fallback for robustness)
        try:
            docstring_info = DocstringExtractor.extract(callable_obj)
        except:
            docstring_info = None

        if not docstring_info:
            docstring_info = DocstringInfo()

        parameters = {}
        param_list = list(sig.parameters.items())

        # Determine skip behavior: explicit parameter overrides auto-detection
        should_skip_first_param = (
            skip_first_param if skip_first_param is not None
            else SignatureAnalyzer._should_skip_first_parameter(callable_obj)
        )

        first_param_after_self_skipped = False

        for i, (param_name, param) in enumerate(param_list):
            # Always skip self/cls
            if param_name in (CONSTANTS.SELF_PARAM, CONSTANTS.CLS_PARAM):
                continue

            # Always skip dunder parameters (internal/reserved fields)
            if param_name.startswith(CONSTANTS.DUNDER_PREFIX) and param_name.endswith(CONSTANTS.DUNDER_SUFFIX):
                continue

            # Skip first parameter for image processing functions only
            if should_skip_first_param and not first_param_after_self_skipped:
                first_param_after_self_skipped = True
                continue

            # Handle **kwargs parameters - try to extract original function signature
            if param.kind == inspect.Parameter.VAR_KEYWORD:
                # Try to find the original function if this is a wrapper
                original_params = SignatureAnalyzer._extract_original_parameters(callable_obj)
                if original_params:
                    parameters.update(original_params)
                continue 

            from typing import Any
            param_type = type_hints.get(param_name, Any)
            default_value = param.default if param.default != inspect.Parameter.empty else None
            is_required = param.default == inspect.Parameter.empty



            # Get parameter description from docstring
            param_description = docstring_info.parameters.get(param_name) if docstring_info else None

            parameters[param_name] = ParameterInfo(
                name=param_name,
                param_type=param_type,
                default_value=default_value,
                is_required=is_required,
                description=param_description
            )

        return parameters

    @staticmethod
    def _should_skip_first_parameter(callable_obj: Callable) -> bool:
        """
        Determine if the first parameter should be skipped for any callable.

        Universal logic that works with any object:
        - Constructors (__init__ methods): don't skip (all params are configuration)
        - All other callables: skip first param (assume it's data being processed)
        """
        # Check if this is any __init__ method (constructor)
        if (hasattr(callable_obj, '__qualname__') and
            callable_obj.__qualname__.endswith(CONSTANTS.INIT_METHOD_SUFFIX)):
            return False

        # Everything else: skip first parameter
        return True

    @staticmethod
    def _extract_original_parameters(callable_obj: Callable) -> Dict[str, ParameterInfo]:
        """
        Extract parameters from the original function if this is a wrapper with **kwargs.

        This handles cases where scikit-image or other auto-registered functions
        are wrapped with (image, **kwargs) signatures.
        """
        try:
            # Check if this function has access to the original function
            # Common patterns: __wrapped__, closure variables, etc.

            # Pattern 1: Check if it's a functools.wraps wrapper
            if hasattr(callable_obj, '__wrapped__'):
                return SignatureAnalyzer._analyze_callable(callable_obj.__wrapped__)

            # Pattern 2: Check closure for original function reference
            if hasattr(callable_obj, '__closure__') and callable_obj.__closure__:
                for cell in callable_obj.__closure__:
                    if hasattr(cell.cell_contents, '__call__'):
                        # Found a callable in closure - might be the original function
                        try:
                            orig_sig = inspect.signature(cell.cell_contents)
                            # Skip if it also has **kwargs (avoid infinite recursion)
                            if any(p.kind == inspect.Parameter.VAR_KEYWORD for p in orig_sig.parameters.values()):
                                continue
                            return SignatureAnalyzer._analyze_callable(cell.cell_contents)
                        except:
                            continue

            # Pattern 3: Try to extract from function name and module
            # This is a fallback for scikit-image functions
            if hasattr(callable_obj, '__name__') and hasattr(callable_obj, '__module__'):
                func_name = callable_obj.__name__
                module_name = callable_obj.__module__

                # Try to find the original function in scikit-image
                if 'skimage' in module_name:
                    try:
                        import importlib
                        # Extract the actual module path (remove wrapper module parts)
                        if 'scikit_image_registry' in module_name:
                            # This is our wrapper, try to find the original in skimage
                            for skimage_module in ['skimage.filters', 'skimage.morphology',
                                                 'skimage.segmentation', 'skimage.feature',
                                                 'skimage.measure', 'skimage.transform',
                                                 'skimage.restoration', 'skimage.exposure']:
                                try:
                                    mod = importlib.import_module(skimage_module)
                                    if hasattr(mod, func_name):
                                        orig_func = getattr(mod, func_name)
                                        return SignatureAnalyzer._analyze_callable(orig_func)
                                except:
                                    continue
                    except:
                        pass

            return {}

        except Exception:
            return {}

    @staticmethod
    def _analyze_dataclass(dataclass_type: type) -> Dict[str, ParameterInfo]:
        """Extract parameter information from dataclass fields."""
        import logging
        logger = logging.getLogger(__name__)

        # PERFORMANCE: Check cache first to avoid expensive AST parsing
        # Use the class object itself as the key (classes are hashable and have stable identity)
        cache_key = dataclass_type
        if cache_key in SignatureAnalyzer._dataclass_analysis_cache:
            logger.info(f"✅ CACHE HIT for {dataclass_type.__name__} (id={id(dataclass_type)})")
            return SignatureAnalyzer._dataclass_analysis_cache[cache_key]

        logger.info(f"❌ CACHE MISS for {dataclass_type.__name__} (id={id(dataclass_type)}), cache has {len(SignatureAnalyzer._dataclass_analysis_cache)} entries")

        try:
            # Try to get type hints, fall back to __annotations__ if resolution fails
            try:
                type_hints = get_type_hints(dataclass_type)
            except Exception:
                # Fall back to __annotations__ for robustness
                type_hints = getattr(dataclass_type, '__annotations__', {})

            # Extract docstring information from dataclass
            docstring_info = DocstringExtractor.extract(dataclass_type)

            # Extract inline field documentation using AST
            inline_docs = SignatureAnalyzer._extract_inline_field_docs(dataclass_type)

            # ENHANCEMENT: For dataclasses modified by decorators (like GlobalPipelineConfig),
            # also extract field documentation from the field types themselves
            field_type_docs = SignatureAnalyzer._extract_field_type_docs(dataclass_type)

            parameters = {}

            for field in dataclasses.fields(dataclass_type):
                param_type = type_hints.get(field.name, str)

                # Get default value
                if field.default != dataclasses.MISSING:
                    default_value = field.default
                    is_required = False
                elif field.default_factory != dataclasses.MISSING:
                    default_value = field.default_factory()
                    is_required = False
                else:
                    default_value = None
                    is_required = True

                # Get field description from multiple sources (priority order)
                field_description = None

                # 1. Field metadata (highest priority)
                if hasattr(field, 'metadata') and 'description' in field.metadata:
                    field_description = field.metadata['description']
                # 2. Inline documentation strings (from AST parsing)
                elif field.name in inline_docs:
                    field_description = inline_docs[field.name]
                # 3. Field type documentation (for decorator-modified classes)
                elif field.name in field_type_docs:
                    field_description = field_type_docs[field.name]
                # 4. Docstring parameters (fallback)
                elif docstring_info.parameters and field.name in docstring_info.parameters:
                    field_description = docstring_info.parameters.get(field.name)
                # 5. CRITICAL FIX: Use inheritance-aware field documentation extraction
                else:
                    field_description = SignatureAnalyzer.extract_field_documentation(dataclass_type, field.name)

                parameters[field.name] = ParameterInfo(
                    name=field.name,
                    param_type=param_type,
                    default_value=default_value,
                    is_required=is_required,
                    description=field_description
                )

            # PERFORMANCE: Cache the result to avoid re-parsing
            SignatureAnalyzer._dataclass_analysis_cache[cache_key] = parameters
            return parameters

        except Exception:
            # Return empty dict on error (don't cache errors)
            return {}

    @staticmethod
    def _extract_inline_field_docs(dataclass_type: type) -> Dict[str, str]:
        """Extract inline field documentation strings using AST parsing.

        This handles multiple patterns used for field documentation:

        Pattern 1 - Next line string literal:
        @dataclass
        class Config:
            field_name: str = "default"
            '''Field description here.'''

        Pattern 2 - Same line string literal (less common):
        @dataclass
        class Config:
            field_name: str = "default"  # '''Field description'''

        Pattern 3 - Traditional docstring parameters (handled by DocstringExtractor):
        @dataclass
        class Config:
            '''
            Args:
                field_name: Field description here.
            '''
            field_name: str = "default"
        """
        try:
            import ast
            import re

            # Try to get source code - handle cases where it might not be available
            source = None
            try:
                source = inspect.getsource(dataclass_type)
            except (OSError, TypeError):
                # ENHANCEMENT: For decorator-modified classes, try multiple source file strategies
                try:
                    # Strategy 1: Try the file where the class is currently defined
                    source_file = inspect.getfile(dataclass_type)
                    with open(source_file, 'r', encoding='utf-8') as f:
                        file_content = f.read()
                    source = SignatureAnalyzer._extract_class_source_from_file(file_content, dataclass_type.__name__)

                    # Strategy 2: If that fails, try to find the original source file
                    # This handles decorator-modified classes where inspect.getfile() returns the wrong file
                    if not source:
                        try:
                            import os
                            source_dir = os.path.dirname(source_file)

                            # Try common source files in the same directory
                            candidate_files = []

                            # If the current file is lazy_config.py, try config.py
                            if source_file.endswith('lazy_config.py'):
                                candidate_files.append(os.path.join(source_dir, 'config.py'))

                            # Try other common patterns
                            for filename in os.listdir(source_dir):
                                if filename.endswith('.py') and filename != os.path.basename(source_file):
                                    candidate_files.append(os.path.join(source_dir, filename))

                            # Try each candidate file
                            for candidate_file in candidate_files:
                                if os.path.exists(candidate_file):
                                    with open(candidate_file, 'r', encoding='utf-8') as f:
                                        candidate_content = f.read()
                                    source = SignatureAnalyzer._extract_class_source_from_file(candidate_content, dataclass_type.__name__)
                                    if source:  # Found it!
                                        break
                        except Exception:
                            pass
                except Exception:
                    pass

            if not source:
                return {}

            tree = ast.parse(source)

            # Find the class definition - be more flexible with class name matching
            class_node = None
            target_class_name = dataclass_type.__name__

            # Handle cases where the class might have been renamed or modified
            for node in ast.walk(tree):
                if isinstance(node, ast.ClassDef):
                    # Try exact match first
                    if node.name == target_class_name:
                        class_node = node
                        break
                    # Also try without common prefixes/suffixes that decorators might add
                    base_name = target_class_name.replace('Lazy', '').replace('Config', '')
                    node_base_name = node.name.replace('Lazy', '').replace('Config', '')
                    if base_name and node_base_name and base_name == node_base_name:
                        class_node = node
                        break

            if not class_node:
                return {}

            field_docs = {}
            source_lines = source.split('\n')

            # Method 1: Look for field assignments followed by string literals (next line)
            for i, node in enumerate(class_node.body):
                if isinstance(node, ast.AnnAssign) and hasattr(node.target, 'id'):
                    field_name = node.target.id

                    # Check if the next node is a string literal (documentation)
                    if i + 1 < len(class_node.body):
                        next_node = class_node.body[i + 1]
                        if isinstance(next_node, ast.Expr):
                            # Handle both ast.Constant (Python 3.8+) and ast.Str (older versions)
                            if isinstance(next_node.value, ast.Constant) and isinstance(next_node.value.value, str):
                                field_docs[field_name] = next_node.value.value.strip()
                                continue
                            elif hasattr(ast, 'Str') and isinstance(next_node.value, ast.Str):
                                field_docs[field_name] = next_node.value.s.strip()
                                continue

                    # Method 2: Check for inline comments on the same line
                    # Get the line number of the field definition
                    field_line_num = node.lineno - 1  # Convert to 0-based indexing
                    if 0 <= field_line_num < len(source_lines):
                        line = source_lines[field_line_num]

                        # Look for string literals in comments on the same line
                        # Pattern: field: type = value  # """Documentation"""
                        comment_match = re.search(r'#\s*["\']([^"\']+)["\']', line)
                        if comment_match:
                            field_docs[field_name] = comment_match.group(1).strip()
                            continue

                        # Look for triple-quoted strings on the same line
                        # Pattern: field: type = value  """Documentation"""
                        triple_quote_match = re.search(r'"""([^"]+)"""|\'\'\'([^\']+)\'\'\'', line)
                        if triple_quote_match:
                            doc_text = triple_quote_match.group(1) or triple_quote_match.group(2)
                            field_docs[field_name] = doc_text.strip()

            return field_docs

        except Exception as e:
            # Return empty dict if AST parsing fails
            # Could add logging here for debugging: logger.debug(f"AST parsing failed: {e}")
            return {}

    @staticmethod
    def _extract_field_type_docs(dataclass_type: type) -> Dict[str, str]:
        """Extract field documentation from field types for decorator-modified dataclasses.

        This handles cases where dataclasses have been modified by decorators (like @auto_create_decorator)
        that inject fields from other dataclasses. In such cases, the AST parsing of the main class
        won't find documentation for the injected fields, so we need to extract documentation from
        the field types themselves.

        For example, GlobalPipelineConfig has injected fields like 'path_planning_config' of type
        PathPlanningConfig. We extract the class docstring from PathPlanningConfig to use as the
        field description.
        """
        try:
            import dataclasses

            field_type_docs = {}

            # Get all dataclass fields
            if not dataclasses.is_dataclass(dataclass_type):
                return {}

            fields = dataclasses.fields(dataclass_type)

            for field in fields:
                # Check if this field's type is a dataclass
                field_type = field.type

                # Handle Optional types
                if hasattr(field_type, '__origin__') and field_type.__origin__ is Union:
                    # Extract the non-None type from Optional[T]
                    args = field_type.__args__
                    non_none_types = [arg for arg in args if arg is not type(None)]
                    if len(non_none_types) == 1:
                        field_type = non_none_types[0]

                # If the field type is a dataclass, extract its docstring as field documentation
                if dataclasses.is_dataclass(field_type):
                    # ENHANCEMENT: Resolve lazy dataclasses to their base classes for documentation
                    resolved_field_type = SignatureAnalyzer._resolve_lazy_dataclass_for_docs(field_type)

                    docstring_info = DocstringExtractor.extract(resolved_field_type)
                    if docstring_info.summary:
                        field_type_docs[field.name] = docstring_info.summary
                    elif docstring_info.description:
                        # Use first line of description if no summary
                        first_line = docstring_info.description.split('\n')[0].strip()
                        if first_line:
                            field_type_docs[field.name] = first_line

            return field_type_docs

        except Exception as e:
            # Return empty dict if extraction fails
            return {}

    @staticmethod
    def _extract_class_source_from_file(file_content: str, class_name: str) -> Optional[str]:
        """Extract the source code for a specific class from a file.

        This method is used when inspect.getsource() fails (e.g., for decorator-modified classes)
        to extract the class definition directly from the source file.

        Args:
            file_content: The content of the source file
            class_name: The name of the class to extract

        Returns:
            The source code for the class, or None if not found
        """
        try:
            lines = file_content.split('\n')
            class_lines = []
            in_class = False
            class_indent = 0

            for line in lines:
                # Look for the class definition
                if line.strip().startswith(f'class {class_name}'):
                    in_class = True
                    class_indent = len(line) - len(line.lstrip())
                    class_lines.append(line)
                elif in_class:
                    # Check if we've reached the end of the class
                    if line.strip() and not line.startswith(' ') and not line.startswith('\t'):
                        # Non-indented line that's not empty - end of class
                        break
                    elif line.strip() and len(line) - len(line.lstrip()) <= class_indent:
                        # Line at same or less indentation than class - end of class
                        break
                    else:
                        # Still inside the class
                        class_lines.append(line)

            if class_lines:
                return '\n'.join(class_lines)
            return None

        except Exception:
            return None

    @staticmethod
    def extract_field_documentation(dataclass_type: type, field_name: str) -> Optional[str]:
        """Extract documentation for a specific field from a dataclass.

        This method tries multiple approaches to find documentation for a specific field:
        1. Inline field documentation (AST parsing)
        2. Field type documentation (for nested dataclasses)
        3. Docstring parameters
        4. Field metadata

        Args:
            dataclass_type: The dataclass type containing the field
            field_name: Name of the field to get documentation for

        Returns:
            Field documentation string, or None if not found
        """
        try:
            import dataclasses

            if not dataclasses.is_dataclass(dataclass_type):
                return None

            # ENHANCEMENT: Resolve lazy dataclasses to their base classes
            # PipelineConfig should resolve to GlobalPipelineConfig for documentation
            resolved_type = SignatureAnalyzer._resolve_lazy_dataclass_for_docs(dataclass_type)

            # Check cache first for performance
            cache_key = (resolved_type.__name__, resolved_type.__module__)
            if cache_key not in SignatureAnalyzer._field_docs_cache:
                # Extract all field documentation for this dataclass and cache it
                SignatureAnalyzer._field_docs_cache[cache_key] = SignatureAnalyzer._extract_all_field_docs(resolved_type)

            cached_docs = SignatureAnalyzer._field_docs_cache[cache_key]
            if field_name in cached_docs:
                return cached_docs[field_name]

            return None

        except Exception:
            return None

    @staticmethod
    def _resolve_lazy_dataclass_for_docs(dataclass_type: type) -> type:
        """Resolve lazy dataclasses to their base classes for documentation extraction.

        This handles the case where PipelineConfig (lazy) should resolve to GlobalPipelineConfig
        for documentation purposes.

        Args:
            dataclass_type: The dataclass type (potentially lazy)

        Returns:
            The resolved dataclass type for documentation extraction
        """
        try:
            # Check if this is a lazy dataclass by looking for common patterns
            class_name = dataclass_type.__name__

            # Handle PipelineConfig -> GlobalPipelineConfig
            if class_name == 'PipelineConfig':
                try:
                    from openhcs.core.config import GlobalPipelineConfig
                    return GlobalPipelineConfig
                except ImportError:
                    pass

            # Handle LazyXxxConfig -> XxxConfig mappings
            if class_name.startswith('Lazy') and class_name.endswith('Config'):
                try:
                    # Remove 'Lazy' prefix: LazyWellFilterConfig -> WellFilterConfig
                    base_class_name = class_name[4:]  # Remove 'Lazy'

                    # Try to import from openhcs.core.config
                    from openhcs.core import config as config_module
                    if hasattr(config_module, base_class_name):
                        return getattr(config_module, base_class_name)
                except (ImportError, AttributeError):
                    pass

            # For other lazy dataclasses, try to find the Global version
            if not class_name.startswith('Global') and class_name.endswith('Config'):
                try:
                    # Try to find GlobalXxxConfig version
                    global_class_name = f'Global{class_name}'
                    module = __import__(dataclass_type.__module__, fromlist=[global_class_name])
                    if hasattr(module, global_class_name):
                        return getattr(module, global_class_name)
                except (ImportError, AttributeError):
                    pass

            # If no resolution found, return the original type
            return dataclass_type

        except Exception:
            return dataclass_type

    @staticmethod
    def _extract_all_field_docs(dataclass_type: type) -> Dict[str, str]:
        """Extract all field documentation for a dataclass and return as a dictionary.

        This method combines all documentation extraction approaches and caches the results.

        Args:
            dataclass_type: The dataclass type to extract documentation from

        Returns:
            Dictionary mapping field names to their documentation
        """
        all_docs = {}

        try:
            import dataclasses

            # Try inline field documentation first
            inline_docs = SignatureAnalyzer._extract_inline_field_docs(dataclass_type)
            all_docs.update(inline_docs)

            # Try field type documentation (for nested dataclasses)
            field_type_docs = SignatureAnalyzer._extract_field_type_docs(dataclass_type)
            for field_name, doc in field_type_docs.items():
                if field_name not in all_docs:  # Don't overwrite inline docs
                    all_docs[field_name] = doc

            # Try docstring parameters
            docstring_info = DocstringExtractor.extract(dataclass_type)
            if docstring_info.parameters:
                for field_name, doc in docstring_info.parameters.items():
                    if field_name not in all_docs:  # Don't overwrite previous docs
                        all_docs[field_name] = doc

            # Try field metadata
            fields = dataclasses.fields(dataclass_type)
            for field in fields:
                if field.name not in all_docs:  # Don't overwrite previous docs
                    if hasattr(field, 'metadata') and 'description' in field.metadata:
                        all_docs[field.name] = field.metadata['description']

            # ENHANCEMENT: Try inheritance - check parent classes for missing field documentation
            for field in fields:
                if field.name not in all_docs:  # Only for fields still missing documentation
                    # Walk up the inheritance chain
                    for base_class in dataclass_type.__mro__[1:]:  # Skip the class itself
                        if base_class == object:
                            continue
                        if dataclasses.is_dataclass(base_class):
                            # Check if this base class has the field with documentation
                            try:
                                base_fields = dataclasses.fields(base_class)
                                base_field_names = [f.name for f in base_fields]
                                if field.name in base_field_names:
                                    # Try to get documentation from the base class
                                    inherited_doc = SignatureAnalyzer.extract_field_documentation(base_class, field.name)
                                    if inherited_doc:
                                        all_docs[field.name] = inherited_doc
                                        break  # Found documentation, stop looking
                            except Exception:
                                continue  # Try next base class

        except Exception:
            pass  # Return whatever we managed to extract

        return all_docs

    @staticmethod
    def extract_field_documentation_from_context(field_name: str, context_types: list[type]) -> Optional[str]:
        """Extract field documentation by searching through multiple dataclass types.

        This method is useful when you don't know exactly which dataclass contains
        a field, but you have a list of candidate types to search through.

        Args:
            field_name: Name of the field to get documentation for
            context_types: List of dataclass types to search through

        Returns:
            Field documentation string, or None if not found
        """
        for dataclass_type in context_types:
            if dataclass_type:
                doc = SignatureAnalyzer.extract_field_documentation(dataclass_type, field_name)
                if doc:
                    return doc
        return None

    @staticmethod
    def _analyze_dataclass_instance(instance: object) -> Dict[str, ParameterInfo]:
        """Extract parameter information from a dataclass instance."""
        try:
            # Get the type and analyze it
            dataclass_type = type(instance)
            parameters = SignatureAnalyzer._analyze_dataclass(dataclass_type)

            # Update default values with current instance values
            # For lazy dataclasses, use object.__getattribute__ to preserve None values for placeholders
            for name, param_info in parameters.items():
                if hasattr(instance, name):
                    # Check if this is a lazy dataclass that should preserve None values
                    if hasattr(instance, '_resolve_field_value'):
                        # This is a lazy dataclass - use object.__getattribute__ to get stored value
                        current_value = object.__getattribute__(instance, name)
                    else:
                        # Regular dataclass - use normal getattr
                        current_value = getattr(instance, name)

                    # Create new ParameterInfo with current value as default
                    parameters[name] = ParameterInfo(
                        name=param_info.name,
                        param_type=param_info.param_type,
                        default_value=current_value,
                        is_required=param_info.is_required,
                        description=param_info.description
                    )

            return parameters

        except Exception:
            return {}

    # Duplicate method removed - using the fixed version above
