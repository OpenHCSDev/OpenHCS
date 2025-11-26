=============================
Caching Architecture
=============================

Overview
========

OpenHCS has **FIVE SEPARATE CACHING SYSTEMS** that all use token-based invalidation tied to ``ParameterFormManager._live_context_token_counter``. This document maps ALL caches, their invalidation points, and the relationships between them.

The Global Token: ``_live_context_token_counter``
==================================================

**Location**: ``openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py:274``

**Type**: Class-level integer counter (shared across all ParameterFormManager instances)

**Purpose**: Global invalidation signal - when incremented, ALL token-based caches become stale

Token Increment Locations (6 total)
------------------------------------

.. list-table::
   :header-rows: 1
   :widths: 10 30 30 30

   * - Line
     - Location
     - Trigger
     - Scope
   * - 1149
     - ``_setup_ui()``
     - Window open (root forms only)
     - Global
   * - 2187
     - ``reset_all_parameters()``
     - Reset all button
     - Global
   * - 2341
     - ``reset_parameter()``
     - Reset single parameter
     - Global
   * - 3525
     - ``_emit_cross_window_change()``
     - Nested parameter change
     - Global
   * - 4495
     - ``_emit_cross_window_change()``
     - Cross-window parameter change
     - Global
   * - 4817
     - ``_on_window_close()``
     - Window close
     - Global

**CRITICAL MISSING**: Auto-loading pipeline does NOT increment token! (Fixed in pipeline_editor.py line 872)

Cache System 1: Lazy Resolution Cache
======================================

**Location**: ``openhcs/config_framework/lazy_factory.py:133``

**Variable**: ``_lazy_resolution_cache: Dict[Tuple[str, str, int, Optional[str]], Any]``

**Cache Key**: ``(class_name, field_name, token, scope_id)``

**Purpose**: Caches resolved values for lazy dataclass fields to avoid re-resolving from global config

**Invalidation**: Automatic via token - when token changes, old cache entries are ignored (stale keys remain but aren't accessed)

**Max Size**: 10,000 entries (FIFO eviction when exceeded)

Access Pattern
--------------

- Line 305-313: Get scope_id from context for cache key
- Line 322: Check cache with scope-aware key BEFORE resolution
- Line 328: Return cached value if hit
- Line 346: Store resolved value after resolution
- Line 352-358: Evict oldest 20% if max size exceeded

**CRITICAL BUG FIXED (Nov 2025)**: Cache key previously lacked scope_id, causing cross-scope cache pollution. Values resolved with ``scope_id=None`` (during PipelineConfig context) would be cached and incorrectly returned for step-scoped resolutions that should inherit from StepWellFilterConfig. Fixed by including ``scope_id`` in cache key.

**CRITICAL BUG FIXED (earlier)**: Cache check was happening BEFORE RAW value check, causing instance values to be overridden by cached global values. Fixed by moving RAW check to line 276 (before cache check).

Cache System 2: Placeholder Text Cache
=======================================

**Location**: ``openhcs/core/lazy_placeholder_simplified.py:33``

**Variable**: ``_placeholder_text_cache: dict``

**Cache Key**: ``(dataclass_type, field_name, token)``

**Purpose**: Caches resolved placeholder text (e.g., "Pipeline default: 5") to avoid redundant resolution

**Invalidation**: Automatic via token - when token changes, cache is checked and stale entries are ignored

Access Pattern
--------------

- Line 96: Check cache before resolution
- Line 97: Return cached text if hit
- Line 153: Store resolved text after resolution

**Performance Impact**: Reduces placeholder resolution from 60ms to <1ms on cache hit

Cache System 3: Live Context Resolver Cache
============================================

**Location**: ``openhcs/config_framework/live_context_resolver.py:41-43``

**Variables**:

- ``_resolved_value_cache: Dict[Tuple, Any]`` - Caches resolved config values
- ``_merged_context_cache: Dict[Tuple, Any]`` - Caches merged context dataclass instances

**Cache Key**: ``(config_obj_id, attr_name, context_ids_tuple, token)`` for resolved values

**Purpose**: Caches expensive context stack building and resolution operations

**Invalidation**: 

- Automatic via token (stale entries ignored)
- Manual via ``clear_caches()`` method (line 267-268)

**Special Feature**: Can be disabled via ``_disable_lazy_cache`` contextvar during flash detection (historical token resolution)

Cache System 4: Unsaved Changes Cache
======================================

**Location**: ``openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py:296``

**Variable**: ``_configs_with_unsaved_changes: Dict[Tuple[Type, Optional[str]], Set[str]]``

**Cache Key**: ``(config_type, scope_id)`` → ``Set[field_names]``

**Purpose**: Type-based cache for O(1) unsaved changes detection (avoids expensive field resolution)

**Invalidation**: Token-based - cache is checked against current token, stale entries ignored

Access Pattern
--------------

- Marked when ``context_value_changed`` signal emitted
- Checked in ``check_step_has_unsaved_changes()`` for fast-path detection
- Cleared when token changes (implicit via token check)

**Performance Impact**: Reduces unsaved changes check from O(n_managers) to O(1)

Cache System 5: MRO Inheritance Cache
======================================

**Location**: ``openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`` (built at startup)

**Variable**: ``_mro_inheritance_cache: Dict[Tuple[Type, str], Set[Type]]``

**Cache Key**: ``(parent_type, field_name)`` → ``Set[child_types]``

**Purpose**: Maps parent config types to child types for inheritance-based change detection

**Invalidation**: NEVER - built once at startup via ``prewarm_config_analysis_cache()``

Access Pattern
--------------

- Built in ``_build_mro_inheritance_cache()`` during cache warming
- Used in ``_mark_config_type_with_unsaved_changes()`` to mark child types when parent changes

Other Caches (Non-Token-Based)
===============================

Path Cache
----------

**Location**: ``openhcs/core/path_cache.py``

**Purpose**: Remembers last-used directories for file dialogs

**Invalidation**: Manual via ``clear_cache()`` or file-based persistence

Metadata Cache
--------------

**Location**: ``openhcs/core/metadata_cache.py``

**Purpose**: Caches parsed microscope metadata files

**Invalidation**: File mtime-based validation

Component Keys Cache
--------------------

**Location**: ``openhcs/core/orchestrator/orchestrator.py:_component_keys_cache``

**Purpose**: Caches component keys (wells, sites, etc.) from directory scanning

**Invalidation**: Manual via ``clear_component_cache()``

Backend Instance Cache
----------------------

**Location**: ``openhcs/io/backend_registry.py:_backend_instances``

**Purpose**: Singleton cache for backend instances (Memory, Zarr, etc.)

**Invalidation**: Manual via ``cleanup_all_backends()``

Registry Cache (Auto-register)
-------------------------------

**Location**: ``openhcs/core/auto_register_meta.py``

**Purpose**: Caches discovered plugin classes

**Invalidation**: Version-based + file mtime validation

Cache Invalidation Flowchart
=============================

::

    User Action (keystroke, reset, window open/close)
        ↓
    ParameterFormManager._live_context_token_counter += 1
        ↓
        ├─→ Lazy Resolution Cache (stale entries ignored on next access)
        ├─→ Placeholder Text Cache (stale entries ignored on next access)
        ├─→ Live Context Resolver Cache (stale entries ignored on next access)
        └─→ Unsaved Changes Cache (stale entries ignored on next access)

**CRITICAL**: Token increment is the ONLY invalidation mechanism for these 4 caches. If token doesn't increment, caches return stale data!

Common Cache Issues & Debugging
================================

Issue 1: Stale Values After Pipeline Load
------------------------------------------

**Symptom**: UI shows wrong values after auto-loading pipeline

**Root Cause**: Auto-load doesn't increment token

**Fix**: Manually increment token after loading (pipeline_editor.py:872)

Issue 2: Cache Returns Global Value Instead of Instance Value
--------------------------------------------------------------

**Symptom**: Instance with explicit value shows global default

**Root Cause**: Cache check happens before RAW value check in ``__getattribute__``

**Fix**: Move RAW value check BEFORE cache check (lazy_factory.py:276)

Issue 3: Cross-Window Changes Not Reflected
--------------------------------------------

**Symptom**: Editing one window doesn't update another

**Root Cause**: Token not incremented on cross-window change

**Fix**: Ensure ``_emit_cross_window_change()`` increments token (line 4495)

Issue 4: Flash Animation Uses Wrong Token
------------------------------------------

**Symptom**: Flash detection compares wrong before/after values

**Root Cause**: LiveContextResolver uses current token, not historical

**Fix**: Disable cache via ``_disable_lazy_cache`` contextvar during flash detection

Issue 5: Sibling Inheritance Shows Wrong Values (Cross-Scope Cache Pollution)
-------------------------------------------------------------------------------

**Symptom**: When changing ``step_well_filter_config.well_filter_mode = EXCLUDE``, some siblings (``napari_streaming_config``, ``fiji_streaming_config``) correctly show EXCLUDE, but others (``step_materialization_config``, ``streaming_defaults``) still show INCLUDE.

**Root Cause**: Cache key was ``(class_name, field_name, token)`` without scope_id. Values resolved with ``scope_id=None`` (during PipelineConfig context setup) would be cached and incorrectly returned for step-scoped resolutions. The resolver with ``scope_id=None`` skips step-scoped configs due to scope filtering, falling back to ``WellFilterConfig`` which has INCLUDE. This wrong value gets cached and served to siblings.

**Fix**: Cache key is now ``(class_name, field_name, token, scope_id)`` which ensures:

- Values resolved with ``scope_id=None`` won't pollute step-scoped lookups
- Different steps with different ``scope_id`` values get separate cache entries
- Cross-scope cache pollution is prevented

**Debug**: Set ``disable_all_token_caches = True`` in ``FrameworkConfig`` - if bug disappears, it's a cache pollution issue.

Disabling Caches for Debugging
===============================

The framework provides flags to disable caching systems for debugging purposes.

Global Disable (All Caches)
----------------------------

Disable ALL token-based caches at once:

.. code-block:: python

    from openhcs.config_framework import get_framework_config

    config = get_framework_config()
    config.disable_all_token_caches = True  # Disables all 4 token-based caches

Or via environment variable:

.. code-block:: bash

    export OPENHCS_DISABLE_TOKEN_CACHES=1
    python -m openhcs.pyqt_gui.app

Selective Disable (Individual Caches)
--------------------------------------

Disable specific caches while leaving others enabled:

.. code-block:: python

    from openhcs.config_framework import get_framework_config

    config = get_framework_config()
    config.disable_lazy_resolution_cache = True       # Only disable lazy resolution cache
    config.disable_placeholder_text_cache = True      # Only disable placeholder cache
    config.disable_live_context_resolver_cache = True # Only disable live context cache
    config.disable_unsaved_changes_cache = True       # Only disable unsaved changes cache

Or via environment variables:

.. code-block:: bash

    export OPENHCS_DISABLE_LAZY_RESOLUTION_CACHE=1
    export OPENHCS_DISABLE_PLACEHOLDER_CACHE=1
    export OPENHCS_DISABLE_LIVE_CONTEXT_CACHE=1
    export OPENHCS_DISABLE_UNSAVED_CHANGES_CACHE=1

**Use Case**: If you suspect a specific cache is causing issues, disable just that cache to isolate the problem.

Debugging Commands
==================

.. code-block:: bash

    # Find all token increments
    grep -n "_live_context_token_counter += 1" openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py

    # Find all cache accesses
    grep -n "_lazy_resolution_cache" openhcs/config_framework/lazy_factory.py

    # Find all cache clears
    grep -rn "\.clear()" openhcs/config_framework/ | grep -i cache

    # Check logs for cache hits/misses
    grep "🔍 CACHE" ~/.local/share/openhcs/logs/openhcs_unified_*.log | tail -50

Performance Metrics
===================

.. list-table::
   :header-rows: 1
   :widths: 25 15 20 40

   * - Cache
     - Hit Rate
     - Miss Penalty
     - Invalidation Cost
   * - Lazy Resolution
     - ~95%
     - 5-10ms
     - O(1) token increment
   * - Placeholder Text
     - ~98%
     - 60ms
     - O(1) token increment
   * - Live Context Resolver
     - ~90%
     - 50-100ms
     - O(1) token increment
   * - Unsaved Changes
     - ~99%
     - 20-50ms
     - O(1) token increment

**Total Performance Gain**: ~50-100x speedup on cache hits vs cold resolution

