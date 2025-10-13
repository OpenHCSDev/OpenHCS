User Guide
==========

Under Construction
------------------

The user guide is currently being rewritten to reflect the latest OpenHCS architecture and workflows.

.. note::
   **Interface Options**: OpenHCS provides both a PyQt6 desktop GUI (recommended for local use) and a Textual TUI (for remote/SSH environments). Most documentation applies to both interfaces.

**For immediate help, use these resources**:

- :doc:`../guides/complete_examples` - Complete examples and code patterns
- :doc:`../api/index` - API reference with working examples  
- :doc:`../concepts/index` - Core concepts and architecture
- :doc:`../getting_started/getting_started` - Basic installation and setup

.. toctree::
   :maxdepth: 2
   :hidden:

   production_examples
   code_ui_editing
   dtype_conversion
   cpu_only_mode
   analysis_consolidation
   experimental_layouts
   real_time_visualization
   log_viewer

**Available Guides**:

- :doc:`real_time_visualization` - Real-time visualization with napari streaming
- :doc:`code_ui_editing` - Bidirectional editing between TUI and Python code
- :doc:`dtype_conversion` - Automatic data type conversion for GPU libraries
- :doc:`cpu_only_mode` - CPU-only mode for CI testing and deployment
- :doc:`analysis_consolidation` - Automatic analysis result consolidation
- :doc:`experimental_layouts` - Excel-based experimental design and well-to-condition mapping
- :doc:`log_viewer` - Advanced log viewing with async loading and server discovery

**Environment Configuration**:

- :doc:`cpu_only_mode` - Configure OpenHCS for CPU-only environments

**Experimental Design**:

- :doc:`experimental_layouts` - Define complex experimental layouts with biological replicates

**Data Management**:

- :doc:`analysis_consolidation` - Consolidate multi-well analysis results

**What's Coming**:

- **Interface Workflow Guide** - Complete tutorial for both GUI and TUI interfaces
- **Script Generation Guide** - How OpenHCS generates self-contained scripts
- **Integration Patterns** - Real-world usage examples and best practices
- **Performance Optimization** - GPU acceleration and large dataset handling
- **Troubleshooting Guide** - Common issues and debugging approaches

**Current Status**:

The existing user guide sections contain outdated references and examples. We're rewriting them to match the current OpenHCS architecture and provide accurate, practical guidance.

**Need Help Now?**

1. **Start with the example script** - `openhcs/debug/example_export.py`
2. **Check the API documentation** - All examples are tested and working
3. **Review the concepts** - Core architecture explanations are accurate
4. **Ask questions** - The development team is responsive to user needs

**Timeline**:

- **Phase 1**: Complete example integration ✅ **Done**
- **Phase 2**: Interface workflow documentation 🚧 **In Progress**
- **Phase 3**: Practical integration examples 📋 **Planned**
- **Phase 4**: Performance and troubleshooting guides 📋 **Planned**
