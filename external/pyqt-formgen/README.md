# pyqt-formgen

React-quality reactive form generation framework for PyQt6.

## Overview

`pyqt-formgen` is a comprehensive UI framework for building type-safe, reactive forms with PyQt6. It provides automatic form generation from dataclasses and function signatures, with full support for lazy configuration through ObjectState integration.

Extracted from [OpenHCS](https://github.com/czbiohub/opencHCS) for general-purpose use.

## Features

- **Type-based widget creation**: Automatically generate forms from dataclasses, Pydantic models, or function signatures
- **ObjectState integration**: First-class support for lazy configuration and hierarchical inheritance
- **ABC-based protocols**: Type-safe widget contracts eliminate duck typing
- **Reactive updates**: React-style lifecycle hooks with cross-window synchronization
- **Visual feedback**: Game-engine inspired flash animation system for value changes
- **Extensible**: Clean layered architecture for custom widgets and behaviors

## Installation

```bash
pip install pyqt-formgen
```

For development:
```bash
git clone https://github.com/trissim/pyqt-formgen.git
cd pyqt-formgen
pip install -e ".[dev]"
```

## Quick Start

```python
from dataclasses import dataclass
from PyQt6.QtWidgets import QApplication
from pyqt_formgen.forms import ParameterFormManager

@dataclass
class MyConfig:
    name: str = "default"
    count: int = 10
    enabled: bool = True

app = QApplication([])
form = ParameterFormManager(MyConfig)
form.show()
app.exec()
```

## Architecture

The package is organized in layers:

- **Tier 1 (Core)**: Pure PyQt6 utilities (`pyqt_formgen.core`)
- **Tier 2 (Protocols)**: Widget ABCs and adapters (`pyqt_formgen.protocols`)
- **Tier 3 (Services)**: Reusable service layer (`pyqt_formgen.services`)
- **Tier 4 (Forms)**: ParameterFormManager (`pyqt_formgen.forms`)

Additional modules:
- **Theming**: Color schemes and styling (`pyqt_formgen.theming`)
- **Widgets**: Extended widget implementations (`pyqt_formgen.widgets`)
- **Animation**: Flash effects and visual feedback (`pyqt_formgen.animation`)

## Requirements

- Python >= 3.11
- PyQt6 >= 6.4.0
- objectstate >= 0.1.0
- python-introspect >= 0.1.0

## License

MIT License - see LICENSE file for details.

## Documentation

Full documentation available at: (TBD)

## Contributing

Contributions welcome! Please see CONTRIBUTING.md for guidelines.
