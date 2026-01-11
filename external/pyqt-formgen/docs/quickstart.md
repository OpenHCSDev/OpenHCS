# Quick Start

## Installation

```bash
pip install pyqt-formgen
```

## Basic Form from Dataclass

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

## With ObjectState Integration

```python
from dataclasses import dataclass
from objectstate import ObjectState
from pyqt_formgen.forms import ParameterFormManager, FormManagerConfig

@dataclass
class MyConfig:
    name: str = "default"
    count: int = 10

# Create ObjectState-backed form
state = ObjectState(MyConfig)
config = FormManagerConfig(state=state)
form = ParameterFormManager(MyConfig, config=config)
```
