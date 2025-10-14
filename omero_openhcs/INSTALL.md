# OMERO-OpenHCS Installation Guide

## Quick Start

### 1. Install OMERO.web Plugin

```bash
cd omero_openhcs
pip install -e .
```

### 2. Configure OMERO.web

```bash
# Add to installed apps
omero config append omero.web.apps '"omero_openhcs"'

# Add to right panel plugins
omero config append omero.web.ui.right_plugins \
    '["OpenHCS", "omero_openhcs/webclient_plugins/right_plugin.js.html", "openhcs_panel"]'

# Restart OMERO.web
omero web restart
```

### 3. Start OpenHCS Execution Server

```bash
# From the openhcs repository root
python -m openhcs.runtime.execution_server \
    --omero-host localhost \
    --omero-user root \
    --omero-password omero-root-password \
    --omero-data-dir /OMERO/Files \
    --server-port 7777
```

### 4. Test the Integration

```bash
# Generate and upload synthetic plate
cd examples
python import_test_data.py

# This will output a plate ID, e.g., "Plate ID: 1"
# Browse to: http://localhost:4080/webclient/?show=plate-1
# Click the "OpenHCS" tab in the right panel
# Submit a pipeline!
```

## Architecture

```
┌─────────────────────────────────────────────────────────┐
│ OMERO.web (Browser UI)                                  │
│  └─ OpenHCS Plugin (right panel tab)                    │
└─────────────────────────────────────────────────────────┘
                        ↓ HTTP/Django
┌─────────────────────────────────────────────────────────┐
│ OMERO.server                                            │
│  ├─ Plate/Well/Image database                           │
│  └─ User authentication                                 │
└─────────────────────────────────────────────────────────┘
                        ↓ ZeroMQ (port 7777)
┌─────────────────────────────────────────────────────────┐
│ OpenHCS Execution Server                                │
│  ├─ Listens for pipeline requests                       │
│  ├─ Reads from OMERO (zero-copy)                        │
│  ├─ Executes GPU pipelines                              │
│  └─ Writes results back to OMERO                        │
└─────────────────────────────────────────────────────────┘
```

## Workflow

1. **User browses to Plate** in OMERO.web
2. **Clicks "OpenHCS" tab** in right panel
3. **Enters pipeline code** (or loads example)
4. **Clicks "Submit Pipeline"**
5. **Plugin sends request** to Django view
6. **Django view calls** RemoteOrchestrator
7. **RemoteOrchestrator sends** pipeline code to execution server
8. **Execution server**:
   - Reads plate data from OMERO
   - Compiles pipeline
   - Executes on GPU
   - Saves results to OMERO
9. **Plugin polls status** every 2 seconds
10. **User views results** in OMERO.iviewer

## Troubleshooting

### Plugin doesn't appear in right panel

```bash
# Check if app is registered
omero config get omero.web.apps

# Should include: "omero_openhcs"

# Check if plugin is registered
omero config get omero.web.ui.right_plugins

# Should include: ["OpenHCS", "omero_openhcs/webclient_plugins/right_plugin.js.html", "openhcs_panel"]

# Restart OMERO.web
omero web restart
```

### "Error Loading OpenHCS" message

- Check that execution server is running
- Check that RemoteOrchestrator can connect to localhost:7777
- Check Django logs: `omero web logs`

### Pipeline submission fails

- Check execution server logs
- Verify OMERO connection in execution server
- Verify plate ID exists in OMERO

## Development

### Running in development mode

```bash
# Install in editable mode
pip install -e .

# Start OMERO.web with debug
omero config set omero.web.debug True
omero web restart

# View logs
omero web logs
```

### Testing without OMERO.web

You can test the execution server directly:

```python
from openhcs.runtime.remote_orchestrator import RemoteOrchestrator

remote = RemoteOrchestrator(server_host='localhost', server_port=7777)

pipeline_code = """
from openhcs.processing.steps import FunctionStep
from openhcs.processing.gpu_functions import gaussian_filter

pipeline_steps = [
    FunctionStep(func=gaussian_filter, sigma=2.0)
]
"""

config_code = """
from openhcs.core.config import GlobalPipelineConfig
config = GlobalPipelineConfig()
"""

response = remote.run_remote_pipeline(
    plate_id=1,
    pipeline_code=pipeline_code,
    config_code=config_code
)

print(response)
```

## Next Steps

- Add authentication/authorization checks
- Add pipeline templates library
- Add real-time log streaming (WebSockets)
- Add result visualization in browser
- Add pipeline history/favorites
- Add batch processing (multiple plates)

