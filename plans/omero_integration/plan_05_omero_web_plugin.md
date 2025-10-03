# plan_05_omero_web_plugin.md
## Component: OMERO.web Plugin for OpenHCS Integration

### Objective
Create an OMERO.web plugin that provides a web interface for launching OpenHCS pipelines and viewing results directly from the OMERO web interface. This makes OpenHCS accessible to users who don't want to install it locally.

### Plan

1. **Create OMERO.web app structure** (`omero_openhcs/`)
   ```
   omero_openhcs/
   ├── __init__.py
   ├── urls.py              # URL routing
   ├── views.py             # View functions
   ├── templates/           # HTML templates
   │   ├── base.html
   │   ├── pipeline_list.html
   │   ├── pipeline_editor.html
   │   └── viewer.html
   ├── static/              # CSS, JS, images
   │   ├── css/
   │   ├── js/
   │   └── img/
   └── utils.py             # Helper functions
   ```

2. **Implement URL routing** (`urls.py`)
   - `/openhcs/` - main landing page
   - `/openhcs/pipelines/` - list available pipelines
   - `/openhcs/pipelines/<id>/` - pipeline details
   - `/openhcs/execute/<plate_id>/` - execute pipeline on plate
   - `/openhcs/results/<execution_id>/` - view results
   - `/openhcs/viewer/<image_id>/` - embedded viewer

3. **Implement main view** (`views.py`)
   - `index()` - landing page with quick start
   - `pipeline_list()` - list available pipeline presets
   - `pipeline_editor()` - create/edit pipelines
   - `execute_pipeline()` - send execution request to server
   - `view_results()` - display execution results
   - `embedded_viewer()` - embedded image viewer

4. **Implement pipeline execution view**
   ```python
   def execute_pipeline(request, plate_id):
       # Get OMERO connection from request
       conn = request.session['connector'].create_connection()
       
       # Get plate
       plate = conn.getObject("Plate", plate_id)
       
       # Get pipeline from form
       pipeline_id = request.POST.get('pipeline_id')
       pipeline = load_pipeline_preset(pipeline_id)
       
       # Execute remotely
       remote_orch = RemoteOrchestrator('localhost', 7777)
       execution_id = remote_orch.execute_remote(
           plate_id=plate_id,
           pipeline=pipeline,
           config=PipelineConfig(),
           viewer_port=None  # No streaming for web interface
       )
       
       # Redirect to results page
       return redirect('openhcs_results', execution_id=execution_id)
   ```

5. **Implement embedded viewer**
   - Use Vizarr (WebGL-based zarr viewer) for browser-based viewing
   - Or: Use OMERO.iviewer integration
   - Or: Custom canvas-based viewer with ZeroMQ WebSocket bridge
   - Display results alongside original images

6. **Implement pipeline preset management**
   - Store presets in database or filesystem
   - Allow users to save custom pipelines
   - Share pipelines between users
   - Version control for pipelines

7. **Implement result storage**
   - Results saved back to OMERO as new images
   - Linked to original plate/dataset
   - Tagged with processing metadata
   - Provenance tracking (pipeline, parameters, timestamp)

8. **Implement progress monitoring**
   - Poll execution server for status
   - Display progress bar
   - Show current well being processed
   - Estimate time remaining

9. **Implement authentication/authorization**
   - Use OMERO session for authentication
   - Check user permissions before execution
   - Limit concurrent executions per user
   - Resource quotas (CPU, GPU, memory)

10. **Create installation/configuration**
    - `setup.py` for pip installation
    - Configuration file for server connection
    - Integration with OMERO.web settings
    - Documentation for deployment

### Findings

#### OMERO.web Architecture

**OMERO.web** is a Django-based web application:
- Uses Django templates for HTML
- Uses Django ORM for database (optional)
- Integrates with OMERO via BlitzGateway
- Session management via OMERO sessions

**Plugin Structure**:
```python
# urls.py
from django.urls import path
from . import views

urlpatterns = [
    path('', views.index, name='openhcs_index'),
    path('execute/<int:plate_id>/', views.execute_pipeline, name='openhcs_execute'),
]

# views.py
from django.shortcuts import render
from omeroweb.webclient.decorators import login_required

@login_required()
def index(request):
    conn = request.session['connector'].create_connection()
    # ... view logic
    return render(request, 'openhcs/index.html', context)
```

**Installation**:
```bash
pip install omero-openhcs
omero config append omero.web.apps '"omero_openhcs"'
omero config append omero.web.ui.top_links '["OpenHCS", "openhcs_index"]'
```

#### Existing OMERO.web Plugins

**OMERO.iviewer** - image viewer:
- WebGL-based rendering
- Supports multi-channel, z-stacks, timepoints
- ROI drawing and measurement
- Could be extended for OpenHCS results

**OMERO.figure** - figure creation:
- Drag-and-drop interface
- Export to PDF/TIFF
- Similar UI pattern could be used for pipeline editor

**OMERO.parade** - plate browsing:
- Grid view of wells
- Filtering and sorting
- Good reference for plate-based UI

#### Web-Based Visualization Options

**Option 1: Vizarr** (recommended)
- WebGL-based zarr viewer
- Supports OME-NGFF format
- No server-side rendering needed
- Client-side performance
- GitHub: hms-dbmi/vizarr

**Option 2: OMERO.iviewer Integration**
- Reuse existing viewer
- Familiar to OMERO users
- Limited customization

**Option 3: Custom Canvas Viewer**
- Full control over rendering
- Can integrate OpenHCS-specific features
- More development effort

**Option 4: Neuroglancer**
- High-performance for large datasets
- Supports remote data sources
- Complex setup

#### Pipeline Preset Storage

**Option 1: Filesystem** (simple)
```
/opt/omero/openhcs/presets/
├── cell_segmentation.pkl
├── neurite_tracing.pkl
└── organoid_analysis.pkl
```

**Option 2: OMERO Annotations** (integrated)
- Store pipelines as OMERO file annotations
- Attach to Project/Dataset
- Share via OMERO permissions
- Version control via annotation history

**Option 3: Database** (scalable)
- Django model for pipelines
- PostgreSQL storage
- Full-text search
- User permissions

**Recommendation**: Start with filesystem, migrate to OMERO annotations.

#### Result Streaming to Web Browser

**Challenge**: ZeroMQ doesn't work directly in browser
**Solution**: WebSocket bridge

```python
# Server-side WebSocket handler
import asyncio
import websockets
import zmq

async def zmq_to_websocket(websocket, zmq_port):
    context = zmq.Context()
    subscriber = context.socket(zmq.SUB)
    subscriber.connect(f"tcp://localhost:{zmq_port}")
    subscriber.setsockopt_string(zmq.SUBSCRIBE, "")
    
    while True:
        message = subscriber.recv_json()
        await websocket.send(json.dumps(message))

# Client-side JavaScript
const ws = new WebSocket('ws://localhost:8765');
ws.onmessage = (event) => {
    const data = JSON.parse(event.data);
    updateViewer(data);
};
```

**Alternative**: Don't stream to web interface, just show final results.

#### Progress Monitoring

**Server-side**: Execution server tracks progress
```python
execution_status = {
    'execution_id': 'uuid',
    'status': 'running',
    'wells_total': 96,
    'wells_completed': 42,
    'current_well': 'E06',
    'current_step': 'Cell Segmentation',
    'started_at': '2025-10-03T10:30:00Z',
    'estimated_completion': '2025-10-03T11:15:00Z'
}
```

**Client-side**: Poll server every 2 seconds
```javascript
function updateProgress() {
    fetch(`/openhcs/status/${executionId}`)
        .then(response => response.json())
        .then(data => {
            document.getElementById('progress-bar').value = 
                data.wells_completed / data.wells_total * 100;
            document.getElementById('status-text').innerText = 
                `Processing ${data.current_well}: ${data.current_step}`;
        });
}
setInterval(updateProgress, 2000);
```

#### Authentication and Resource Management

**OMERO Session**:
- User already authenticated via OMERO.web
- Session available in `request.session['connector']`
- Use OMERO permissions for access control

**Resource Quotas**:
- Limit concurrent executions per user (e.g., 2)
- Limit total GPU time per user per day
- Priority queue (admin > power users > regular users)
- Stored in Django database or Redis

**Implementation**:
```python
from django.core.cache import cache

def can_execute(user_id):
    active_executions = cache.get(f'executions:{user_id}', 0)
    return active_executions < 2

def start_execution(user_id, execution_id):
    cache.incr(f'executions:{user_id}')
    cache.set(f'execution:{execution_id}:user', user_id)

def finish_execution(execution_id):
    user_id = cache.get(f'execution:{execution_id}:user')
    cache.decr(f'executions:{user_id}')
```

#### Deployment Considerations

**Server Requirements**:
- OMERO.web server (Django)
- Execution server (OpenHCS daemon)
- OMERO.server (for data access)
- All on same machine or networked

**Network Configuration**:
- OMERO.web: port 80/443 (HTTPS)
- Execution server: port 7777 (internal)
- OMERO.server: port 4064 (internal)
- Firewall rules for internal communication

**Scalability**:
- Multiple execution servers for load balancing
- Round-robin or least-loaded selection
- Shared OMERO binary repository (NFS)

### Implementation Draft

(Code will be written here after smell loop approval)

