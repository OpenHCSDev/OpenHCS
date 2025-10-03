# plan_06_local_testing.md
## Component: Local OMERO Installation & Integration Testing

### Objective
Set up a local OMERO instance for development and testing, enabling a laptop-based demo for the facility manager. This validates the integration architecture before deploying to production servers.

### Plan

1. **Install OMERO.server locally using Docker**
   - Use official OMERO Docker images
   - Docker Compose setup for OMERO.server + OMERO.web + PostgreSQL
   - Configure for local development (not production)
   - Expose ports: 4064 (OMERO.server), 4080 (OMERO.web)

2. **Import sample HCS data**
   - Download public HCS dataset from IDR (Image Data Resource)
   - Or: Use existing OpenHCS test data (ImageXpress/Opera Phenix)
   - Import to OMERO using CLI: `omero import`
   - Verify data is accessible via OMERO.web

3. **Test Phase 1: OMERO Local Backend**
   - Implement `OMEROLocalBackend` (plan_01)
   - Test reading images from OMERO binary repository
   - Test saving results back to OMERO
   - Verify metadata preservation

4. **Test Phase 2: Network Streaming**
   - Implement network streaming (plan_02)
   - Test streaming from localhost to localhost (simulates remote)
   - Verify Napari receives streamed results
   - Test with different image sizes

5. **Test Phase 3: Execution Server**
   - Implement execution server (plan_03)
   - Start server on localhost:7777
   - Test receiving pipeline code
   - Test server-side compilation
   - Test execution and result streaming

6. **Test Phase 4: Remote Orchestrator**
   - Implement remote orchestrator (plan_04)
   - Test sending pipeline to local server
   - Test receiving streamed results
   - Verify end-to-end workflow

7. **Create demo script**
   - Automated script that demonstrates full workflow
   - Load plate from OMERO
   - Define simple pipeline (e.g., normalize → segment)
   - Execute remotely
   - Display results in Napari
   - Save results back to OMERO
   - Show before/after comparison

8. **Create demo presentation**
   - Slides explaining the architecture
   - Live demo script
   - Performance comparison (local vs remote)
   - Benefits for facility users
   - Deployment plan

9. **Document troubleshooting**
   - Common issues and solutions
   - Docker troubleshooting
   - OMERO connection issues
   - Network streaming issues
   - Performance tuning

10. **Prepare for facility manager meeting**
    - Test demo on laptop (offline capability)
    - Prepare talking points
    - Prepare technical requirements document
    - Prepare timeline and resource estimates

### Findings

#### OMERO Docker Setup

**Official Docker Images**:
- `openmicroscopy/omero-server` - OMERO.server
- `openmicroscopy/omero-web-standalone` - OMERO.web
- `postgres:11` - PostgreSQL database

**Docker Compose Example**:
```yaml
version: '3'

services:
  postgres:
    image: postgres:11
    environment:
      POSTGRES_USER: omero
      POSTGRES_PASSWORD: omero
      POSTGRES_DB: omero
    volumes:
      - postgres_data:/var/lib/postgresql/data

  omero-server:
    image: openmicroscopy/omero-server:latest
    environment:
      CONFIG_omero_db_host: postgres
      CONFIG_omero_db_user: omero
      CONFIG_omero_db_pass: omero
      CONFIG_omero_db_name: omero
      ROOTPASS: omero-root-password
    ports:
      - "4064:4064"
    volumes:
      - omero_data:/OMERO
    depends_on:
      - postgres

  omero-web:
    image: openmicroscopy/omero-web-standalone:latest
    environment:
      OMEROHOST: omero-server
    ports:
      - "4080:4080"
    depends_on:
      - omero-server

volumes:
  postgres_data:
  omero_data:
```

**Start OMERO**:
```bash
docker-compose up -d
# Wait for services to start (~30 seconds)
docker-compose logs -f omero-server  # Check logs
```

**Access**:
- OMERO.web: http://localhost:4080
- OMERO.server: localhost:4064
- Default credentials: root / omero-root-password

#### Sample HCS Data Sources

**Option 1: IDR (Image Data Resource)**
- Public repository of microscopy data
- HCS datasets available
- Example: idr0002 (Centrosome study, 96-well plates)
- Download via `aspera` or web interface

**Option 2: OpenHCS Test Data**
- Use existing test data from `tests/data/`
- ImageXpress or Opera Phenix format
- Already validated with OpenHCS
- Smaller, faster for testing

**Option 3: Synthetic Data**
- Generate synthetic HCS data
- Controlled size and complexity
- Good for performance testing

**Recommendation**: Start with OpenHCS test data (fastest), then try IDR data (realistic).

#### OMERO Import

**CLI Import**:
```bash
# Install OMERO CLI
pip install omero-py

# Import plate
omero import --server localhost:4064 --user root --password omero-root-password \
  /path/to/plate/data

# Create dataset first (optional)
omero obj new Dataset name="OpenHCS Test Data"
omero import --dataset 1 /path/to/plate/data
```

**Python Import**:
```python
from omero.gateway import BlitzGateway
from omero.model import DatasetI, PlateI
from omero.rtypes import rstring

conn = BlitzGateway('root', 'omero-root-password', host='localhost', port=4064)
conn.connect()

# Create dataset
dataset = DatasetI()
dataset.setName(rstring("OpenHCS Test Data"))
dataset = conn.getUpdateService().saveAndReturnObject(dataset)

# Import images (requires OMERO.fs or manual file placement)
# For testing, use CLI import (simpler)
```

#### Testing Workflow

**Incremental Testing** (build confidence step-by-step):

1. **Backend Test**:
   ```python
   from openhcs.io.omero_local import OMEROLocalBackend
   
   backend = OMEROLocalBackend(
       omero_data_dir=Path('/OMERO'),
       omero_conn=conn
   )
   
   # Test load
   image = backend.load(image_id=1)
   assert image.shape == (10, 512, 512)  # Z, Y, X
   
   # Test save
   backend.save(image, 'processed.tif', dataset_id=1)
   ```

2. **Streaming Test**:
   ```python
   from openhcs.io.napari_stream import NapariStreamingBackend
   
   backend = NapariStreamingBackend()
   backend.save(image, 'test.tif', 
                napari_host='localhost', 
                napari_port=5555)
   # Verify Napari receives image
   ```

3. **Server Test**:
   ```bash
   # Start server
   python openhcs/runtime/start_execution_server.py --port 7777
   
   # Send test request
   python test_remote_execution.py
   ```

4. **End-to-End Test**:
   ```python
   from openhcs.runtime.remote_orchestrator import RemoteOrchestrator
   
   remote = RemoteOrchestrator('localhost', 7777)
   remote.run_remote_pipeline(
       plate_id=1,
       pipeline=test_pipeline,
       config=test_config,
       viewer_port=5555
   )
   ```

#### Demo Script Structure

**demo.py**:
```python
#!/usr/bin/env python3
"""
OpenHCS + OMERO Integration Demo

Demonstrates remote execution of OpenHCS pipelines on OMERO server
with real-time streaming visualization.
"""

import time
from omero.gateway import BlitzGateway
from openhcs.runtime.remote_orchestrator import RemoteOrchestrator
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.filters.gaussian_filter import gaussian_filter
from openhcs.processing.backends.analysis.cell_counting import count_cells

def main():
    print("=" * 60)
    print("OpenHCS + OMERO Integration Demo")
    print("=" * 60)
    
    # 1. Connect to OMERO
    print("\n[1/5] Connecting to OMERO...")
    conn = BlitzGateway('root', 'omero-root-password', 
                        host='localhost', port=4064)
    conn.connect()
    print("✓ Connected to OMERO")
    
    # 2. Get plate
    print("\n[2/5] Loading plate from OMERO...")
    plate = conn.getObject("Plate", 1)
    print(f"✓ Loaded plate: {plate.getName()}")
    print(f"  Wells: {plate.getNumberOfWells()}")
    
    # 3. Define pipeline
    print("\n[3/5] Defining processing pipeline...")
    pipeline = [
        FunctionStep(
            func=(gaussian_filter, {'sigma': 2.0}),
            name="Denoise"
        ),
        FunctionStep(
            func=(count_cells, {'method': 'watershed'}),
            name="Count Cells"
        )
    ]
    print("✓ Pipeline defined (2 steps)")
    
    # 4. Execute remotely
    print("\n[4/5] Executing pipeline on OMERO server...")
    print("  (Watch Napari window for real-time results)")
    
    remote = RemoteOrchestrator('localhost', 7777)
    start_time = time.time()
    
    remote.run_remote_pipeline(
        plate_id=plate.getId(),
        pipeline=pipeline,
        config=GlobalPipelineConfig(),
        viewer_port=5555
    )
    
    elapsed = time.time() - start_time
    print(f"✓ Pipeline completed in {elapsed:.1f}s")
    
    # 5. Show results
    print("\n[5/5] Results saved to OMERO")
    print("  Check OMERO.web for processed images")
    
    print("\n" + "=" * 60)
    print("Demo Complete!")
    print("=" * 60)

if __name__ == "__main__":
    main()
```

#### Performance Metrics for Demo

**Collect these metrics to show value**:
- Data transfer time: 0s (vs 10-60 min for download)
- Processing time: Same as local (no overhead)
- Result streaming latency: <100ms
- Total workflow time: Compile + Execute + Stream
- GPU utilization: Show server GPU usage

**Comparison Table**:
```
Metric                  | Local Processing | Remote Execution
------------------------|------------------|------------------
Data Transfer           | 10-60 min        | 0s
Processing Time         | 5 min            | 5 min
Result Transfer         | 2-5 min          | Real-time stream
Total Time              | 17-70 min        | 5 min
GPU Required            | Local GPU        | Server GPU (shared)
Storage Required        | 100GB local      | 0GB (stays on server)
```

#### Troubleshooting Guide

**Issue: OMERO.server won't start**
- Check Docker logs: `docker-compose logs omero-server`
- Verify PostgreSQL is running: `docker-compose ps`
- Check port conflicts: `lsof -i :4064`

**Issue: Can't import data**
- Verify OMERO.fs is configured
- Check file permissions in `/OMERO` volume
- Use `omero import --debug` for detailed logs

**Issue: Backend can't read files**
- Verify `/OMERO` path is correct
- Check OMERO binary repository structure
- Verify BlitzGateway connection

**Issue: Streaming not working**
- Check firewall: `sudo ufw status`
- Verify ports are open: `netstat -an | grep 5555`
- Test ZeroMQ connection manually

**Issue: Server compilation fails**
- Check server has access to function registry
- Verify imports in generated code
- Check server logs for detailed error

### Implementation Draft

(Code will be written here after smell loop approval)

