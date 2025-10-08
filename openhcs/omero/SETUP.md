# OpenHCS + OMERO Integration - Local Setup Guide

This guide shows how to run the OMERO integration demo on your laptop.

## Prerequisites

1. **Docker & Docker Compose** - For running OMERO locally
   ```bash
   docker --version
   docker-compose --version
   ```

2. **Python Dependencies**
   ```bash
   pip install omero-py napari[all]
   ```

3. **OpenHCS** - Already installed (you're in the repo)

---

## Quick Start

### 1. Start OMERO

From the project root:

```bash
docker-compose up -d
```

This starts:
- PostgreSQL (database)
- OMERO.server (port 4064)
- OMERO.web (port 4080)

**Wait ~30 seconds** for OMERO to initialize.

Check status:
```bash
docker-compose ps
```

All services should be "Up".

---

### 2. Import Test Data

**Option A: Use existing test data**

```bash
python examples/import_test_data.py
```

This will:
- Connect to OMERO
- Create a dataset
- Show you the `omero import` command to run

**Option B: Manual import via CLI**

```bash
# Install OMERO CLI
pip install omero-py

# Import a plate
omero login -s localhost -u root -w omero-root-password
omero import -d <dataset_id> tests/data/<your_plate_directory>
```

**Option C: Use OMERO.web interface**

1. Open http://localhost:4080
2. Login: `root` / `omero-root-password`
3. Create a dataset
4. Import images via web interface

---

### 3. Run Demo

```bash
python examples/omero_demo.py
```

This will:
1. Connect to OMERO
2. Load test dataset
3. Start execution server (background)
4. Start Napari viewer
5. Execute pipeline remotely
6. Stream results to Napari
7. Save results to OMERO

**Expected output:**

```
============================================================
  OpenHCS + OMERO Integration Demo
============================================================

[1/7] Connecting to OMERO (localhost:4064)...
✓ Connected as root

[2/7] Loading dataset...
✓ Loaded dataset: OpenHCS_Test_Data (ID: 1, 384 images)

[3/7] Starting execution server (port 7777)...
✓ Server running (PID: 12345)

[4/7] Starting Napari viewer (port 5555)...
✓ Viewer ready

[5/7] Executing pipeline remotely...
  → Pipeline: Multi-Subdirectory Test Pipeline
  → Steps: 8
✓ Pipeline accepted (execution_id: abc-123-def)
  → Processing...
✓ Completed in 45.2s (96 wells)

[6/7] Validating results...
✓ Dataset contains 384 images
✓ Found 1 result dataset(s)

[7/7] Demo complete!
============================================================
  🔥 TEST COMPLETED SUCCESSFULLY!
============================================================

📊 Summary:
  • Data transfer: 0 bytes (processing on server)
  • Results streamed: Real-time to Napari
  • Results saved: Back to OMERO
  • Execution ID: abc-123-def

💡 Napari viewer is still running. Close it to exit.

Press Enter to exit...
```

---

## Troubleshooting

### OMERO won't start

```bash
# Check logs
docker-compose logs omero-server

# Restart
docker-compose down
docker-compose up -d
```

### Can't connect to OMERO

```bash
# Check if OMERO is running
docker-compose ps

# Test connection
python -c "from omero.gateway import BlitzGateway; conn = BlitzGateway('root', 'omero-root-password', host='localhost', port=4064); print('Connected!' if conn.connect() else 'Failed')"
```

### No test data

Make sure you have test data in `tests/data/`. If not:

1. Download sample HCS data from IDR (Image Data Resource)
2. Or use your own microscopy data
3. Import into OMERO using one of the methods above

### Port conflicts

If ports 4064, 4080, 5555, or 7777 are in use:

```bash
# Check what's using a port
lsof -i :4064

# Kill the process or change ports in docker-compose.yml
```

### Napari won't start

Make sure you're not in headless mode:

```bash
unset OPENHCS_HEADLESS
unset CI
```

---

## Stopping OMERO

```bash
docker-compose down
```

To remove all data (fresh start):

```bash
docker-compose down -v
```

---

## Architecture

```
┌─────────────────────────────────────────────────────────┐
│                    Your Laptop                          │
│                                                         │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐ │
│  │   OMERO      │  │  Execution   │  │   Napari     │ │
│  │   Server     │  │   Server     │  │   Viewer     │ │
│  │  (Docker)    │  │  (Python)    │  │  (Python)    │ │
│  │              │  │              │  │              │ │
│  │  Port 4064   │  │  Port 7777   │  │  Port 5555   │ │
│  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘ │
│         │                 │                 │          │
│         │                 │                 │          │
│         └─────────────────┴─────────────────┘          │
│              Zero-copy data access                     │
│              Real-time streaming                       │
└─────────────────────────────────────────────────────────┘
```

**Key Points:**
- OMERO stores data in `/OMERO/Files` (inside Docker)
- Execution server reads directly from OMERO (zero-copy)
- Results stream to Napari in real-time
- Results saved back to OMERO
- **No data leaves the server** (except streaming visualization)

---

## Next Steps

After the demo works locally:

1. **Deploy to production** - Run execution server on actual OMERO server
2. **Remote execution** - Run demo from your laptop, execution on server
3. **Scale up** - Process full plates (thousands of images)
4. **OMERO.web plugin** - Browser-based interface (Milestone 1.5)

---

## Demo Script for Facility Manager

**Setup (before meeting):**
1. Start OMERO: `docker-compose up -d`
2. Import test data: `python examples/import_test_data.py`
3. Test demo: `python examples/omero_demo.py`

**During meeting:**
1. Show OMERO.web interface (http://localhost:4080)
2. Show test dataset in OMERO
3. Run demo: `python examples/omero_demo.py`
4. Highlight:
   - Zero data transfer (processing where data lives)
   - Real-time visualization (Napari streaming)
   - Results saved to OMERO (provenance)
   - Same pipeline as existing OpenHCS tests (compatibility)

**Key talking points:**
- "This is the same pipeline we use for local processing"
- "No data leaves the OMERO server - only visualization streams"
- "Results are automatically saved back to OMERO with full provenance"
- "Researchers can run this from their laptops, processing happens on the server"

