# OpenHCS + OMERO Integration - Setup Guide

This guide shows how to run OMERO integration tests.

## Prerequisites

1. **Docker & Docker Compose** - For running OMERO locally
   ```bash
   docker --version
   docker-compose --version
   ```

2. **Python Dependencies**
   ```bash
   pip install "openhcs[omero]"
   ```

---

## Quick Start

### 1. Start OMERO

From the `openhcs/omero` directory:

```bash
cd openhcs/omero
docker-compose up -d
./wait_for_omero.sh
```

This starts:
- PostgreSQL (database)
- OMERO.server (port 4064)
- OMERO.web (port 4080)

Check status:
```bash
docker-compose ps
```

All services should be "Up".

---

### 2. Run Integration Tests

From the project root:

```bash
cd ../..  # Back to project root
pytest tests/integration/test_main.py --it-microscopes=OMERO --it-backends=disk -v
```

The tests automatically:
1. Generate synthetic microscopy data
2. Upload to OMERO as a Plate
3. Run full OpenHCS pipeline
4. Save results back to OMERO as FileAnnotations
5. Validate output

**Expected output:**

```
tests/integration/test_main.py::test_main[disk-OMERO-3d-multiprocessing-direct] PASSED
```

---

## Troubleshooting

### OMERO won't start

```bash
# Check logs
docker-compose logs omeroserver

# Restart
docker-compose down
docker-compose up -d
./wait_for_omero.sh
```

### Can't connect to OMERO

```bash
# Check if OMERO is running
docker-compose ps

# Test connection
python -c "from omero.gateway import BlitzGateway; conn = BlitzGateway('root', 'openhcs', host='localhost', port=4064); print('Connected!' if conn.connect() else 'Failed')"
```

### Port conflicts

If ports 4064 or 4080 are in use:

```bash
# Check what's using a port
lsof -i :4064

# Kill the process or change ports in docker-compose.yml
```

---

## Stopping OMERO

```bash
cd openhcs/omero
docker-compose down
```

To remove all data (fresh start):

```bash
docker-compose down -v
```

---

## Configuration

**Default credentials:**
- Host: `localhost`
- Port: `4064`
- User: `root`
- Password: `openhcs`
- Web Port: `4080`

**View OMERO.web:**
```bash
open http://localhost:4080
# Login: root / openhcs
```

---

For detailed testing documentation, see `docs/source/development/omero_testing.rst`
