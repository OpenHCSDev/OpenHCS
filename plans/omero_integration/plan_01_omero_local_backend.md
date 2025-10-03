# plan_01_omero_local_backend.md
## Component: OMERO Local Storage Backend

### Objective
Implement a storage backend that reads directly from OMERO's binary repository using local filesystem access (server-side only). This backend enables zero-copy data access when OpenHCS runs on the same server as OMERO, eliminating network overhead.

### Plan

1. **Create `OMEROLocalBackend` class** in `openhcs/io/omero_local.py`
   - Inherit from `StorageBackend` (provides load/save/list operations)
   - Register via `StorageBackendMeta` metaclass for auto-discovery
   - Backend type: `'omero_local'`

2. **Implement initialization**
   - Accept `omero_data_dir: Path` - path to OMERO binary repository (e.g., `/OMERO/Files`)
   - Accept `omero_conn: BlitzGateway` - OMERO connection for metadata queries
   - Store both for use in load/save operations

3. **Implement `load()` method**
   - Query OMERO for image metadata using BlitzGateway
   - Resolve local file path from OMERO's binary repository structure
   - Read directly from filesystem (no network transfer)
   - Support multiple formats: `.tif`, `.zarr`, `.ome.tiff`
   - Return numpy array (3D, matching OpenHCS contract)

4. **Implement `save()` method**
   - Accept numpy array and output path
   - Create new OMERO Image object using `createImageFromNumpySeq()`
   - Link to appropriate Dataset/Project based on kwargs
   - Store metadata (processing provenance, parameters)
   - Return saved image ID

5. **Implement `list_files()` method**
   - Query OMERO for images in specified Dataset/Project
   - Return list of image IDs (not file paths)
   - Support filtering by name, date, tags

6. **Add OMERO-specific helper methods**
   - `_get_local_file_path(image_id)` - resolve OMERO image to filesystem path
   - `_create_plane_generator(data)` - yield 2D planes for OMERO upload
   - `_get_or_create_dataset(name, project_id)` - dataset management

7. **Error handling**
   - Fail loudly if OMERO connection is lost
   - Fail loudly if binary repository path is invalid
   - Fail loudly if image file doesn't exist at expected path
   - No defensive programming - let Python raise natural errors

### Findings

#### Existing Backend System Architecture

**Base Classes** (`openhcs/io/base.py`):
- `DataSink` - abstract base for save operations only
- `StorageBackend(DataSink)` - adds load/list operations for full storage
- `StreamingBackend(DataSink)` - for streaming destinations (no persistence)

**Registration Pattern** (`openhcs/io/backend_registry.py`):
- `StorageBackendMeta` metaclass auto-registers backends
- `get_backend_instance(backend_type)` - lazy instantiation
- `create_storage_registry()` - discovers all backends

**Existing Backends**:
- `DiskStorageBackend` - local filesystem
- `MemoryStorageBackend` - in-memory overlay (uses real paths)
- `ZarrStorageBackend` - OME-NGFF zarr format
- `NapariStreamingBackend` - ZeroMQ streaming to Napari
- `FijiStreamingBackend` - ZeroMQ streaming to Fiji

**Key Pattern**: All backends use `_backend_type` class attribute for registration.

#### OMERO Binary Repository Structure

OMERO stores files in: `/OMERO/Files/[hash]/[filename]`
- Hash is computed from file ID
- Original filename preserved
- Metadata stored in PostgreSQL database
- Binary data stored as flat files

#### OMERO Python API (BlitzGateway)

**Connection**:
```python
from omero.gateway import BlitzGateway
conn = BlitzGateway(username, password, host=host, port=4064)
conn.connect()
```

**Image Access**:
```python
image = conn.getObject("Image", image_id)
fileset = image.getFileset()
for orig_file in fileset.listFiles():
    path = orig_file.getPath()
    name = orig_file.getName()
```

**Image Creation**:
```python
def plane_generator(data):
    for z in range(data.shape[0]):
        yield data[z]

new_image = conn.createImageFromNumpySeq(
    plane_generator(data),
    name="Processed Image",
    sizeZ=data.shape[0],
    sizeC=data.shape[1] if data.ndim > 3 else 1,
    sizeT=1
)
```

#### OpenHCS 3D Array Contract

All OpenHCS functions expect 3D arrays: `(Z, Y, X)` or `(Z, C, Y, X)` for multi-channel.
- Single 2D images must be wrapped: `image[np.newaxis, ...]`
- OMERO stores as separate planes - must be assembled into 3D stack

#### FileManager Integration

`FileManager` (`openhcs/io/filemanager.py`) provides unified API:
```python
filemanager.load(path, backend='omero_local', image_id=123)
filemanager.save(data, path, backend='omero_local', dataset_id=456)
```

Backend is resolved via `_get_backend(backend_type)` which calls `get_backend_instance()`.

### Implementation Draft

(Code will be written here after smell loop approval)

