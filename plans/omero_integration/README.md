# OMERO Integration Plans

## Overview

This directory contains comprehensive plans for integrating OpenHCS with OMERO, enabling remote execution of OpenHCS pipelines on OMERO servers with streaming visualization to client workstations.

## Architecture Summary

```
Local Workstation                          OMERO Server
─────────────────                          ────────────

OpenHCS Client                            OMERO.server (Java)
    │                                          │
RemoteOrchestrator                       OpenHCS Execution Server
    │                                          │
    │                                     OMEROLocalBackend
    │                                     (reads binary repo)
    │                                          │
    │ 1. Send pipeline definition             │
    │─────────────────────────────────────────>│
    │    (ZMQ REQ/REP)                         │
    │                                          │
    │                                          │ 2. Compile pipeline
    │                                          │    (data is local)
    │                                          │
    │                                          │ 3. Execute with GPU
    │                                          │    (multiprocessing)
    │                                          │
    │ 4. Stream results incrementally          │
    │<─────────────────────────────────────────│
    │    (ZMQ PUB/SUB, like Napari)            │
    │                                          │
    │ 5. Display in local viewer               │
    │    (Napari/custom)                       │
    │                                          │
    │                                          │ 6. Write results to OMERO
    │                                          │    (BlitzGateway API)
```

## Key Insight

**IPC and network sockets are fundamentally the same.** OpenHCS already has the exact pattern needed for remote execution via the Napari streaming system. The integration requires:

1. **Server-side OMERO backend** - reads directly from OMERO binary repository (zero-copy)
2. **Execution server** - listens for pipeline requests, executes locally
3. **Network streaming** - one-line change to support remote hosts
4. **Client orchestrator** - sends pipelines to server, receives results
5. **Web interface** - OMERO.web plugin for browser-based access

## Plan Files (Execution Order)

### Phase 1: Core Infrastructure (2-3 weeks)

#### plan_01_omero_local_backend.md
**Component**: OMERO Local Storage Backend  
**Effort**: Low  
**Dependencies**: None  
**Description**: Storage backend that reads directly from OMERO's binary repository using local filesystem access. Enables zero-copy data access when OpenHCS runs on OMERO server.

**Key Classes**:
- `OMEROLocalBackend(StorageBackend)` - main backend class
- Inherits from existing `StorageBackend` interface
- Auto-registered via `StorageBackendMeta` metaclass

**Integration Points**:
- OMERO BlitzGateway API for metadata
- OMERO binary repository filesystem structure
- OpenHCS FileManager and backend registry

---

#### plan_02_network_streaming.md
**Component**: Network Streaming Backend  
**Effort**: Trivial (one line change)  
**Dependencies**: None  
**Description**: Generalize existing `NapariStreamingBackend` to support remote hosts. Changes `tcp://localhost:{port}` to `tcp://{host}:{port}`.

**Key Changes**:
- `NapariStreamingBackend._get_publisher()` - add host parameter
- `NapariStreamingConfig` - add `napari_host` field
- `NapariStreamVisualizer` - bind to all interfaces

**Backward Compatibility**: Default `napari_host="localhost"` preserves existing behavior.

---

#### plan_03_execution_server.md
**Component**: OpenHCS Execution Server  
**Effort**: Moderate  
**Dependencies**: plan_01, plan_02  
**Description**: Server daemon that listens for pipeline execution requests via ZeroMQ and executes them. Based on existing `subprocess_runner.py` pattern.

**Key Classes**:
- `OpenHCSExecutionServer` - main server class
- Reuses `subprocess_runner.run_single_plate()` execution pattern
- ZeroMQ REQ/REP for command protocol
- Threading for concurrent executions

**Protocol**:
- Request: `{command, plate_id, pipeline, compiled_contexts, config, client_address}`
- Response: `{status, execution_id, message, wells_processed}`

---

#### plan_04_remote_orchestrator.md
**Component**: Remote Orchestrator Client  
**Effort**: Low  
**Dependencies**: plan_03  
**Description**: Client-side orchestrator that sends pipeline execution requests to remote server and receives streamed results. Mimics `PipelineOrchestrator` interface.

**Key Classes**:
- `RemoteOrchestrator` - client-side wrapper
- Handles serialization (dill pickle → base64)
- Manages result streaming
- Provides high-level `run_remote_pipeline()` method

**Usage Pattern**:
```python
remote_orch = RemoteOrchestrator('omero-server.mni.mcgill.ca', 7777)
remote_orch.run_remote_pipeline(
    plate_id=123,
    pipeline=pipeline,
    config=PipelineConfig(),
    viewer_port=5555
)
```

---

### Phase 2: Web Interface (4-6 weeks)

#### plan_05_omero_web_plugin.md
**Component**: OMERO.web Plugin  
**Effort**: Moderate  
**Dependencies**: plan_01, plan_02, plan_03, plan_04  
**Description**: OMERO.web plugin providing browser-based interface for launching OpenHCS pipelines and viewing results.

**Features**:
- Pipeline preset management
- Execution from web interface
- Progress monitoring
- Result visualization (Vizarr or OMERO.iviewer)
- Authentication via OMERO sessions
- Resource quotas and permissions

**URL Structure**:
- `/openhcs/` - landing page
- `/openhcs/pipelines/` - pipeline list
- `/openhcs/execute/<plate_id>/` - execute pipeline
- `/openhcs/results/<execution_id>/` - view results

---

## Technical Feasibility

| Component | Feasibility | Effort | Notes |
|-----------|-------------|--------|-------|
| **OMEROLocalBackend** | ✅ High | Low | Direct file access to binary repo |
| **Network Streaming** | ✅ High | Trivial | One line change in existing code |
| **Execution Server** | ✅ High | Moderate | Based on subprocess_runner pattern |
| **Remote Orchestrator** | ✅ High | Low | Client-side wrapper |
| **OMERO.web Plugin** | ✅ High | Moderate | Standard Django app |

## Key Design Decisions

### 1. **Compilation Happens Server-Side** ⭐
**Rationale**: Server knows its own execution environment (GPU topology, OMERO paths, backends). Compilation on server ensures correct GPU assignments and meaningful error messages.

**Implementation**: Client sends Python code (not pickled objects). Server executes code to reconstruct pipeline, then compiles in its own environment.

### 2. **Send Python Code, Not Pickled Objects** ⭐
**Rationale**:
- **10-100x smaller payload** (10-100 KB vs 1-10 MB)
- **Human-readable** (can inspect and debug)
- **Leverages existing UI↔code conversion** (`generate_complete_pipeline_steps_code()`)
- **Server-side compilation** (correct environment)

**Implementation**: Use existing `openhcs/debug/pickle_to_python.py` code generation functions.

### 3. Streaming Uses Existing Napari Pattern
**Rationale**: OpenHCS already has robust streaming infrastructure. Reusing it requires minimal changes and leverages battle-tested code.

### 4. Server Based on SubprocessRunner
**Rationale**: `subprocess_runner.py` already implements execution pattern. Adapt for network communication (ZeroMQ instead of pickle files) and server-side compilation.

### 5. ZeroMQ for Communication
**Rationale**: Already used throughout OpenHCS. Network-transparent (IPC and TCP use same API). High performance, low latency.

## Performance Characteristics

### Data Transfer
- **Download-Process-Upload**: 100GB plate → 10-60 minutes network transfer
- **Remote Execution**: 0 bytes transferred (data stays on server)

### Pipeline Transfer
- **Python code**: ~10-100 KB (human-readable)
- **Pickled objects**: ~1-10 MB (opaque)
- **Advantage**: 10-100x smaller with code approach

### Compilation
- **Server-side**: ~5-10 seconds for 96-well plate
- **Correct environment**: GPU topology, OMERO paths, backends
- **Meaningful errors**: Based on actual execution environment

### Execution
- **Server-side**: Same as local execution (no overhead)
- **GPU access**: Server GPUs (shared resource)
- **GPU distribution**: Optimized for server hardware

### Streaming
- **Incremental**: Results stream as they're generated
- **Bandwidth**: ~1-10 MB/s per well (depends on image size)
- **Latency**: <100ms on LAN

## Security Considerations

### Phase 1 (Trusted Network)
- Assume facility LAN is trusted
- No authentication on ZeroMQ sockets
- No encryption
- Firewall rules restrict access to internal network

### Phase 2 (Production)
- CurveZMQ for encryption
- Token-based authentication
- Rate limiting
- Resource quotas per user
- Audit logging

## Deployment Scenarios

### Scenario 1: Single Server
- OMERO.server, OMERO.web, and OpenHCS execution server on same machine
- Simplest deployment
- Good for small facilities (<10 users)

### Scenario 2: Separate Execution Server
- OMERO.server on one machine
- OpenHCS execution server on GPU workstation
- Shared OMERO binary repository (NFS)
- Better GPU utilization

### Scenario 3: Multiple Execution Servers
- Load balancing across multiple GPU servers
- Round-robin or least-loaded selection
- Scales to large facilities (>50 users)

## Testing Strategy

### Unit Tests
- `OMEROLocalBackend` - mock OMERO connection
- `RemoteOrchestrator` - mock ZeroMQ sockets
- Serialization/deserialization round-trips

### Integration Tests
- End-to-end: client → server → execution → streaming
- Use test OMERO server with sample data
- Verify results match local execution

### Performance Tests
- Benchmark remote vs local execution
- Measure streaming latency
- Test concurrent executions

## Documentation Requirements

### User Documentation
- Installation guide (server and client)
- Quick start tutorial
- Pipeline creation guide
- Troubleshooting common issues

### Developer Documentation
- Architecture overview
- API reference
- Extension points
- Contributing guide

### Administrator Documentation
- Server deployment
- Configuration options
- Monitoring and logging
- Security hardening

## Future Enhancements

### Phase 3: Advanced Features
- Pipeline marketplace (share pipelines)
- Batch processing queue
- Result caching and reuse
- Integration with OMERO.scripts
- Jupyter notebook integration
- REST API for programmatic access

### Phase 4: Optimization
- Compression for serialized contexts
- Delta encoding for incremental updates
- GPU scheduling optimization
- Distributed execution across multiple servers

## Success Metrics

### Technical
- ✅ Zero data transfer (processing happens server-side)
- ✅ <1s latency for streaming (real-time feedback)
- ✅ >10 concurrent users supported
- ✅ 100% compatibility with existing OpenHCS pipelines

### User Experience
- ✅ Familiar interface (mimics local OpenHCS)
- ✅ No local installation required (web interface)
- ✅ Real-time progress monitoring
- ✅ Results automatically saved to OMERO

## Risks and Mitigations

### Risk 1: Network Reliability
**Impact**: High  
**Mitigation**: Retry logic, timeout handling, execution resumption

### Risk 2: Server Overload
**Impact**: Medium  
**Mitigation**: Resource quotas, queue system, multiple servers

### Risk 3: Version Compatibility
**Impact**: Medium  
**Mitigation**: Version checking, backward compatibility, migration tools

### Risk 4: Security Vulnerabilities
**Impact**: High  
**Mitigation**: Authentication, encryption, audit logging, security reviews

## Conclusion

The OMERO integration is **architecturally sound** and leverages existing OpenHCS infrastructure. The remote execution pattern is superior to download-process-upload because:

1. **Performance**: Data never moves, processing happens where data lives
2. **Architecture**: Reuses existing streaming patterns (Napari)
3. **Scalability**: Server resources shared across users
4. **User Experience**: Real-time streaming feedback

The facility manager should be approached with a **proof-of-concept** demonstrating:
- Read-only integration (fetch from OMERO, process, display)
- Performance advantage (no data transfer)
- Familiar interface (same as local OpenHCS)

**Timeline**: 2-3 weeks for Phase 1 (core infrastructure), 4-6 weeks for Phase 2 (web interface).

**Risk**: Low. No changes to OMERO server, only client-side integration.

