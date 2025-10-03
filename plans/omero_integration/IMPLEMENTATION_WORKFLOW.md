# OMERO Integration Implementation Workflow

## Branch: `omero`

All development happens on the `omero` branch. When complete and tested, we'll create a PR to `main`.

## GitHub Milestones

We've created 6 milestones corresponding to the plan files:

### Phase 1: Core Infrastructure (Milestones 1-5)

#### Milestone 1: OMERO Local Backend
- **Plan**: `plan_01_omero_local_backend.md`
- **GitHub**: https://github.com/trissim/openhcs/milestone/1
- **Effort**: Low
- **Dependencies**: None
- **Deliverables**:
  - `openhcs/io/omero_local.py` - OMEROLocalBackend class
  - Unit tests
  - Integration tests with local OMERO

#### Milestone 2: Network Streaming
- **Plan**: `plan_02_network_streaming.md`
- **GitHub**: https://github.com/trissim/openhcs/milestone/2
- **Effort**: Trivial (one line change)
- **Dependencies**: None
- **Deliverables**:
  - Updated `openhcs/io/napari_stream.py`
  - Updated `openhcs/runtime/napari_stream_visualizer.py`
  - Network streaming tests

#### Milestone 3: Execution Server
- **Plan**: `plan_03_execution_server.md`
- **GitHub**: https://github.com/trissim/openhcs/milestone/3
- **Effort**: Moderate
- **Dependencies**: Milestone 1, 2
- **Deliverables**:
  - `openhcs/runtime/execution_server.py`
  - `openhcs/runtime/start_execution_server.py`
  - Server tests

#### Milestone 4: Remote Orchestrator
- **Plan**: `plan_04_remote_orchestrator.md`
- **GitHub**: https://github.com/trissim/openhcs/milestone/4
- **Effort**: Low
- **Dependencies**: Milestone 3
- **Deliverables**:
  - `openhcs/runtime/remote_orchestrator.py`
  - Client tests
  - End-to-end integration tests
  - Example scripts

#### Milestone 5: Local OMERO Testing & Demo
- **Plan**: `plan_06_local_testing.md`
- **GitHub**: https://github.com/trissim/openhcs/milestone/5
- **Effort**: Low
- **Dependencies**: Milestone 1-4
- **Deliverables**:
  - `docker-compose.yml` - Local OMERO setup
  - `examples/omero_demo.py` - Demo script
  - Demo slides
  - Testing documentation
  - Troubleshooting guide

### Phase 2: Web Interface (Milestone 6)

#### Milestone 6: OMERO.web Plugin
- **Plan**: `plan_05_omero_web_plugin.md`
- **GitHub**: https://github.com/trissim/openhcs/milestone/6
- **Effort**: Moderate
- **Dependencies**: Milestone 1-5 (all of Phase 1)
- **Deliverables**:
  - `omero_openhcs/` - Django app
  - Installation guide
  - User documentation

## Implementation Order

### Week 1: Core Components
1. **Milestone 2** (Network Streaming) - Start here (easiest, no dependencies)
2. **Milestone 1** (OMERO Backend) - Parallel with Milestone 2
3. **Milestone 3** (Execution Server) - After 1 & 2 complete

### Week 2: Integration & Testing
4. **Milestone 4** (Remote Orchestrator) - After Milestone 3
5. **Milestone 5** (Local Testing & Demo) - After Milestone 4
6. **Demo to facility manager** - End of Week 2

### Week 3-4: Web Interface (Optional)
7. **Milestone 6** (OMERO.web Plugin) - After successful demo

## Development Workflow

### For Each Milestone:

1. **Create issues** for each deliverable
   - Link to milestone
   - Assign to yourself
   - Add labels (enhancement, documentation, etc.)

2. **Implement** following the plan
   - Write code
   - Write tests
   - Update documentation
   - Commit frequently with descriptive messages

3. **Test** incrementally
   - Unit tests pass
   - Integration tests pass
   - Manual testing with local OMERO

4. **Update milestone progress** on GitHub
   - Close issues as completed
   - Update milestone description with progress notes

5. **Move to next milestone** when all issues closed

### Commit Message Format

```
[Milestone X] Brief description

Detailed description of changes.

- Bullet point 1
- Bullet point 2

Closes #issue_number
```

Example:
```
[Milestone 1] Implement OMEROLocalBackend.load()

Add method to load images from OMERO binary repository using
local filesystem access.

- Query OMERO for image metadata
- Resolve local file path
- Read image using tifffile/zarr
- Return 3D numpy array

Closes #1
```

## Testing Strategy

### Unit Tests
- Test each component in isolation
- Mock external dependencies (OMERO connection, ZeroMQ sockets)
- Fast, deterministic

### Integration Tests
- Test components working together
- Use local OMERO instance (Docker)
- Test with real data

### End-to-End Tests
- Full workflow: client → server → execution → streaming
- Verify results match local execution
- Performance benchmarks

### Demo Testing
- Run demo script on laptop
- Verify all features work offline
- Practice presentation

## Progress Tracking

### GitHub Project Board (Optional)
Create a project board with columns:
- **Backlog** - All issues
- **In Progress** - Currently working on
- **Testing** - Implementation done, testing in progress
- **Done** - Completed and tested

### Weekly Updates
Post weekly progress updates as GitHub discussions or issues:
- What was completed
- What's in progress
- Blockers or issues
- Next week's goals

## Pull Request to Main

### When to Create PR:
- All Phase 1 milestones complete (1-5)
- All tests passing
- Demo successful
- Documentation complete

### PR Checklist:
- [ ] All milestones 1-5 closed
- [ ] All tests passing (unit + integration + e2e)
- [ ] Demo script works on laptop
- [ ] Documentation updated
- [ ] CHANGELOG.md updated
- [ ] No merge conflicts with main
- [ ] Code reviewed (self-review or peer review)

### PR Description Template:
```markdown
## OMERO Integration - Phase 1

This PR adds OMERO integration to OpenHCS, enabling remote execution of pipelines on OMERO servers with zero data transfer.

### Architecture
- Send Python code (not pickled objects) for server-side compilation
- Leverage existing UI↔code conversion system
- ZeroMQ for communication (same as Napari streaming)
- Server-side compilation ensures correct GPU topology and paths

### Components Added
- OMEROLocalBackend - reads from OMERO binary repository
- Network streaming - generalized Napari pattern for remote hosts
- Execution server - listens for pipeline requests, executes remotely
- Remote orchestrator - client-side wrapper for remote execution
- Local testing setup - Docker Compose for development

### Testing
- Unit tests: X passing
- Integration tests: Y passing
- End-to-end tests: Z passing
- Demo script: ✓ working

### Demo
See `examples/omero_demo.py` for a complete demonstration.

### Documentation
- Architecture overview: `plans/omero_integration/README.md`
- Implementation plans: `plans/omero_integration/plan_*.md`
- User guide: `docs/omero_integration.md`
- Troubleshooting: `plans/omero_integration/plan_06_local_testing.md`

### Performance
- Data transfer: 0 bytes (vs 10-60 min for download)
- Processing time: Same as local (no overhead)
- Streaming latency: <100ms on LAN

### Breaking Changes
None. All changes are additive.

### Future Work
- Phase 2: OMERO.web plugin (Milestone 6)
- Production deployment guide
- Multi-server load balancing
- Authentication and encryption

Closes #milestone1 #milestone2 #milestone3 #milestone4 #milestone5
```

## Success Criteria

### Phase 1 Complete When:
- ✅ Can read images from local OMERO instance
- ✅ Can stream results over network
- ✅ Can execute pipelines remotely
- ✅ Can send pipelines from client to server
- ✅ Demo script works on laptop
- ✅ All tests passing
- ✅ Documentation complete

### Ready for Facility Manager Demo When:
- ✅ Docker Compose setup works reliably
- ✅ Demo script runs without errors
- ✅ Results are visually impressive
- ✅ Performance metrics collected
- ✅ Presentation slides ready
- ✅ Can answer technical questions

### Ready for Production When:
- ✅ Phase 1 complete and tested
- ✅ Facility manager approves
- ✅ Security review complete
- ✅ Deployment plan documented
- ✅ Monitoring and logging in place
- ✅ Backup and recovery tested

## Next Steps

1. **Start with Milestone 2** (Network Streaming) - easiest, builds confidence
2. **Then Milestone 1** (OMERO Backend) - can work in parallel
3. **Set up local OMERO** (Docker Compose) - needed for testing
4. **Implement Milestone 3** (Execution Server) - core functionality
5. **Implement Milestone 4** (Remote Orchestrator) - client side
6. **Complete Milestone 5** (Testing & Demo) - validate everything works
7. **Demo to facility manager** - get feedback and approval
8. **Create PR to main** - merge when approved
9. **Optional: Milestone 6** (Web Plugin) - if facility wants it

## Questions or Issues?

- Create GitHub issues for bugs or questions
- Tag with appropriate milestone
- Use discussions for design questions
- Update plans as needed (they're living documents)

---

**Current Status**: Branch created, milestones set up, ready to start implementation!

**Next Action**: Begin Milestone 2 (Network Streaming) - modify `NapariStreamingBackend._get_publisher()` to accept host parameter.

