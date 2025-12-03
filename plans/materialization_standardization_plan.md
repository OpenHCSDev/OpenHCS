# Materialization Standardization Plan

## Goal
Make materialization functions consistent and reusable across built-in and custom functions, with clear hooks/templates so new outputs can be materialized without bespoke glue code.

## Current Gaps
- Mixed materializer signatures (`backend` vs `backends + backend_kwargs`) and duplicated backend handling.
- No shared helper layer for common cases (CSV, ROI, image stack), so each backend reimplements basics.
- Custom function template/docs do not show how to declare special outputs with materializers; authoring is ad hoc.
- Registry/function reference plumbing preserves materialization metadata, but we lack a first-class API to plug in reusable materializers or per-output hooks.

## Proposal (Phased)
1) **Canonical interface + helper layer**
   - Standardize materializer signature: `(data, path, filemanager, backends: List[str], backend_kwargs: Dict[str, dict]) -> str`.
   - Add `openhcs.processing.materialization.helpers` with reusable helpers (csv/table writer, ROI writer, image stack saver) that map to disk/zarr/streaming backends and enforce capability checks.
   - Provide a thin wrapper to fan-out to multiple backends and inject common kwargs (images_dir, source).

2) **Inventory and migrate built-ins**
   - Survey existing materializers (cell counting, MTM, HMM/axon, ashlar positions, consolidated outputs) and align signatures to the canonical form.
   - Replace bespoke backend branching with helper invocations; keep behavior identical (OMERO/disk/zarr/streaming).
   - Add lightweight unit tests for helpers and a smoke test covering one representative materializer per family.

3) **Planner/runtime integration hooks**
   - Ensure `@special_outputs` accepts either a callable or a named helper reference; map helper names to concrete callables in the planner.
   - Keep path planner behavior unchanged; only standardize how materializers are invoked in `FunctionStep._materialize_special_outputs`.
   - Preserve backward compatibility by allowing legacy signature callables behind a shim adapter.

4) **Custom function UX**
   - Update the custom-function template and docs with an example `@special_outputs(("my_csv", helpers.csv_table))`.
   - Expose helper names in the custom-function editor (dropdown or code snippet) so users can opt into standardized materialization without writing boilerplate.
   - Document best practices (return shapes, expected data formats) and a quick checklist for adding new materializers.

5) **Safety, compatibility, rollout**
   - Add a feature flag to fall back to legacy invocation if any adapter fails.
   - Keep API stable for existing pipelines; warn when deprecated signatures are detected.
   - Changelog entry + migration guide summarizing signature change and helper usage.
