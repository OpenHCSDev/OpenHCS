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
   - Standardize materializer signature: `(data, path, filemanager, backends: List[str], backend_kwargs: Dict[str, dict]) -> str` (no legacy signatures).
   - Add `openhcs.processing.materialization.helpers` with reusable helpers (csv/table writer, ROI writer, image stack saver) that map to disk/zarr/streaming backends and enforce capability checks.
   - Provide a thin wrapper to fan-out to multiple backends and inject common kwargs (images_dir, source).

2) **Inventory and migrate built-ins**
   - Survey existing materializers (cell counting, MTM, HMM/axon, ashlar positions, consolidated outputs) and align signatures to the canonical form.
   - Replace bespoke backend branching with helper invocations; keep behavior identical (OMERO/disk/zarr/streaming).
   - Add lightweight unit tests for helpers and a smoke test covering one representative materializer per family.

3) **Registry + planner/runtime integration (aligned with FunctionReference pattern)**
   - Register materializers alongside processing functions in a materializer registry (stable names, signature-checked), with built-in helpers registered at startup and custom materializers registered when custom code loads.
   - `@special_outputs` may store a materializer name; PathPlanner writes the name into step plans; execution resolves the name via the registry before calling the canonical signature.
   - Remove legacy branches/shims: execution assumes the canonical signature; missing/invalid materializers fail fast.

4) **Custom function UX**
   - Update the custom-function template and docs with an example `@special_outputs(("my_csv", "csv_table"))`, backed by the registry.
   - Allow custom materializers to register into the materializer registry (validated against the canonical signature) so they can be referenced by name and resolved in workers.
   - Expose helper/materializer names in the editor (dropdown/snippet) and document expected data formats and return shapes.

5) **Safety, compatibility, rollout**
   - Full cutover (no legacy flag): migrate all built-ins to the canonical signature; fail fast on mismatches.
   - Changelog entry + migration guide summarizing the signature change, registry usage, and helper paths.
