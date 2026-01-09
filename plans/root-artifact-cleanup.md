---
name: root-artifact-cleanup
description: Plan to remove accidental root artifacts and prevent re-adding them
---

# Plan

Detailed steps to clean the repo root of accidental artifacts, remove or relocate local-only files, and add guardrails so these files do not return.

## Requirements
- Inventory tracked root artifacts and classify keep/remove/move.
- Remove selected tracked files from git and local disk.
- Decide destinations for “keep but move” items (e.g., `docs/archive/` vs. local-only).
- Handle untracked local artifacts (delete or move into an ignored location).
- Add scoped ignore rules to prevent re-adding local-only artifacts.

## Scope
- In: root-level PDFs/MDs/JS artifacts, untracked local notes, `.gitignore` updates, cleanup commits.
- Out: refactors, content edits to retained docs, bulk doc moves beyond agreed destinations.

## Files and entry points
- Repo root tracked artifacts (PDF/MD/JS files)
- `.gitignore`
- `fraud_proof_document.js` (tracked root artifact)

## Data model / API changes
- None.

## Action items
[x] Enumerate tracked root PDFs/MDs/JS (e.g., `git ls-files` + filter) and classify: keep, remove, or move to `docs/archive/` (or other folder you pick).
[x] Enumerate untracked root artifacts and classify: delete vs. move to a local-only folder (e.g., `local/`).
[x] Confirm keepers (likely `README.md`, `CHANGELOG.md`, any intentional docs) and destinations for “move” items; lock the removal list.
[x] `git rm` the removal set (including `fraud_proof_document.js` if confirmed) and, if applicable, `git mv` any “keep but relocate” items into the chosen folder.
[x] Delete or relocate untracked local artifacts into the ignored local-only folder (backup first if needed).
[x] Update `.gitignore` with narrow root-scoped patterns for local PDFs/MDs/JS and the local-only folder; avoid patterns that match subdirectories unintentionally.
[x] Validate with `git status -s`, `git diff --stat`, and a root tracked-file listing; ensure only intentional files remain at repo root.
[ ] Commit cleanup with a clear message; summarize what was removed/moved and where local-only artifacts now live.

## Findings (steps 1–3)
- Tracked root PDFs/MD/JS (via `git ls-files` filtered to root, sorted):
  - `1-s2.0-S0014488625003929-main.pdf`
  - `CALLBACK_LEAK_FIX_TESTING.md`
  - `CHANGELOG.md`
  - `cmv.md`
  - `difopein.md`
  - `enabled_field_styling_debug.md`
  - `Executive Summary.pdf`
  - `fournier.md`
  - `fraud_proof_document.js`
  - `geometry_invalidation_analysis.md`
  - `geometry_reactive_fix.md`
  - `INTEGRATION_BRANCH_READY.md`
  - `ipn_2022_retreat_1.pdf`
  - `ipsc-excitatory-neurons_neurite-outgrowth_fluorescent-protein-transduction.pdf`
  - `MANIFESTO.md`
  - `MicroTAS2024_Program.pdf`
  - `Molecular-Mechanism-of-AMPA-Receptor-Modulation-by.pdf`
  - `montages.pdf`
  - `OMERO_ZMQ_BACKEND_BUG.md`
  - `openhcs_polymorphic_design_analysis.md`
  - `Optimal-Degrees-of-Synaptic-Connectivity_2017_neur.pdf`
  - `paper.pdf`
  - `PIIS002192581931508X.pdf`
  - `PIIS0021925819827291.pdf`
  - `PIIS0896627317301022.pdf`
  - `PIPELINE_EDITOR_REACTIVE_LABELS_FIX.md`
  - `PR55_CODE_QUALITY_ASSESSMENT.md`
  - `PR55_FINAL_SCOPE.md`
  - `race_condition_fix_debounced_geometry.md`
  - `README.md`
  - `Small-Molecule-Stabilization-of-14-3-3-Protein-Pro.pdf`
  - `text_styling_invalidation_fix.md`
  - `THREAD_LOCAL_GLOBAL_ARCHITECTURE.md`
  - `toplas_appendix_restructure_plan.md`
  - `UI_ANTI_DUCKTYPING_PR.md`
- Untracked root artifacts (from `git status -s`):
  - `BATCH_FLASH_LABEL_OPTIMIZATION.md`
  - `scripts/napri/` (directory)
  - `text_selection_implementation_plan.md`
  - `text_selection_implementation_summary.md`
  - `unsaved_changes_indicator_implementation_plan.md`
- Decisions/next moves (post step 3):
  - Keepers: `README.md`, `CHANGELOG.md`.
  - Removals executed via `git rm`: all tracked root PDFs/MDs/JS listed above **except** `README.md`, `CHANGELOG.md`.
  - Untracked artifacts moved into `local/` (ignored): `BATCH_FLASH_LABEL_OPTIMIZATION.md`, `text_selection_implementation_plan.md`, `text_selection_implementation_summary.md`, `unsaved_changes_indicator_implementation_plan.md`, and `scripts/napri/`.
  - Guardrails added in `.gitignore`: ignore root-level `*.pdf`, `*.md`, `*.js` with exceptions for `README.md`, `CHANGELOG.md`; ignore `local/`; keep `plans/root-artifact-cleanup.md` tracked while other `plans/*` stay ignored.
  - Root tracked PDFs/MD/JS now: `README.md`, `CHANGELOG.md` (from `git ls-files` filter).
  - Validation snapshot:
    - `git status -s`: staged deletions for 33 root artifacts; unstaged changes in `.gitignore` and `plans/root-artifact-cleanup.md` (to be staged), no other working changes.
    - `git diff --stat --cached`: shows deletions of the 33 root artifacts (PDF/MD/JS).
    - `git ls-files` root filter: only `README.md`, `CHANGELOG.md` remain.

## Testing and validation
- `git status -s`
- `git diff --stat HEAD~1`
- `git ls-files -z | awk -v RS='\0' -F/ 'NF==1 && $0 ~ /\.(md|pdf|js)$/ {print $0}'`

## Risks and edge cases
- Removing documents that should remain tracked (e.g., intentional root docs); mitigate via explicit keep list before `git rm`.
- Overly broad ignore patterns hiding needed files elsewhere in the repo; mitigate by root-scoping patterns.
- Accidental loss of local-only files if not backed up before deletion; mitigate by moving to an ignored `local/` folder instead of deleting.

## Open questions
- Which root PDFs/MDs should remain tracked (e.g., `README.md`, `CHANGELOG.md`)?
- Should `fraud_proof_document.js` be removed or moved under `docs/`?
- Preferred destination for “keep but move” artifacts (e.g., `docs/archive/`, `docs/research/`, or similar)?
