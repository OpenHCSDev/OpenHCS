# Plan: Restructure Nominal Typing Proof Paper

## Current State
- **1,620 lines** (excessive)
- **13 case studies** (repetitive structure)
- AI-generated verbosity
- Real substance buried in structure

## Target State
- **~800 lines** (50% reduction)
- **5 core case studies** (condensed)
- Academic voice
- Contributions upfront

---

## Proposed Structure Changes

### Section 1: Introduction (NEW - currently missing)
**Current:** Jumps straight to Abstract + Definitions
**Change:** Add 1-page introduction that:
- States the problem: "Languages with explicit inheritance use nominal typing, but is this formally necessary?"
- Positions the work: "We prove nominal typing is mandatory for provenance-tracking systems"
- Outlines contributions upfront
- Previews empirical validation (OpenHCS)

**Lines:** Abstract (current) + 30 new lines of intro = ~80 lines total

---

### Section 2: Preliminaries (Condense Sections 1-3)
**Current:**
- Section 1: Definitions (29 lines)
- Section 2: type() Theorem (98 lines - TOO LONG)
- Section 3: C3 Linearization (12 lines)

**Problems:**
- Section 2.1 "Semantic vs Practical Minimality" is interesting but tangential
- Multiple examples that repeat the same point
- The "(bases, namespace)" insight is buried

**Change:**
1. Keep Definitions (1.1-1.5) as-is
2. **Condense type() Theorem:**
   - Keep Theorem 2.1 (Completeness)
   - **CUT Theorem 2.2** (Semantic Minimality) - interesting but not core
   - Keep Theorem 2.3 (Practical Minimality) - 1 paragraph
   - **CUT "Semantic Axes" discussion** - move insight to Section 6 (Minimal System)
3. Keep C3 as-is (prior work, just cite it)

**Lines:** 29 + 40 (condensed type()) + 12 = **~80 lines**
**Savings:** 98 - 40 = **58 lines cut**

---

### Section 3: Core Theorems (Keep Sections 4-5)
**Current:**
- Section 4: Error Localization Theorem (32 lines)
- Section 5: Information Scattering Theorem (19 lines)

**Change:** Keep both, these are core contributions.

**Lines:** **~50 lines** (no change)

---

### Section 4: The Greenfield Distinction (NEW - reorganize Section 6)
**Current:** Section 6 "Minimal System: namespace-Only Classes" (88 lines)

**Problem:** This contains the KEY insight but is buried as Section 6

**Change:**
1. Move this EARLIER (before case studies)
2. Rename: "Greenfield vs Retrofit: The Structural Typing Exception"
3. **Condense:**
   - Keep Theorem 6.1 (Structural Is Correct for Namespace-Only)
   - Keep Corollaries 6.2-6.3 (Go/TypeScript)
   - Keep Theorem 6.4 (Bases Mandates Nominal)
   - **CUT** the Python code example (redundant with case studies later)
4. This explains WHY structural typing exists (retrofit) vs WHY nominal is needed (greenfield with bases)

**Lines:** **~50 lines** (condensed from 88)
**Savings:** **38 lines cut**

---

### Section 5: Empirical Validation - OpenHCS Case Studies (MAJOR CONDENSE)
**Current:** Sections 11 (13 case studies, ~700 lines!!!)

**Problem:**
- 13 case studies with repetitive structure
- Each has "Why duck typing fails:" section
- Multiple tables repeating the same comparison

**Change:**
1. **Select 5 representative case studies:**
   - **Case Study 1: WellFilterConfig hierarchy** (structurally identical, semantically distinct)
   - **Case Study 2: Dual-axis resolver** (the algorithm, provenance tracking)
   - **Case Study 3: MemoryTypeConverter** (runtime type generation via `type()`)
   - **Case Study 4: @global_pipeline_config chain** (5-stage type transformation)
   - **Case Study 5: PR #44 outcomes** (measured migration: 55% reduction)

2. **CUT:**
   - ParameterInfo (redundant with WellFilterConfig - both show structural equivalence problem)
   - StreamingConfig (redundant with WellFilterConfig)
   - AutoRegisterMeta (interesting but not core)
   - GlobalConfigMeta (interesting but not core)
   - DynamicInterfaceMeta (interesting but not core)
   - _FRAMEWORK_CONFIG (redundant with MemoryTypeConverter)
   - Module __getattr__ (interesting but not core)
   - Dynamic method injection (redundant)

3. **Restructure each case study:**
   - **Before:** "Structural view / Nominal view / Why it matters / Why duck typing fails" (verbose)
   - **After:** "Code snippet → Key insight → Measurement (if applicable)" (concise)

4. **Add ONE summary table** at the end covering all patterns

**Lines:** ~250 lines (5 case studies × 50 lines each)
**Savings:** 700 - 250 = **450 lines cut**

---

### Section 6: Formal Algorithm (Condense Section with Lean Proof)
**Current:**
- Formal Algorithm: Lazy Configuration Resolution (145 lines)
- Formal Verification in Lean 4 (204 lines)

**Problems:**
- Repeats the dual-axis resolver from Case Study 2
- Lean code snippets are verbose
- Five algorithms with invariants is overkill

**Change:**
1. **Merge** "Formal Algorithm" + "Lean Verification" into one section
2. **Condense algorithms:**
   - Keep RESOLVE (Algorithm 4) - this is the core
   - Keep GETATTRIBUTE (Algorithm 5) - shows usage
   - **CUT** Algorithms 1-3 (type generation, field injection, normalization) - interesting but details
3. **Lean proofs:**
   - Keep theorem statements
   - Keep ONE complete proof (resolution_completeness)
   - **CUT** the duck typing model (interesting but can summarize)
   - Point to GitHub for full Lean development

**Lines:** ~150 lines (condensed)
**Savings:** 349 - 150 = **199 lines cut**

---

### Section 7: Related Work (Tighten)
**Current:** 99 lines

**Problems:**
- Repeats points made earlier
- Too detailed on each paper

**Change:**
1. Keep the structure (5 subsections)
2. **Cut repetition:** Don't re-explain what nominal/structural typing is
3. **Be concise:** 1-2 sentences per paper, focus on how it differs from our work
4. **Positioning table** at the end (current table is good, keep it)

**Lines:** **~60 lines** (condensed)
**Savings:** 99 - 60 = **39 lines cut**

---

### Section 8: Conclusion (Keep but condense)
**Current:** "Conclusion: The Nominal Typing Thesis" (19 lines)

**Change:**
- Keep the 7 points but make them a bulleted list (not prose)
- Add 1 paragraph on future work
- Keep fundamental theorem + corollary

**Lines:** **~20 lines** (no change needed, it's already concise)

---

## Line Count Summary

| Section | Current | Proposed | Savings |
|---------|---------|----------|---------|
| Abstract + Intro | 29 | 80 | -51 (added intro) |
| Preliminaries (1-3) | 139 | 80 | **+59** |
| Core Theorems (4-5) | 51 | 50 | **+1** |
| Greenfield Distinction (reorganized 6) | 88 | 50 | **+38** |
| Concession Hierarchy (7) | 19 | 0 (merge into Section 4) | **+19** |
| Main Result (8) | 14 | 0 (merge into Section 4) | **+14** |
| Counterexample (9) | 63 | 0 (becomes Case Study 1) | **+63** |
| Practical Implications (10) | 10 | 0 (cut or move to intro) | **+10** |
| Case Studies (11) | ~700 | 250 | **+450** |
| Formal Algorithm + Lean | 349 | 150 | **+199** |
| Related Work | 99 | 60 | **+39** |
| Conclusion | 19 | 20 | -1 |
| References | 16 | 16 | 0 |
| **TOTAL** | **~1,620** | **~776** | **~844 saved** |

---

## Specific Cuts

### High-Value Cuts (necessary)
1. **Section 2.1 "Semantic vs Practical Minimality"** - 58 lines - interesting tangent, not core
2. **8 of 13 case studies** - 450 lines - repetitive, keep only representative ones
3. **Algorithms 1-3 in formal section** - 100 lines - implementation details
4. **Lean duck typing model** - 99 lines - can summarize result, point to GitHub

### Medium-Value Cuts (should do)
5. **Section 6 Python code examples** - 30 lines - redundant with case studies
6. **Related Work repetition** - 39 lines - tighten prose
7. **Section 7 "Concession Hierarchy"** - 19 lines - merge into Section 4

### Low-Value Cuts (optional)
8. **Table repetitions** - consolidate multiple tables into one summary table

---

## Tone Adjustments

### Remove AI-isms
- **"In conclusion..." / "To summarize..."** - cut transitional fluff
- **"Observation:" / "Key insight:"** - formalize or remove
- **Repetitive section conclusions** - each section doesn't need a summary

### Formalize Language
- **Current:** "Duck typing is Ω(n) where nominal is O(1); strictly dominated"
- **Better:** "Theorem 4.4 establishes strict dominance: E(nominal) = O(1) < Ω(n) = E(duck)."

- **Current:** "Why duck typing fails: All converters have identical signatures..."
- **Better:** "Structurally identical converters require nominal identity for dispatch."

---

## New Section Ordering

1. **Abstract** (keep)
2. **Introduction** (NEW - 1 page)
3. **Preliminaries** (condensed Sections 1-3)
4. **Core Theorems** (Sections 4-5)
5. **The Greenfield Distinction** (reorganized Section 6)
6. **Empirical Validation: OpenHCS** (5 case studies)
7. **Formalization and Verification** (Algorithms + Lean)
8. **Related Work** (condensed)
9. **Conclusion**
10. **References**

---

## What This Achieves

**Length:** 1,620 → ~780 lines (52% reduction)
**Structure:** Less repetitive, contributions upfront
**Voice:** More academic, less AI-verbose
**Impact:** Core contributions clear, substance preserved

**Keeps:**
- All theorems (4.1-4.4, 5.1-5.2, 6.1-6.4, 7.1-7.2)
- Lean proofs (verified claims)
- Measured outcomes (55% reduction, 82% reduction, etc.)
- Real code examples (WellFilterConfig, dual-axis resolver)

**Cuts:**
- Repetitive case studies (8 of 13)
- Tangential discussions (semantic minimality)
- Implementation details (type generation algorithms)
- Verbose transitions and explanations

---

## Next Steps (when approved)

1. Create new condensed version in `docs/papers/nominal_typing_proof_v2.md`
2. Keep original as `nominal_typing_proof_v1_draft.md`
3. Implement changes section by section
4. Review each section before moving to next
5. Final pass for tone/voice consistency

---

## Implementation Order

### Phase 1: Structure (no content changes yet)
1. Rename current file to `nominal_typing_proof_v1_draft.md`
2. Create skeleton for v2 with new section ordering
3. Copy over sections that stay unchanged (Abstract, Core Theorems)

### Phase 2: Section-by-section condensing
1. Write new Introduction
2. Condense Preliminaries
3. Reorganize Greenfield Distinction
4. Select and condense 5 case studies
5. Condense Formal Algorithm + Lean
6. Tighten Related Work
7. Polish Conclusion

### Phase 3: Polish
1. Remove AI-isms throughout
2. Formalize language
3. Consistency pass
4. Final read-through

---

## Success Criteria

**Quantitative:**
- [ ] ~800 lines total
- [ ] 5 case studies (down from 13)
- [ ] 1 summary table (instead of multiple)
- [ ] All theorems preserved

**Qualitative:**
- [ ] Contributions clear in first 2 pages
- [ ] No repetitive structure
- [ ] Academic voice throughout
- [ ] Lean proofs highlighted (not buried)

**Test:** Could Sumner read this and immediately identify the novel contributions?
