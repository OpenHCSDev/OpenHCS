# Restructuring Plan for TOPLAS Submission

## Target Venue: ACM TOPLAS (Transactions on Programming Languages and Systems)

**Journal characteristics:**
- 20-40 pages typical
- 10,000-20,000 words
- ~1,500-3,000 lines
- Comprehensive treatment expected
- All details, all proofs, extensive empirical validation

## Current State
- **1,620 lines**
- **13 case studies**
- Real substance (theorems, Lean proofs, architectural case studies)
- **Problems:** AI-generated structure, contributions buried, repetitive format

## Target State for TOPLAS
- **~1,800 lines** (slight expansion)
- **Keep all 13 case studies** (journals value comprehensive validation)
- **Keep all 5 algorithms** (complete formalization)
- **Keep full Lean proofs** (machine verification is a selling point)
- **Fix structure, remove repetition, formalize voice**

---

## What TOPLAS Readers Expect

### Comprehensive Coverage
- All case studies (not a subset)
- Full formal development (all algorithms)
- Complete proofs (Lean code included)
- Thorough related work
- Discussion of limitations

### Clear Contributions
- Stated upfront in Introduction
- Positioned against prior work
- Empirical validation

### Academic Rigor
- Formal voice throughout
- No AI-isms or verbose transitions
- Precise terminology

---

## Core Problem: Not Length, But Structure

### Issue 1: Contributions Buried
**Problem:** Key theorems scattered, greenfield distinction is Section 6
**Fix:** Add Introduction with contributions upfront, move greenfield to Section 4

### Issue 2: Repetitive Format
**Problem:** All 13 case studies use identical template
**Fix:** Vary presentation, consolidate tables, narrative flow

### Issue 3: AI-Generated Voice
**Problem:** "In conclusion...", "To summarize...", "Key insight:"
**Fix:** Remove transitional fluff, formalize language

### Issue 4: Duplicate Section Numbers
**Problem:** Two sections numbered "7" (lines 219 and 239 in current draft)
**Fix:** Renumber all sections after restructuring

---

## New Section Structure

### 1. Abstract (KEEP AS-IS)
**Current:** 29 lines
**Status:** Good, no changes needed

---

### 2. Introduction (NEW - CRITICAL)
**Current:** Missing
**Target:** ~100 lines

**Must include:**

1. **Problem Statement** (1 paragraph)
   - Languages with explicit inheritance (Python, Java, C++) use nominal typing
   - Is this a stylistic choice or a formal necessity?
   - Prior work (Malayeri & Aldrich) shows tradeoffs but no definitive answer

2. **Our Thesis** (1 paragraph)
   - Nominal typing is mandatory for systems requiring provenance tracking
   - Provenance = knowing which type provided a value
   - Duck typing is proven impossible for this task

3. **Contributions** (bulleted list)
   - Formal proof: E(nominal) = O(1), E(duck) = Ω(n) (strict dominance)
   - Dual-axis resolution algorithm with O(1) complexity
   - Machine-checked verification in Lean 4 (including duck typing impossibility)
   - Empirical validation: 13 case studies from production bioimage analysis platform
   - Architectural patterns: metaclass registration, bidirectional type registries, MRO-based resolution

4. **Empirical Context: OpenHCS** (3 paragraphs)

   **What it does:**
   OpenHCS is a bioimage analysis platform. Pipelines are compiled before execution — errors surface at definition time, not after processing starts. The GUI and Python code are interconvertible: design in GUI, export to code, edit, re-import. Changes to parent config propagate automatically to all child windows.

   **Why it matters for this paper:**
   The system requires knowing *which type* provided a value, not just *what* the value is. Dual-axis resolution walks both the context hierarchy (global → plate → step) and the class hierarchy (MRO) simultaneously. Every resolved value carries provenance: (value, source_scope, source_type). This is only possible with nominal typing — duck typing cannot answer "which type provided this?"

   **Key architectural patterns (detailed in Section 6):**
   - `@global_pipeline_config` decorator chain: one decorator spawns a 5-stage type transformation (Case Study 7)
   - Dual-axis resolver: MRO IS the priority system — no custom priority function exists (Case Study 8)
   - `ObjectState`: single source of truth with bidirectional type registry lookup (Case Study 9)

5. **Roadmap** (1 paragraph)
   - Section 3: Preliminaries and type system foundations
   - Section 4: Greenfield vs retrofit distinction
   - Section 5: Core theorems (complexity bounds)
   - Section 6: Empirical validation (13 case studies)
   - Section 7: Formal algorithms and Lean verification
   - Section 8: Related work

---

### 3. Preliminaries (KEEP ALL, REORDER SLIGHTLY)
**Current:** Sections 1-3 (139 lines)
**Target:** ~150 lines (slight expansion)

**Section 3.1: Definitions (KEEP)**
- Definition 1.1: Class
- Definition 1.2-1.5: Typing disciplines
**Lines:** 29 (no change)

**Section 3.2: The type() Constructor (KEEP ALL)**
- Theorem 2.1: Completeness
- Theorem 2.2: Semantic Minimality
- Theorem 2.3: Practical Minimality
- Definition 2.4: Two-Axis Semantic Core
- Theorem 2.5: Orthogonality of Semantic Axes

**Current problem:** Section 2.2 "Semantic vs Practical Minimality" reads like a tangent
**Fix for TOPLAS:** This IS interesting for PL researchers - keep it, but tighten prose slightly
**Lines:** 98 → 90 (minor tightening, keep all theorems)

**Section 3.3: C3 Linearization (KEEP)**
- Theorem 3.1: C3 Optimality (cite Barrett et al.)
- Corollary 3.2: MRO is deterministic
**Lines:** 12 (no change)

**Total Section 3:** ~150 lines

---

### 4. The Greenfield Distinction (MOVE UP FROM SECTION 6)
**Current position:** Section 6 (after core theorems, buried)
**New position:** Section 4 (before core theorems)

**Why:** This is a KEY contribution - explains when structural typing IS valid (retrofit) vs when nominal is mandatory (greenfield)

**Current:** Section 6 "Minimal System: namespace-Only Classes" (88 lines)
**Target:** ~90 lines (keep almost all)

**Keep:**
- Theorem 6.1: Structural Typing Is Correct for Namespace-Only Systems
- Corollary 6.2: Go's Design Is Consistent
- Corollary 6.3: TypeScript's Design Is Consistent
- Theorem 6.4: Bases Mandates Nominal
- The critical observation table

**Minor cuts:**
- Redundant Python code examples (will appear in case studies)

**Lines:** 88 → 90 (keep essentially all content, minor expansion for clarity)

---

### 5. Core Theorems (KEEP, MERGE SCATTERED SECTIONS)
**Current:** Sections 4, 5, 7, 8 (scattered across paper)
**Target:** ~100 lines (consolidated)

**Merge into one coherent section:**

**Section 5.1: Error Localization**
- Theorem 4.1: E(nominal) = O(1)
- Theorem 4.2: E(structural) = O(k)
- Theorem 4.3: E(duck) = Ω(n)
- Corollary 4.4: Strict Dominance

**Section 5.2: Information Scattering**
- Theorem 5.1: Duck Typing Scatters
- Theorem 5.2: Nominal Typing Centralizes
- Corollary 5.3: Maintenance Entropy

**Section 5.3: Main Result**
- Theorem 8.1: Nominal Typing Is Uniquely Correct (from current Section 8)

**Lines:** ~100 (consolidated from scattered sections)

---

### 6. Empirical Validation: OpenHCS Case Studies (RESTRUCTURE, KEEP ALL 13)
**Current:** Section 11 (~700 lines, repetitive structure)
**Target:** ~650 lines (less repetition, same content)

**Problem:** Each case study follows identical template:
```
Case Study X: Title

**Structural view:** ...
**Nominal view:** ...
**Why it matters:** ...
**Why duck typing fails:** ...
```

This gets repetitive after 13 iterations.

**Solution:** Vary the presentation, use narrative flow.

**Restructured format:**

**Section 6.1: Introduction to Case Studies** (NEW - 1 paragraph)
- OpenHCS context
- Why 13 examples matter (comprehensive validation)
- Preview of patterns
- State once: "Duck typing fails for all 13 because..." (don't repeat per-study)

**Section 6.2-6.14: Individual Case Studies** (13 × ~45 lines)

**Pre-assigned presentation types (vary structure to avoid repetition):**

| Study | Title | Presentation Type |
|-------|-------|-------------------|
| 1 | WellFilterConfig Hierarchy | Code-first |
| 2 | ParameterInfo Discriminated Unions | Problem-first |
| 3 | MemoryType Converters | Code-first |
| 4 | StreamingConfig Polymorphism | Problem-first |
| 5 | PR #44 Migration | Architectural-change-first |
| 6 | AutoRegisterMeta | Pattern-first |
| 7 | @global_pipeline_config Chain | Problem-first (flagship) |
| 8 | Dual-Axis Resolver | Code-first |
| 9 | GlobalConfigMeta __instancecheck__ | Code-first |
| 10 | DynamicInterfaceMeta | Pattern-first |
| 11 | _FRAMEWORK_CONFIG | Code-first |
| 12 | MemoryType Method Injection | Code-first |
| 13 | Bidirectional Type Registry | Problem-first |

**Presentation type definitions:**

**Code-first** (5 studies): Show code snippet immediately, then explain significance

**Architectural-change-first** (1 study): Describe what changed structurally (not line counts)
```
Case Study 1: Structurally Identical, Semantically Distinct Types

[Code snippet: WellFilterConfig vs StepWellFilterConfig]

These classes are structurally identical but participate in different
inheritance hierarchies. The MRO position determines resolution priority...
```

**Problem-first** (5 studies): Motivate the problem, then show solution
```
Case Study 7: Five-Stage Type Transformation

The @global_pipeline_config decorator chain demonstrates nominal typing's
power for systematic type manipulation. Starting from a base config...

[Then code snippet]
```

**Measurement-first** (1 study): Lead with architectural changes, not line counts
```
Case Study 5: Migration from Duck to Nominal Typing

PR #44 (90 commits, 106 files) migrated the UI layer from duck typing
to nominal typing. The migration eliminated hasattr()-based dispatch
tables and replaced them with ABC contracts, enabling fail-loud error
detection at class definition time rather than runtime.

Key architectural changes:
- Removed: 47 hasattr() probing calls in ParameterFormManager
- Added: AbstractFormWidget ABC with enforced interface contracts
- Result: Type errors caught at import time, not user interaction time
```

**Pattern-first** (2 studies): State abstract pattern, then show instance
```
Case Study 6: AutoRegisterMeta

Pattern: Metaclass-based auto-registration uses type identity as registry key.
This is impossible with duck typing because...

[Then concrete example]
```

**Section 6.15: Summary and Patterns** (NEW)
- Table 6.1: Comprehensive summary of all 13 patterns
- Common themes across case studies
- Nominal typing invariant

**Lines:** 700 → 650 (remove repetition, keep all studies)

---

### 7. Formalization and Verification (KEEP ALL, EXPAND DISCUSSION)
**Current:** Sections on "Formal Algorithm" and "Lean Verification" (349 lines)
**Target:** ~380 lines (expand discussion of what proofs guarantee)

**Section 7.1: Dual-Axis Resolution Algorithm**

**Keep all 5 algorithms:**
- Algorithm 1: GENERATE-LAZY-TYPE
- Algorithm 2: INJECT-FIELDS
- Algorithm 3: NORMALIZE
- Algorithm 4: RESOLVE (core)
- Algorithm 5: GETATTRIBUTE

**Keep all 7 invariants:**
- Invariant 1: Registry Bijection
- Invariant 2: Marker Preservation
- Invariant 3: Lazy Exclusion
- Invariant 4: Normalization Idempotence
- Invariant 5: Resolution Determinism
- Invariant 6: MRO Monotonicity
- Invariant 7: Lazy Transparency

**Keep theorems:**
- Theorem 7.1: Completeness of Resolution
- Theorem 7.2: Provenance Preservation
- Corollary 7.3: Duck Typing Incompleteness

**Lines:** ~150 (keep all)

**Section 7.2: Machine-Checked Verification in Lean 4**

**Keep:**
- Full Lean code listings
- Type universe and registry definitions
- MRO formalization
- Scope stack and config context
- The RESOLVE algorithm in Lean
- All theorem statements

**Include duck typing impossibility proofs (NEW - already implemented):**
- DuckObject structure (fields as (String × Nat) pairs)
- structurallyEquivalent definition and equivalence relation proofs
- DuckRespecting function definition
- duck_provenance_indistinguishable theorem (Corollary 7.3)
- duck_provenance_absurdity theorem
- nominal_types_distinguishable contrast theorem

**Current Lean file status:**
| Component | Lines | Status |
|-----------|-------|--------|
| NominalResolution namespace | 157 | ✅ Compiles |
| DuckTyping namespace | 127 | ✅ Compiles |
| **Total** | 284 | ✅ No warnings |

**Expand:** Add discussion subsection (~30 lines)
- What the Lean proofs guarantee
- What they don't guarantee (assumes well-formed MRO)
- Verification status table
- The duck typing impossibility is proven from first principles
- Limitations and future work in verification

**Lines:** ~260 (expanded from 204, includes duck typing proofs)

**Total Section 7:** ~410 lines (includes duck typing impossibility proofs)

---

### 8. Related Work (EXPAND FOR TOPLAS)
**Current:** 99 lines
**Target:** ~120 lines (more thorough for journal)

**Current structure is good (5 subsections):**
- 8.1: Type Theory Foundations
- 8.2: Practical Hybrid Systems
- 8.3: Metaprogramming Complexity
- 8.4: Behavioral Subtyping
- 8.5: Positioning This Work

**Expand:**
1. **More detail on Malayeri & Aldrich's empirical study**
   - Their finding: structural typing would benefit Java (300% interface explosion)
   - Our work: formalizes when this tradeoff favors each approach

2. **Add gradual typing discussion**
   - TypeScript, Mypy, Sorbet
   - How our provenance argument relates to gradual guarantees

3. **Connect to design patterns literature**
   - Factory pattern vs metaclass registration
   - Template method vs MRO-based resolution

4. **Expand positioning table**
   - Add row for gradual typing
   - Add row for trait systems (Rust, Scala)

**Lines:** 99 → 120

---

### 9. Discussion (NEW SECTION FOR TOPLAS)
**Target:** ~100 lines

**TOPLAS expects this section:**

**Section 9.1: Limitations** (~40 lines)

| Limitation | Honest Statement |
|------------|------------------|
| **Diamond inheritance** | Theorems assume well-formed MRO; pathological diamonds can break C3 linearization entirely (Python raises TypeError) |
| **Runtime overhead** | Provenance tracking stores (value, scope_id, source_type) tuples — memory overhead per resolved field |
| **Not universal** | Simple scripts, one-off tools, and prototype code don't benefit from provenance tracking |
| **Python-specific** | Theorems rely on C3 linearization and `type(name, bases, namespace)`; other languages may differ |
| **Metaclass complexity** | The @global_pipeline_config chain requires understanding 5 metaprogramming stages |
| **Lean proofs assume well-formedness** | Registry.wellFormed and MRO monotonicity are axioms, not derived |

**Section 9.2: When Structural Typing Is Appropriate** (~30 lines)
- Retrofit scenarios (integrating independent components)
- Languages without inheritance (Go, early JavaScript)
- Theorem 6.1 formalizes exactly when

**Section 9.3: Future Work** (~25 lines)
- Extend to other nominal languages (Java, C++, Rust)
- Formalize the greenfield vs retrofit distinction more rigorously
- Explore gradual nominal/structural typing
- Apply to trait systems

**Section 9.4: Implications for Language Design** (~15 lines)
- Language designers should provide both
- TypeScript's "branding" workaround validates our thesis
- Python's descriptor protocol + MRO is near-optimal

**Lines:** ~100 (new)

---

### 10. Conclusion (KEEP, MINOR POLISH)
**Current:** 19 lines
**Target:** 20 lines

**Keep the 7 points:**
1. Provenance tracking requires nominal typing
2. Type-keyed dispatch → O(1) vs O(n)
3. Hierarchy-aware resolution needs MRO
4. Contract enforcement at definition time
5. Virtual base class semantics
6. Dynamic class generation
7. Discriminated unions

**Add:** 1 sentence on broader impact
- "These results provide formal justification for architectural decisions in large-scale nominal systems."

**Lines:** 19 → 20

---

### 11. References (EXPAND SLIGHTLY)
**Current:** 16 references
**Target:** ~20 references

**Add:**
- Papers on gradual typing (Siek & Taha)
- TypeScript design rationale
- More on trait systems (Schärli et al.)
- Design patterns (Gang of Four)

**Lines:** 16 → 20

---

## Revised Line Count Summary for TOPLAS

| Section | Current | Proposed | Change | Notes |
|---------|---------|----------|--------|-------|
| Abstract | 29 | 29 | 0 | Keep |
| **Introduction** | 0 | 150 | +150 | NEW (includes OpenHCS context) |
| Preliminaries (1-3) | 139 | 150 | +11 | Minor tightening |
| **Greenfield Distinction** | 88 | 90 | +2 | Move from Sec 6 → Sec 4 |
| Core Theorems (4-5, 8) | 96 | 100 | +4 | Consolidate scattered |
| Concession Hierarchy (7) | 19 | 0 | -19 | Merge into Sec 4 |
| Counterexample (9) | 63 | 0 | -63 | Becomes Case Study 1 |
| Practical Implications (10) | 10 | 0 | -10 | Merge into intro |
| **Case Studies (11)** | ~700 | ~650 | -50 | Restructure, keep all 13 |
| Formal Algorithm + Lean | 349 | 410 | +61 | Expand + duck typing proofs |
| Related Work | 99 | 120 | +21 | Expand for journal |
| **Discussion** | 0 | 110 | +110 | NEW (expanded limitations) |
| Conclusion | 19 | 20 | +1 | Minor polish |
| References | 16 | 20 | +4 | Add more papers |
| **TOTAL** | **~1,620** | **~1,850** | **+230** | Appropriate for TOPLAS |

---

## Specific Changes to Make

### High Priority (Structure)

1. **Add Introduction (150 lines)**
   - Problem statement
   - Thesis
   - OpenHCS context (what, why architecturally interesting, scale, why nominal)
   - Contributions (upfront!)
   - Empirical context
   - Roadmap

2. **Move Greenfield Distinction from Section 6 → Section 4**
   - This is KEY contribution
   - Should come before case studies, not after

3. **Consolidate Core Theorems**
   - Currently scattered across Sections 4, 5, 7, 8
   - Merge into one coherent Section 5

4. **Add Discussion section (100 lines)**
   - Limitations
   - When structural IS appropriate
   - Future work
   - Implications for language design

### Medium Priority (Remove Repetition)

5. **Restructure Case Studies**
   - Keep all 13
   - Vary presentation (not identical template)
   - Add comprehensive Table 6.1 at end

6. **Consolidate Tables**
   - Currently: small tables throughout
   - Better: one Table 6.1 summarizing all patterns

7. **Remove repetitive "Why duck typing fails" sections**
   - Said once in introduction to case studies
   - Individual studies focus on specific insights

### Low Priority (Voice/Tone)

8. **Remove AI-isms (comprehensive list)**
   - "In conclusion..." → cut
   - "To summarize..." → cut
   - "Observation:" → "We observe that" or remove
   - "Key insight:" → integrate into narrative
   - "This is crucial because..." → cut or rephrase
   - "It's worth noting that..." → cut
   - "Interestingly,..." → cut
   - "Importantly,..." → cut
   - "**Why duck typing fails:**" → remove as header, state once in Section 6.1
   - "This matters because..." → cut
   - "The key point is..." → cut
   - Excessive `| table |` formatting → convert to prose where appropriate
   - Bold headers that repeat the same pattern → vary or remove

9. **Formalize Language**
   - "Duck typing is Ω(n)" → "Theorem 4.3 establishes E(duck) = Ω(n)"
   - "This is why..." → "This follows from..."
   - Consistent terminology throughout

10. **Polish Transitions**
    - Remove verbose section conclusions
    - Smoother flow between sections
    - Forward/backward references

---

## What This Achieves for TOPLAS

### Length: Appropriate
- Target: 1,500-2,000 lines for comprehensive journal paper
- Achieved: ~1,760 lines
- Within expected range

### Completeness: Full
- All 13 case studies (comprehensive empirical validation)
- All 5 algorithms (complete formalization)
- Full Lean development (machine verification)
- Discussion section (expected in journals)

### Structure: Fixed
- Contributions upfront (Introduction)
- Logical flow (Greenfield → Theorems → Case Studies → Formalization)
- No buried insights

### Voice: Academic
- Remove AI-generated fluff
- Formalize language
- Consistent tone

### Novelty: Clear
- Positioned against prior work
- Contributions stated explicitly
- Empirical validation comprehensive

---

## Implementation Order

### Phase 1: Structural Changes (no edits to existing content yet)
1. Rename current file: `nominal_typing_proof_v1_draft.md`
2. Create new file: `nominal_typing_proof_v2_toplas.md`
3. Create skeleton with new section ordering
4. Copy unchanged sections (Abstract, some Preliminaries)

### Phase 2: New Sections
1. Write Introduction (150 lines, includes OpenHCS context)
2. Write Discussion (100 lines)
3. Expand Related Work (+21 lines)
4. Expand Lean discussion (+31 lines)

### Phase 3: Reorganize Existing Content
1. Move Greenfield Distinction (Section 6 → Section 4)
2. Consolidate Core Theorems (merge scattered sections)
3. Merge Counterexample into Case Study 1
4. Merge Practical Implications into Introduction

### Phase 4: Restructure Case Studies

**4.1: Write Section 6.1 Introduction (~1 paragraph)**
- OpenHCS context (bioimage analysis platform, 50k LOC)
- Why 13 examples matter (comprehensive validation across pattern types)
- State ONCE: "Duck typing fails for all 13 because provenance requires type identity"
- Preview the pattern taxonomy (type discrimination, metaclass registration, MRO resolution, bidirectional lookup)

**4.2: Create Table 6.1 (Comprehensive Case Study Summary)**

| Study | Pattern | Duck Failure Mode | Nominal Mechanism |
|-------|---------|-------------------|-------------------|
| 1 | Type discrimination | Structural equivalence | `isinstance()` + MRO position |
| 2 | Discriminated unions | No exhaustiveness check | `__subclasses__()` enumeration |
| 3 | Converter dispatch | O(n) attribute probing | `type()` as dict key |
| 4 | Polymorphic config | No interface guarantee | ABC contracts |
| 5 | Architecture migration | Fail-silent at runtime | Fail-loud at definition |
| 6 | Auto-registration | No type identity | `__init_subclass__` hook |
| 7 | Type transformation | Cannot track lineage | 5-stage `type()` chain |
| 8 | Dual-axis resolution | No scope × MRO product | Registry + MRO traversal |
| 9 | Custom isinstance | Impossible | `__instancecheck__` override |
| 10 | Dynamic interfaces | No interface identity | Metaclass-generated ABCs |
| 11 | Framework detection | Module probing fragile | Sentinel type in registry |
| 12 | Method injection | No target type | `type()` namespace manipulation |
| 13 | Bidirectional lookup | Two dicts, sync bugs | Single registry, `type()` keys |

**4.3: Apply pre-assigned presentation types (from Section 6 of this plan)**
- Code-first (5): Studies 1, 3, 8, 9, 11, 12
- Problem-first (5): Studies 2, 4, 7, 13
- Architectural-change-first (1): Study 5
- Pattern-first (2): Studies 6, 10

**4.4: For each case study, ensure:**
- NO "Why duck typing fails:" header (stated once in 6.1)
- Follows assigned presentation type
- ~45 lines max
- Links back to Table 6.1 row
- References relevant theorem (Theorem 5.1, Corollary 7.3, etc.)

**4.5: Remove from each study:**
- Repetitive duck typing failure explanation
- Redundant "Key insight:" headers
- Standalone "Observation:" blocks

### Phase 5: Voice and Tone
1. Remove AI-isms throughout
2. Formalize language
3. Polish transitions
4. Consistency pass

### Phase 6: Final Polish
1. Check all theorem numbering (may shift with reorganization)
2. Verify all forward/backward references
3. Consistency in terminology
4. Final read-through

---

## Success Criteria for TOPLAS Submission

### Quantitative
- [ ] ~1,750-1,850 lines total
- [ ] All 13 case studies included
- [ ] All 5 algorithms included
- [ ] Full Lean verification included (284 lines, both namespaces)
- [ ] Duck typing impossibility proofs included (Corollary 7.3 machine-checked)
- [ ] Introduction + Discussion sections added
- [ ] 120+ lines of Related Work
- [ ] No duplicate section numbers

### Qualitative
- [ ] Contributions stated in first 2 pages (Introduction)
- [ ] Greenfield distinction appears early (Section 4, not Section 6)
- [ ] No AI-generated repetition (see comprehensive AI-isms list)
- [ ] Academic voice throughout
- [ ] One comprehensive table (not many small ones)
- [ ] Theorems positioned clearly against prior work
- [ ] Case studies use varied presentation types (code-first, problem-first, etc.)

### TOPLAS-Specific
- [ ] Discussion of limitations (6 specific limitations identified)
- [ ] Future work section
- [ ] Comprehensive related work
- [ ] Full formal development (not condensed)
- [ ] Extensive empirical validation

### Test Questions
1. Can a PL researcher identify the novel contributions in 2 pages? (Introduction)
2. Is the greenfield vs retrofit distinction clear before case studies?
3. Are the 13 case studies varied in presentation (not template-repetitive)?
4. Does the Discussion section address limitations honestly (all 6)?
5. Is the positioning against Malayeri & Aldrich clear?
6. Is Corollary 7.3 (duck typing impossibility) machine-checked in Lean?

---

## Timeline Estimate

**Phase 1 (Structure):** 1 hour
- Rename files, create skeleton

**Phase 2 (New Sections):** 3-4 hours
- Write Introduction (1.5 hours)
- Write Discussion (1.5 hours)
- Expand Related Work (0.5 hours)
- Expand Lean discussion (0.5 hours)

**Phase 3 (Reorganize):** 2 hours
- Move sections around
- Consolidate theorems
- Merge scattered content

**Phase 4 (Restructure Case Studies):** 2-3 hours
- Most time-consuming
- Vary 13 case study presentations
- Create comprehensive table

**Phase 5 (Voice/Tone):** 2 hours
- Remove AI-isms
- Formalize language
- Polish throughout

**Phase 6 (Final):** 1 hour
- Check references
- Consistency pass
- Read-through

**Total:** 11-13 hours of focused work

---

## Next Steps

1. **Get approval on this plan**
2. **Execute Phase 1** (structure)
3. **Review skeleton before proceeding**
4. **Execute phases sequentially** (pause for review between each)
5. **Final review with Sumner** (after all phases complete)

---

## Notes

- This is a **journal plan**, not a conference plan
- Length is appropriate (~1,760 lines for TOPLAS)
- Keep comprehensive coverage (all case studies, algorithms, proofs)
- Main fixes: structure, voice, remove repetition
- NOT a condensing exercise - a reorganizing + polishing exercise
