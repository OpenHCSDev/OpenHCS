# TOPLAS Paper Restructure Plan: Appendix Migration

## Objective
Move combative, defensive, and preemptive content to appendix while preserving all technical substance. Main text reads as standard academic contribution; appendix serves as ammunition for rebuttal phase.

---

## PHASE 1: Content Audit

### 1.1 Sections to Move Entirely

| Current Location | Content Description | New Appendix Location |
|------------------|---------------------|----------------------|
| Section 3.6 | "Attack Surface Closure" - enumerated rejection positions | Appendix B.1 |
| Wherever located | "Challenge to Reviewers" subsection | Appendix B.2 |
| Section 2.4.2 (partial) | "Epistemic failure of the field" commentary | Appendix C.1 |

### 1.2 Section Headers to Rename

| Current Header | Issue | New Header |
|----------------|-------|------------|
| "The Debate Is Over" | Combative framing | "Summary of Results" or "Conclusions" |
| "Attack Surface Closure" | Adversarial tone | "Completeness and Robustness Analysis" (in appendix) |
| Any header with "Challenge" | Direct confrontation | Remove or neutralize |

### 1.3 Specific Theorems/Lemmas to Relocate

These are theorems that exist specifically to preempt objections rather than advance the core argument:

| Theorem | Purpose | Action |
|---------|---------|--------|
| Theorem 3.32 (Model Completeness) | Preempts "model incomplete" objection | Keep reference in main text, move full proof to Appendix B.3 |
| Theorems 3.34-3.36 (No Tradeoff) | Preempts "duck typing has tradeoffs" | Keep statement in main, move detailed proof to Appendix B.4 |
| Lemma 3.37 (Axiom Definitional) | Preempts "axioms assumptive" | Move entirely to Appendix B.5 |
| Theorem 3.39 (Extension Impossibility) | Preempts "clever extension could fix" | Keep statement, move proof to Appendix B.6 |
| Theorem 3.55 (Independence) | Preempts "dominance ≠ migration" | Move to Appendix B.7 |

### 1.4 Prose Passages to Edit

Locate and modify any passages containing:

- [ ] "The field failed..."
- [ ] "This should have been obvious..."
- [ ] "No one asked..."
- [ ] "asymmetric burden of proof"
- [ ] "epistemic failure"
- [ ] "for 34 years..."
- [ ] Direct second-person address to reviewers
- [ ] Rhetorical questions implying field negligence
- [ ] "incoherent" used polemically vs. technically (keep technical uses)

---

## PHASE 2: New Appendix Structure

### Proposed Appendix Organization

```
Appendix A: Lean Proof Artifacts
  A.1 Core Type System Proofs
  A.2 Information-Theoretic Proofs  
  A.3 Complexity Bound Proofs
  A.4 Impossibility Proofs
  A.5 Build Instructions and Verification

Appendix B: Completeness and Robustness Analysis
  B.1 Comprehensive Objection Analysis (formerly "Attack Surface Closure")
  B.2 Detailed Counterargument Proofs
  B.3 Model Completeness (Theorem 3.32 full proof)
  B.4 Tradeoff Impossibility (Theorems 3.34-3.36 full proofs)
  B.5 Axiom Justification (Lemma 3.37)
  B.6 Extension Impossibility (Theorem 3.39 full proof)
  B.7 Dominance-Migration Independence (Theorem 3.55)

Appendix C: Historical and Methodological Context
  C.1 On the Epistemic History of Typing Discipline Selection
  C.2 Why Formal Treatment Was Delayed
  C.3 Implications for PL Pedagogy

Appendix D: Extended Case Studies
  D.1-D.13 Full code listings and analysis for each case study
```

### Appendix B.1 Reframing

**Current framing (Section 3.6):**
> "To reject this paper, a reviewer must claim one of the following..."

**New framing (Appendix B.1):**
> "This appendix addresses potential concerns about the scope and applicability of our results. For each identified concern, we provide formal analysis demonstrating why it does not affect our conclusions."

Then present the same 13 positions as:
> "Concern 1: The model may be incomplete..."
> "Analysis: Theorem 3.32 establishes..."

Same content. Reader is "someone with concerns" not "reviewer trying to reject."

---

## PHASE 3: Main Text Modifications

### 3.1 Introduction Rewrite

**Remove:**
- Any framing of contribution as "correcting" the field
- Implication that prior researchers were negligent
- "finally" or "at last" language

**Keep:**
- Clear statement of contribution
- Scope definition
- Paper organization

**Add:**
- Acknowledgment of prior work's foundations (Malayeri, Aldrich, etc.)
- Framing as "completing" rather than "correcting"

### 3.2 Abstract Check

Verify abstract contains:
- [ ] No combative language
- [ ] Clear contribution statement
- [ ] Scope limitations acknowledged
- [ ] No direct claims about field failure

### 3.3 Related Work Section

**Keep entirely:**
- The 0/5 table (factual)
- Technical comparisons
- Prior art analysis

**Remove or soften:**
- Any editorializing about why prior work didn't do this
- Implications of negligence

**Reframe:**
> "Prior work established qualitative foundations. We provide the first machine-verified formal treatment."

Not:
> "Prior work failed to formalize despite obvious need."

### 3.4 Conclusion Rewrite

**Current (assumed):** Strong claims about debate being closed

**New framing:**
- Summarize theorems proven
- Note Lean verification
- Suggest future work (tooling, LLM evaluation, pedagogy)
- Acknowledge limitations appropriately
- Let reader draw "debate is closed" conclusion themselves

### 3.5 Cross-References to Appendix

For each moved theorem/section, leave a clean reference:

> "We establish that no extension to shape-based typing can recover the capabilities proven absent (see Appendix B.6 for the complete impossibility proof)."

This:
1. Signals the proof exists
2. Doesn't clutter main text
3. Provides citation target for rebuttal

---

## PHASE 4: Specific Edits Checklist

### 4.1 Global Search-and-Replace

| Find | Replace With |
|------|--------------|
| "the field failed" | [delete or reframe contextually] |
| "obvious" (when editorializing) | [delete] |
| "should have been" | [delete] |
| "no one asked" | [delete] |
| "challenge to reviewers" | [delete header, move content] |
| "the debate is over" | "summary of results" |
| "incoherent" (check each) | Keep if technical definition, soften if rhetorical |
| "wrong" (check each) | Keep if technical ("mathematically incorrect"), soften if polemic |

### 4.2 Per-Section Audit

For each section, verify:

- [ ] **Section 1 (Introduction):** No combative framing
- [ ] **Section 2 (Foundations):** Technical only
- [ ] **Section 2.4.2:** Move epistemic commentary to Appendix C.1
- [ ] **Section 3 (Core Theorems):** Keep theorem statements, move preemptive proofs
- [ ] **Section 3.6:** Move entirely to Appendix B.1
- [ ] **Section 4 (Complexity):** Technical only (should be clean)
- [ ] **Section 5 (Case Studies):** Empirical, should be clean
- [ ] **Section 6 (Methodology):** Should be clean
- [ ] **Section 7 (Related Work):** Remove editorializing, keep facts
- [ ] **Section 8 (Extensions):** Check TypeScript section for tone
- [ ] **Section 9 (Conclusions):** Rewrite per 3.4 above

### 4.3 Theorem Statement Audit

For each major theorem, verify statement is:
- Neutral in phrasing
- Technically precise
- Not framed as "refutation" but as "establishment"

Example:
> ✗ "Theorem 3.13 refutes any possibility of..."
> ✓ "Theorem 3.13 establishes the impossibility of..."

---

## PHASE 5: New Content to Add

### 5.1 Acknowledgments Section

Add:
- Prior work that laid foundations (Malayeri, Aldrich, etc.)
- Any feedback received
- Sumner (if co-author)
- Lean community / mathlib if applicable

### 5.2 Limitations Section (brief, in main text)

> "Our analysis applies to languages with class-based inheritance (B ≠ ∅). Languages without inheritance constructs fall outside scope. Additionally, our complexity bounds assume standard computational models."

This preempts "you didn't consider X" while being honest about scope.

### 5.3 Future Work Section

- Tooling (linters implementing the decision procedure)
- LLM code generation evaluation (Section 9.2 expansion)
- Pedagogical implications
- Extension to other paradigms

---

## PHASE 6: Quality Assurance

### 6.1 Full Read-Through Checklist

After all edits, read main text with these questions:

1. [ ] Could a reviewer quote any sentence as "combative"?
2. [ ] Is every strong claim backed by theorem reference?
3. [ ] Does the paper read as "contribution" not "correction"?
4. [ ] Are appendix references clear and useful?
5. [ ] Would a neutral reader feel respected?

### 6.2 Adversarial Read-Through

Have someone (or LLM) read specifically looking for:
- Sentences that could be quoted in a negative review
- Tone issues
- Implicit insults to prior researchers
- Anything that makes reader defensive

### 6.3 Technical Verification

After restructure:
- [ ] All theorem numbers still correct
- [ ] All cross-references valid
- [ ] Appendix references resolve
- [ ] Lean code references still accurate
- [ ] Page count tracked (target: similar length, better distribution)

---

## PHASE 7: Final Structure

### Main Paper (~50-55 pages)
1. Introduction (contribution-focused)
2. Foundations (technical definitions)
3. Core Results (theorems with proof sketches, full proofs in appendix where appropriate)
4. Complexity Analysis
5. Case Studies (summaries, full code in Appendix D)
6. Methodology
7. Related Work (factual comparison)
8. Extensions
9. Conclusions and Future Work

### Appendix (~25-30 pages)
A. Lean Proof Artifacts
B. Completeness and Robustness Analysis
C. Historical Context
D. Extended Case Studies

---

## PHASE 8: Pre-Submission Checklist

- [ ] Main text tone audit complete
- [ ] All combative content in appendix
- [ ] Appendix properly structured
- [ ] Cross-references verified
- [ ] Abstract neutral
- [ ] Conclusion neutral
- [ ] Related work factual only
- [ ] Co-author (Sumner) reviewed and approved
- [ ] Email to Myers drafted
- [ ] arXiv submission prepared
- [ ] TOPLAS formatting requirements met

---

## Appendix B.1 Template

For reference, here's how to reframe the "Attack Surface Closure" content:

```markdown
## Appendix B: Completeness and Robustness Analysis

This appendix provides detailed analysis addressing potential concerns 
about the scope, applicability, and completeness of our results.

### B.1 Comprehensive Concern Analysis

We identify thirteen categories of potential concerns and demonstrate 
why each does not affect our conclusions.

#### Concern 1: Model Completeness
*Potential concern:* The (N, B, S) model may fail to capture relevant 
aspects of type systems.

*Analysis:* Theorem 3.32 establishes model completeness by demonstrating 
that any type system feature expressible in a Turing-complete language 
maps to operations on (N, B, S). The proof proceeds by...

[Continue for all 13 concerns]
```

---

## Notes

- This restructure changes ZERO technical content
- Every theorem, proof, and claim remains
- Only presentation changes
- Appendix exists for rebuttal: "See Appendix B.3" answers any objection
- Goal: make rejection require engaging substance, not dismissing tone
