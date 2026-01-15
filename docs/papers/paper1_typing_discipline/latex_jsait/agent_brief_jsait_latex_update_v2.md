# Agent Brief: JSAIT Special Issue Submission — LaTeX Update Plan (No-Hedge, Info-Theory-First)

**Purpose:** This document is a self-contained brief for an editing agent to revise Tristan’s LaTeX manuscript to better fit the IEEE JSAIT Special Issue **“Data Compression: Classical Theories Meet Modern Advances”** (deadline listed as **Mar 31, 2026**; guest editors include Chao Tian, Jun Chen, Deniz Gunduz, Pulkit Tandon, Lele Wang).  
Primary alignment topics: **task/semantics-aware compression**, **compression-inspired prediction/learning/inference**, and **information-theoretic framing**.

This is a *strategic rewrite*, not a change to the mathematics. The Lean proofs are treated as ground truth for the formal claims; the goal is to present them in language and structure that reads as **information theory**, not “programming languages manifesto.”

---

## 0) Critical constraints

### 0.1 Non-negotiable semantics
- All theorem statements must preserve the existing Lean semantics exactly.
- No “escape-hatch” phrasing. Avoid: “in our framework,” “under assumptions,” “given the premises,” “we restrict attention to,” “in this universe.”
- Replace any conditional hedges with **category names** (e.g., “interface-only observer” as a defined object).

### 0.2 Allowable changes
- Rewording, section ordering, naming/notation, and framing.
- Moving language-specific material (Python/Java/TS/Rust instantiations) into **Corollaries / Examples / Appendix**.
- Replacing overloaded terms (“Kolmogorov complexity,” “rate”) with technically correct equivalents while preserving claims.

---

## 1) What the submission must *feel like* to JSAIT

### 1.1 Top-level story (what reviewers should read)
**Type identity / typing disciplines are semantic compression schemes**: a representation of behavior classes that permits certain queries with bounded evidence (“witness”) cost.  
Core contributions are:
1) A precise, invariance-based **impossibility** theorem: interface-only evidence cannot recover non-invariant properties (e.g., provenance/nominal identity).  
2) A positive result: nominal tagging yields **constant-size witness** for type identity in the witness-cost model.  
3) A structural theorem (matroid / axes): the space of semantic queries decomposes cleanly (as formalized in Lean).

### 1.2 Target impression
- “This is a semantics-aware compression / inference paper with machine-checked theorems.”
- Not “this is a Python paper.” Python is an **instantiation** of the general theorem.

---

## 2) Immediate “language fixes” to eliminate perceived hedging

### 2.1 Impossibility theorem template (use this style)
Replace any “given…” phrasing with:

> **Theorem (Impossibility from interface-only evidence).**  
> No procedure—deterministic or randomized, regardless of time or memory—can compute **P** using **only** interface-membership observations with correctness requirement **C**.

or the quotient form:

> **Definition (Shape-equivalence).**  x ~ y iff all interface membership observations return identical answers on x and y.  
> **Theorem (Quotient barrier).** Every interface-only procedure is constant on ~-equivalence classes. Therefore no interface-only procedure can compute any property that varies within a ~-class.

**Do not** use “in our model.” The restriction is baked into the noun phrase: *interface-only*.

### 2.2 “Premises are definitions” style
Use:
- “is defined as”
- “an interface-only observer is any procedure that…”
- “shape-equivalence is defined by…”

Avoid:
- “assume”
- “suppose”
- “under the assumptions”
- “given the premises”

---

## 3) Info-theory framing corrections (semantic preservation required)

### 3.1 Replace “Kolmogorov complexity” with “witness description length”
If the draft uses “Kolmogorov complexity K(·)” to mean “minimum AST size,” replace with:

- **Witness description length**: W(·) = minimum witness program/AST length under a fixed encoding.

Then optionally include a *Remark* connecting W to algorithmic information theory **only as interpretation** (no theorem dependency).

**Reason:** IT reviewers will attack “Kolmogorov-optimal” unless the encoding + reference machine are pinned. W is already the intended object.

### 3.2 Fix “rate” language
If the draft defines rate as log|T| without a source distribution, adjust phrasing to be correct without weakening:
- Call it “tag alphabet size” or “identifier entropy upper bound” unless you define a distribution and expected code length.
- If keeping “rate–distortion,” either:
  - (Preferred) switch to **Information Bottleneck** style (rate as I(X;T) / expected code length; distortion as task loss), or
  - define a **3-axis tradeoff**: (tag length L, witness length W, error D). Call this “rate–distortion–witness” and avoid pretending it is Shannon RD unless fully defined.

---

## 4) Structural edit plan (LaTeX)

### 4.1 High-impact reordering (recommended)
1) **Abstract**: Info-theory-first; one sentence on Lean artifacts at the end.
2) **Introduction**:
   - Define “interface-only observer” and “nominal-tag access” early.
   - State headline impossibility result in the no-hedge template.
3) **Formal model**:
   - Definitions: observations, equivalence, witness cost.
4) **Main theorems**:
   - Impossibility (quotient barrier)
   - Constant-witness nominal result
   - Matroid/axes structure theorem (if central; otherwise move later)
5) **Instantiations**:
   - Python/Java/TS/Rust as corollaries/examples.
6) **Related work**:
   - Add at least 3 anchors from compression/information theory (semantic compression, IB, MDL or AIT if used).
7) **Artifact / Reproducibility**:
   - Lean proof status, build steps, hashes/Zenodo version.

### 4.2 Abstract rewrite checklist
- First line: “We formalize type identity as semantic compression/inference under observational constraints.”
- Mention “impossibility” explicitly.
- Mention “constant witness” explicitly.
- Mention Lean at end only: “All results are machine-checked in Lean.”

### 4.3 Python placement rules
- Python statements must appear as **Corollary / Example**:
  - “CPython instantiates nominal-tag access” (constant-time header tag read).
- Avoid “Python is optimal” in theorems/titles.
- Cite authoritative sources (Python docs + CPython object layout) in bibliography.

---

## 5) Citations to add (agent to insert as BibTeX + in-text)
**Special issue page:** “Data Compression: Classical Theories Meet Modern Advances” (IT Society JSAIT CFP page).  
**Information Bottleneck:** Tishby et al. / standard IB references.  
**MDL/AIT (optional):** Grünwald (MDL) / Li & Vitányi (Kolmogorov) if interpreting W.  
**Python / CPython (for instantiation):**
- Python docs: `type()` semantics, data model.
- CPython object layout / `ob_type` / `Py_TYPE()` macro docs.
(Agent should use the official Python docs + official CPython docs/repos, not blogs.)

---

## 6) “No-hedge” banned phrases list (search & replace)
Search manuscript for these and replace:
- “in our model/framework/universe”
- “under assumptions”
- “given the premises”
- “we restrict to”
- “we consider only”
- “likely / plausibly / suggests”
Replace with:
- defined class names (“interface-only observer,” “shape-respecting procedure,” “nominal-tag oracle”)
- absolute theorems (“No procedure … can … using only …”)

---

## 7) Practical file availability / sources
The editing agent should work from the **Zenodo version** (authoritative) or a freshly provided LaTeX bundle. Some earlier chat-uploaded `.tex` files may be unavailable/expired in the chat indexing layer.

**Lean files provided in this chat (for reference):**
- `abstract_class_system.lean`
- `axis_framework.lean`
- `context_formalization.lean`
- `discipline_migration.lean`
- `nominal_resolution.lean`
- `python_instantiation.lean`
- `java_instantiation.lean`
- `typescript_instantiation.lean`
- `rust_instantiation.lean`

---

## 8) Deliverable: what the agent should output
1) Updated LaTeX source with:
   - Rewritten Abstract + Intro + main theorem statements in “no-hedge” style.
   - Corrected info-theory terminology (W instead of K; corrected “rate” language).
   - Python/other languages moved to corollary/example sections with citations.
2) Updated `.bib` with the new references.
3) A short “changes summary” (bullet list) enumerating exactly what was changed and where.

---

## 9) Submission risk audit (what to watch for)
- Any remaining “rate–distortion” language that is not formally defined invites reviewer attack.
- Any “dominance” language that reads like a universal claim *without* explicit observer definition invites desk reject.
- Any numeric/empirical claims without a method should be removed or converted into a reproducible experiment.

---

## 10) One-sentence cover-letter positioning
> “This manuscript contributes machine-checked impossibility and optimality results for semantics-aware compression/inference under observational constraints, with concrete instantiations in widely used runtimes (e.g., CPython), aligning with the special issue’s focus on modern compression theory and semantics-aware methods.”
---

## 11) Drop-in LaTeX blocks (IT-first, no-hedge) — pasteable text

**Goal:** Make page 1 read like an information theory paper: observation-limited inference / semantic representation / information barriers.  
**Rule:** No “in our framework,” no “given assumptions,” no “we restrict attention to.” The restriction is baked into defined category names (e.g., *interface-only procedure*).

### 11.1 Abstract (replace current abstract)
```tex
\begin{abstract}
We study semantic representation under observational constraints: a procedure is allowed to query only interface-membership evidence of a value, and must decide semantic properties such as type identity or provenance. We formalize the indistinguishability relation induced by interface-only evidence and prove an information barrier: every interface-only procedure is constant on indistinguishability classes, hence cannot compute any property that varies within such a class. In contrast, nominal tagging provides constant-size evidence: type identity admits a constant-length witness under our witness-description-length measure. All stated results are machine-checked in Lean4.
\end{abstract}
```

### 11.2 Flagship impossibility theorem (quotient barrier form)
```tex
\begin{definition}[Interface-only observations]
An interface-only procedure is any procedure whose interaction with a value is limited to interface membership queries.
\end{definition}

\begin{definition}[Indistinguishability]
For values $x,y$, write $x \sim y$ iff every interface membership query returns the same answer on $x$ and on $y$.
\end{definition}

\begin{theorem}[Impossibility from interface-only evidence]
Every interface-only procedure is constant on $\sim$-equivalence classes.
Consequently, no interface-only procedure can compute any property that differs for some $x \sim y$.
\end{theorem}
```

### 11.3 Positive result (nominal tags give constant witness)
```tex
\begin{definition}[Witness description length]
Let $W(P)$ denote the minimum description length (e.g., AST size under a fixed encoding) of a witness program for property $P$.
\end{definition}

\begin{theorem}[Constant witness for nominal type identity]
Nominal-tag access admits a constant-length witness for type identity: $W(\text{type-identity}) = O(1)$.
\end{theorem}
```

### 11.4 Python placement (corollary/instantiation, not headline)
```tex
\begin{corollary}[CPython instantiation]
CPython realizes nominal-tag access (the runtime stores the type tag per object and exposes it via \texttt{type()}), hence the constant-witness construction applies concretely.
\end{corollary}
```

**Agent note:** Place Python/Java/TS/Rust instantiations in a dedicated “Instantiations” section or an appendix. Avoid making language names appear in theorem titles or the abstract’s first two sentences.

---

## 12) “Audience compilation” rules (PL → IT translation without changing math)

### 12.1 Replace PL-first nouns with IT-first nouns
- Replace “type system” (in the opening) with “semantic representation under observational constraints.”
- Replace “duck typing/structural typing debate” with “interface-only evidence” and “indistinguishability classes.”
- Replace “optimal type identity check” with “constant-size evidence (witness description length).”

### 12.2 Force an information-barrier reading
Use one of these on page 1 (agent chooses the best match to existing theorems):
- “Even with unbounded computation, interface-only procedures cannot compute provenance/nominal identity.”
- “The barrier is informational (indistinguishability), not computational.”

### 12.3 Term hygiene (do this globally)
- Prefer **witness description length** W over “Kolmogorov complexity” K unless K is fully formalized with an encoding + reference machine.
- Avoid calling anything “rate–distortion” unless the rate is an expected codelength / mutual information under a distribution. Otherwise, present a **(L, W, D)** tradeoff (tag length, witness length, error/distortion).

---

## 13) Acceptance-risk minimization (agent checklist)

Before finalizing the LaTeX update, confirm:
- Abstract’s first sentence is IT-first (semantic representation / observational constraints).
- Main impossibility theorem is stated as “No procedure … using only … can …” or quotient barrier form (no “given assumptions” language).
- “Rate” and “Kolmogorov complexity” are not used in nonstandard ways.
- Python is a corollary/example with authoritative citations, not the paper’s thesis statement.

