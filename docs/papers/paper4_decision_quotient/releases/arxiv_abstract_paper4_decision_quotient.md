# arXiv abstract (Paper 4: Decision Quotient)

Copy/paste **only** the abstract text (do **not** include this header). If you view this file in a rendered Markdown preview, the TeX math may render; use the **source view** (or copy from the code block) to get raw text.

## Single-paragraph (recommended)

```text
We present a Lean 4 framework for polynomial-time reductions and complexity-theory proofs, and use it to formalize the complexity of identifying decision-relevant information: given a decision problem, which coordinates suffice to compute an optimal action? We define SUFFICIENCY-CHECK with explicit input encodings and prove (in Lean) coNP-completeness, $(1-\varepsilon)\ln n$ inapproximability (via reduction from SET-COVER), $2^{\Omega(n)}$ lower bounds under ETH for succinct encodings, and W[2]-hardness for a natural parameterization, yielding a dichotomy between explicit and succinct models. The development provides bundled Karp reductions with polynomial-time witnesses, composition lemmas/tactics, and reusable templates for NP/coNP and $\Sigma_2^P$ membership and hardness. The formalization comprises about 5,600 lines of Lean across 36 files, with 230+ theorems and explicit polynomial bounds.
```

## TOC-style (preserves newlines in arXiv email announcements)

Note: arXiv preserves carriage returns only when the following line begins with whitespace. The indents below are intentional.

```text
We present a Lean 4 framework for polynomial-time reductions and complexity-theory proofs, and use it to formalize the complexity of identifying decision-relevant information.
  Problem: given a decision problem, which coordinates suffice to compute an optimal action? (SUFFICIENCY-CHECK; explicit encodings).
  Verified complexity results (Lean): coNP-complete; $(1-\varepsilon)\ln n$ inapproximable (from SET-COVER); $2^{\Omega(n)}$ lower bounds under ETH for succinct encodings; W[2]-hard for a natural parameterization; and a dichotomy between explicit and succinct models.
  Formalization contributions: bundled Karp reductions with polynomial-time witnesses; composition lemmas/tactics; and templates for NP/coNP and $\Sigma_2^P$ membership and hardness.
  Scale: about 5,600 lines of Lean across 36 files, with 230+ theorems and explicit polynomial bounds.
```
