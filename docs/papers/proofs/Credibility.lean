/-
  Credibility.lean
  
  Main module for Paper 5: A Credibility Theory for AI-Mediated Signaling
  
  This module imports all submodules and provides a summary of results.
-/

import Credibility.Basic
import Credibility.CheapTalk
import Credibility.CostlySignals
import Credibility.Impossibility
import Credibility.CoherentStopping

/-!
# Paper 5: Credibility Theory

## Summary of Results

### Section 3: Cheap Talk
- `cheap_talk_bound`: Cheap talk credibility is bounded by prior/(prior + (1-prior)·q)
- `magnitude_penalty`: Higher magnitude claims receive less credibility
- `emphasis_penalty`: Excessive signaling decreases credibility past threshold
- `meta_assertion_trap`: Meta-assertions provide negligible boost
- `composedCredibility`: Sequential Bayesian update for signal composition

### Section 4: Costly Signals
- `costly_signal_effectiveness`: Costly signals achieve arbitrarily high credibility
- `proof_as_ultimate_signal`: Machine-checked proofs achieve maximal credibility

### Section 5: Impossibility
- `text_credibility_bound`: No text achieves full credibility for high-magnitude claims
- `memory_iteration_futility`: Rephrasing memory cannot escape cheap talk bound
- `optimal_strategy_dominance`: Optimal strategy dominates alternatives

### Section 6: Coherent Stopping
- `goalDetermined`: When all propagation paths lead to goal
- `coherentToStop`: Stopping is coherent iff state is goal-determined
- `coherentToStop_absorbing`: Once coherent, always coherent along propagation

### Section 7: Leverage (see Paper 3)
Leverage results (brevity principle, etc.) are instances of Paper 3's Leverage
Maximization Metatheorem. See: DOI 10.5281/zenodo.XXXXXXX

## Verification Status

Run `lake build` to verify all proofs compile.
Run `grep -r "sorry" Credibility/*.lean` to check for incomplete proofs.

## Module Dependency Graph

```
Basic.lean ───────────────────┐
    ↓                         │
CheapTalk.lean                │
    ↓                         │
CostlySignals.lean            │
    ↓                         │
Impossibility.lean    CoherentStopping.lean
```
-/

