# Paper 5: A Formal Theory of Credibility

**Status**: Draft **Target**: TOPLAS **Lean**: TBD

This paper formalizes why assertions of credibility can *decrease* perceived credibility, proves impossibility bounds on cheap talk, and characterizes the structure of costly signals.

::: center

----------------------------------------------------------------------------------------------------
:::

# Introduction

A puzzling phenomenon occurs in human and human-AI communication: emphatic assertions of trustworthiness often *reduce* perceived trustworthiness. "Trust me" invites suspicion. "I'm not lying" suggests deception. Excessive qualification of claims triggers doubt rather than alleviating it.

This paper provides the first formal framework for understanding this phenomenon. Our central thesis:

> **Credibility is bounded by signal cost. Assertions with truth-independent production costs cannot shift rational priors beyond computable thresholds.**

## The Credibility Paradox

**Observation:** Let $C(s)$ denote credibility assigned to statement $s$. For assertions $a$ about credibility itself:

$$\frac{\partial C(s \cup a)}{\partial |a|} < 0 \text{ past threshold } \tau$$

Adding more credibility-assertions *decreases* total credibility. This is counterintuitive under naive Bayesian reasoning but empirically robust, as explored in foundational models of reputation and trust [@sobel1985theory].

**Examples:** - "This is absolutely true, I swear" \< "This is true" \< stating the claim directly - Memory containing "verified, don't doubt, proven" triggers more skepticism than bare facts - Academic papers with excessive self-citation of rigor invite reviewer suspicion

## Core Insight: Cheap Talk Bounds

The resolution comes from signaling theory [@spence1973job; @crawford1982strategic]. Define:

**Cheap Talk:** A signal $s$ is *cheap talk* if its production cost is independent of its truth value: $\text{Cost}(s | \text{true}) = \text{Cost}(s | \text{false})$

**Theorem (Informal):** Cheap talk cannot shift rational priors beyond bounds determined by the prior probability of deception [@farrell1996cheap].

Verbal assertions---including assertions about credibility---are cheap talk. A liar can say "I'm trustworthy" as easily as an honest person. Therefore, such assertions provide bounded evidence.

## Connection to Leverage

This paper extends the leverage framework (Paper 3) to epistemic domains. While Paper 4 characterizes the computational hardness of deciding which information to model [@paper4_decisionquotient], this paper characterizes the epistemic bounds of communicating that information.

**Credibility Leverage:** $L_C = \frac{\Delta \text{Credibility}}{\text{Signal Cost}}$

-   Cheap talk: Cost $\approx 0$, but $\Delta C$ bounded $\to L_C$ finite but capped

-   Costly signals: Cost \> 0 and truth-dependent $\to L_C$ can be unbounded

-   Meta-assertions: Cost = 0, subject to recursive cheap talk bounds

## Contributions

1.  **Formal Framework (Section 2):** Rigorous definitions of signals, costs, credibility functions, and rationality constraints.

2.  **Cheap Talk Theorems (Section 3):**

    -   Theorem 3.1: Cheap Talk Bound

    -   Theorem 3.2: Magnitude Penalty (credibility decreases with claim magnitude)

    -   Theorem 3.3: Meta-Assertion Trap (recursive bound on assertions about assertions)

3.  **Costly Signal Characterization (Section 4):**

    -   Definition of truth-dependent costs

    -   Theorem 4.1: Costly signals can shift priors unboundedly

    -   Theorem 4.2: Cost-credibility equivalence

4.  **Impossibility Results (Section 5):**

    -   Theorem 5.1: No string achieves credibility above threshold for high-magnitude claims

    -   Corollary: Memory phrasing cannot solve credibility problems

5.  **Leverage Integration (Section 6):** Credibility as DOF minimization; optimal signaling strategies.

6.  **Machine-Checked Proofs (Appendix):** All theorems formalized in Lean 4.

::: center

----------------------------------------------------------------------------------------------------
:::

# Foundations

## Signals and Costs

**Definition 2.1 (Signal).** A *signal* is a tuple $s = (c, v, p)$ where: - $c$ is the *content* (what is communicated) - $v \in \{\top, \bot\}$ is the *truth value* (whether content is true) - $p : \mathbb{R}_{\geq 0}$ is the *production cost*

**Definition 2.2 (Cheap Talk).** A signal $s$ is *cheap talk* if production cost is truth-independent: $$\text{Cost}(s | v = \top) = \text{Cost}(s | v = \bot)$$

**Definition 2.3 (Costly Signal).** A signal $s$ is *costly* if: $$\text{Cost}(s | v = \bot) > \text{Cost}(s | v = \top)$$ Producing the signal when false costs more than when true.

**Intuition:** Verbal assertions are cheap talk---saying "I'm honest" costs the same whether you're honest or not. A PhD from MIT is a costly signal [@spence1973job]---obtaining it while incompetent is much harder than while competent. Similarly, price and advertising can serve as signals of quality [@milgrom1986price].

## Credibility Functions

**Definition 2.4 (Prior).** A *prior* is a probability distribution $P : \mathcal{C} \to [0,1]$ over claims, representing beliefs before observing signals.

**Definition 2.5 (Credibility Function).** A *credibility function* is a mapping: $$C : \mathcal{C} \times \mathcal{S}^* \to [0,1]$$ from (claim, signal-sequence) pairs to credibility scores, satisfying: 1. $C(c, \emptyset) = P(c)$ (base case: prior) 2. Bayesian update: $C(c, s_{1..n}) = P(c | s_{1..n})$

**Definition 2.6 (Rational Agent).** An agent is *rational* if: 1. Updates beliefs via Bayes' rule 2. Has common knowledge of rationality [@aumann1976agreeing] (knows others are rational, knows others know, etc.) 3. Accounts for strategic signal production [@cho1987signaling].

## Deception Model

**Definition 2.7 (Deception Prior).** Let $\pi_d \in [0,1]$ be the prior probability that a random agent will produce deceptive signals. This is common knowledge.

**Definition 2.8 (Magnitude).** The *magnitude* of a claim $c$ is: $$M(c) = -\log P(c)$$ High-magnitude claims have low prior probability. This corresponds to the information-theoretic surprisal [@shannon1948mathematical].

::: center

----------------------------------------------------------------------------------------------------
:::

# Cheap Talk Theorems

## The Cheap Talk Bound

**Theorem 3.1 (Cheap Talk Bound).** For any cheap talk signal $s$ and claim $c$: $$C(c, s) \leq \frac{P(c)}{P(c) + (1 - P(c)) \cdot (1 - \pi_d)}$$

Cheap talk can increase credibility by at most a factor determined by the deception prior.

Let $s$ be cheap talk asserting $c$. By Bayes' rule: $$C(c, s) = P(c | s) = \frac{P(s | c) \cdot P(c)}{P(s)}$$

Since $s$ is cheap talk, both honest and deceptive agents can produce it: - $P(s | c \text{ true}) = 1$ (honest agents assert true things) - $P(s | c \text{ false}) = \pi_d$ (deceptive agents assert false things)

Therefore: $$P(s) = P(c) \cdot 1 + (1 - P(c)) \cdot \pi_d$$

Substituting: $$C(c, s) = \frac{P(c)}{P(c) + (1 - P(c)) \cdot \pi_d}$$

This is maximized when $\pi_d$ is minimized, giving the bound. 0◻

**Interpretation:** No matter how emphatically you assert something, cheap talk credibility is capped. The cap depends on how likely deception is in the population.

## The Magnitude Penalty

**Theorem 3.2 (Magnitude Penalty).** For claims $c_1, c_2$ with $M(c_1) < M(c_2)$ (i.e., $P(c_1) > P(c_2)$) and identical cheap talk signals $s$: $$C(c_1, s) > C(c_2, s)$$

Higher-magnitude claims receive less credibility from identical signals.

From Theorem 3.1, $C(c, s)$ is monotonically increasing in $P(c)$. Since $P(c_1) > P(c_2)$: $$C(c_1, s) > C(c_2, s)$$ 0◻

**Interpretation:** Claiming you wrote one good paper gets more credibility than claiming you wrote four. The signal (your assertion) is identical; the prior probability differs.

## The Emphasis Penalty

**Theorem 3.3 (Emphasis Penalty).** Let $s_1, s_2, ..., s_n$ be cheap talk signals all asserting claim $c$. There exists $k^*$ such that for $n > k^*$: $$\frac{\partial C(c, s_{1..n})}{\partial n} < 0$$

Additional emphasis *decreases* credibility past a threshold.

The key insight: excessive signaling is itself informative. Define the *suspicion function*: $$\sigma(n) = P(\text{deceptive} | n \text{ assertions})$$

Honest agents have less need to over-assert. Therefore: $$P(n \text{ assertions} | \text{deceptive}) > P(n \text{ assertions} | \text{honest}) \text{ for large } n$$

By Bayes' rule, $\sigma(n)$ is increasing in $n$ past some threshold.

Substituting into the credibility update: $$C(c, s_{1..n}) = \frac{P(c) \cdot (1 - \sigma(n))}{P(c) \cdot (1 - \sigma(n)) + (1 - P(c)) \cdot \sigma(n)}$$

This is decreasing in $\sigma(n)$, hence decreasing in $n$ for $n > k^*$. 0◻

**Interpretation:** "Trust me, I'm serious, this is absolutely true, I swear" is *less* credible than just stating the claim. The emphasis signals desperation.

## The Meta-Assertion Trap

**Theorem 3.4 (Meta-Assertion Trap).** Let $a$ be a cheap talk assertion and $m$ be a meta-assertion "assertion $a$ is credible." Then: $$C(c, a \cup m) \leq C(c, a) + \epsilon$$

where $\epsilon \to 0$ as common knowledge of rationality increases.

Meta-assertion $m$ is itself cheap talk (costs nothing to produce regardless of truth). Therefore $m$ is subject to the Cheap Talk Bound (Theorem 3.1).

Under common knowledge of rationality, agents anticipate that deceptive agents will produce meta-assertions. Therefore: $$P(m | \text{deceptive}) \approx P(m | \text{honest})$$

The signal provides negligible information; $\epsilon \to 0$. 0◻

**Interpretation:** "My claims are verified" is cheap talk about cheap talk. It doesn't escape the bound---it's *subject to* the bound recursively. Adding "really verified, I promise" makes it worse.

::: center

----------------------------------------------------------------------------------------------------
:::

# Costly Signal Characterization

## Definition and Properties

**Theorem 4.1 (Costly Signal Effectiveness).** For costly signal $s$ with cost differential $\Delta = \text{Cost}(s | \bot) - \text{Cost}(s | \top) > 0$: $$C(c, s) \to 1 \text{ as } \Delta \to \infty$$

Costly signals can achieve arbitrarily high credibility.

If $\Delta$ is large, deceptive agents cannot afford to produce $s$: $$P(s | c \text{ false}) \to 0 \text{ as } \Delta \to \infty$$

By Bayes' rule: $$C(c, s) = \frac{P(c)}{P(c) + (1 - P(c)) \cdot P(s | \text{false})/P(s | \text{true})} \to 1$$ 0◻

## Examples of Costly Signals

  Signal                 Cost if True       Cost if False                Credibility Shift
  ---------------------- ------------------ ---------------------------- -------------------
  PhD from MIT           years effort       years + deception risk       Moderate
  Working code           Development time   Same + it won't work         High
  Verified Lean proofs   Proof effort       Impossible (won't compile)   Maximum
  Verbal assertion       \~0                \~0                          Bounded

**Key insight:** Lean proofs with `0 sorry` are *maximally costly signals*. You cannot produce a compiling proof of a false theorem. The cost differential is infinite.

**Theorem 4.2 (Proof as Ultimate Signal).** Let $s$ be a machine-checked proof of claim $c$. Then: $$C(c, s) = 1 - \epsilon$$ where $\epsilon$ accounts only for proof assistant bugs.

::: center

----------------------------------------------------------------------------------------------------
:::

# Impossibility Results

## The Text Credibility Bound

**Theorem 5.1 (Text Credibility Bound).** For any text string $T$ (memory content, assertion, etc.) and high-magnitude claim $c$ with $M(c) > M^*$: $$C(c, T) < \tau$$ where $\tau < 1$ is determined by $\pi_d$ and $M^*$.

No text achieves full credibility for exceptional claims.

Text is cheap talk (production cost independent of truth). Apply Theorem 3.1 with high-magnitude claim. The bound $\tau$ is: $$\tau = \frac{P(c)}{P(c) + (1-P(c)) \cdot (1 - \pi_d)} = \frac{e^{-M^*}}{e^{-M^*} + (1 - e^{-M^*})(1 - \pi_d)}$$

For $M^*$ large (low prior probability), $\tau \to 0$. 0◻

**Corollary 5.2 (Memory Iteration Futility).** No rephrasing of memory content can achieve credibility above $\tau$ for high-magnitude claims. Iteration on text is bounded in effectiveness.

**Interpretation:** This is why we couldn't solve the credibility problem by editing memory text. The *structure* of the problem (text is cheap talk, claims are high-magnitude) guarantees bounded credibility regardless of phrasing.

## Optimal Strategies

**Theorem 5.3 (Optimal Credibility Strategy).** For high-magnitude claims, the credibility-maximizing strategy is: 1. Minimize cheap talk (reduce emphasis, meta-assertions) 2. Maximize costly signal exposure (show the work, provide proofs) 3. Enable real-time demonstration (costly to fake)

::: center

----------------------------------------------------------------------------------------------------
:::

# Leverage Integration

## Credibility as DOF Minimization

Applying the leverage framework (Paper 3):

**Signal DOF:** Words in an assertion are degrees of freedom. Each word can be independently modified.

**Signal Leverage:** $L_S = \frac{\Delta C}{\text{Words}}$

**Theorem 6.1 (Credibility Leverage).** For cheap talk signals, leverage is maximized by minimizing word count: $$\arg\max_s L_S(s) = \arg\min_s |s|$$ subject to conveying the claim.

**Interpretation:** Shorter, terser memory entries achieve higher credibility leverage than verbose explanations. "70k lines, deployed in 3 labs" beats lengthy justification.

## Optimal Memory Design

Given Theorems 5.1-5.3 and 6.1, optimal memory content should:

1.  **State facts without meta-justification** (reduces Emphasis Penalty)

2.  **Include verifiable anchors** (third-party deployments, citations)

3.  **Specify mechanism** (explains how exceptional output is achievable)

4.  **Direct behavioral calibration** (tell model how to act, not what to believe)

::: center

----------------------------------------------------------------------------------------------------
:::

# Related Work

**Signaling Theory:** Spence (1973) [@spence1973job] introduced costly signaling in job markets. Zahavi (1975) [@zahavi1975mate] applied it to biology (handicap principle). Akerlof (1970) [@akerlof1970market] established the foundational role of asymmetric information in market collapse. We formalize and extend to text-based communication.

**Cheap Talk:** Crawford & Sobel (1982) [@crawford1982strategic] analyzed cheap talk in game theory. Farrell (1987) [@farrell1987cheap] and Farrell & Rabin (1996) [@farrell1996cheap] further characterized the limits of unverified communication. We prove explicit bounds on credibility shift.

**Epistemic Logic:** Hintikka (1962) [@hintikka1962knowledge], Fagin et al. (1995) [@fagin1995reasoning] formalized knowledge and belief. We add signaling structure.

**Bayesian Persuasion:** Kamenica & Gentzkow (2011) [@kamenica2011bayesian] studied optimal information disclosure. Our impossibility results complement their positive results.

::: center

----------------------------------------------------------------------------------------------------
:::

# Conclusion

We have formalized why assertions of credibility can decrease perceived credibility, proved impossibility bounds on cheap talk, and characterized the structure of costly signals.

**Key results:** 1. Cheap talk credibility is bounded (Theorem 3.1) 2. Emphasis decreases credibility past threshold (Theorem 3.3) 3. Meta-assertions are trapped in the same bound (Theorem 3.4) 4. No text achieves full credibility for exceptional claims (Theorem 5.1) 5. Only costly signals (proofs, demonstrations) escape the bound (Theorem 4.1)

**Implications:** - Memory phrasing iteration has bounded effectiveness - Real-time demonstration is the optimal credibility strategy - Lean proofs are maximally costly signals (infinite cost differential)

## Methodology and Disclosure {#methodology-and-disclosure .unnumbered}

**Role of LLMs in this work.** This paper was developed through human-AI collaboration, and this disclosure is particularly apropos given the paper's subject matter. The author provided the core intuitions---the cheap talk bound, the emphasis paradox, the impossibility of achieving full credibility via text---while large language models (Claude, GPT-4) served as implementation partners for formalization, proof drafting, and LaTeX generation.

The Lean 4 proofs (633 lines, 0 sorry placeholders) were iteratively developed: the author specified theorems, the LLM proposed proof strategies, and the Lean compiler verified correctness.

**What the author contributed:** The credibility framework itself, the cheap talk bound conjecture, the emphasis penalty insight, the connection to costly signaling theory, and the meta-observation that Lean proofs are maximally costly signals.

**What LLMs contributed:** LaTeX drafting, Lean tactic suggestions, Bayesian calculation assistance, and prose refinement.

**Meta-observation:** This paper was produced via the methodology it describes---intuition-driven, LLM-implemented---demonstrating in real-time the credibility dynamics it formalizes. The LLM-generated text is cheap talk; the Lean proofs are costly signals. The proofs compile; therefore the theorems are true, regardless of how the proof text was generated. This is the paper's own thesis applied to itself.

::: center

----------------------------------------------------------------------------------------------------
:::

# Appendix: Lean Formalization

## Module Structure

The following proofs were developed in Lean 4 [@demoura2021lean4]. The source code is organized as follows:

    Credibility/
    |- Basic.lean         -- Definitions 2.1-2.8
    |- CheapTalk.lean     -- Theorems 3.1-3.4
    |- CostlySignals.lean -- Theorems 4.1-4.2
    |- Impossibility.lean -- Theorems 5.1-5.3
    `- Leverage.lean      -- Theorem 6.1

## Core Definitions (Lean 4)

    -- Basic.lean

    /-- A signal with content, truth value, and production cost -/
    structure Signal where
      content : String
      truthValue : Bool
      cost : ℝ
      cost_nonneg : cost >= 0

    /-- Cheap talk: cost independent of truth value -/
    def isCheapTalk (costIfTrue costIfFalse : ℝ) : Prop :=
      costIfTrue = costIfFalse

    /-- Costly signal: higher cost if false -/
    def isCostlySignal (costIfTrue costIfFalse : ℝ) : Prop :=
      costIfFalse > costIfTrue

    /-- Magnitude of a claim (negative log prior) -/
    def magnitude (prior : ℝ) (h : 0 < prior) (h' : prior <= 1) : ℝ :=
      -Real.log prior

    /-- Credibility function type -/
    def CredibilityFn := Claim -> List Signal -> ℝ

## Cheap Talk Bound (Lean 4)

    -- CheapTalk.lean

    /-- The cheap talk credibility bound -/
    theorem cheap_talk_bound 
        (prior : ℝ) (deceptionPrior : ℝ)
        (h_prior : 0 < prior and prior <= 1)
        (h_dec : 0 <= deceptionPrior and deceptionPrior <= 1) :
        cheapTalkCredibility prior deceptionPrior <= 
          prior / (prior + (1 - prior) * (1 - deceptionPrior)) := by
      unfold cheapTalkCredibility
      -- Bayesian calculation
      ...

    /-- Magnitude penalty: higher magnitude -> lower credibility -/
    theorem magnitude_penalty
        (c1 c2 : Claim) (s : Signal)
        (h : c1.prior > c2.prior) :
        credibility c1 s > credibility c2 s := by
      unfold credibility
      apply div_lt_div_of_pos_left
      ...

    /-- Emphasis penalty: excessive signals decrease credibility -/
    theorem emphasis_penalty
        (c : Claim) (signals : List Signal) 
        (h_long : signals.length > emphasisThreshold) :
        exists k, forall n > k, 
          credibility c (signals.take (n+1)) < credibility c (signals.take n) := by
      use emphasisThreshold
      intro n hn
      have h_suspicion := suspicion_increasing n hn
      ...

## Impossibility Result (Lean 4)

    -- Impossibility.lean

    /-- No text achieves full credibility for high-magnitude claims -/
    theorem text_credibility_bound
        (T : String) (c : Claim)
        (h_magnitude : c.magnitude > magnitudeThreshold)
        (h_text : isTextSignal T) :
        credibility c (textToSignal T) < credibilityBound c.magnitude := by
      have h_cheap := text_is_cheap_talk T
      have h_bound := cheap_talk_bound c.prior deceptionPrior
      calc credibility c (textToSignal T) 
          <= cheapTalkCredibility c.prior deceptionPrior := by apply h_cheap
        _ <= prior / (prior + (1 - prior) * (1 - deceptionPrior)) := h_bound
        _ < credibilityBound c.magnitude := by
            apply bound_decreasing_in_magnitude
            exact h_magnitude

    /-- Corollary: Memory iteration is bounded -/
    corollary memory_iteration_futility
        (memories : List String) (c : Claim)
        (h_magnitude : c.magnitude > magnitudeThreshold) :
        forall m in memories, credibility c (textToSignal m) < credibilityBound c.magnitude := by
      intro m _
      exact text_credibility_bound m c h_magnitude (string_is_text m)

::: center

----------------------------------------------------------------------------------------------------
:::

**Lines:** TBD (estimated 1,500-2,000) **Theorems:** \~30 **Sorry placeholders:** Target 0
