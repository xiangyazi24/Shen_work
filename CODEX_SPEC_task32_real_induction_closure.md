# Task 32: Discharge FirstCrossingPointwiseUniformClosureResidual

## Goal

Create `ShenWork/PDE/P3MoserRealInductionClosure.lean` that proves
`FirstCrossingPointwiseUniformClosureResidual` for `intervalDomain`.

## Background

```lean
def FirstCrossingPointwiseUniformClosureResidual
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ {T : ℝ} {u v : ℝ → D.Point → ℝ},
    IsPaper2ClassicalSolution D p T u v →
      ShortTimeBoundedBeforeResidual D p →
        (∀ {τ : ℝ},
          0 ≤ τ →
            τ < T →
              BoundedBeforeOnSubinterval D u τ T →
                ∃ δ, 0 < δ ∧ τ + δ ≤ T ∧
                  BoundedBeforeOnSubinterval D u (τ + δ) T) →
          ∃ M, ∀ t, 0 < t → t < T → ∀ x, |u t x| ≤ M
```

Given:
- A classical solution on [0,T]
- Short-time bounded: ∃ τ₀ > 0 with BoundedBeforeOnSubinterval on [0,τ₀)
- Right extension: if bounded-before on [0,τ) and τ < T, then bounded-before on [0,τ+δ)

Prove: ∃ M (UNIFORM), ∀ t ∈ (0,T), ∀ x, |u t x| ≤ M

## Proof strategy: real induction

This is a STANDARD first-crossing / continuation / real-induction argument.

### Step 1: Define the "good set"

```
S = { τ ∈ [0, T] | BoundedBeforeOnSubinterval D u τ T }
```

Note: `BoundedBeforeOnSubinterval D u τ T` means `τ ≤ T ∧ ∀ t, 0 < t → t < τ → ∃ M_t, ∀ x, |u t x| ≤ M_t`

### Step 2: S is nonempty

By `ShortTimeBoundedBeforeResidual`, there exists τ₀ > 0 with bounded-before on [0,τ₀).

### Step 3: S has a supremum

S ⊆ [0, T] is nonempty and bounded above by T, so τ* = sSup S exists.

### Step 4: τ* = T

**Proof by contradiction.** Suppose τ* < T.

Need to show BoundedBeforeOnSubinterval at τ*.

For any τ' < τ* with τ' ∈ S (such τ' exists since τ* = sSup S), we have
bounded-before on [0, τ'). Taking τ' close to τ*, we get bounded-before on
[0, τ*-ε) for any ε > 0.

Actually, the argument is:
- For any t ∈ (0, τ*), there exists τ' ∈ S with τ' > t (since τ* = sSup).
  By bounded-before at τ', t has a bound.
- So bounded-before on (0, τ*) holds: BoundedBeforeOnSubinterval D u τ* T
  (since τ* ≤ T by construction)

Now apply the right-extension hypothesis at τ*:
- We have bounded-before on [0, τ*) and τ* < T (by assumption)
- Extension gives δ > 0 with bounded-before on [0, τ*+δ)
- But τ*+δ > τ* = sSup S, contradiction

So τ* = T. We have BoundedBeforeOnSubinterval D u T T, which gives:
∀ t, 0 < t → t < T → ∃ M_t, ∀ x, |u t x| ≤ M_t

### Step 5: Uniformize the bound (THE HARD PART)

The per-t bounds M_t need to become a single M. Two approaches:

**Approach A (concrete for intervalDomain):** Use T29's
`intervalDomain_slice_bounded_of_classical`, which shows each time slice has a bound
from spatial compactness. The bound at time t is `sSup (range |u t|)`. The function
t ↦ sSup (range |u t|) is... well, we need it to be bounded on (0,T). This requires
showing the supNorm is continuous in time and hence bounded on compact subsets.

If this is too hard, use:

**Approach B (leave as residual):** Introduce a residual for the uniformization step.
The real-induction gives bounded-before with per-t bounds (τ* = T). The uniformization
step needs an additional argument. Package it cleanly.

**Approach C (avoid the problem):** Instead of BoundedBeforeOnSubinterval (per-t bounds),
track a STRONGER induction hypothesis: "∃ M, ∀ t ∈ (0,τ), ∀ x, |u t x| ≤ M" (uniform
from the start). But then the extension step needs to preserve the uniform bound, which
is harder to state.

**RECOMMENDED APPROACH (A modified):** For `intervalDomain`, each time slice is bounded
by `intervalDomain_slice_bounded_of_classical` (T29). The function t ↦ bound(t) exists.
To get a uniform bound on (ε, T-ε) for any ε > 0, use the time continuity of the
classical solution: u is jointly continuous in (t,x) on (0,T) × [0,1], hence bounded
on the compact subset [ε, T-ε] × [0,1]. Then take ε → 0... but [0,T] × [0,1] is not
compact in the parabolic sense (0 is not in (0,T)).

ACTUALLY, the cleanest approach: use the CLASSICAL SOLUTION'S continuity on the whole
CLOSED domain. The `intervalDomainClassicalRegularity` provides joint space-time
continuity on (0,T) × [0,1]. A continuous function on (0,T) × [0,1] restricted to
any compact [ε, T-ε] × [0,1] is bounded. To bound on ALL of (0,T) × [0,1], use the
fact that we already proved bounded-before on [0,T) (from the real induction), which
gives per-t bounds. Then:

Pick any t₀ ∈ (0, T/2). The bound at t₀ is M_{t₀}. The extension argument already
covers times ABOVE t₀. For times BELOW t₀, the short-time boundedness gives bounds.
The number of "steps" is finite (each step extends by δ ≥ (T-τ)/2, so at most O(log(T/τ₀))
steps), and each step has its own bound. Take M = max of all step bounds.

This can work! The proof outline:
1. Short-time: ∃ τ₁ > 0 with bound M₁ on (0, τ₁)
2. Extension at τ₁: bound on (0, τ₁ + (T-τ₁)/2), bound M₂
3. Extension at τ₂ = τ₁ + (T-τ₁)/2: bound on (0, τ₂ + (T-τ₂)/2), bound M₃
4. After O(log) steps, reach T

But in Lean, this inductive construction is complex. The cleanest Lean approach is
probably Zorn's lemma or `Real.sSup` properties.

## Lean implementation hints

- Use `Real.sSup` for the supremum
- Key Mathlib lemmas: `Real.lt_sSup_iff`, `Real.sSup_le`, `not_isLUB_of_lt` or similar
- The set `S = {τ | BoundedBeforeOnSubinterval ... τ T}` is nonempty and bounded above
- Proof by contradiction: if sSup S < T, construct a larger element
- For uniformization: if you can't close it, define a named residual

## Files to read first

1. `ShenWork/PDE/P3MoserRealInduction.lean` — the residual definition
2. `ShenWork/PDE/P3MoserFirstCrossingContinuation.lean` — BoundedBeforeOnSubinterval + helper lemmas
3. `ShenWork/PDE/P3MoserShortTimeBounded.lean` — T29 (slice boundedness)
4. `ShenWork/PDE/P3MoserContinuityExtension.lean` — T30 (extension)

## Constraints

- NO sorry, NO axiom, NO native_decide
- All `#print axioms` must show ONLY `[propext, Classical.choice, Quot.sound]`
- If the uniformization step is too hard, introduce a named residual. But the real
  induction (τ* = T with per-t bounds) MUST be proved.

## Verification

```bash
lake env lean ShenWork/PDE/P3MoserRealInductionClosure.lean
```
