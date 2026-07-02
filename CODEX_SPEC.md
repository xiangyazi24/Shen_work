# Codex Spec: Close 2 sorry in weightedGradDiss_le_of_Linf

## Target file
`~/repos/Shen_work/ShenWork/Paper2/IntervalDomainH1GradientBound.lean`

## Task
Fill the 2 `sorry` at lines 243-244 in `weightedGradDiss_le_of_Linf`. These are the LAST 2 sorry in the entire project.

## The theorem and proof state

```lean
theorem weightedGradDiss_le_of_Linf
    {params : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T)
    {Minf : ℝ} (hMinf : 0 ≤ Minf)
    (hLinf : ∀ x : intervalDomain.Point, u t x ≤ Minf)
    (pExp : ℝ) (hpExp2 : 2 ≤ pExp) :
    intervalDomainLpWeightedGradientDissipation pExp u t ≤
      Minf ^ (pExp - 2) * intervalDomainLpWeightedGradientDissipation 2 u t := by
  unfold intervalDomainLpWeightedGradientDissipation
  change intervalDomainIntegral _ ≤ Minf ^ (pExp - 2) * intervalDomainIntegral _
  unfold intervalDomainIntegral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
  · sorry   -- Goal 1
  · sorry   -- Goal 2
  · intro y hy   -- (pointwise bound — PROVED, don't touch)
    ...
```

**Goal 1**: `IntervalIntegrable (intervalDomainLift (fun x => (u t x) ^ (pExp - 2) * (intervalDomain.gradNorm (u t) x) ^ 2)) volume 0 1`

**Goal 2**: `IntervalIntegrable (fun y => Minf ^ (pExp - 2) * intervalDomainLift (fun x => (u t x) ^ ((2:ℝ) - 2) * (intervalDomain.gradNorm (u t) x) ^ 2) y) volume 0 1`

## Strategy: one helper lemma, parameterized by pExp

Add a private helper BEFORE `weightedGradDiss_le_of_Linf` (between the `gradNorm_eq` theorem at line 55 and the H¹ DI section comment at line 57). The helper proves integrability for ANY real exponent:

```lean
private theorem weightedGradDiss_intervalIntegrable
    {params : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    IntervalIntegrable
      (intervalDomainLift
        (fun x => (u t x) ^ (pExp - 2) *
          (intervalDomain.gradNorm (u t) x) ^ 2))
      volume 0 1
```

Then:
- **Goal 1**: `exact weightedGradDiss_intervalIntegrable hsol ht0 htT`
- **Goal 2**: `exact (weightedGradDiss_intervalIntegrable (pExp := (2:ℝ)) hsol ht0 htT).const_mul _`

## Proof plan for the helper

### Step 1: Get C² regularity
```lean
have hCu : ContDiffOn ℝ 2
    (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
  (hsol.regularity.2.2.2.2.1 t ⟨ht0, htT⟩).1.1
```

### Step 2: Get ContinuousOn of deriv via Neumann BCs
The key insight: `intervalDomainLift` is a zero-extension, so `deriv (lift u)` might be discontinuous at the boundary. BUT the Neumann BCs force `derivWithin (lift u) Icc 0 = 0` and `derivWithin (lift u) Icc 1 = 0`, matching the derivative from outside (also 0). So `deriv (lift u)` IS continuous on [0,1].

```lean
have hdw0 :
    derivWithin (intervalDomainLift (u t))
      (Set.Icc (0 : ℝ) 1) 0 = 0 :=
  intervalDomain_solution_derivWithin_u_left_zero
    hsol ht0 htT
have hdw1 :
    derivWithin (intervalDomainLift (u t))
      (Set.Icc (0 : ℝ) 1) 1 = 0 :=
  intervalDomain_solution_derivWithin_u_right_zero
    hsol ht0 htT
have hdu_cont :
    ContinuousOn (deriv (intervalDomainLift (u t)))
      (Set.Icc (0 : ℝ) 1) :=
  deriv_intervalDomainLift_continuousOn_Icc_of_regularity
    hCu hdw0 hdw1
```

These lemmas are in scope:
- `intervalDomain_solution_derivWithin_u_left_zero` (IntervalDomainLpEnergyFrontiers.lean:380)
- `intervalDomain_solution_derivWithin_u_right_zero` (IntervalDomainLpEnergyFrontiers.lean:401)
- `deriv_intervalDomainLift_continuousOn_Icc_of_regularity` (IntervalDomainL2CrossControl.lean:271)

All transitively imported via:
  IntervalDomainH1GradientBound
  → IntervalDomainLpBootstrapEnergyInequality
  → IntervalDomainLpEnergyFrontiers
  → IntervalDomainL2CrossControl

### Step 3: Build ContinuousOn of the product integrand
```lean
have hu_cont : ContinuousOn
    (intervalDomainLift (u t))
    (Set.Icc (0 : ℝ) 1) :=
  hCu.continuousOn
have hne : ∀ y ∈ Set.Icc (0 : ℝ) 1,
    intervalDomainLift (u t) y ≠ 0 :=
  fun y hy => ne_of_gt
    (intervalDomain_solution_lift_u_pos hsol ht0 htT hy)
have hpow_cont : ContinuousOn
    (fun y => (intervalDomainLift (u t) y) ^ (pExp - 2))
    (Set.Icc (0 : ℝ) 1) :=
  hu_cont.rpow_const
    (fun y hy => Or.inl (hne y hy))
have hgrad_sq_cont : ContinuousOn
    (fun y => (deriv (intervalDomainLift (u t)) y) ^ 2)
    (Set.Icc (0 : ℝ) 1) :=
  hdu_cont.pow 2
have hprod_cont : ContinuousOn
    (fun y => (intervalDomainLift (u t) y) ^ (pExp - 2) *
      (deriv (intervalDomainLift (u t)) y) ^ 2)
    (Set.Icc (0 : ℝ) 1) :=
  hpow_cont.mul hgrad_sq_cont
```

Note: `ContinuousOn.pow` is the standard Mathlib lemma for `(f x)^n` where `n : ℕ`. If `ContinuousOn.pow` doesn't exist, use `hdu_cont.mul hdu_cont` then congr with `sq`.

### Step 4: Transfer to the lift and get integrability
```lean
have hlift_cont : ContinuousOn
    (intervalDomainLift
      (fun x => (u t x) ^ (pExp - 2) *
        (intervalDomain.gradNorm (u t) x) ^ 2))
    (Set.uIcc (0 : ℝ) 1) := by
  rw [Set.uIcc_of_le zero_le_one]
  refine hprod_cont.congr ?_
  intro y hy
  simp only [intervalDomainLift, dif_pos hy]
  rw [gradNorm_eq, sq_abs]
exact hlift_cont.intervalIntegrable
```

The key congr step: on `Icc 0 1`,
- `intervalDomainLift (fun x => ...) y = (u t ⟨y,hy⟩)^(pExp-2) * (gradNorm (u t) ⟨y,hy⟩)^2` (by `dif_pos hy`)
- `(lift (u t) y)^(pExp-2) * (deriv (lift (u t)) y)^2` (the raw product)
- They're equal because `lift (u t) y = u t ⟨y,hy⟩` and `gradNorm f ⟨y,hy⟩ = |deriv (lift f) y|` and `|x|^2 = x^2`.

The congr direction in `ContinuousOn.congr`: if `hcont : ContinuousOn f s` and `heq : ∀ x ∈ s, g x = f x`, then `hcont.congr heq : ContinuousOn g s`. So we need `lift(...) y = product y` for `y ∈ Icc 0 1`.

Wait — the direction might be wrong. `ContinuousOn.congr` takes `h : ContinuousOn f s` and `heq : ∀ x ∈ s, g x = f x` and returns `ContinuousOn g s`. So we need:
- `hprod_cont : ContinuousOn (fun y => (lift u y)^c * (deriv (lift u) y)^2) Icc`
- The congr function should show `lift (weighted_fn) y = (lift u y)^c * (deriv (lift u) y)^2` for `y ∈ Icc`

So the `congr` argument should show: `intervalDomainLift (...) y = (lift u y)^c * (deriv (lift u) y)^2`:
```
simp only [intervalDomainLift, dif_pos hy]
-- LHS becomes: (u t ⟨y,hy⟩)^(pExp-2) * (gradNorm (u t) ⟨y,hy⟩)^2
-- RHS is: (intervalDomainLift (u t) y)^(pExp-2) * (deriv (lift (u t)) y)^2
-- intervalDomainLift (u t) y = u t ⟨y,hy⟩ (by dif_pos hy, but this is the OUTER lift — hmm)
```

Actually, there's a subtlety. The `intervalDomainLift` that wraps the whole expression IS what we're congruing. The `intervalDomainLift (u t)` in the product is a SEPARATE lift. After `simp only [intervalDomainLift, dif_pos hy]` on the LHS, it unfolds the OUTER lift but not the inner `lift (u t)`. 

Hmm, let me think about this differently. After `simp only [intervalDomainLift, dif_pos hy]`:
- LHS: `(u t ⟨y,hy⟩) ^ (pExp-2) * (gradNorm (u t) ⟨y,hy⟩) ^ 2`
- We need this to equal `(intervalDomainLift (u t) y)^(pExp-2) * (deriv (intervalDomainLift (u t)) y)^2`

Now `intervalDomainLift (u t) y = u t ⟨y,hy⟩` (by dif_pos hy on the inner lift). And `gradNorm (u t) ⟨y,hy⟩ = |deriv (intervalDomainLift (u t)) y|` (by rfl from gradNorm_eq). And `|x|^2 = x^2` (by sq_abs).

So the congr function needs to:
1. Unfold the outer `intervalDomainLift` (dif_pos hy) → get `(u t ⟨y,hy⟩) ^ c * (gradNorm (u t) ⟨y,hy⟩) ^ 2`
2. This should equal `(lift (u t) y) ^ c * (deriv (lift (u t)) y) ^ 2`
3. Use `intervalDomainLift_apply_of_mem (u t) y hy` to rewrite `lift (u t) y = u t ⟨y,hy⟩`
4. Use `gradNorm_eq` to rewrite `gradNorm (u t) ⟨y,hy⟩ = |deriv (lift (u t)) y|`
5. Use `sq_abs` to get `|x|^2 = x^2`

The direction: we need `congr_fun : ∀ y ∈ Icc, lift(whole) y = product y`:
```
lift(whole) y = (u t ⟨y,hy⟩)^c * (gradNorm ⟨y,hy⟩)^2   -- by dif_pos
             = (lift(u t) y)^c * (|deriv(lift(u t)) y|)^2  -- by intervalDomainLift_apply_of_mem + gradNorm_eq
             = (lift(u t) y)^c * (deriv(lift(u t)) y)^2    -- by sq_abs
```

So the congr shows `lift(whole) y = product y`, matching `ContinuousOn.congr`:
`hprod_cont.congr (fun y hy => ...)` where `... : lift(whole) y = product y`.

Wait, `ContinuousOn.congr` signature: `ContinuousOn f s → (∀ x ∈ s, g x = f x) → ContinuousOn g s`. So it needs `g x = f x`, meaning `lift(whole) y = product y`. Yes, that's what we need.

Actually, I just realized: it's simpler to NOT use `ContinuousOn.congr` but instead directly show `ContinuousOn (lift ...) (Icc 0 1)` by showing it's equal to a product of continuous functions on `Icc 0 1`.

Actually, the cleaner approach is to use `EqOn` and `ContinuousOn.congr`. Let me just write the spec clearly and let Codex figure out the exact tactic chain.

## Available lemma signatures (for reference)

From the file itself (line 47-55):
```lean
private theorem intervalDomainLift_apply_of_mem (f : intervalDomainPoint → ℝ)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalDomainLift f x = f ⟨x, hx⟩ := dif_pos hx

private theorem gradNorm_eq (f : intervalDomainPoint → ℝ)
    (p : intervalDomainPoint) :
    intervalDomain.gradNorm f p = |deriv (intervalDomainLift f) p.1| := rfl
```

From IntervalDomainLpEnergyFrontiers.lean:
```lean
-- line 19
theorem intervalDomain_solution_lift_u_pos
    ... (hy : y ∈ Set.Icc (0:ℝ) 1) :
    0 < intervalDomainLift (u t) y

-- line 380
theorem intervalDomain_solution_derivWithin_u_left_zero
    ... : derivWithin (intervalDomainLift (u t)) (Set.Icc (0:ℝ) 1) 0 = 0

-- line 401
theorem intervalDomain_solution_derivWithin_u_right_zero
    ... : derivWithin (intervalDomainLift (u t)) (Set.Icc (0:ℝ) 1) 1 = 0
```

From IntervalDomainL2CrossControl.lean:
```lean
-- line 271
theorem deriv_intervalDomainLift_continuousOn_Icc_of_regularity
    {f : intervalDomain.Point → ℝ}
    (hf : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0:ℝ) 1))
    (hdw0 : derivWithin (intervalDomainLift f) (Set.Icc (0:ℝ) 1) 0 = 0)
    (hdw1 : derivWithin (intervalDomainLift f) (Set.Icc (0:ℝ) 1) 1 = 0) :
    ContinuousOn (deriv (intervalDomainLift f)) (Set.Icc (0:ℝ) 1)
```

From IntervalDomainL2PDEIntegral.lean:
```lean
-- line 257
theorem intervalDomainLift_mul (f g : intervalDomain.Point → ℝ) (y : ℝ) :
    intervalDomainLift (fun x => f x * g x) y =
      intervalDomainLift f y * intervalDomainLift g y
```

## Namespacing

The file is inside `namespace ShenWork.Paper2.IntervalDomainH1GradientBound`. The lemmas from other files need full qualification or `open` statements. The existing code uses:
- `ShenWork.Paper2.intervalDomain_solution_derivWithin_u_left_zero`
- `ShenWork.Paper2.intervalDomain_solution_lift_u_pos`
- `deriv_intervalDomainLift_continuousOn_Icc_of_regularity` (in the same Paper2 namespace? check)
- `ShenWork.Paper2.IntervalDomainL2PDEIntegral.intervalDomainLift_mul` (or just `intervalDomainLift_mul` if opened)

Actually, looking at line 802 of IntervalDomainLpEnergyFrontiers.lean:
```lean
    rw [intervalDomainLift_mul]
```
It's used without namespace, so it's accessible. Same for line 62:
```lean
    exact ne_of_gt (intervalDomain_solution_lift_u_pos hsol ht0 htT hy)
```
No full namespace needed.

## Hard rules

- NO `sorry`, `admit`, `native_decide`, or custom `axiom`.
- Lines ≤ 100 chars.
- All edits in `ShenWork/Paper2/IntervalDomainH1GradientBound.lean` only.
- Do NOT change the theorem statement.
- Do NOT change any code in the pointwise bound branch (lines 245-262).
- The helper lemma goes between `gradNorm_eq` (line 55) and the H¹ DI section comment (line 57).
- No new imports needed (all lemmas are transitively imported).
- Build check: `cd ~/repos/Shen_work && lake env lean ShenWork/Paper2/IntervalDomainH1GradientBound.lean` (faster than full build)
- Full build if needed: `cd ~/repos/Shen_work && lake build ShenWork.Paper2.IntervalDomainH1GradientBound`
- Acceptance: 0 sorry in the file.

## Stall protocol
If stuck on a specific step, deliver what compiles + stall report with exact goal state and error.
