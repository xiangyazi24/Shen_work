# Codex Spec: Close the one sorry in weightedGradDiss_eq_two_mul_H1energy

## Repository
`~/repos/shen_work` (Lean 4, Mathlib v4.29.1+, on uisai2)

## File
`ShenWork/Paper2/IntervalDomainH1GradientBound.lean`

## The sorry to close

```lean
theorem weightedGradDiss_eq_two_mul_H1energy
    {params : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    intervalDomainLpWeightedGradientDissipation 2 u t = 2 * H1energy u t
```

## Definitions (exact)

```lean
-- ShenWork/PDE/IntervalDomain.lean:2750
def intervalDomainLift (f : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun x => if hx : x ∈ Set.Icc (0 : ℝ) 1 then f ⟨x, hx⟩ else 0

-- ShenWork/PDE/IntervalDomain.lean:2753
def intervalDomainIntegral (f : intervalDomainPoint → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, intervalDomainLift f x

-- ShenWork/PDE/IntervalDomain.lean:2915
def intervalDomainGradNorm (f : intervalDomainPoint → ℝ)
    (x : intervalDomainPoint) : ℝ :=
  |deriv (intervalDomainLift f) x.1|

-- ShenWork/Paper2/IntervalDomainEnergyStep.lean:218
def intervalDomainLpWeightedGradientDissipation
    (pExp : ℝ) (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  intervalDomain.integral
    (fun x => (u t x) ^ (pExp - 2) * (intervalDomain.gradNorm (u t) x) ^ 2)

-- ShenWork/Paper2/IntervalChiNegH1Energy.lean:95
def H1energy (u : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ x in (0:ℝ)..1, (deriv (intervalDomainLift (u τ)) x) ^ 2

-- intervalDomain.integral = intervalDomainIntegral (line 2992)
-- intervalDomain.gradNorm = intervalDomainGradNorm (line 2993)
```

## The math (why the equality holds for pExp = 2)

LHS = `intervalDomainIntegral (fun p => (u t p)^(2-2) * (gradNorm (u t) p)^2)`
    = `∫₀¹ lift(fun p => (u t p)^0 * |deriv(lift(u t)) p.1|^2) x`
    = `∫₀¹ (1 * (deriv(lift(u t)) x)^2)` (for x ∈ Icc 0 1)
    = `∫₀¹ (deriv(lift(u t)) x)^2`

RHS = `2 * ((1/2) * ∫₀¹ (deriv(lift(u t)) x)^2)`
    = `∫₀¹ (deriv(lift(u t)) x)^2`

## Key steps for the proof:

1. `(2:ℝ) - 2 = 0` by norm_num
2. `Real.rpow x 0 = 1` by rpow_zero (the `^` in `(u t p)^(pExp-2)` is `Real.rpow`)
3. `1 * y = y` by one_mul
4. `|y|^2 = y^2` by sq_abs
5. `intervalDomainGradNorm f p = |deriv (intervalDomainLift f) p.1|` by definition
6. `intervalDomainIntegral f = ∫₀¹ (intervalDomainLift f) x` by definition
7. On `[0,1]`, `intervalDomainLift f x = f ⟨x, hx⟩` by `dif_pos hx`

CRITICAL: Do NOT unfold `intervalDomainLift` inside `deriv` on the RHS. The RHS has
`deriv (intervalDomainLift (u t)) x` — unfolding `intervalDomainLift` here would give
`deriv (fun y => if y ∈ Icc 0 1 then ... else 0) x`, which is wrong. Use `conv_lhs`
or targeted `rw` to only unfold on the LHS.

## Proof strategy

```lean
suffices h : intervalDomainLpWeightedGradientDissipation 2 u t =
    ∫ x in (0:ℝ)..1, (deriv (intervalDomainLift (u t)) x) ^ 2 by
  simp only [H1energy]; linarith
-- Now prove the suffices:
-- unfold LHS to ∫₀¹ lift(...) x, then show integrand equals (deriv(lift(u t)) x)^2
```

## Build and verify
```bash
export PATH=$HOME/.elan/bin:$PATH
cd ~/repos/shen_work
lake build ShenWork.Paper2.IntervalDomainH1GradientBound 2>&1 | tail -5
grep -n "sorryAx" <(lake build ShenWork.Paper2.IntervalDomainH1GradientBound 2>&1)
```

## Constraints
- No sorry, no axiom, no native_decide
- Only edit `weightedGradDiss_eq_two_mul_H1energy` proof (replace the tactic block)
- Do NOT change any theorem statement or add new theorems
