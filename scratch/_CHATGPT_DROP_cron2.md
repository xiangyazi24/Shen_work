# Q833 (cron2) — endpoint values for the `secondDeriv` bound in sub-sorry 1A

Static repo inspection only; I did not run a local Lean build.

## Short answer

Yes, the strategy is correct, with one Lean-level nuance.

For the power-source `IntervalWeakH2Neumann` route, the `secondDeriv` field is indeed the concrete classical expression

```lean
deriv (deriv g)
```

when the structure is built by

```lean
intervalWeakH2Neumann_of_contDiffOn
```

because that constructor sets:

```lean
secondDeriv := deriv (deriv g)
```

and `intervalWeakH2Neumann_of_eigenvalue_summable` finishes by calling that constructor for

```lean
g := fun x : ℝ => ν * intervalDomainLift w x ^ γ
```

So for `hH2_per_slice` built along this route, the endpoint goal is really about `deriv (deriv g) 0` and `deriv (deriv g) 1`.

The nuance is: `deriv (deriv g) 0 = 0` is not merely a one-line consequence of `deriv` being zero when non-differentiable.  There are two cases.  If `deriv g` is not differentiable at the endpoint, `deriv_zero_of_not_differentiableAt` gives zero.  If it is differentiable, you still need the one-sided constant-zero argument to force the derivative to be zero.  The repo already has exactly this argument packaged for interval lifts.

## Endpoint lemmas already in the repo

On branch `chatgpt-scratch`, the file

```text
ShenWork/PDE/IntervalLiftEndpointDeriv.lean
```

proves for any subtype profile:

```lean
theorem lift_deriv2_eq_zero_at_zero (f : intervalDomainPoint → ℝ) :
    deriv (deriv (intervalDomainLift f)) 0 = 0

theorem lift_deriv2_eq_zero_at_one (f : intervalDomainPoint → ℝ) :
    deriv (deriv (intervalDomainLift f)) 1 = 0
```

and the exact bound-shaped corollaries:

```lean
theorem lift_deriv2_abs_le_at_zero
    (f : intervalDomainPoint → ℝ) {B : ℝ} (hB : 0 ≤ B) :
    |deriv (deriv (intervalDomainLift f)) 0| ≤ B

theorem lift_deriv2_abs_le_at_one
    (f : intervalDomainPoint → ℝ) {B : ℝ} (hB : 0 ≤ B) :
    |deriv (deriv (intervalDomainLift f)) 1| ≤ B
```

So boundary values are indeed automatically bounded by any nonnegative constant once the source is rewritten as an `intervalDomainLift`.

## How to apply this to `ν · u^γ`

For

```lean
g := fun x : ℝ => ν * intervalDomainLift w x ^ γ
```

do not try to prove the endpoint second derivative bound from scratch.  Rewrite `g` as a zero-extension:

```lean
let f : intervalDomainPoint → ℝ := fun y => ν * w y ^ γ
have hg_lift : g = intervalDomainLift f := by
  funext x
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · simp [g, f, intervalDomainLift, hx]
  · simp [g, f, intervalDomainLift, hx, Real.zero_rpow hγ.ne']
```

Then the endpoint cases are:

```lean
-- x = 0
simpa [g, hg_lift] using
  ShenWork.IntervalLiftEndpointDeriv.lift_deriv2_abs_le_at_zero f hC_nonneg

-- x = 1
simpa [g, hg_lift] using
  ShenWork.IntervalLiftEndpointDeriv.lift_deriv2_abs_le_at_one f hC_nonneg
```

You may need to orient the rewrite manually, e.g.

```lean
rw [hg_lift]
exact ShenWork.IntervalLiftEndpointDeriv.lift_deriv2_abs_le_at_zero f hC_nonneg
```

inside an endpoint branch.

## Splitting `x ∈ Icc 0 1`

The robust proof shape is:

```lean
rcases lt_or_eq_of_le hx.1 with hx0 | rfl
· rcases lt_or_eq_of_le hx.2 with hx1 | rfl
  · -- interior: x ∈ Ioo 0 1
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx0, hx1⟩
    -- use eventual equality with the smooth cosine representative
    -- then compactness / joint continuity gives `≤ C`
  · -- x = 1
    -- rewrite source as intervalDomainLift f; use lift_deriv2_abs_le_at_one
· -- x = 0
  -- rewrite source as intervalDomainLift f; use lift_deriv2_abs_le_at_zero
```

This matches your proposed decomposition:

```text
Icc 0 1 = Ioo 0 1 ∪ {0,1}
```

Interior points are controlled by joint continuity/compactness of the smooth representative; endpoint points are controlled by the zero-extension endpoint lemmas.

## Important caveat: check which H² constructor produced `secondDeriv`

For the power source built by `intervalWeakH2Neumann_of_eigenvalue_summable`, the above applies directly: its `secondDeriv` is `deriv (deriv g)` for the zero-extended `g`.

For `chemDivSource_weakH2_of_cosineRep`, the repo deliberately builds the H² certificate with the smooth representative’s second derivative instead:

```lean
set F := deriv (chemFluxFun p.β U_cos V_cos)
have hF_H2 : IntervalWeakH2Neumann F := ...
exact {
  secondDeriv := hF_H2.secondDeriv
  ...
}
```

In that case the boundary issue is different: the `secondDeriv` is not the zero-extension’s `deriv (deriv ...)`; it is the representative derivative selected for the weak H² certificate.  Your Q833 statement sounds like the power-source `ν · u^γ` case in sub-sorry 1A, so the zero-extension endpoint lemmas are the right tool.

## Verdict

Your mathematical split is correct.  The Lean-safe statement is:

* On `Ioo 0 1`, transfer to the smooth cosine representative and use joint continuity plus compactness.
* At `0` and `1`, first rewrite `ν * intervalDomainLift w x ^ γ` as `intervalDomainLift (fun y => ν * w y ^ γ) x`, then use `lift_deriv2_abs_le_at_zero` / `lift_deriv2_abs_le_at_one`.

Do not rely on “`deriv` is zero when non-differentiable” alone as the proof explanation for the second derivative.  The repo endpoint lemmas already handle both differentiable and non-differentiable cases for `deriv (deriv (intervalDomainLift f))`.
