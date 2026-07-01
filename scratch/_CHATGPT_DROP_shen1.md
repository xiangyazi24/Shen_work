# Q2732 (shen1) — shortest route from endpoint-safe Agmon to `UnitIntervalPositiveAgmonInterpolation`

Repo: `xiangyazi24/Shen_work`  
Main commit audited: `216cbc4f0f79aebc217ea39ff038e325bfa108e2` (`Add endpoint-safe Agmon inequality`)  
Branch for this drop: `chatgpt-scratch`  
Scope: non-Zinan files only. I did **not** inspect, edit, rely on, or propose edits to:

- `ShenWork/PDE/P3MoserHighExcursionProducer.lean`
- `ShenWork/PDE/P3MoserThresholdPlanProducer.lean`

I inspected the requested files on the connected repo default branch:

- `ShenWork/PDE/GagliardoNirenberg.lean`
- `ShenWork/PDE/IntervalAgmonInterpolation.lean`
- `ShenWork/PDE/IntervalDomain.lean`
- `ShenWork/Paper2/IntervalDomainLemma41.lean`

I also checked adjacent non-forbidden helper files to identify existing bridge lemmas that should be reused:

- `ShenWork/PDE/IntervalEllipticCharacterization.lean`
- `ShenWork/Paper2/IntervalDomainStructuredMoserPower.lean`
- `ShenWork/PDE/IntervalDomainAPrioriGlobal.lean`
- `ShenWork/Paper2/IntervalDomainL2CrossControl.lean`

## Executive route

The new theorem

```lean
ShenWork.GagliardoNirenberg.agmon_inequality_interval_rightDeriv
```

is the correct endpoint-safe engine. It asks only for right derivatives on `Ioo 0 L`, not ordinary endpoint derivatives of the zero extension.

The shortest faithful Lean route is now:

1. For `h := intervalDomainLift f`, define
   ```lean
   g  y := h y ^ (q / 2)
   gp y := (q / 2) * h y ^ (q / 2 - 1) * deriv h y
   ```
2. Prove the input bundle for `agmon_inequality_interval_rightDeriv` using:
   - positivity of `h` on `Icc 0 1` from subtype positivity;
   - `ContDiffOn` to ordinary interior `HasDerivAt h (deriv h x) x`, then to `HasDerivWithinAt ... (Ioi x)`;
   - `Real.hasDerivAt_rpow_const` plus composition to get the right derivative of `g`;
   - integrability via continuous `derivWithin h (Icc 0 1)` representatives and a.e. equality with `deriv h` on the interior.
3. Apply `agmon_inequality_interval_rightDeriv (L := 1)` to get, for each `y ∈ Icc 0 1`,
   ```lean
   (intervalDomainLift f y) ^ q ≤ 2 * Y + q * Real.sqrt (Y * G)
   ```
   where
   ```lean
   Y := intervalDomain.integral (fun x => f x ^ q)
   G := intervalDomain.integral
     (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2)
   ```
4. Use a uniform Young step to get the pre-absorption inequality
   ```lean
   Y ≤ 2 * δ * Y + δ * q * Real.sqrt (Y * G) + Cδ * (intervalDomain.integral f) ^ q
   ```
   with `Cδ` depending only on `q, δ`, not on `f`.
5. Reuse the already-proved
   ```lean
   ShenWork.Paper2.IntervalDomainLemma41.interpolation_absorption
   ```
   and choose `δ` small enough that
   ```lean
   δ ^ 2 * q ^ 2 / (1 - 2 * δ) ^ 2 ≤ eps
   ```

The remaining work is not a new analytic frontier. It is a proof-producing bridge: endpoint-safe Agmon input, rpow/integral rewrites, uniform Young, final absorption.

## Existing theorem inventory to compose

### Endpoint-safe Agmon

In `ShenWork/PDE/GagliardoNirenberg.lean`:

```lean
theorem ShenWork.GagliardoNirenberg.agmon_inequality_interval_rightDeriv
    {L : ℝ} (hL : 0 < L)
    {f f' : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Icc 0 L))
    (hf_deriv : ∀ x ∈ Ioo (0 : ℝ) L, HasDerivWithinAt f (f' x) (Ioi x) x)
    (_hf'_int : IntervalIntegrable f' volume 0 L)
    (hf_sq_int : IntervalIntegrable (fun y => f y ^ 2) volume 0 L)
    (hf'_sq_int : IntervalIntegrable (fun y => f' y ^ 2) volume 0 L)
    (hff'_int : IntervalIntegrable (fun y => f y * f' y) volume 0 L)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    f x ^ 2 ≤ (2 / L) * (∫ y in (0 : ℝ)..L, f y ^ 2) +
      2 * sqrt (∫ y in (0 : ℝ)..L, f y ^ 2) *
        sqrt (∫ y in (0 : ℝ)..L, f' y ^ 2)
```

This theorem uses `intervalIntegral.integral_eq_sub_of_hasDeriv_right` internally. It is exactly the endpoint-safe replacement for the old theorem, whose closed ordinary `HasDerivAt` input did not fit zero-extensions.

### Current target and wiring

In `ShenWork/PDE/IntervalAgmonInterpolation.lean`:

```lean
def UnitIntervalPositiveAgmonInterpolation : Prop :=
  ∀ q : ℝ, 1 < q →
  ∀ eps : ℝ, 0 < eps →
    ∃ Ceps > 0,
      ∀ f : intervalDomain.Point → ℝ,
        (∀ x, 0 < f x) →
        ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) →
          intervalDomain.integral (fun x => f x ^ q) ≤
            eps * intervalDomain.integral
              (fun x => f x ^ (q - 2) *
                (intervalDomain.gradNorm f x) ^ 2) +
            Ceps * (intervalDomain.integral f) ^ q
```

Also already proved:

```lean
theorem intervalDomain_classicalSolutionPositiveInterpolation_of_uniform_agmon
    {params : CM2Params}
    (hagmon : UnitIntervalPositiveAgmonInterpolation) :
    IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation
      params
```

Do not change this wiring. It is already the correct quantifier-order bridge.

### Interval-domain definitions

In `ShenWork/PDE/IntervalDomain.lean`:

```lean
def intervalDomainPoint : Type := Subtype (Set.Icc (0 : ℝ) 1)

def intervalDomainLift (f : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun x => if hx : x ∈ Set.Icc (0 : ℝ) 1 then f ⟨x, hx⟩ else 0

def intervalDomainIntegral (f : intervalDomainPoint → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, intervalDomainLift f x

def intervalDomainGradNorm (f : intervalDomainPoint → ℝ)
    (x : intervalDomainPoint) : ℝ :=
  |deriv (intervalDomainLift f) x.1|

def intervalDomain : ShenWork.Paper2.BoundedDomainData where
  Point := intervalDomainPoint
  integral := intervalDomainIntegral
  gradNorm := intervalDomainGradNorm
  -- other fields elided
```

These definitions mean the final gradient integral is literally an interval integral of an `intervalDomainLift`, and `gradNorm` is the ordinary derivative of the zero extension. The proof must use a.e. agreement with `derivWithin` at the endpoints; do not try to prove endpoint ordinary differentiability.

### Algebraic absorption

In `ShenWork/Paper2/IntervalDomainLemma41.lean`:

```lean
theorem ShenWork.Paper2.IntervalDomainLemma41.interpolation_absorption
    {Y G Mp δ pv C : ℝ}
    (hY : 0 ≤ Y) (hG : 0 ≤ G) (hMp : 0 ≤ Mp)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1 / 4) (hp : 0 < pv)
    (hC : 0 ≤ C)
    (hineq : Y ≤ 2 * δ * Y + δ * pv * Real.sqrt (Y * G) + C * Mp) :
    Y ≤ δ ^ 2 * pv ^ 2 / (1 - 2 * δ) ^ 2 * G +
      2 * C / (1 - 2 * δ) * Mp
```

This is the final algebraic close. Reuse it.

### Existing bridge lemmas to reuse

In `ShenWork/PDE/IntervalEllipticCharacterization.lean`:

```lean
theorem ShenWork.IntervalEllipticCharacterization.hasDerivAt_of_contDiffOn_two_interior
    {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt g (deriv g x) x

theorem ShenWork.IntervalEllipticCharacterization.continuousOn_of_contDiffOn_two
    {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Icc (0 : ℝ) 1)) :
    ContinuousOn g (Set.uIcc (0 : ℝ) 1)

theorem ShenWork.IntervalEllipticCharacterization.continuousOn_derivWithin_of_contDiffOn_two
    {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (derivWithin g (Set.Icc (0 : ℝ) 1)) (Set.Icc (0 : ℝ) 1)

theorem ShenWork.IntervalEllipticCharacterization.deriv_eq_derivWithin_interior
    {g : ℝ → ℝ} {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    deriv g x = derivWithin g (Set.Icc (0 : ℝ) 1) x

theorem ShenWork.IntervalEllipticCharacterization.intervalIntegrable_deriv_of_contDiffOn_two
    {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Icc (0 : ℝ) 1)) :
    IntervalIntegrable (deriv g) volume 0 1
```

These are the exact helpers I would import and use. The proof style in `IntervalDomainL2CrossControl.lean` is especially relevant: it builds a continuous `derivWithin` representative, proves interval-integrability, then uses `congr_ae` and the null endpoint `{1}` to transfer back to ordinary `deriv`.

In `ShenWork/Paper2/IntervalDomainStructuredMoserPower.lean`, there is a directly reusable pattern for rpow continuity/integrability:

```lean
theorem ShenWork.Paper2.IntervalDomainStructuredMoserData.intervalDomain_classical_solution_powerIntegrable
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ∀ r : ℝ, 1 < r → ∀ t, 0 < t → t < T →
      IntervalIntegrable
        (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ r))
        volume 0 1
```

The theorem itself is solution-specific, but its proof pattern is exactly what is needed here: use `ContinuousOn.rpow_const`, a positive/nonzero base on `Icc`, then `.intervalIntegrable` after rewriting `Icc` to `uIcc`.

In `ShenWork/PDE/IntervalDomainAPrioriGlobal.lean`, useful existing candidates are:

```lean
theorem ShenWork.IntervalDomainExistence.integral_pow_le_sup_pow_mul
    {pExp : ℝ} (hpExp : 1 ≤ pExp)
    {f : intervalDomain.Point → ℝ}
    (hf_nonneg : ∀ x : intervalDomain.Point, 0 ≤ f x)
    (hf_bdd : BddAbove (Set.range fun x : intervalDomain.Point => |f x|))
    (hf_int : IntervalIntegrable (intervalDomainLift f) MeasureTheory.volume 0 1)
    (hfp_int :
      IntervalIntegrable
        (fun y : ℝ => intervalDomainLift (fun x : intervalDomain.Point => (f x) ^ pExp) y)
        MeasureTheory.volume 0 1) :
    intervalDomain.integral (fun x : intervalDomain.Point => (f x) ^ pExp) ≤
      (intervalDomainSupNorm f) ^ (pExp - 1) * intervalDomain.integral f
```

and

```lean
theorem ShenWork.IntervalDomainExistence.intervalDomain_Lp_interpolation_classicalSlice
    {pExp : ℝ} (hpExp : 1 ≤ pExp)
    {f : intervalDomain.Point → ℝ}
    (hf_nonneg : ∀ x : intervalDomain.Point, 0 ≤ f x)
    (hf_bdd : BddAbove (Set.range fun x : intervalDomain.Point => |f x|))
    (hf_int : IntervalIntegrable (intervalDomainLift f) MeasureTheory.volume 0 1)
    (hfp_int :
      IntervalIntegrable
        (fun y : ℝ => intervalDomainLift (fun x : intervalDomain.Point => (f x) ^ pExp) y)
        MeasureTheory.volume 0 1)
    (hf_cont : ContinuousOn (intervalDomainLift f) (Set.Icc (0 : ℝ) 1))
    {f' : ℝ → ℝ}
    (hf_deriv : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (intervalDomainLift f) (f' x) x)
    (hf'_int : IntervalIntegrable f' MeasureTheory.volume 0 1)
    (hf_sq_int : IntervalIntegrable (fun y : ℝ => (intervalDomainLift f y) ^ 2)
      MeasureTheory.volume 0 1)
    (hf'_sq_int : IntervalIntegrable (fun y : ℝ => f' y ^ 2) MeasureTheory.volume 0 1)
    (hff'_int : IntervalIntegrable (fun y : ℝ => intervalDomainLift f y * f' y)
      MeasureTheory.volume 0 1) :
    intervalDomain.integral (fun x : intervalDomain.Point => (f x) ^ pExp) ≤
        (intervalDomainSupNorm f) ^ (pExp - 1) * intervalDomain.integral f ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        (intervalDomainLift f x) ^ 2 ≤
          (2 / (1 : ℝ)) *
              (∫ y in (0 : ℝ)..1, (intervalDomainLift f y) ^ 2) +
            2 * Real.sqrt
                (∫ y in (0 : ℝ)..1, (intervalDomainLift f y) ^ 2) *
              Real.sqrt (∫ y in (0 : ℝ)..1, f' y ^ 2)
```

The first theorem may be useful for the Young step if the import graph allows. The second theorem still uses the old ordinary closed-interval derivative interface, so it should not be used directly for `UnitIntervalPositiveAgmonInterpolation` unless it is first refactored to use `agmon_inequality_interval_rightDeriv`.

## 1. Exact smaller lemmas needed to apply `agmon_inequality_interval_rightDeriv`

Let

```lean
h  : ℝ → ℝ := intervalDomainLift f
g  : ℝ → ℝ := fun y => h y ^ (q / 2)
gp : ℝ → ℝ := fun y => (q / 2) * h y ^ (q / 2 - 1) * deriv h y
```

To call

```lean
ShenWork.GagliardoNirenberg.agmon_inequality_interval_rightDeriv
  (L := 1) (f := g) (f' := gp)
```

these are the exact smaller obligations:

### 1. Positivity and nonzero base on `Icc`

```lean
∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift f y
```

Proof pattern:

```lean
intro y hy
let x : intervalDomain.Point := ⟨y, hy⟩
simpa [intervalDomainLift, hy, x] using hf_pos x
```

This is used by `ContinuousOn.rpow_const`, `Real.hasDerivAt_rpow_const`, `Real.rpow_add`, and `Real.rpow_pos_of_pos`.

### 2. `g` continuous on `Icc 0 1`

```lean
ContinuousOn (fun y => (intervalDomainLift f y) ^ (q / 2)) (Set.Icc (0 : ℝ) 1)
```

Proof pattern:

```lean
(hfC2.continuousOn.rpow_const
  (fun y hy => Or.inl (ne_of_gt (hpos_lift y hy))))
```

### 3. Right derivative of `g` on `Ioo 0 1`

```lean
∀ y ∈ Set.Ioo (0 : ℝ) 1,
  HasDerivWithinAt
    (fun z => (intervalDomainLift f z) ^ (q / 2))
    ((q / 2) * (intervalDomainLift f y) ^ (q / 2 - 1) *
      deriv (intervalDomainLift f) y)
    (Set.Ioi y) y
```

Use the existing interior derivative helper:

```lean
have hh_at : HasDerivAt h (deriv h y) y :=
  ShenWork.IntervalEllipticCharacterization.hasDerivAt_of_contDiffOn_two_interior
    hfC2 hy
have hh_right : HasDerivWithinAt h (deriv h y) (Set.Ioi y) y :=
  hh_at.hasDerivWithinAt
```

Then try first:

```lean
have hp : HasDerivAt (fun z : ℝ => z ^ (q / 2))
    ((q / 2) * (h y) ^ (q / 2 - 1)) (h y) :=
  Real.hasDerivAt_rpow_const
    (x := h y) (p := q / 2) (Or.inl (ne_of_gt hbase_pos))

-- Try this method name first:
have hg := hp.comp_hasDerivWithinAt y hh_right
```

If `comp_hasDerivWithinAt` elaborates in the opposite direction, use the dot-call from the outer derivative theorem (`hp`) and provide `y` explicitly. The result may have coefficient order

```lean
((q / 2) * h y ^ (q / 2 - 1)) * deriv h y
```

so finish with `ring_nf`/`ring` on multiplication associativity.

### 4. Interval-integrability of `gp`, `g^2`, `gp^2`, and `g*gp`

The faithful endpoint route is:

- prove continuity on `Icc` of the `derivWithin` representative
  ```lean
  fun y => (q / 2) * h y ^ (q / 2 - 1) *
    derivWithin h (Set.Icc (0 : ℝ) 1) y
  ```
  using
  ```lean
  ShenWork.IntervalEllipticCharacterization.continuousOn_derivWithin_of_contDiffOn_two hfC2
  ```
- get `IntervalIntegrable` by rewriting `Icc` to `uIcc` and calling `.intervalIntegrable`;
- transfer to the ordinary-`deriv` representative by `.congr_ae`, using
  ```lean
  ShenWork.IntervalEllipticCharacterization.deriv_eq_derivWithin_interior
  ```
  and the null endpoint `{1}` pattern already used in `IntervalDomainL2CrossControl.lean`.

This is the key endpoint convention: ordinary `deriv h` may be junk at endpoints, but it equals `derivWithin h (Icc 0 1)` a.e. on the interval. That is enough because every target is an interval integral.

## 2. API names to try first

### `ContDiffOn` to derivative data

Try the existing repo theorem first:

```lean
ShenWork.IntervalEllipticCharacterization.hasDerivAt_of_contDiffOn_two_interior
```

Then:

```lean
HasDerivAt.hasDerivWithinAt
```

If proving directly, the exact pattern already in the repo is:

```lean
have hIcc_nhds : Set.Icc (0 : ℝ) 1 ∈ 𝓝 x := by
  rw [mem_nhds_iff]
  exact ⟨Set.Ioo (0 : ℝ) 1, Set.Ioo_subset_Icc_self, isOpen_Ioo, hx⟩
have hcd : ContDiffAt ℝ 2 g x := by
  have := hg.contDiffWithinAt (Set.mem_Icc_of_Ioo hx)
  exact this.contDiffAt hIcc_nhds
have hdiff : DifferentiableAt ℝ g x := hcd.differentiableAt (by norm_num)
exact hdiff.hasDerivAt
```

For continuous `derivWithin` and derivative integrability, use:

```lean
ShenWork.IntervalEllipticCharacterization.continuousOn_derivWithin_of_contDiffOn_two
ShenWork.IntervalEllipticCharacterization.intervalIntegrable_deriv_of_contDiffOn_two
ShenWork.IntervalEllipticCharacterization.deriv_eq_derivWithin_interior
```

### `Real.rpow` continuity and chain rule

Try these first:

```lean
ContinuousOn.rpow_const
Real.hasDerivAt_rpow_const
Real.rpow_add
Real.rpow_one
Real.rpow_pos_of_pos
Real.rpow_nonneg
Real.rpow_le_rpow
```

For the derivative chain rule, prefer:

```lean
Real.hasDerivAt_rpow_const
HasDerivAt.comp_hasDerivWithinAt
```

or, if available in this Mathlib version:

```lean
HasDerivWithinAt.rpow_const
```

The repo already uses `Real.hasDerivAt_rpow_const` in `ShenWork/PDE/ODEExistence.lean` and `ContinuousOn.rpow_const` in `IntervalDomainStructuredMoserPower.lean` and `IntervalDomainAPrioriGlobal.lean`.

### Interval-integrability and a.e. endpoint transfer

Try these first:

```lean
ContinuousOn.intervalIntegrable
IntervalIntegrable.const_mul
IntervalIntegrable.mul_continuousOn
IntervalIntegrable.congr
IntervalIntegrable.congr_ae
ContinuousOn.mul
ContinuousOn.rpow_const
ContinuousOn.pow
```

For the null endpoint transfer, follow the pattern in `IntervalDomainL2CrossControl.lean`:

```lean
rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
have hnull : volume ({(1:ℝ)} : Set ℝ) = 0 := by simp
refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
```

Then, for `y ∈ Ioc 0 1` and `y ≠ 1`, build

```lean
have hyIoo : y ∈ Set.Ioo (0:ℝ) 1 := ⟨hyIoc.1, lt_of_le_of_ne hyIoc.2 hy1⟩
```

and rewrite ordinary derivative via:

```lean
ShenWork.IntervalEllipticCharacterization.deriv_eq_derivWithin_interior hyIoo
```

### Interval-domain integral rewrites

Use:

```lean
unfold intervalDomain intervalDomainIntegral
intervalIntegral.integral_congr
intervalIntegral.integral_const_mul
intervalIntegral.integral_mono_on
Set.uIcc_of_le
Set.uIoc_of_le
```

For subtype conversion:

```lean
have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
  simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
let x : intervalDomain.Point := ⟨y, hyIcc⟩
simp [intervalDomainLift, hyIcc, x]
```

For `gradNorm`:

```lean
simp [intervalDomain, intervalDomainGradNorm, intervalDomainLift, hyIcc, x, sq_abs]
```

## 3. Existing theorem chain that already handles part of the bridge

Yes, but no single theorem currently proves the target.

Reusable candidates:

1. `ShenWork.IntervalEllipticCharacterization.hasDerivAt_of_contDiffOn_two_interior`  
   Converts closed `Icc` C2 to ordinary interior derivative. Use this before `.hasDerivWithinAt`.

2. `ShenWork.IntervalEllipticCharacterization.continuousOn_derivWithin_of_contDiffOn_two`  
   Gives the continuous closed-interval derivative representative. This is better than trying to prove `ContinuousOn (deriv h) (Icc 0 1)`, which is not faithful for zero-extensions.

3. `ShenWork.IntervalEllipticCharacterization.deriv_eq_derivWithin_interior`  
   Bridges `deriv` and `derivWithin` on the open interior; use it under `congr_ae`.

4. `ShenWork.IntervalEllipticCharacterization.intervalIntegrable_deriv_of_contDiffOn_two`  
   Already proves the a.e. endpoint bridge for `deriv h` itself.

5. `ShenWork.Paper2.IntervalDomainStructuredMoserData.intervalDomain_classical_solution_powerIntegrable`  
   Not directly applicable to arbitrary `f`, but its proof is the exact pattern for power integrability from positivity + closed continuity.

6. `ShenWork.IntervalDomainExistence.integral_pow_le_sup_pow_mul`  
   Can support the first `∫ f^q ≤ sup^(q-1) * mass` step if the import graph allows. I would not route through `intervalDomain_Lp_interpolation_classicalSlice` unchanged because it still requires ordinary `HasDerivAt` on `Icc`.

7. `ShenWork.IntervalDomainExistence.intervalDomain_Lp_interpolation_classicalSlice`  
   Useful as a pattern only. It packages old Agmon + power estimate but is not endpoint-safe as stated.

## 4. Next Lean lemma statements to add

I would add these in the following order. They are proof-producing lemmas, not residual wrappers.

### Lemma 1: the Agmon input bundle for `g = h^(q/2)`

This isolates all endpoint and integrability pain. Use `gp` with ordinary `deriv h`, but prove integrability via the `derivWithin` continuous representative and a.e. equality.

```lean
import ShenWork.PDE.GagliardoNirenberg
import ShenWork.PDE.IntervalEllipticCharacterization
import ShenWork.Paper2.IntervalDomainLemma41
import ShenWork.PDE.IntervalDomain

open MeasureTheory Set intervalIntegral
open ShenWork.IntervalDomain
open ShenWork.IntervalEllipticCharacterization

noncomputable section

namespace ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

/-- Input package for endpoint-safe Agmon applied to
`g = (intervalDomainLift f)^(q/2)`. -/
theorem intervalDomain_positive_C2_rpowHalf_agmonInputs
    {q : ℝ} (hq : 1 < q)
    {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x)
    (hfC2 : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)) :
    let h : ℝ → ℝ := intervalDomainLift f
    let g : ℝ → ℝ := fun y => h y ^ (q / 2)
    let gp : ℝ → ℝ := fun y =>
      (q / 2) * h y ^ (q / 2 - 1) * deriv h y
    ContinuousOn g (Set.Icc (0 : ℝ) 1) ∧
      (∀ y ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivWithinAt g (gp y) (Set.Ioi y) y) ∧
      IntervalIntegrable gp volume 0 1 ∧
      IntervalIntegrable (fun y => g y ^ 2) volume 0 1 ∧
      IntervalIntegrable (fun y => gp y ^ 2) volume 0 1 ∧
      IntervalIntegrable (fun y => g y * gp y) volume 0 1
```

This is the most useful next lemma. If it is too large, split out only the last three integrability conjuncts into a separate lemma.

### Lemma 2: rewrite the Agmon derivative integral to the interval-domain `G`

This should be proved by `intervalIntegral.integral_congr` plus rpow arithmetic and `sq_abs`.

```lean
/-- Rewrites the squared derivative of `f^(q/2)` to the weighted gradient
integral used by `UnitIntervalPositiveAgmonInterpolation`. -/
theorem intervalDomain_rpowHalf_deriv_sq_integral_eq
    {q : ℝ} (hq : 1 < q)
    {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x) :
    let h : ℝ → ℝ := intervalDomainLift f
    let gp : ℝ → ℝ := fun y =>
      (q / 2) * h y ^ (q / 2 - 1) * deriv h y
    ∫ y in (0 : ℝ)..1, gp y ^ 2 =
      (q ^ 2 / 4) * intervalDomain.integral
        (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2)
```

Key local arithmetic:

```lean
have hpow_exp : (q / 2 - 1) + (q / 2 - 1) = q - 2 := by ring
have hcoeff : (q / 2) * (q / 2) = q ^ 2 / 4 := by ring
```

Use `Real.rpow_add` under `0 < intervalDomainLift f y`.

### Lemma 3: endpoint-safe Agmon rewritten to the `Y/G` bound

This is the first theorem that should actually call `agmon_inequality_interval_rightDeriv`.

```lean
/-- Endpoint-safe Agmon for `f^(q/2)`, rewritten in interval-domain notation. -/
theorem intervalDomain_positive_C2_power_agmon_core
    {q : ℝ} (hq : 1 < q)
    {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x)
    (hfC2 : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)) :
    let Y : ℝ := intervalDomain.integral (fun x => f x ^ q)
    let G : ℝ := intervalDomain.integral
      (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2)
    ∀ y ∈ Set.Icc (0 : ℝ) 1,
      (intervalDomainLift f y) ^ q ≤ 2 * Y + q * Real.sqrt (Y * G)
```

Why pointwise on `Icc` is okay now: the new Agmon theorem returns the estimate for `x ∈ Icc`; it only requires right derivative data on `Ioo`.

Main rewrites:

```lean
(∫ y in (0 : ℝ)..1, (h y ^ (q / 2)) ^ 2) = Y
(∫ y in (0 : ℝ)..1, gp y ^ 2) = (q ^ 2 / 4) * G
```

Then simplify the square-root coefficient using `q > 0`, `Y ≥ 0`, `G ≥ 0`:

```lean
2 * sqrt Y * sqrt ((q ^ 2 / 4) * G) = q * sqrt (Y * G)
```

This scalar simplification may deserve a tiny helper lemma if `nlinarith`/`rw [Real.sqrt_mul]` gets noisy.

### Lemma 4: uniform pre-absorption, then final closure

This must choose its constant before `f`.

```lean
/-- Uniform Young/pre-absorption step from the pointwise power Agmon core. -/
theorem intervalDomain_positive_C2_pre_absorption_uniform
    {q δ : ℝ} (hq : 1 < q) (hδ : 0 < δ) :
    ∃ Cδ : ℝ, 0 ≤ Cδ ∧
      ∀ f : intervalDomain.Point → ℝ,
        (∀ x, 0 < f x) →
        ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) →
          let Y : ℝ := intervalDomain.integral (fun x => f x ^ q)
          let G : ℝ := intervalDomain.integral
            (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2)
          let Mp : ℝ := (intervalDomain.integral f) ^ q
          Y ≤ 2 * δ * Y + δ * q * Real.sqrt (Y * G) + Cδ * Mp
```

This can use either:

- the direct pointwise route from Lemma 3:
  `f^q ≤ B` implies `f^(q-1) ≤ B^((q-1)/q)`, integrate `f * f^(q-1)`; or
- existing `integral_pow_le_sup_pow_mul` plus a new `intervalDomainSupNorm_rpow_le_of_pointwise_rpow_le` helper.

I prefer the direct pointwise route because it avoids `sSup`/`intervalDomainSupNorm` friction.

After Lemma 4, the final theorem is just:

```lean
-- final closure outline, using existing interpolation_absorption
theorem unitIntervalPositiveAgmonInterpolation_proved :
    UnitIntervalPositiveAgmonInterpolation := by
  intro q hq eps heps
  -- choose δ with 0<δ, δ<1/4, and δ^2*q^2/(1-2δ)^2 ≤ eps
  -- obtain Cδ from intervalDomain_positive_C2_pre_absorption_uniform
  -- set Ceps := 2*Cδ/(1 - 2*δ) + 1
  -- for each f, apply pre-absorption and then
  -- ShenWork.Paper2.IntervalDomainLemma41.interpolation_absorption
```

Do not choose `Cδ` after `f`; that would recreate the old non-uniform slice problem.

## Conversion notes for the final proof

### `intervalDomainLift` power equality

Inside `y ∈ Icc 0 1`:

```lean
let x : intervalDomain.Point := ⟨y, hy⟩
have hpow_lift :
    intervalDomainLift (fun x : intervalDomain.Point => f x ^ q) y =
      (intervalDomainLift f y) ^ q := by
  simp [intervalDomainLift, hy, x]
```

### `g^2 = h^q`

For `hpos : 0 < h y`:

```lean
have hhalf : h y ^ (q / 2) * h y ^ (q / 2) = h y ^ q := by
  rw [← Real.rpow_add hpos]
  ring_nf
```

Then use `pow_two`.

### `gp^2` rewrite

For `hpos : 0 < h y`:

```lean
have hpow : h y ^ (q / 2 - 1) * h y ^ (q / 2 - 1) = h y ^ (q - 2) := by
  rw [← Real.rpow_add hpos]
  ring_nf
have hcoeff : (q / 2) * (q / 2) = q ^ 2 / 4 := by ring
```

Then unfold `gp`, use `pow_two`, `hpow`, `hcoeff`, and `sq_abs` for `gradNorm`.

### `gradNorm` rewrite

Under `hy : y ∈ Icc 0 1` and `x := ⟨y, hy⟩`:

```lean
simp [intervalDomain, intervalDomainGradNorm, intervalDomainLift, hy, x, sq_abs]
```

This turns the target gradient integrand into a statement about `(deriv (intervalDomainLift f) y)^2`.

### a.e. endpoint bridge

For integrability of expressions using ordinary `deriv h`, prove the corresponding expression with `derivWithin h (Icc 0 1)` continuous on `Icc`, then transfer with `.congr_ae`. The only bad point under the interval-integral restricted measure is `{1}` after rewriting to `Ioc 0 1`.

This is the same endpoint convention used in `IntervalEllipticCharacterization.intervalIntegrable_deriv_of_contDiffOn_two` and in the cross-control proof.

## Final recommendation

Add the Agmon-input bundle and the derivative-square rewrite first. Those are the two highest-value, most local lemmas. Once `intervalDomain_positive_C2_power_agmon_core` compiles, the final `UnitIntervalPositiveAgmonInterpolation` proof should be a standard Young + `interpolation_absorption` exercise, with the main remaining risk being scalar `rpow`/Young algebra rather than endpoint analysis.
