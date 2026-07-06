ANSWER Q3626 dae2ca6e

# Q3626 audit: next theorem for the chemotaxis differentiated leg

Audited repo/head:

```text
xiangyazi24/Shen_work
main at f36d73122ef55971a3efb1ecafc6c5f1ab63fb14
```

Relevant source evidence:

* `ShenWork/PDE/IntervalGradDuhamelBound.lean` now contains the full-kernel first-gradient zero-time API:
  ```lean
  gradDuhamel_tendsto_zero_of_bounded
  valueDuhamel_deriv_tendsto_zero_of_bounded
  ```
  The underlying bound is `gradDuhamel_sup_bound`, which integrates `(t-s)^(-1/2)` into a `√t` factor.
* `ShenWork/PDE/IntervalFullKernelSecondDerivCtheta.lean` contains the needed kernel-side Hölder-cancellation estimate:
  ```lean
  neumannHeatSecondDeriv_Ctheta_to_Linfty
  ```
  with conclusion
  ```lean
  |deriv (fun z => deriv (fun w => intervalFullSemigroupOperator t h w) z) x|
    ≤ weightedHeatHessConst θ * t ^ (-1 + θ / 2 : ℝ) * Hh
  ```
  for `0 < t`, `0 < θ < 1`, measurable/bounded `h`, Hölder modulus `Hh`, and `x ∈ Set.Icc 0 1`.
* `ShenWork/Paper2/IntervalGradientDuhamelMap.lean` defines the actual mild map with `intervalFullSemigroupOperator`; its chemotaxis term is already the first spatial derivative of the full-kernel semigroup applied to `chemFluxLifted`.
* `ShenWork/Paper2/IntervalChiNegH1BFormZeroStartTraceProducer.lean` defines the downstream residual `PatchedSliceDerivUniformApproachAtZero`.  This audit does not consume that residual or `ux_zeroFace`.

## Executive answer

The next faithful theorem is a generic full-kernel second-spatial-derivative Duhamel zero-time theorem:

```lean
secondDerivDuhamel_tendsto_zero_of_uniform_holder
```

It should live in a new PDE file, for example:

```text
ShenWork/PDE/IntervalSecondDerivDuhamelZero.lean
```

This keeps the theorem out of the dirty PPID/BForm files and avoids adding new imports to `IntervalGradDuhamelBound.lean`.  It imports only the kernel estimate stack and Mathlib rpow integration tools.

The theorem must assume a uniform Hölder modulus for the source family.  Boundedness alone is not enough for the chemotaxis differentiated leg, because the second-derivative full-kernel `L∞` estimate has a non-integrable `(t-s)^(-1)` singularity.  The existing Hölder cancellation improves this to `(t-s)^(-1 + θ/2)`, which is integrable when `0 < θ`.

## Recommended file and imports

```lean
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import ShenWork.PDE.IntervalFullKernelSecondDerivCtheta

open MeasureTheory intervalIntegral
open scoped Topology

open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.IntervalNeumannFullKernel

noncomputable section

namespace ShenWork.IntervalSecondDerivDuhamelZero
```

I recommend a new namespace rather than extending `ShenWork.IntervalGradDuhamelBound`, because this is the second-derivative/Hölder analogue and depends on a different kernel file.

## Calculus helper 1: interval-integrability of the singular power

Add:

```lean
/-- `(t-s)^(-1+θ/2)` is interval-integrable on `[0,t]` when `0 < θ`.
The endpoint `s=t` is an improper singularity, but the exponent is greater than
`-1`. -/
theorem intervalIntegrable_sub_rpow_neg_one_add_half
    {θ t : ℝ} (hθ0 : 0 < θ) :
    IntervalIntegrable
      (fun s : ℝ => (t - s) ^ (-1 + θ / 2 : ℝ)) volume 0 t := by
  have hpow : IntervalIntegrable
      (fun x : ℝ => x ^ (-1 + θ / 2 : ℝ)) volume 0 t :=
    intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < -1 + θ / 2)
  have h := (hpow.comp_sub_left t).symm
  simpa using h
```

Notes:

* `hθ0` is enough: `-1 < -1 + θ/2`.
* No `hθ1` is needed for this integrability lemma.
* This mirrors `intervalIntegrable_sub_rpow_neg_half` in `IntervalGradDuhamelBound.lean`.

## Calculus helper 2: exact integral

Add:

```lean
/-- Exact integral of the Hölder-cancellation singularity:
`∫₀ᵗ (t-s)^(-1+θ/2) ds = t^(θ/2)/(θ/2)`. -/
theorem integral_sub_rpow_neg_one_add_half
    {θ t : ℝ} (ht : 0 ≤ t) (hθ0 : 0 < θ) :
    (∫ s in (0 : ℝ)..t, (t - s) ^ (-1 + θ / 2 : ℝ)) =
      t ^ (θ / 2 : ℝ) / (θ / 2) := by
  rw [intervalIntegral.integral_comp_sub_left
    (fun x : ℝ => x ^ (-1 + θ / 2 : ℝ)) t]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -1 + θ / 2))]
  have hexp : (-1 + θ / 2 : ℝ) + 1 = θ / 2 := by ring
  have hθhalf_ne : (θ / 2 : ℝ) ≠ 0 := by linarith
  rw [hexp, Real.zero_rpow hθhalf_ne, sub_zero]
```

Potential compile adjustment:

If the final expression after `rw` is not syntactically identical because of division normalization, close with:

```lean
  ring
```

or:

```lean
  rfl
```

The pattern is exactly the one already used for `(t-s)^(-1/2)` in `IntervalGradDuhamelBound.lean`.

## Main theorem: second-derivative Duhamel zero-time estimate

Smallest generic theorem statement:

```lean
/-- Zero-time vanishing of the full-kernel second-spatial-derivative Duhamel
integral under a uniform Hölder modulus for the source family.  This is the
Hölder-cancellation analogue of `gradDuhamel_tendsto_zero_of_bounded`. -/
theorem secondDerivDuhamel_tendsto_zero_of_uniform_holder
    {q : ℝ → ℝ → ℝ} {θ Hq Cq : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hHq : 0 ≤ Hq)
    (hq_meas : ∀ s, AEStronglyMeasurable (q s) (intervalMeasure 1))
    (hq_bound : ∀ s y, |q s y| ≤ Cq)
    (hq_holder : ∀ s a b,
      a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |q s a - q s b| ≤ Hq * |a - b| ^ θ)
    (h2_int : ∀ {t x : ℝ}, 0 < t →
      IntervalIntegrable
        (fun s : ℝ =>
          deriv (fun z : ℝ => deriv
            (fun w : ℝ => intervalFullSemigroupOperator (t - s) (q s) w) z) x)
        volume 0 t) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |∫ s in (0 : ℝ)..t,
          deriv (fun z : ℝ => deriv
            (fun w : ℝ => intervalFullSemigroupOperator (t - s) (q s) w) z) x| < ε := by
  intro ε hε
  let β : ℝ := θ / 2
  have hβ_pos : 0 < β := by dsimp [β]; linarith
  let C : ℝ := weightedHeatHessConst θ * Hq
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (weightedHeatHessConst_nonneg θ) hHq
  let A : ℝ := C / β
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg hC_nonneg hβ_pos.le

  -- Choose `δ` so that `t^β < ε/(A+1)`.
  let δ : ℝ := (ε / (A + 1)) ^ (1 / β)
  have hden_pos : 0 < A + 1 := by linarith
  have htarget_pos : 0 < ε / (A + 1) := by positivity
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact Real.rpow_pos_of_pos htarget_pos _

  refine ⟨δ, hδ_pos, ?_⟩
  intro t ht htδ x hx

  -- Pointwise bound away from the endpoint `s=t`.
  have hptw : ∀ s, 0 ≤ s → s < t →
      |deriv (fun z : ℝ => deriv
          (fun w : ℝ => intervalFullSemigroupOperator (t - s) (q s) w) z) x|
        ≤ C * (t - s) ^ (-1 + θ / 2 : ℝ) := by
    intro s hs0 hst
    have hσ : 0 < t - s := by linarith
    have h := neumannHeatSecondDeriv_Ctheta_to_Linfty
      (t := t - s) (θ := θ) hσ hθ0 hθ1
      (h := q s) (hq_meas s) (Ch := Cq) (hq_bound s)
      (Hh := Hq) hHq (hq_holder s) (x := x) hx
    calc
      |deriv (fun z : ℝ => deriv
          (fun w : ℝ => intervalFullSemigroupOperator (t - s) (q s) w) z) x|
          ≤ weightedHeatHessConst θ * (t - s) ^ (-1 + θ / 2 : ℝ) * Hq := h
      _ = C * (t - s) ^ (-1 + θ / 2 : ℝ) := by
        dsimp [C]
        ring

  have hdom_int : IntervalIntegrable
      (fun s : ℝ => C * (t - s) ^ (-1 + θ / 2 : ℝ)) volume 0 t :=
    (intervalIntegrable_sub_rpow_neg_one_add_half (θ := θ) (t := t) hθ0).const_mul C

  -- Exclude the endpoint `s=t`, where the pointwise heat estimate is not used.
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]

  have hae :
      (fun s : ℝ =>
        |deriv (fun z : ℝ => deriv
          (fun w : ℝ => intervalFullSemigroupOperator (t - s) (q s) w) z) x|)
      ≤ᵐ[volume.restrict (Set.Icc 0 t)]
      (fun s : ℝ => C * (t - s) ^ (-1 + θ / 2 : ℝ)) := by
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [hne] with s hs_ne hs_mem
    exact hptw s hs_mem.1 (lt_of_le_of_ne hs_mem.2 hs_ne)

  have hδpow : δ ^ β = ε / (A + 1) := by
    dsimp [δ]
    rw [← Real.rpow_mul (le_of_lt htarget_pos)]
    have hβ_ne : β ≠ 0 := ne_of_gt hβ_pos
    field_simp [hβ_ne]

  have ht_power : t ^ β < ε / (A + 1) := by
    have hpow := Real.rpow_lt_rpow ht.le htδ hβ_pos
    simpa [hδpow] using hpow

  have htail : A * t ^ β < ε := by
    have hstep : A * t ^ β ≤ A * (ε / (A + 1)) :=
      mul_le_mul_of_nonneg_left (le_of_lt ht_power) hA_nonneg
    have hfrac : A * (ε / (A + 1)) < ε := by
      calc
        A * (ε / (A + 1)) = (A * ε) / (A + 1) := by ring
        _ < ε := by
          rw [div_lt_iff₀ hden_pos]
          nlinarith [hε]
    exact lt_of_le_of_lt hstep hfrac

  calc
    |∫ s in (0 : ℝ)..t,
        deriv (fun z : ℝ => deriv
          (fun w : ℝ => intervalFullSemigroupOperator (t - s) (q s) w) z) x|
        ≤ ∫ s in (0 : ℝ)..t,
            |deriv (fun z : ℝ => deriv
              (fun w : ℝ => intervalFullSemigroupOperator (t - s) (q s) w) z) x| :=
          intervalIntegral.abs_integral_le_integral_abs ht.le
    _ ≤ ∫ s in (0 : ℝ)..t, C * (t - s) ^ (-1 + θ / 2 : ℝ) :=
          intervalIntegral.integral_mono_ae_restrict ht.le
            (h2_int (t := t) (x := x) ht).abs hdom_int hae
    _ = C * (t ^ β / β) := by
          rw [intervalIntegral.integral_const_mul,
            integral_sub_rpow_neg_one_add_half (t := t) (θ := θ) ht.le hθ0]
          dsimp [β]
    _ = A * t ^ β := by
          dsimp [A]
          field_simp [ne_of_gt hβ_pos]
          ring
    _ < ε := htail
```

This is the most useful generic theorem for the chemotaxis differentiated leg.  It is explicitly full-kernel and has no dependence on `PatchedSliceDerivUniformApproachAtZero`, `ux_zeroFace`, or helper `intervalSemigroupOperator 1`.

## Leibniz-facing corollary for the actual differentiated chemotaxis leg

The chemotaxis term in the mild map is already a gradient Duhamel term.  To obtain the derivative of that term, downstream code will need a derivative-under-time-integral identity.  The generic corollary should be:

```lean
/-- Zero-time vanishing of the spatial derivative of a full-kernel gradient-Duhamel
leg, assuming the derivative-under-the-time-integral identity. -/
theorem gradDuhamel_deriv_tendsto_zero_of_uniform_holder
    {q : ℝ → ℝ → ℝ} {θ Hq Cq : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hHq : 0 ≤ Hq)
    (hq_meas : ∀ s, AEStronglyMeasurable (q s) (intervalMeasure 1))
    (hq_bound : ∀ s y, |q s y| ≤ Cq)
    (hq_holder : ∀ s a b,
      a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |q s a - q s b| ≤ Hq * |a - b| ^ θ)
    (h2_int : ∀ {t x : ℝ}, 0 < t →
      IntervalIntegrable
        (fun s : ℝ =>
          deriv (fun z : ℝ => deriv
            (fun w : ℝ => intervalFullSemigroupOperator (t - s) (q s) w) z) x)
        volume 0 t)
    (hLeibniz : ∀ {t x : ℝ}, 0 < t →
      deriv (fun y : ℝ =>
        ∫ s in (0 : ℝ)..t,
          deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) y) x =
      ∫ s in (0 : ℝ)..t,
        deriv (fun z : ℝ => deriv
          (fun w : ℝ => intervalFullSemigroupOperator (t - s) (q s) w) z) x) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun y : ℝ =>
          ∫ s in (0 : ℝ)..t,
            deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) y) x| < ε := by
  intro ε hε
  rcases secondDerivDuhamel_tendsto_zero_of_uniform_holder
      hθ0 hθ1 hHq hq_meas hq_bound hq_holder h2_int ε hε with
    ⟨δ, hδ, hδsmall⟩
  exact ⟨δ, hδ, fun t ht htδ x hx => by
    rw [hLeibniz (t := t) (x := x) ht]
    exact hδsmall t ht htδ x hx⟩
```

This corollary is the exact shape needed for the differentiated chemotaxis leg after instantiating

```lean
q s := chemFluxLifted p (D.u s)
```

and proving uniform Hölder data for that source family.

## Why boundedness is not enough

For the logistic derivative leg, `gradDuhamel_tendsto_zero_of_bounded` works from boundedness because the per-slice first-gradient bound has the integrable singularity `(t-s)^(-1/2)`.

For the chemotaxis differentiated leg, differentiating the gradient term introduces the second spatial derivative of the full kernel.  The naive bounded-source estimate would behave like `(t-s)^(-1)`, which is not integrable near `s=t`.  This is why the theorem above must assume a Hölder modulus and use `neumannHeatSecondDeriv_Ctheta_to_Linfty`, whose singularity is `(t-s)^(-1+θ/2)`.

## Lean issues to watch

### 1. Sign of the exponent

Set

```lean
α := -1 + θ / 2
β := θ / 2
```

For `0 < θ < 1`, one has:

```lean
-1 < α
0 < β
α + 1 = β
```

The integrability theorem only needs `0 < θ`, but `neumannHeatSecondDeriv_Ctheta_to_Linfty` also needs `θ < 1`.

### 2. `Real.rpow` at zero

The exact integral proof uses:

```lean
Real.zero_rpow (by linarith : θ / 2 ≠ 0)
```

because the antiderivative contributes `0^(θ/2)`, not `0^(-1+θ/2)`.  This is safe since `θ/2 > 0`.

The pointwise domination should **not** be applied at `s=t`, where `(t-s)=0` and the kernel estimate requires a positive heat time.  Exclude `s=t` a.e. exactly as in `gradDuhamel_sup_bound`:

```lean
have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
  rw [ae_iff]
  simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
```

and then use `integral_mono_ae_restrict` over `volume.restrict (Set.Icc 0 t)`.

### 3. Interval-integrability of the second-derivative integrand

Keep this as an explicit hypothesis:

```lean
h2_int : ∀ {t x : ℝ}, 0 < t → IntervalIntegrable ... volume 0 t
```

The current theorem should prove the analytic smallness from the kernel estimate, not a Leibniz/regularity theorem about the time-dependent source.

### 4. Source hypotheses

`neumannHeatSecondDeriv_Ctheta_to_Linfty` requires:

* `AEStronglyMeasurable (q s) (intervalMeasure 1)`
* a pointwise bound `∀ y, |q s y| ≤ Cq`
* a Hölder modulus on `[0,1]`

The bound constant `Cq` does not need a nonnegativity assumption for this theorem, because it is only passed to the existing boundedness hypothesis.  The actual smallness rate depends on `Hq`, not `Cq`.

### 5. `rpow` horizon

The clean horizon is:

```lean
δ := (ε / (A + 1)) ^ (1 / β)
where β = θ / 2, A = weightedHeatHessConst θ * Hq / β.
```

Then show:

```lean
t < δ  ⇒  t^β < ε/(A+1)
```

using:

```lean
Real.rpow_lt_rpow ht.le htδ hβ_pos
Real.rpow_mul
```

For `Real.rpow_mul`, the base is `ε/(A+1)`, which is strictly positive.

### 6. Multiplication order

The existing kernel theorem returns:

```lean
weightedHeatHessConst θ * (t - s)^α * Hq
```

The integrable majorant is cleaner as:

```lean
C * (t - s)^α
where C = weightedHeatHessConst θ * Hq
```

Use `ring` to rewrite the multiplication order.

## Downstream instantiation plan

To use this for `PatchedSliceDerivUniformApproachAtZero`, a later clean bridge should decompose the derivative of the mild equation into:

1. homogeneous initial leg — already handled by the C¹/full-Neumann initial package;
2. logistic derivative leg — handled by `valueDuhamel_deriv_tendsto_zero_of_bounded`;
3. chemotaxis differentiated leg — handled by the theorem proposed here, with
   ```lean
   q s := chemFluxLifted p (D.u s)
   ```
   and uniform Hölder data for `chemFluxLifted` near zero;
4. a derivative-of-fixed-point-equation/Leibniz bridge.

The new theorem is non-circular: it does not consume the target residual or zero-face fields.  It is also faithful: every operator in the statement is `intervalFullSemigroupOperator`, matching `IntervalGradientDuhamelMap.lean`.

## Final recommendation

Add a new file:

```text
ShenWork/PDE/IntervalSecondDerivDuhamelZero.lean
```

with the two calculus helpers plus:

```lean
secondDerivDuhamel_tendsto_zero_of_uniform_holder
```

and optionally:

```lean
gradDuhamel_deriv_tendsto_zero_of_uniform_holder
```

This is the next smallest faithful PDE theorem for the chemotaxis differentiated leg.  It should land before any attempt to wire `PatchedSliceDerivUniformApproachAtZero` in the BForm/PPID layer.
