# Q1249 / cron1 — `HasDerivAt` of `heatDu` in time

Repo: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target file updated by this drop:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Summary

The requested proof should live in:

```text
ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean
```

and should be inserted after `heatD2u` / after the existing `heatDu_eq_secondValue` bridge.  It differentiates

```lean
heatDu u₀ t x
```

at positive `t` by working on the open one-sided neighborhood

```lean
Set.Ioi (t / 2)
```

where the `if 0 < r then ... else 0` branch of `heatDu` is definitionally the Laplacian cosine series.  The core step is exactly the repo lemma:

```lean
ShenWork.HasDerivWithinAtTsum.hasDerivWithinAt_tsum
```

from `ShenWork/PDE/HasDerivWithinAtTsum.lean`, applied to the terms

```lean
F n τ  = unitIntervalCosineHeatLaplacianPointWeight τ x n * a n
F' n τ = λ_n^2 * (Real.exp (-τ * λ_n) * a n) * cosineMode n x
```

with majorant

```lean
u n = M₀ * (λ_n^2 * Real.exp (-(t / 2) * λ_n)).
```

The only helper not already named in the nearby files is the elementary summability of `λ_n^2 * exp (-r λ_n)` for `r > 0`; it is proved from `Real.summable_pow_mul_exp_neg_nat_mul 4` exactly like the existing `unitIntervalCosineEigenvalue_mul_exp_summable` proof.

## Pasteable proof block

Standalone check imports are included below.  If pasting directly into `IntervalHeatSemigroupFlooredSourceTimeData.lean`, add the two imports and then paste the declarations inside the existing namespace; do **not** keep the self-import line.

```lean
import ShenWork.Paper2.IntervalHeatSemigroupFlooredSourceTimeData
import ShenWork.PDE.HasDerivWithinAtTsum
import ShenWork.Paper2.IntervalMildRegularityBootstrap

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.RegularityBootstrap

noncomputable section

namespace ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-- Heat smoothing supplies the quadratic polynomial weight needed for the
second time derivative of the heat semigroup:
`∑ λₙ² exp (-r λₙ) < ∞`, for every `r > 0`. -/
private theorem unitIntervalCosineEigenvalue_sq_exp_summable
    {r : ℝ} (hr : 0 < r) :
    Summable fun n : ℕ =>
      (λ_ n) ^ 2 * Real.exp (-r * (λ_ n)) := by
  set ρ : ℝ := r * Real.pi ^ 2 with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    positivity
  have hbase : Summable fun n : ℕ =>
      Real.pi ^ 4 * ((n : ℝ) ^ 4 * Real.exp (-ρ * (n : ℝ))) := by
    simpa using
      (Real.summable_pow_mul_exp_neg_nat_mul 4 (r := ρ) hρpos).mul_left
        (Real.pi ^ 4)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hbase
  · exact mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)
  · have hn_sq_ge : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      by_cases hn : n = 0
      · subst n
        norm_num
      · have hn0 : (0 : ℝ) ≤ n := by positivity
        have hn1 : (1 : ℝ) ≤ n := by
          exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
        have hmul : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) :=
          mul_nonneg hn0 (sub_nonneg.mpr hn1)
        nlinarith
    have hlam_eq : (λ_ n) = (n : ℝ) ^ 2 * Real.pi ^ 2 := by
      unfold unitIntervalCosineEigenvalue
      ring
    have hlam_sq_eq : (λ_ n) ^ 2 = (n : ℝ) ^ 4 * Real.pi ^ 4 := by
      rw [hlam_eq]
      ring
    have hexp_le :
        Real.exp (-r * (λ_ n)) ≤ Real.exp (-ρ * (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hmul : ρ * (n : ℝ) ≤ ρ * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hn_sq_ge hρpos.le
      rw [hlam_eq, hρdef] at hmul ⊢
      nlinarith
    calc
      (λ_ n) ^ 2 * Real.exp (-r * (λ_ n))
          = ((n : ℝ) ^ 4 * Real.pi ^ 4) *
              Real.exp (-r * (λ_ n)) := by rw [hlam_sq_eq]
      _ ≤ ((n : ℝ) ^ 4 * Real.pi ^ 4) *
              Real.exp (-ρ * (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hexp_le (by positivity)
      _ = Real.pi ^ 4 * ((n : ℝ) ^ 4 * Real.exp (-ρ * (n : ℝ))) := by
            ring

/-- One differentiated Laplacian-weighted heat cosine term. -/
private theorem heatLaplacianTerm_hasDerivAt_time
    (a : ℕ → ℝ) (x t : ℝ) (n : ℕ) :
    HasDerivAt
      (fun τ : ℝ =>
        unitIntervalCosineHeatLaplacianPointWeight τ x n * a n)
      ((λ_ n) ^ 2 * (Real.exp (-t * (λ_ n)) * a n) * cosineMode n x) t := by
  let lam : ℝ := λ_ n
  have hlin : HasDerivAt (fun τ : ℝ => -τ * lam) (-lam) t := by
    have h := (hasDerivAt_id t).neg.mul_const lam
    simpa [lam] using h
  have hexp : HasDerivAt (fun τ : ℝ => Real.exp (-τ * lam))
      (-lam * Real.exp (-t * lam)) t := by
    simpa using hlin.exp
  have h := ((hexp.mul_const (cosineMode n x)).const_mul (-lam)).mul_const (a n)
  convert h using 1
  · ext τ
    simp [unitIntervalCosineHeatLaplacianPointWeight,
      unitIntervalCosineHeatPointWeight, lam]
    ring
  · simp [lam]
    ring

/-- Bounded coefficients give a summable base series for the heat Laplacian. -/
private theorem summable_heatLaplacian_terms_of_bound
    {a : ℕ → ℝ} {M t x : ℝ} (ht : 0 < t)
    (ha : ∀ n, |a n| ≤ M) :
    Summable fun n : ℕ =>
      unitIntervalCosineHeatLaplacianPointWeight t x n * a n := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (ha 0)
  have hmajor : Summable fun n : ℕ =>
      M * ((λ_ n) * Real.exp (-t * (λ_ n))) :=
    (ShenWork.IntervalMildRegularityBootstrap
      .unitIntervalCosineEigenvalue_mul_exp_summable ht).mul_left M
  refine Summable.of_norm_bounded hmajor ?_
  intro n
  have hlam_nonneg : 0 ≤ λ_ n := by
    unfold unitIntervalCosineEigenvalue
    positivity
  have hcos : |cosineMode n x| ≤ 1 := by
    simp only [cosineMode]
    exact Real.abs_cos_le_one _
  rw [Real.norm_eq_abs]
  calc
    |unitIntervalCosineHeatLaplacianPointWeight t x n * a n|
        = (λ_ n) * Real.exp (-t * (λ_ n)) * |cosineMode n x| * |a n| := by
          simp [unitIntervalCosineHeatLaplacianPointWeight,
            unitIntervalCosineHeatPointWeight, abs_mul,
            abs_of_nonneg hlam_nonneg, abs_of_nonneg (Real.exp_nonneg _)]
          ring
    _ ≤ (λ_ n) * Real.exp (-t * (λ_ n)) * 1 * M := by
          gcongr
          exact hcos
          exact ha n
    _ = M * ((λ_ n) * Real.exp (-t * (λ_ n))) := by
          ring

/-- The differentiated heat-Laplacian term is dominated on `Ioi r` by the
positive-time majorant at `r`. -/
private theorem heatD2Term_abs_le_majorant
    {a : ℕ → ℝ} {M r τ x : ℝ}
    (ha : ∀ n, |a n| ≤ M) (hτ : τ ∈ Set.Ioi r) (n : ℕ) :
    |(λ_ n) ^ 2 * (Real.exp (-τ * (λ_ n)) * a n) * cosineMode n x|
      ≤ M * ((λ_ n) ^ 2 * Real.exp (-r * (λ_ n))) := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (ha 0)
  have hlam_nonneg : 0 ≤ λ_ n := by
    unfold unitIntervalCosineEigenvalue
    positivity
  have hcos : |cosineMode n x| ≤ 1 := by
    simp only [cosineMode]
    exact Real.abs_cos_le_one _
  have hexp_mono : Real.exp (-τ * (λ_ n)) ≤ Real.exp (-r * (λ_ n)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    |(λ_ n) ^ 2 * (Real.exp (-τ * (λ_ n)) * a n) * cosineMode n x|
        = (λ_ n) ^ 2 * Real.exp (-τ * (λ_ n)) * |a n| * |cosineMode n x| := by
          rw [abs_mul, abs_mul, abs_mul,
            abs_of_nonneg (sq_nonneg (λ_ n)),
            abs_of_nonneg (Real.exp_nonneg _)]
          ring
    _ ≤ (λ_ n) ^ 2 * Real.exp (-τ * (λ_ n)) * M * 1 := by
          gcongr
          exact ha n
          exact hcos
    _ = M * ((λ_ n) ^ 2 * Real.exp (-τ * (λ_ n))) := by
          ring
    _ ≤ M * ((λ_ n) ^ 2 * Real.exp (-r * (λ_ n))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hexp_mono (sq_nonneg (λ_ n))) hM

/-- Positive-time derivative of `heatDu`: `∂ₜ ΔS(t)u₀ = Δ²S(t)u₀`.

This is the missing `d1` heat-time atom.  The proof differentiates the
Laplian cosine series term-by-term on `Ioi (t / 2)` using
`HasDerivWithinAtTsum.hasDerivWithinAt_tsum`, then converts the within-set
result to `HasDerivAt` because `Ioi (t / 2)` is a neighborhood of `t`. -/
private theorem heatDu_hasDerivAt
    (u₀ : intervalDomainPoint → ℝ) {M₀ t x : ℝ} (ht : 0 < t)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    HasDerivAt (fun r : ℝ => heatDu u₀ r x) (heatD2u u₀ t x) t := by
  let a : ℕ → ℝ := cosineCoeffs (intervalDomainLift u₀)
  let r : ℝ := t / 2
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hrt : t ∈ Set.Ioi r := by
    dsimp [r]
    linarith
  let F : ℕ → ℝ → ℝ := fun n τ =>
    unitIntervalCosineHeatLaplacianPointWeight τ x n * a n
  let F' : ℕ → ℝ → ℝ := fun n τ =>
    (λ_ n) ^ 2 * (Real.exp (-τ * (λ_ n)) * a n) * cosineMode n x
  let u : ℕ → ℝ := fun n =>
    M₀ * ((λ_ n) ^ 2 * Real.exp (-r * (λ_ n)))
  have hu : Summable u := by
    simpa [u] using
      (unitIntervalCosineEigenvalue_sq_exp_summable (r := r) hr).mul_left M₀
  have hF : ∀ n, ∀ τ ∈ Set.Ioi r,
      HasDerivWithinAt (F n) (F' n τ) (Set.Ioi r) τ := by
    intro n τ _hτ
    exact (heatLaplacianTerm_hasDerivAt_time a x τ n).hasDerivWithinAt
  have hbound : ∀ n, ∀ τ ∈ Set.Ioi r, |F' n τ| ≤ u n := by
    intro n τ hτ
    simpa [F', u, a] using
      heatD2Term_abs_le_majorant
        (a := a) (M := M₀) (r := r) (τ := τ) (x := x)
        (by simpa [a] using hu₀_bound) hτ n
  have hF0 : Summable fun n : ℕ => F n t := by
    simpa [F, a] using
      summable_heatLaplacian_terms_of_bound
        (a := a) (M := M₀) (t := t) (x := x) ht
        (by simpa [a] using hu₀_bound)
  have hwithin :
      HasDerivWithinAt (fun τ : ℝ => ∑' n : ℕ, F n τ)
        (∑' n : ℕ, F' n t) (Set.Ioi r) t :=
    ShenWork.HasDerivWithinAtTsum.hasDerivWithinAt_tsum
      (convex_Ioi r) hu hF hbound hrt hF0 hrt
  have hAtSum :
      HasDerivAt (fun τ : ℝ => ∑' n : ℕ, F n τ)
        (∑' n : ℕ, F' n t) t :=
    hwithin.hasDerivAt (isOpen_Ioi.mem_nhds hrt)
  have hbranch :
      (fun τ : ℝ => heatDu u₀ τ x) =ᶠ[𝓝 t]
        (fun τ : ℝ => ∑' n : ℕ, F n τ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hrt] with τ hτ
    have hτpos : 0 < τ := lt_trans hr hτ
    simp [heatDu, F, a,
      ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianValue, hτpos]
  have hvalue : (∑' n : ℕ, F' n t) = heatD2u u₀ t x := by
    simp [heatD2u, F', a, ht]
  simpa [hvalue] using hAtSum.congr_of_eventuallyEq hbranch

end ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData
```

## Use inside `d1`

After importing/opening `hasDerivAt_srcSlice1`, the time derivative subgoal in `d1` should be:

```lean
have hdu2 : HasDerivAt (fun r : ℝ => heatDu u₀ r x) (heatD2u u₀ s x) s :=
  heatDu_hasDerivAt u₀ (t := s) (x := x) hs_pos _hu₀_bound

exact hasDerivAt_srcSlice1
  (hfloor s hs_pos x hxIcc)
  hderiv_lift
  hdu2
```

where `hderiv_lift` is the already-used first heat derivative proof from `heatSlice_field_hasDerivWithinAt`, converted from the positive slab to `HasDerivAt` exactly as in the existing `d0` proof.

## Notes

* The proof is intentionally on `Ioi (t / 2)`, not on all of `ℝ`, because the `heatDu` definition is branchy and the heat series representation is only the active branch near positive `t`.
* The base summability `hF0` is only the Laplacian series at time `t`; it uses the existing repo lemma `IntervalMildRegularityBootstrap.unitIntervalCosineEigenvalue_mul_exp_summable` and bounded coefficients.
* The derivative majorant uses the stronger quadratic summability helper `unitIntervalCosineEigenvalue_sq_exp_summable` at the lower endpoint `t / 2`.
* I did not run a local `lake build`; this drop was produced through the GitHub connector only.
