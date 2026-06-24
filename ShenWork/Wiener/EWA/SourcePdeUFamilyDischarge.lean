/-
  ShenWork/Wiener/EWA/SourcePdeUFamilyDischarge.lean

  **χ₀<0 — discharging the tractable members of the `pde_u` family carried by
  `realSlice_reducedCore` (SourceReducedCore.lean:84).**

  For `u = realSlice u_star` the reduced core carries a family of per-interior-point
  `pde_u` hypotheses.  Five of them follow CLEANLY from already-banked/landed atoms
  (none touch the `rpow u^γ` defeq wall that blocked the resolver source):

  * `htime`     ← the landed time spectral bridge `fullSourceCoeff_timeDeriv_eq`
                  (SourceSpectralBridges.lean), fed `0 < t` and the eventual
                  cosine-synthesis agreement built from the carried slab `realizes`.
  * `hlap`      ← the landed Laplacian spectral bridge `fullSourceCoeff_laplacian_eq`
                  (SourceSpectralBridges.lean), fed the eigenvalue-ℓ¹ summability
                  `hsumE` at the slice time and the carried `realizes` on `Icc 0 1`.
  * `hsum_lap`  ← `hsumE` by comparison (`λₙ ≥ 0`, `|cosineMode| ≤ 1`).
  * `hsum_chem` ← the `DuhamelSourceTimeC1` envelope of `coupledChemDivSourceCoeffs`
                  (`henv_bound` + `henv_summable`) by comparison.
  * `hsum_log`  ← the `DuhamelSourceTimeC1` envelope of `coupledLogisticSourceCoeffs`
                  by comparison.

  The remaining two members `hchemInv`/`hlogInv` are the cosine-inversion
  identities `chemDiv_source_inversion`/`logistic_source_inversion`
  (SourceInversion.lean): each consumes a CONTINUOUS surrogate `g` agreeing with the
  source lift on `[0,1]` together with the `ℓ¹` Fourier summability of `reflCircle g`.
  Those surrogate atoms are NOT among the banked feeders of `realSlice_reducedCore`,
  so they are left as honest residuals (see the module docstring tail) rather than
  faked.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceSpectralBridges
import ShenWork.Wiener.EWA.SourceTimeDerivDischarge

noncomputable section

namespace ShenWork.EWA

open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift intervalDomain)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)
open Set Filter Topology

/-! ### `|cosineMode| ≤ 1`. -/

private theorem cosineMode_abs_le_one' (n : ℕ) (x : ℝ) : |cosineMode n x| ≤ 1 := by
  simp only [cosineMode]; exact Real.abs_cos_le_one _

/-! ### `htime` — the time-derivative member, from the landed time bridge. -/

/-- **`htime` of the `pde_u` family, discharged.**  At an interior time
`t ∈ Ioo 0 T`, the interval-domain time derivative of the slice equals the
`fullSourceCoeffDot` synthesis.  Direct from the landed `fullSourceCoeff_timeDeriv_eq`,
fed `0 < t` and the eventual cosine-synthesis agreement near `t` extracted from the
carried slab `realizes` (`Ioo 0 T` is open, so agreement holds on a neighborhood). -/
theorem realSlice_htime_of_atoms (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u)) {T : ℝ}
    (hrealizes : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) x
        = ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      x.1 ∈ Ioo (0 : ℝ) 1 →
      intervalDomain.timeDeriv u t x
        = ∑' n, fullSourceCoeffDot p u u₀cos t n * cosineMode n x.1 := by
  intro t ht x _
  -- eventual agreement of the slice with the cosine synthesis, pointwise in `x`.
  have hrep : ∀ᶠ s in nhds t, ∀ y : intervalDomainPoint,
      u s y = ∑' n, fullSourceCoeff p u u₀cos s n * cosineMode n y.1 := by
    refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) (fun s hs y => ?_)
    have hlift : intervalDomainLift (u s) y.1 = u s y := by
      simp [intervalDomainLift, y.2]
    rw [← hlift, hrealizes s hs y.1 y.2]
  exact fullSourceCoeff_timeDeriv_eq p u u₀cos hu0bd hchem hlog ht.1 hrep x

/-! ### `hlap` — the Laplacian member, from the landed Laplacian bridge. -/

/-- **`hlap` of the `pde_u` family, discharged.**  At an interior time
`t ∈ Ioo 0 T`, the interval-domain Laplacian of the slice equals the term-by-term
second-spatial-derivative cosine series.  Direct from the landed
`fullSourceCoeff_laplacian_eq`, fed the eigenvalue-ℓ¹ summability `hsumE` at the
slice time and the carried slab `realizes` on `Icc 0 1`. -/
theorem realSlice_hlap_of_atoms (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {T : ℝ}
    (hsumE : ∀ t ∈ Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |fullSourceCoeff p u u₀cos t n|))
    (hrealizes : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) x
        = ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      x.1 ∈ Ioo (0 : ℝ) 1 →
      intervalDomain.laplacian (u t) x
        = ∑' n, (-(unitIntervalCosineEigenvalue n))
            * fullSourceCoeff p u u₀cos t n * cosineMode n x.1 := by
  intro t ht x hx
  exact fullSourceCoeff_laplacian_eq p u u₀cos (hsumE t ht) (hrealizes t ht) hx

/-! ### `hsum_lap` — Laplacian-series summability, from `hsumE`. -/

/-- **`hsum_lap` of the `pde_u` family, discharged.**  The Laplacian cosine series is
summable at every interior `(t,x)`: comparison against `hsumE`'s ℓ¹ majorant
`λₙ·|coeffₙ|`, using `λₙ ≥ 0` and `|cosineMode| ≤ 1`. -/
theorem realSlice_hsum_lap_of_atoms (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {T : ℝ}
    (hsumE : ∀ t ∈ Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |fullSourceCoeff p u u₀cos t n|)) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      x.1 ∈ Ioo (0 : ℝ) 1 →
      Summable (fun n => unitIntervalCosineEigenvalue n
        * fullSourceCoeff p u u₀cos t n * cosineMode n x.1) := by
  intro t ht x _
  refine Summable.of_norm
    ((hsumE t ht).of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_))
  have hlam : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue; positivity
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hlam]
  calc unitIntervalCosineEigenvalue n * |fullSourceCoeff p u u₀cos t n|
          * |cosineMode n x.1|
      ≤ unitIntervalCosineEigenvalue n * |fullSourceCoeff p u u₀cos t n| * 1 :=
        mul_le_mul_of_nonneg_left (cosineMode_abs_le_one' n x.1)
          (mul_nonneg hlam (abs_nonneg _))
    _ = unitIntervalCosineEigenvalue n * |fullSourceCoeff p u u₀cos t n| := mul_one _

/-! ### `hsum_chem` / `hsum_log` — source-series summability, from the envelopes. -/

/-- Generic envelope-comparison: if `a` carries a `DuhamelSourceTimeC1` structure, then
the cosine series `aₙ(t)·cos(nπx)` is summable for every `t ≥ 0`, by comparison against
the ℓ¹ envelope (`|a s n| ≤ envelope n` for `s ≥ 0`, `|cosineMode| ≤ 1`). -/
private theorem duhamelSource_cosineSeries_summable {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC1 a) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    Summable (fun n => a t n * cosineMode n x) := by
  refine Summable.of_norm
    (src.henv_summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_))
  have hcos := cosineMode_abs_le_one' n x
  rw [Real.norm_eq_abs, abs_mul]
  calc |a t n| * |cosineMode n x|
      ≤ |a t n| * 1 := mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
    _ = |a t n| := mul_one _
    _ ≤ src.envelope n := src.henv_bound t ht n

/-- **`hsum_chem` of the `pde_u` family, discharged.**  Comparison against the
chemDiv `DuhamelSourceTimeC1` envelope. -/
theorem realSlice_hsum_chem_of_atoms (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u)) {T : ℝ} :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      x.1 ∈ Ioo (0 : ℝ) 1 →
      Summable (fun n =>
        coupledChemDivSourceCoeffs p u t n * cosineMode n x.1) :=
  fun t ht x _ => duhamelSource_cosineSeries_summable hchem ht.1.le x.1

/-- **`hsum_log` of the `pde_u` family, discharged.**  Comparison against the
logistic `DuhamelSourceTimeC1` envelope. -/
theorem realSlice_hsum_log_of_atoms (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ)
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u)) {T : ℝ} :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      x.1 ∈ Ioo (0 : ℝ) 1 →
      Summable (fun n =>
        coupledLogisticSourceCoeffs p u t n * cosineMode n x.1) :=
  fun t ht x _ => duhamelSource_cosineSeries_summable hlog ht.1.le x.1

end ShenWork.EWA
