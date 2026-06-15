/-
  ShenWork/Wiener/EWA/SourceSpectralBridges.lean

  **χ₀<0 classical-PDE-satisfaction — Laplacian + time spectral bridges.**

  Two `fullSourceCoeff` specializations mirroring the committed χ₀=0
  `laplacian_eq_of_rep` / `timeDeriv_eq_of_rep` (IntervalDomainPdeUChiZero.lean):

  * (A) `fullSourceCoeff_laplacian_eq` — a direct instantiation of the committed
    `laplacian_eq_of_rep` at `b := fullSourceCoeff p u u₀cos t₀`, with a `tsum_congr`
    converting `bₙ·(−(nπ)²·cos(nπx))` to `−λₙ·fullSourceCoeff·cosineMode`
    (`unitIntervalCosineEigenvalue n = (nπ)²` and `cosineMode n x = cos(nπx)`, both
    definitional).

  * (B) `fullSourceCoeff_timeDeriv_eq` — the time bridge: transport `(fun s => u s x)`
    to the cosine synthesis near `t₀` from `hrep`, then `.congr_of_eventuallyEq`
    / `.deriv` against the committed `fullSourceCoeff_hasDerivAt_time`.

  `hsum`/`hrep`/`hu0bd`/`hchem`/`hlog` are CARRIED inputs (the assembly discharges
  them from the committed `fullSourceCoeff_eigenvalue_summable` / `realizes_clean`).

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceTimeRegularitySlice
import ShenWork.Paper2.IntervalDomainPdeUChiZero

noncomputable section

namespace ShenWork.EWA

open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift intervalDomain)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)
open Set Filter Topology

/-- **(A) Laplacian bridge for `fullSourceCoeff`.**  Direct instantiation of the
committed `ShenWork.IntervalDomainPdeUChiZero.laplacian_eq_of_rep` at
`b := fullSourceCoeff p u u₀cos t₀`, converting the spectral RHS to the
`−λₙ·coeff·cosineMode` form via the definitional equalities
`unitIntervalCosineEigenvalue n = (nπ)²` and `cosineMode n x = cos(nπx)`. -/
theorem fullSourceCoeff_laplacian_eq (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (u₀cos : ℕ → ℝ) {t₀ : ℝ}
    (hsum : Summable
      (fun n => unitIntervalCosineEigenvalue n * |fullSourceCoeff p u u₀cos t₀ n|))
    (hrep : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u t₀) y = ∑' n, fullSourceCoeff p u u₀cos t₀ n * cosineMode n y)
    {x : intervalDomainPoint} (hx : x.1 ∈ Set.Ioo (0 : ℝ) 1) :
    intervalDomain.laplacian (u t₀) x
      = ∑' n, (-(unitIntervalCosineEigenvalue n)) * fullSourceCoeff p u u₀cos t₀ n
          * cosineMode n x.1 := by
  rw [ShenWork.IntervalDomainPdeUChiZero.laplacian_eq_of_rep hsum hrep hx]
  refine tsum_congr (fun n => ?_)
  simp only [unitIntervalCosineEigenvalue, cosineMode]; ring

/-- **(B) Time bridge for `fullSourceCoeff`.**  At an interior time `t₀ > 0`, if `u`
agrees near `t₀` with its cosine synthesis (`hrep`), the pointwise time derivative is
the `fullSourceCoeffDot` synthesis.  Transport `(fun s => u s x)` to the synthesis via
`hrep`, then apply `(fullSourceCoeff_hasDerivAt_time …).congr_of_eventuallyEq |>.deriv`. -/
theorem fullSourceCoeff_timeDeriv_eq (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (u₀cos : ℕ → ℝ) {Mu0 : ℝ} (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u))
    {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hrep : ∀ᶠ s in nhds t₀, ∀ y : intervalDomainPoint,
      u s y = ∑' n, fullSourceCoeff p u u₀cos s n * cosineMode n y.1)
    (x : intervalDomainPoint) :
    intervalDomain.timeDeriv u t₀ x
      = ∑' n, fullSourceCoeffDot p u u₀cos t₀ n * cosineMode n x.1 := by
  have heq : (fun s => u s x) =ᶠ[𝓝 t₀]
      (fun s => ∑' n, fullSourceCoeff p u u₀cos s n * cosineMode n x.1) := by
    filter_upwards [hrep] with s hs using hs x
  have hd := (fullSourceCoeff_hasDerivAt_time p u u₀cos hu0bd hchem hlog ht₀ x.1
    ).congr_of_eventuallyEq heq
  change deriv (fun s => u s x) t₀ = _
  rw [hd.deriv]

end ShenWork.EWA
