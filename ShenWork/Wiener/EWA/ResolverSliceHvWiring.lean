/-
  ShenWork/Wiener/EWA/ResolverSliceHvWiring.lean

  **χ₀<0 capstone wiring — `realSlice_Hv_closed`'s `C`/`hC`/`hdecay`/`ha0` residual
  DISCHARGED from window-uniform `G1`/`G2` (+ the now-internal `m`/`M`).**

  `realSlice_Hv_closed` (`SourcePerSliceClose.lean`) carried — as its single remaining
  residual — the window-uniform power-source quadratic-decay package
  `C`/`hC`/`hdecay`/`ha0`.  `realSlice_powerSource_window_uniform_decay`
  (`ResolverSourceWindowUniformDecay.lean`) produces that package from four
  window-uniform scalar bundles `m`/`M`/`G1`/`G2`.

  This file CLOSES the chain by:

  * discharging the C⁰ pair `m`/`M` INTERNALLY via `realSlice_window_uniform_C0`
    (`ResolverSliceWindowBounds.lean`) — from the value-field joint continuity
    `fullSourceCoeff_jointSolutionClosed` + `hrealizes` + `realSlice_pos`;
  * carrying the C¹/C² pair `G1`/`G2` as the PRECISE remaining frontier (the
    window-uniform first/second spatial-derivative bounds of the lift) — together with
    the window cosine representation `bc`/`hbsum`/`hagree` that
    `realSlice_powerSource_window_uniform_decay` also consumes;
  * feeding the assembled `C`/`hC`/`hdecay`/`ha0` into `realSlice_Hv_closed`.

  Result: `realSlice_Hv` produces
  `HasResolverDirectSpectralData T (mildChemicalConcentration p (realSlice u_star)) p`
  with the `C`/`hC`/`hdecay`/`ha0` residual GONE, carrying instead only:

  * the value-side standing atoms of `realSlice_Hv_closed`
    (`hu0bd`/`hchem`/`hlog`/`hδρ`/`hheat`/`hu_ball`/`hsumE`/`hrealizes`), and
  * the window cosine representation `bc`/`hbsum`/`hagree` + the window-uniform
    SPATIAL-derivative bounds `G1`/`G2`/`hG1`/`hG2` — the honest new frontier (the
    `m`/`M` C⁰ pair is no longer carried; only the C¹/C² pair remains).

  **The precise remaining input** to fully close `G1`/`G2` is the joint (t,x)-continuity
  of `∂ₓ` and `∂ₓₓ` of the value field
  `S(t,x) = ∑'ₙ fullSourceCoeff p (realSlice u_star) u₀cos t n · cosineMode n x`
  over the clamp window `Icc (t₀/4) ((t₀+3T)/4) ×ˢ Icc 0 1` — the SPATIAL analogue of
  `SourceJointRegularity`'s value/time-derivative joint continuity, which is not in the
  tree.  With it, `G1`/`G2` would discharge by the same compact-box `bddAbove_image`
  route as `m`/`M` (and the per-`x` series-derivative formula
  `cosineCoeffSeries_grad_hasDerivAt` for the value).

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.ResolverSliceWindowBounds
import ShenWork.Wiener.EWA.ResolverSourceWindowUniformDecay
import ShenWork.Wiener.EWA.SourcePerSliceClose

noncomputable section

namespace ShenWork.EWA

open Set
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.IntervalResolverDirectTimeRegularity (HasResolverDirectSpectralData)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)

variable {T : ℝ}

/-- **`Hv` for the EWA slice with the `C`/`hC`/`hdecay`/`ha0` residual DISCHARGED.**

The window-uniform power-source quadratic-decay package — the single residual carried
by `realSlice_Hv_closed` — is produced internally:

* `m`/`M` (C⁰) from `realSlice_window_uniform_C0` (value-field joint continuity +
  positivity), then
* fed with the carried window cosine representation `bc`/`hbsum`/`hagree` and the
  carried window-uniform SPATIAL-derivative bounds `G1`/`G2` into
  `realSlice_powerSource_window_uniform_decay`,

yielding `C`/`hC`/`hdecay`/`ha0`, which discharge the `realSlice_Hv_closed` residual.

The remaining carried hypotheses are exactly: the value-side standing atoms; the window
cosine representation `bc`/`hbsum`/`hagree`; and the window-uniform first/second
spatial-derivative bounds `G1`/`G2`/`hG1`/`hG2` (the honest new frontier). -/
theorem realSlice_Hv
    (p : CM2Params) (u_star : EWA T 1) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p (realSlice u_star)))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p (realSlice u_star)))
    {u₀E : WA 1} {δ₀ ρ : ℝ} (hδρ : 0 < δ₀ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ₀)
    (hu_ball : u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    (hsumE : ∀ t ∈ Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |fullSourceCoeff p (realSlice u_star) u₀cos t n|))
    (hrealizes : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x)
    -- window cosine representation (consumed by the decay producer):
    (bc : ℝ → ℝ → ℕ → ℝ)
    (hbsum : ∀ t₀, 0 < t₀ → t₀ < T → ∀ σ ∈ Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc t₀ σ n|))
    (hagree : ∀ t₀, 0 < t₀ → t₀ < T → ∀ σ ∈ Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
      Set.EqOn (intervalDomainLift (realSlice u_star σ))
        (fun x => ∑' n, bc t₀ σ n * cosineMode n x) (Icc (0 : ℝ) 1))
    -- window-uniform SPATIAL-derivative bounds `G1`/`G2` (the honest new frontier):
    (G1 G2 : ℝ → ℝ)
    (hG1 : ∀ t₀, 0 < t₀ → t₀ < T → ∀ σ ∈ Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
      ∀ x ∈ Icc (0 : ℝ) 1,
        |deriv (intervalDomainLift (realSlice u_star σ)) x| ≤ G1 t₀)
    (hG2 : ∀ t₀, 0 < t₀ → t₀ < T → ∀ σ ∈ Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
      ∀ x ∈ Icc (0 : ℝ) 1,
        |deriv (deriv (intervalDomainLift (realSlice u_star σ))) x| ≤ G2 t₀) :
    HasResolverDirectSpectralData T
      (mildChemicalConcentration p (realSlice u_star)) p := by
  -- C⁰ window-uniform `m`/`M` from value-field joint continuity + positivity.
  obtain ⟨m, M, hm, hlb, hub⟩ :=
    realSlice_window_uniform_C0 p u_star u₀cos hu0bd hchem hlog hδρ hheat hu_ball hrealizes
  -- assemble the `C`/`hC`/`hdecay`/`ha0` package from the four window-uniform bundles.
  obtain ⟨C, hC, hdecay, ha0⟩ :=
    realSlice_powerSource_window_uniform_decay p u_star bc hbsum hagree m M hm hlb hub
      G1 G2 hG1 hG2
  -- feed it into `realSlice_Hv_closed`, discharging the residual.
  exact realSlice_Hv_closed p u_star u₀cos hu0bd hchem hlog hδρ hheat hu_ball hsumE
    hrealizes C hC hdecay ha0

end ShenWork.EWA

#print axioms ShenWork.EWA.realSlice_Hv
