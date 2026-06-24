/-
  ShenWork/Wiener/EWA/SourcePerSliceClose.lean

  **χ₀<0 — closing the resolver TIME-`C¹` package `Hv` of the maximally-wired
  reduced core from the STANDING inputs.**

  `realSlice_reducedCore_wired` (`SourceReducedCoreWire.lean`) collapses the
  24-hyp χ₀<0 frontier to four named OPEN packages plus a satisfiable standing-input
  class.  This file closes the FIRST of those packages,

      Hv : HasResolverDirectSpectralData T (mildChemicalConcentration p (realSlice u_star)) p,

  by feeding the defeq-wall-cracked producer
  `realSlice_resolverSpectralData_full` (`SourcePowerCoeffDerivComplete.lean`)
  ENTIRELY from inputs that the reduced core already carries — the slab `realizes`
  (`hrealizes`), the eigenvalue-ℓ¹ budget (`hsumE`), the heat-floor positivity atoms
  (`hδρ`/`hheat`/`hu_ball`, which feed `realSlice_pos`), the datum bound (`hu0bd`),
  and the two source TIME-`C¹` packages (`hchem`/`hlog`).  The time-derivative engine
  inputs come from the BANKED quadruple machinery: `realSlice_hasDerivAt_time` for the
  per-slice slice-derivative (the `vdotL` witness), `realSlice_pos` for positivity,
  and the closed-slab joint-continuity fields
  `fullSourceCoeff_jointSolutionClosed` / `fullSourceCoeffDot_jointTimeDerivClosed`
  for the chain-rule integrand `gPow`'s joint continuity.

  The single witness chosen throughout is

      vdotL s x := ∑' n, fullSourceCoeffDot p (realSlice u_star) u₀cos s n · cosineMode n x,

  which IS the spatial form of `realSlice_hasDerivAt_time`'s derivative, and

      bc t₀ σ n := fullSourceCoeff p (realSlice u_star) u₀cos σ n,

  so that `hagree` is exactly the slab `realizes` and `hbsum` is exactly `hsumE`.

  RESULT: `realSlice_Hv_closed` produces `Hv` from the standing inputs alone — the
  first of the four open packages is fully discharged, NOT carried.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourcePowerCoeffDerivComplete
import ShenWork.Wiener.EWA.SourceResolverSpectralDischarge
import ShenWork.Wiener.EWA.SourceTimeDerivDischarge
import ShenWork.Wiener.EWA.SourceJointRegularity
import ShenWork.Wiener.EWA.SourcePositivity
import ShenWork.Wiener.EWA.SourceRealizesRecords

noncomputable section

namespace ShenWork.EWA

open Set Filter Topology
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.IntervalResolverDirectTimeRegularity (HasResolverDirectSpectralData)
open ShenWork.PDE (intervalNeumannResolverSourceCoeff)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1 cosineCoeffSeries_contDiff_two)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)

variable {T : ℝ}

/-! ### The `vdotL` witness and its building blocks. -/

/-- The chosen `vdotL` witness: the spatial form of the per-slice time-derivative
delivered by `realSlice_hasDerivAt_time`. -/
private def vdotLslice (p : CM2Params) (u_star : EWA T 1) (u₀cos : ℕ → ℝ)
    (s x : ℝ) : ℝ :=
  ∑' n, fullSourceCoeffDot p (realSlice u_star) u₀cos s n * cosineMode n x

/-- The lift of `realSlice u_star s` agrees on the closed slab with the χ₀<0 value
field `∑' fullSourceCoeff · cosineMode`. -/
private theorem lift_eq_valueField
    (p : CM2Params) (u_star : EWA T 1) (u₀cos : ℕ → ℝ)
    (hrealizes : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) T) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    intervalDomainLift (realSlice u_star s) x
      = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos s n * cosineMode n x :=
  hrealizes s hs x hx

/-! ### Joint continuity of the chain-rule integrand `gPow` on a closed window.

`gPow p (realSlice u_star) (vdotLslice …) σ x
   = ν·γ·(lift (realSlice u_star σ) x)^{γ−1} · vdotL σ x`.
On a closed time-window `Icc a b ⊆ Ioo 0 T` times `Icc 0 1`:
* the base `lift` is jointly continuous (it equals the closed-slab value field,
  `fullSourceCoeff_jointSolutionClosed`), and the rpow exponent `γ−1` is handled by
  strict positivity from `realSlice_pos`;
* the time-derivative factor `vdotL` is jointly continuous
  (`fullSourceCoeffDot_jointTimeDerivClosed`). -/
private theorem gPow_continuousOn_window
    (p : CM2Params) (u_star : EWA T 1) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p (realSlice u_star)))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p (realSlice u_star)))
    {u₀E : WA 1} {δ ρ : ℝ} (hδρ : 0 < δ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ)
    (hu_ball : u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    (hrealizes : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x)
    {a b : ℝ} (hab : Icc a b ⊆ Ioo (0 : ℝ) T) :
    ContinuousOn
      (Function.uncurry (gPow p (realSlice u_star) (vdotLslice p u_star u₀cos)))
      (Icc a b ×ˢ Icc (0 : ℝ) 1) := by
  -- the box is contained in the closed slab.
  have hbox : Icc a b ×ˢ Icc (0 : ℝ) 1 ⊆ Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1 :=
    prod_mono hab (subset_refl _)
  -- value field on the closed box (congr to the lift).
  have hVal : ContinuousOn
      (Function.uncurry (fun (s : ℝ) (x : ℝ) => intervalDomainLift (realSlice u_star s) x))
      (Icc a b ×ˢ Icc (0 : ℝ) 1) := by
    refine ((fullSourceCoeff_jointSolutionClosed p (realSlice u_star) u₀cos hu0bd hchem hlog
      (T := T)).mono hbox).congr ?_
    intro q hq
    obtain ⟨hqs, hqx⟩ := hq
    have hs : q.1 ∈ Ioo (0 : ℝ) T := hab hqs
    simpa [Function.uncurry] using
      lift_eq_valueField p u_star u₀cos hrealizes hs hqx
  -- rpow base `lift`, exponent `γ−1`, via strict positivity from `realSlice_pos`.
  have hpow : ContinuousOn
      (Function.uncurry (fun (s : ℝ) (x : ℝ) =>
        (intervalDomainLift (realSlice u_star s) x) ^ (p.γ - 1)))
      (Icc a b ×ˢ Icc (0 : ℝ) 1) := by
    refine ContinuousOn.rpow_const hVal ?_
    intro q hq
    left
    obtain ⟨hqs, hqx⟩ := hq
    have hs : q.1 ∈ Ioo (0 : ℝ) T := hab hqs
    have hpos : 0 < intervalDomainLift (realSlice u_star q.1) q.2 := by
      rw [intervalDomainLift, dif_pos hqx]
      exact realSlice_pos hδρ hheat hu_ball ⟨hs.1.le, hs.2.le⟩ ⟨q.2, hqx⟩
    exact ne_of_gt hpos
  -- time-deriv factor `vdotL` on the closed box.
  have hDot : ContinuousOn
      (Function.uncurry (fun (s : ℝ) (x : ℝ) => vdotLslice p u_star u₀cos s x))
      (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    (fullSourceCoeffDot_jointTimeDerivClosed p (realSlice u_star) u₀cos hu0bd hchem hlog
      (T := T)).mono hbox
  -- assemble: ν·γ · pow · vdotL.
  have : ContinuousOn
      (Function.uncurry (fun (s : ℝ) (x : ℝ) =>
        p.ν * p.γ * (intervalDomainLift (realSlice u_star s) x) ^ (p.γ - 1)
          * vdotLslice p u_star u₀cos s x))
      (Icc a b ×ˢ Icc (0 : ℝ) 1) := by
    have h1 : ContinuousOn
        (Function.uncurry (fun (s : ℝ) (x : ℝ) =>
          p.ν * p.γ * (intervalDomainLift (realSlice u_star s) x) ^ (p.γ - 1)))
        (Icc a b ×ˢ Icc (0 : ℝ) 1) := continuousOn_const.mul hpow
    exact h1.mul hDot
  -- unfold `gPow` (NOT irreducible in this file).
  simpa only [gPow, Function.uncurry] using this

/-! ### Spatial continuity of the power source `ν·lift^γ` on `Icc 0 1`. -/

/-- For an interior time `s`, the power source `x ↦ ν·(lift (realSlice u_star s) x)^γ`
is continuous on `Icc 0 1`: the lift equals the globally-`C²` value field there, and
the rpow exponent `γ ≥ 0` is handled by `0 ≤ γ`. -/
private theorem powerSource_continuousOn_Icc
    (p : CM2Params) (u_star : EWA T 1) (u₀cos : ℕ → ℝ)
    (hsumE : ∀ t ∈ Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |fullSourceCoeff p (realSlice u_star) u₀cos t n|))
    (hrealizes : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) T) :
    ContinuousOn (fun x => p.ν * (intervalDomainLift (realSlice u_star s) x) ^ p.γ)
      (Icc (0 : ℝ) 1) := by
  have hcont : ContinuousOn (intervalDomainLift (realSlice u_star s)) (Icc (0 : ℝ) 1) :=
    ((cosineCoeffSeries_contDiff_two (hsumE s hs)).continuous.continuousOn).congr
      (fun x hx => hrealizes s hs x hx)
  exact continuousOn_const.mul (hcont.rpow_const (fun x _ => Or.inr p.hγ.le))

/-! ### The K1(i) engine inputs, per interior σ, fully assembled.

`hK1` packages, for each interior σ, the four engine fields
(`hf_cont`/`hslice`/`hpos`/`hslabcont`) of `realSlice_powerCoeff_hasDerivAt` /
`realSlice_resolverSpectralData_full`.  The `vdotL` witness is `vdotLslice`:
`HasDerivAt (fun r => lift (realSlice u_star r) x) (vdotLslice … s x) s` is exactly
`realSlice_hasDerivAt_time` read at the interior subtype point `⟨x,_⟩`. -/
private theorem hK1_assembled
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
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x) :
    ∀ σ ∈ Ioo (0 : ℝ) T, ∃ δ > 0,
      (∀ᶠ s in 𝓝 σ,
          ContinuousOn
            (fun x => p.ν * (intervalDomainLift (realSlice u_star s) x) ^ p.γ)
            (Icc (0 : ℝ) 1))
        ∧ (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball σ δ,
            HasDerivAt (fun r => intervalDomainLift (realSlice u_star r) x)
              (vdotLslice p u_star u₀cos s x) s)
        ∧ (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball σ δ,
            0 < intervalDomainLift (realSlice u_star s) x)
        ∧ ContinuousOn (Function.uncurry (gPow p (realSlice u_star)
            (vdotLslice p u_star u₀cos)))
            (Icc (σ - δ) (σ + δ) ×ˢ Icc (0 : ℝ) 1) := by
  intro σ hσ
  -- choose δ so that the closed window `[σ-δ, σ+δ] ⊆ Ioo 0 T`.
  obtain ⟨δ, hδpos, hδsub⟩ : ∃ δ > 0, Icc (σ - δ) (σ + δ) ⊆ Ioo (0 : ℝ) T := by
    have hσ0 : 0 < σ := hσ.1
    have hσT : σ < T := hσ.2
    refine ⟨min (σ / 2) ((T - σ) / 2), lt_min (by linarith) (by linarith), ?_⟩
    intro y hy
    have h1 : σ - min (σ / 2) ((T - σ) / 2) ≤ y := hy.1
    have h2 : y ≤ σ + min (σ / 2) ((T - σ) / 2) := hy.2
    have hmin1 : min (σ / 2) ((T - σ) / 2) ≤ σ / 2 := min_le_left _ _
    have hmin2 : min (σ / 2) ((T - σ) / 2) ≤ (T - σ) / 2 := min_le_right _ _
    exact ⟨by linarith, by linarith⟩
  refine ⟨δ, hδpos, ?_, ?_, ?_, ?_⟩
  · -- eventual spatial continuity of `ν·lift^γ`: holds for all `s ∈ Ioo 0 T`.
    filter_upwards [isOpen_Ioo.mem_nhds hσ] with s hs
    exact powerSource_continuousOn_Icc p u_star u₀cos hsumE hrealizes hs
  · -- the per-point time-derivative of the lift, from `realSlice_hasDerivAt_time`.
    intro x hx s hs
    have hdist : |s - σ| < δ := by
      have := Metric.mem_ball.1 hs; rwa [Real.dist_eq] at this
    have hsmem : s ∈ Icc (σ - δ) (σ + δ) := by
      have := abs_lt.1 hdist; exact ⟨by linarith [this.1], by linarith [this.2]⟩
    have hsIoo : s ∈ Ioo (0 : ℝ) T := hδsub hsmem
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
    have hd := realSlice_hasDerivAt_time p (realSlice u_star) u₀cos hu0bd hchem hlog
      hrealizes hsIoo ⟨x, hxIcc⟩
    -- rewrite `(fun s => realSlice u_star s ⟨x,_⟩)` as `lift … x` and the deriv as `vdotL`.
    have hfun : (fun r => intervalDomainLift (realSlice u_star r) x)
        = (fun r => realSlice u_star r ⟨x, hxIcc⟩) := by
      funext r; rw [intervalDomainLift, dif_pos hxIcc]
    rw [hfun]
    simpa only [vdotLslice] using hd
  · -- strict positivity from `realSlice_pos`.
    intro x hx s hs
    have hdist : |s - σ| < δ := by
      have := Metric.mem_ball.1 hs; rwa [Real.dist_eq] at this
    have hsmem : s ∈ Icc (σ - δ) (σ + δ) := by
      have := abs_lt.1 hdist; exact ⟨by linarith [this.1], by linarith [this.2]⟩
    have hsIoo : s ∈ Ioo (0 : ℝ) T := hδsub hsmem
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
    rw [intervalDomainLift, dif_pos hxIcc]
    exact realSlice_pos hδρ hheat hu_ball ⟨hsIoo.1.le, hsIoo.2.le⟩ ⟨x, hxIcc⟩
  · -- joint continuity of the chain-rule integrand on the closed window.
    exact gPow_continuousOn_window p u_star u₀cos hu0bd hchem hlog hδρ hheat hu_ball
      hrealizes hδsub

/-! ### `Hv` closed from the standing inputs + the window-uniform decay package.

`realSlice_Hv_closed` feeds `realSlice_resolverSpectralData_full`
(`SourcePowerCoeffDerivComplete.lean`) entirely from the STANDING inputs of
`realSlice_reducedCore_wired`:

* the spectral-rep witness `bc t₀ σ n := fullSourceCoeff … σ n`, so that
  `hbsum` is exactly `hsumE` and `hagree` is exactly the slab `realizes`;
* `hpos` from `realSlice_pos`;
* the K1 time-derivative engine quadruple (`hK1` + `hslabcont`) DISCHARGED by
  `hK1_assembled` / `gPow_continuousOn_window` (the defeq-wall-cracked time-`C¹`,
  built from `realSlice_hasDerivAt_time` + `realSlice_pos` + the closed-slab joint
  continuity `fullSourceCoeff_jointSolutionClosed` /
  `fullSourceCoeffDot_jointTimeDerivClosed`).

The ONLY carried residual is the **window-uniform power-source quadratic-decay
package** `C`/`hC`/`hdecay`/`ha0`: a single per-`t₀` constant `C t₀` dominating the
source cosine coefficients `cosineCoeffs (ν·lift^γ)` uniformly over the clamp window
`Icc (t₀/4) ((t₀+3T)/4)`.  Pointwise-in-`σ` this is `realSlice_resolverDecay`'s
`SourceCoeffQuadraticDecay`, but its constant is `σ`-dependent (the slice's C²-norm);
no banked producer supplies a window-uniform `C t₀`, so it is carried as the precise
remaining standing input.  Everything else is closed. -/
theorem realSlice_Hv_closed
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
    -- the window-uniform power-source quadratic-decay package (carried residual):
    (C : ℝ → ℝ) (hC : ∀ t₀, 0 ≤ C t₀)
    (hdecay : ∀ t₀, 0 < t₀ → t₀ < T →
      ∀ σ ∈ Icc (t₀ / 4) ((t₀ + 3 * T) / 4), ∀ k : ℕ, 1 ≤ k →
        |cosineCoeffs (fun x => p.ν * intervalDomainLift (realSlice u_star σ) x ^ p.γ) k|
          ≤ C t₀ / ((k : ℝ) * Real.pi) ^ 2)
    (ha0 : ∀ t₀, 0 < t₀ → t₀ < T → ∀ σ ∈ Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
      |cosineCoeffs (fun x => p.ν * intervalDomainLift (realSlice u_star σ) x ^ p.γ) 0|
        ≤ C t₀) :
    HasResolverDirectSpectralData T
      (mildChemicalConcentration p (realSlice u_star)) p := by
  -- spectral-rep witness = the χ₀<0 value field; `hbsum`/`hagree` then are
  -- exactly `hsumE` / the slab `realizes`.
  refine realSlice_resolverSpectralData_full p u_star (vdotLslice p u_star u₀cos)
    (fun _ σ n => fullSourceCoeff p (realSlice u_star) u₀cos σ n)
    ?_ ?_ ?_ C hC hdecay ha0 ?_ ?_
  · -- hbsum: from `hsumE` (window ⊆ Ioo 0 T).
    intro t₀ ht₀ ht₀T σ hσ
    have hσIoo : σ ∈ Ioo (0 : ℝ) T :=
      ⟨lt_of_lt_of_le (by linarith) hσ.1, lt_of_le_of_lt hσ.2 (by linarith)⟩
    exact hsumE σ hσIoo
  · -- hagree: the slab `realizes` as an `EqOn`.
    intro t₀ ht₀ ht₀T σ hσ x hx
    have hσIoo : σ ∈ Ioo (0 : ℝ) T :=
      ⟨lt_of_lt_of_le (by linarith) hσ.1, lt_of_le_of_lt hσ.2 (by linarith)⟩
    exact hrealizes σ hσIoo x hx
  · -- hpos: from `realSlice_pos`.
    intro t₀ ht₀ ht₀T σ hσ x hx
    have hσIoo : σ ∈ Ioo (0 : ℝ) T :=
      ⟨lt_of_lt_of_le (by linarith) hσ.1, lt_of_le_of_lt hσ.2 (by linarith)⟩
    rw [intervalDomainLift, dif_pos hx]
    exact realSlice_pos hδρ hheat hu_ball ⟨hσIoo.1.le, hσIoo.2.le⟩ ⟨x, hx⟩
  · -- hK1: the K1(i) engine quadruple, discharged.
    exact hK1_assembled p u_star u₀cos hu0bd hchem hlog hδρ hheat hu_ball hsumE hrealizes
  · -- hslabcont: joint continuity of `gPow` on each clamp window (⊆ Ioo 0 T).
    intro t₀ ht₀ ht₀T
    have hsub : Icc (t₀ / 4) ((t₀ + 3 * T) / 4) ⊆ Ioo (0 : ℝ) T := by
      intro y hy
      exact ⟨lt_of_lt_of_le (by linarith) hy.1, lt_of_le_of_lt hy.2 (by linarith)⟩
    exact gPow_continuousOn_window p u_star u₀cos hu0bd hchem hlog hδρ hheat hu_ball
      hrealizes hsub

/-! ### Package 4 (partial): subtype continuity of the realized logistic source `wLog`.

`h_src_cont_log : ∀ τ, Continuous (wLog p u_star τ.1)` is the SPATIAL (subtype)
continuity of the realized logistic source slice.  It closes from the realized
slice's spatial regularity: the lift is `C²` on `Icc 0 1` (the value field, by
`cosineCoeffSeries_contDiff_two` + `hrealizes`), hence the slice is continuous on the
compact subtype `intervalDomainPoint`; the logistic formula `u·(a − b·u^α)` is then
continuous via `Continuous.rpow_const` with `0 ≤ α` (the same spine as the banked
`logisticSource_subtypeCont`). -/

/-- The realized slice `realSlice u_star s` is continuous on the subtype
`intervalDomainPoint`, for interior `s`, from its lift's continuity on `Icc 0 1`. -/
private theorem realSlice_subtype_continuous
    (p : CM2Params) (u_star : EWA T 1) (u₀cos : ℕ → ℝ)
    (hsumE : ∀ t ∈ Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |fullSourceCoeff p (realSlice u_star) u₀cos t n|))
    (hrealizes : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) T) :
    Continuous (realSlice u_star s) := by
  -- lift continuous on Icc (value field is globally C²).
  have hcont : ContinuousOn (intervalDomainLift (realSlice u_star s)) (Icc (0 : ℝ) 1) :=
    ((cosineCoeffSeries_contDiff_two (hsumE s hs)).continuous.continuousOn).congr
      (fun x hx => hrealizes s hs x hx)
  -- transport to the subtype via `restrict (lift) = slice`.
  rw [continuousOn_iff_continuous_restrict] at hcont
  have heq : (Icc (0 : ℝ) 1).restrict (intervalDomainLift (realSlice u_star s))
      = realSlice u_star s := by
    funext ⟨y, hy⟩
    simp only [Set.restrict_apply, intervalDomainLift]
    rw [dif_pos hy]; exact congr_arg (realSlice u_star s) (Subtype.ext rfl)
  rwa [heq] at hcont

/-- **`h_src_cont_log` DISCHARGED (per interior time).**  The realized logistic source
slice `wLog p u_star s = u·(a − b·u^α)` of the realized slice is continuous on the
subtype, for every interior `s` and `0 ≤ p.α`. -/
theorem realSlice_wLog_continuous
    (p : CM2Params) (u_star : EWA T 1) (u₀cos : ℕ → ℝ) (hαnn : 0 ≤ p.α)
    (hsumE : ∀ t ∈ Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |fullSourceCoeff p (realSlice u_star) u₀cos t n|))
    (hrealizes : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) T) :
    Continuous (wLog p u_star s) := by
  have hw : Continuous (realSlice u_star s) :=
    realSlice_subtype_continuous p u_star u₀cos hsumE hrealizes hs
  have hrpow : Continuous (fun x : intervalDomainPoint => (realSlice u_star s x) ^ p.α) :=
    hw.rpow_const (fun _ => Or.inr hαnn)
  -- `wLog p u_star s = intervalLogisticSource p (realSlice u_star s) = u·(a − b·u^α)`.
  change Continuous (intervalLogisticSource p (realSlice u_star s))
  unfold intervalLogisticSource
  exact hw.mul (continuous_const.sub (continuous_const.mul hrpow))

end ShenWork.EWA

#print axioms ShenWork.EWA.realSlice_Hv_closed
#print axioms ShenWork.EWA.realSlice_wLog_continuous
