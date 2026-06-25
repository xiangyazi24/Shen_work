/-
  ShenWork/Wiener/EWA/SourceClassicalRegularityOn.lean

  **Windowed χ₀<0 capstone — `intervalDomainClassicalRegularity` for the
  source-form solution, taking `DuhamelSourceTimeC1On` instead of the global
  `DuhamelSourceTimeC1`.**

  Mirrors `SourceClassicalRegularity.lean`, replacing the four joint-continuity
  call sites with their windowed `_on` counterparts from
  `SourceJointRegularityOn.lean`.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceJointRegularityOn
import ShenWork.Wiener.EWA.SourceClassicalExistence
import ShenWork.Wiener.EWA.SourceClassicalRegularity
import ShenWork.PDE.IntervalCosineSliceRegularity
import ShenWork.PDE.IntervalResolverSpatialC2
import ShenWork.PDE.IntervalResolverGradientBridge
import ShenWork.Paper2.IntervalMildRegularityFrontierAssembly

noncomputable section

namespace ShenWork.EWA

open ShenWork.IntervalDomain
  (intervalDomainPoint intervalDomainLift intervalDomainClassicalRegularity)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalCosineSliceRegularity
open ShenWork.IntervalResolverSpatialC2 (resolverR_summability)
open ShenWork.IntervalResolverGradientBridge (resolverR_apply_eq)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.Paper2 (SourceCoeffQuadraticDecay)
open ShenWork.Paper2.RegularityFrontierAssembly
open ShenWork.IntervalResolverDirectTimeRegularity (HasResolverDirectSpectralData)
open ShenWork.PDE (intervalNeumannResolverR intervalNeumannResolverCoeff)
open Set Filter Topology

variable {T : ℝ}

/-- **Windowed `intervalDomainClassicalRegularity` for the χ₀<0 source-form solution.**

Same statement as `realSlice_classicalRegularity`, but takes
`DuhamelSourceTimeC1On … 0 T` in place of the global `DuhamelSourceTimeC1 …`.
The proof mirrors the global version with the four joint-continuity call sites
replaced by their windowed counterparts from `SourceJointRegularityOn.lean`. -/
theorem realSlice_classicalRegularity_on (p : CM2Params) (u_star : EWA T 1)
    (u₀cos : ℕ → ℝ) {Mu0 : ℝ} (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem_on : DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p (realSlice u_star)) 0 T)
    (hlog_on : DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs p (realSlice u_star)) 0 T)
    -- slab eigenvalue-ℓ¹ summability of the source coefficients:
    (hsumE : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |fullSourceCoeff p (realSlice u_star) u₀cos t n|))
    -- slab `realizes`: the lift equals its `fullSourceCoeff` synthesis on `[0,1]`:
    (hrealizes : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x)
    -- `u`-slice time-derivative bridge (subtype slice = `fullSourceCoeffDot` synthesis):
    (htimeDeriv : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      deriv (fun s : ℝ => realSlice u_star s x) t
        = ∑' n, fullSourceCoeffDot p (realSlice u_star) u₀cos t n * cosineMode n x.1)
    -- `u`-slice time differentiability (transferred slice HasDerivAt):
    (hdiffU : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      DifferentiableAt ℝ (fun s : ℝ => realSlice u_star s x) t)
    -- endpoint nonvanishing of `u` (genuine classical positivity at `{0,1}`):
    (huNE0 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift (realSlice u_star t) 0 ≠ 0)
    (huNE1 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift (realSlice u_star t) 1 ≠ 0)
    -- `v`-side resolver-regularity atoms:
    (hdecay : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      SourceCoeffQuadraticDecay p (realSlice u_star t))
    (Hv : HasResolverDirectSpectralData T (mildChemicalConcentration p (realSlice u_star)) p)
    (Hvpos : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      0 < mildChemicalConcentration p (realSlice u_star) t x) :
    intervalDomainClassicalRegularity T (realSlice u_star)
      (mildChemicalConcentration p (realSlice u_star)) := by
  set u := realSlice u_star with hu
  set v := mildChemicalConcentration p u with hvdef
  -- abbreviations for the two coefficient families
  have hvR : ∀ s, v s = intervalNeumannResolverR p (u s) := fun s => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- (1) spatial C² on Ioo 0 1
  · intro t ht
    refine ⟨intervalDomainCosineSlice_contDiffOn_Ioo (hsumE t ht)
        (realSlice_lift_eqOn_Icc p u_star u₀cos (hrealizes t ht)), ?_⟩
    rw [hvR t]
    exact intervalDomainCosineSlice_contDiffOn_Ioo (resolverR_summability (hdecay t ht))
      (resolver_lift_eqOn_Icc p (u t))
  -- (2) time DifferentiableAt (u,v) + per-x ContinuousOn ∂ₜ (u,v)
  · intro x t ht
    have hvts := timeSlices_v_of_resolverSpectral Hv x
    refine ⟨⟨hdiffU t ht x, hvts.1 t ht⟩, ?_, hvts.2⟩
    -- per-x continuity of `s ↦ deriv (u · x) s` from the windowed joint closed ∂ₜ field
    have hjoint := fullSourceCoeffDot_jointTimeDerivClosed_on p u u₀cos hu0bd hchem_on hlog_on
    -- compose the joint closed field with `s ↦ (s, x.1)` (`x.1 ∈ Icc 0 1`)
    have hmapCont : Continuous (fun s : ℝ => (s, x.1)) := by fun_prop
    have hmap : Set.MapsTo (fun s : ℝ => (s, x.1))
        (Set.Ioo (0 : ℝ) T) (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
      fun s hs => ⟨hs, x.2⟩
    have hcomp := hjoint.comp hmapCont.continuousOn hmap
    have hcont : ContinuousOn
        (fun s : ℝ => ∑' n, fullSourceCoeffDot p u u₀cos s n * cosineMode n x.1)
        (Set.Ioo (0 : ℝ) T) := by
      simpa only [Function.uncurry, Function.comp] using hcomp
    exact ContinuousOn.congr hcont (fun s hs => htimeDeriv s hs x)
  -- (3) joint ∂ₜ continuity on Ioo×Ioo
  · refine ⟨?_, jointTimeDerivInterior_v_of_resolverSpectral Hv⟩
    have hjoint := fullSourceCoeffDot_jointTimeDerivInterior_on p u u₀cos hu0bd hchem_on hlog_on
    refine ContinuousOn.congr hjoint (fun q hq => ?_)
    obtain ⟨ht, hx⟩ := hq
    have hxIcc : q.2 ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
    simp only [Function.uncurry]
    rw [deriv_lift_slice_eq_subtype u hxIcc q.1]
    exact htimeDeriv q.1 ht ⟨q.2, hxIcc⟩
  -- (4) interior Neumann limits
  · intro t ht
    refine ⟨⟨intervalDomainCosineSlice_neumann_limit_left (hsumE t ht)
        (realSlice_lift_eqOn_Icc p u_star u₀cos (hrealizes t ht)),
      intervalDomainCosineSlice_neumann_limit_right (hsumE t ht)
        (realSlice_lift_eqOn_Icc p u_star u₀cos (hrealizes t ht))⟩, ?_⟩
    rw [hvR t]
    exact ⟨intervalDomainCosineSlice_neumann_limit_left (resolverR_summability (hdecay t ht))
        (resolver_lift_eqOn_Icc p (u t)),
      intervalDomainCosineSlice_neumann_limit_right (resolverR_summability (hdecay t ht))
        (resolver_lift_eqOn_Icc p (u t))⟩
  -- (5) closed C² on Icc + endpoint derivs = 0
  · intro t ht
    refine ⟨intervalDomainCosineSlice_conjunct7 (hsumE t ht)
        (realSlice_lift_eqOn_Icc p u_star u₀cos (hrealizes t ht))
        (huNE0 t ht) (huNE1 t ht), ?_⟩
    rw [hvR t]
    have hpos0 : intervalDomainLift (intervalNeumannResolverR p (u t)) 0 ≠ 0 := by
      have h := Hvpos t ht ⟨0, by constructor <;> norm_num⟩
      rw [hvR t] at h
      have : intervalDomainLift (intervalNeumannResolverR p (u t)) 0
          = intervalNeumannResolverR p (u t) ⟨0, by constructor <;> norm_num⟩ := by
        rw [intervalDomainLift, dif_pos (show (0:ℝ) ∈ Set.Icc (0:ℝ) 1 by
          constructor <;> norm_num)]
      rw [this]; exact ne_of_gt h
    have hpos1 : intervalDomainLift (intervalNeumannResolverR p (u t)) 1 ≠ 0 := by
      have h := Hvpos t ht ⟨1, by constructor <;> norm_num⟩
      rw [hvR t] at h
      have : intervalDomainLift (intervalNeumannResolverR p (u t)) 1
          = intervalNeumannResolverR p (u t) ⟨1, by constructor <;> norm_num⟩ := by
        rw [intervalDomainLift, dif_pos (show (1:ℝ) ∈ Set.Icc (0:ℝ) 1 by
          constructor <;> norm_num)]
      rw [this]; exact ne_of_gt h
    exact intervalDomainCosineSlice_conjunct7 (resolverR_summability (hdecay t ht))
      (resolver_lift_eqOn_Icc p (u t)) hpos0 hpos1
  -- (6) joint ∂ₜ continuity on Ioo×Icc
  · refine ⟨?_, jointTimeDerivClosed_v_of_resolverSpectral Hv⟩
    have hjoint := fullSourceCoeffDot_jointTimeDerivClosed_on p u u₀cos hu0bd hchem_on hlog_on
    refine ContinuousOn.congr hjoint (fun q hq => ?_)
    obtain ⟨ht, hx⟩ := hq
    simp only [Function.uncurry]
    rw [deriv_lift_slice_eq_subtype u hx q.1]
    exact htimeDeriv q.1 ht ⟨q.2, hx⟩
  -- (7) joint solution-field continuity on Ioo×Icc
  · refine ⟨?_, jointSolutionClosed_v_of_resolverSpectral Hv⟩
    have hjoint := fullSourceCoeff_jointSolutionClosed_on p u u₀cos hu0bd hchem_on hlog_on
    refine ContinuousOn.congr hjoint (fun q hq => ?_)
    obtain ⟨ht, hx⟩ := hq
    simp only [Function.uncurry]
    exact hrealizes q.1 ht q.2 hx

end ShenWork.EWA
