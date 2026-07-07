import ShenWork.Paper2.IntervalGradientSourceBridgePhysicalRep
import ShenWork.Paper2.IntervalGradientSourceBridgeSourceCertificates
import ShenWork.Paper2.IntervalMildToClassical
import ShenWork.Paper2.IntervalMildSourceDecay

open MeasureTheory intervalIntegral
open scoped Topology

noncomputable section

namespace ShenWork

open ShenWork.IntervalDomain
open ShenWork.IntervalCoupledRegularityBootstrap

/-- Regularity-only version of `solution_chemotaxisFlux_hasDerivAt`.

The proof is the same pointwise flux differentiability calculation, but its
inputs are only `intervalDomainClassicalRegularity` and nonnegativity of the
chemical component. It does not consume the parabolic PDE field packaged in
`IsPaper2ClassicalSolution`. -/
theorem chemotaxisFlux_hasDerivAt_of_classicalRegularity_nonneg
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hreg : intervalDomainClassicalRegularity T u v)
    (hv_nonneg : ∀ t x, 0 < t → t < T → 0 ≤ v t x)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    {y : intervalDomainPoint} (hy_int : y.1 ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun y' : ℝ =>
        intervalDomainLift (u τ) y' * deriv (intervalDomainLift (v τ)) y'
          / (1 + intervalDomainLift (v τ) y') ^ p.β)
      (intervalDomainChemotaxisDiv p (u τ) (v τ) y) y.1 := by
  classical
  set y₀ : ℝ := y.1 with hy₀
  have hy_Icc : y₀ ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy_int
  have hC2u : ContDiffOn ℝ 2 (intervalDomainLift (u τ)) (Set.Ioo (0:ℝ) 1) :=
    (hreg.1 τ hτ).1
  have hC2v : ContDiffOn ℝ 2 (intervalDomainLift (v τ)) (Set.Ioo (0:ℝ) 1) :=
    (hreg.1 τ hτ).2
  have hU_diff : DifferentiableAt ℝ (intervalDomainLift (u τ)) y₀ :=
    (hC2u.differentiableOn (by norm_num)).differentiableAt
      (IsOpen.mem_nhds isOpen_Ioo hy_int)
  have hV_diff : DifferentiableAt ℝ (intervalDomainLift (v τ)) y₀ :=
    (hC2v.differentiableOn (by norm_num)).differentiableAt
      (IsOpen.mem_nhds isOpen_Ioo hy_int)
  have hDV_C1 : ContDiffOn ℝ 1 (deriv (intervalDomainLift (v τ))) (Set.Ioo (0:ℝ) 1) :=
    hC2v.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hW_diff : DifferentiableAt ℝ (deriv (intervalDomainLift (v τ))) y₀ :=
    (hDV_C1.differentiableOn (by norm_num)).differentiableAt
      (IsOpen.mem_nhds isOpen_Ioo hy_int)
  have hv_nn : 0 ≤ intervalDomainLift (v τ) y₀ := by
    have hv_point : 0 ≤ v τ ⟨y₀, hy_Icc⟩ :=
      hv_nonneg τ ⟨y₀, hy_Icc⟩ hτ.1 hτ.2
    simpa [intervalDomainLift, hy_Icc] using hv_point
  have hV₀_pos : 0 < 1 + intervalDomainLift (v τ) y₀ := by linarith
  have hOnePlusV_diff :
      DifferentiableAt ℝ (fun z : ℝ => 1 + intervalDomainLift (v τ) z) y₀ :=
    (differentiableAt_const _).add hV_diff
  have hpow_at : HasDerivAt (fun x : ℝ => x ^ p.β)
      (p.β * (1 + intervalDomainLift (v τ) y₀) ^ (p.β - 1))
      (1 + intervalDomainLift (v τ) y₀) :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hV₀_pos))
  have hD_diff :
      DifferentiableAt ℝ
        (fun z : ℝ => (1 + intervalDomainLift (v τ) z) ^ p.β) y₀ := by
    have hcomp := (hpow_at.differentiableAt).comp y₀ hOnePlusV_diff
    simpa [Function.comp] using hcomp
  have hN_diff :
      DifferentiableAt ℝ
        (fun z : ℝ =>
          intervalDomainLift (u τ) z * deriv (intervalDomainLift (v τ)) z) y₀ :=
    hU_diff.mul hW_diff
  have hD_ne :
      (fun z : ℝ => (1 + intervalDomainLift (v τ) z) ^ p.β) y₀ ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hV₀_pos _)
  have hflux_diff :
      DifferentiableAt ℝ
        (fun z : ℝ =>
          intervalDomainLift (u τ) z * deriv (intervalDomainLift (v τ)) z
            / (1 + intervalDomainLift (v τ) z) ^ p.β) y₀ :=
    hN_diff.div hD_diff hD_ne
  have hderiv_eq :
      deriv
        (fun z : ℝ =>
          intervalDomainLift (u τ) z * deriv (intervalDomainLift (v τ)) z
            / (1 + intervalDomainLift (v τ) z) ^ p.β) y₀
        = intervalDomainChemotaxisDiv p (u τ) (v τ) y := by
    unfold intervalDomainChemotaxisDiv
    rfl
  have h := hflux_diff.hasDerivAt
  rw [hderiv_eq] at h
  exact h

end ShenWork

namespace ShenWork.Paper2.IntervalGradientSourceBridgeOpen

open Set
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalFullKernelSpectralClean
open ShenWork.IntervalSemigroupNeumann
open ShenWork.IntervalDomain
  (intervalMeasure intervalDomain intervalDomainPoint intervalDomainLift
    intervalDomainChemotaxisDiv intervalDomainClassicalRegularity)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceLift coupledLogisticSourceCoeffs
    coupledLogisticSourceLift resolver_lift_deriv_eq_resolverGradReal_of_sourceDecay)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration mildChemical_nonneg)
open ShenWork.IntervalMildSourceDecay
  (sourceCoeffQuadraticDecay_of_mildSolution_of_closedC2_neumann)

/-- Regularity-only producer for the open chemotaxis-flux derivative input of
the gradient-source bridge.

Compared with
`chemFluxLifted_hasDerivWithinAt_coupledChemDivSourceLift_open_of_classical`,
this uses only the non-PDE classical-regularity package for `(D.u,
resolver(D.u))` plus the positivity/closed-C² data already carried by
`GradientMildSolutionData`. -/
theorem chemFluxLifted_hasDerivWithinAt_coupledChemDivSourceLift_open_of_mildRegularity
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hreg : intervalDomainClassicalRegularity D.T D.u
      (coupledChemicalConcentration p D.u))
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) D.T) :
    ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (chemFluxLifted p (D.u s))
        (coupledChemDivSourceLift p D.u s y) (Set.Ioi y) y := by
  intro y hy
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
  let Y : intervalDomainPoint := ⟨y, hyIcc⟩
  have hv_nonneg :
      ∀ t x, 0 < t → t < D.T →
        0 ≤ coupledChemicalConcentration p D.u t x := by
    intro t x ht htT
    simpa [coupledChemicalConcentration, mildChemicalConcentration] using
      mildChemical_nonneg (p := p) (T := D.T)
        (u := D.u) D.hnonneg D.hcont ht htT.le x
  have hflux :
      HasDerivAt
        (fun y' : ℝ =>
          intervalDomainLift (D.u s) y' *
            deriv (intervalDomainLift (coupledChemicalConcentration p D.u s)) y' /
            (1 + intervalDomainLift (coupledChemicalConcentration p D.u s) y') ^ p.β)
        (intervalDomainChemotaxisDiv p (D.u s)
          (coupledChemicalConcentration p D.u s) Y) y :=
    ShenWork.chemotaxisFlux_hasDerivAt_of_classicalRegularity_nonneg
      (p := p) (T := D.T) (u := D.u)
      (v := coupledChemicalConcentration p D.u) hreg hv_nonneg hs (y := Y) hy
  have hC2 : ContDiffOn ℝ 2 (intervalDomainLift (D.u s)) (Set.Icc (0 : ℝ) 1) :=
    (hreg.2.2.2.2.1 s hs).1.1
  have hN0 : Filter.Tendsto (deriv (intervalDomainLift (D.u s)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    (hreg.2.2.2.1 s hs).1.1
  have hN1 : Filter.Tendsto (deriv (intervalDomainLift (D.u s)))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) :=
    (hreg.2.2.2.1 s hs).1.2
  have hdecay : SourceCoeffQuadraticDecay p (D.u s) :=
    sourceCoeffQuadraticDecay_of_mildSolution_of_closedC2_neumann
      p D hs.1 hs.2.le hC2 hN0 hN1
  have heq_fun :
      chemFluxLifted p (D.u s) =ᶠ[𝓝 y]
        (fun y' : ℝ =>
          intervalDomainLift (D.u s) y' *
            deriv (intervalDomainLift (coupledChemicalConcentration p D.u s)) y' /
            (1 + intervalDomainLift (coupledChemicalConcentration p D.u s) y') ^ p.β) := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioo hy] with z hz
    have hgradR :
        deriv (intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p (D.u s))) z =
          resolverGradReal p (D.u s) z := by
      simpa [coupledChemicalConcentration] using
        resolver_lift_deriv_eq_resolverGradReal_of_sourceDecay
          (p := p) (u := D.u s) hdecay hz
    unfold chemFluxLifted
    simp [coupledChemicalConcentration]
    rw [hgradR]
  have hvalue :
      intervalDomainChemotaxisDiv p (D.u s) (coupledChemicalConcentration p D.u s) Y =
        coupledChemDivSourceLift p D.u s y := by
    change intervalDomainChemotaxisDiv p (D.u s) (coupledChemicalConcentration p D.u s) Y =
      intervalDomainLift
        (fun x => intervalDomainChemotaxisDiv p (D.u s)
          (coupledChemicalConcentration p D.u s) x) y
    simp [intervalDomainLift, hyIcc, Y]
  have hchem :
      HasDerivAt (chemFluxLifted p (D.u s))
        (coupledChemDivSourceLift p D.u s y) y := by
    have h := hflux.congr_of_eventuallyEq heq_fun
    rwa [hvalue] at h
  exact hchem.hasDerivWithinAt

/-- Gradient-mild slice bridge from non-PDE classical regularity and an
endpoint-insensitive chem-div continuous representative.

This is the hreg-based replacement for the classical slice theorem on the
source-bridge route: all easy source/ball inputs are discharged from
`GradientMildSolutionData`, and the derivative input is discharged by the
regularity-only flux lemma above. -/
theorem gradient_source_bridge_slice_open_of_gradientMildRegularity_representative
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hreg : intervalDomainClassicalRegularity D.T D.u
      (coupledChemicalConcentration p D.u))
    {r x s : ℝ} (hr : 0 < r) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s ∈ Set.Ioo (0 : ℝ) D.T)
    {Gdiv : ℝ → ℝ}
    (hdiv_rep_cont : ContinuousOn Gdiv (Set.Icc (0 : ℝ) 1))
    (hdiv_rep_eq :
      Set.EqOn (coupledChemDivSourceLift p D.u s) Gdiv (Set.Ioo (0 : ℝ) 1)) :
    (-p.χ₀) *
        deriv (fun z : ℝ =>
          intervalFullSemigroupOperator r (chemFluxLifted p (D.u s)) z) x
      + intervalFullSemigroupOperator r (logisticLifted p (D.u s)) x
      =
    (-p.χ₀) *
        unitIntervalSineHeatValue r
          (sineCoeffs (coupledChemDivSourceLift p D.u s)) x
      + unitIntervalCosineHeatValue r
          (coupledLogisticSourceCoeffs p D.u s) x := by
  have hchem_cont_global :
      Continuous (chemFluxLifted p (D.u s)) :=
    ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_continuous_of_continuous
      p (D.hcont s hs.1 hs.2.le) (D.hnonneg s hs.1 hs.2.le)
  have hchem_meas :
      AEStronglyMeasurable (chemFluxLifted p (D.u s)) (intervalMeasure 1) :=
    hchem_cont_global.aestronglyMeasurable
  have hchem_cont :
      ContinuousOn (chemFluxLifted p (D.u s)) (Set.Icc (0 : ℝ) 1) :=
    hchem_cont_global.continuousOn
  obtain ⟨Cchem, _hCchem_nonneg, hchem_bound⟩ :=
    ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_bounded_of_continuous
      p (D.hbound s hs.1 hs.2.le) D.hM.le
      (D.hcont s hs.1 hs.2.le) (D.hnonneg s hs.1 hs.2.le)
  have hQderiv : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (chemFluxLifted p (D.u s))
        (coupledChemDivSourceLift p D.u s y) (Set.Ioi y) y :=
    chemFluxLifted_hasDerivWithinAt_coupledChemDivSourceLift_open_of_mildRegularity
      D hreg hs
  have hlog_cont : Continuous (intervalLogisticSource p (D.u s)) :=
    intervalLogisticSource_continuous_of_continuous (D.hcont s hs.1 hs.2.le)
  have hlog_bound :
      ∀ n : ℕ,
        |cosineCoeffs (logisticLifted p (D.u s)) n| ≤
          2 * (D.M * (p.a + p.b * D.M ^ p.α)) :=
    logisticLifted_cosineCoeffs_bound_of_ball p D.hM
      (D.hcont s hs.1 hs.2.le) (D.hbound s hs.1 hs.2.le)
  exact gradient_source_bridge_slice_open_representative_of_continuousOn
    (p := p) (u := D.u) (r := r) (x := x) (s := s) hr hx
    hchem_meas hchem_cont (Cchem := Cchem) hchem_bound hQderiv
    (Gdiv := Gdiv) hdiv_rep_cont hdiv_rep_eq hlog_cont
    (Mlog := 2 * (D.M * (p.a + p.b * D.M ^ p.α))) hlog_bound

end ShenWork.Paper2.IntervalGradientSourceBridgeOpen

namespace ShenWork.IntervalMildToLocalExistence

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainPoint intervalDomainClassicalRegularity)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceLift coupledLogisticSourceCoeffs)
open ShenWork.Paper2.IntervalGradientSourceBridgeOpen

/-- A.e. in time, the regularity-only per-slice gradient-source bridge rewrites
the weak gradient/logistic integrand as the mixed sine/cosine source integrand.

The full classical-solution package is replaced by non-PDE classical regularity
plus an endpoint-insensitive continuous representative for the chem-div source
at each interior time. -/
theorem gradientMildSourceIntegrand_eq_mixedSpectralSource_ae_of_gradientMildRegularity_representative
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hreg : intervalDomainClassicalRegularity D.T D.u
      (coupledChemicalConcentration p D.u))
    (hrep : ∀ s, s ∈ Set.Ioo (0 : ℝ) D.T →
      ∃ Gdiv : ℝ → ℝ,
        ContinuousOn Gdiv (Set.Icc (0 : ℝ) 1) ∧
        Set.EqOn (coupledChemDivSourceLift p D.u s) Gdiv (Set.Ioo (0 : ℝ) 1))
    {t x : ℝ} (ht0 : 0 < t) (htT : t < D.T) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    (fun s : ℝ =>
      (-p.χ₀) *
          deriv (fun z : ℝ =>
            intervalFullSemigroupOperator (t - s) (chemFluxLifted p (D.u s)) z) x
        + intervalFullSemigroupOperator (t - s) (logisticLifted p (D.u s)) x)
      =ᵐ[volume.restrict (Set.uIoc (0 : ℝ) t)]
    (fun s : ℝ =>
      (-p.χ₀) *
          unitIntervalSineHeatValue (t - s)
            (sineCoeffs (coupledChemDivSourceLift p D.u s)) x
        + unitIntervalCosineHeatValue (t - s)
            (coupledLogisticSourceCoeffs p D.u s) x) := by
  rw [Set.uIoc_of_le ht0.le]
  rw [← Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := t) (μ := volume))]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with s hsIoo_t
  have hr : 0 < t - s := sub_pos.mpr hsIoo_t.2
  have hsT : s ∈ Set.Ioo (0 : ℝ) D.T :=
    ⟨hsIoo_t.1, lt_trans hsIoo_t.2 htT⟩
  obtain ⟨Gdiv, hGcont, hGeq⟩ := hrep s hsT
  exact
    gradient_source_bridge_slice_open_of_gradientMildRegularity_representative
      (p := p) (D := D) (hreg := hreg)
      (r := t - s) (x := x) (s := s)
      hr hx hsT (Gdiv := Gdiv) hGcont hGeq

/-- Integrated form of the regularity-only gradient-source bridge with explicit
Duhamel integrability inputs. -/
theorem gradientMildDuhamelTerms_eq_integral_mixedSpectralSource_of_gradientMildRegularity_representative_integrable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hreg : intervalDomainClassicalRegularity D.T D.u
      (coupledChemicalConcentration p D.u))
    (hrep : ∀ s, s ∈ Set.Ioo (0 : ℝ) D.T →
      ∃ Gdiv : ℝ → ℝ,
        ContinuousOn Gdiv (Set.Icc (0 : ℝ) 1) ∧
        Set.EqOn (coupledChemDivSourceLift p D.u s) Gdiv (Set.Ioo (0 : ℝ) 1))
    {t x : ℝ} (ht0 : 0 < t) (htT : t < D.T) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hchem_int :
      IntervalIntegrable
        (fun s : ℝ =>
          deriv (fun z : ℝ =>
            intervalFullSemigroupOperator (t - s) (chemFluxLifted p (D.u s)) z) x)
        volume (0 : ℝ) t)
    (hlog_int :
      IntervalIntegrable
        (fun s : ℝ =>
          intervalFullSemigroupOperator (t - s) (logisticLifted p (D.u s)) x)
        volume (0 : ℝ) t) :
    gradientMildChemotaxisDuhamelTerm p D.u t x
      + gradientMildLogisticDuhamelTerm p D.u t x
      =
    ∫ s in (0 : ℝ)..t,
      ((-p.χ₀) *
          unitIntervalSineHeatValue (t - s)
            (sineCoeffs (coupledChemDivSourceLift p D.u s)) x
        + unitIntervalCosineHeatValue (t - s)
            (coupledLogisticSourceCoeffs p D.u s) x) := by
  let A : ℝ → ℝ := fun s : ℝ =>
    deriv (fun z : ℝ =>
      intervalFullSemigroupOperator (t - s) (chemFluxLifted p (D.u s)) z) x
  let B : ℝ → ℝ := fun s : ℝ =>
    intervalFullSemigroupOperator (t - s) (logisticLifted p (D.u s)) x
  let C : ℝ → ℝ := fun s : ℝ =>
    (-p.χ₀) *
        unitIntervalSineHeatValue (t - s)
          (sineCoeffs (coupledChemDivSourceLift p D.u s)) x
      + unitIntervalCosineHeatValue (t - s)
          (coupledLogisticSourceCoeffs p D.u s) x
  have hleft :
      gradientMildChemotaxisDuhamelTerm p D.u t x
        + gradientMildLogisticDuhamelTerm p D.u t x
        = ∫ s in (0 : ℝ)..t, ((-p.χ₀) * A s + B s) := by
    rw [gradientMildChemotaxisDuhamelTerm, gradientMildLogisticDuhamelTerm]
    rw [intervalIntegral.integral_add (hchem_int.const_mul (-p.χ₀)) hlog_int]
    rw [intervalIntegral.integral_const_mul]
  calc
    gradientMildChemotaxisDuhamelTerm p D.u t x
        + gradientMildLogisticDuhamelTerm p D.u t x
        = ∫ s in (0 : ℝ)..t, ((-p.χ₀) * A s + B s) := hleft
    _ = ∫ s in (0 : ℝ)..t, C s := by
      apply intervalIntegral.integral_congr_ae
      rw [Set.uIoc_of_le ht0.le]
      filter_upwards
        [(MeasureTheory.Ioo_ae_eq_Ioc
          (a := (0 : ℝ)) (b := t) (μ := volume)).symm] with s hs_ae hsIoc
      have hsIoo_t : s ∈ Set.Ioo (0 : ℝ) t := hs_ae.mp hsIoc
      have hr : 0 < t - s := sub_pos.mpr hsIoo_t.2
      have hsT : s ∈ Set.Ioo (0 : ℝ) D.T :=
        ⟨hsIoo_t.1, lt_trans hsIoo_t.2 htT⟩
      obtain ⟨Gdiv, hGcont, hGeq⟩ := hrep s hsT
      simpa [A, B, C] using
        gradient_source_bridge_slice_open_of_gradientMildRegularity_representative
          (p := p) (D := D) (hreg := hreg)
          (r := t - s) (x := x) (s := s)
          hr hx hsT (Gdiv := Gdiv) hGcont hGeq
    _ = ∫ s in (0 : ℝ)..t,
        ((-p.χ₀) *
            unitIntervalSineHeatValue (t - s)
              (sineCoeffs (coupledChemDivSourceLift p D.u s)) x
          + unitIntervalCosineHeatValue (t - s)
              (coupledLogisticSourceCoeffs p D.u s) x) := rfl

/-- Integrated regularity-only gradient-source bridge with Duhamel
integrability discharged from windowed measurable source bounds. -/
theorem gradientMildDuhamelTerms_eq_integral_mixedSpectralSource_of_gradientMildRegularity_representative_windowBounds
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hreg : intervalDomainClassicalRegularity D.T D.u
      (coupledChemicalConcentration p D.u))
    (hrep : ∀ s, s ∈ Set.Ioo (0 : ℝ) D.T →
      ∃ Gdiv : ℝ → ℝ,
        ContinuousOn Gdiv (Set.Icc (0 : ℝ) 1) ∧
        Set.EqOn (coupledChemDivSourceLift p D.u s) Gdiv (Set.Ioo (0 : ℝ) 1))
    {t x : ℝ} (ht0 : 0 < t) (htT : t < D.T) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hchem_meas :
      Measurable (Function.uncurry (fun s y => chemFluxLifted p (D.u s) y)))
    {Cchem : ℝ} (hCchem : 0 ≤ Cchem)
    (hchem_bound : ∀ s, 0 < s → s ≤ t → ∀ y, |chemFluxLifted p (D.u s) y| ≤ Cchem)
    (hlog_meas :
      Measurable (Function.uncurry (fun s y => logisticLifted p (D.u s) y)))
    {Clog : ℝ} (hClog : 0 ≤ Clog)
    (hlog_bound : ∀ s, 0 < s → s ≤ t → ∀ y, |logisticLifted p (D.u s) y| ≤ Clog) :
    gradientMildChemotaxisDuhamelTerm p D.u t x
      + gradientMildLogisticDuhamelTerm p D.u t x
      =
    ∫ s in (0 : ℝ)..t,
      ((-p.χ₀) *
          unitIntervalSineHeatValue (t - s)
            (sineCoeffs (coupledChemDivSourceLift p D.u s)) x
        + unitIntervalCosineHeatValue (t - s)
            (coupledLogisticSourceCoeffs p D.u s) x) := by
  let Q : ℝ → ℝ → ℝ :=
    fun s y => if 0 < s ∧ s ≤ t then chemFluxLifted p (D.u s) y else 0
  let L : ℝ → ℝ → ℝ :=
    fun s y => if 0 < s ∧ s ≤ t then logisticLifted p (D.u s) y else 0
  have hQ_meas : Measurable (Function.uncurry Q) := by
    have hbase : Measurable
        (fun z : ℝ × ℝ => chemFluxLifted p (D.u z.1) z.2) := by
      simpa [Function.uncurry] using hchem_meas
    simp only [Q]
    refine Measurable.ite ?_ hbase measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  have hQ_sup : ∀ s y, |Q s y| ≤ Cchem := by
    intro s y
    simp only [Q]
    split_ifs with h
    · exact hchem_bound s h.1 h.2 y
    · simpa using hCchem
  have hL_meas : Measurable (Function.uncurry L) := by
    have hbase : Measurable
        (fun z : ℝ × ℝ => logisticLifted p (D.u z.1) z.2) := by
      simpa [Function.uncurry] using hlog_meas
    simp only [L]
    refine Measurable.ite ?_ hbase measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  have hL_sup : ∀ s y, |L s y| ≤ Clog := by
    intro s y
    simp only [L]
    split_ifs with h
    · exact hlog_bound s h.1 h.2 y
    · simpa using hClog
  have hchem_cut_int :
      IntervalIntegrable
        (fun s : ℝ =>
          deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (Q s) z) x)
        volume (0 : ℝ) t :=
    ShenWork.IntervalDuhamelIntegrability.gradDuhamel_intervalIntegrable_of_joint_measurable
      ht0 hQ_meas hCchem hQ_sup x
  have hlog_cut_int :
      IntervalIntegrable
        (fun s : ℝ => intervalFullSemigroupOperator (t - s) (L s) x)
        volume (0 : ℝ) t :=
    ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
      ht0 hL_meas hClog hL_sup x
  have hchem_congr : Set.EqOn
      (fun s : ℝ =>
        deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (Q s) z) x)
      (fun s : ℝ =>
        deriv (fun z : ℝ =>
          intervalFullSemigroupOperator (t - s) (chemFluxLifted p (D.u s)) z) x)
      (Set.uIoc 0 t) := by
    intro s hs
    rw [Set.uIoc_of_le ht0.le] at hs
    have hmem : 0 < s ∧ s ≤ t := ⟨hs.1, hs.2⟩
    simp only [Q, if_pos hmem]
  have hlog_congr : Set.EqOn
      (fun s : ℝ => intervalFullSemigroupOperator (t - s) (L s) x)
      (fun s : ℝ =>
        intervalFullSemigroupOperator (t - s) (logisticLifted p (D.u s)) x)
      (Set.uIoc 0 t) := by
    intro s hs
    rw [Set.uIoc_of_le ht0.le] at hs
    have hmem : 0 < s ∧ s ≤ t := ⟨hs.1, hs.2⟩
    simp only [L, if_pos hmem]
  exact
    gradientMildDuhamelTerms_eq_integral_mixedSpectralSource_of_gradientMildRegularity_representative_integrable
      (p := p) (D := D) hreg hrep ht0 htT hx
      (hchem_cut_int.congr hchem_congr)
      (hlog_cut_int.congr hlog_congr)

/-- Source-certificate version of the regularity-only integrated
gradient-source bridge.

The old source-certificate theorem required a full
`IsPaper2ClassicalSolution`; this version needs only non-PDE classical
regularity plus the endpoint-insensitive chem-div representative input. -/
theorem gradientMildDuhamelTerms_eq_integral_mixedSpectralSource_of_gradientMildSolutionData_and_regularRepr
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hreg : intervalDomainClassicalRegularity D.T D.u
      (coupledChemicalConcentration p D.u))
    (hrep : ∀ s, s ∈ Set.Ioo (0 : ℝ) D.T →
      ∃ Gdiv : ℝ → ℝ,
        ContinuousOn Gdiv (Set.Icc (0 : ℝ) 1) ∧
        Set.EqOn (coupledChemDivSourceLift p D.u s) Gdiv (Set.Ioo (0 : ℝ) 1))
    {t x : ℝ} (ht0 : 0 < t) (htT : t < D.T) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    gradientMildChemotaxisDuhamelTerm p D.u t x
      + gradientMildLogisticDuhamelTerm p D.u t x
      =
    ∫ s in (0 : ℝ)..t,
      ((-p.χ₀) *
          unitIntervalSineHeatValue (t - s)
            (sineCoeffs (coupledChemDivSourceLift p D.u s)) x
        + unitIntervalCosineHeatValue (t - s)
            (coupledLogisticSourceCoeffs p D.u s) x) := by
  have hchem_meas :
      Measurable (Function.uncurry (fun s y => chemFluxLifted p (D.u s) y)) :=
    ShenWork.Paper2.chemFluxLifted_uncurry_measurable (p := p) (u := D.u) D.hmeas
  have hlog_meas :
      Measurable (Function.uncurry (fun s y => logisticLifted p (D.u s) y)) :=
    ShenWork.Paper2.logisticLifted_uncurry_measurable (p := p) (u := D.u) D.hmeas
  exact
    gradientMildDuhamelTerms_eq_integral_mixedSpectralSource_of_gradientMildRegularity_representative_windowBounds
      (p := p) (D := D) hreg hrep ht0 htT hx
      hchem_meas (gradientBridgeChemFluxBound_nonneg p D.hM.le)
      (fun s hs hst y =>
        gradientBridge_chemFlux_windowBound_of_gradientMildSolutionData D
          s hs (le_trans hst htT.le) y)
      hlog_meas (gradientBridgeLogisticBound_nonneg p D.hM.le)
      (fun s hs hst y =>
        gradientBridge_logistic_windowBound_of_gradientMildSolutionData D
          s hs (le_trans hst htT.le) y)

end ShenWork.IntervalMildToLocalExistence
