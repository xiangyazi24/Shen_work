/-
  Linear drift comparison before strict positivity.

  The comparison field for `u` is a global cosine representative selected from
  the B-form spectral agreement at each positive time.  Thus its ordinary
  spatial derivatives at the endpoints are genuine; no zero-extension
  differentiability is asserted.  The reaction coefficient is the expanded
  coefficient

    -chi * d_x (v_x / (1+v)^beta) + (a - b*u^alpha),

  and never divides by `u`.
-/
import ShenWork.Paper2.IntervalBFormPrePositivityBootstrap
import ShenWork.Paper2.IntervalBFormLinearDriftComparisonRegularDischarge
import ShenWork.PDE.IntervalMildFrontierFromSpectral

open Filter Topology Set
open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement mildSolution_hasDerivAt_time)
open ShenWork.IntervalMildFrontierFromSpectral
  (mildSolution_jointContinuousOn_closed)
open ShenWork.IntervalBFormSpectral
  (HasBFormSpectralPdeAgreement intervalConjugateMildSolution_pde_u_of_spectral)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.IntervalDuhamelClosedC2
  (cosineCoeffSeries_contDiff_two cosineCoeffSeries_deriv_at_zero
    cosineCoeffSeries_deriv_at_one)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.PDE.ParabolicMaxPrinciple (dt dx dxx)
open ShenWork.Paper2.BFormPositiveDatumNegPart
  (BoundedOnIntervalStrip NeumannLinearDriftCoefficientsRegular
    IsClassicalNeumannLinearDriftSubSolution
    IsClassicalNeumannLinearDriftSuperSolution
    neumannLinearDriftResidual neumann_interval_comparison_with_drift)

noncomputable section

namespace ShenWork.Paper2

/-- Honest resolver-side regularity required by the expanded linear drift.
The extension `vExt` agrees with the interval resolver on `[0,1]`; its global
spatial `C²` slices make ordinary endpoint derivatives meaningful. -/
structure PrePositivityResolverC2JointCertificate
    (p : CM2Params) (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) : Type where
  vExt : ℝ → ℝ → ℝ
  eqOn_resolver : ∀ t, 0 < t → t < T →
    Set.EqOn
      (intervalDomainLift (mildChemicalConcentration p u t)) (vExt t)
      (Set.Icc (0 : ℝ) 1)
  sliceC2 : ∀ t, 0 < t → t < T → ContDiff ℝ 2 (vExt t)
  jointContinuousOn :
    ContinuousOn (Function.uncurry vExt)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)
  gradJointContinuousOn :
    ContinuousOn (fun q : ℝ × ℝ ↦ deriv (vExt q.1) q.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)
  grad2JointContinuousOn :
    ContinuousOn
      (fun q : ℝ × ℝ ↦ deriv (fun y ↦ deriv (vExt q.1) y) q.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)
  denom_pos : ∀ t, 0 < t → t < T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
    0 < 1 + vExt t x
  chemDiv_eq_fluxDeriv : ∀ t, 0 < t → t < T → ∀ x,
    ∀ hx : x ∈ Set.Ioo (0 : ℝ) 1,
    intervalDomain.chemotaxisDiv p (u t) (mildChemicalConcentration p u t)
        ⟨x, Set.Ioo_subset_Icc_self hx⟩ =
      deriv (fun y : ℝ ↦
        intervalDomainLift (u t) y * deriv (vExt t) y /
          (1 + vExt t y) ^ p.β) x

/-- Spectral and resolver regularity available before strict positivity. -/
structure PrePositivitySpectralRegularityData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (S : NonnegativeConjugateMildSolutionData p u₀) : Type where
  hPdeAgreement : HasBFormSpectralPdeAgreement p S.T S.u
  hTimeNhd : HasTimeNeighborhoodSpectralAgreement S.T S.u
  resolver : PrePositivityResolverC2JointCertificate p S.T S.u

private noncomputable def prePositivitySliceCoeffs
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (Hpde : HasBFormSpectralPdeAgreement p T u) (t : ℝ) : ℕ → ℝ :=
  if ht : 0 < t ∧ t < T then
    Classical.choose (bFormSpectral_slice_before_strictPositivity Hpde ht.1 ht.2)
  else fun _ ↦ 0

private theorem prePositivitySliceCoeffs_spec
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (Hpde : HasBFormSpectralPdeAgreement p T u)
    {t : ℝ} (ht : 0 < t) (htT : t < T) :
    Summable (fun n : ℕ ↦ unitIntervalCosineEigenvalue n *
      |prePositivitySliceCoeffs Hpde t n|) ∧
    Set.EqOn (intervalDomainLift (u t))
      (fun x : ℝ ↦ ∑' n : ℕ, prePositivitySliceCoeffs Hpde t n * cosineMode n x)
      (Set.Icc (0 : ℝ) 1) := by
  rw [prePositivitySliceCoeffs, dif_pos ⟨ht, htT⟩]
  exact Classical.choose_spec
    (bFormSpectral_slice_before_strictPositivity Hpde ht htT)

/-- Global cosine representative of the nonnegative mild solution. -/
def prePositivityComparisonField
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (Hpde : HasBFormSpectralPdeAgreement p T u) : ℝ → ℝ → ℝ :=
  fun t x ↦ ∑' n : ℕ, prePositivitySliceCoeffs Hpde t n * cosineMode n x

theorem prePositivityComparisonField_eq_lift
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (Hpde : HasBFormSpectralPdeAgreement p T u)
    {t x : ℝ} (ht : 0 < t) (htT : t < T) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    prePositivityComparisonField Hpde t x = intervalDomainLift (u t) x := by
  exact (prePositivitySliceCoeffs_spec Hpde ht htT).2 hx |>.symm

theorem prePositivityComparisonField_sliceC2
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (Hpde : HasBFormSpectralPdeAgreement p T u)
    {t : ℝ} (ht : 0 < t) (htT : t < T) :
    ContDiff ℝ 2 (prePositivityComparisonField Hpde t) := by
  exact cosineCoeffSeries_contDiff_two
    (prePositivitySliceCoeffs_spec Hpde ht htT).1

/-- The comparison representative attached to the full pre-positivity data. -/
def PrePositivitySpectralRegularityData.uExt
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {S : NonnegativeConjugateMildSolutionData p u₀}
    (H : PrePositivitySpectralRegularityData p S) : ℝ → ℝ → ℝ :=
  prePositivityComparisonField H.hPdeAgreement

/-- The resolver drift factor `v_x/(1+v)^β`. -/
def PrePositivitySpectralRegularityData.fluxFactor
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {S : NonnegativeConjugateMildSolutionData p u₀}
    (H : PrePositivitySpectralRegularityData p S) : ℝ → ℝ → ℝ :=
  fun t x ↦ deriv (H.resolver.vExt t) x / (1 + H.resolver.vExt t x) ^ p.β

/-- Expanded first-order drift coefficient. -/
def PrePositivitySpectralRegularityData.drift
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {S : NonnegativeConjugateMildSolutionData p u₀}
    (H : PrePositivitySpectralRegularityData p S) : ℝ → ℝ → ℝ :=
  fun t x ↦ -p.χ₀ * H.fluxFactor t x

/-- Expanded zeroth-order coefficient.  The logistic contribution is directly
`a - b*u^α`; in particular this definition never divides by `u`. -/
def PrePositivitySpectralRegularityData.react
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {S : NonnegativeConjugateMildSolutionData p u₀}
    (H : PrePositivitySpectralRegularityData p S) : ℝ → ℝ → ℝ :=
  fun t x ↦
    -p.χ₀ * deriv (H.fluxFactor t) x
      + (p.a - p.b * (H.uExt t x) ^ p.α)

theorem PrePositivitySpectralRegularityData.uExt_eq_lift
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {S : NonnegativeConjugateMildSolutionData p u₀}
    (H : PrePositivitySpectralRegularityData p S)
    {t x : ℝ} (ht : 0 < t) (htT : t < S.T) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    H.uExt t x = intervalDomainLift (S.u t) x :=
  prePositivityComparisonField_eq_lift H.hPdeAgreement ht htT hx

theorem PrePositivitySpectralRegularityData.uExt_sliceC2
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {S : NonnegativeConjugateMildSolutionData p u₀}
    (H : PrePositivitySpectralRegularityData p S)
    {t : ℝ} (ht : 0 < t) (htT : t < S.T) :
    ContDiff ℝ 2 (H.uExt t) :=
  prePositivityComparisonField_sliceC2 H.hPdeAgreement ht htT

theorem PrePositivitySpectralRegularityData.uExt_jointContinuousOn
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {S : NonnegativeConjugateMildSolutionData p u₀}
    (H : PrePositivitySpectralRegularityData p S) :
    ContinuousOn (Function.uncurry H.uExt)
      (Set.Ioo (0 : ℝ) S.T ×ˢ Set.Icc (0 : ℝ) 1) := by
  refine (mildSolution_jointContinuousOn_closed H.hTimeNhd).congr ?_
  intro q hq
  simpa [Function.uncurry] using H.uExt_eq_lift hq.1.1 hq.1.2 hq.2

theorem PrePositivitySpectralRegularityData.uExt_space_hasDerivAt
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {S : NonnegativeConjugateMildSolutionData p u₀}
    (H : PrePositivitySpectralRegularityData p S)
    {t x : ℝ} (ht : 0 < t) (htT : t < S.T) :
    HasDerivAt (fun y : ℝ ↦ H.uExt t y) (dx H.uExt t x) x := by
  have hdiff : Differentiable ℝ (H.uExt t) :=
    (H.uExt_sliceC2 ht htT).differentiable (by norm_num)
  simpa [dx] using (hdiff x).hasDerivAt

theorem PrePositivitySpectralRegularityData.uExt_time_hasDerivAt
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {S : NonnegativeConjugateMildSolutionData p u₀}
    (H : PrePositivitySpectralRegularityData p S)
    {t x : ℝ} (ht : 0 < t) (htT : t < S.T) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun s : ℝ ↦ H.uExt s x) (dt H.uExt t x) t := by
  let X : intervalDomainPoint := ⟨x, hx⟩
  obtain ⟨a₀, M, hM, ha₀, a, src, offset, hoff, hagree⟩ :=
    H.hTimeNhd.exists_data t ht htT
  have hbase := mildSolution_hasDerivAt_time
    hM ha₀ src hoff hagree X
  have heq :
      (fun s : ℝ ↦ H.uExt s x) =ᶠ[ᵊ t] (fun s : ℝ ↦ S.u s X) := by
    filter_upwards [Ioo_mem_nhds ht htT] with s hs
    calc
      H.uExt s x = intervalDomainLift (S.u s) x :=
        H.uExt_eq_lift hs.1 hs.2 hx
      _ = S.u s X := by simp [intervalDomainLift, X, hx]
  have hU := hbase.congr_of_eventuallyEq heq
  simpa [dt] using hU.differentiableAt.hasDerivAt

theorem PrePositivitySpectralRegularityData.uExt_space_second_hasDerivAt
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {S : NonnegativeConjugateMildSolutionData p u₀}
    (H : PrePositivitySpectralRegularityData p S)
    {t x : ℝ} (ht : 0 < t) (htT : t < S.T) :
    HasDerivAt (fun y : ℝ ↦ dx H.uExt t y) (dxx H.uExt t x) x := by
  have hderivC1 : ContDiff ℝ 1 (deriv (H.uExt t)) := by
    simpa using (H.uExt_sliceC2 ht htT).deriv'
  have hdiff : Differentiable ℝ (deriv (H.uExt t)) :=
    hderivC1.differentiable (by norm_num)
  simpa [dx, dxx] using (hdiff x).hasDerivAt

theorem PrePositivitySpectralRegularityData.uExt_neumann
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {S : NonnegativeConjugateMildSolutionData p u₀}
    (H : PrePositivitySpectralRegularityData p S)
    {t : ℝ} (ht : 0 < t) (htT : t < S.T) :
    dx H.uExt t 0 = 0 ∧ dx H.uExt t 1 = 0 := by
  have hsum := (prePositivitySliceCoeffs_spec H.hPdeAgreement ht htT).1
  exact
    ⟨by simpa [PrePositivitySpectralRegularityData.uExt,
        prePositivityComparisonField, dx] using
        cosineCoeffSeries_deriv_at_zero hsum,
      by simpa [PrePositivitySpectralRegularityData.uExt,
        prePositivityComparisonField, dx] using
        cosineCoeffSeries_deriv_at_one hsum⟩

end ShenWork.Paper2
