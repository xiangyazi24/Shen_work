import ShenWork.Paper1.WholeLineWeightedRegularityHeatGradientDuhamelHolder
import ShenWork.Paper1.WholeLineWeightedRegularityRestart

open Filter MeasureTheory Set Topology
open scoped RealInnerProductSpace Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# The spatial gradient of the full weighted mild candidate

The first spatial derivative of a full weighted heat restart consists of the
heat-gradient orbit of the restart datum and the heat-gradient Duhamel
history of the exact-weight forcing.  This construction uses the forcing
itself, not a spatial derivative of the forcing.
-/

/-- First spatial heat derivative of the full-generator mild candidate based
at `a`.  The totalized heat-gradient is zero at its zero-lag endpoint, which
is harmless in the Bochner time integral. -/
def weightedMovingHeatFullGradientCandidate
    (eta c a : ℝ) (Z₀ : WholeLineRealL2)
    (F : ℝ → WholeLineRealL2) (t : ℝ) : WholeLineRealL2 :=
  weightedMovingHeatL2Gradient eta c (t - a) Z₀ +
    ∫ q in a..t,
      weightedMovingHeatL2Gradient eta c (t - q) (F q)

/-- The scalar weighted heat-gradient depends only on the almost-everywhere
class of its `L²` datum. -/
theorem weightedMovingHeatGradientEta_congr_ae
    {eta c t : ℝ} {f g : ℝ → ℝ}
    (hfg : f =ᵐ[volume] g) (x : ℝ) :
    weightedMovingHeatGradientEta eta c t f x =
      weightedMovingHeatGradientEta eta c t g x := by
  unfold weightedMovingHeatGradientEta
  congr 1
  apply integral_congr_ae
  filter_upwards [hfg] with y hy
  rw [hy]

/-- A bounded measurable datum has the scalar weighted heat-gradient as the
classical spatial derivative of its positive-time weighted heat orbit. -/
theorem weightedMovingHeatEta_spatial_hasDerivAt_of_bounded
    {eta c t x C : ℝ} {f : ℝ → ℝ}
    (ht : 0 < t)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ C) :
    HasDerivAt (weightedMovingHeatEta eta c t f)
      (weightedMovingHeatGradientEta eta c t f x) x := by
  have hbase := wholeLineDriftHeatOp_spatial_hasDerivAt_of_bounded
    (d := c - 2 * eta) (x := x) ht hf_meas hf
  have hscaled := hbase.const_mul (weightedMovingHeatGrowth eta c t)
  have hexp : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    simp
  convert hscaled using 1
  · funext z
    unfold weightedMovingHeatEta weightedMovingHeatMarkovKernel
      wholeLineDriftHeatOp wholeLineCauchyMovingHeatOp
      wholeLineCauchyHeatOp modifiedSemigroup heatSemigroup
    congr 1
    rw [← mul_assoc, hexp, one_mul]
  · unfold weightedMovingHeatGradientEta wholeLineDriftHeatGradOp
      wholeLineCauchyHeatGradOp
    congr 1
    have hintegrand : (fun y : ℝ => Real.exp (-t) *
          (deriv (fun z : ℝ => heatKernel t (z - y))
              (x + (c - 2 * eta) * t) * f y)) =
        fun y => Real.exp (-t) *
          (deriv (fun z : ℝ => heatKernel t z)
              (x + (c - 2 * eta) * t - y) * f y) := by
      funext y
      rw [deriv_comp_sub_const]
    rw [hintegrand, integral_const_mul, ← mul_assoc, hexp, one_mul]

/-- Uniform-in-space first-gradient bound on a finite positive-lag horizon
for a uniformly bounded scalar datum. -/
theorem weightedMovingHeatGradientEta_abs_le_horizon_rpow_neg_half
    {eta c H t K : ℝ} (ht : 0 < t) (htH : t ≤ H)
    (hK : 0 ≤ K) {f : ℝ → ℝ}
    (hf : ∀ y, |f y| ≤ K) (x : ℝ) :
    |weightedMovingHeatGradientEta eta c t f x| ≤
      (Real.exp (|eta ^ 2 - c * eta| * H) *
        ((2 / Real.sqrt (4 * Real.pi)) * K)) *
          t ^ (-(1 / 2 : ℝ)) := by
  have hfun : (fun y : ℝ =>
        deriv (fun z : ℝ => heatKernel t (z - y))
            (x + (c - 2 * eta) * t) * f y) =
      fun y => deriv (fun z : ℝ => heatKernel t z)
          (x + (c - 2 * eta) * t - y) * f y := by
    funext y
    rw [deriv_comp_sub_const]
  have hraw := heatKernel_deriv_convolution_bounded_abs_le
    ht hK hf (x + (c - 2 * eta) * t)
  rw [hfun] at hraw
  have hgrowth : weightedMovingHeatGrowth eta c t ≤
      Real.exp (|eta ^ 2 - c * eta| * H) :=
    weightedMovingHeatGrowth_le_exp_abs_mul_of_mem_Icc ⟨ht.le, htH⟩
  have hgrowth_nonneg : 0 ≤ weightedMovingHeatGrowth eta c t := by
    unfold weightedMovingHeatGrowth
    positivity
  have hraw_nonneg : 0 ≤ (2 / Real.sqrt (4 * Real.pi * t)) * K := by
    positivity
  unfold weightedMovingHeatGradientEta
  rw [abs_mul, abs_of_nonneg hgrowth_nonneg]
  calc
    weightedMovingHeatGrowth eta c t *
          |∫ y : ℝ,
            deriv (fun z : ℝ => heatKernel t z)
              (x + (c - 2 * eta) * t - y) * f y| ≤
        weightedMovingHeatGrowth eta c t *
          ((2 / Real.sqrt (4 * Real.pi * t)) * K) :=
      mul_le_mul_of_nonneg_left hraw hgrowth_nonneg
    _ ≤ Real.exp (|eta ^ 2 - c * eta| * H) *
          ((2 / Real.sqrt (4 * Real.pi * t)) * K) :=
      mul_le_mul_of_nonneg_right hgrowth hraw_nonneg
    _ = (Real.exp (|eta ^ 2 - c * eta| * H) *
          ((2 / Real.sqrt (4 * Real.pi)) * K)) *
            t ^ (-(1 / 2 : ℝ)) := by
      rw [two_div_sqrt_four_pi_mul_eq_rpow_cauchy ht]
      ring

/-- Scalar Duhamel history for the weighted moving heat flow. -/
def weightedMovingHeatValueHistory
    (eta c a r : ℝ) (f : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ q in a..r, weightedMovingHeatEta eta c (r - q) (f q) x

/-- Scalar spatial-gradient Duhamel history for the weighted moving heat
flow. -/
def weightedMovingHeatGradientHistory
    (eta c a r : ℝ) (f : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ q in a..r, weightedMovingHeatGradientEta eta c (r - q) (f q) x

/-- Differentiate a weighted heat Duhamel history under an explicit local
dominated-convergence majorant.  The forcing itself is differentiated only
through the heat kernel, so no spatial derivative of the forcing occurs. -/
theorem weightedMovingHeatValueHistory_hasDerivAt_of_dominated
    {eta c a r x C rho : ℝ} {f : ℝ → ℝ → ℝ}
    {bound : ℝ → ℝ}
    (har : a < r) (hrho : 0 < rho)
    (hf_slice_meas : ∀ q ∈ Set.Ioc a r,
      AEStronglyMeasurable (f q) volume)
    (hf_bound : ∀ q ∈ Set.Ioc a r, ∀ y, |f q y| ≤ C)
    (hvalue_meas : ∀ z ∈ Metric.ball x rho,
      AEStronglyMeasurable
        (fun q : ℝ => weightedMovingHeatEta eta c (r - q) (f q) z)
        (volume.restrict (Set.uIoc a r)))
    (hvalue_int : IntervalIntegrable
      (fun q : ℝ => weightedMovingHeatEta eta c (r - q) (f q) x)
      volume a r)
    (hgrad_meas : AEStronglyMeasurable
      (fun q : ℝ => weightedMovingHeatGradientEta eta c (r - q) (f q) x)
      (volume.restrict (Set.uIoc a r)))
    (hbound_int : IntervalIntegrable bound volume a r)
    (hbound : ∀ᵐ q : ℝ ∂volume, q ∈ Set.uIoc a r →
      ∀ z ∈ Metric.ball x rho,
        ‖weightedMovingHeatGradientEta eta c (r - q) (f q) z‖ ≤
          bound q) :
    HasDerivAt (weightedMovingHeatValueHistory eta c a r f)
      (weightedMovingHeatGradientHistory eta c a r f x) x := by
  have hne : ∀ᵐ q : ℝ ∂volume, q ≠ r := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  unfold weightedMovingHeatValueHistory weightedMovingHeatGradientHistory
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := a) (b := r)
    (F := fun z q => weightedMovingHeatEta eta c (r - q) (f q) z)
    (F' := fun z q => weightedMovingHeatGradientEta eta c (r - q) (f q) z)
    (x₀ := x) (s := Metric.ball x rho) (bound := bound)
    (Metric.ball_mem_nhds x hrho)
    ?hF_meas hvalue_int hgrad_meas hbound hbound_int ?h_diff).2
  · filter_upwards [Metric.ball_mem_nhds x hrho] with z hz
    exact hvalue_meas z hz
  · filter_upwards [hne] with q hqr hqI z _hz
    rw [Set.uIoc_of_le har.le, Set.mem_Ioc] at hqI
    have hq_lt : q < r := lt_of_le_of_ne hqI.2 hqr
    exact weightedMovingHeatEta_spatial_hasDerivAt_of_bounded
      (sub_pos.mpr hq_lt) (hf_slice_meas q hqI) (hf_bound q hqI)

/-- Uniformly bounded forcing specialization.  The integrable
`(r-q)⁻¹ᵗ²` majorant is constructed internally, so the caller only supplies
measurability and existence of the scalar value history. -/
theorem weightedMovingHeatValueHistory_hasDerivAt_of_uniform_bound
    {eta c a r x K rho : ℝ} {f : ℝ → ℝ → ℝ}
    (har : a < r) (hrho : 0 < rho) (hK : 0 ≤ K)
    (hf_slice_meas : ∀ q ∈ Set.Ioc a r,
      AEStronglyMeasurable (f q) volume)
    (hf_bound : ∀ q ∈ Set.Ioc a r, ∀ y, |f q y| ≤ K)
    (hvalue_meas : ∀ z ∈ Metric.ball x rho,
      AEStronglyMeasurable
        (fun q : ℝ => weightedMovingHeatEta eta c (r - q) (f q) z)
        (volume.restrict (Set.uIoc a r)))
    (hvalue_int : IntervalIntegrable
      (fun q : ℝ => weightedMovingHeatEta eta c (r - q) (f q) x)
      volume a r)
    (hgrad_meas : AEStronglyMeasurable
      (fun q : ℝ => weightedMovingHeatGradientEta eta c (r - q) (f q) x)
      (volume.restrict (Set.uIoc a r))) :
    HasDerivAt (weightedMovingHeatValueHistory eta c a r f)
      (weightedMovingHeatGradientHistory eta c a r f x) x := by
  let A := Real.exp (|eta ^ 2 - c * eta| * (r - a)) *
    ((2 / Real.sqrt (4 * Real.pi)) * K)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hmajor : IntervalIntegrable
      (fun q : ℝ => A * (r - q) ^ (-(1 / 2 : ℝ)))
      volume a r := by
    exact (intervalIntegrable_sub_rpow_neg_half_between a r).const_mul A
  apply weightedMovingHeatValueHistory_hasDerivAt_of_dominated
    har hrho hf_slice_meas hf_bound hvalue_meas hvalue_int hgrad_meas
      hmajor
  filter_upwards [Measure.ae_ne volume r] with q hqr hqI z _hz
  rw [Set.uIoc_of_le har.le, Set.mem_Ioc] at hqI
  have hlag : 0 < r - q := sub_pos.mpr (lt_of_le_of_ne hqI.2 hqr)
  have hlagH : r - q ≤ r - a := by linarith [hqI.1]
  simpa only [Real.norm_eq_abs, A] using
    weightedMovingHeatGradientEta_abs_le_horizon_rpow_neg_half
      (eta := eta) (c := c) hlag hlagH hK (hf_bound q hqI) z

/-- Differentiate an actual scalar full-generator restart.  This is the
non-circular uniqueness step: it consumes the value restart and the
heat-history derivative, but no `L²` information about the terminal spatial
derivative. -/
theorem weightedMovingHeat_fullGenerator_spatial_identity
    {eta c a r x C : ℝ} {Wr Wa Wrx : ℝ → ℝ}
    {f : ℝ → ℝ → ℝ}
    (har : a < r)
    (hrestart : ∀ z,
      Wr z = weightedMovingHeatEta eta c (r - a) Wa z +
        weightedMovingHeatValueHistory eta c a r f z)
    (hWr_deriv : HasDerivAt Wr (Wrx x) x)
    (hWa_meas : AEStronglyMeasurable Wa volume)
    (hWa_bound : ∀ y, |Wa y| ≤ C)
    (hhistory : HasDerivAt (weightedMovingHeatValueHistory eta c a r f)
      (weightedMovingHeatGradientHistory eta c a r f x) x) :
    Wrx x = weightedMovingHeatGradientEta eta c (r - a) Wa x +
      weightedMovingHeatGradientHistory eta c a r f x := by
  have hhom := weightedMovingHeatEta_spatial_hasDerivAt_of_bounded
    (eta := eta) (c := c) (x := x) (sub_pos.mpr har) hWa_meas hWa_bound
  have hright := hhom.add hhistory
  have hfun : Wr = fun z =>
      weightedMovingHeatEta eta c (r - a) Wa z +
        weightedMovingHeatValueHistory eta c a r f z := by
    funext z
    exact hrestart z
  have hrightW : HasDerivAt Wr
      (weightedMovingHeatGradientEta eta c (r - a) Wa x +
        weightedMovingHeatGradientHistory eta c a r f x) x := by
    rw [hfun]
    exact hright
  exact hWr_deriv.unique hrightW

/-- Scalar representative of a heat-gradient Bochner history.  As for the
value semigroup, only local space-time product integrability is needed to
justify Fubini on the unbounded spatial line. -/
theorem weightedMovingHeatL2Gradient_intervalIntegral_coe_ae
    {eta c a r : ℝ} (har : a ≤ r)
    {f : ℝ → ℝ → ℝ} {F : ℝ → WholeLineRealL2}
    (hFrep : ∀ q ∈ Set.Ioc a r,
      (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] f q))
    (hDint : IntervalIntegrable
      (fun q => weightedMovingHeatL2Gradient eta c (r - q) (F q))
      volume a r)
    (hlocal : ∀ A : Set ℝ, MeasurableSet A →
      (volume : Measure ℝ) A < ⊤ →
      Integrable
        (fun z : ℝ × ℝ => A.indicator
          (weightedMovingHeatGradientEta eta c (r - z.1) (f z.1)) z.2)
        ((volume.restrict (Set.Ioc a r)).prod volume)) :
    ((((∫ q in a..r,
          weightedMovingHeatL2Gradient eta c (r - q) (F q)) :
        WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      fun x => ∫ q in a..r,
        weightedMovingHeatGradientEta eta c (r - q) (f q) x) := by
  have hDrep : ∀ᵐ q ∂(volume.restrict (Set.Ioc a r)),
      (((weightedMovingHeatL2Gradient eta c (r - q) (F q) :
          WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        weightedMovingHeatGradientEta eta c (r - q) (f q)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (Measure.ae_ne volume r).filter_mono ae_restrict_le] with q hq hqr
    have hlag : 0 < r - q := sub_pos.mpr (lt_of_le_of_ne hq.2 hqr)
    rw [weightedMovingHeatL2Gradient_of_pos hlag]
    exact (weightedMovingHeatGradientL2CLM_coe_ae hlag (F q)).trans
      (Eventually.of_forall fun x =>
        weightedMovingHeatGradientEta_congr_ae (hFrep q hq) x)
  exact wholeLineRealL2_intervalIntegral_coe_ae_of_local_prod_integrable
    har hDint hDrep hlocal

/-- Uniform exact-weight forcing control and strong measurability produce
the Bochner-integrable heat-gradient history.  The only endpoint
singularity is `(r-q)⁻¹ᐟ²`, which is integrable. -/
theorem weightedMovingHeatL2Gradient_intervalIntegrable_of_uniform_norm_bound
    {eta c a r K : ℝ} (har : a ≤ r) (_hK : 0 ≤ K)
    {F : ℝ → WholeLineRealL2}
    (hF : ∀ q ∈ Set.Icc a r, ‖F q‖ ≤ K)
    (hhist_meas : AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Gradient eta c (r - q) (F q))
      (volume.restrict (Set.Icc a r))) :
    IntervalIntegrable
      (fun q => weightedMovingHeatL2Gradient eta c (r - q) (F q))
      volume a r := by
  let A := weightedMovingHeatGradientHorizonConst eta c (r - a)
  have hA : 0 ≤ A :=
    weightedMovingHeatGradientHorizonConst_nonneg eta c (r - a)
  have hmajor : IntervalIntegrable
      (fun q : ℝ => A * K * (r - q) ^ (-(1 / 2 : ℝ)))
      volume a r := by
    exact (intervalIntegrable_sub_rpow_neg_half_between a r).const_mul
      (A * K)
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le har] at hmajor ⊢
  apply hmajor.mono' hhist_meas
  filter_upwards [ae_restrict_mem measurableSet_Icc] with q hq
  have hlag0 : 0 ≤ r - q := sub_nonneg.mpr hq.2
  have hlagH : r - q ≤ r - a := by linarith [hq.1]
  calc
    ‖weightedMovingHeatL2Gradient eta c (r - q) (F q)‖ ≤
        A * (r - q) ^ (-(1 / 2 : ℝ)) * ‖F q‖ := by
      exact weightedMovingHeatL2Gradient_apply_norm_le_rpow_neg_half
        hlag0 hlagH (F q)
    _ ≤ A * (r - q) ^ (-(1 / 2 : ℝ)) * K :=
      mul_le_mul_of_nonneg_left (hF q hq)
        (mul_nonneg hA (Real.rpow_nonneg hlag0 _))
    _ = A * K * (r - q) ^ (-(1 / 2 : ℝ)) := by ring

/-- Lift an a.e. pointwise differentiated mild restart to the canonical
`L²` gradient candidate.  This is the exact identification seam: it does
not assume the desired Hilbert equality, but only the scalar differentiated
restart and the Fubini data for its heat-gradient history. -/
theorem weightedMovingHeatFullGradientCandidate_eq_of_pointwise
    {eta c a r : ℝ} (har : a < r)
    {x₀ xr : ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    {X₀ Xr : WholeLineRealL2}
    {F : ℝ → WholeLineRealL2}
    (hX₀ : (((X₀ : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] x₀))
    (hXr : (((Xr : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] xr))
    (hFrep : ∀ q ∈ Set.Ioc a r,
      (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] f q))
    (hDint : IntervalIntegrable
      (fun q => weightedMovingHeatL2Gradient eta c (r - q) (F q))
      volume a r)
    (hlocal : ∀ A : Set ℝ, MeasurableSet A →
      (volume : Measure ℝ) A < ⊤ →
      Integrable
        (fun z : ℝ × ℝ => A.indicator
          (weightedMovingHeatGradientEta eta c (r - z.1) (f z.1)) z.2)
        ((volume.restrict (Set.Ioc a r)).prod volume))
    (hpoint : ∀ᵐ x ∂volume,
      xr x = weightedMovingHeatGradientEta eta c (r - a) x₀ x +
        ∫ q in a..r,
          weightedMovingHeatGradientEta eta c (r - q) (f q) x) :
    Xr = weightedMovingHeatFullGradientCandidate eta c a X₀ F r := by
  have hlag : 0 < r - a := sub_pos.mpr har
  have hhom :
      (((weightedMovingHeatL2Gradient eta c (r - a) X₀ :
          WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        weightedMovingHeatGradientEta eta c (r - a) x₀) := by
    rw [weightedMovingHeatL2Gradient_of_pos hlag]
    exact (weightedMovingHeatGradientL2CLM_coe_ae hlag X₀).trans
      (Eventually.of_forall fun x =>
        weightedMovingHeatGradientEta_congr_ae hX₀ x)
  have hduh := weightedMovingHeatL2Gradient_intervalIntegral_coe_ae
    har.le hFrep hDint hlocal
  unfold weightedMovingHeatFullGradientCandidate
  apply Lp.ext
  filter_upwards [hXr,
    Lp.coeFn_add
      (weightedMovingHeatL2Gradient eta c (r - a) X₀)
      (∫ q in a..r,
        weightedMovingHeatL2Gradient eta c (r - q) (F q)),
    hhom, hduh, hpoint] with x hxr hadd hhomx hduhx hpointx
  rw [hxr, hadd]
  simp only [Pi.add_apply]
  rw [hhomx, hduhx, hpointx]

/-- Specialization of the preceding identification seam to the actual
classical weighted population derivative.  Thus a scalar differentiated
restart immediately identifies the full heat-gradient candidate almost
everywhere with `paper5WeightedPopulationX`. -/
theorem weightedMovingHeatFullGradientCandidate_coe_ae_populationX_of_pointwise
    {eta c a r : ℝ} (har : a < r)
    {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {f : ℝ → ℝ → ℝ} {F : ℝ → WholeLineRealL2}
    (hWa_meas : AEStronglyMeasurable
      (paper5WeightedPopulation eta u U a) volume)
    (hWa_sq : Integrable (fun x : ℝ =>
      paper5WeightedPopulation eta u U a x ^ 2) volume)
    (hFrep : ∀ q ∈ Set.Ioc a r,
      (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] f q))
    (hDint : IntervalIntegrable
      (fun q => weightedMovingHeatL2Gradient eta c (r - q) (F q))
      volume a r)
    (hlocal : ∀ A : Set ℝ, MeasurableSet A →
      (volume : Measure ℝ) A < ⊤ →
      Integrable
        (fun z : ℝ × ℝ => A.indicator
          (weightedMovingHeatGradientEta eta c (r - z.1) (f z.1)) z.2)
        ((volume.restrict (Set.Ioc a r)).prod volume))
    (hpoint : ∀ᵐ x ∂volume,
      paper5WeightedPopulationX eta u U r x =
        weightedMovingHeatGradientEta eta c (r - a)
            (paper5WeightedPopulation eta u U a) x +
          ∫ q in a..r,
            weightedMovingHeatGradientEta eta c (r - q) (f q) x) :
    (((weightedMovingHeatFullGradientCandidate eta c a
          (wholeLineRealL2Total
            (paper5WeightedPopulation eta u U a)) F r :
        WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      paper5WeightedPopulationX eta u U r) := by
  let X₀ : WholeLineRealL2 :=
    wholeLineRealL2Total (paper5WeightedPopulation eta u U a)
  have hX₀ : ((X₀ : ℝ → ℝ) =ᵐ[volume]
      paper5WeightedPopulation eta u U a) :=
    wholeLineRealL2Total_coe_ae _ hWa_meas hWa_sq
  have hlag : 0 < r - a := sub_pos.mpr har
  have hhom :
      (((weightedMovingHeatL2Gradient eta c (r - a) X₀ :
          WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        weightedMovingHeatGradientEta eta c (r - a)
          (paper5WeightedPopulation eta u U a)) := by
    rw [weightedMovingHeatL2Gradient_of_pos hlag]
    exact (weightedMovingHeatGradientL2CLM_coe_ae hlag X₀).trans
      (Eventually.of_forall fun x =>
        weightedMovingHeatGradientEta_congr_ae hX₀ x)
  have hduh := weightedMovingHeatL2Gradient_intervalIntegral_coe_ae
    har.le hFrep hDint hlocal
  unfold weightedMovingHeatFullGradientCandidate
  filter_upwards [Lp.coeFn_add
      (weightedMovingHeatL2Gradient eta c (r - a) X₀)
      (∫ q in a..r,
        weightedMovingHeatL2Gradient eta c (r - q) (F q)),
    hhom, hduh, hpoint] with x hadd hhomx hduhx hpointx
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hhomx, hduhx, ← hpointx]

/-- Identification from the actual value restart and classical spatial
differentiation.  The only differentiation hypothesis on the Duhamel leg is
the standard heat-history derivative, produced above by an integrable local
majorant. -/
theorem weightedMovingHeatFullGradientCandidate_coe_ae_populationX_of_restart
    {eta c a r C : ℝ} (har : a < r)
    {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {f : ℝ → ℝ → ℝ} {F : ℝ → WholeLineRealL2}
    (hWa_meas : AEStronglyMeasurable
      (paper5WeightedPopulation eta u U a) volume)
    (hWa_sq : Integrable (fun x : ℝ =>
      paper5WeightedPopulation eta u U a x ^ 2) volume)
    (hWa_bound : ∀ y, |paper5WeightedPopulation eta u U a y| ≤ C)
    (hrestart : ∀ z,
      paper5WeightedPopulation eta u U r z =
        weightedMovingHeatEta eta c (r - a)
            (paper5WeightedPopulation eta u U a) z +
          weightedMovingHeatValueHistory eta c a r f z)
    (hWr_deriv : ∀ x, HasDerivAt
      (paper5WeightedPopulation eta u U r)
      (paper5WeightedPopulationX eta u U r x) x)
    (hhistory : ∀ x, HasDerivAt
      (weightedMovingHeatValueHistory eta c a r f)
      (weightedMovingHeatGradientHistory eta c a r f x) x)
    (hFrep : ∀ q ∈ Set.Ioc a r,
      (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] f q))
    (hDint : IntervalIntegrable
      (fun q => weightedMovingHeatL2Gradient eta c (r - q) (F q))
      volume a r)
    (hlocal : ∀ A : Set ℝ, MeasurableSet A →
      (volume : Measure ℝ) A < ⊤ →
      Integrable
        (fun z : ℝ × ℝ => A.indicator
          (weightedMovingHeatGradientEta eta c (r - z.1) (f z.1)) z.2)
        ((volume.restrict (Set.Ioc a r)).prod volume)) :
    (((weightedMovingHeatFullGradientCandidate eta c a
          (wholeLineRealL2Total
            (paper5WeightedPopulation eta u U a)) F r :
        WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      paper5WeightedPopulationX eta u U r) := by
  apply weightedMovingHeatFullGradientCandidate_coe_ae_populationX_of_pointwise
    har hWa_meas hWa_sq hFrep hDint hlocal
  exact Eventually.of_forall fun x => by
    have hx := weightedMovingHeat_fullGenerator_spatial_identity
      (eta := eta) (c := c) (x := x) har hrestart (hWr_deriv x)
        hWa_meas hWa_bound (hhistory x)
    simpa only [weightedMovingHeatGradientHistory] using hx

/-- Any concrete function represented almost everywhere by an element of
`WholeLineRealL2` has an integrable square. -/
theorem integrable_sq_of_wholeLineRealL2_ae_eq
    (Z : WholeLineRealL2) {w : ℝ → ℝ}
    (hrep : ((Z : ℝ → ℝ) =ᵐ[volume] w)) :
    Integrable (fun x : ℝ => w x ^ 2) volume := by
  have hZsq : Integrable (fun x : ℝ => Z x ^ 2) volume :=
    (memLp_two_iff_integrable_sq (Lp.memLp Z).1).1 (Lp.memLp Z)
  refine hZsq.congr ?_
  filter_upwards [hrep] with x hx
  exact congrArg (fun z : ℝ => z ^ 2) hx

/-- The pointwise differentiated restart also produces the desired terminal
square-integrability.  In particular, no terminal `L²` hypothesis for
`paper5WeightedPopulationX` is used in this conclusion. -/
theorem paper5WeightedPopulationX_sq_integrable_of_fullGradientCandidate_pointwise
    {eta c a r : ℝ} (har : a < r)
    {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {f : ℝ → ℝ → ℝ} {F : ℝ → WholeLineRealL2}
    (hWa_meas : AEStronglyMeasurable
      (paper5WeightedPopulation eta u U a) volume)
    (hWa_sq : Integrable (fun x : ℝ =>
      paper5WeightedPopulation eta u U a x ^ 2) volume)
    (hFrep : ∀ q ∈ Set.Ioc a r,
      (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] f q))
    (hDint : IntervalIntegrable
      (fun q => weightedMovingHeatL2Gradient eta c (r - q) (F q))
      volume a r)
    (hlocal : ∀ A : Set ℝ, MeasurableSet A →
      (volume : Measure ℝ) A < ⊤ →
      Integrable
        (fun z : ℝ × ℝ => A.indicator
          (weightedMovingHeatGradientEta eta c (r - z.1) (f z.1)) z.2)
        ((volume.restrict (Set.Ioc a r)).prod volume))
    (hpoint : ∀ᵐ x ∂volume,
      paper5WeightedPopulationX eta u U r x =
        weightedMovingHeatGradientEta eta c (r - a)
            (paper5WeightedPopulation eta u U a) x +
          ∫ q in a..r,
            weightedMovingHeatGradientEta eta c (r - q) (f q) x) :
    Integrable (fun x : ℝ =>
      paper5WeightedPopulationX eta u U r x ^ 2) volume := by
  let Z := weightedMovingHeatFullGradientCandidate eta c a
    (wholeLineRealL2Total (paper5WeightedPopulation eta u U a)) F r
  have hrep : ((Z : ℝ → ℝ) =ᵐ[volume]
      paper5WeightedPopulationX eta u U r) := by
    exact weightedMovingHeatFullGradientCandidate_coe_ae_populationX_of_pointwise
      har hWa_meas hWa_sq hFrep hDint hlocal hpoint
  exact integrable_sq_of_wholeLineRealL2_ae_eq Z hrep

/-- Concrete `hWx2` producer from a value-level full-generator restart.
Neither the terminal gradient nor a spatial derivative of the forcing is
assumed. -/
theorem paper5WeightedPopulationX_sq_integrable_of_fullGenerator_restart
    {eta c a r C : ℝ} (har : a < r)
    {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {f : ℝ → ℝ → ℝ} {F : ℝ → WholeLineRealL2}
    (hWa_meas : AEStronglyMeasurable
      (paper5WeightedPopulation eta u U a) volume)
    (hWa_sq : Integrable (fun x : ℝ =>
      paper5WeightedPopulation eta u U a x ^ 2) volume)
    (hWa_bound : ∀ y, |paper5WeightedPopulation eta u U a y| ≤ C)
    (hrestart : ∀ z,
      paper5WeightedPopulation eta u U r z =
        weightedMovingHeatEta eta c (r - a)
            (paper5WeightedPopulation eta u U a) z +
          weightedMovingHeatValueHistory eta c a r f z)
    (hWr_deriv : ∀ x, HasDerivAt
      (paper5WeightedPopulation eta u U r)
      (paper5WeightedPopulationX eta u U r x) x)
    (hhistory : ∀ x, HasDerivAt
      (weightedMovingHeatValueHistory eta c a r f)
      (weightedMovingHeatGradientHistory eta c a r f x) x)
    (hFrep : ∀ q ∈ Set.Ioc a r,
      (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] f q))
    (hDint : IntervalIntegrable
      (fun q => weightedMovingHeatL2Gradient eta c (r - q) (F q))
      volume a r)
    (hlocal : ∀ A : Set ℝ, MeasurableSet A →
      (volume : Measure ℝ) A < ⊤ →
      Integrable
        (fun z : ℝ × ℝ => A.indicator
          (weightedMovingHeatGradientEta eta c (r - z.1) (f z.1)) z.2)
        ((volume.restrict (Set.Ioc a r)).prod volume)) :
    Integrable (fun x : ℝ =>
      paper5WeightedPopulationX eta u U r x ^ 2) volume := by
  let Z := weightedMovingHeatFullGradientCandidate eta c a
    (wholeLineRealL2Total (paper5WeightedPopulation eta u U a)) F r
  apply integrable_sq_of_wholeLineRealL2_ae_eq Z
  exact weightedMovingHeatFullGradientCandidate_coe_ae_populationX_of_restart
    har hWa_meas hWa_sq hWa_bound hrestart hWr_deriv hhistory
      hFrep hDint hlocal

/-- The full spatial-gradient candidate is square-root Hölder on every
positive interior window.  The forcing is required only to be uniformly
bounded in the exact weighted `L²` space, together with the two Bochner
integrability statements which define the Duhamel histories. -/
theorem weightedMovingHeatFullGradientCandidate_sub_norm_le_sqrt
    {eta c a R s t delta K : ℝ}
    (hdelta : 0 < delta) (hK : 0 ≤ K)
    (haR : a < R)
    (hsInterior : a + delta ≤ s) (hst : s ≤ t) (htR : t ≤ R)
    (hstep : 0 < t - s)
    (hsmall : t - s ≤ min (delta / 2) 1)
    {F : ℝ → WholeLineRealL2} (Z₀ : WholeLineRealL2)
    (hF : ∀ q ∈ Set.Icc a R, ‖F q‖ ≤ K)
    (hTint : IntervalIntegrable
      (fun q => weightedMovingHeatL2Gradient eta c (t - q) (F q))
      volume a t)
    (hSint : IntervalIntegrable
      (fun q => weightedMovingHeatL2Gradient eta c (s - q) (F q))
      volume a s) :
    ‖weightedMovingHeatFullGradientCandidate eta c a Z₀ F t -
        weightedMovingHeatFullGradientCandidate eta c a Z₀ F s‖ ≤
      (weightedMovingHeatGradientTimeHorizonConst eta c (R - a) *
          (s - a) ^ (-(3 / 2 : ℝ)) * ‖Z₀‖ +
        5 * weightedMovingHeatGradientHorizonConst eta c (R - a) * K +
        2 * weightedMovingHeatGradientTimeHorizonConst eta c (R - a) * K) *
        Real.sqrt (t - s) := by
  have has : a ≤ s := by linarith
  have hr : 0 < s - a := by linarith
  have hh0 : 0 ≤ t - s := hstep.le
  have hrhR : (s - a) + (t - s) ≤ R - a := by linarith
  have hfar : a ≤ s - (t - s) := by
    have hhdelta : t - s ≤ delta / 2 :=
      hsmall.trans (min_le_left _ _)
    linarith
  have hhom0 :=
    weightedMovingHeatL2Gradient_sub_apply_norm_le_rpow_neg_three_half
      (eta := eta) (c := c) hr hh0 hrhR Z₀
  have hstep_one : t - s ≤ 1 := hsmall.trans (min_le_right _ _)
  have hle_sqrt : t - s ≤ Real.sqrt (t - s) := by
    rw [Real.le_sqrt' hstep]
    nlinarith
  have hH : 0 ≤ R - a := sub_nonneg.mpr haR.le
  have hB : 0 ≤
      weightedMovingHeatGradientTimeHorizonConst eta c (R - a) :=
    weightedMovingHeatGradientTimeHorizonConst_nonneg hH
  have hcoef : 0 ≤
      weightedMovingHeatGradientTimeHorizonConst eta c (R - a) *
        (s - a) ^ (-(3 / 2 : ℝ)) * ‖Z₀‖ := by positivity
  have hhom :
      ‖weightedMovingHeatL2Gradient eta c (t - a) Z₀ -
          weightedMovingHeatL2Gradient eta c (s - a) Z₀‖ ≤
        (weightedMovingHeatGradientTimeHorizonConst eta c (R - a) *
          (s - a) ^ (-(3 / 2 : ℝ)) * ‖Z₀‖) *
          Real.sqrt (t - s) := by
    calc
      ‖weightedMovingHeatL2Gradient eta c (t - a) Z₀ -
          weightedMovingHeatL2Gradient eta c (s - a) Z₀‖ =
          ‖weightedMovingHeatL2Gradient eta c
              ((s - a) + (t - s)) Z₀ -
            weightedMovingHeatL2Gradient eta c (s - a) Z₀‖ := by
        congr 3
        ring
      _ ≤ (weightedMovingHeatGradientTimeHorizonConst eta c (R - a) *
            (s - a) ^ (-(3 / 2 : ℝ)) * (t - s)) * ‖Z₀‖ := by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using hhom0
      _ = (weightedMovingHeatGradientTimeHorizonConst eta c (R - a) *
            (s - a) ^ (-(3 / 2 : ℝ)) * ‖Z₀‖) * (t - s) := by ring
      _ ≤ (weightedMovingHeatGradientTimeHorizonConst eta c (R - a) *
            (s - a) ^ (-(3 / 2 : ℝ)) * ‖Z₀‖) *
            Real.sqrt (t - s) :=
        mul_le_mul_of_nonneg_left hle_sqrt hcoef
  have hduh := weightedMovingHeatL2Gradient_duhamel_sub_norm_le_sqrt
    (eta := eta) (c := c) haR hK has hst htR hstep hfar
      hF hTint hSint
  unfold weightedMovingHeatFullGradientCandidate
  calc
    ‖(weightedMovingHeatL2Gradient eta c (t - a) Z₀ +
          ∫ q in a..t,
            weightedMovingHeatL2Gradient eta c (t - q) (F q)) -
        (weightedMovingHeatL2Gradient eta c (s - a) Z₀ +
          ∫ q in a..s,
            weightedMovingHeatL2Gradient eta c (s - q) (F q))‖ ≤
        ‖weightedMovingHeatL2Gradient eta c (t - a) Z₀ -
            weightedMovingHeatL2Gradient eta c (s - a) Z₀‖ +
          ‖(∫ q in a..t,
              weightedMovingHeatL2Gradient eta c (t - q) (F q)) -
            ∫ q in a..s,
              weightedMovingHeatL2Gradient eta c (s - q) (F q)‖ := by
      have hrearrange :
          (weightedMovingHeatL2Gradient eta c (t - a) Z₀ +
              ∫ q in a..t,
                weightedMovingHeatL2Gradient eta c (t - q) (F q)) -
            (weightedMovingHeatL2Gradient eta c (s - a) Z₀ +
              ∫ q in a..s,
                weightedMovingHeatL2Gradient eta c (s - q) (F q)) =
          (weightedMovingHeatL2Gradient eta c (t - a) Z₀ -
              weightedMovingHeatL2Gradient eta c (s - a) Z₀) +
            ((∫ q in a..t,
                weightedMovingHeatL2Gradient eta c (t - q) (F q)) -
              ∫ q in a..s,
                weightedMovingHeatL2Gradient eta c (s - q) (F q)) := by
        abel
      rw [hrearrange]
      exact norm_add_le _ _
    _ ≤ (weightedMovingHeatGradientTimeHorizonConst eta c (R - a) *
            (s - a) ^ (-(3 / 2 : ℝ)) * ‖Z₀‖) * Real.sqrt (t - s) +
        (5 * weightedMovingHeatGradientHorizonConst eta c (R - a) * K +
          2 * weightedMovingHeatGradientTimeHorizonConst eta c (R - a) * K) *
          Real.sqrt (t - s) := add_le_add hhom hduh
    _ = _ := by ring

/-- Measurable-history specialization of the full gradient modulus.  The
integrable inverse-square-root endpoint majorant is discharged internally. -/
theorem weightedMovingHeatFullGradientCandidate_sub_norm_le_sqrt_of_history_measurable
    {eta c a R s t delta K : ℝ}
    (hdelta : 0 < delta) (hK : 0 ≤ K)
    (haR : a < R)
    (hsInterior : a + delta ≤ s) (hst : s ≤ t) (htR : t ≤ R)
    (hstep : 0 < t - s)
    (hsmall : t - s ≤ min (delta / 2) 1)
    {F : ℝ → WholeLineRealL2} (Z₀ : WholeLineRealL2)
    (hF : ∀ q ∈ Set.Icc a R, ‖F q‖ ≤ K)
    (hhist_meas : ∀ r ∈ Set.Icc a R,
      AEStronglyMeasurable
        (fun q => weightedMovingHeatL2Gradient eta c (r - q) (F q))
        (volume.restrict (Set.Icc a r))) :
    ‖weightedMovingHeatFullGradientCandidate eta c a Z₀ F t -
        weightedMovingHeatFullGradientCandidate eta c a Z₀ F s‖ ≤
      (weightedMovingHeatGradientTimeHorizonConst eta c (R - a) *
          (s - a) ^ (-(3 / 2 : ℝ)) * ‖Z₀‖ +
        5 * weightedMovingHeatGradientHorizonConst eta c (R - a) * K +
        2 * weightedMovingHeatGradientTimeHorizonConst eta c (R - a) * K) *
        Real.sqrt (t - s) := by
  have has : a ≤ s := by linarith
  have hat : a ≤ t := has.trans hst
  have hsR : s ≤ R := hst.trans htR
  have hTint :=
    weightedMovingHeatL2Gradient_intervalIntegrable_of_uniform_norm_bound
      (eta := eta) (c := c) hat hK
      (fun q hq => hF q ⟨hq.1, hq.2.trans htR⟩)
      (hhist_meas t ⟨hat, htR⟩)
  have hSint :=
    weightedMovingHeatL2Gradient_intervalIntegrable_of_uniform_norm_bound
      (eta := eta) (c := c) has hK
      (fun q hq => hF q ⟨hq.1, hq.2.trans hsR⟩)
      (hhist_meas s ⟨has, hsR⟩)
  exact weightedMovingHeatFullGradientCandidate_sub_norm_le_sqrt
    hdelta hK haR hsInterior hst htR hstep hsmall Z₀ hF hTint hSint

section AxiomAudit

#print axioms weightedMovingHeatEta_spatial_hasDerivAt_of_bounded
#print axioms weightedMovingHeatGradientEta_abs_le_horizon_rpow_neg_half
#print axioms weightedMovingHeatValueHistory_hasDerivAt_of_dominated
#print axioms weightedMovingHeatValueHistory_hasDerivAt_of_uniform_bound
#print axioms weightedMovingHeat_fullGenerator_spatial_identity
#print axioms weightedMovingHeatGradientEta_congr_ae
#print axioms weightedMovingHeatL2Gradient_intervalIntegral_coe_ae
#print axioms
  weightedMovingHeatL2Gradient_intervalIntegrable_of_uniform_norm_bound
#print axioms weightedMovingHeatFullGradientCandidate_eq_of_pointwise
#print axioms
  weightedMovingHeatFullGradientCandidate_coe_ae_populationX_of_pointwise
#print axioms
  weightedMovingHeatFullGradientCandidate_coe_ae_populationX_of_restart
#print axioms integrable_sq_of_wholeLineRealL2_ae_eq
#print axioms
  paper5WeightedPopulationX_sq_integrable_of_fullGradientCandidate_pointwise
#print axioms
  paper5WeightedPopulationX_sq_integrable_of_fullGenerator_restart
#print axioms weightedMovingHeatFullGradientCandidate_sub_norm_le_sqrt
#print axioms
  weightedMovingHeatFullGradientCandidate_sub_norm_le_sqrt_of_history_measurable

end AxiomAudit

end ShenWork.Paper1
