import ShenWork.Paper1.WholeLineWeightedRegularitySecondDerivClosure
import ShenWork.Paper1.WholeLineWeightedRegularityScalarEnergyUpgrade

open Filter MeasureTheory Set Topology
open scoped RealInnerProductSpace

noncomputable section

namespace ShenWork.Paper1

/-!
# Scalar pairing for the exact weighted generator

The spatial generator need not be a strongly continuous `L²` trajectory.
For the quadratic energy it is enough to rewrite its pairing with the state
by whole-line integration by parts.  The resulting scalar expression only
uses the `L²` norms of the state and its first spatial derivative.
-/

/-- A pointwise realization of the full conjugated spatial generator has
the expected Hilbert-space pairing with the weighted population. -/
theorem paper5WeightedPopulation_inner_spatialGenerator_eq
    {eta c t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {Z X A : WholeLineRealL2}
    (hu2 : ContDiff ℝ 2 (coMovingPath c u t))
    (hU2 : ContDiff ℝ 2 U)
    (hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) *
        |coMovingPath c u t x - U x| ^ 2))
    (hWx2 : Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2))
    (hZrep : ((Z : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      paper5WeightedPopulation eta (coMovingPath c u) U t)
    (hXrep : ((X : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      paper5WeightedPopulationX eta (coMovingPath c u) U t)
    (hArep : ((A : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      fun x =>
        paper5WeightedPopulationXX eta (coMovingPath c u) U t x +
          (c - 2 * eta) *
            paper5WeightedPopulationX eta (coMovingPath c u) U t x +
          (eta ^ 2 - c * eta) *
            paper5WeightedPopulation eta (coMovingPath c u) U t x) :
    ⟪Z, A⟫ = -‖X‖ ^ 2 + (eta ^ 2 - c * eta) * ‖Z‖ ^ 2 := by
  let W : ℝ → ℝ :=
    paper5WeightedPopulation eta (coMovingPath c u) U t
  let Wx : ℝ → ℝ :=
    paper5WeightedPopulationX eta (coMovingPath c u) U t
  let Wxx : ℝ → ℝ :=
    paper5WeightedPopulationXX eta (coMovingPath c u) U t
  let G : ℝ → ℝ := fun x =>
    Wxx x + (c - 2 * eta) * Wx x + (eta ^ 2 - c * eta) * W x
  have hA2 : Integrable (fun x : ℝ => ((A : WholeLineRealL2) x) ^ 2)
      volume :=
    (memLp_two_iff_integrable_sq (Lp.memLp A).1).1 (Lp.memLp A)
  have hG2 : Integrable (fun x : ℝ => G x ^ 2) volume := by
    apply hA2.congr
    filter_upwards [hArep] with x hx
    simp only [G, W, Wx, Wxx, hx]
  obtain ⟨hWxx2, _hWxWxx, hWWxx, hibp⟩ :=
    paper5WeightedPopulation_diffusion_data_of_spatialGenerator_sq
      hu2 hU2 hclose hWx2 hG2
  have hWWxx' : Integrable (fun x : ℝ => W x * Wxx x) volume := by
    simpa only [W, Wxx] using hWWxx
  have hW2 : Integrable (fun x : ℝ => W x ^ 2) volume := by
    simpa only [W] using
      paper5WeightedPopulation_sq_integrable_of_weighted_difference hclose
  obtain ⟨hWxW, _hdiffBot, _hdiffTop, hdriftBot, hdriftTop⟩ :=
    paper5WeightedPopulation_spatial_product_data
      hu2 hU2 hW2 hWx2 hWWxx
  have hdrift : (∫ x : ℝ, Wx x * W x) = 0 := by
    exact paper5WeightedPopulation_driftIntegral_eq_zero
      (hu2.of_le (by norm_num)) (hU2.of_le (by norm_num))
      hWxW hdriftBot hdriftTop
  have hW_Wx : Integrable (fun x : ℝ => W x * Wx x) volume := by
    simpa only [mul_comm] using hWxW
  have hW_W : Integrable (fun x : ℝ => W x * W x) volume := by
    simpa only [pow_two] using hW2
  have hW_dWx : Integrable
      (fun x : ℝ => W x * ((c - 2 * eta) * Wx x)) volume := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      hW_Wx.const_mul (c - 2 * eta)
  have hW_kW : Integrable
      (fun x : ℝ => W x * ((eta ^ 2 - c * eta) * W x)) volume := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      hW_W.const_mul (eta ^ 2 - c * eta)
  have hdInt :
      (∫ x : ℝ, W x * ((c - 2 * eta) * Wx x)) =
        (c - 2 * eta) * (∫ x : ℝ, W x * Wx x) := by
    rw [show (fun x : ℝ => W x * ((c - 2 * eta) * Wx x)) =
        fun x => (c - 2 * eta) * (W x * Wx x) by
      funext x
      ring,
      integral_const_mul]
  have hkInt :
      (∫ x : ℝ, W x * ((eta ^ 2 - c * eta) * W x)) =
        (eta ^ 2 - c * eta) * (∫ x : ℝ, W x * W x) := by
    rw [show (fun x : ℝ => W x * ((eta ^ 2 - c * eta) * W x)) =
        fun x => (eta ^ 2 - c * eta) * (W x * W x) by
      funext x
      ring,
      integral_const_mul]
  have hexpand :
      (∫ x : ℝ, W x * G x) =
        (∫ x : ℝ, W x * Wxx x) +
          (c - 2 * eta) * (∫ x : ℝ, W x * Wx x) +
          (eta ^ 2 - c * eta) * (∫ x : ℝ, W x * W x) := by
    have hs1 :
        (∫ x : ℝ, (W x * Wxx x +
            W x * ((c - 2 * eta) * Wx x)) +
          W x * ((eta ^ 2 - c * eta) * W x)) =
        (∫ x : ℝ, W x * Wxx x +
          W x * ((c - 2 * eta) * Wx x)) +
        ∫ x : ℝ, W x * ((eta ^ 2 - c * eta) * W x) := by
      exact integral_add (hWWxx'.add hW_dWx) hW_kW
    have hs2 :
        (∫ x : ℝ, W x * Wxx x +
          W x * ((c - 2 * eta) * Wx x)) =
        (∫ x : ℝ, W x * Wxx x) +
          ∫ x : ℝ, W x * ((c - 2 * eta) * Wx x) := by
      exact integral_add hWWxx' hW_dWx
    calc
      (∫ x : ℝ, W x * G x) =
          ∫ x : ℝ, (W x * Wxx x +
              W x * ((c - 2 * eta) * Wx x)) +
            W x * ((eta ^ 2 - c * eta) * W x) := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [G]
        ring
      _ = (∫ x : ℝ, W x * Wxx x +
            W x * ((c - 2 * eta) * Wx x)) +
          ∫ x : ℝ, W x * ((eta ^ 2 - c * eta) * W x) := hs1
      _ = ((∫ x : ℝ, W x * Wxx x) +
            ∫ x : ℝ, W x * ((c - 2 * eta) * Wx x)) +
          ∫ x : ℝ, W x * ((eta ^ 2 - c * eta) * W x) := by rw [hs2]
      _ = (∫ x : ℝ, W x * Wxx x) +
          (c - 2 * eta) * (∫ x : ℝ, W x * Wx x) +
          (eta ^ 2 - c * eta) * (∫ x : ℝ, W x * W x) := by
        rw [hdInt, hkInt]
  have hinnerA : (∫ x : ℝ, W x * G x) = ⟪Z, A⟫ := by
    exact wholeLineIntegral_mul_eq_inner_of_aeEq Z A
      (by simpa only [W] using hZrep) (by simpa only [G, W, Wx, Wxx] using hArep)
  have hinnerX : (∫ x : ℝ, Wx x * Wx x) = ‖X‖ ^ 2 := by
    have h := wholeLineIntegral_mul_eq_inner_of_aeEq X X
      (by simpa only [Wx] using hXrep) (by simpa only [Wx] using hXrep)
    rwa [real_inner_self_eq_norm_sq] at h
  have hinnerZ : (∫ x : ℝ, W x * W x) = ‖Z‖ ^ 2 := by
    have h := wholeLineIntegral_mul_eq_inner_of_aeEq Z Z
      (by simpa only [W] using hZrep) (by simpa only [W] using hZrep)
    rwa [real_inner_self_eq_norm_sq] at h
  have hdrift' : (∫ x : ℝ, W x * Wx x) = 0 := by
    simpa only [mul_comm] using hdrift
  have hibp' : (∫ x : ℝ, W x * Wxx x) =
      -∫ x : ℝ, Wx x * Wx x := by
    simpa only [W, Wx, Wxx, pow_two] using hibp
  calc
    ⟪Z, A⟫ = ∫ x : ℝ, W x * G x := hinnerA.symm
    _ = (∫ x : ℝ, W x * Wxx x) +
          (c - 2 * eta) * (∫ x : ℝ, W x * Wx x) +
          (eta ^ 2 - c * eta) * (∫ x : ℝ, W x * W x) := hexpand
    _ = -(∫ x : ℝ, Wx x * Wx x) +
          (eta ^ 2 - c * eta) * (∫ x : ℝ, W x * W x) := by
      rw [hibp', hdrift']
      ring
    _ = -‖X‖ ^ 2 + (eta ^ 2 - c * eta) * ‖Z‖ ^ 2 := by
      rw [hinnerX, hinnerZ]

/-- Once the generator pairing has the integration-by-parts form, continuity
of the state, first derivative, and forcing gives continuity of the scalar
pairing needed by the right-derivative fencing argument. -/
theorem wholeLineRealL2_inner_generator_add_forcing_continuousAt
    {Z X A F : ℝ → WholeLineRealL2} {k q : ℝ}
    (hZ : ContinuousAt Z q) (hX : ContinuousAt X q)
    (hF : ContinuousAt F q)
    (henergy : ∀ᶠ s in nhds q,
      ⟪Z s, A s⟫ = -‖X s‖ ^ 2 + k * ‖Z s‖ ^ 2) :
    ContinuousAt (fun s => ⟪Z s, A s + F s⟫) q := by
  let R : ℝ → ℝ := fun s =>
    -‖X s‖ ^ 2 + k * ‖Z s‖ ^ 2 + ⟪Z s, F s⟫
  have hR : ContinuousAt R q := by
    dsimp only [R]
    fun_prop
  apply hR.congr_of_eventuallyEq
  filter_upwards [henergy] with s hs
  rw [inner_add_right, hs]

section AxiomAudit

#print axioms paper5WeightedPopulation_inner_spatialGenerator_eq
#print axioms wholeLineRealL2_inner_generator_add_forcing_continuousAt

end AxiomAudit

end ShenWork.Paper1
