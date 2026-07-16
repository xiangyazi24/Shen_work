import ShenWork.Paper1.WholeLineWeightedRegularityL2PointwiseIdentification
import ShenWork.Paper1.WholeLineWeightedRegularityL2Semigroup
import Mathlib.Analysis.Calculus.FDeriv.Extend

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Natural zero-time generator domain closure

The weighted Gaussian generator is already the ordinary derivative of the
weighted heat orbit at every positive lag.  This file records the endpoint
closure needed by the nonlinear restart argument: strong convergence of the
positive-lag generator regularizations implies a genuine right derivative of
the heat orbit at lag zero.  No spatial pointwise convergence of those
regularizations is required.
-/

/-- If the positive-lag weighted generator regularizations of one `L²` datum
converge strongly, then the datum belongs to the right generator domain of
the totalized weighted heat semigroup. -/
theorem weightedMovingHeatL2Semigroup_hasDerivWithinAt_zero_of_generator_tendsto
    {eta c : ℝ} {Z G : WholeLineRealL2}
    (hgen : Tendsto
      (fun r : ℝ => weightedMovingHeatL2Generator eta c r Z)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds G)) :
    HasDerivWithinAt
      (fun r : ℝ => weightedMovingHeatL2Semigroup eta c r Z) G
      (Set.Ici 0) 0 := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
      (s := Set.Ioi (0 : ℝ))
  · intro r hr
    exact (weightedMovingHeatL2Semigroup_orbit_hasDerivAt
      (eta := eta) (c := c) hr Z).differentiableAt.differentiableWithinAt
  · have hzero := weightedMovingHeatL2Semigroup_tendsto_zero eta c Z
    change Tendsto
      (fun r : ℝ => weightedMovingHeatL2Semigroup eta c r Z)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (weightedMovingHeatL2Semigroup eta c 0 Z))
    simpa only [weightedMovingHeatL2Semigroup_zero,
      ContinuousLinearMap.one_apply] using hzero
  · exact self_mem_nhdsWithin
  · refine hgen.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (weightedMovingHeatL2Semigroup_orbit_hasDerivAt
      (eta := eta) (c := c) hr Z).deriv.symm

/-- A concrete positive sequence converts a right Hilbert derivative into a
strong sequence of forward slopes.  This is the sequence form consumed by
the representative-identification lemma. -/
theorem hasDerivWithinAt_Ici_forwardSlope_sequence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : ℝ → E} {V : E} {t : ℝ}
    (hZ : HasDerivWithinAt Z V (Set.Ici t) t)
    {eps : ℕ → ℝ}
    (heps_pos : ∀ n, 0 < eps n)
    (heps : Tendsto eps atTop (nhds 0)) :
    Tendsto
      (fun n => (eps n)⁻¹ • (Z (t + eps n) - Z t))
      atTop (nhds V) := by
  have hslope := (hasDerivWithinAt_iff_tendsto_slope).1 hZ
  have hset : Set.Ici t \ {t} = Set.Ioi t := by
    ext x
    simp only [mem_diff, mem_Ici, mem_singleton_iff, mem_Ioi]
    constructor
    · rintro ⟨hxt, hxne⟩
      exact lt_of_le_of_ne hxt (Ne.symm hxne)
    · intro hxt
      exact ⟨hxt.le, ne_of_gt hxt⟩
  rw [hset] at hslope
  have hadd : Tendsto (fun n => t + eps n) atTop (nhds t) := by
    simpa only [add_zero] using tendsto_const_nhds.add heps
  have haddWithin : Tendsto (fun n => t + eps n) atTop
      (nhdsWithin t (Set.Ioi t)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hadd, ?_⟩
    exact Eventually.of_forall fun n => by
      simpa only [mem_Ioi, lt_add_iff_pos_right] using heps_pos n
  have hcomp := hslope.comp haddWithin
  have heq :
      (slope Z t ∘ fun n => t + eps n) =
        fun n => (eps n)⁻¹ • (Z (t + eps n) - Z t) := by
    funext n
    rw [Function.comp_apply, slope_def_module]
    simp only [add_sub_cancel_left]
  rw [← heq]
  exact hcomp

/-- A right strong derivative of canonical whole-line `L²` sections is
identified almost everywhere with an independently known classical
pointwise right derivative.  Only one explicit positive sequence is used;
there is no common spatial dominator. -/
theorem wholeLineRealL2Total_hasDerivWithinAt_coe_ae_of_pointwise
    {phi phi_t : ℝ → ℝ → ℝ} {t : ℝ} {V : WholeLineRealL2}
    (hphi_meas : ∀ n : ℕ,
      AEStronglyMeasurable (phi (t + ((n + 1 : ℕ) : ℝ)⁻¹)) volume)
    (hphi_sq : ∀ n : ℕ, Integrable (fun x : ℝ =>
      phi (t + ((n + 1 : ℕ) : ℝ)⁻¹) x ^ 2) volume)
    (hphi0_meas : AEStronglyMeasurable (phi t) volume)
    (hphi0_sq : Integrable (fun x : ℝ => phi t x ^ 2) volume)
    (hright : HasDerivWithinAt
      (fun s => wholeLineRealL2Total (phi s)) V (Set.Ici t) t)
    (hpoint : ∀ x, HasDerivAt (fun s => phi s x) (phi_t t x) t) :
    ((V : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] phi_t t := by
  let eps : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)⁻¹
  let Q : ℕ → WholeLineRealL2 := fun n =>
    (eps n)⁻¹ •
      (wholeLineRealL2Total (phi (t + eps n)) -
        wholeLineRealL2Total (phi t))
  let q : ℕ → ℝ → ℝ := fun n x =>
    (eps n)⁻¹ * (phi (t + eps n) x - phi t x)
  have heps_pos : ∀ n, 0 < eps n := by
    intro n
    dsimp only [eps]
    positivity
  have heps : Tendsto eps atTop (nhds 0) := by
    simpa only [eps, Nat.cast_add, Nat.cast_one, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0))
  have hQ : Tendsto Q atTop (nhds V) := by
    simpa only [Q] using
      hasDerivWithinAt_Ici_forwardSlope_sequence hright heps_pos heps
  have hrep : ∀ n, ((Q n : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] q n := by
    intro n
    have hplus := wholeLineRealL2Total_coe_ae
      (phi (t + eps n)) (by simpa only [eps] using hphi_meas n)
        (by simpa only [eps] using hphi_sq n)
    have hzero := wholeLineRealL2Total_coe_ae
      (phi t) hphi0_meas hphi0_sq
    filter_upwards [Lp.coeFn_sub
        (wholeLineRealL2Total (phi (t + eps n)))
        (wholeLineRealL2Total (phi t)),
      Lp.coeFn_smul (eps n)⁻¹
        (wholeLineRealL2Total (phi (t + eps n)) -
          wholeLineRealL2Total (phi t)),
      hplus, hzero] with x hsub hsmul hplusx hzerox
    dsimp only [Q, q]
    rw [hsmul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hplusx, hzerox]
  have hq : ∀ x, Tendsto (fun n => q n x) atTop (nhds (phi_t t x)) := by
    intro x
    have hslope := (hpoint x).tendsto_slope_zero_right
    have hepsWithin : Tendsto eps atTop (nhdsWithin 0 (Set.Ioi 0)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨heps, ?_⟩
      exact Eventually.of_forall fun n => heps_pos n
    have hcomp := hslope.comp hepsWithin
    simpa only [q, Function.comp_apply, smul_eq_mul] using hcomp
  exact wholeLineRealL2_limit_coe_ae_of_pointwise hQ hrep hq

section AxiomAudit

#print axioms
  weightedMovingHeatL2Semigroup_hasDerivWithinAt_zero_of_generator_tendsto
#print axioms hasDerivWithinAt_Ici_forwardSlope_sequence
#print axioms wholeLineRealL2Total_hasDerivWithinAt_coe_ae_of_pointwise

end AxiomAudit

end ShenWork.Paper1
