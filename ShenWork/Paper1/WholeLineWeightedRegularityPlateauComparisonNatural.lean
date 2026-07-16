import ShenWork.Paper1.WholeLineWeightedRegularityCoMovingComparisonNatural
import ShenWork.Paper1.WholeLineWeightedRegularityLeftTailBarrierNatural

open Filter Topology Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Concrete inputs for the dynamic lower-plateau comparison

The canonical restart supplies all classical parabolic regularity internally.
The final theorem pairs its exact evolution equation with the committed
stationary lower-plateau subsolution away from the `C¹` splice.
-/

/-- A positive-time canonical restart is jointly continuous on every closed
forward slab. -/
theorem wholeLineCauchyGlobal_coMovingRestart_continuousOn
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (c : ℝ) {t₀ T : ℝ} (ht₀ : 0 < t₀) :
    ContinuousOn
      (fun q : ℝ × ℝ =>
        wholeLineCauchyGlobalU p u₀ (t₀ + q.1)
          (q.2 + c * (t₀ + q.1)))
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set ℝ)) := by
  intro q hq
  have hphys : 0 < t₀ + q.1 := by linarith [hq.1.1]
  have hjoint := wholeLineCauchyGlobalU_joint_hasFDerivAt_positive
    p hregime u₀ hu₀ hphys
      (x := q.2 + c * (t₀ + q.1))
  have hmap : DifferentiableAt ℝ
      (fun r : ℝ × ℝ =>
        (t₀ + r.1, r.2 + c * (t₀ + r.1))) q := by
    fun_prop
  exact (hjoint.differentiableAt.comp q hmap).continuousAt.continuousWithinAt

/-- Every spatial slice of a positive-time canonical restart is `C²`. -/
theorem wholeLineCauchyGlobal_coMovingRestart_contDiff_two
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (c t₀ : ℝ) {t : ℝ} (ht : 0 < t₀ + t) :
    ContDiff ℝ 2 (fun x =>
      wholeLineCauchyGlobalU p u₀ (t₀ + t)
        (x + c * (t₀ + t))) := by
  simpa [coMovingPath] using
    wholeLineCauchyGlobalU_coMoving_contDiff_two_positive
      p hregime u₀ hu₀ (c := c) ht

/-- The exact canonical parabolic equation and the stationary patched
subsolution are simultaneously available on a restarted slab.  No
monotonicity of a time slice is assumed; the only spatial envelope used by
the existing Lemma 4.2 estimate is its nonmonotone `InWaveTrapSet` input. -/
theorem wholeLineCauchyGlobal_coMovingRestart_plateau_operator_pair
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {c t₀ T M kappaTilde D : ℝ}
    (ht₀ : 0 < t₀)
    (hcond : PaperLemma42ExactConditions
      p c (kappa c) kappaTilde M)
    (hD : paperDMin p.χ M (kappa c) kappaTilde p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (hplateau : ∀ x, lowerBarrierPlateau (kappa c) kappaTilde D x ≤
      constantSubsolutionThreshold p.χ (kappa c) kappaTilde D)
    (htrap : ∀ t ∈ Set.Icc (0 : ℝ) T,
      InWaveTrapSet (kappa c) M (fun x =>
        wholeLineCauchyGlobalU p u₀ (t₀ + t)
          (x + c * (t₀ + t)))) :
    ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ x,
      HasDerivAt
        (fun s => wholeLineCauchyGlobalU p u₀ (t₀ + s)
          (x + c * (t₀ + s)))
        (paperWaveOperator p c
          (fun y => wholeLineCauchyGlobalU p u₀ (t₀ + t)
            (y + c * (t₀ + t)))
          (fun y => wholeLineCauchyGlobalU p u₀ (t₀ + t)
            (y + c * (t₀ + t))) x) t ∧
      (x ≠ lowerBarrierXPlus (kappa c) kappaTilde D →
        0 ≤ paperWaveOperator p c
          (fun y => wholeLineCauchyGlobalU p u₀ (t₀ + t)
            (y + c * (t₀ + t)))
          (lowerBarrierPlateau (kappa c) kappaTilde D) x) := by
  intro t ht x
  have hphys : 0 < t₀ + t := ht₀.trans_le (le_add_of_nonneg_right ht.1.le)
  constructor
  · exact wholeLineCauchyGlobal_coMovingRestart_hasDerivAt_paperWaveOperator
      p hregime u₀ hu₀ c t₀ hphys x
  · intro hx
    exact paperWaveOperator_lowerBarrierPlateau_nonneg_chiNonpos_away
      p hcond hD hD1 hplateau (htrap t ⟨ht.1.le, ht.2⟩) hx

#print axioms wholeLineCauchyGlobal_coMovingRestart_continuousOn
#print axioms wholeLineCauchyGlobal_coMovingRestart_contDiff_two
#print axioms wholeLineCauchyGlobal_coMovingRestart_plateau_operator_pair

end ShenWork.Paper1

