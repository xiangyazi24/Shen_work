import ShenWork.Paper1.Theorem12EnergyProducer
import ShenWork.Paper1.WholeLineCauchyGlobalGluing
import ShenWork.Paper1.WavePositiveLeftEndpoint

open Filter Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Available global-Cauchy inputs for the corrected Step 4 energy argument

This file records exactly the fields that the canonical global BUC solution
already supplies to the corrected Section 5 energy producer.  It deliberately
does not package the still-missing weighted Sobolev propagation, dominated
time differentiation, or Step 4 compactness statements as assumptions.
-/

theorem wholeLineCauchyGlobal_coMoving_slice_isCUnifBdd
    (p : CMParams) (u₀ : WholeLineBUC) (c t : ℝ) :
    IsCUnifBdd (coMovingPath c (wholeLineCauchyGlobalU p u₀) t) := by
  apply isCUnifBdd_comp_add_const
  exact WholeLineBUC.isCUnifBdd (wholeLineCauchyGlobalBUC p u₀ t)

theorem wholeLineCauchyGlobal_coMoving_mem_Icc_stableCeiling
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    coMovingPath c (wholeLineCauchyGlobalU p u₀) t x ∈
      Set.Icc (0 : ℝ) (wholeLineCauchyStableCeiling p u₀) := by
  constructor
  · exact wholeLineCauchyGlobal_nonnegative p hregime u₀ hu₀ ht (x + c * t)
  · exact wholeLineCauchyGlobal_le_stableCeiling
      p hregime u₀ hu₀ ht (x + c * t)

theorem wholeLineCauchyGlobal_coMovingV_eq_frozenElliptic
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    coMovingPath c (wholeLineCauchyGlobalV p u₀) t =
      frozenElliptic p
        (coMovingPath c (wholeLineCauchyGlobalU p u₀) t) := by
  have huC : IsCUnifBdd (wholeLineCauchyGlobalU p u₀ t) :=
    WholeLineBUC.isCUnifBdd (wholeLineCauchyGlobalBUC p u₀ t)
  have hu0 : ∀ x, 0 ≤ wholeLineCauchyGlobalU p u₀ t x :=
    fun x => wholeLineCauchyGlobal_nonnegative p hregime u₀ hu₀ ht x
  change
    (fun x => frozenElliptic p (wholeLineCauchyGlobalU p u₀ t)
        (x + c * t)) =
      frozenElliptic p
        (fun x => wholeLineCauchyGlobalU p u₀ t (x + c * t))
  exact (frozenElliptic_comp_add_const_fun p huC hu0 (c * t)).symm

theorem wholeLineCauchyGlobal_weightedEnergy_control
    (p : CMParams) (u₀ : WholeLineBUC) (η c : ℝ) (U : ℝ → ℝ) :
    ∀ᶠ t in atTop,
      coMovingWeightedL2Energy η c (wholeLineCauchyGlobalU p u₀) U t ≤
        paper5WeightedEnergy η c (wholeLineCauchyGlobalU p u₀) U t := by
  filter_upwards [] with t
  exact (paper5WeightedEnergy_eq_coMovingWeightedL2Energy
    η c (wholeLineCauchyGlobalU p u₀) U t).symm.le

/-- The complete nonnegative-global/frame-control fragment currently
available for the canonical BUC solution.  The omitted fields are precisely
the analytic producers that cannot be obtained from the present classical
solution interface alone. -/
theorem wholeLineCauchyGlobal_step4Energy_available_data
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (η c : ℝ) (U : ℝ → ℝ) :
    let u := wholeLineCauchyGlobalU p u₀
    let v := wholeLineCauchyGlobalV p u₀
    let E := paper5WeightedEnergy η c u U
    IsGlobalNonnegativeCauchySolutionFrom p u₀.1 u v ∧
      (∀ᶠ t in atTop, coMovingWeightedL2Energy η c u U t ≤ E t) ∧
      (∀ t, IsCUnifBdd (coMovingPath c u t)) ∧
      (∀ t, 0 ≤ t → ∀ x,
        coMovingPath c u t x ∈
          Set.Icc (0 : ℝ) (wholeLineCauchyStableCeiling p u₀)) ∧
      (∀ t, 0 ≤ t →
        coMovingPath c v t = frozenElliptic p (coMovingPath c u t)) := by
  dsimp only
  refine ⟨wholeLineCauchyGlobal_isGlobalNonnegativeCauchySolutionFrom
      p hregime u₀ hu₀, wholeLineCauchyGlobal_weightedEnergy_control
      p u₀ η c U, ?_, ?_, ?_⟩
  · exact fun t => wholeLineCauchyGlobal_coMoving_slice_isCUnifBdd p u₀ c t
  · exact fun t ht x =>
      wholeLineCauchyGlobal_coMoving_mem_Icc_stableCeiling
        p hregime u₀ hu₀ c ht x
  · exact fun t ht => wholeLineCauchyGlobal_coMovingV_eq_frozenElliptic
      p hregime u₀ hu₀ c ht

/-- Function-level specialization for the paper's actual BUC datum class.
This is the strongest direct bridge from the global construction toward the
`hcore` surface: it gives a nonnegative global solution and a (possibly large)
uniform ceiling, but makes no claim that the ceiling is close enough to
`MChi p` for the corrected quadratic to remain negative. -/
theorem paperNonnegativeInitialDatum_step4Energy_available_data
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : ℝ → ℝ) (hu₀ : PaperNonnegativeInitialDatum u₀)
    (η c : ℝ) (U : ℝ → ℝ) :
    ∃ u v : ℝ → ℝ → ℝ, ∃ E : ℝ → ℝ, ∃ M : ℝ,
      IsGlobalNonnegativeCauchySolutionFrom p u₀ u v ∧
      (∀ᶠ t in atTop, coMovingWeightedL2Energy η c u U t ≤ E t) ∧
      (∀ t, IsCUnifBdd (coMovingPath c u t)) ∧
      (∀ t, 0 ≤ t → ∀ x, coMovingPath c u t x ∈ Set.Icc (0 : ℝ) M) ∧
      (∀ t, 0 ≤ t →
        coMovingPath c v t = frozenElliptic p (coMovingPath c u t)) := by
  let w : WholeLineBUC := wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1
  have hw0 : ∀ x, 0 ≤ w.1 x := by
    intro x
    simpa [w] using hu₀.2 x
  have hdata := wholeLineCauchyGlobal_step4Energy_available_data
    p hregime w hw0 η c U
  refine ⟨wholeLineCauchyGlobalU p w, wholeLineCauchyGlobalV p w,
    paper5WeightedEnergy η c (wholeLineCauchyGlobalU p w) U,
    wholeLineCauchyStableCeiling p w, ?_⟩
  simpa [w] using hdata

section Theorem12Step4EnergyProducerAxiomAudit

#print axioms wholeLineCauchyGlobal_coMoving_slice_isCUnifBdd
#print axioms wholeLineCauchyGlobal_coMoving_mem_Icc_stableCeiling
#print axioms wholeLineCauchyGlobal_coMovingV_eq_frozenElliptic
#print axioms wholeLineCauchyGlobal_weightedEnergy_control
#print axioms wholeLineCauchyGlobal_step4Energy_available_data
#print axioms paperNonnegativeInitialDatum_step4Energy_available_data

end Theorem12Step4EnergyProducerAxiomAudit

end ShenWork.Paper1
