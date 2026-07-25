import ShenWork.Paper1.WholeLineChiPosEntropyFarLeftNormalFamily
import ShenWork.Paper1.WholeLineMaximalBUCConstruction

/-!
# Ceiling-free far-left bands

The persistent plateau gives the lower half of the far-left band without any
ceiling assumption.  This file isolates the complementary input as an
arbitrary global upper bound, and records exactly how a uniform bound on a
global maximal BUC orbit would supply it.  No `WholeLineCauchyCeilingRegime`
is used.
-/

open Filter Set

noncomputable section

namespace ShenWork.Paper1

/-- Plateau persistence plus any global upper bound gives the zeroth-order
far-left band.  This is the ceiling-free replacement for
`exists_eventualCoMovingLeftBand_of_persistent_plateau`. -/
theorem exists_eventualCoMovingLeftBand_of_persistent_plateau_of_global_upper
    (p : CMParams) (u₀ : WholeLineBUC)
    {N : ℕ} {c kappa kappaTilde D M : ℝ}
    (hkappa : 0 < kappa) (hgap : kappa < kappaTilde) (hD : 1 ≤ D)
    (hpersist : ∀ n : ℕ, N ≤ n →
      ∀ r ∈ Set.Icc (0 : ℝ) (wholeLineCauchyGlobalStep p u₀), ∀ x,
        lowerBarrierPlateau kappa kappaTilde D x ≤
          wholeLineCauchyGlobalU p u₀
            (((n : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀ + r)
            (x + c * (((n : ℝ) + 1) *
              wholeLineCauchyGlobalStep p u₀ + r)))
    (hupper : ∀ t, 0 ≤ t → ∀ x, wholeLineCauchyGlobalU p u₀ t x ≤ M) :
    ∃ ell : ℝ, 0 < ell ∧
      EventualCoMovingLeftBand c ell M (wholeLineCauchyGlobalU p u₀) := by
  obtain ⟨T, R, ell, hell, hlower⟩ :=
    wholeLineCauchyGlobal_eventual_coMoving_left_floor_of_persistent_plateau
      p u₀ hkappa hgap hD hpersist
  refine ⟨ell, hell, max T 0, R, ?_⟩
  intro t ht z hz
  have hT : T ≤ t := (le_max_left T 0).trans ht
  have ht0 : 0 ≤ t := (le_max_right T 0).trans ht
  constructor
  · simpa only [coMovingPath] using hlower t hT z hz
  · simpa only [coMovingPath] using hupper t ht0 (z + c * t)

/-- The ceiling-free maximal construction and an a-priori orbit bound produce
one global maximal orbit with a pointwise upper bound. -/
theorem exists_global_maximalBUCOrbit_with_uniform_upper
    (p : CMParams) (hapriori : WholeLineLargeChiAPrioriBound p)
    (u₀ : ℝ → ℝ) (hu₀ : PaperNonnegativeInitialDatum u₀) :
    ∃ (U : ℝ → WholeLineBUC) (C : ℝ),
      IsWholeLineMaximalBUCOrbit p u₀ (⊤ : WithTop ℝ) U ∧
        ∀ t, 0 ≤ t → ∀ x, (U t).1 x ≤ C := by
  obtain ⟨Tmax, U, horbit⟩ := wholeLineMaximalBUCImport_constructed p u₀ hu₀
  obtain ⟨C, hC⟩ := hapriori u₀ hu₀ Tmax U horbit
  have htop : Tmax = ⊤ := horbit.2.2.2.2.2.2.2 ⟨C, hC⟩
  subst Tmax
  refine ⟨U, C, horbit, ?_⟩
  intro t ht x
  exact (WholeLineBUC.apply_le_norm (U t) x).trans
    (hC t ht (WithTop.coe_lt_top t))

/-- Exact identification bridge needed to transfer the maximal-orbit bound to
the historical fixed-ceiling canonical glue. -/
def CanonicalMaximalBUCIdentification
    (p : CMParams) (u₀ : WholeLineBUC) (U : ℝ → WholeLineBUC) : Prop :=
  ∀ t, 0 ≤ t → wholeLineCauchyGlobalBUC p u₀ t = U t

/-- Once the identification bridge is known, a maximal-orbit norm bound is a
global upper bound for the historical canonical orbit. -/
theorem canonical_global_upper_of_maximal_identification
    {p : CMParams} {u₀ : WholeLineBUC} {U : ℝ → WholeLineBUC} {C : ℝ}
    (hid : CanonicalMaximalBUCIdentification p u₀ U)
    (hC : ∀ t, 0 ≤ t → ‖U t‖ ≤ C) :
    ∀ t, 0 ≤ t → ∀ x, wholeLineCauchyGlobalU p u₀ t x ≤ C := by
  intro t ht x
  have heq := congrArg (fun w : WholeLineBUC => w.1 x) (hid t ht)
  change (wholeLineCauchyGlobalBUC p u₀ t).1 x ≤ C
  calc
    (wholeLineCauchyGlobalBUC p u₀ t).1 x = (U t).1 x := heq
    _ ≤ ‖U t‖ := WholeLineBUC.apply_le_norm (U t) x
    _ ≤ C := hC t ht

/-- Plateau persistence, a global maximal orbit bound, and the precise
canonical/maximal identification give the desired canonical far-left band. -/
theorem exists_eventualCoMovingLeftBand_of_persistent_plateau_of_maximal_identification
    (p : CMParams) (u₀ : WholeLineBUC)
    {U : ℝ → WholeLineBUC} {C : ℝ}
    (hid : CanonicalMaximalBUCIdentification p u₀ U)
    (hC : ∀ t, 0 ≤ t → ‖U t‖ ≤ C)
    {N : ℕ} {c kappa kappaTilde D : ℝ}
    (hkappa : 0 < kappa) (hgap : kappa < kappaTilde) (hD : 1 ≤ D)
    (hpersist : ∀ n : ℕ, N ≤ n →
      ∀ r ∈ Set.Icc (0 : ℝ) (wholeLineCauchyGlobalStep p u₀), ∀ x,
        lowerBarrierPlateau kappa kappaTilde D x ≤
          wholeLineCauchyGlobalU p u₀
            (((n : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀ + r)
            (x + c * (((n : ℝ) + 1) *
              wholeLineCauchyGlobalStep p u₀ + r))) :
    ∃ ell : ℝ, 0 < ell ∧
      EventualCoMovingLeftBand c ell C (wholeLineCauchyGlobalU p u₀) := by
  exact exists_eventualCoMovingLeftBand_of_persistent_plateau_of_global_upper
    p u₀ hkappa hgap hD hpersist
      (canonical_global_upper_of_maximal_identification hid hC)

section AxiomAudit

#print axioms
  exists_eventualCoMovingLeftBand_of_persistent_plateau_of_global_upper
#print axioms exists_global_maximalBUCOrbit_with_uniform_upper
#print axioms canonical_global_upper_of_maximal_identification
#print axioms
  exists_eventualCoMovingLeftBand_of_persistent_plateau_of_maximal_identification

end AxiomAudit

end ShenWork.Paper1
