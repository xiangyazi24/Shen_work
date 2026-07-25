import ShenWork.Paper1.WholeLineChiPosStage3FourThird
import ShenWork.Paper1.WholeLineChiPosEntropyClassicalCompactness
import ShenWork.Paper1.WholeLineMaximalBUCConstruction
import ShenWork.Paper1.WholeLineChiPosCeilingFreeFarLeftBand

/-!
# What the ceiling-free `chi < 4` continuation actually closes

The maximal physical BUC orbit is global and uniformly bounded for normalized
parameters and a datum with a positive left plateau.  This file also records
a structural mismatch in the current canonical parabolic-compactness target:
its translated sequence is required to be classical for every translated
time, including the artificial negative-time extension of the canonical
orbit.  Consequently that target already forces spatial differentiability of
the raw initial datum, which is not part of the paper datum interface.
-/

open Filter Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-- Ceiling-free construction of a global uniformly bounded physical maximal
orbit throughout the normalized strict range `chi < 4`. -/
theorem exists_global_maximalBUCOrbit_with_uniform_band_upto_four_atLeft
    (p : CMParams) (hm : p.m = 1) (hgamma : p.γ = 1)
    (halpha : p.α = 1)
    (hχ : 0 ≤ p.χ) (hχfour : p.χ < 4)
    (u₀ : ℝ → ℝ) (hu₀ : PaperNonnegativeInitialDatum u₀)
    (hleft : StrictlyPositiveAtLeft u₀) :
    ∃ (U : ℝ → WholeLineBUC) (C : ℝ),
      IsWholeLineMaximalBUCOrbit p u₀ (⊤ : WithTop ℝ) U ∧
        ∀ t, 0 ≤ t → ∀ x, 0 ≤ (U t).1 x ∧ (U t).1 x ≤ C := by
  obtain ⟨Tmax, U, horbit⟩ :=
    wholeLineMaximalBUCImport_constructed p u₀ hu₀
  have hapriori : WholeLineLargeChiAPrioriBoundAtLeft p :=
    wholeLineLargeChiAPrioriBoundAtLeft_upto_four
      p hm hgamma halpha hχ hχfour
  obtain ⟨C, hC⟩ := hapriori u₀ hu₀ hleft Tmax U horbit
  have htop : Tmax = ⊤ := horbit.2.2.2.2.2.2.2 ⟨C, hC⟩
  subst Tmax
  refine ⟨U, C, horbit, ?_⟩
  intro t ht x
  constructor
  · exact horbit.2.2.2.2.2.2.1 t x ht (WithTop.coe_lt_top t)
  · exact (WholeLineBUC.apply_le_norm (U t) x).trans
      (hC t ht (WithTop.coe_lt_top t))

/-- Once the missing identification with the historical canonical glue is
supplied, the new maximal-orbit estimate and a persistent plateau give the
full canonical zeroth-order far-left band for `chi < 4`. -/
theorem
    exists_canonical_eventualCoMovingLeftBand_upto_four_of_identification
    (p : CMParams) (hm : p.m = 1) (hgamma : p.γ = 1)
    (halpha : p.α = 1)
    (hχ : 0 ≤ p.χ) (hχfour : p.χ < 4)
    (u₀ : WholeLineBUC)
    (hu₀ : PaperNonnegativeInitialDatum u₀.1)
    (hleft : StrictlyPositiveAtLeft u₀.1)
    (hidentify : ∀ U : ℝ → WholeLineBUC,
      IsWholeLineMaximalBUCOrbit p u₀.1 (⊤ : WithTop ℝ) U →
        CanonicalMaximalBUCIdentification p u₀ U)
    {N : ℕ} {c kappa kappaTilde D : ℝ}
    (hkappa : 0 < kappa) (hgap : kappa < kappaTilde) (hD : 1 ≤ D)
    (hpersist : ∀ n : ℕ, N ≤ n →
      ∀ r ∈ Set.Icc (0 : ℝ) (wholeLineCauchyGlobalStep p u₀), ∀ x,
        lowerBarrierPlateau kappa kappaTilde D x ≤
          wholeLineCauchyGlobalU p u₀
            (((n : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀ + r)
            (x + c * (((n : ℝ) + 1) *
              wholeLineCauchyGlobalStep p u₀ + r))) :
    ∃ ell M : ℝ, 0 < ell ∧
      EventualCoMovingLeftBand c ell M
        (wholeLineCauchyGlobalU p u₀) := by
  obtain ⟨U, C, horbit, hUC⟩ :=
    exists_global_maximalBUCOrbit_with_uniform_band_upto_four_atLeft
      p hm hgamma halpha hχ hχfour u₀.1 hu₀ hleft
  have hid := hidentify U horbit
  have hupper : ∀ t, 0 ≤ t → ∀ x,
      wholeLineCauchyGlobalU p u₀ t x ≤ C := by
    intro t ht x
    have heq := congrArg (fun w : WholeLineBUC => w.1 x) (hid t ht)
    change (wholeLineCauchyGlobalBUC p u₀ t).1 x ≤ C
    exact heq.trans_le (hUC t ht x).2
  obtain ⟨ell, hell, hband⟩ :=
    exists_eventualCoMovingLeftBand_of_persistent_plateau_of_global_upper
      p u₀ hkappa hgap hD hpersist hupper
  exact ⟨ell, C, hell, hband⟩

/-! ## The current canonical compactness target sees negative time -/

/-- The exact `ChiOneClassicalSequenceData` currently used by canonical
parabolic compactness forces the artificial negative-time initial slice to be
spatially differentiable.  This follows already from the zeroth member of the
translation sequence `timeShift n = n`, `spaceShift n = -n`; it is unrelated
to any late-time parabolic smoothing estimate. -/
theorem differentiable_negative_initial_slice_of_canonicalParabolicCompactness
    {p : CMParams} {chi c ell k : ℝ} {u₀ : WholeLineBUC}
    (H : CanonicalChiOneFarLeftParabolicCompactness
      p chi c ell k u₀) :
    ∀ x : ℝ, DifferentiableAt ℝ (fun y : ℝ => u₀.1 (y - c)) x := by
  let timeShift : ℕ → ℝ := fun n => n
  let spaceShift : ℕ → ℝ := fun n => -(n : ℝ)
  have htime : ∀ n : ℕ, (n : ℝ) ≤ timeShift n := by
    intro n
    rfl
  have hspace : ∀ n : ℕ, spaceShift n ≤ -(n : ℝ) := by
    intro n
    rfl
  obtain ⟨ux, uxx, ut, r, rx, rxx, Hseq⟩ :=
    H.translatedData timeShift spaceShift htime hspace
  intro x
  have hd := (Hseq.u_space_deriv 0 (-1) x).differentiableAt
  have heq :
      chiOneFarLeftTranslate c (wholeLineCauchyGlobalU p u₀)
          timeShift spaceShift 0 (-1) =
        fun y : ℝ => u₀.1 (y - c) := by
    funext y
    simp only [timeShift, spaceShift, chiOneFarLeftTranslate, coMovingPath,
      Nat.cast_zero, neg_zero, zero_add, wholeLineCauchyGlobalU,
      wholeLineCauchyGlobalBUC]
    rw [if_neg (by norm_num : ¬ (0 : ℝ) ≤ -1)]
    congr 1
    ring
  rw [heq] at hd
  exact hd

/-- A pointwise failure of differentiability of the shifted datum therefore
refutes the present canonical compactness target before one reaches any
Arzelà--Ascoli estimate. -/
theorem not_canonicalParabolicCompactness_of_nondifferentiable_initial_slice
    {p : CMParams} {chi c ell k : ℝ} {u₀ : WholeLineBUC} {x : ℝ}
    (hnot : ¬ DifferentiableAt ℝ (fun y : ℝ => u₀.1 (y - c)) x) :
    ¬ CanonicalChiOneFarLeftParabolicCompactness p chi c ell k u₀ := by
  intro H
  exact hnot
    (differentiable_negative_initial_slice_of_canonicalParabolicCompactness
      H x)

/-! ## Correct positive-time interior estimate still missing -/

/-- The one-sided, eventually-on-compact-box form of the genuine remaining
parabolic estimate.  Unlike `ChiOneClassicalSequenceData`, it does not ask
finite translated prefixes to be classical at artificial negative times.

The two `SpaceTimeLocallyPrecompact` fields are the precise uniform
positive-time interior requirement: boundedness and a common space-time
modulus for `u_xx` and `u_t`.  Existing local `C^2` files prove existence,
continuity, and compact-window bounds, but do not produce this modulus
uniformly over all late translates. -/
def ChiOneFarLeftEventualSecondJetEstimate
    (c : ℝ) (orbit : ℝ → ℝ → ℝ) : Prop :=
  ∀ (timeShift spaceShift : ℕ → ℝ),
    (∀ n : ℕ, (n : ℝ) ≤ timeShift n) →
    (∀ n : ℕ, spaceShift n ≤ -(n : ℝ)) →
    ∃ (ux uxx ut : ℕ → ℝ → ℝ → ℝ),
      SpaceTimeLocallyPrecompact uxx ∧
      SpaceTimeLocallyPrecompact ut ∧
      ∀ R > 0, ∀ᶠ n in atTop,
        ∀ t ∈ Set.Icc (-R) R, ∀ x ∈ Set.Icc (-R) R,
          HasDerivAt
              (chiOneFarLeftTranslate c orbit timeShift spaceShift n t)
              (ux n t x) x ∧
            HasDerivAt (ux n t) (uxx n t x) x ∧
            HasDerivAt
              (fun s => chiOneFarLeftTranslate c orbit
                timeShift spaceShift n s x)
              (ut n t x) t

/-- The current (over-strong) canonical compactness target contains the
correct eventual second-jet estimate as a projection. -/
theorem eventualSecondJetEstimate_of_canonicalParabolicCompactness
    {p : CMParams} {chi c ell k : ℝ} {u₀ : WholeLineBUC}
    (H : CanonicalChiOneFarLeftParabolicCompactness
      p chi c ell k u₀) :
    ChiOneFarLeftEventualSecondJetEstimate c
      (wholeLineCauchyGlobalU p u₀) := by
  intro timeShift spaceShift htime hspace
  obtain ⟨ux, uxx, ut, r, rx, rxx, Hseq⟩ :=
    H.translatedData timeShift spaceShift htime hspace
  refine ⟨ux, uxx, ut, Hseq.uxx_precompact, Hseq.ut_precompact, ?_⟩
  intro R hR
  filter_upwards [] with n
  intro t ht x hx
  exact ⟨Hseq.u_space_deriv n t x, Hseq.ux_space_deriv n t x,
    Hseq.u_time_deriv n t x⟩

section AxiomAudit

#print axioms
  exists_global_maximalBUCOrbit_with_uniform_band_upto_four_atLeft
#print axioms
  exists_canonical_eventualCoMovingLeftBand_upto_four_of_identification
#print axioms
  differentiable_negative_initial_slice_of_canonicalParabolicCompactness
#print axioms
  not_canonicalParabolicCompactness_of_nondifferentiable_initial_slice
#print axioms
  eventualSecondJetEstimate_of_canonicalParabolicCompactness

end AxiomAudit

end ShenWork.Paper1
