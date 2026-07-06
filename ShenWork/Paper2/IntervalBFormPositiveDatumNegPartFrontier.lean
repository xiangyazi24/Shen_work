import ShenWork.Paper2.IntervalBFormDirectClassical

open Filter Topology Set

open ShenWork.IntervalDomain
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData conjugatePicardLimit)
open ShenWork.IntervalMildToClassical
  (mildChemicalConcentration)
open ShenWork.Paper2
open ShenWork.Paper2.BFormDirectClassical

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-!
This additive file records the honest positive-datum B-form frontier needed to
replace the old `hlocal` hypothesis in the general-χ B-form headline.

The analytic route intended for the frontier is the negative-part route:
construct the B-form map with the chemotactic power truncated at `u₊`, use the
algebraic cancellation `(u₊)^m u₋ = 0` as the pointwise core of the weak
negative-part estimate, obtain `u ≥ 0`, then use the strong maximum principle to
recover strict closed-interval positivity and deactivate the truncation.  The
scalar cancellation is proved below; the PDE-level negative-part estimate and
strong maximum-principle upgrade are exposed as named frontier fields, rather
than smuggled in through the false `PositiveInitialDatum → PaperPositiveInitialDatum`
conversion.
-/

/-- Negative part of a scalar. -/
def negativePart (r : ℝ) : ℝ := max (-r) 0

lemma negativePart_nonneg (r : ℝ) : 0 ≤ negativePart r := by
  exact le_max_right (-r) 0

lemma le_negativePart_neg (r : ℝ) : -r ≤ negativePart r := by
  exact le_max_left (-r) 0

lemma negativePart_eq_zero_of_nonneg {r : ℝ} (hr : 0 ≤ r) :
    negativePart r = 0 := by
  simp [negativePart, hr]

lemma negativePart_eq_zero_iff {r : ℝ} :
    negativePart r = 0 ↔ 0 ≤ r := by
  constructor
  · intro h
    have hle : -r ≤ negativePart r := le_negativePart_neg r
    rw [h] at hle
    linarith
  · exact negativePart_eq_zero_of_nonneg

lemma positivePart_mul_negativePart_eq_zero (r : ℝ) :
    positivePart r * negativePart r = 0 := by
  by_cases hr : 0 < r
  · have hneg : negativePart r = 0 :=
      negativePart_eq_zero_of_nonneg (le_of_lt hr)
    simp [hneg]
  · have hpos : positivePart r = 0 :=
      positivePart_eq_zero_of_nonpos (le_of_not_gt hr)
    simp [hpos]

/-- Scalar core of the weak negative-part cancellation:
`(u₊)^m u₋ = 0` for `m > 0`. -/
lemma positivePart_rpow_mul_negativePart_eq_zero {m r : ℝ} (hm : 0 < m) :
    (positivePart r) ^ m * negativePart r = 0 := by
  by_cases hr : 0 < r
  · have hneg : negativePart r = 0 :=
      negativePart_eq_zero_of_nonneg (le_of_lt hr)
    simp [hneg]
  · have hpos : positivePart r = 0 :=
      positivePart_eq_zero_of_nonpos (le_of_not_gt hr)
    have hm_ne : m ≠ 0 := ne_of_gt hm
    simp [hpos, Real.zero_rpow hm_ne]

/-- The truncated chemotactic power used in the positive-datum route. -/
def truncatedChemotacticPower (p : CM2Params) (r : ℝ) : ℝ :=
  (positivePart r) ^ p.m

lemma truncatedChemotacticPower_zero (p : CM2Params) :
    truncatedChemotacticPower p 0 = 0 := by
  simp [truncatedChemotacticPower, positivePart, Real.zero_rpow (ne_of_gt p.hm)]

lemma truncatedChemotacticPower_mul_negativePart_eq_zero
    (p : CM2Params) (r : ℝ) :
    truncatedChemotacticPower p r * negativePart r = 0 := by
  exact positivePart_rpow_mul_negativePart_eq_zero p.hm

/-- PDE-level positivity certificate for the boundary-vanishing datum route.

`negativePart_zero` is the formal endpoint of the weak negative-part energy
estimate for the truncated B-form problem.  `strictPos` is the strong maximum
principle upgrade after nonnegativity.  `hpde_u` is the original B-form
equation after the truncation is inactive. -/
structure BFormNegativePartPositivityRoute
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) where
  datum : PositiveInitialDatum intervalDomain u₀
  negativePart_zero :
    ∀ t, 0 < t → t ≤ DB.T → ∀ x : intervalDomainPoint,
      negativePart (conjugatePicardLimit p u₀ DB.T t x) = 0
  strictPos :
    ∀ t x, 0 < t → t < DB.T →
      0 < conjugatePicardLimit p u₀ DB.T t x
  hpde_u :
    ∀ t x, 0 < t → t < DB.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv (conjugatePicardLimit p u₀ DB.T) t x =
        intervalDomain.laplacian
            ((conjugatePicardLimit p u₀ DB.T) t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p
              ((conjugatePicardLimit p u₀ DB.T) t)
              (mildChemicalConcentration p
                (conjugatePicardLimit p u₀ DB.T) t) x
          + (conjugatePicardLimit p u₀ DB.T) t x
            * (p.a - p.b *
              ((conjugatePicardLimit p u₀ DB.T) t x) ^ p.α)

theorem BFormNegativePartPositivityRoute.nonneg
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (R : BFormNegativePartPositivityRoute p DB) :
    ∀ t, 0 < t → t ≤ DB.T → ∀ x : intervalDomainPoint,
      0 ≤ conjugatePicardLimit p u₀ DB.T t x := by
  intro t ht htT x
  exact (negativePart_eq_zero_iff.mp (R.negativePart_zero t ht htT x))

theorem BFormNegativePartPositivityRoute.truncation_inactive
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (R : BFormNegativePartPositivityRoute p DB) :
    ∀ t, 0 < t → t ≤ DB.T → ∀ x : intervalDomainPoint,
      positivePart (conjugatePicardLimit p u₀ DB.T t x)
        = conjugatePicardLimit p u₀ DB.T t x := by
  intro t ht htT x
  exact positivePart_eq_self_of_nonneg (R.nonneg t ht htT x)

/-- B-form classical frontier for positive data, with the solution fixed to the
canonical B-form Picard limit and its elliptic resolver. -/
structure BFormPositiveClassicalFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) where
  route : BFormNegativePartPositivityRoute p DB
  regularity :
    intervalDomain.classicalRegularity DB.T
      (conjugatePicardLimit p u₀ DB.T)
      (mildChemicalConcentration p
        (conjugatePicardLimit p u₀ DB.T))
  v_nonneg :
    ∀ t x, 0 < t → t < DB.T →
      0 ≤ mildChemicalConcentration p
        (conjugatePicardLimit p u₀ DB.T) t x
  hpde_v :
    ∀ t x, 0 < t → t < DB.T → x ∈ intervalDomain.inside →
      0 = intervalDomain.laplacian
            ((mildChemicalConcentration p
              (conjugatePicardLimit p u₀ DB.T)) t) x
          - p.μ *
            (mildChemicalConcentration p
              (conjugatePicardLimit p u₀ DB.T)) t x
          + p.ν *
            ((conjugatePicardLimit p u₀ DB.T) t x) ^ p.γ
  neumann :
    ∀ t x, 0 < t → t < DB.T → x ∈ intervalDomain.boundary →
      intervalDomain.normalDeriv
          ((conjugatePicardLimit p u₀ DB.T) t) x = 0 ∧
        intervalDomain.normalDeriv
          ((mildChemicalConcentration p
            (conjugatePicardLimit p u₀ DB.T)) t) x = 0

theorem isClassicalSolution_of_BFormPositiveClassicalFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormPositiveClassicalFrontier p DB) :
    IsPaper2ClassicalSolution intervalDomain p DB.T
      (conjugatePicardLimit p u₀ DB.T)
      (mildChemicalConcentration p
        (conjugatePicardLimit p u₀ DB.T)) := by
  exact IsPaper2ClassicalSolution.of_components DB.hT F.regularity
    F.route.strictPos F.v_nonneg F.route.hpde_u F.hpde_v F.neumann

theorem localClassicalSolution_of_BFormPositiveClassicalFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormPositiveClassicalFrontier p DB) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u₀ u := by
  refine ⟨DB.T, DB.hT,
    conjugatePicardLimit p u₀ DB.T,
    mildChemicalConcentration p (conjugatePicardLimit p u₀ DB.T), ?_⟩
  exact ⟨isClassicalSolution_of_BFormPositiveClassicalFrontier F,
    ShenWork.Paper2.BFormInitialTrace.conjugatePicardLimit_initialTrace_of_conjugate_data
      p F.route.datum.admissible.2 DB⟩

/-- Per-datum B-form frontier for the boundary-vanishing
`PositiveInitialDatum` class. -/
def BFormPositiveLocalFrontier (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomainPoint → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
      ∃ DB : ConjugateMildExistenceData p u₀,
        Nonempty (BFormPositiveClassicalFrontier p DB)

/-- Per-datum B-form frontier for the paper-positive datum class.

This is the datum-faithful analogue of `BFormPositiveLocalFrontier` for
component packages whose constructors require the uniform closed-domain floor
carried by `PaperPositiveInitialDatum`. -/
def BFormPaperPositiveLocalFrontier (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomainPoint → ℝ,
    PaperPositiveInitialDatum intervalDomain u₀ →
      ∃ DB : ConjugateMildExistenceData p u₀,
        Nonempty (BFormPositiveClassicalFrontier p DB)

/-- Local existence for the full `PositiveInitialDatum` class from the
negative-part B-form frontier.  This is the replacement for the old `hlocal`
hypothesis; it does not pass through `PaperPositiveInitialDatum`. -/
theorem positiveDatum_localExistence_of_BForm
    {p : CM2Params}
    (hPerDatum : BFormPositiveLocalFrontier p) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨DB, ⟨F⟩⟩ := hPerDatum u₀ hu₀
  exact localClassicalSolution_of_BFormPositiveClassicalFrontier F

/-- General-χ B-form headline with the old `hlocal` frontier narrowed to the
positive-datum B-form negative-part frontier. -/
theorem paper2_theorem_1_1_general_chi_bform_negpart
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hPerDatum : BFormPositiveLocalFrontier p)
    (hUniform : IntervalDomainUniformLocalExistence p) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bform
    p hχ ha hb hγ_ge_one
    (positiveDatum_localExistence_of_BForm hPerDatum) hUniform

#print axioms negativePart_eq_zero_iff
#print axioms positivePart_mul_negativePart_eq_zero
#print axioms positivePart_rpow_mul_negativePart_eq_zero
#print axioms truncatedChemotacticPower_zero
#print axioms truncatedChemotacticPower_mul_negativePart_eq_zero
#print axioms BFormNegativePartPositivityRoute.nonneg
#print axioms BFormNegativePartPositivityRoute.truncation_inactive
#print axioms isClassicalSolution_of_BFormPositiveClassicalFrontier
#print axioms localClassicalSolution_of_BFormPositiveClassicalFrontier
#print axioms positiveDatum_localExistence_of_BForm
#print axioms paper2_theorem_1_1_general_chi_bform_negpart

end ShenWork.Paper2.BFormPositiveDatumNegPart
