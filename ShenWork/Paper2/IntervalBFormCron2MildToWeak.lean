import ShenWork.Paper2.IntervalBFormCron2BNDuality

open MeasureTheory
open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
  (intervalNeumannFullKernel intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData conjugatePicardLimit)

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-!
This additive file isolates the honest remaining mild-to-weak frontier.

The proved theorem `bN_duality_regular` discharges the chemotaxis duality at
each positive lag `t - s`.  The only analytic input still not present in the
tree is the Neumann semigroup weak Duhamel identity that turns the tested mild
formula, after those lagwise B_N dualities, into the local-in-time weak PDE.

The final theorem below shows exactly how that remaining semigroup identity
implies the original `TruncatedMildToWeakAvailable` interface.
-/

/-- Weak local PDE restricted to a specified test-function class.  This is the
satisfiable version of `TruncatedWeakLocalPDE`; the original frontier quantifies
over all `φ : ℝ → ℝ`, so a later bridge to that interface must explain why every
admissible `φ` lies in the chosen class. -/
def TruncatedWeakLocalPDEOn (p : CM2Params) (T : ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (Test : (ℝ → ℝ) → Prop) : Prop :=
  ∀ t, 0 < t → t ≤ T → ∀ φ : ℝ → ℝ, Test φ →
    (∫ x,
        intervalDomainLift
            (fun z : intervalDomainPoint =>
              intervalDomain.timeDeriv u t z) x * φ x
        ∂ intervalMeasure 1)
      + (∫ x,
          deriv (intervalDomainLift (u t)) x * deriv φ x
          ∂ intervalMeasure 1)
      =
    p.χ₀ *
        (∫ x,
          truncatedChemFluxLifted p (u t) x * deriv φ x
          ∂ intervalMeasure 1)
      + (∫ x, truncatedLogisticLifted p (u t) x * φ x
          ∂ intervalMeasure 1)

/-- The lagwise B_N duality needed inside the Duhamel convolution. -/
def TruncatedBNDualityForTestAt (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (t s : ℝ) (φ : ℝ → ℝ) : Prop :=
  (∫ x,
      intervalConjugateKernelOperator (t - s)
        (truncatedChemFluxLifted p (u s)) x * φ x
      ∂ intervalMeasure 1)
    =
  -(∫ y,
      truncatedChemFluxLifted p (u s) y *
        deriv (fun z : ℝ =>
          intervalFullSemigroupOperator (t - s) φ z) y
      ∂ intervalMeasure 1)

/-- The proved regular B_N adjoint identity, specialized to the truncated flux
appearing in the cron2 mild map. -/
theorem truncated_bN_duality_regular_at
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {t s : ℝ} {φ : ℝ → ℝ} (hst : s < t)
    (hF_int : Integrable
      (fun q : ℝ × ℝ =>
        deriv
            (fun y' : ℝ =>
              intervalNeumannFullKernel (t - s) q.1 y') q.2
          * truncatedChemFluxLifted p (u s) q.2 * φ q.1)
      ((intervalMeasure 1).prod (intervalMeasure 1)))
    (hS_deriv : ∀ y : ℝ,
      deriv
          (fun z : ℝ =>
            intervalFullSemigroupOperator (t - s) φ z) y
        =
      ∫ x,
        deriv
            (fun z : ℝ =>
              intervalNeumannFullKernel (t - s) z x) y * φ x
        ∂ intervalMeasure 1) :
    TruncatedBNDualityForTestAt p u t s φ := by
  have hτ : 0 < t - s := sub_pos.mpr hst
  simpa [TruncatedBNDualityForTestAt] using
    (bN_duality_regular (τ := t - s) hτ
      (truncatedChemFluxLifted p (u s)) φ hF_int hS_deriv)

/-- Remaining semigroup weak identity after the lagwise B_N duality has been
made available.  This is the precise current stall: it is a Duhamel/Neumann
semigroup weak differentiation theorem, not a chemotaxis-duality gap. -/
def TruncatedMildSemigroupWeakAfterBNDualityOn
    (p : CM2Params) (T : ℝ) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (Test : (ℝ → ℝ) → Prop) : Prop :=
  TruncatedConjugateMildSolution p T u₀ u →
    ∀ t, 0 < t → t ≤ T → ∀ φ : ℝ → ℝ, Test φ →
      (∀ s, 0 < s → s < t → TruncatedBNDualityForTestAt p u t s φ) →
        (∫ x,
            intervalDomainLift
                (fun z : intervalDomainPoint =>
                  intervalDomain.timeDeriv u t z) x * φ x
            ∂ intervalMeasure 1)
          + (∫ x,
              deriv (intervalDomainLift (u t)) x * deriv φ x
              ∂ intervalMeasure 1)
          =
        p.χ₀ *
            (∫ x,
              truncatedChemFluxLifted p (u t) x * deriv φ x
              ∂ intervalMeasure 1)
          + (∫ x, truncatedLogisticLifted p (u t) x * φ x
              ∂ intervalMeasure 1)

/-- Minimal regular data needed to turn the truncated mild fixed point into the
weak local PDE on a chosen test-function class.  The first two fields are the
regular hypotheses consumed by `bN_duality_regular`; the third field is the
semigroup weak Duhamel identity that is still absent from the tree. -/
structure TruncatedMildToWeakRegularData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀)
    (Test : (ℝ → ℝ) → Prop) : Prop where
  bN_fubini_integrable :
    ∀ t, 0 < t → t ≤ DB.T → ∀ φ : ℝ → ℝ, Test φ →
      ∀ s, 0 < s → s < t →
        Integrable
          (fun q : ℝ × ℝ =>
            deriv
                (fun y' : ℝ =>
                  intervalNeumannFullKernel (t - s) q.1 y') q.2
              * truncatedChemFluxLifted p
                  (conjugatePicardLimit p u₀ DB.T s) q.2 * φ q.1)
          ((intervalMeasure 1).prod (intervalMeasure 1))
  bN_semigroup_deriv :
    ∀ t, 0 < t → t ≤ DB.T → ∀ φ : ℝ → ℝ, Test φ →
      ∀ s, 0 < s → s < t → ∀ y : ℝ,
        deriv
            (fun z : ℝ =>
              intervalFullSemigroupOperator (t - s) φ z) y
          =
        ∫ x,
          deriv
              (fun z : ℝ =>
                intervalNeumannFullKernel (t - s) z x) y * φ x
          ∂ intervalMeasure 1
  semigroup_weak :
    TruncatedMildSemigroupWeakAfterBNDualityOn p DB.T u₀
      (conjugatePicardLimit p u₀ DB.T) Test

/-- The regular B_N theorem plus the semigroup weak identity yield the weak PDE
for the selected test-function class. -/
theorem truncatedWeakLocalPDEOn_of_regularData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    {Test : (ℝ → ℝ) → Prop}
    (H : TruncatedMildToWeakRegularData p DB Test)
    (hmild : TruncatedConjugateMildSolution p DB.T u₀
      (conjugatePicardLimit p u₀ DB.T)) :
    TruncatedWeakLocalPDEOn p DB.T
      (conjugatePicardLimit p u₀ DB.T) Test := by
  intro t ht htT φ hφ
  exact H.semigroup_weak hmild t ht htT φ hφ
    (fun s hs hst =>
      truncated_bN_duality_regular_at (p := p)
        (u := conjugatePicardLimit p u₀ DB.T) (t := t) (s := s)
        (φ := φ) hst
        (H.bN_fubini_integrable t ht htT φ hφ s hs hst)
        (H.bN_semigroup_deriv t ht htT φ hφ s hs hst))

/-- Bridge back to the original all-test-function frontier.  The extra
`all_tests` premise is exactly the price of the old interface quantifying over
arbitrary `φ : ℝ → ℝ`; for a Sobolev/smooth test class this is the remaining
interface mismatch, not a B_N-duality gap. -/
theorem truncatedMildToWeakAvailable_of_regularData_allTests
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    {Test : (ℝ → ℝ) → Prop}
    (H : TruncatedMildToWeakRegularData p DB Test)
    (all_tests : ∀ φ : ℝ → ℝ, Test φ) :
    TruncatedMildToWeakAvailable p DB := by
  intro hmild t ht htT φ
  exact truncatedWeakLocalPDEOn_of_regularData H hmild t ht htT φ (all_tests φ)

end ShenWork.Paper2.BFormPositiveDatumNegPart
