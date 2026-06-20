import ShenWork.Paper2.IntervalBFormCron2RegularNegativePartEnergy

open Filter Topology Set MeasureTheory
open scoped Topology

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator)

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-!
Constructor for the remaining semigroup-weak Duhamel atom.

The fields below are deliberately standard heat-semigroup facts, stated at the
negative-part test actually used by the energy argument.  They are the textbook
Neumann semigroup/Duhamel ingredients not currently available as Mathlib
theorems in this project:

* the `t^{-1/2}` gradient smoothing bound;
* the endpoint Lebesgue-point facts for the ordinary and divergence Duhamel
  terms;
* dominated-convergence majorants for the weak differentiation step;
* the three tested weak identities for the homogeneous, ordinary-source, and
  `H^{-1}` chemotaxis Duhamel legs.

No universal B_N duality is assumed here.  The chemotaxis Duhamel field consumes
only the lagwise `TruncatedBNDualityForTestAt` supplied by the restricted
regular B_N theorem.
-/

/-- Homogeneous Neumann heat leg in the truncated mild formula. -/
def negativePartInitialHeatLeg
    (u₀ : intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  intervalFullSemigroupOperator t (intervalDomainLift u₀) x

/-- Chemotaxis B-form Duhamel leg before multiplying by `-χ₀`. -/
def negativePartChemotaxisDuhamelLeg
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (t x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t,
    intervalConjugateKernelOperator (t - s)
      (truncatedChemFluxLifted p (u s)) x

/-- Ordinary logistic-source Duhamel leg. -/
def negativePartLogisticDuhamelLeg
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (t x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t,
    intervalFullSemigroupOperator (t - s)
      (truncatedLogisticLifted p (u s)) x

/-- Tested weak contribution of one scalar-in-space leg. -/
def negativePartTestedLegWeakContribution
    (w : ℝ → ℝ → ℝ) (t : ℝ) (φ : ℝ → ℝ) : ℝ :=
  (∫ x, deriv (fun r : ℝ => w r x) t * φ x ∂ intervalMeasure 1)
    + (∫ x, deriv (w t) x * deriv φ x ∂ intervalMeasure 1)

/-- Left side of the negative-part tested weak PDE. -/
def negativePartTestedWeakLHS
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) : ℝ :=
  (∫ x,
      intervalDomainLift
          (fun z : intervalDomainPoint =>
            intervalDomain.timeDeriv u t z) x * negativePartTest u t x
      ∂ intervalMeasure 1)
    + (∫ x,
        deriv (intervalDomainLift (u t)) x * deriv (negativePartTest u t) x
        ∂ intervalMeasure 1)

/-- Chemotaxis endpoint term in the negative-part tested weak PDE. -/
def negativePartChemWeakTerm
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) : ℝ :=
  ∫ x,
    truncatedChemFluxLifted p (u t) x * deriv (negativePartTest u t) x
    ∂ intervalMeasure 1

/-- Logistic endpoint term in the negative-part tested weak PDE. -/
def negativePartLogisticWeakTerm
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) : ℝ :=
  ∫ x, truncatedLogisticLifted p (u t) x * negativePartTest u t x
    ∂ intervalMeasure 1

/-- SATISFIABLE standard heat-semigroup fact, currently a Mathlib/project gap:
`‖∂ₓ S_N(τ)f‖₂ ≤ C τ^{-1/2} ‖f‖₂` on the unit interval. -/
def NeumannHeatGradientTMinusHalfBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ τ, 0 < τ → ∀ f : ℝ → ℝ,
      Real.sqrt
          (∫ x,
            (deriv (fun z : ℝ => intervalFullSemigroupOperator τ f z) x) ^ 2
            ∂ intervalMeasure 1)
        ≤ C * τ ^ (-(1 / 2 : ℝ)) *
          Real.sqrt (∫ x, (f x) ^ 2 ∂ intervalMeasure 1)

/-- SATISFIABLE standard endpoint fact for ordinary `L²` Duhamel forcing at
Lebesgue points. -/
def HeatDuhamelEndpointLebesguePointFact
    (F : ℝ → ℝ → ℝ) (φ : ℝ → ℝ) (t : ℝ) : Prop :=
  Tendsto
    (fun h : ℝ =>
      h⁻¹ *
        ∫ s in t..(t + h),
          (∫ x,
            intervalFullSemigroupOperator (t + h - s) (F s) x * φ x
            ∂ intervalMeasure 1))
    (𝓝[>] (0 : ℝ))
    (𝓝 (∫ x, F t x * φ x ∂ intervalMeasure 1))

/-- SATISFIABLE standard endpoint fact for the `H^{-1}` divergence Duhamel
forcing, after restricted B_N duality identifies the endpoint pairing. -/
def ChemotaxisDuhamelEndpointLebesguePointFact
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (φ : ℝ → ℝ) (t : ℝ) : Prop :=
  Tendsto
    (fun h : ℝ =>
      h⁻¹ *
        ∫ s in t..(t + h),
          (∫ x,
            intervalConjugateKernelOperator (t + h - s)
              (truncatedChemFluxLifted p (u s)) x * φ x
            ∂ intervalMeasure 1))
    (𝓝[>] (0 : ℝ))
    (𝓝 (-(∫ x, truncatedChemFluxLifted p (u t) x * deriv φ x
      ∂ intervalMeasure 1)))

/-- SATISFIABLE standard dominated-convergence majorant for ordinary Duhamel
weak differentiation.  The analytic proof uses the gradient bound above and
the integrability of `(t-s)^{-1/2}`. -/
def HeatDuhamelDCTDominatingFunction
    (F : ℝ → ℝ → ℝ) (φ : ℝ → ℝ) (t : ℝ) : Prop :=
  ∃ G : ℝ → ℝ, IntegrableOn G (Set.Icc (0 : ℝ) t) volume ∧
    ∀ s, 0 < s → s < t →
      |∫ x,
        deriv (fun z : ℝ =>
          intervalFullSemigroupOperator (t - s) (F s) z) x * deriv φ x
        ∂ intervalMeasure 1| ≤ G s

/-- SATISFIABLE standard dominated-convergence majorant for the divergence
Duhamel leg, stated in the restricted-duality form actually used here. -/
def ChemotaxisDuhamelDCTDominatingFunction
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (φ : ℝ → ℝ) (t : ℝ) : Prop :=
  ∃ G : ℝ → ℝ, IntegrableOn G (Set.Icc (0 : ℝ) t) volume ∧
    ∀ s, 0 < s → s < t →
      |∫ y,
        truncatedChemFluxLifted p (u s) y *
          deriv (fun z : ℝ =>
            intervalFullSemigroupOperator (t - s) φ z) y
        ∂ intervalMeasure 1| ≤ G s

/-- Standard semigroup/Duhamel facts sufficient to discharge the
negative-part semigroup-weak field after the restricted lagwise B_N dualities
have been supplied. -/
structure NegativePartStandardHeatSemigroupDuhamelFacts
    (p : CM2Params) (T : ℝ) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  gradient_tminus_half :
    NeumannHeatGradientTMinusHalfBound
  source_endpoint_l2_lebesgue :
    ∀ t, 0 < t → t ≤ T →
      HeatDuhamelEndpointLebesguePointFact
        (fun s => truncatedLogisticLifted p (u s))
        (negativePartTest u t) t
  chem_endpoint_l2_lebesgue :
    ∀ t, 0 < t → t ≤ T →
      ChemotaxisDuhamelEndpointLebesguePointFact p u
        (negativePartTest u t) t
  source_dct_dominator :
    ∀ t, 0 < t → t ≤ T →
      HeatDuhamelDCTDominatingFunction
        (fun s => truncatedLogisticLifted p (u s))
        (negativePartTest u t) t
  chem_dct_dominator :
    ∀ t, 0 < t → t ≤ T →
      ChemotaxisDuhamelDCTDominatingFunction p u
        (negativePartTest u t) t
  semigroup_form_identity :
    ∀ t, 0 < t → t ≤ T →
      negativePartTestedLegWeakContribution
          (negativePartInitialHeatLeg u₀) t (negativePartTest u t)
        = 0
  source_duhamel_differentiation :
    ∀ t, 0 < t → t ≤ T →
      negativePartTestedLegWeakContribution
          (negativePartLogisticDuhamelLeg p u) t (negativePartTest u t)
        = negativePartLogisticWeakTerm p u t
  hminusone_duhamel_differentiation_after_restricted_duality :
    ∀ t, 0 < t → t ≤ T →
      (∀ s, 0 < s → s < t →
        TruncatedBNDualityForTestAt p u t s (negativePartTest u t)) →
      negativePartTestedLegWeakContribution
          (negativePartChemotaxisDuhamelLeg p u) t (negativePartTest u t)
        = -negativePartChemWeakTerm p u t
  tested_mild_decomposition :
    TruncatedConjugateMildSolution p T u₀ u →
      ∀ t, 0 < t → t ≤ T →
        negativePartTestedWeakLHS u t
          =
        negativePartTestedLegWeakContribution
            (negativePartInitialHeatLeg u₀) t (negativePartTest u t)
          + (-p.χ₀) *
            negativePartTestedLegWeakContribution
              (negativePartChemotaxisDuhamelLeg p u) t
              (negativePartTest u t)
          + negativePartTestedLegWeakContribution
              (negativePartLogisticDuhamelLeg p u) t
              (negativePartTest u t)

/-- Constructor for the cron2 negative-part semigroup-weak atom from standard
Neumann semigroup/Duhamel facts and the already-proved restricted lagwise B_N
duality. -/
theorem negativePartMildSemigroupWeakAfterFluxTestDuality_of_standardHeatSemigroupDuhamelFacts
    {p : CM2Params} {T : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (H : NegativePartStandardHeatSemigroupDuhamelFacts p T u₀ u) :
    NegativePartMildSemigroupWeakAfterFluxTestDuality p T u₀ u := by
  intro hmild t ht htT hdual
  change
    negativePartTestedWeakLHS u t
      =
    p.χ₀ * negativePartChemWeakTerm p u t
      + negativePartLogisticWeakTerm p u t
  rw [H.tested_mild_decomposition hmild t ht htT,
    H.semigroup_form_identity t ht htT,
    H.hminusone_duhamel_differentiation_after_restricted_duality
      t ht htT hdual,
    H.source_duhamel_differentiation t ht htT]
  ring

end ShenWork.Paper2.BFormPositiveDatumNegPart
