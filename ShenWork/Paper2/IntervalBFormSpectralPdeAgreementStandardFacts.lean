import Mathlib.Topology.UniformSpace.UniformConvergence
import ShenWork.PDE.IntervalResolverSpectralJointC2Producer
import ShenWork.Paper2.IntervalBFormPdeUProducer
import ShenWork.Paper2.IntervalBFormRestart
import ShenWork.Paper2.IntervalConjugateCosineSeries
import ShenWork.Paper2.IntervalDuhamelSourceShift

open Filter Topology Set MeasureTheory
open scoped Topology

noncomputable section

namespace ShenWork.IntervalBFormSpectral

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalGradientDuhamelMap
  (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator)
open ShenWork.IntervalConjugateCosineSeries
  (intervalSineInner)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalDuhamelClosedC2
  (DuhamelSourceTimeC1)
open ShenWork.IntervalSourceCoefficientTimeC1
  (localRestartCoeff)
open ShenWork.CosineSpectrum
  (cosineMode)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceCoeffs
   coupledLogisticSourceCoeffs)
open ShenWork.IntervalMildToClassical
  (mildChemicalConcentration)

/-- The flux slice used by the B-form chemotaxis Duhamel leg. -/
def bFormChemFluxAt (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) : ℝ → ℝ :=
  chemFluxLifted p (u t)

/-- One positive-time cosine term in the B-kernel representation. -/
def bFormPositiveTimeCosineTerm
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (t r x : ℝ) (n : ℕ) : ℝ :=
  (Real.exp (-r * unitIntervalCosineEigenvalue n) *
    (((n : ℝ) * Real.pi) * intervalSineInner (bFormChemFluxAt p u t) n))
      * cosineMode n x

/-- The B-form chemotaxis Duhamel leg before multiplication by `-χ₀`. -/
def bFormConjugateDuhamelLeg
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (t x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t,
    intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x

/-- The ordinary logistic Duhamel leg. -/
def bFormLogisticDuhamelLeg
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (t x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t,
    intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x

/-- The non-homogeneous part of the B-form mild profile. -/
def bFormInhomogeneousDuhamelLeg
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (t x : ℝ) : ℝ :=
  (-p.χ₀) * bFormConjugateDuhamelLeg p u t x
    + bFormLogisticDuhamelLeg p u t x

/-- Local bounded classical regularity on the current finite Picard window.
The bound is the local fixed-point ball bound, not a global boundedness
conclusion. -/
def BFormBoundedClassicalRegularity
    (p : CM2Params) (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  intervalDomain.classicalRegularity T u (mildChemicalConcentration p u) ∧
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint, |u t x| ≤ C

/-- SATISFIABLE standard fact, currently a project theorem gap: M-test form of
the differentiated B-kernel cosine series on every positive-time strip `r ≥ ε`,
locally uniformly in the spatial interior. -/
def BFormDifferentiatedCosineSeriesUniformConvergence
    (p : CM2Params) (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ t₀, 0 < t₀ → t₀ < T →
    ∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioo (0 : ℝ) 1 →
      ∀ ε, 0 < ε →
        ∃ M0 : ℕ → ℝ, ∃ M1 : ℕ → ℝ, ∃ M2 : ℕ → ℝ,
          Summable M0 ∧ Summable M1 ∧ Summable M2 ∧
            (∀ n, 0 ≤ M0 n ∧ 0 ≤ M1 n ∧ 0 ≤ M2 n) ∧
            (∀ r, ε ≤ r → r ≤ T → ∀ x, x ∈ K → ∀ n,
              |bFormPositiveTimeCosineTerm p u t₀ r x n| ≤ M0 n ∧
                |deriv (fun y : ℝ =>
                    bFormPositiveTimeCosineTerm p u t₀ r y n) x| ≤ M1 n ∧
                |deriv (fun y : ℝ =>
                    deriv (fun z : ℝ =>
                      bFormPositiveTimeCosineTerm p u t₀ r z n) y) x|
                  ≤ M2 n)

/-- SATISFIABLE standard fact, currently a project theorem gap: interior Abel trace.
`B_N(r)Q(t)` tends locally uniformly to `∂ₓQ(t)` as `r ↓ 0`. -/
def BFormInteriorZeroTimeTrace
    (p : CM2Params) (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ t₀, 0 < t₀ → t₀ < T →
    ∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioo (0 : ℝ) 1 →
      TendstoUniformlyOn
        (fun r x =>
          intervalConjugateKernelOperator r (bFormChemFluxAt p u t₀) x)
        (fun x => deriv (bFormChemFluxAt p u t₀) x)
        (𝓝[>] (0 : ℝ)) K

/-- SATISFIABLE standard fact, currently a project theorem gap: Duhamel
differentiation identity for the inhomogeneous B-form leg.  The endpoint
contribution of the B-kernel is the zero-time trace `∂ₓQ(t)`. -/
def BFormDuhamelTimeDerivativeInteriorPdeIdentity
    (p : CM2Params) (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
    deriv (fun τ : ℝ => bFormInhomogeneousDuhamelLeg p u τ x.1) t
      =
    deriv
        (fun y : ℝ =>
          deriv (fun z : ℝ => bFormInhomogeneousDuhamelLeg p u t z) y)
        x.1
      - p.χ₀ * deriv (bFormChemFluxAt p u t) x.1
      + logisticLifted p (u t) x.1

/-- SATISFIABLE standard fact, currently a project theorem gap: semigroup
generator identity, gated to the actual source slices used by the B-form mild
profile. -/
def BFormSemigroupGeneratorIdentity
    (p : CM2Params) (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ t s x, 0 < s → s < t → t < T → x ∈ intervalDomain.inside →
    deriv (fun r : ℝ =>
        intervalConjugateKernelOperator r (chemFluxLifted p (u s)) x.1)
        (t - s)
      =
        deriv
          (fun y : ℝ =>
            deriv (fun z : ℝ =>
              intervalConjugateKernelOperator (t - s)
                (chemFluxLifted p (u s)) z) y)
          x.1
    ∧
    deriv (fun r : ℝ =>
        intervalFullSemigroupOperator r (logisticLifted p (u s)) x.1)
        (t - s)
      =
        deriv
          (fun y : ℝ =>
            deriv (fun z : ℝ =>
              intervalFullSemigroupOperator (t - s)
                (logisticLifted p (u s)) z) y)
          x.1

/-- The data produced by the Duhamel-cosine reconstruction of the B-form mild
profile.  This is intentionally a from-zero/global reconstruction package, not
the local restart witness demanded by `HasBFormSpectralPdeAgreement.exists_data`.
The local witness is derived below by restarting this global cosine formula. -/
def BFormDuhamelCosineReconstructionData
    (p : CM2Params) (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∃ (aInit : ℕ → ℝ) (aB : ℝ → ℕ → ℝ),
  ∃ (_source_timeC1 : DuhamelSourceTimeC1 aB),
  ∃ (_logistic_data : ∀ t, 0 < t → t < T →
      LogisticCosineFourierData p u t),
  ∃ (_chem_data : ∀ t, 0 < t → t < T →
      ChemDivCosineFourierData p (u t)
        (coupledChemicalConcentration p u t)),
    (∀ σ, 0 < σ → σ < T → ∀ n,
      aB σ n =
        coupledLogisticSourceCoeffs p u σ n
          - p.χ₀ * coupledChemDivSourceCoeffs p u σ n) ∧
    (∀ t, 0 < t → t ≤ T →
      Set.EqOn (intervalDomainLift (u t))
        (fun x => ∑' n, localRestartCoeff aInit aB t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1)) ∧
    (∀ t, 0 < t → t ≤ T →
      Summable (fun n => |localRestartCoeff aInit aB t n|))

/-- SATISFIABLE standard fact, currently the precise project theorem gap:
the four heat-semigroup/Duhamel facts, together with the actual B-form mild
solution and local classical regularity, reconstruct the from-zero cosine
coefficient family of the B-form Duhamel solution. -/
def BFormDuhamelCosineReconstructionFromStandardFacts
    (p : CM2Params) (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ {u₀ : intervalDomainPoint → ℝ},
    ShenWork.IntervalConjugateDuhamelMap.IntervalConjugateMildSolution
      p T u₀ u →
    BFormBoundedClassicalRegularity p T u →
    BFormDifferentiatedCosineSeriesUniformConvergence p T u →
    BFormInteriorZeroTimeTrace p T u →
    BFormDuhamelTimeDerivativeInteriorPdeIdentity p T u →
    BFormSemigroupGeneratorIdentity p T u →
    BFormDuhamelCosineReconstructionData p T u

/-- Named standard facts reducing B-form interior PDE faithfulness to heat
semigroup/Duhamel analysis on the actual Picard trajectory. -/
structure BFormSpectralPdeAgreementStandardFacts
    (p : CM2Params) (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  differentiated_cosine_series_uniform :
    BFormDifferentiatedCosineSeriesUniformConvergence p T u
  interior_zero_time_trace :
    BFormInteriorZeroTimeTrace p T u
  duhamel_time_derivative_identity :
    BFormDuhamelTimeDerivativeInteriorPdeIdentity p T u
  semigroup_generator_identity :
    BFormSemigroupGeneratorIdentity p T u
  duhamel_cosine_reconstruction :
    BFormDuhamelCosineReconstructionFromStandardFacts p T u

/-- Constructor from the named standard heat-semigroup/Duhamel facts to the
existing spectral-agreement interface consumed by the PDE producer.  The
local restart witness is derived from the reconstructed global Duhamel-cosine
formula; it is not carried as a field. -/
theorem hasBFormSpectralPdeAgreement_of_standardFacts
    {p : CM2Params} {T : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hB : ShenWork.IntervalConjugateDuhamelMap.IntervalConjugateMildSolution
      p T u₀ u)
    (hreg : BFormBoundedClassicalRegularity p T u)
    (H : BFormSpectralPdeAgreementStandardFacts p T u) :
    HasBFormSpectralPdeAgreement p T u := by
  constructor
  intro t₀ ht₀ ht₀T x hxIoo
  obtain ⟨aInit, aB, hsrcB, hlogistic_data, hchem_data, hsource_split,
      hglobal_cosine, hglobal_l1_summable⟩ :=
    H.duhamel_cosine_reconstruction hB hreg
      H.differentiated_cosine_series_uniform
      H.interior_zero_time_trace
      H.duhamel_time_derivative_identity
      H.semigroup_generator_identity
  set τ : ℝ := t₀ / 2 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hτT : τ < T := by rw [hτdef]; linarith
  have htmτ : t₀ - τ = τ := by rw [hτdef]; ring
  obtain ⟨C, hCnn, hCbd⟩ := hreg.2
  set a₀ : ℕ → ℝ := cosineCoeffs (intervalDomainLift (u τ)) with ha₀def
  set a : ℝ → ℕ → ℝ := fun σ n => aB (τ + σ) n with hadef
  have ha₀_bd : ∀ k, |a₀ k| ≤ 2 * C := by
    intro k
    have hC2 :
        ContDiffOn ℝ 2 (intervalDomainLift (u τ)) (Set.Icc (0 : ℝ) 1) :=
      (hreg.1.2.2.2.2.1 τ ⟨hτpos, hτT⟩).1.1
    refine ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
      hC2.continuousOn hCnn ?_ k
    intro y hy
    simpa [intervalDomainLift, hy] using
      hCbd τ hτpos hτT.le ⟨y, hy⟩
  have srcShift : DuhamelSourceTimeC1 a := by
    simpa [a, add_comm] using
      ShenWork.IntervalDuhamelSourceShift.DuhamelSourceTimeC1.shift_nonneg
        hsrcB hτpos.le
  have ha_cont : ∀ k, ContinuousOn (fun s => aB s k) (Set.Icc 0 T) := by
    intro k
    exact (continuous_iff_continuousAt.2
      (fun s => (hsrcB.hderiv s k).continuousAt)).continuousOn
  have hB_restart :
      ∀ t₁, 0 < t₁ → t₁ < T →
        ∀ᶠ s in 𝓝 t₁, ∀ y : intervalDomainPoint,
          u s y =
            ∑' n,
              localRestartCoeff
                (cosineCoeffs (intervalDomainLift (u (t₁ / 2))))
                (fun σ n => aB (t₁ / 2 + σ) n)
                (s - t₁ / 2) n * cosineMode n y.1 :=
    ShenWork.IntervalConjugatePicard.bForm_restart_of_global_cosine
      (u := u) (T := T) (a₀ := aInit) (aB := aB)
      ha_cont hglobal_cosine hglobal_l1_summable
  have hoff : 0 < t₀ - τ := by rw [htmτ]; exact hτpos
  have hrep : ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
      u s y = ∑' n, localRestartCoeff a₀ a (s - τ) n * cosineMode n y.1 := by
    have h := hB_restart t₀ ht₀ ht₀T
    simpa [a₀, a, τ, hτdef] using h
  have hsource_at : ∀ n, a (t₀ - τ) n =
      coupledLogisticSourceCoeffs p u t₀ n
        - p.χ₀ * coupledChemDivSourceCoeffs p u t₀ n := by
    intro n
    have harg : τ + (t₀ - τ) = t₀ := by ring
    change aB (τ + (t₀ - τ)) n =
      coupledLogisticSourceCoeffs p u t₀ n
        - p.χ₀ * coupledChemDivSourceCoeffs p u t₀ n
    rw [harg]
    exact hsource_split t₀ ht₀ ht₀T n
  have hsum_b : Summable (fun n =>
      unitIntervalCosineEigenvalue n * |localRestartCoeff a₀ a (t₀ - τ) n|) := by
    rw [htmτ]
    exact ShenWork.IntervalResolverSpectralJointC2Producer.localRestartCoeff_eigenvalue_summable
      (τ := τ) (M := 2 * C) (a₀ := a₀) (a := a) hτpos ha₀_bd srcShift
  exact ⟨a₀, 2 * C, by nlinarith [hCnn], ha₀_bd,
    a, srcShift, τ, hoff, hlogistic_data t₀ ht₀ ht₀T,
    hchem_data t₀ ht₀ ht₀T, hrep, hsource_at, hsum_b⟩

/-- The corresponding interior PDE constructor, keeping the standard facts
visible at the call site. -/
theorem intervalConjugateMildSolution_pde_u_of_standardFacts
    (p : CM2Params) {T : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hB : ShenWork.IntervalConjugateDuhamelMap.IntervalConjugateMildSolution
      p T u₀ u)
    (hreg : BFormBoundedClassicalRegularity p T u)
    (H : BFormSpectralPdeAgreementStandardFacts p T u) :
    ∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv u t x =
        intervalDomain.laplacian (u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (u t)
              (mildChemicalConcentration p u t) x
          + u t x * (p.a - p.b * (u t x) ^ p.α) :=
  intervalConjugateMildSolution_pde_u_of_spectral p hB
    (hasBFormSpectralPdeAgreement_of_standardFacts hB hreg H)

#print axioms hasBFormSpectralPdeAgreement_of_standardFacts
#print axioms intervalConjugateMildSolution_pde_u_of_standardFacts

end ShenWork.IntervalBFormSpectral
