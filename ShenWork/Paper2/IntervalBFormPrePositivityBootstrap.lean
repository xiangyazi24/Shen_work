/-
  B-form spatial bootstrap before strict positivity.

  The solution package below deliberately stops at nonnegativity.  The only
  spectral input used by this file is `HasBFormSpectralPdeAgreement`; its local
  restart representation already supplies the summable cosine series needed
  for closed spatial C² regularity and the one-sided Neumann limits.
-/
import ShenWork.Paper2.IntervalBFormPdeUProducer
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.PDE.IntervalCosineSliceRegularity

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomain intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalMildPicard (HasContinuousSlices HasJointMeasurability)
open ShenWork.IntervalConjugateDuhamelMap (IntervalConjugateMildSolution)
open ShenWork.IntervalBFormSpectral (HasBFormSpectralPdeAgreement)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalCosineSliceRegularity
  (intervalDomainCosineSlice_conjunct7_unconditional
    intervalDomainCosineSlice_neumann_limit_left
    intervalDomainCosineSlice_neumann_limit_right)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.Paper2

/-- Mild-solution data available before strict positivity has been proved. -/
structure NonnegativeConjugateMildSolutionData (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) where
  T : ℝ
  hT : 0 < T
  M : ℝ
  hM : 0 < M
  u : ℝ → intervalDomainPoint → ℝ
  hmild : IntervalConjugateMildSolution p T u₀ u
  hbound : ∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M
  hnonneg : ∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ u t x
  hcont : HasContinuousSlices T u
  hmeas : HasJointMeasurability u

/-- The minimal spectral input needed for the pre-positivity spatial bootstrap. -/
structure NonnegativeBFormSpectralData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (S : NonnegativeConjugateMildSolutionData p u₀) : Prop where
  hPdeAgreement : HasBFormSpectralPdeAgreement p S.T S.u

private def prePositivityMidpoint : intervalDomainPoint :=
  ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩

private theorem prePositivityMidpoint_mem_Ioo :
    prePositivityMidpoint.1 ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor <;> norm_num [prePositivityMidpoint]

/-- Spectral PDE agreement supplies one summable cosine representation of every
strictly positive-time solution slice. -/
theorem bFormSpectral_slice_before_strictPositivity
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (Hpde : HasBFormSpectralPdeAgreement p T u)
    {t : ℝ} (ht : 0 < t) (htT : t < T) :
    ∃ b : ℕ → ℝ,
      Summable (fun n : ℕ ↦ unitIntervalCosineEigenvalue n * |b n|) ∧
      Set.EqOn (intervalDomainLift (u t))
        (fun x : ℝ ↦ ∑' n : ℕ, b n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1) := by
  obtain ⟨a₀, _M, _hM, _ha₀, a, _src, offset, _hoff,
      _hlog, _hchem, hrep, _hsplit, hsum⟩ :=
    Hpde.exists_data t ht htT
      (x := prePositivityMidpoint) prePositivityMidpoint_mem_Ioo
  refine ⟨fun n ↦ localRestartCoeff a₀ a (t - offset) n, hsum, ?_⟩
  intro x hx
  simp only [intervalDomainLift, hx, dif_pos]
  exact hrep.self_of_nhds ⟨x, hx⟩

/-- Closed spatial C² regularity and the two endpoint derivative equalities are
available from spectral agreement before strict positivity. -/
theorem bFormSpectral_u_closedC2_endpointDerivs_before_strictPositivity
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (Hpde : HasBFormSpectralPdeAgreement p T u) :
    ∀ t, 0 < t → t < T →
      ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1)
        ∧ deriv (intervalDomainLift (u t)) 0 = 0
        ∧ deriv (intervalDomainLift (u t)) 1 = 0 := by
  intro t ht htT
  obtain ⟨b, hsum, hagree⟩ :=
    bFormSpectral_slice_before_strictPositivity Hpde ht htT
  exact intervalDomainCosineSlice_conjunct7_unconditional hsum hagree

/-- The genuine one-sided Neumann limits also precede strict positivity. -/
theorem bFormSpectral_u_neumannLimits_before_strictPositivity
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (Hpde : HasBFormSpectralPdeAgreement p T u) :
    ∀ t, 0 < t → t < T →
      Tendsto (deriv (intervalDomainLift (u t)))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Tendsto (deriv (intervalDomainLift (u t)))
          (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
  intro t ht htT
  obtain ⟨b, hsum, hagree⟩ :=
    bFormSpectral_slice_before_strictPositivity Hpde ht htT
  exact ⟨intervalDomainCosineSlice_neumann_limit_left hsum hagree,
    intervalDomainCosineSlice_neumann_limit_right hsum hagree⟩

/-- Data-level closed-C² wrapper.  No strict-positivity field is present or used. -/
theorem NonnegativeBFormSpectralData.u_closedC2_endpointDerivs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {S : NonnegativeConjugateMildSolutionData p u₀}
    (H : NonnegativeBFormSpectralData p S) :
    ∀ t, 0 < t → t < S.T →
      ContDiffOn ℝ 2 (intervalDomainLift (S.u t)) (Set.Icc (0 : ℝ) 1)
        ∧ deriv (intervalDomainLift (S.u t)) 0 = 0
        ∧ deriv (intervalDomainLift (S.u t)) 1 = 0 :=
  bFormSpectral_u_closedC2_endpointDerivs_before_strictPositivity H.hPdeAgreement

/-- Data-level one-sided Neumann-limit wrapper. -/
theorem NonnegativeBFormSpectralData.u_neumannLimits
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {S : NonnegativeConjugateMildSolutionData p u₀}
    (H : NonnegativeBFormSpectralData p S) :
    ∀ t, 0 < t → t < S.T →
      Tendsto (deriv (intervalDomainLift (S.u t)))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Tendsto (deriv (intervalDomainLift (S.u t)))
          (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) :=
  bFormSpectral_u_neumannLimits_before_strictPositivity H.hPdeAgreement

end ShenWork.Paper2
