import Mathlib.Topology.UniformSpace.UniformConvergence
import ShenWork.PDE.IntervalResolverSpectralJointC2Producer
import ShenWork.Paper2.IntervalBFormPdeUProducer
import ShenWork.Paper2.IntervalBFormRestart
import ShenWork.Paper2.IntervalBFormLegDefs
import ShenWork.Paper2.IntervalDuhamelSourceShift
import ShenWork.Paper2.IntervalCD6CosineModeBounds

open Filter Topology Set MeasureTheory
open scoped Topology Interval

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

theorem bFormPositiveTimeCosineTerm_deriv
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (t r x : ℝ) (n : ℕ) :
    deriv (fun y : ℝ => bFormPositiveTimeCosineTerm p u t r y n) x =
      (Real.exp (-r * unitIntervalCosineEigenvalue n) *
        (((n : ℝ) * Real.pi) * intervalSineInner (bFormChemFluxAt p u t) n)) *
        deriv (cosineMode n) x := by
  let c : ℝ :=
    Real.exp (-r * unitIntervalCosineEigenvalue n) *
      (((n : ℝ) * Real.pi) * intervalSineInner (bFormChemFluxAt p u t) n)
  change deriv (fun y : ℝ => c * cosineMode n y) x =
    c * deriv (cosineMode n) x
  rw [ShenWork.CosineSpectrum.cosineMode_deriv]
  exact ((ShenWork.CosineSpectrum.cosineMode_hasDerivAt n x).const_mul c).deriv

theorem bFormPositiveTimeCosineTerm_second_deriv
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (t r x : ℝ) (n : ℕ) :
    deriv
        (fun y : ℝ =>
          deriv (fun z : ℝ => bFormPositiveTimeCosineTerm p u t r z n) y) x =
      (Real.exp (-r * unitIntervalCosineEigenvalue n) *
        (((n : ℝ) * Real.pi) * intervalSineInner (bFormChemFluxAt p u t) n)) *
        (-(((n : ℝ) * Real.pi) ^ 2 * cosineMode n x)) := by
  let c : ℝ :=
    Real.exp (-r * unitIntervalCosineEigenvalue n) *
      (((n : ℝ) * Real.pi) * intervalSineInner (bFormChemFluxAt p u t) n)
  have hfun :
      (fun y : ℝ =>
          deriv (fun z : ℝ => bFormPositiveTimeCosineTerm p u t r z n) y) =
        fun y : ℝ =>
          c * (-((n : ℝ) * Real.pi) *
            Real.sin ((n : ℝ) * Real.pi * y)) := by
    funext y
    rw [bFormPositiveTimeCosineTerm_deriv]
    rw [ShenWork.CosineSpectrum.cosineMode_deriv]
  change deriv
      (fun y : ℝ =>
        deriv (fun z : ℝ => bFormPositiveTimeCosineTerm p u t r z n) y) x =
    c * (-(((n : ℝ) * Real.pi) ^ 2 * cosineMode n x))
  rw [hfun]
  let freq : ℝ := (n : ℝ) * Real.pi
  have hlin : HasDerivAt (fun y : ℝ => freq * y) freq x := by
    simpa using ((hasDerivAt_id x).const_mul freq)
  have hsin :
      HasDerivAt (fun y : ℝ => Real.sin (freq * y))
        (Real.cos (freq * x) * freq) x :=
    (Real.hasDerivAt_sin (freq * x)).comp x hlin
  have hderiv := (hsin.const_mul (c * (-freq))).deriv
  rw [show (fun y : ℝ =>
        c * (-((n : ℝ) * Real.pi) *
          Real.sin ((n : ℝ) * Real.pi * y))) =
      fun y : ℝ => c * (-((n : ℝ) * Real.pi)) *
        Real.sin ((n : ℝ) * Real.pi * y) by
        funext y
        ring]
  dsimp [freq] at hderiv
  rw [hderiv]
  simp only [cosineMode]
  ring
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

/-- Sine coefficients of a bounded flux slice are uniformly bounded.  The
factor `2` is the positive-mode Neumann normalization in `intervalSineInner`. -/
theorem intervalSineInner_abs_le_of_bound
    {g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ y ∈ Set.Icc (0 : ℝ) 1, |g y| ≤ C) :
    ∀ n : ℕ, |intervalSineInner g n| ≤ 2 * C := by
  intro n
  unfold intervalSineInner
  by_cases hn : n = 0
  · simp [hn, hC]
  · simp only [hn, if_false]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hint :
        ‖∫ y in (0 : ℝ)..1,
            Real.sin ((n : ℝ) * Real.pi * y) * g y‖ ≤ C := by
      have hbound : ∀ y ∈ Ι (0 : ℝ) 1,
          ‖Real.sin ((n : ℝ) * Real.pi * y) * g y‖ ≤ C := by
        intro y hy
        have hyUcc : y ∈ Set.uIcc (0 : ℝ) 1 :=
          Set.uIoc_subset_uIcc hy
        have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
          simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hyUcc
        rw [Real.norm_eq_abs, abs_mul]
        calc |Real.sin ((n : ℝ) * Real.pi * y)| * |g y|
            ≤ 1 * C :=
              mul_le_mul (Real.abs_sin_le_one _)
                (hg y hyIcc) (abs_nonneg _) (by norm_num)
          _ = C := by ring
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := 1) (C := C) hbound
      simpa using h
    calc
      2 * |∫ y in (0 : ℝ)..1,
            Real.sin ((n : ℝ) * Real.pi * y) * g y|
          = 2 * ‖∫ y in (0 : ℝ)..1,
            Real.sin ((n : ℝ) * Real.pi * y) * g y‖ := by
              rw [Real.norm_eq_abs]
      _ ≤ 2 * C := mul_le_mul_of_nonneg_left hint (by norm_num)

theorem bFormDifferentiatedCosineSeriesUniformConvergence_of_sineInner_bound
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hσ : ∀ t₀, 0 < t₀ → t₀ < T →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ n : ℕ, |intervalSineInner (bFormChemFluxAt p u t₀) n| ≤ C) :
    BFormDifferentiatedCosineSeriesUniformConvergence p T u := by
  intro t₀ ht₀ ht₀T K _hK _hKsub ε hε
  obtain ⟨C, hC, hσC⟩ := hσ t₀ ht₀ ht₀T
  let M0 : ℕ → ℝ := fun n =>
    C * (|((n : ℝ) * Real.pi)| ^ 1 *
      Real.exp (-ε * unitIntervalCosineEigenvalue n))
  let M1 : ℕ → ℝ := fun n =>
    C * (|((n : ℝ) * Real.pi)| ^ 2 *
      Real.exp (-ε * unitIntervalCosineEigenvalue n))
  let M2 : ℕ → ℝ := fun n =>
    C * (|((n : ℝ) * Real.pi)| ^ 3 *
      Real.exp (-ε * unitIntervalCosineEigenvalue n))
  refine ⟨M0, M1, M2, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      (ShenWork.Paper2.CD6CosineModeBounds.frequency_pow_mul_exp_summable
        1 hε).mul_left C
  · exact
      (ShenWork.Paper2.CD6CosineModeBounds.frequency_pow_mul_exp_summable
        2 hε).mul_left C
  · exact
      (ShenWork.Paper2.CD6CosineModeBounds.frequency_pow_mul_exp_summable
        3 hε).mul_left C
  · intro n
    have hpow1 : 0 ≤ |((n : ℝ) * Real.pi)| ^ 1 := by positivity
    have hpow2 : 0 ≤ |((n : ℝ) * Real.pi)| ^ 2 := by positivity
    have hpow3 : 0 ≤ |((n : ℝ) * Real.pi)| ^ 3 := by positivity
    have hexp : 0 ≤ Real.exp (-ε * unitIntervalCosineEigenvalue n) :=
      Real.exp_nonneg _
    exact ⟨mul_nonneg hC (mul_nonneg hpow1 hexp),
      mul_nonneg hC (mul_nonneg hpow2 hexp),
      mul_nonneg hC (mul_nonneg hpow3 hexp)⟩
  · intro r hεr _hrT x _hxK n
    let freq : ℝ := (n : ℝ) * Real.pi
    let lam : ℝ := unitIntervalCosineEigenvalue n
    let sigma : ℝ := intervalSineInner (bFormChemFluxAt p u t₀) n
    have hlam_nonneg : 0 ≤ lam := by
      dsimp [lam, unitIntervalCosineEigenvalue]
      positivity
    have hexp_le :
        Real.exp (-r * lam) ≤ Real.exp (-ε * lam) := by
      apply Real.exp_le_exp.mpr
      have hmul : ε * lam ≤ r * lam :=
        mul_le_mul_of_nonneg_right hεr hlam_nonneg
      linarith
    have hcoef_nonneg :
        0 ≤ Real.exp (-ε * lam) * (|freq| * C) :=
      mul_nonneg (Real.exp_nonneg _) (mul_nonneg (abs_nonneg _) hC)
    have hcoef_le :
        |Real.exp (-r * lam) * (freq * sigma)| ≤
          Real.exp (-ε * lam) * (|freq| * C) := by
      calc
        |Real.exp (-r * lam) * (freq * sigma)|
            = Real.exp (-r * lam) * (|freq| * |sigma|) := by
              rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _), abs_mul]
        _ ≤ Real.exp (-r * lam) * (|freq| * C) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left
                  (by simpa [sigma] using hσC n) (abs_nonneg freq))
                (Real.exp_nonneg _)
        _ ≤ Real.exp (-ε * lam) * (|freq| * C) :=
              mul_le_mul_of_nonneg_right hexp_le
                (mul_nonneg (abs_nonneg freq) hC)
    have hcos : |cosineMode n x| ≤ 1 := by
      unfold cosineMode
      exact Real.abs_cos_le_one _
    have hderiv_cos : |deriv (cosineMode n) x| ≤ |freq| := by
      rw [ShenWork.CosineSpectrum.cosineMode_deriv]
      dsimp [freq]
      rw [abs_mul, abs_neg]
      exact mul_le_of_le_one_right (abs_nonneg _)
        (Real.abs_sin_le_one _)
    have hsecond_cos :
        |(-(((n : ℝ) * Real.pi) ^ 2 * cosineMode n x))| ≤ |freq| ^ 2 := by
      dsimp [freq]
      rw [abs_neg, abs_mul, abs_pow]
      exact mul_le_of_le_one_right (pow_nonneg (abs_nonneg _) 2) hcos
    have hM0 :
        |bFormPositiveTimeCosineTerm p u t₀ r x n| ≤ M0 n := by
      dsimp [bFormPositiveTimeCosineTerm, M0, freq, lam, sigma] at *
      calc
        |Real.exp (-r * unitIntervalCosineEigenvalue n) *
              (((n : ℝ) * Real.pi) *
                intervalSineInner (bFormChemFluxAt p u t₀) n) *
            cosineMode n x|
            =
          |Real.exp (-r * unitIntervalCosineEigenvalue n) *
              (((n : ℝ) * Real.pi) *
                intervalSineInner (bFormChemFluxAt p u t₀) n)| *
            |cosineMode n x| := by rw [abs_mul]
        _ ≤
          (Real.exp (-ε * unitIntervalCosineEigenvalue n) *
              (|((n : ℝ) * Real.pi)| * C)) * 1 :=
            mul_le_mul
              (by simpa [freq, lam, sigma] using hcoef_le)
              hcos
              (abs_nonneg _)
              (by
                simpa [freq, lam] using hcoef_nonneg)
        _ = C * (|((n : ℝ) * Real.pi)| ^ 1 *
              Real.exp (-ε * unitIntervalCosineEigenvalue n)) := by
            ring
    have hM1 :
        |deriv (fun y : ℝ =>
            bFormPositiveTimeCosineTerm p u t₀ r y n) x| ≤ M1 n := by
      rw [bFormPositiveTimeCosineTerm_deriv]
      dsimp [M1, freq, lam, sigma] at *
      calc
        |(Real.exp (-r * unitIntervalCosineEigenvalue n) *
              (((n : ℝ) * Real.pi) *
                intervalSineInner (bFormChemFluxAt p u t₀) n)) *
            deriv (cosineMode n) x|
            =
          |Real.exp (-r * unitIntervalCosineEigenvalue n) *
              (((n : ℝ) * Real.pi) *
                intervalSineInner (bFormChemFluxAt p u t₀) n)| *
            |deriv (cosineMode n) x| := by rw [abs_mul]
        _ ≤
          (Real.exp (-ε * unitIntervalCosineEigenvalue n) *
              (|((n : ℝ) * Real.pi)| * C)) *
            |((n : ℝ) * Real.pi)| :=
            mul_le_mul
              (by simpa [freq, lam, sigma] using hcoef_le)
              (by simpa [freq] using hderiv_cos)
              (abs_nonneg _)
              (by simpa [freq, lam] using hcoef_nonneg)
        _ = C * (|((n : ℝ) * Real.pi)| ^ 2 *
              Real.exp (-ε * unitIntervalCosineEigenvalue n)) := by
            ring
    have hM2 :
        |deriv (fun y : ℝ =>
            deriv (fun z : ℝ =>
              bFormPositiveTimeCosineTerm p u t₀ r z n) y) x|
          ≤ M2 n := by
      rw [bFormPositiveTimeCosineTerm_second_deriv]
      dsimp [M2, freq, lam, sigma] at *
      calc
        |(Real.exp (-r * unitIntervalCosineEigenvalue n) *
              (((n : ℝ) * Real.pi) *
                intervalSineInner (bFormChemFluxAt p u t₀) n)) *
            (-(((n : ℝ) * Real.pi) ^ 2 * cosineMode n x))|
            =
          |Real.exp (-r * unitIntervalCosineEigenvalue n) *
              (((n : ℝ) * Real.pi) *
                intervalSineInner (bFormChemFluxAt p u t₀) n)| *
            |(-(((n : ℝ) * Real.pi) ^ 2 * cosineMode n x))| := by
              rw [abs_mul]
        _ ≤
          (Real.exp (-ε * unitIntervalCosineEigenvalue n) *
              (|((n : ℝ) * Real.pi)| * C)) *
            |((n : ℝ) * Real.pi)| ^ 2 :=
            mul_le_mul
              (by simpa [freq, lam, sigma] using hcoef_le)
              (by simpa [freq] using hsecond_cos)
              (abs_nonneg _)
              (by simpa [freq, lam] using hcoef_nonneg)
        _ = C * (|((n : ℝ) * Real.pi)| ^ 3 *
              Real.exp (-ε * unitIntervalCosineEigenvalue n)) := by
            ring
    exact ⟨hM0, hM1, hM2⟩

theorem bFormDifferentiatedCosineSeriesUniformConvergence_of_flux_bound
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hQ : ∀ t₀, 0 < t₀ → t₀ < T →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ y ∈ Set.Icc (0 : ℝ) 1, |bFormChemFluxAt p u t₀ y| ≤ C) :
    BFormDifferentiatedCosineSeriesUniformConvergence p T u := by
  refine bFormDifferentiatedCosineSeriesUniformConvergence_of_sineInner_bound ?_
  intro t₀ ht₀ ht₀T
  rcases hQ t₀ ht₀ ht₀T with ⟨C, hC, hCbd⟩
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  exact intervalSineInner_abs_le_of_bound hC hCbd

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
