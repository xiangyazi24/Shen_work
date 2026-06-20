/-
  B-form PID interior PDE with the arbitrary representation parameters removed.

  This file fixes the spectral families used by
  `intervalConjugateMildSolution_pde_u_PID_global_restart` to the canonical
  B-form choices:

  * solution coefficients are `localRestartCoeff aInit (bFormSourceCoeffs p u)`;
  * source coefficients are `bFormSourceCoeffs p u =
      logistic - χ₀ * chemDiv`;
  * source time-`C¹` is assembled from the logistic and chem-div coefficient
    packages;
  * logistic/chem-div Fourier data are built from constant-extension
    continuity plus Fourier summability.

  The remaining explicit input is the global B-form cosine representation of
  the conjugate Picard limit.  No χ₀ = 0 specialization is used.
-/
import ShenWork.Paper2.IntervalBFormSpectralProviderDischarge
import ShenWork.Paper2.IntervalBFormSpectralHtime

open Filter Topology Set

noncomputable section

namespace ShenWork.IntervalBFormSpectral

open ShenWork.IntervalDomain
  (intervalDomainConstExtend constExtend_eq_lift_on_Icc intervalDomainPoint)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalCosineInversion (reflCircle)
open ShenWork.IntervalCoupledRegularityBootstrap (coupledLogisticSourceLift)

/-- Constant-extension provider for the logistic Fourier package. -/
def logisticCosineFourierData_constExtend
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ)
    (hcont : Continuous
      (intervalDomainConstExtend (intervalLogisticSource p (u t))))
    (hsum : Summable (fun n : ℤ =>
      fourierCoeff
        (reflCircle
          (intervalDomainConstExtend (intervalLogisticSource p (u t)))) n)) :
    LogisticCosineFourierData p u t where
  representative := intervalDomainConstExtend (intervalLogisticSource p (u t))
  continuous_representative := hcont
  representative_eq_logistic := by
    intro y hy
    exact constExtend_eq_lift_on_Icc hy
  fourier_summable := hsum

end ShenWork.IntervalBFormSpectral

namespace ShenWork.IntervalConjugatePicard

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalDomainConstExtend
   intervalDomainChemotaxisDiv)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1 duhamelSpectralCoeff)
open ShenWork.IntervalCosineInversion (reflCircle)
open ShenWork.IntervalBFormSpectral
  (HasBFormSpectralPdeAgreement LogisticCosineFourierData
   ChemDivCosineFourierData bFormSourceCoeffs
   bFormSource_duhamelSourceTimeC1 logisticCosineFourierData_constExtend
   chemDivCosineFourierData_constExtend)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceCoeffs
   coupledLogisticSourceCoeffs)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant)
open ShenWork.Paper2 (PaperPositiveInitialDatum)

/-- Unweighted summability of canonical restart coefficients, from bounded
restart data and a time-`C¹` source. -/
theorem localRestartCoeff_abs_summable
    {τ M : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ)
    (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC1 a) :
    Summable (fun n : ℕ => |localRestartCoeff a₀ a τ n|) := by
  have hhom : Summable (fun n : ℕ =>
      |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|) := by
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
      ((ShenWork.IntervalSemigroupComposition.expEigSummable hτ).mul_right M)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (ha₀ n) (Real.exp_pos _).le
  have hduh : Summable (fun n : ℕ => |duhamelSpectralCoeff a τ n|) := by
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
      (src.henv_summable.mul_left τ)
    exact ShenWork.IntervalPicardIterateRestart.abs_duhamelSpectralCoeff_le
      src hτ n
  refine (hhom.add hduh).of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
  unfold localRestartCoeff
  exact abs_add_le _ _

/-- B-form spectral agreement for the conjugate Picard PID solution with
`bc`, `aB`, `hsource_split`, and the Fourier-data records fixed to their
canonical providers. -/
theorem hasBFormSpectralPdeAgreement_conjugatePicardLimit_of_PID_unconditional
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (Hinf : ConjugatePicardInfThresholdData p u₀ D.T)
    (hsmall :
      |p.χ₀| * (heatGradientLinftyLinftyConstant *
          (2 * Real.sqrt D.T) * Hinf.CQ)
        + D.T * Hinf.CL ≤ paperPositiveFloor hu₀ / 2)
    (aInit : ℕ → ℝ) {MInit : ℝ}
    (haInit : ∀ n, |aInit n| ≤ MInit)
    (hlogSrc : DuhamelSourceTimeC1
      (coupledLogisticSourceCoeffs p (conjugatePicardLimit p u₀ D.T)))
    (hchemSrc : DuhamelSourceTimeC1
      (coupledChemDivSourceCoeffs p (conjugatePicardLimit p u₀ D.T)))
    (hB_global : ∀ t, 0 < t → t ≤ D.T →
      Set.EqOn (intervalDomainLift (conjugatePicardLimit p u₀ D.T t))
        (fun x => ∑' n,
          localRestartCoeff aInit
            (bFormSourceCoeffs p (conjugatePicardLimit p u₀ D.T))
            t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hlogCont : ∀ t, 0 < t → t < D.T →
      Continuous
        (intervalDomainConstExtend
          (ShenWork.IntervalDomainExistence.intervalLogisticSource p
            ((conjugatePicardLimit p u₀ D.T) t))))
    (hlogFourier : ∀ t, 0 < t → t < D.T →
      Summable (fun n : ℤ =>
        fourierCoeff
          (reflCircle
            (intervalDomainConstExtend
              (ShenWork.IntervalDomainExistence.intervalLogisticSource p
                ((conjugatePicardLimit p u₀ D.T) t)))) n))
    (hchemCont : ∀ t, 0 < t → t < D.T →
      Continuous
        (intervalDomainConstExtend
          (fun x : intervalDomainPoint =>
            intervalDomainChemotaxisDiv p
              ((conjugatePicardLimit p u₀ D.T) t)
              (coupledChemicalConcentration p
                (conjugatePicardLimit p u₀ D.T) t) x)))
    (hchemFourier : ∀ t, 0 < t → t < D.T →
      Summable (fun n : ℤ =>
        fourierCoeff
          (reflCircle
            (intervalDomainConstExtend
              (fun x : intervalDomainPoint =>
                intervalDomainChemotaxisDiv p
                  ((conjugatePicardLimit p u₀ D.T) t)
                  (coupledChemicalConcentration p
                    (conjugatePicardLimit p u₀ D.T) t) x))) n)) :
    HasBFormSpectralPdeAgreement p D.T
      (conjugatePicardLimit p u₀ D.T) := by
  let u : ℝ → intervalDomainPoint → ℝ := conjugatePicardLimit p u₀ D.T
  let aB : ℝ → ℕ → ℝ := bFormSourceCoeffs p u
  have hsrcB : DuhamelSourceTimeC1 aB := by
    simpa [aB, u] using
      bFormSource_duhamelSourceTimeC1
        (p := p) (u := u) hlogSrc hchemSrc
  have hlogData : ∀ t, 0 < t → t < D.T →
      LogisticCosineFourierData p u t := by
    intro t ht htT
    exact logisticCosineFourierData_constExtend p u t
      (by simpa [u] using hlogCont t ht htT)
      (by simpa [u] using hlogFourier t ht htT)
  have hchemData : ∀ t, 0 < t → t < D.T →
      ChemDivCosineFourierData p (u t)
        (coupledChemicalConcentration p u t) := by
    intro t ht htT
    exact chemDivCosineFourierData_constExtend p (u t)
      (coupledChemicalConcentration p u t)
      (by simpa [u] using hchemCont t ht htT)
      (by simpa [u] using hchemFourier t ht htT)
  exact hasBFormSpectralPdeAgreement_conjugatePicardLimit_of_PID_global_restart
    D hu₀ Hinf hsmall
    (fun σ n => localRestartCoeff aInit aB σ n)
    (fun σ hσ _hσT =>
      ShenWork.IntervalResolverSpectralJointC2Producer.localRestartCoeff_eigenvalue_summable
        (τ := σ) (M := MInit) (a₀ := aInit) (a := aB)
        hσ haInit hsrcB)
    (fun σ hσ hσT => by
      simpa [u, aB] using hB_global σ hσ hσT.le)
    aInit aB hsrcB
    (fun σ _hσ _hσT n => by
      simp [aB, bFormSourceCoeffs, u])
    (by
      intro t ht htT
      simpa [u, aB] using hB_global t ht htT)
    (by
      intro t ht _htT
      exact localRestartCoeff_abs_summable
        (τ := t) (M := MInit) (a₀ := aInit) (a := aB)
        ht haInit hsrcB)
    (by
      intro t ht htT
      simpa [u] using hlogData t ht htT)
    (by
      intro t ht htT
      simpa [u] using hchemData t ht htT)

/-- Interior B-form PDE for PID with the arbitrary spectral families fixed to
the canonical B-form coefficient providers. -/
theorem intervalConjugateMildSolution_pde_u_PID_unconditional
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (Hinf : ConjugatePicardInfThresholdData p u₀ D.T)
    (hsmall :
      |p.χ₀| * (heatGradientLinftyLinftyConstant *
          (2 * Real.sqrt D.T) * Hinf.CQ)
        + D.T * Hinf.CL ≤ paperPositiveFloor hu₀ / 2)
    (aInit : ℕ → ℝ) {MInit : ℝ}
    (haInit : ∀ n, |aInit n| ≤ MInit)
    (hlogSrc : DuhamelSourceTimeC1
      (coupledLogisticSourceCoeffs p (conjugatePicardLimit p u₀ D.T)))
    (hchemSrc : DuhamelSourceTimeC1
      (coupledChemDivSourceCoeffs p (conjugatePicardLimit p u₀ D.T)))
    (hB_global : ∀ t, 0 < t → t ≤ D.T →
      Set.EqOn (intervalDomainLift (conjugatePicardLimit p u₀ D.T t))
        (fun x => ∑' n,
          localRestartCoeff aInit
            (bFormSourceCoeffs p (conjugatePicardLimit p u₀ D.T))
            t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hlogCont : ∀ t, 0 < t → t < D.T →
      Continuous
        (intervalDomainConstExtend
          (ShenWork.IntervalDomainExistence.intervalLogisticSource p
            ((conjugatePicardLimit p u₀ D.T) t))))
    (hlogFourier : ∀ t, 0 < t → t < D.T →
      Summable (fun n : ℤ =>
        fourierCoeff
          (reflCircle
            (intervalDomainConstExtend
              (ShenWork.IntervalDomainExistence.intervalLogisticSource p
                ((conjugatePicardLimit p u₀ D.T) t)))) n))
    (hchemCont : ∀ t, 0 < t → t < D.T →
      Continuous
        (intervalDomainConstExtend
          (fun x : intervalDomainPoint =>
            intervalDomainChemotaxisDiv p
              ((conjugatePicardLimit p u₀ D.T) t)
              (coupledChemicalConcentration p
                (conjugatePicardLimit p u₀ D.T) t) x)))
    (hchemFourier : ∀ t, 0 < t → t < D.T →
      Summable (fun n : ℤ =>
        fourierCoeff
          (reflCircle
            (intervalDomainConstExtend
              (fun x : intervalDomainPoint =>
                intervalDomainChemotaxisDiv p
                  ((conjugatePicardLimit p u₀ D.T) t)
                  (coupledChemicalConcentration p
                    (conjugatePicardLimit p u₀ D.T) t) x))) n)) :
    ∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv (conjugatePicardLimit p u₀ D.T) t x =
        intervalDomain.laplacian ((conjugatePicardLimit p u₀ D.T) t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p
              ((conjugatePicardLimit p u₀ D.T) t)
              (ShenWork.IntervalMildToClassical.mildChemicalConcentration p
                (conjugatePicardLimit p u₀ D.T) t) x
          + (conjugatePicardLimit p u₀ D.T) t x
            * (p.a - p.b * ((conjugatePicardLimit p u₀ D.T) t x) ^ p.α) := by
  have Hpde :
      HasBFormSpectralPdeAgreement p D.T
        (conjugatePicardLimit p u₀ D.T) :=
    hasBFormSpectralPdeAgreement_conjugatePicardLimit_of_PID_unconditional
      D hu₀ Hinf hsmall aInit haInit hlogSrc hchemSrc hB_global
      hlogCont hlogFourier hchemCont hchemFourier
  exact intervalConjugateMildSolution_pde_u_from_picard_data_and_spectral D Hpde

#print axioms ShenWork.IntervalBFormSpectral.logisticCosineFourierData_constExtend
#print axioms localRestartCoeff_abs_summable
#print axioms hasBFormSpectralPdeAgreement_conjugatePicardLimit_of_PID_unconditional
#print axioms intervalConjugateMildSolution_pde_u_PID_unconditional

end ShenWork.IntervalConjugatePicard
