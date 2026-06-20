/-
  Discharge the two localized B-form spectral-provider inputs:

  * strict positivity (`hpost`) from the PID inf-threshold estimate;
  * the B-form restart cosine representation from a global B-form cosine
    formula.

  This file is additive; the original provider is left unchanged.
-/
import ShenWork.Paper2.IntervalBFormSpectralProvider
import ShenWork.Paper2.IntervalConjugatePicardInfThreshold
import ShenWork.Paper2.IntervalBFormRestart

open Filter Topology Set

noncomputable section

namespace ShenWork.IntervalConjugatePicard

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalBFormSpectral
  (HasBFormSpectralPdeAgreement LogisticCosineFourierData
   ChemDivCosineFourierData)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceCoeffs
   coupledLogisticSourceCoeffs)
open ShenWork.Paper2 (PaperPositiveInitialDatum)

/-- Localized B-form spectral agreement with strict positivity supplied
explicitly, rather than projected from `ConjugateMildExistenceData.hmapsTo_pos`.
-/
theorem hasBFormSpectralPdeAgreement_conjugatePicardLimit_of_localized_data_with_hpost
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀)
    (hpost : ∀ σ, 0 < σ → σ < D.T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        0 < intervalDomainLift (conjugatePicardLimit p u₀ D.T σ) x)
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ < D.T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ < D.T →
      Set.EqOn (intervalDomainLift (conjugatePicardLimit p u₀ D.T σ))
        (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (aB : ℝ → ℕ → ℝ)
    (hsrcB : DuhamelSourceTimeC1 aB)
    (hsource_split : ∀ σ, 0 < σ → σ < D.T → ∀ n,
      aB σ n =
        coupledLogisticSourceCoeffs p (conjugatePicardLimit p u₀ D.T) σ n
          - p.χ₀ *
            coupledChemDivSourceCoeffs p (conjugatePicardLimit p u₀ D.T) σ n)
    (hB_restart : ∀ t₀, 0 < t₀ → t₀ < D.T →
      ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
        conjugatePicardLimit p u₀ D.T s y =
          ∑' n,
            localRestartCoeff
              (cosineCoeffs
                (intervalDomainLift
                  (conjugatePicardLimit p u₀ D.T (t₀ / 2))))
              (fun σ n => aB (t₀ / 2 + σ) n)
              (s - t₀ / 2) n * cosineMode n y.1)
    (hlogData : ∀ t, 0 < t → t < D.T →
      LogisticCosineFourierData p (conjugatePicardLimit p u₀ D.T) t)
    (hchemData : ∀ t, 0 < t → t < D.T →
      ChemDivCosineFourierData p
        ((conjugatePicardLimit p u₀ D.T) t)
        (coupledChemicalConcentration p
          (conjugatePicardLimit p u₀ D.T) t)) :
    HasBFormSpectralPdeAgreement p D.T
      (conjugatePicardLimit p u₀ D.T) := by
  constructor
  intro t₀ ht₀ ht₀T x hx
  set u : ℝ → intervalDomainPoint → ℝ :=
    conjugatePicardLimit p u₀ D.T
  set τ : ℝ := t₀ / 2 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hτT : τ < D.T := by rw [hτdef]; linarith
  have htmτ : t₀ - τ = τ := by rw [hτdef]; ring
  have hMnn : 0 ≤ D.M := D.hM.le
  have hubt := conjugatePicardLimit_hubt_of_picard_data D
  set a₀ : ℕ → ℝ := cosineCoeffs (intervalDomainLift (u τ)) with ha₀def
  set a : ℝ → ℕ → ℝ := fun σ n => aB (τ + σ) n with hadef
  have ha₀_bd : ∀ k, |a₀ k| ≤ 2 * D.M := by
    intro k
    refine ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
      (((ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two
        (hbsum τ hτpos hτT)).continuous.continuousOn).congr
          (hagree τ hτpos hτT)) hMnn ?_ k
    intro y hy
    rw [abs_of_pos (hpost τ hτpos hτT y hy)]
    have hyb := hubt τ hτpos hτT y hy
    linarith
  have srcShift : DuhamelSourceTimeC1 a := by
    simpa [a, add_comm] using
      ShenWork.IntervalDuhamelSourceShift.DuhamelSourceTimeC1.shift_nonneg
        hsrcB hτpos.le
  have hoff : 0 < t₀ - τ := by rw [htmτ]; exact hτpos
  have hrep : ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
      u s y = ∑' n, localRestartCoeff a₀ a (s - τ) n * cosineMode n y.1 := by
    have h := hB_restart t₀ ht₀ ht₀T
    simpa [u, a₀, a, τ, hτdef] using h
  have hsource_at : ∀ n, a (t₀ - τ) n =
      coupledLogisticSourceCoeffs p u t₀ n
        - p.χ₀ * coupledChemDivSourceCoeffs p u t₀ n := by
    intro n
    have harg : τ + (t₀ - τ) = t₀ := by ring
    change aB (τ + (t₀ - τ)) n =
      coupledLogisticSourceCoeffs p u t₀ n
        - p.χ₀ * coupledChemDivSourceCoeffs p u t₀ n
    rw [harg]
    simpa [u] using hsource_split t₀ ht₀ ht₀T n
  have hsum_b : Summable (fun n =>
      unitIntervalCosineEigenvalue n * |localRestartCoeff a₀ a (t₀ - τ) n|) := by
    rw [htmτ]
    exact ShenWork.IntervalResolverSpectralJointC2Producer.localRestartCoeff_eigenvalue_summable
      (τ := τ) (M := 2 * D.M) (a₀ := a₀) (a := a) hτpos ha₀_bd srcShift
  exact ⟨a₀, 2 * D.M, by nlinarith [D.hM.le], ha₀_bd,
    a, srcShift, τ, hoff, hlogData t₀ ht₀ ht₀T,
    hchemData t₀ ht₀ ht₀T, hrep, hsource_at, hsum_b⟩

/-- The localized B-form spectral provider with `hpost` discharged from the
absolute PID inf-threshold and `hB_restart` discharged from a global B-form
cosine representation. -/
theorem hasBFormSpectralPdeAgreement_conjugatePicardLimit_of_PID_global_restart
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (Hinf : ConjugatePicardInfThresholdData p u₀ D.T)
    (hsmall :
      |p.χ₀| * (heatGradientLinftyLinftyConstant *
          (2 * Real.sqrt D.T) * Hinf.CQ)
        + D.T * Hinf.CL ≤ paperPositiveFloor hu₀ / 2)
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ < D.T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ < D.T →
      Set.EqOn (intervalDomainLift (conjugatePicardLimit p u₀ D.T σ))
        (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (aInit : ℕ → ℝ)
    (aB : ℝ → ℕ → ℝ)
    (hsrcB : DuhamelSourceTimeC1 aB)
    (hsource_split : ∀ σ, 0 < σ → σ < D.T → ∀ n,
      aB σ n =
        coupledLogisticSourceCoeffs p (conjugatePicardLimit p u₀ D.T) σ n
          - p.χ₀ *
            coupledChemDivSourceCoeffs p (conjugatePicardLimit p u₀ D.T) σ n)
    (hB_global : ∀ t, 0 < t → t ≤ D.T →
      Set.EqOn (intervalDomainLift (conjugatePicardLimit p u₀ D.T t))
        (fun x => ∑' n, localRestartCoeff aInit aB t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hB_global_summable : ∀ t, 0 < t → t ≤ D.T →
      Summable (fun n => |localRestartCoeff aInit aB t n|))
    (hlogData : ∀ t, 0 < t → t < D.T →
      LogisticCosineFourierData p (conjugatePicardLimit p u₀ D.T) t)
    (hchemData : ∀ t, 0 < t → t < D.T →
      ChemDivCosineFourierData p
        ((conjugatePicardLimit p u₀ D.T) t)
        (coupledChemicalConcentration p
          (conjugatePicardLimit p u₀ D.T) t)) :
    HasBFormSpectralPdeAgreement p D.T
      (conjugatePicardLimit p u₀ D.T) := by
  have hpost := conjugatePicardLimit_hpost_of_PID
    (p := p) (u₀ := u₀) (T := D.T) hu₀ Hinf hsmall
  have ha_cont : ∀ k, ContinuousOn (fun s => aB s k) (Set.Icc 0 D.T) := by
    intro k
    exact (continuous_iff_continuousAt.2
      (fun s => (hsrcB.hderiv s k).continuousAt)).continuousOn
  have hB_restart :
      ∀ t₀, 0 < t₀ → t₀ < D.T →
        ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
          conjugatePicardLimit p u₀ D.T s y =
            ∑' n,
              localRestartCoeff
                (cosineCoeffs
                  (intervalDomainLift
                    (conjugatePicardLimit p u₀ D.T (t₀ / 2))))
                (fun σ n => aB (t₀ / 2 + σ) n)
                (s - t₀ / 2) n * cosineMode n y.1 :=
    conjugatePicardLimit_B_restart_of_global_cosine
      (p := p) (u₀ := u₀) (T := D.T) (a₀ := aInit) (aB := aB)
      ha_cont hB_global hB_global_summable
  exact hasBFormSpectralPdeAgreement_conjugatePicardLimit_of_localized_data_with_hpost
    D hpost bc hbsum hagree aB hsrcB hsource_split hB_restart hlogData
      hchemData

/-- Interior B-form PDE with the two localized provider inputs discharged as in
`hasBFormSpectralPdeAgreement_conjugatePicardLimit_of_PID_global_restart`. -/
theorem intervalConjugateMildSolution_pde_u_PID_global_restart
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (Hinf : ConjugatePicardInfThresholdData p u₀ D.T)
    (hsmall :
      |p.χ₀| * (heatGradientLinftyLinftyConstant *
          (2 * Real.sqrt D.T) * Hinf.CQ)
        + D.T * Hinf.CL ≤ paperPositiveFloor hu₀ / 2)
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ < D.T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ < D.T →
      Set.EqOn (intervalDomainLift (conjugatePicardLimit p u₀ D.T σ))
        (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (aInit : ℕ → ℝ)
    (aB : ℝ → ℕ → ℝ)
    (hsrcB : DuhamelSourceTimeC1 aB)
    (hsource_split : ∀ σ, 0 < σ → σ < D.T → ∀ n,
      aB σ n =
        coupledLogisticSourceCoeffs p (conjugatePicardLimit p u₀ D.T) σ n
          - p.χ₀ *
            coupledChemDivSourceCoeffs p (conjugatePicardLimit p u₀ D.T) σ n)
    (hB_global : ∀ t, 0 < t → t ≤ D.T →
      Set.EqOn (intervalDomainLift (conjugatePicardLimit p u₀ D.T t))
        (fun x => ∑' n, localRestartCoeff aInit aB t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hB_global_summable : ∀ t, 0 < t → t ≤ D.T →
      Summable (fun n => |localRestartCoeff aInit aB t n|))
    (hlogData : ∀ t, 0 < t → t < D.T →
      LogisticCosineFourierData p (conjugatePicardLimit p u₀ D.T) t)
    (hchemData : ∀ t, 0 < t → t < D.T →
      ChemDivCosineFourierData p
        ((conjugatePicardLimit p u₀ D.T) t)
        (coupledChemicalConcentration p
          (conjugatePicardLimit p u₀ D.T) t)) :
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
    hasBFormSpectralPdeAgreement_conjugatePicardLimit_of_PID_global_restart
      D hu₀ Hinf hsmall bc hbsum hagree aInit aB hsrcB hsource_split
      hB_global hB_global_summable hlogData hchemData
  exact intervalConjugateMildSolution_pde_u_from_picard_data_and_spectral D Hpde

#print axioms hasBFormSpectralPdeAgreement_conjugatePicardLimit_of_localized_data_with_hpost
#print axioms hasBFormSpectralPdeAgreement_conjugatePicardLimit_of_PID_global_restart
#print axioms intervalConjugateMildSolution_pde_u_PID_global_restart

end ShenWork.IntervalConjugatePicard
