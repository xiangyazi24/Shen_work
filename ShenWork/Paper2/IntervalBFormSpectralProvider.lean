/-
  B-form spectral provider for the conjugate Picard limit.

  This file is additive.  It packages the B-form restart/spectral data needed by
  `HasBFormSpectralPdeAgreement` for
  `conjugatePicardLimit p u₀ D.T`, and then feeds the existing B-form PDE
  producer.  The strict positivity input used by the localized source machinery
  is not assumed separately: it is projected from the B-form Picard data, whose
  `hmapsTo_pos` field is the upstream small-time inf-threshold positivity
  discharge.
-/
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalDuhamelSourceShift
import ShenWork.PDE.IntervalResolverSpectralJointC2Producer

open Filter Topology Set

noncomputable section

namespace ShenWork.IntervalConjugatePicard

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalBFormSpectral
  (HasBFormSpectralPdeAgreement LogisticCosineFourierData
   ChemDivCosineFourierData)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceCoeffs
   coupledLogisticSourceCoeffs)

/-- Strict positivity of the conjugate Picard limit on the closed interval.

The upstream datum that makes this satisfiable is
`ConjugateMildExistenceData.hmapsTo_pos`; in the intended PID construction that
field is discharged by the small-time inf-threshold estimate for the B-form
Picard map. -/
theorem conjugatePicardLimit_hpost_of_picard_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) :
    ∀ σ, 0 < σ → σ < D.T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        0 < intervalDomainLift (conjugatePicardLimit p u₀ D.T σ) x := by
  intro σ hσ hσT x hx
  have hpos :=
    (conjugateMildSolutionData_of_data D).hpos σ hσ hσT.le ⟨x, hx⟩
  simpa [intervalDomainLift, hx] using hpos

/-- Upper bound of the conjugate Picard limit on the closed interval, projected
from the Picard ball data. -/
theorem conjugatePicardLimit_hubt_of_picard_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) :
    ∀ σ, 0 < σ → σ < D.T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        intervalDomainLift (conjugatePicardLimit p u₀ D.T σ) x ≤ D.M := by
  intro σ hσ hσT x hx
  have hbound :=
    (conjugateMildSolutionData_of_data D).hbound σ hσ hσT.le ⟨x, hx⟩
  have hle := (abs_le.mp hbound).2
  simpa [intervalDomainLift, hx] using hle

/-- Localized B-form spectral agreement for the conjugate Picard limit.

The hypotheses are the B-form analogues of the localized χ₀=0 provider:

* `bc`, `hbsum`, `hagree` give the per-slice cosine representation used to bound
  the restart base coefficients;
* `aB`, `hsrcB`, `hsource_split` are the total B-form source coefficients
  `logistic - χ₀ * chemDiv`;
* `hB_restart` is the B-form restart cosine representation coming from the
  conjugate-kernel Duhamel formula;
* `hlogData` and `hchemData` are the named Fourier inversion packages for the
  two physical source slices.

No χ₀=0 specialization is used. -/
theorem hasBFormSpectralPdeAgreement_conjugatePicardLimit_of_localized_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀)
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
  have hpost := conjugatePicardLimit_hpost_of_picard_data D
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

/-- B-form interior PDE for the conjugate Picard limit, with the localized
spectral provider assembled in this file. -/
theorem intervalConjugateMildSolution_pde_u_unconditional
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀)
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
    hasBFormSpectralPdeAgreement_conjugatePicardLimit_of_localized_data
      D bc hbsum hagree aB hsrcB hsource_split hB_restart hlogData hchemData
  exact intervalConjugateMildSolution_pde_u_from_picard_data_and_spectral D Hpde

#print axioms conjugatePicardLimit_hpost_of_picard_data
#print axioms hasBFormSpectralPdeAgreement_conjugatePicardLimit_of_localized_data
#print axioms intervalConjugateMildSolution_pde_u_unconditional

end ShenWork.IntervalConjugatePicard
