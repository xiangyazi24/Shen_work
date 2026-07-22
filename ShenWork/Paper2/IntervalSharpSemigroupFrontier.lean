import ShenWork.Paper2.IntervalSharpSpectralCalculus
import ShenWork.PDE.IntervalSemigroupComposition

/-!
# Concrete full-kernel bridge and exact Paper-2 statement frontier

The current `intervalDomainSemigroupEstimateData` uses
`intervalSemigroupOperator 1`, the zeroth-reflection helper.  The genuine
Neumann propagator is `intervalFullSemigroupOperator`.  This file defines its
spectrally shifted version, proves its exact diagonal action, and records the
constant-mode obstruction that prevents the unshifted propagator from
satisfying the exponential branch of Paper-2 Lemma 2.1.

It deliberately does not manufacture a `SemigroupEstimateData` instance from
arbitrary point functions: the statement structure has no `MemLp` or
fractional-domain hypotheses, while the honest series theorems require them.
-/

noncomputable section

open MeasureTheory

namespace ShenWork.Paper2.IntervalSharpSemigroupFrontier

open ShenWork.Paper2
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.HeatKernelGradientEstimates
open ShenWork.PDE.ResolventEstimate
open ShenWork.PDE.AnalyticSemigroupGen
open ShenWork.Paper2.IntervalSharpSpectralCalculus

/-- The physically correct shifted Neumann heat propagator on `[0,1]`. -/
def intervalShiftedFullSemigroupOperator
    (omega t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-(omega * t)) * intervalFullSemigroupOperator t f x

/-- Scalar multiplication commutes with normalized Neumann cosine
coefficients. -/
theorem cosineCoeffs_const_mul (c : ℝ) (f : ℝ → ℝ) (n : ℕ) :
    cosineCoeffs (fun x => c * f x) n = c * cosineCoeffs f n := by
  have hraw : ∀ m : ℕ,
      unitIntervalCosineRawCoeff (fun x => ((c * f x : ℝ) : ℂ)) m =
        (c : ℂ) * unitIntervalCosineRawCoeff
          (fun x => ((f x : ℝ) : ℂ)) m := by
    intro m
    unfold unitIntervalCosineRawCoeff
    calc
      (∫ x in (0 : ℝ)..1,
          (Real.cos ((m : ℝ) * Real.pi * x) : ℂ) *
            ((c * f x : ℝ) : ℂ)) =
          ∫ x in (0 : ℝ)..1,
            (c : ℂ) *
              ((Real.cos ((m : ℝ) * Real.pi * x) : ℂ) *
                ((f x : ℝ) : ℂ)) := by
        apply intervalIntegral.integral_congr
        intro x _hx
        change
          (Real.cos ((m : ℝ) * Real.pi * x) : ℂ) *
              ((c * f x : ℝ) : ℂ) =
            (c : ℂ) *
              ((Real.cos ((m : ℝ) * Real.pi * x) : ℂ) *
                ((f x : ℝ) : ℂ))
        rw [Complex.ofReal_mul]
        ring_nf
      _ = (c : ℂ) *
          ∫ x in (0 : ℝ)..1,
            (Real.cos ((m : ℝ) * Real.pi * x) : ℂ) *
              ((f x : ℝ) : ℂ) := by
        exact intervalIntegral.integral_const_mul
          (μ := volume) (a := (0 : ℝ)) (b := 1) (c : ℂ)
          (fun x =>
            (Real.cos ((m : ℝ) * Real.pi * x) : ℂ) *
              ((f x : ℝ) : ℂ))
  unfold cosineCoeffs unitIntervalNeumannCosineCoeff
  by_cases hn : n = 0
  · subst n
    simp only [if_pos]
    rw [hraw 0]
    simp [Complex.mul_re]
  · simp only [if_neg hn]
    rw [hraw n]
    simp [Complex.mul_re]
    ring_nf

/-- Exact cosine diagonalization of the shifted full-kernel propagator. -/
theorem cosineCoeffs_intervalShiftedFullSemigroupOperator
    {omega t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs f n| ≤ M) (n : ℕ) :
    cosineCoeffs
        (fun x => intervalShiftedFullSemigroupOperator omega t f x) n =
      Real.exp (-(shiftedNeumannEigenvalue omega n * t)) *
        cosineCoeffs f n := by
  rw [show
      (fun x => intervalShiftedFullSemigroupOperator omega t f x) =
        fun x => Real.exp (-(omega * t)) *
          intervalFullSemigroupOperator t f x by rfl]
  rw [cosineCoeffs_const_mul,
    ShenWork.IntervalSemigroupComposition.cosineCoeffs_semigroup ht hf hM n]
  unfold shiftedNeumannEigenvalue
  rw [show
      -((ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue n + omega) * t) =
        -(omega * t) +
          -(t * ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue n) by ring,
    Real.exp_add]
  rw [show unitIntervalCosineEigenvalue n =
      ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue n by
    unfold unitIntervalCosineEigenvalue
    simp [ShenWork.Paper3.unitIntervalNeumannSpectrum]
    ring]
  ring_nf

/-- Constant cosine coefficient sequence. -/
def constantModeCoeff : ℕ → ℂ :=
  fun n => if n = 0 then 1 else 0

theorem constantModeCoeff_l2Norm :
    coeffL2Norm constantModeCoeff = 1 := by
  unfold coeffL2Norm coeffL2Energy constantModeCoeff
  rw [tsum_eq_single 0]
  · norm_num
  · intro n hn
    simp [hn]

/-- The unshifted Neumann heat flow fixes the constant mode. -/
theorem unshiftedNeumannHeatCoeff_constantMode
    (t : ℝ) :
    shiftedNeumannHeatCoeff 0 t constantModeCoeff = constantModeCoeff := by
  funext n
  by_cases hn : n = 0
  · subst n
    simp [shiftedNeumannHeatCoeff, shiftedNeumannEigenvalue,
      ShenWork.Paper3.unitIntervalNeumannSpectrum, constantModeCoeff]
  · simp [shiftedNeumannHeatCoeff, constantModeCoeff, hn]

/-- Formal constant-mode obstruction: an unshifted Neumann semigroup cannot
obey the positive exponential factor in Lemma 2.1, even at `sigma = 0`. -/
theorem unshiftedNeumann_constantMode_forbids_exp_decay
    {delta : ℝ} (hdelta : 0 < delta) :
    ¬ ∃ C : ℝ, ∀ t > 0,
      shiftedSpectralFractionalNorm 1 0
          (shiftedNeumannHeatCoeff 0 t constantModeCoeff) ≤
        C * t ^ (-(0 : ℝ)) * Real.exp (-(delta * t)) *
          coeffL2Norm constantModeCoeff := by
  intro h
  apply ShenWork.Paper2.IntervalDomainLemma21.one_not_bounded_by_exp_decay
    hdelta
  rcases h with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro t ht
  have hbound := hC t ht
  rw [unshiftedNeumannHeatCoeff_constantMode] at hbound
  have hfrac0 :
      shiftedSpectralFractionalNorm 1 0 constantModeCoeff = 1 := by
    simpa [constantModeCoeff] using
      shiftedSpectralFractionalNorm_one_constantMode 0
  rw [hfrac0, constantModeCoeff_l2Norm] at hbound
  simpa using hbound

/-- Generic exact-statement obstruction.  Any `SemigroupEstimateData` with a
normalized fixed mode violates `Lemma_2_1`, because that lemma asks for decay
at every `0 < delta < p.mu`. -/
theorem Lemma_2_1_not_of_fixed_normalized_mode
    {D : BoundedDomainData} (p : CM2Params) (S : SemigroupEstimateData D)
    (u : D.Point → ℝ)
    (hfixed : ∀ t > 0, S.semigroup t u = u)
    (hfrac : S.fractionalNorm 0 1 u = 1)
    (hlp : S.lpNorm 1 u = 1) :
    ¬ Lemma_2_1 D p S := by
  intro hlemma
  have hdelta_pos : 0 < p.μ / 2 := by linarith [p.hμ]
  have hdelta_lt : p.μ / 2 < p.μ := by linarith [p.hμ]
  rcases hlemma.1 0 1 (p.μ / 2)
      (by norm_num) (by norm_num) hdelta_pos hdelta_lt with
    ⟨C, _hCpos, hbound⟩
  apply ShenWork.Paper2.IntervalDomainLemma21.one_not_bounded_by_exp_decay
    hdelta_pos
  refine ⟨C, ?_⟩
  intro t ht
  have h := hbound t ht u
  rw [hfixed t ht, hfrac, hlp] at h
  simpa using h

#print axioms cosineCoeffs_const_mul
#print axioms cosineCoeffs_intervalShiftedFullSemigroupOperator
#print axioms constantModeCoeff_l2Norm
#print axioms unshiftedNeumannHeatCoeff_constantMode
#print axioms unshiftedNeumann_constantMode_forbids_exp_decay
#print axioms Lemma_2_1_not_of_fixed_normalized_mode

end ShenWork.Paper2.IntervalSharpSemigroupFrontier
