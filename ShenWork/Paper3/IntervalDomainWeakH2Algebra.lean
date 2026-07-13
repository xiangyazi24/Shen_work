/- Algebra and reconstruction for weak Neumann H2 source profiles. -/
import ShenWork.Paper3.IntervalDomainResolvedSourceRegularityProducer
import ShenWork.Paper2.IntervalReflCircleContinuousOn

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalCosineInversion
open ShenWork.PDE.IntervalMildSourceDecayHelper
open ShenWork.Paper2

noncomputable section

noncomputable def intervalWeakH2Neumann_const (c : ℝ) :
    IntervalWeakH2Neumann (fun _x : ℝ => c) :=
  intervalWeakH2Neumann_of_contDiffOn
    (by fun_prop) (by simp) (by simp) (by simp) (by simp)

/-- Weak Neumann `H²` is stable under subtraction when the two original
profiles are interval-integrable. -/
noncomputable def IntervalWeakH2Neumann.sub
    {f g : ℝ → ℝ} (Hf : IntervalWeakH2Neumann f)
    (Hg : IntervalWeakH2Neumann g)
    (hf : IntervalIntegrable f volume 0 1)
    (hg : IntervalIntegrable g volume 0 1) :
    IntervalWeakH2Neumann (fun x => f x - g x) where
  secondDeriv := fun x => Hf.secondDeriv x - Hg.secondDeriv x
  second_intervalIntegrable :=
    Hf.second_intervalIntegrable.sub Hg.second_intervalIntegrable
  second_abs_integral_bound := by
    let B := ∫ x in (0 : ℝ)..1,
      |Hf.secondDeriv x - Hg.secondDeriv x|
    refine ⟨B, ?_, le_rfl⟩
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x _ => abs_nonneg _)
  weak_cosine_laplacian := by
    intro k
    let c : ℝ → ℝ := fun x => Real.cos ((k : ℝ) * Real.pi * x)
    have hc : ContinuousOn c (Set.uIcc (0 : ℝ) 1) := by fun_prop
    have hf2 := Hf.second_intervalIntegrable.continuousOn_mul hc
    have hg2 := Hg.second_intervalIntegrable.continuousOn_mul hc
    have hfc := hf.continuousOn_mul hc
    have hgc := hg.continuousOn_mul hc
    change (∫ x in (0 : ℝ)..1,
        c x * (Hf.secondDeriv x - Hg.secondDeriv x)) =
      -((k : ℝ) * Real.pi) ^ 2 *
        ∫ x in (0 : ℝ)..1, c x * (f x - g x)
    rw [show (∫ x in (0 : ℝ)..1,
        c x * (Hf.secondDeriv x - Hg.secondDeriv x)) =
      (∫ x in (0 : ℝ)..1, c x * Hf.secondDeriv x) -
        ∫ x in (0 : ℝ)..1, c x * Hg.secondDeriv x by
          rw [← intervalIntegral.integral_sub hf2 hg2]
          apply intervalIntegral.integral_congr
          intro x _
          ring,
      show (∫ x in (0 : ℝ)..1, c x * (f x - g x)) =
        (∫ x in (0 : ℝ)..1, c x * f x) -
          ∫ x in (0 : ℝ)..1, c x * g x by
            rw [← intervalIntegral.integral_sub hfc hgc]
            apply intervalIntegral.integral_congr
            intro x _
            ring,
      Hf.weak_cosine_laplacian k, Hg.weak_cosine_laplacian k]
    ring

/-- A weak certificate plus closed-interval continuity produces the complete
qualitative resolver package.  Fourier summability is recovered from the
certificate's quadratic cosine decay, so no endpoint regularity is hidden in
the clamped global representative. -/
noncomputable def resolvedSourceProfileRegularity_of_weakH2
    {f : ℝ → ℝ} (H : IntervalWeakH2Neumann f)
    (hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
    ResolvedSourceProfileRegularity f := by
  let F : ℝ → ℝ := fun x => f (clamp01 x)
  have hFcont : Continuous F := by
    refine continuousOn_univ.mp ?_
    exact hcont.comp clamp01_continuous.continuousOn
      (fun x _ => clamp01_mem x)
  have hFeq : ∀ x ∈ Set.Icc (0 : ℝ) 1, F x = f x := by
    intro x hx
    dsimp [F]
    rw [clamp01_eq_self hx]
  let hex := intervalWeakH2Neumann_cosineCoeff_quadratic_decay H
  let C := Classical.choose hex
  have hC := (Classical.choose_spec hex).1
  have hdecay := (Classical.choose_spec hex).2
  let Hd : ResolvedSourceCoeffQuadraticDecay (cosineCoeffs f) :=
    ⟨C, hC, hdecay⟩
  have hfabs : Summable (fun n : ℕ => |cosineCoeffs f n|) := Hd.abs_summable
  have hFabs : Summable (fun n : ℕ => |cosineCoeffs F n|) := by
    refine hfabs.congr (fun n => ?_)
    rw [cosineCoeffs_congr_on_Icc (fun x hx => hFeq x hx) n]
  have hFsum :=
    IntervalReflCircleContinuousOn.fourierCoeff_reflCircle_summable_of_cosineCoeff_abs_continuousOn
      hFcont.continuousOn hFabs
  exact
    { weakH2 := H
      representative := F
      representative_continuous := hFcont
      representative_fourier_summable := hFsum
      representative_eq := hFeq
      coeff_eq := fun k =>
        cosineCoeffs_congr_on_Icc (fun x hx => (hFeq x hx).symm) k }

#print axioms intervalWeakH2Neumann_const
#print axioms IntervalWeakH2Neumann.sub
#print axioms resolvedSourceProfileRegularity_of_weakH2

end

end ShenWork.Paper3
