import ShenWork.Paper3.IntervalDomainMPositiveHeatShiftSeed
import ShenWork.Paper3.IntervalDomainNegativeSensitivityMassFloor
import ShenWork.Paper2.IntervalConjugateKernelIBP

/-!
# Uniform mass in the square-root seed of a Holder bump

The tail regularity for faithful general powers is only `1/2`-Holder.  A
pointwise lower bound nevertheless produces a one-sided interval of fixed
width on which the half-sized square-root seed has fixed positive mass.
-/

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.Paper2.BFormPositiveDatumNegPart
open ShenWork.IntervalMildPicardThreshold (unitClip unitClip_of_mem)

def holderHalfSqrtSeedMassLower (eta G : ℝ) : ℝ :=
  (Real.sqrt (eta / 2) / 2) *
    min (1 / 2 : ℝ) ((eta / (2 * (G + 1))) ^ 2)

theorem holderHalfSqrtSeedMassLower_pos
    {eta G : ℝ} (heta : 0 < eta) (hG : 0 ≤ G) :
    0 < holderHalfSqrtSeedMassLower eta G := by
  unfold holderHalfSqrtSeedMassLower
  have hG1 : 0 < G + 1 := by linarith
  have hden : 0 < 2 * (G + 1) := mul_pos (by norm_num) hG1
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hfrac : 0 < eta / (2 * (G + 1)) := div_pos heta hden
  apply mul_pos
  · exact div_pos (Real.sqrt_pos.mpr (by linarith)) (by norm_num)
  · exact lt_min hhalf (sq_pos_of_pos hfrac)

/-- A positive point in a nonnegative `1/2`-Holder slice gives a uniform
lower bound for the total mass of its half square-root seed. -/
theorem halfRestartSliceSqrtSeed_integral_lower_of_holder_point
    {w : intervalDomainPoint → ℝ} {eta G : ℝ}
    (hw_cont : Continuous w)
    (heta : 0 < eta) (hG : 0 ≤ G)
    (hholder : ∀ x y : intervalDomainPoint,
      |w x - w y| ≤ G * |x.1 - y.1| ^ ((1 : ℝ) / 2))
    {x₀ : intervalDomainPoint} (hx₀ : eta ≤ w x₀) :
    holderHalfSqrtSeedMassLower eta G ≤
      ∫ y, halfRestartSliceSqrtSeed w y ∂(intervalMeasure 1) := by
  let q : ℝ := eta / (2 * (G + 1))
  let ell : ℝ := min (1 / 2 : ℝ) (q ^ 2)
  let c : ℝ := Real.sqrt (eta / 2) / 2
  let f : ℝ → ℝ := halfRestartSliceSqrtSeed w
  have hG1 : 0 < G + 1 := by linarith
  have hq : 0 < q := div_pos heta (by positivity)
  have hell : 0 < ell := by
    dsimp [ell]
    exact lt_min (by norm_num) (sq_pos_of_pos hq)
  have hellHalf : ell ≤ 1 / 2 := by
    dsimp [ell]
    exact min_le_left _ _
  have hellSq : ell ≤ q ^ 2 := by
    dsimp [ell]
    exact min_le_right _ _
  have hsqrtEll : Real.sqrt ell ≤ q := by
    calc
      Real.sqrt ell ≤ Real.sqrt (q ^ 2) := Real.sqrt_le_sqrt hellSq
      _ = q := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hq]
  have hGsqrt : G * Real.sqrt ell ≤ eta / 2 := by
    calc
      G * Real.sqrt ell ≤ G * q :=
        mul_le_mul_of_nonneg_left hsqrtEll hG
      _ ≤ (G + 1) * q := by
        exact mul_le_mul_of_nonneg_right (by linarith) hq.le
      _ = eta / 2 := by
        dsimp [q]
        field_simp [ne_of_gt hG1]
  have hf_cont : Continuous f := by
    simpa [f] using halfRestartSliceSqrtSeed_continuous hw_cont
  have hf_nonneg : ∀ y, 0 ≤ f y := by
    intro y
    dsimp [f, halfRestartSliceSqrtSeed, restartSliceSqrtSeed]
    positivity
  have hfint : IntervalIntegrable f volume (0 : ℝ) 1 := by
    exact hf_cont.continuousOn.intervalIntegrable_of_Icc (by norm_num)
  have hnonnegAe : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] f :=
    Filter.Eventually.of_forall hf_nonneg
  have hpoint (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1)
      (hdist : |x₀.1 - y| ≤ ell) : c ≤ f y := by
    let Y : intervalDomainPoint := ⟨y, hy⟩
    have hsqrtdist : Real.sqrt |x₀.1 - y| ≤ Real.sqrt ell :=
      Real.sqrt_le_sqrt hdist
    have hdrop0 := hholder x₀ Y
    have hdrop : w x₀ - w Y ≤ G * Real.sqrt ell := by
      calc
        w x₀ - w Y ≤ |w x₀ - w Y| := le_abs_self _
        _ ≤ G * |x₀.1 - Y.1| ^ ((1 : ℝ) / 2) := hdrop0
        _ = G * Real.sqrt |x₀.1 - y| := by
          simp only [Y, Real.sqrt_eq_rpow]
        _ ≤ G * Real.sqrt ell :=
          mul_le_mul_of_nonneg_left hsqrtdist hG
    have hwy : eta / 2 ≤ w Y := by linarith [hGsqrt]
    have hsqrt : Real.sqrt (eta / 2) ≤ Real.sqrt (w Y) :=
      Real.sqrt_le_sqrt hwy
    have hclip : w (unitClip y) = w Y := by
      rw [unitClip_of_mem hy]
    dsimp [c, f, halfRestartSliceSqrtSeed, restartSliceSqrtSeed]
    rw [hclip]
    exact div_le_div_of_nonneg_right hsqrt (by norm_num)
  have hinter : c * ell ≤ ∫ y in (0 : ℝ)..1, f y := by
    by_cases hxleft : x₀.1 ≤ 1 / 2
    · have hright : x₀.1 + ell ≤ 1 := by linarith [x₀.2.2]
      have hsub : Set.Icc x₀.1 (x₀.1 + ell) ⊆ Set.Icc (0 : ℝ) 1 :=
        fun y hy => ⟨le_trans x₀.2.1 hy.1, le_trans hy.2 hright⟩
      have hmonoSub :
          ∫ y in x₀.1..(x₀.1 + ell), c ≤
            ∫ y in x₀.1..(x₀.1 + ell), f y :=
        intervalIntegral.integral_mono_on (by linarith)
          intervalIntegrable_const
          ((hf_cont.continuousOn.mono hsub).intervalIntegrable_of_Icc
            (by linarith))
          (fun y hy => hpoint y (hsub hy) (by
            rw [abs_of_nonpos (sub_nonpos.mpr hy.1)]
            linarith [hy.2]))
      have hsubFull : (∫ y in x₀.1..(x₀.1 + ell), f y) ≤
          ∫ y in (0 : ℝ)..1, f y :=
        intervalIntegral.integral_mono_interval x₀.2.1 (by linarith)
          hright hnonnegAe hfint
      have hconst : (∫ _y in x₀.1..(x₀.1 + ell), c) = c * ell := by
        simp [intervalIntegral.integral_const, mul_comm]
      rw [hconst] at hmonoSub
      exact hmonoSub.trans hsubFull
    · have hxright : 1 / 2 < x₀.1 := lt_of_not_ge hxleft
      have hleft : 0 ≤ x₀.1 - ell := by linarith [x₀.2.1]
      have hsub : Set.Icc (x₀.1 - ell) x₀.1 ⊆ Set.Icc (0 : ℝ) 1 :=
        fun y hy => ⟨le_trans hleft hy.1, le_trans hy.2 x₀.2.2⟩
      have hmonoSub :
          ∫ y in (x₀.1 - ell)..x₀.1, c ≤
            ∫ y in (x₀.1 - ell)..x₀.1, f y :=
        intervalIntegral.integral_mono_on (by linarith)
          intervalIntegrable_const
          ((hf_cont.continuousOn.mono hsub).intervalIntegrable_of_Icc
            (by linarith))
          (fun y hy => hpoint y (hsub hy) (by
            rw [abs_of_nonneg (sub_nonneg.mpr hy.2)]
            linarith [hy.1]))
      have hsubFull : (∫ y in (x₀.1 - ell)..x₀.1, f y) ≤
          ∫ y in (0 : ℝ)..1, f y :=
        intervalIntegral.integral_mono_interval hleft (by linarith)
          x₀.2.2 hnonnegAe hfint
      have hconst : (∫ _y in (x₀.1 - ell)..x₀.1, c) = c * ell := by
        simp [intervalIntegral.integral_const, mul_comm]
      rw [hconst] at hmonoSub
      exact hmonoSub.trans hsubFull
  rw [ShenWork.Paper2.IntervalConjugateKernelIBP.intervalMeasure_one_integral_eq_intervalIntegral]
  simpa [holderHalfSqrtSeedMassLower, c, ell, q] using hinter

end ShenWork.Paper3

#print axioms ShenWork.Paper3.halfRestartSliceSqrtSeed_integral_lower_of_holder_point
