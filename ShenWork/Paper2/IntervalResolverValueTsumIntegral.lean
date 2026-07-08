/-
  Termwise integration of the resolver value series.

  Proves ∫_a^b R(x) dx = ∑ c_k · ∫_a^b cos(kπx) dx for a,b ∈ (0,1),
  using `integral_tsum_pairing` with ψ = 1_{(a,b]} indicator.

  Source: Q3978 (ChatGPT) + user-provided Ioc architecture.
-/
import ShenWork.Paper2.IntervalResolverWeakODEBridge
import ShenWork.Paper2.IntervalTruncatedTestedSpectral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory intervalIntegral
open ShenWork.IntervalDomain
open ShenWork.PDE
open ShenWork.Paper2
open ShenWork.IntervalResolverWeakBounds
open scoped Topology BigOperators

noncomputable section

namespace ShenWork.IntervalResolverWeakBounds

private lemma integral_intervalMeasure_mul_indicator_Ioc_eq_intervalIntegral_of_le
    {f : ℝ → ℝ} {a b : ℝ}
    (ha0 : 0 ≤ a) (hb1 : b ≤ 1) (hab : a ≤ b) :
    (∫ x, f x * (Set.Ioc a b).indicator (fun _ : ℝ => (1 : ℝ)) x
        ∂ intervalMeasure 1)
      = ∫ x in a..b, f x := by
  classical
  have hsub : Set.Ioc a b ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨ha0.trans hx.1.le, hx.2.trans hb1⟩
  have hmul :
      (fun x : ℝ => f x * (Set.Ioc a b).indicator (fun _ : ℝ => (1 : ℝ)) x)
        = (Set.Ioc a b).indicator f := by
    ext x
    by_cases hx : x ∈ Set.Ioc a b <;> simp [hx]
  have hinter :
      Set.Ioc a b ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc a b :=
    Set.inter_eq_left.mpr hsub
  rw [hmul]
  rw [MeasureTheory.integral_indicator measurableSet_Ioc]
  rw [intervalIntegral.integral_of_le hab]
  simp [intervalMeasure, intervalSet, Measure.restrict_restrict, hinter]

private lemma integral_zero_one_mul_indicator_Ioc_eq_intervalIntegral_of_le
    {f : ℝ → ℝ} {a b : ℝ}
    (ha0 : 0 < a) (hb1 : b < 1) (hab : a ≤ b) :
    (∫ x in (0 : ℝ)..1,
        f x * (Set.Ioc a b).indicator (fun _ : ℝ => (1 : ℝ)) x)
      = ∫ x in a..b, f x := by
  classical
  have hsub : Set.Ioc a b ⊆ Set.Ioc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨lt_trans ha0 hx.1, hx.2.trans hb1.le⟩
  have hmul :
      (fun x : ℝ => f x * (Set.Ioc a b).indicator (fun _ : ℝ => (1 : ℝ)) x)
        = (Set.Ioc a b).indicator f := by
    ext x
    by_cases hx : x ∈ Set.Ioc a b <;> simp [hx]
  have hinter :
      Set.Ioc a b ∩ Set.Ioc (0 : ℝ) 1 = Set.Ioc a b :=
    Set.inter_eq_left.mpr hsub
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [hmul]
  rw [MeasureTheory.integral_indicator measurableSet_Ioc]
  rw [intervalIntegral.integral_of_le hab]
  simp [Measure.restrict_restrict, hinter]

private theorem resolverValueSeriesReal_integral_tsum_of_le
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    {a b : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1)
    (hab : a ≤ b) :
    (∫ x in a..b, resolverValueSeriesReal p u x)
      =
    ∑' k : ℕ,
      (intervalNeumannResolverCoeff p u k).re *
        ∫ x in a..b, unitIntervalCosineMode k x := by
  classical
  let C : ℕ → ℝ := fun k => (intervalNeumannResolverCoeff p u k).re
  let E : ℕ → ℝ → ℝ := fun k x => unitIntervalCosineMode k x
  let B : ℕ → ℝ := fun _ => (1 : ℝ)
  let ψ : ℝ → ℝ := (Set.Ioc a b).indicator (fun _ : ℝ => (1 : ℝ))
  have he : ∀ n : ℕ, Continuous (E n) := by
    intro n; dsimp [E]; unfold unitIntervalCosineMode; fun_prop
  have heB : ∀ n : ℕ, ∀ x ∈ Set.Icc (0 : ℝ) 1, |E n x| ≤ B n := by
    intro n x _
    dsimp [E, B]
    simpa [unitIntervalCosineMode] using Real.abs_cos_le_one ((n : ℝ) * Real.pi * x)
  have hsum : Summable (fun n : ℕ => |C n| * B n) := by
    simpa [B] using resolverCoeff_re_abs_summable_of_continuousOn p hUcont
  have hrep : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      resolverValueSeriesReal p u x = ∑' n : ℕ, C n * E n x := by
    intro x _; simp [resolverValueSeriesReal, C, E]
  have hψm : AEStronglyMeasurable ψ (intervalMeasure 1) := by
    exact ((measurable_const : Measurable (fun _ : ℝ => (1 : ℝ))).indicator
      measurableSet_Ioc).aestronglyMeasurable
  have hψb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |ψ x| ≤ (1 : ℝ) := by
    intro x _; by_cases hxab : x ∈ Set.Ioc a b <;> simp [ψ, hxab]
  have hpair := integral_tsum_pairing
    (w := resolverValueSeriesReal p u) (ψ := ψ) (c := C) (B := B) (e := E) (Cψ := 1)
    he heB hsum hrep hψm hψb
  have hleft :
      (∫ x, resolverValueSeriesReal p u x * ψ x ∂ intervalMeasure 1)
        = ∫ x in a..b, resolverValueSeriesReal p u x := by
    simpa [ψ] using
      integral_intervalMeasure_mul_indicator_Ioc_eq_intervalIntegral_of_le
        (f := resolverValueSeriesReal p u) ha.1.le hb.2.le hab
  have hright :
      (∑' n : ℕ, C n * ∫ x in (0 : ℝ)..1, E n x * ψ x)
        = ∑' n : ℕ, C n * ∫ x in a..b, E n x := by
    apply tsum_congr; intro n; congr 1
    simpa [ψ, E] using
      integral_zero_one_mul_indicator_Ioc_eq_intervalIntegral_of_le
        (f := E n) ha.1 hb.2 hab
  calc
    ∫ x in a..b, resolverValueSeriesReal p u x
        = ∫ x, resolverValueSeriesReal p u x * ψ x ∂ intervalMeasure 1 := hleft.symm
    _ = ∑' n : ℕ, C n * ∫ x in (0 : ℝ)..1, E n x * ψ x := hpair
    _ = ∑' n : ℕ, C n * ∫ x in a..b, E n x := hright
    _ = ∑' k : ℕ,
        (intervalNeumannResolverCoeff p u k).re *
          ∫ x in a..b, unitIntervalCosineMode k x := by simp [C, E]

theorem resolverValueSeriesReal_integral_tsum
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    {a b : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ x in a..b, resolverValueSeriesReal p u x)
      =
    ∑' k : ℕ,
      (intervalNeumannResolverCoeff p u k).re *
        ∫ x in a..b, unitIntervalCosineMode k x := by
  classical
  by_cases hab : a ≤ b
  · exact resolverValueSeriesReal_integral_tsum_of_le p hUcont ha hb hab
  · have hba : b ≤ a := le_of_not_ge hab
    have hswap := resolverValueSeriesReal_integral_tsum_of_le p hUcont hb ha hba
    calc
      ∫ x in a..b, resolverValueSeriesReal p u x
          = -(∫ x in b..a, resolverValueSeriesReal p u x) := by
            rw [intervalIntegral.integral_symm b a]
      _ = -(∑' k : ℕ,
            (intervalNeumannResolverCoeff p u k).re *
              ∫ x in b..a, unitIntervalCosineMode k x) := by rw [hswap]
      _ = ∑' k : ℕ,
            (intervalNeumannResolverCoeff p u k).re *
              ∫ x in a..b, unitIntervalCosineMode k x := by
            have hterm :
                (fun k : ℕ =>
                  (intervalNeumannResolverCoeff p u k).re *
                    ∫ x in b..a, unitIntervalCosineMode k x)
                  =
                fun k : ℕ =>
                  -((intervalNeumannResolverCoeff p u k).re *
                    ∫ x in a..b, unitIntervalCosineMode k x) := by
              funext k; rw [intervalIntegral.integral_symm a b]; ring
            rw [hterm, tsum_neg]; simp

end ShenWork.IntervalResolverWeakBounds
