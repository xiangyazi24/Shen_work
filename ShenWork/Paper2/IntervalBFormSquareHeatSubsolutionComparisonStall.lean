import ShenWork.Paper2.IntervalBFormSquareHeatSubsolution
import ShenWork.PDE.ParabolicMaxPrinciple
import Mathlib.Analysis.Calculus.Deriv.Inverse

open Filter Topology Set

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

namespace NeumannLinearDriftComparisonStall

/-!
This file is intentionally additive.  It records the exact obstruction to
closing `NeumannLinearDriftComparison` from
`PDE.ParabolicMaxPrinciple.comparison_principle` without changing the existing
interfaces.

The tree comparison theorem is a whole-line theorem for
`u_t - u_xx ≤ g(u)` / `g(v) ≤ v_t - v_xx`, with classical regularity and
boundedness carried by `IsClassicalSubSolution` and
`IsClassicalSuperSolution`.  The interval B-form comparison interface below is
instead a Neumann interval drift-reaction statement using bare `deriv` in the
residual and carrying no continuity, differentiability, or boundedness
hypotheses for the test subsolution `w`.

The counterexample below is the minimal gap: with zero coefficients and zero
solution, a one-point spike has zero raw `deriv` residual in Lean's derivative
API, satisfies the stated initial and Neumann endpoint clauses, but violates
the desired comparison conclusion at the spike.  Hence the current Prop cannot
be discharged honestly from the tree theorem; the missing data must be added
before the max-principle machinery can be reused.
-/

def pointSpike (t₀ x₀ : ℝ) : ℝ → ℝ → ℝ :=
  fun t x => if t = t₀ ∧ x = x₀ then 1 else 0

lemma deriv_singleton_spike_eq_zero (a x : ℝ) :
    deriv (fun y : ℝ => if y = a then (1 : ℝ) else 0) x = 0 := by
  classical
  refine deriv_zero_of_frequently_const (f := fun y : ℝ => if y = a then (1 : ℝ) else 0)
    (x := x) (c := 0) ?_
  by_cases hx : x = a
  · subst x
    have hev : ∀ᶠ y in 𝓝[≠] a, (fun y : ℝ => if y = a then (1 : ℝ) else 0) y = 0 := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hyne : y ≠ a := by simpa using hy
      simp [hyne]
    exact hev.frequently
  · have hopen : IsOpen ({a}ᶜ : Set ℝ) := isClosed_singleton.isOpen_compl
    have hmem : x ∈ ({a}ᶜ : Set ℝ) := by simpa using hx
    have hnhds : ({a}ᶜ : Set ℝ) ∈ 𝓝 x := hopen.mem_nhds hmem
    have hev : ∀ᶠ y in 𝓝[≠] x, (fun y : ℝ => if y = a then (1 : ℝ) else 0) y = 0 := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds hnhds] with y hy
      have hyne : y ≠ a := by simpa using hy
      simp [hyne]
    exact hev.frequently

lemma deriv_pointSpike_time_eq_zero (t₀ x₀ t x : ℝ) :
    deriv (fun τ : ℝ => pointSpike t₀ x₀ τ x) t = 0 := by
  classical
  by_cases hx : x = x₀
  · subst x
    simpa [pointSpike] using deriv_singleton_spike_eq_zero t₀ t
  · have hfun : (fun τ : ℝ => pointSpike t₀ x₀ τ x) = fun _ : ℝ => 0 := by
      funext τ
      simp [pointSpike, hx]
    simp [hfun]

lemma deriv_pointSpike_space_eq_zero (t₀ x₀ t x : ℝ) :
    deriv (fun y : ℝ => pointSpike t₀ x₀ t y) x = 0 := by
  classical
  by_cases ht : t = t₀
  · subst t
    simpa [pointSpike, and_comm] using deriv_singleton_spike_eq_zero x₀ x
  · have hfun : (fun y : ℝ => pointSpike t₀ x₀ t y) = fun _ : ℝ => 0 := by
      funext y
      simp [pointSpike, ht]
    simp [hfun]

lemma pointSpike_dx_fun_eq_zero (t₀ x₀ t : ℝ) :
    (fun y : ℝ => deriv (fun z : ℝ => pointSpike t₀ x₀ t z) y) =
      fun _ : ℝ => 0 := by
  funext y
  exact deriv_pointSpike_space_eq_zero t₀ x₀ t y

lemma deriv_pointSpike_second_space_eq_zero (t₀ x₀ t x : ℝ) :
    deriv (fun z : ℝ => deriv (fun y : ℝ => pointSpike t₀ x₀ t y) z) x = 0 := by
  rw [pointSpike_dx_fun_eq_zero t₀ x₀ t]
  simp

lemma pointSpike_zero_coeff_residual_eq_zero (t₀ x₀ t x : ℝ) :
    neumannLinearDriftResidual
      (fun _ _ : ℝ => 0) (fun _ _ : ℝ => 0) (pointSpike t₀ x₀) t x = 0 := by
  simp [neumannLinearDriftResidual,
    deriv_pointSpike_time_eq_zero,
    deriv_pointSpike_second_space_eq_zero]

def zeroNeumannLinearDriftSolution :
    NeumannLinearDriftSolution 1
      (fun _ _ : ℝ => 0) (fun _ _ : ℝ => 0) (fun _ : ℝ => 0)
      (fun _ _ : ℝ => 0) where
  initial := by
    intro x hx
    rfl
  pde := by
    intro t x ht htT hx
    simp [neumannLinearDriftResidual]
  neumann := by
    intro t ht htT
    simp

theorem not_zero_coeff_zero_solution_comparison :
    ¬ NeumannLinearDriftComparison 1
      (fun _ _ : ℝ => 0) (fun _ _ : ℝ => 0) (fun _ : ℝ => 0)
      (fun _ _ : ℝ => 0) := by
  classical
  intro hcmp
  let w : ℝ → ℝ → ℝ := pointSpike (1 / 2) (1 / 2)
  have hinit : ∀ x ∈ Set.Icc (0 : ℝ) 1, w 0 x ≤ (fun _ : ℝ => 0) x := by
    intro x hx
    simp [w, pointSpike]
  have hres :
      ∀ t x, 0 < t → t < (1 : ℝ) → x ∈ Set.Ioo (0 : ℝ) 1 →
        neumannLinearDriftResidual
          (fun _ _ : ℝ => 0) (fun _ _ : ℝ => 0) w t x ≤ 0 := by
    intro t x ht htT hx
    rw [pointSpike_zero_coeff_residual_eq_zero]
  have hneu :
      ∀ t, 0 < t → t < (1 : ℝ) →
        deriv (fun z : ℝ => w t z) 0 = 0 ∧
        deriv (fun z : ℝ => w t z) 1 = 0 := by
    intro t ht htT
    constructor <;> exact deriv_pointSpike_space_eq_zero (1 / 2) (1 / 2) t _
  have hle :=
    hcmp w (by norm_num) zeroNeumannLinearDriftSolution hinit hres hneu
      (1 / 2) (1 / 2) (by norm_num) (by norm_num)
      (by constructor <;> norm_num)
  have hspike : w (1 / 2) (1 / 2) = 1 := by
    simp [w, pointSpike]
  norm_num [hspike] at hle

end NeumannLinearDriftComparisonStall

end ShenWork.Paper2.BFormPositiveDatumNegPart
