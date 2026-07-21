import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Uniqueness for the resolver equation `-v_zz + v = u`

The Green-representation discharge for `resolver_oscillation_bound` needs: the
solution `v` of `-v_zz + v = u` (the repo's pointwise `pde_v`) EQUALS the
convolution `½ e^{-|·|} ∗ u`.  Both solve the same 2nd-order ODE and are bounded,
so their difference `w := v − v_conv` satisfies `w'' = w` and is bounded — and the
only bounded `C²` solution of `w'' = w` on `ℝ` is `w ≡ 0`.

This file proves that uniqueness keystone (Fable's factoring route, 2026-07-21):
factor `w'' = w` into the two first-order equations `(w'+w)' = (w'+w)` and
`(w'−w)' = −(w'−w)`, integrate each to `w'+w = C e^{z}` and `w'−w = D e^{−z}`,
so `w = ½(C e^{z} − D e^{−z})`, and boundedness forces `C = D = 0`.
-/

open Filter Topology Real

noncomputable section

namespace ShenWork.Paper1

/-- A bounded function of the form `z ↦ C e^{z} + D e^{−z}` has `C = 0`.
(The `e^{z}` mode is unbounded at `+∞` unless its coefficient vanishes.) -/
theorem coeff_pos_zero_of_bounded {C D M : ℝ}
    (hbd : ∀ z : ℝ, |C * Real.exp z + D * Real.exp (-z)| ≤ M) :
    C = 0 := by
  by_contra hC
  -- `C e^z + D e^{-z} = e^z (C + D e^{-2z})`, and `C + D e^{-2z} → C ≠ 0`, `e^z → ∞`
  have hlim : Tendsto (fun z : ℝ => C * Real.exp z + D * Real.exp (-z)) atTop atBot ∨
      Tendsto (fun z : ℝ => C * Real.exp z + D * Real.exp (-z)) atTop atTop := by
    rcases lt_or_gt_of_ne hC with hneg | hpos
    · left
      have hCexp : Tendsto (fun z : ℝ => C * Real.exp z) atTop atBot :=
        Tendsto.const_mul_atTop_of_neg hneg Real.tendsto_exp_atTop
      have hDexp : Tendsto (fun z : ℝ => D * Real.exp (-z)) atTop (𝓝 0) := by
        have : Tendsto (fun z : ℝ => Real.exp (-z)) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
        simpa using (tendsto_const_nhds (x := D)).mul this
      exact hCexp.atBot_add hDexp
    · right
      have hCexp : Tendsto (fun z : ℝ => C * Real.exp z) atTop atTop :=
        Tendsto.const_mul_atTop hpos Real.tendsto_exp_atTop
      have hDexp : Tendsto (fun z : ℝ => D * Real.exp (-z)) atTop (𝓝 0) := by
        have : Tendsto (fun z : ℝ => Real.exp (-z)) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
        simpa using (tendsto_const_nhds (x := D)).mul this
      exact hCexp.atTop_add hDexp
  rcases hlim with hlim | hlim
  · -- unbounded below contradicts `≥ -M`
    have := (hlim.eventually (eventually_lt_atBot (-M - 1))).exists
    obtain ⟨z, hz⟩ := this
    have := hbd z
    rw [abs_le] at this
    linarith [this.1]
  · have := (hlim.eventually (eventually_gt_atTop (M + 1))).exists
    obtain ⟨z, hz⟩ := this
    have := hbd z
    rw [abs_le] at this
    linarith [this.2]

/-- Symmetrically, `D = 0` (the `e^{−z}` mode is unbounded at `−∞`). -/
theorem coeff_neg_zero_of_bounded {C D M : ℝ}
    (hbd : ∀ z : ℝ, |C * Real.exp z + D * Real.exp (-z)| ≤ M) :
    D = 0 := by
  -- apply `coeff_pos_zero_of_bounded` to `z ↦ D e^{z} + C e^{-z}` via reflection
  apply coeff_pos_zero_of_bounded (D := C) (M := M)
  intro z
  have := hbd (-z)
  simpa [neg_neg, add_comm] using this

/-- **Uniqueness keystone.**  A bounded `C²` function with `w'' = w` on `ℝ` is
identically `0`.  `w1 = w'`, `w2 = w''`; `hw`/`hw1` are the pointwise
`HasDerivAt` facts, `hode : w2 = w`, `hbd` the bound. -/
theorem bounded_solution_wzz_eq_w_is_zero
    {w w1 w2 : ℝ → ℝ}
    (hw : ∀ x, HasDerivAt w (w1 x) x)
    (hw1 : ∀ x, HasDerivAt w1 (w2 x) x)
    (hode : ∀ x, w2 x = w x)
    (hbd : ∃ M, ∀ x, |w x| ≤ M) :
    ∀ x, w x = 0 := by
  -- g z = e^{-z}(w1 z + w z) has derivative 0
  set g : ℝ → ℝ := fun z => Real.exp (-z) * (w1 z + w z) with hg
  have hgderiv : ∀ z, HasDerivAt g 0 z := by
    intro z
    have hexp : HasDerivAt (fun z : ℝ => Real.exp (-z)) (-Real.exp (-z)) z := by
      have h := ((hasDerivAt_id z).neg).exp
      simpa using h
    have hsum : HasDerivAt (fun z => w1 z + w z) (w2 z + w1 z) z :=
      (hw1 z).add (hw z)
    have := hexp.mul hsum
    have hz : -Real.exp (-z) * (w1 z + w z) + Real.exp (-z) * (w2 z + w1 z) = 0 := by
      rw [hode z]; ring
    rw [hz] at this
    exact this
  -- h z = e^{z}(w1 z - w z) has derivative 0
  set h : ℝ → ℝ := fun z => Real.exp z * (w1 z - w z) with hh
  have hhderiv : ∀ z, HasDerivAt h 0 z := by
    intro z
    have hexp : HasDerivAt (fun z : ℝ => Real.exp z) (Real.exp z) z := Real.hasDerivAt_exp z
    have hsub : HasDerivAt (fun z => w1 z - w z) (w2 z - w1 z) z :=
      (hw1 z).sub (hw z)
    have := hexp.mul hsub
    have hz : Real.exp z * (w1 z - w z) + Real.exp z * (w2 z - w1 z) = 0 := by
      rw [hode z]; ring
    rw [hz] at this
    exact this
  -- g and h are constant
  have hgconst : ∀ z, g z = g 0 :=
    fun z => is_const_of_deriv_eq_zero (fun x => (hgderiv x).differentiableAt)
      (fun x => (hgderiv x).deriv) z 0
  have hhconst : ∀ z, h z = h 0 :=
    fun z => is_const_of_deriv_eq_zero (fun x => (hhderiv x).differentiableAt)
      (fun x => (hhderiv x).deriv) z 0
  -- from g const: w1 + w = C e^{z}; from h const: w1 - w = D e^{-z}
  set C : ℝ := w1 0 + w 0 with hCdef
  set D : ℝ := w1 0 - w 0 with hDdef
  have hgval : g 0 = C := by simp [hg, hCdef]
  have hhval : h 0 = D := by simp [hh, hDdef]
  have hfw : ∀ z, w1 z + w z = C * Real.exp z := by
    intro z
    have heq : Real.exp (-z) * (w1 z + w z) = C := by
      have := (hgconst z).trans hgval; simpa [hg] using this
    have hz : (0:ℝ) < Real.exp z := Real.exp_pos z
    rw [Real.exp_neg] at heq
    field_simp at heq
    linarith [heq]
  have hhw : ∀ z, w1 z - w z = D * Real.exp (-z) := by
    intro z
    have heq : Real.exp z * (w1 z - w z) = D := by
      have := (hhconst z).trans hhval; simpa [hh] using this
    have hz : (0:ℝ) < Real.exp z := Real.exp_pos z
    rw [Real.exp_neg]
    field_simp
    linear_combination heq
  -- w = ½(C e^z - D e^{-z})
  have hwform : ∀ z, w z = (C * Real.exp z - D * Real.exp (-z)) / 2 := by
    intro z
    have h1 := hfw z
    have h2 := hhw z
    linarith
  -- boundedness → C = 0 and D = 0
  obtain ⟨M, hM⟩ := hbd
  have hbound2 : ∀ z, |C * Real.exp z + (-D) * Real.exp (-z)| ≤ 2 * M := by
    intro z
    have hw2 : (2 : ℝ) * w z = C * Real.exp z - D * Real.exp (-z) := by
      rw [hwform z]; ring
    have : C * Real.exp z + (-D) * Real.exp (-z) = 2 * w z := by rw [hw2]; ring
    rw [this, abs_mul]
    have : |(2:ℝ)| = 2 := by norm_num
    rw [this]
    have := hM z; nlinarith [this, abs_nonneg (w z)]
  have hC0 : C = 0 := coeff_pos_zero_of_bounded hbound2
  have hD0 : D = 0 := by
    have := coeff_neg_zero_of_bounded hbound2
    linarith
  intro z
  rw [hwform z, hC0, hD0]
  simp

section AxiomAudit

#print axioms bounded_solution_wzz_eq_w_is_zero

end AxiomAudit

end ShenWork.Paper1
