import Mathlib.Analysis.ODE.Gronwall

/-!
# Eventual absorption for a scalar linear damping inequality

This file isolates the scalar argument used by the minimal-model absorbing
estimate.  The carrying level `K` is fixed before the trajectory, whereas the
entrance time may depend on the value of the trajectory at one positive time.
-/

open Filter Set Topology

namespace ShenWork.Paper3

noncomputable section

/-- A positive-time differential inequality `E' / p + E ≤ K` forces the
trajectory into the fixed absorbing interval `(-∞, K + 1]`.  No initial
energy occurs in the eventual bound; it only affects the entrance time. -/
theorem eventually_le_add_one_of_linear_damping
    {E : ℝ → ℝ} {p K : ℝ}
    (hp : 0 < p)
    (hderiv : ∀ t, 0 < t → HasDerivAt E (deriv E t) t)
    (hdamp : ∀ t, 0 < t → (1 / p) * deriv E t + E t ≤ K) :
    ∀ᶠ t : ℝ in atTop, E t ≤ K + 1 := by
  have hpoint : ∀ t, 1 ≤ t →
      E t ≤ K + (E 1 - K) * Real.exp (-p * (t - 1)) := by
    intro t ht
    have hcont : ContinuousOn E (Set.Icc (1 : ℝ) t) := by
      intro s hs
      exact (hderiv s (lt_of_lt_of_le zero_lt_one hs.1)).continuousAt.continuousWithinAt
    have hbound : ∀ s ∈ Set.Ico (1 : ℝ) t,
        deriv E s ≤ -p * E s + p * K := by
      intro s hs
      have hd := hdamp s (lt_of_lt_of_le zero_lt_one hs.1)
      have hd' := mul_le_mul_of_nonneg_left hd hp.le
      field_simp [hp.ne'] at hd'
      nlinarith
    have hgr := le_gronwallBound_of_liminf_deriv_right_le
      (f := E) (f' := fun s => deriv E s)
      (δ := E 1) (K := -p) (ε := p * K) (a := 1) (b := t)
      hcont
      (fun s hs r hr => by
        have hsder : HasDerivWithinAt E (deriv E s) (Set.Ici s) s :=
          (hderiv s (lt_of_lt_of_le zero_lt_one hs.1)).hasDerivWithinAt
        exact hsder.liminf_right_slope_le hr)
      (le_refl (E 1)) hbound t ⟨ht, le_rfl⟩
    rw [gronwallBound_of_K_ne_0 (neg_ne_zero.mpr hp.ne')] at hgr
    calc
      E t ≤ E 1 * Real.exp (-p * (t - 1)) +
          (p * K) / (-p) * (Real.exp (-p * (t - 1)) - 1) := hgr
      _ = K + (E 1 - K) * Real.exp (-p * (t - 1)) := by
        field_simp [hp.ne']
        ring
  let B : ℝ := |E 1 - K|
  have hlin : Tendsto (fun t : ℝ => -p * (t - 1)) atTop atBot := by
    have hbase : Tendsto (fun t : ℝ => (-p) * t + p) atTop atBot :=
      tendsto_atBot_add_const_right _ p
        (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hp))
    convert hbase using 1
    funext t
    ring
  have hexp : Tendsto (fun t : ℝ => Real.exp (-p * (t - 1)))
      atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hlin
  have hdecay : Tendsto
      (fun t : ℝ => B * Real.exp (-p * (t - 1))) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hexp
  have hevlt : ∀ᶠ t : ℝ in atTop,
      B * Real.exp (-p * (t - 1)) < 1 :=
    (tendsto_order.1 hdecay).2 1 zero_lt_one
  filter_upwards [hevlt, eventually_ge_atTop (1 : ℝ)] with t hsmall ht
  have hmul :
      (E 1 - K) * Real.exp (-p * (t - 1)) ≤
        B * Real.exp (-p * (t - 1)) :=
    mul_le_mul_of_nonneg_right (le_abs_self (E 1 - K))
      (Real.exp_pos _).le
  exact (hpoint t ht).trans (by linarith)

#print axioms eventually_le_add_one_of_linear_damping

end

end ShenWork.Paper3
