import ShenWork.Paper3.IntervalDomainPersistenceDiniFrontier
import Mathlib.Analysis.Calculus.MeanValue

open Filter Topology

namespace ShenWork.Paper3

noncomputable section

/-- A positive constant cannot be crossed downwards when a baseline lower
Dini bound is available everywhere and a strictly positive linear lower bound
is available at contacts with the barrier.  The baseline field is used only
to meet the fencing theorem away from contact points. -/
theorem positive_constant_barrier_of_contact_RightLowerDiniGE
    {z : ℝ → ℝ} {T0 T c k kbase : ℝ}
    (hc : 0 < c) (hk : 0 < k) (hT0 : 0 < T0)
    (hcont : ContinuousOn z (Set.Icc T0 T))
    (hinit : c ≤ z T0)
    (hbase : RightLowerDiniGE z (fun y => kbase * y) (Set.Ioi 0))
    (hcontact : RightLowerDiniGE z (fun y => k * y)
      {t : ℝ | 0 < t ∧ z t = c}) :
    ∀ t ∈ Set.Icc T0 T, c ≤ z t := by
  let f : ℝ → ℝ := fun t => -z t
  let B : ℝ → ℝ := fun _ => -c
  let f' : ℝ → ℝ := fun t =>
    if z t = c then -(k * z t) else -(kbase * z t)
  have hf' : ∀ x ∈ Set.Ico T0 T, ∀ r, f' x < r →
      ∃ᶠ s in nhdsWithin x (Set.Ioi x), slope f x s < r := by
    intro x hx r hr
    have hxpos : x ∈ Set.Ioi (0 : ℝ) := lt_of_lt_of_le hT0 hx.1
    by_cases hxc : z x = c
    · have hd := hcontact x ⟨hxpos, hxc⟩ r (by simpa [f', hxc] using hr)
      exact hd.mono (fun s hs => by
        simpa [f, slope_def_field, div_eq_inv_mul, sub_eq_add_neg,
          add_comm, add_left_comm, add_assoc, mul_comm] using hs)
    · have hd := hbase x hxpos r (by simpa [f', hxc] using hr)
      exact hd.mono (fun s hs => by
        simpa [f, slope_def_field, div_eq_inv_mul, sub_eq_add_neg,
          add_comm, add_left_comm, add_assoc, mul_comm] using hs)
  have hfa : f T0 ≤ B T0 := by
    dsimp [f, B]
    linarith
  have hB : ∀ x, HasDerivAt B 0 x := by
    intro x
    exact hasDerivAt_const x (-c)
  have hstrict : ∀ x ∈ Set.Ico T0 T, f x = B x → f' x < 0 := by
    intro x _hx hfx
    have hxc : z x = c := by
      dsimp [f, B] at hfx
      linarith
    simp only [f', hxc, if_pos]
    exact neg_lt_zero.mpr (mul_pos hk hc)
  have hcmp := image_le_of_liminf_slope_right_lt_deriv_boundary
    (f := f) (f' := f') (B := B) (B' := fun _ => 0)
    hcont.neg hf' hfa hB hstrict
  intro t ht
  have hle := hcmp ht
  dsimp [f, B] at hle
  linarith

end

end ShenWork.Paper3

#print axioms
  ShenWork.Paper3.positive_constant_barrier_of_contact_RightLowerDiniGE
