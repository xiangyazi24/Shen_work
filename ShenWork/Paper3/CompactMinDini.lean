import Mathlib

open Filter Topology

namespace ShenWork.Paper3

noncomputable section

def lowerRightDini (z : ℝ → ℝ) (t : ℝ) : ℝ :=
  Filter.liminf (fun h : ℝ => (z (t + h) - z t) / h) (𝓝[>] (0 : ℝ))

theorem le_liminf_of_eventually_ge_sub
    {ι : Type*} {l : Filter ι} {q : ι → ℝ} {G : ℝ}
    (hcobdd : IsCoboundedUnder GE.ge l q)
    (hbdd : IsBoundedUnder GE.ge l q)
    (h : ∀ eps > 0, ∀ᶠ x in l, G - eps ≤ q x) :
    G ≤ Filter.liminf q l := by
  rw [Filter.le_liminf_iff' hcobdd hbdd]
  intro y hy
  have heps : 0 < G - y := sub_pos.mpr hy
  filter_upwards [h (G - y) heps] with x hx
  linarith

theorem lowerRightDini_ge_of_eventually_slope_ge
    {z : ℝ → ℝ} {t G : ℝ}
    (hcobdd :
      IsCoboundedUnder GE.ge (𝓝[>] (0 : ℝ))
        (fun h : ℝ => (z (t + h) - z t) / h))
    (hbdd :
      IsBoundedUnder GE.ge (𝓝[>] (0 : ℝ))
        (fun h : ℝ => (z (t + h) - z t) / h))
    (h : ∀ eps > 0, ∀ᶠ h in 𝓝[>] (0 : ℝ),
      G - eps ≤ (z (t + h) - z t) / h) :
    G ≤ lowerRightDini z t := by
  exact le_liminf_of_eventually_ge_sub hcobdd hbdd h

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.le_liminf_of_eventually_ge_sub
#print axioms ShenWork.Paper3.lowerRightDini_ge_of_eventually_slope_ge
