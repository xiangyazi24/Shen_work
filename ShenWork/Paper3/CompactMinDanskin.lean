import Mathlib

open Filter Topology

namespace ShenWork.Paper3

noncomputable section

def compactMinLowerRightDini (z : ℝ → ℝ) (t : ℝ) : ℝ :=
  Filter.liminf (fun h : ℝ => (z (t + h) - z t) / h) (𝓝[>] (0 : ℝ))

theorem compactMin_liminf_ge_of_eventually_ge_sub
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

structure CompactMinFamily
    (K : Set ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ → ℝ) : Prop where
  z_le : ∀ s x, x ∈ K → z s ≤ f s x
  exists_min : ∀ s, ∃ x, x ∈ K ∧ f s x = z s

def UniformRightDerivLowerOnCompact
    (K : Set ℝ) (f ft : ℝ → ℝ → ℝ) (t : ℝ) : Prop :=
  ∀ eps > 0, ∃ eta > 0, ∀ h, 0 < h → h < eta →
    ∀ x, x ∈ K → ft t x - eps ≤ (f (t + h) x - f t x) / h

def UniformTimeContinuityOnCompact
    (K : Set ℝ) (f : ℝ → ℝ → ℝ) (t : ℝ) : Prop :=
  ∀ eps > 0, ∃ eta > 0, ∀ h, 0 < h → h < eta →
    ∀ x, x ∈ K → |f (t + h) x - f t x| ≤ eps

theorem lowerRightDini_min_ge_of_near_argmin_ft_lower
    {K : Set ℝ} {f ft : ℝ → ℝ → ℝ} {z : ℝ → ℝ} {t G : ℝ}
    (H : CompactMinFamily K f z)
    (hderiv : UniformRightDerivLowerOnCompact K f ft t)
    (htime : UniformTimeContinuityOnCompact K f t)
    (hnear : ∀ eps > 0, ∃ rho > 0, ∀ x, x ∈ K →
      f t x ≤ z t + rho → G - eps ≤ ft t x)
    (hcobdd :
      IsCoboundedUnder GE.ge (𝓝[>] (0 : ℝ))
        (fun h : ℝ => (z (t + h) - z t) / h))
    (hbdd :
      IsBoundedUnder GE.ge (𝓝[>] (0 : ℝ))
        (fun h : ℝ => (z (t + h) - z t) / h)) :
    G ≤ compactMinLowerRightDini z t := by
  refine compactMin_liminf_ge_of_eventually_ge_sub hcobdd hbdd ?_
  intro eps heps
  let e := eps / 3
  have he : 0 < e := by dsimp [e]; linarith
  rcases hnear e he with ⟨rho, hrho, hnear'⟩
  rcases htime (rho / 4) (by positivity) with ⟨etaT, hetaT, hT⟩
  rcases hderiv e he with ⟨etaD, hetaD, hD⟩
  let eta := min etaT etaD
  have heta : 0 < eta := lt_min hetaT hetaD
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Set.Ioo (0 : ℝ) eta :=
    Ioo_mem_nhdsGT heta
  filter_upwards [hev] with h hh
  have hh0 : 0 < h := hh.1
  have hhT : h < etaT := lt_of_lt_of_le hh.2 (min_le_left _ _)
  have hhD : h < etaD := lt_of_lt_of_le hh.2 (min_le_right _ _)
  rcases H.exists_min (t + h) with ⟨xh, hxhK, hxh⟩
  rcases H.exists_min t with ⟨x0, hx0K, hx0⟩
  have htxh_abs := hT h hh0 hhT xh hxhK
  have htx0_abs := hT h hh0 hhT x0 hx0K
  have htxh_le : f t xh ≤ f (t + h) xh + rho / 4 := by
    have := (abs_le.mp htxh_abs).1
    linarith
  have htx0_le : f (t + h) x0 ≤ f t x0 + rho / 4 := by
    have := (abs_le.mp htx0_abs).2
    linarith
  have hnear_xh : f t xh ≤ z t + rho := by
    have hz0 : z (t + h) ≤ f (t + h) x0 := H.z_le (t + h) x0 hx0K
    linarith
  have hft : G - e ≤ ft t xh := hnear' xh hxhK hnear_xh
  have hquot1 : ft t xh - e ≤ (f (t + h) xh - f t xh) / h :=
    hD h hh0 hhD xh hxhK
  have hnum : f (t + h) xh - f t xh ≤ z (t + h) - z t := by
    have hz : z t ≤ f t xh := H.z_le t xh hxhK
    linarith
  have hquot2 :
      (f (t + h) xh - f t xh) / h ≤ (z (t + h) - z t) / h :=
    div_le_div_of_nonneg_right hnum (le_of_lt hh0)
  have h2e : 2 * e ≤ eps := by dsimp [e]; linarith
  linarith

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.lowerRightDini_min_ge_of_near_argmin_ft_lower
