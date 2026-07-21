import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Monotone

/-!
# Scalar first-touch comparison

If `α 0 ≤ a 0` and, at every time where the two functions touch (`α t = a t`), the
sub-solution's slope is strictly smaller (`dα t < da t`), then `α t ≤ a t` for all
`t ≥ 0`.  This is the scalar core of the parabolic first-touch argument (Fable R2).
-/

open Filter Topology Set

noncomputable section

namespace ShenWork.Paper1

/-- **Scalar first-touch comparison.** -/
theorem scalar_first_touch {a α da dα : ℝ → ℝ}
    (ha : ∀ t, HasDerivAt a (da t) t)
    (hα : ∀ t, HasDerivAt α (dα t) t)
    (h0 : α 0 ≤ a 0)
    (htouch : ∀ t, 0 ≤ t → α t = a t → dα t < da t) :
    ∀ t, 0 ≤ t → α t ≤ a t := by
  intro t1 ht1
  by_contra hcon
  push_neg at hcon
  have hca : Continuous a := continuous_iff_continuousAt.mpr fun t => (ha t).continuousAt
  have hcα : Continuous α := continuous_iff_continuousAt.mpr fun t => (hα t).continuousAt
  set S : Set ℝ := Icc 0 t1 ∩ {t | α t ≤ a t} with hS
  have hScl : IsClosed S := isClosed_Icc.inter (isClosed_le hcα hca)
  have hSne : S.Nonempty := ⟨0, ⟨left_mem_Icc.mpr ht1, h0⟩⟩
  have hSbdd : BddAbove S := ⟨t1, fun x hx => hx.1.2⟩
  set t0 : ℝ := sSup S with ht0
  have ht0S : t0 ∈ S := hScl.csSup_mem hSne hSbdd
  have ht00 : 0 ≤ t0 := ht0S.1.1
  have ht0t1 : t0 ≤ t1 := ht0S.1.2
  have hαa0 : α t0 ≤ a t0 := ht0S.2
  have ht0lt : t0 < t1 := by
    rcases lt_or_eq_of_le ht0t1 with h | h
    · exact h
    · exfalso; rw [h] at hαa0; linarith
  -- α t₀ = a t₀ (strict `<` would put a right-neighbourhood into `S`, past the sup)
  have htouch0 : α t0 = a t0 := by
    rcases lt_or_eq_of_le hαa0 with hlt | heq
    · exfalso
      have hnhd : ∀ᶠ s in 𝓝 t0, α s < a s :=
        hcα.continuousAt.eventually_lt hca.continuousAt hlt
      obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hnhd
      set s : ℝ := min (t0 + δ / 2) t1 with hs
      have hst0 : t0 < s := lt_min (by linarith) ht0lt
      have hsle : s ≤ t1 := min_le_right _ _
      have hsdist : dist s t0 < δ := by
        rw [Real.dist_eq, abs_of_pos (by linarith)]
        have : s ≤ t0 + δ / 2 := min_le_left _ _
        linarith
      have hsS : s ∈ S := ⟨⟨by linarith, hsle⟩, le_of_lt (hball hsdist)⟩
      exact absurd (le_csSup hSbdd hsS) (by rw [← ht0]; linarith)
    · exact heq
  -- `h = a − α`: `h t₀ = 0`, `h' t₀ = da t₀ − dα t₀ > 0`
  have hpos : 0 < da t0 - dα t0 := by
    have := htouch t0 ht00 htouch0; linarith
  have hh : ∀ t, HasDerivAt (fun t => a t - α t) (da t - dα t) t :=
    fun t => (ha t).sub (hα t)
  -- slope of `h` at `t₀` within `(t₀,∞)` tends to `h' t₀ > 0`
  have hslope : Tendsto (slope (fun t => a t - α t) t0) (𝓝[>] t0)
      (𝓝 (da t0 - dα t0)) := by
    have hd := (hh t0).hasDerivWithinAt (s := Ioi t0)
    rw [hasDerivWithinAt_iff_tendsto_slope] at hd
    rwa [diff_singleton_eq_self (notMem_Ioi.mpr le_rfl)] at hd
  have heventpos : ∀ᶠ s in 𝓝[>] t0,
      0 < slope (fun t => a t - α t) t0 s :=
    hslope.eventually (eventually_gt_nhds hpos)
  -- there is `s ∈ (t₀, t₁)` with positive slope, hence `α s < a s`, hence `s ∈ S`
  have hmem : Ioo t0 t1 ∈ 𝓝[>] t0 := Ioo_mem_nhdsGT ht0lt
  obtain ⟨s, hspos, hsIoo⟩ := (heventpos.and (eventually_mem_set.mpr hmem)).exists
  have hden : 0 < s - t0 := by linarith [hsIoo.1]
  have hh0 : a t0 - α t0 = 0 := by linarith [htouch0]
  rw [slope_def_field] at hspos
  have hsval : 0 < a s - α s := by
    rcases (div_pos_iff.1 hspos) with ⟨hn, _⟩ | ⟨_, hd⟩
    · linarith [hn, hh0]
    · exact absurd hden (not_lt.mpr hd.le)
  have hsS : s ∈ S := ⟨⟨by linarith [ht00, hsIoo.1], le_of_lt hsIoo.2⟩,
    by simp only [Set.mem_setOf_eq]; linarith [hsval]⟩
  exact absurd (le_csSup hSbdd hsS) (by rw [← ht0]; linarith [hsIoo.1])

section AxiomAudit

#print axioms scalar_first_touch

end AxiomAudit

end ShenWork.Paper1
