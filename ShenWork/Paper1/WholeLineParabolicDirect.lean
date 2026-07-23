import ShenWork.Paper1.WholeLineScalarFirstTouch

open Filter Topology Set

noncomputable section

namespace ShenWork.Paper1

/--
Direct parabolic lower barrier using a continuous attained lower envelope.

The extra `hstart` hypothesis is essential on a noncompact spatial domain:
pointwise time differentiability does not prevent minimizers from escaping to
spatial infinity immediately after `t = 0`.
-/
theorem parabolic_lower_barrier_direct_of_initial_interval
    {u : ℝ → ℝ → ℝ} {a α dα : ℝ → ℝ} {ut : ℝ → ℝ → ℝ}
    (hα : ∀ t, HasDerivAt α (dα t) t)
    (hut : ∀ t z, 0 < t → HasDerivAt (fun s => u s z) (ut t z) t)
    (ha_cont : Continuous a)
    (ha_lb : ∀ t z, a t ≤ u t z)
    (ha_attain : ∀ t, ∃ z0, a t = u t z0)
    (hstart : ∃ ε, 0 < ε ∧
      ∀ t, 0 ≤ t → t ≤ ε → α t ≤ a t)
    (hrate : ∀ t z0, 0 ≤ t →
      (∀ z, u t z0 ≤ u t z) →
      u t z0 = α t → dα t < ut t z0) :
    ∀ t z, 0 ≤ t → α t ≤ u t z := by
  have hαcont : Continuous α :=
    continuous_iff_continuousAt.mpr fun t => (hα t).continuousAt
  intro t1 z ht1
  have hαa : α t1 ≤ a t1 := by
    by_contra hnot
    have hbad1 : a t1 < α t1 := lt_of_not_ge hnot
    obtain ⟨ε, hεpos, hε⟩ := hstart
    have hεt1 : ε < t1 := by
      by_contra h
      have ht1ε : t1 ≤ ε := le_of_not_gt h
      exact (not_lt_of_ge (hε t1 ht1 ht1ε)) hbad1

    -- The genuine bad-time set.  Its infimum is a first failure because
    -- `hstart` supplies a positive initial good interval.
    set B : Set ℝ := Icc 0 t1 ∩ {t | a t < α t} with hB
    have ht1B : t1 ∈ B := ⟨⟨ht1, le_rfl⟩, hbad1⟩
    have hBne : B.Nonempty := ⟨t1, ht1B⟩
    have hBbdd : BddBelow B := ⟨0, fun x hx => hx.1.1⟩
    set t0 : ℝ := sInf B with ht0

    have ht0_nonneg : 0 ≤ t0 := by
      rw [ht0]
      exact le_csInf hBne (fun x hx => hx.1.1)
    have ht0_le_t1 : t0 ≤ t1 := by
      have h := csInf_le hBbdd ht1B
      rwa [← ht0] at h

    have hε_lower : ∀ x ∈ B, ε ≤ x := by
      intro x hx
      by_contra hxe
      have hxε : x ≤ ε := (lt_of_not_ge hxe).le
      exact (not_lt_of_ge (hε x hx.1.1 hxε)) hx.2
    have hεt0 : ε ≤ t0 := by
      rw [ht0]
      exact le_csInf hBne hε_lower
    have ht0pos : 0 < t0 := lt_of_lt_of_le hεpos hεt0

    -- `t0` is not itself strictly bad.  Otherwise continuity gives a bad
    -- point strictly to its left, contradicting the defining lower bound.
    have hnot_bad0 : ¬ a t0 < α t0 := by
      intro hbad0
      have hnhd : ∀ᶠ s in 𝓝 t0, a s < α s :=
        ha_cont.continuousAt.eventually_lt hαcont.continuousAt hbad0
      obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hnhd
      set δ0 : ℝ := min δ t0 with hδ0
      have hδ0pos : 0 < δ0 := by
        simp only [hδ0]
        exact lt_min hδ ht0pos
      have hδ0_le_δ : δ0 ≤ δ := by
        simp only [hδ0]
        exact min_le_left _ _
      have hδ0_le_t0 : δ0 ≤ t0 := by
        simp only [hδ0]
        exact min_le_right _ _
      set s : ℝ := t0 - δ0 / 2 with hs
      have hs0 : 0 ≤ s := by
        simp only [hs]
        linarith
      have hslt : s < t0 := by
        simp only [hs]
        linarith
      have hsdist : dist s t0 < δ := by
        rw [Real.dist_eq]
        have hsub : s - t0 = -(δ0 / 2) := by
          simp only [hs]
          ring
        rw [hsub, abs_neg, abs_of_pos (by positivity)]
        linarith
      have hsB : s ∈ B :=
        ⟨⟨hs0, le_trans hslt.le ht0_le_t1⟩, hball hsdist⟩
      have hinf := csInf_le hBbdd hsB
      rw [← ht0] at hinf
      linarith
    have hα_le_a0 : α t0 ≤ a t0 := le_of_not_gt hnot_bad0

    -- Conversely, strict goodness at `t0` would persist in a neighborhood,
    -- but the defining property of `sInf B` supplies bad points arbitrarily
    -- close from the right.
    have ha_le_α0 : a t0 ≤ α t0 := by
      by_contra hnot
      have hstrict : α t0 < a t0 := lt_of_not_ge hnot
      have hnhd : ∀ᶠ s in 𝓝 t0, α s < a s :=
        hαcont.continuousAt.eventually_lt ha_cont.continuousAt hstrict
      obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hnhd
      have hex : ∃ b ∈ B, b < t0 + δ := by
        by_contra hno
        push_neg at hno
        have hnewLower : t0 + δ ≤ sInf B :=
          le_csInf hBne (fun b hb => hno b hb)
        rw [← ht0] at hnewLower
        linarith
      obtain ⟨b, hbB, hblt⟩ := hex
      have ht0leb : t0 ≤ b := by
        have h := csInf_le hBbdd hbB
        rwa [← ht0] at h
      have hbdist : dist b t0 < δ := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht0leb)]
        linarith
      have hgoodb : α b < a b := hball hbdist
      exact (not_lt_of_ge hgoodb.le) hbB.2

    have hat_touch : α t0 = a t0 := le_antisymm hα_le_a0 ha_le_α0

    -- Freeze an argmin at the first touch.
    obtain ⟨z0, hz0⟩ := ha_attain t0
    have hzmin : ∀ z, u t0 z0 ≤ u t0 z := by
      intro z
      calc
        u t0 z0 = a t0 := hz0.symm
        _ ≤ u t0 z := ha_lb t0 z
    have htouch : u t0 z0 = α t0 := by
      calc
        u t0 z0 = a t0 := hz0.symm
        _ = α t0 := hat_touch.symm
    have hgap : dα t0 < ut t0 z0 :=
      hrate t0 z0 ht0_nonneg hzmin htouch

    -- For ψ(t) = u(t,z0) - α(t), ψ(t0)=0 and ψ'(t0)>0.
    -- Hence ψ is negative immediately to the LEFT of t0.
    have hψderiv : HasDerivAt
        (fun s => u s z0 - α s) (ut t0 z0 - dα t0) t0 :=
      (hut t0 z0 ht0pos).sub (hα t0)
    have hpos : 0 < ut t0 z0 - dα t0 := by linarith
    have hslope : Tendsto
        (slope (fun s => u s z0 - α s) t0)
        (𝓝[<] t0) (𝓝 (ut t0 z0 - dα t0)) := by
      have hd := hψderiv.hasDerivWithinAt (s := Iio t0)
      rw [hasDerivWithinAt_iff_tendsto_slope] at hd
      rwa [diff_singleton_eq_self (notMem_Iio.mpr le_rfl)] at hd
    have heventpos : ∀ᶠ s in 𝓝[<] t0,
        0 < slope (fun r => u r z0 - α r) t0 s :=
      hslope.eventually (eventually_gt_nhds hpos)
    have hmem : Ioo 0 t0 ∈ 𝓝[<] t0 := Ioo_mem_nhdsLT ht0pos
    obtain ⟨s, hspos, hsIoo⟩ :=
      (heventpos.and (eventually_mem_set.mpr hmem)).exists
    have hψ0 : u t0 z0 - α t0 = 0 := by
      rw [htouch]
      ring
    rw [slope_def_field] at hspos
    have hψneg : u s z0 - α s < 0 := by
      rcases (div_pos_iff.1 hspos) with ⟨_, hdenpos⟩ | ⟨hnumneg, _⟩
      · exfalso
        linarith [hsIoo.2, hdenpos]
      · linarith [hnumneg, hψ0]

    -- Every nonnegative time strictly before the first bad time is good.
    have hgood_s : α s ≤ a s := by
      by_contra hnot
      have hbad_s : a s < α s := lt_of_not_ge hnot
      have hsB : s ∈ B :=
        ⟨⟨hsIoo.1.le, le_trans hsIoo.2.le ht0_le_t1⟩, hbad_s⟩
      have hinf := csInf_le hBbdd hsB
      rw [← ht0] at hinf
      linarith [hsIoo.2]
    have hψnonneg : 0 ≤ u s z0 - α s := by
      have halb := ha_lb s z0
      linarith
    linarith
  exact hαa.trans (ha_lb t1 z)

#print axioms parabolic_lower_barrier_direct_of_initial_interval

end ShenWork.Paper1

namespace ShenWork.Paper1
section AxiomAudit
#print axioms parabolic_lower_barrier_direct_of_initial_interval
end AxiomAudit
end ShenWork.Paper1
