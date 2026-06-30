import ShenWork.PDE.P3MoserIntegratedClosure

open MeasureTheory Filter Set Metric
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserHighExcursionProducer

/-- A continuous function exceeding a threshold at an interior point of `(0, T)`
exceeds the midpoint `(C + Y t) / 2` on a nontrivial subinterval. -/
theorem exists_Icc_subinterval_gt_mid_of_continuousOn_gt
    {Y : ℝ → ℝ} {T C t : ℝ}
    (hcont : ContinuousOn Y (Icc 0 T))
    (ht_pos : 0 < t) (ht_lt : t < T)
    (hexcursion : C < Y t) :
    ∃ a b : ℝ, ∃ mid : ℝ, C < mid ∧
      0 < a ∧ a ≤ t ∧ t ≤ b ∧ b < T ∧ a < b ∧
      ∀ s ∈ Icc a b, mid < Y s := by
  set mid := (C + Y t) / 2
  have hCmid : C < mid := by simp only [mid]; linarith
  have hmidY : mid < Y t := by simp only [mid]; linarith
  have hca : ContinuousAt Y t :=
    hcont.continuousAt (Icc_mem_nhds ht_pos ht_lt)
  have hpre : Y ⁻¹' Ioi mid ∈ nhds t :=
    hca.preimage_mem_nhds (Ioi_mem_nhds hmidY)
  rcases Metric.mem_nhds_iff.mp hpre with ⟨δ, hδ, hball⟩
  set δ' := min (δ / 2) (min (t / 2) ((T - t) / 2))
  have ht_sub : 0 < T - t := by linarith
  have hδ'_pos : 0 < δ' := by
    simp only [δ']; simp only [lt_min_iff]; exact ⟨by linarith, by linarith, by linarith⟩
  have hδ'_lt_t : δ' < t := by
    calc δ' ≤ t / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
      _ < t := by linarith
  have hδ'_lt_Tt : δ' < T - t := by
    calc δ' ≤ (T - t) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
      _ < T - t := by linarith
  have hδ'_le_δ2 : δ' ≤ δ / 2 := min_le_left _ _
  refine ⟨t - δ', t + δ', mid, hCmid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · intro s hs
    apply mem_Ioi.mp
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have : |s - t| ≤ δ' := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    linarith

/-- Time integral of a function bounded below by `L` on `[a, b]` is at least `(b-a) * L`. -/
theorem intervalIntegral_ge_of_ge_on_Icc
    {Y : ℝ → ℝ} {a b L : ℝ}
    (hab : a ≤ b)
    (hint : IntervalIntegrable Y volume a b)
    (hge : ∀ s ∈ Icc a b, L ≤ Y s) :
    (b - a) * L ≤ ∫ s in a..b, Y s := by
  have hconst : ∫ _s in a..b, L = (b - a) * L := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  rw [← hconst]
  exact intervalIntegral.integral_mono_on hab
    intervalIntegrable_const hint
    (fun s hs => hge s (Set.uIcc_of_le hab ▸ hs))

/-- Produce a lower-average window from energy continuity, pointwise excursion,
and current-exponent Lp bounds. -/
def lowerAverageWindow_of_continuousOn_excursion
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p Cnext t : ℝ}
    (hcont_higher :
      ContinuousOn (integratedMoserEnergy D u (p + rho)) (Icc 0 T))
    (hLp : LpPowerBoundedBefore D p T u)
    (_hp0_le : p0 ≤ p)
    (_hp_nonneg : 0 ≤ p)
    (ht_pos : 0 < t) (ht_lt : t < T)
    (hexcursion : Cnext < integratedMoserEnergy D u (p + rho) t)
    (hint :
      ∀ a b, 0 < a → b < T → a ≤ b →
        IntervalIntegrable (integratedMoserEnergy D u (p + rho)) volume a b) :
    IntegratedMoserHighExcursionLowerAverageWindow
      D u T rho p0 p Cnext t := by
  have hexist := exists_Icc_subinterval_gt_mid_of_continuousOn_gt
    hcont_higher ht_pos ht_lt hexcursion
  let a := Classical.choose hexist
  let b := Classical.choose (Classical.choose_spec hexist)
  let mid := Classical.choose (Classical.choose_spec (Classical.choose_spec hexist))
  have hprops := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hexist))
  have hCnext_mid := hprops.1
  have ha_pos := hprops.2.1
  have ha_le := hprops.2.2.1
  have ht_le := hprops.2.2.2.1
  have hb_lt := hprops.2.2.2.2.1
  have hab := hprops.2.2.2.2.2.1
  have hgt := hprops.2.2.2.2.2.2
  have hexistM := currentEnergy_Icc_bound_of_LpPowerBoundedBefore hLp ha_pos hb_lt
  let M := Classical.choose hexistM
  have hM := Classical.choose_spec hexistM
  have hab_le : a ≤ b := le_of_lt hab
  have hint_ab := hint a b ha_pos hb_lt hab_le
  have hlower :=
    intervalIntegral_ge_of_ge_on_Icc hab_le hint_ab
      (fun s hs => le_of_lt (hgt s hs))
  exact
    { a := a
      b := b
      M := M
      lowerBound := (b - a) * mid
      hab := hab
      ha_pos := ha_pos
      hb_lt := hb_lt
      haT := ⟨by linarith, by linarith⟩
      hbT := ⟨hab_le, by linarith⟩
      currentEnergy_le_Icc := hM
      lowerAverage := hlower }

/-- Last-exit time: if `Z` is continuous on `[0, T]`, `Z 0 < K`, and
`2*K < Z t` for some `0 < t < T`, there exists `a ∈ (0, t)` with `Z a = K`
and `K ≤ Z s` for all `s ∈ [a, t]`. -/
theorem exists_lastExit_of_continuousOn
    {Z : ℝ → ℝ} {T K t : ℝ}
    (hcont : ContinuousOn Z (Icc 0 T))
    (hZ0 : Z 0 < K) (_hK_pos : 0 < K)
    (ht_pos : 0 < t) (ht_lt : t < T)
    (hhigh : 2 * K < Z t) :
    ∃ a : ℝ, 0 < a ∧ a < t ∧
      Z a = K ∧
      ∀ s ∈ Icc a t, K ≤ Z s := by
  classical
  let S : Set ℝ := Icc (0 : ℝ) t ∩ {s : ℝ | Z s ≤ K}
  have hcont_t : ContinuousOn Z (Icc (0 : ℝ) t) :=
    hcont.mono (Icc_subset_Icc_right ht_lt.le)
  have hS_nonempty : S.Nonempty := ⟨0, by simp [S, ht_pos.le, hZ0.le]⟩
  have hS_subset : S ⊆ Icc (0 : ℝ) t := Set.inter_subset_left
  have hS_closed : IsClosed S :=
    hcont_t.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hS_compact : IsCompact S :=
    isCompact_Icc.of_isClosed_subset hS_closed hS_subset
  have hS_bddAbove : BddAbove S := ⟨t, fun x hx => hx.1.2⟩
  let a : ℝ := sSup S
  have haS : a ∈ S := hS_compact.sSup_mem hS_nonempty
  have ha0 : 0 ≤ a := haS.1.1
  have hat : a ≤ t := haS.1.2
  have hZa_le : Z a ≤ K := haS.2
  have hK_lt_Zt : K < Z t := by nlinarith
  have hZa_eq : Z a = K := by
    by_contra hZa_ne
    have hZa_lt : Z a < K := lt_of_le_of_ne hZa_le hZa_ne
    have hcont_at : ContinuousOn Z (Icc a t) :=
      hcont.mono (fun x hx => ⟨le_trans ha0 hx.1, le_trans hx.2 ht_lt.le⟩)
    obtain ⟨c, hcIcc, hc_eq⟩ :=
      intermediate_value_Icc hat hcont_at ⟨hZa_le, hK_lt_Zt.le⟩
    have ha_lt_c : a < c := by
      rcases eq_or_lt_of_le hcIcc.1 with h | h
      · exfalso; exact hZa_ne (h ▸ hc_eq)
      · exact h
    have hcS : c ∈ S :=
      ⟨⟨le_trans ha0 hcIcc.1, hcIcc.2⟩, le_of_eq hc_eq⟩
    exact not_lt_of_ge (le_csSup hS_bddAbove hcS) ha_lt_c
  have ha_pos : 0 < a := by
    rcases eq_or_lt_of_le ha0 with h | h
    · exfalso; exact ne_of_lt hZ0 (h ▸ hZa_eq)
    · exact h
  have ha_lt_t : a < t := by
    rcases eq_or_lt_of_le hat with h | h
    · exfalso; exact ne_of_lt hK_lt_Zt (h ▸ hZa_eq.symm)
    · exact h
  refine ⟨a, ha_pos, ha_lt_t, hZa_eq, ?_⟩
  intro s hs
  by_contra hnot
  have hZs_lt : Z s < K := lt_of_not_ge hnot
  have hsS : s ∈ S := ⟨⟨le_trans ha0 hs.1, hs.2⟩, hZs_lt.le⟩
  have hs_le_a : s ≤ a := le_csSup hS_bddAbove hsS
  have hs_eq_a : s = a := le_antisymm hs_le_a hs.1
  exact ne_of_lt hZs_lt (hs_eq_a ▸ hZa_eq)

/-- Threshold plan for the integrated Moser crossing step.  All constants
are chosen in the correct quantifier order:
M, Cp, Cq → eps → Ceps → R → K → Cnext = 2K.

The `K_gap` field encodes the strict inequality that makes the upper bound
`R` strictly less than the lower bound `K/(Cq*(p+rho))`. -/
structure IntegratedMoserCrossingThresholdPlan
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 p : ℝ) where
  M : ℝ
  Cp : ℝ
  Cq : ℝ
  eps : ℝ
  Ceps : ℝ
  Tbar : ℝ
  Gbar : ℝ
  R : ℝ
  K : ℝ
  M_one_le : 1 ≤ M
  M_bound : ∀ s, 0 < s → s < T → integratedMoserEnergy D u p s ≤ M
  Cq_pos : 0 < Cq
  eps_pos : 0 < eps
  Ceps_nonneg : 0 ≤ Ceps
  T_le_Tbar : T ≤ Tbar
  one_le_Tbar : 1 ≤ Tbar
  Gbar_def : Gbar = (M + Cp * p * (Tbar * M)) / 2
  R_def : R = eps * Gbar + Tbar * (Ceps * M)
  init_lt_K : integratedMoserEnergy D u (p + rho) 0 < K
  K_one_le : 1 ≤ K
  K_gap : (Cq * (p + rho)) * (R + 1) < K
  gradient_bound :
    ∀ a b, 0 < a → a ≤ b → b < T →
      ∫ s in a..b, integratedMoserGradientEnergy D u p s ≤ Gbar
  rel_interp :
    ∀ s, 0 < s → s < T →
      integratedMoserEnergy D u (p + rho) s ≤
        eps * integratedMoserGradientEnergy D u p s +
        Ceps * integratedMoserEnergy D u p s
  drop_q :
    ∀ t1 ∈ Icc (0 : ℝ) T, ∀ t2 ∈ Icc t1 T,
      integratedMoserEnergy D u (p + rho) t2 -
        integratedMoserEnergy D u (p + rho) t1 +
        2 * ∫ s in t1..t2,
          integratedMoserGradientEnergy D u (p + rho) s ≤
      Cq * (p + rho) * ∫ s in t1..t2,
        max 1 (integratedMoserEnergy D u (p + rho) s)

/-- Integrate a pointwise upper bound `Z(s) ≤ eps*G(s) + C` to get
`∫Z ≤ eps*∫G + (b-a)*C`. -/
theorem intervalIntegral_le_of_pointwise_le_split
    {Z G : ℝ → ℝ} {a b eps C : ℝ}
    (hab : a ≤ b)
    (hint_Z : IntervalIntegrable Z volume a b)
    (hint_G : IntervalIntegrable G volume a b)
    (hpoint : ∀ s ∈ Icc a b, Z s ≤ eps * G s + C) :
    ∫ s in a..b, Z s ≤ eps * (∫ s in a..b, G s) + (b - a) * C := by
  have hint_sum : IntervalIntegrable (fun s => eps * G s + C) volume a b :=
    (hint_G.const_mul eps).add intervalIntegrable_const
  have hmono : ∫ s in a..b, Z s ≤ ∫ s in a..b, (eps * G s + C) :=
    intervalIntegral.integral_mono_on hab hint_Z hint_sum
      (fun s hs => hpoint s (Set.uIcc_of_le hab ▸ hs))
  have hsplit : (∫ s in a..b, (eps * G s + C)) =
      (∫ s in a..b, eps * G s) + (∫ _s in a..b, C) :=
    intervalIntegral.integral_add (hint_G.const_mul eps) intervalIntegrable_const
  have hmul : (∫ s in a..b, eps * G s) = eps * (∫ s in a..b, G s) :=
    intervalIntegral.integral_const_mul eps G
  have hconst : (∫ _s in a..b, C) = (b - a) * C := by
    rw [intervalIntegral.integral_const]; simp [smul_eq_mul]
  linarith

/-- The threshold plan produces the next-exponent Lp bound via contradiction:
any pointwise excursion above `2K` leads to a last-exit window whose
lower-average exceeds the interpolation upper bound. -/
theorem LpPowerBoundedBefore_of_crossingThresholdPlan
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p : ℝ}
    (hplan : IntegratedMoserCrossingThresholdPlan D u T rho p0 p)
    (hcont : ContinuousOn (integratedMoserEnergy D u (p + rho)) (Icc 0 T))
    (hgrad_nonneg :
      ∀ a b, 0 < a → a ≤ b → b < T →
        0 ≤ ∫ s in a..b, integratedMoserGradientEnergy D u (p + rho) s)
    (hint_higher :
      ∀ a b, 0 < a → b < T → a ≤ b →
        IntervalIntegrable (integratedMoserEnergy D u (p + rho)) volume a b)
    (hint_grad :
      ∀ a b, 0 < a → b < T → a ≤ b →
        IntervalIntegrable (integratedMoserGradientEnergy D u p) volume a b)
    (hp_nonneg : 0 ≤ p) (hrho_pos : 0 < rho) :
    LpPowerBoundedBefore D (p + rho) T u := by
  refine ⟨2 * hplan.K, ?_⟩
  intro t ht_pos ht_lt
  by_contra hnot
  push_neg at hnot
  have hhigh : 2 * hplan.K < integratedMoserEnergy D u (p + rho) t := hnot
  have hK_pos : 0 < hplan.K := lt_of_lt_of_le zero_lt_one hplan.K_one_le
  rcases exists_lastExit_of_continuousOn hcont hplan.init_lt_K hK_pos
    ht_pos ht_lt hhigh with ⟨a, ha_pos, ha_lt, hZa_eq, hK_le⟩
  have hab : a ≤ t := le_of_lt ha_lt
  have ha_mem : a ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith⟩
  have ht_mem : t ∈ Icc a T := ⟨hab, by linarith⟩
  have hdrop := hplan.drop_q a ha_mem t ht_mem
  have hZt_ge : hplan.K < integratedMoserEnergy D u (p + rho) t := by linarith
  have hgrad_nn := hgrad_nonneg a t ha_pos hab ht_lt
  have hq_pos : 0 < p + rho := by linarith
  have hCq_q_pos : 0 < hplan.Cq * (p + rho) := mul_pos hplan.Cq_pos hq_pos
  have hmax_eq : ∀ s ∈ Icc a t,
      max 1 (integratedMoserEnergy D u (p + rho) s) =
        integratedMoserEnergy D u (p + rho) s := by
    intro s hs
    have hK_le_s := hK_le s hs
    have h1_le : (1 : ℝ) ≤ integratedMoserEnergy D u (p + rho) s :=
      le_trans hplan.K_one_le hK_le_s
    exact max_eq_right h1_le
  have hZdiff : hplan.K ≤
      hplan.Cq * (p + rho) * ∫ s in a..t,
        integratedMoserEnergy D u (p + rho) s := by
    have h2 : ∫ s in a..t,
        max 1 (integratedMoserEnergy D u (p + rho) s) =
      ∫ s in a..t, integratedMoserEnergy D u (p + rho) s := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact hmax_eq s (Set.uIcc_of_le hab ▸ hs)
    have hZdrop : integratedMoserEnergy D u (p + rho) t -
        integratedMoserEnergy D u (p + rho) a ≤
      hplan.Cq * (p + rho) * ∫ s in a..t,
        integratedMoserEnergy D u (p + rho) s := by
      nlinarith [hdrop, hgrad_nn, h2]
    nlinarith [hZa_eq, hZt_ge]
  have hlower : hplan.K / (hplan.Cq * (p + rho)) ≤
      ∫ s in a..t, integratedMoserEnergy D u (p + rho) s :=
    (div_le_iff₀ hCq_q_pos).mpr (by linarith [hZdiff])
  have hupper : ∫ s in a..t, integratedMoserEnergy D u (p + rho) s ≤
      hplan.R := by
    have hrel_int : ∫ s in a..t, integratedMoserEnergy D u (p + rho) s ≤
        hplan.eps * (∫ s in a..t, integratedMoserGradientEnergy D u p s) +
        (t - a) * (hplan.Ceps * hplan.M) := by
      have hY_le : ∀ s ∈ Icc a t,
          hplan.Ceps * integratedMoserEnergy D u p s ≤ hplan.Ceps * hplan.M := by
        intro s hs
        exact mul_le_mul_of_nonneg_left
          (hplan.M_bound s (by linarith [hs.1]) (by linarith [hs.2])) hplan.Ceps_nonneg
      have hpoint : ∀ s ∈ Icc a t,
          integratedMoserEnergy D u (p + rho) s ≤
            hplan.eps * integratedMoserGradientEnergy D u p s +
            hplan.Ceps * hplan.M := by
        intro s hs
        calc integratedMoserEnergy D u (p + rho) s
            ≤ hplan.eps * integratedMoserGradientEnergy D u p s +
              hplan.Ceps * integratedMoserEnergy D u p s :=
              hplan.rel_interp s (by linarith [hs.1]) (by linarith [hs.2])
          _ ≤ hplan.eps * integratedMoserGradientEnergy D u p s +
              hplan.Ceps * hplan.M := by linarith [hY_le s hs]
      have hint_Z := hint_higher a t ha_pos ht_lt hab
      have hint_G := hint_grad a t ha_pos ht_lt hab
      have hint_sum : IntervalIntegrable
          (fun s => hplan.eps * integratedMoserGradientEnergy D u p s +
            hplan.Ceps * hplan.M) volume a t :=
        (hint_G.const_mul hplan.eps).add intervalIntegrable_const
      exact intervalIntegral_le_of_pointwise_le_split hab hint_Z hint_G hpoint
    have hG_le := hplan.gradient_bound a t ha_pos hab ht_lt
    have hta_le : t - a ≤ hplan.Tbar := by linarith [hplan.T_le_Tbar]
    have h1 : hplan.eps * (∫ s in a..t, integratedMoserGradientEnergy D u p s) ≤
        hplan.eps * hplan.Gbar :=
      mul_le_mul_of_nonneg_left hG_le hplan.eps_pos.le
    have h2 : (t - a) * (hplan.Ceps * hplan.M) ≤
        hplan.Tbar * (hplan.Ceps * hplan.M) :=
      mul_le_mul_of_nonneg_right hta_le
        (mul_nonneg hplan.Ceps_nonneg (le_trans zero_le_one hplan.M_one_le))
    have h3 : hplan.eps * (∫ s in a..t, integratedMoserGradientEnergy D u p s) +
        (t - a) * (hplan.Ceps * hplan.M) ≤
        hplan.eps * hplan.Gbar + hplan.Tbar * (hplan.Ceps * hplan.M) :=
      add_le_add h1 h2
    exact le_trans hrel_int (le_trans h3 (le_of_eq hplan.R_def.symm))
  have hR_lt : hplan.R + 1 < hplan.K / (hplan.Cq * (p + rho)) := by
    rw [lt_div_iff₀ hCq_q_pos]
    nlinarith [hplan.K_gap, mul_comm (hplan.Cq * (p + rho)) (hplan.R + 1)]
  linarith

#print axioms exists_Icc_subinterval_gt_mid_of_continuousOn_gt
#print axioms intervalIntegral_ge_of_ge_on_Icc
#print axioms lowerAverageWindow_of_continuousOn_excursion
#print axioms exists_lastExit_of_continuousOn
#print axioms LpPowerBoundedBefore_of_crossingThresholdPlan

end ShenWork.IntervalDomainExistence.P3MoserHighExcursionProducer

end
