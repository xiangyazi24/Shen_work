import ShenWork.Paper1.Statements

namespace ShenWork.Paper1

open Filter Topology

noncomputable section

private theorem exists_nonneg_abs_bound_of_continuous_tendsto_zero_both_ends'
    {f : ℝ → ℝ}
    (hcont : Continuous f)
    (htop : Tendsto f atTop (𝓝 0))
    (hbot : Tendsto f atBot (𝓝 0)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x, |f x| ≤ D := by
  have hball : Metric.ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
    Metric.ball_mem_nhds _ one_pos
  have htop_event : ∀ᶠ x in atTop, |f x| < 1 := by
    filter_upwards [htop hball] with x hx
    simpa [Metric.mem_ball, Real.dist_eq] using hx
  have hbot_event : ∀ᶠ x in atBot, |f x| < 1 := by
    filter_upwards [hbot hball] with x hx
    simpa [Metric.mem_ball, Real.dist_eq] using hx
  obtain ⟨R, hR⟩ := eventually_atTop.1 htop_event
  obtain ⟨L, hL⟩ := eventually_atBot.1 hbot_event
  obtain ⟨B, hB⟩ :=
    isCompact_Icc.bddAbove_image hcont.abs.continuousOn
  let D : ℝ := max 1 B
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro x
  by_cases hxL : x ≤ L
  · exact (hL x hxL).le.trans (le_max_left _ _)
  · by_cases hxR : R ≤ x
    · exact (hR x hxR).le.trans (le_max_left _ _)
    · have hxIcc : x ∈ Set.Icc L R :=
        ⟨le_of_not_ge hxL, le_of_not_ge hxR⟩
      exact (hB (Set.mem_image_of_mem _ hxIcc)).trans (le_max_right _ _)

/-- The ordinary global `U'` bound in Lemma 5.1 follows directly from the
two-sided derivative limit and continuity in `TravelingWaveRegularity`. -/
theorem Lemma_5_1_wave_derivative_global_bound_of_regularity
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hreg : TravelingWaveRegularity p c U V) :
    ∃ B > 0, ∀ x, |deriv U x| ≤ B := by
  obtain ⟨D, hD_nonneg, hD⟩ :=
    exists_nonneg_abs_bound_of_continuous_tendsto_zero_both_ends'
      hreg.deriv_U_cont hreg.deriv_U_tendszero.1
        hreg.deriv_U_tendszero.2
  exact ⟨D + 1, by linarith, fun x => (hD x).trans (by linarith)⟩

#print axioms Lemma_5_1_wave_derivative_global_bound_of_regularity

/-- Once the signal has the exponential bound from Lemma 5.1, the traveling
wave ODE and regularity force `U'` to have an `exp (-κ x)` bound.  The second
exponential in the paper's statement can therefore be assigned coefficient
zero. -/
theorem Lemma_5_1_wave_derivative_exponential_bound_of_regularity
    {p : CMParams} {c : ℝ} (hc : 2 < c)
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hV_exp : ∀ x,
      |V x| ≤
        (1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
          Real.exp (-(kappa c) * p.γ * x) ∧
      |deriv V x| ≤
        (1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
          Real.exp (-(kappa c) * p.γ * x)) :
    ∃ B1 B2, ∀ x,
      |deriv U x| ≤
        B1 * Real.exp (-(kappa c) * x) +
          B2 * Real.exp (-(kappa c) * p.γ * x) := by
  have hk_pos : 0 < kappa c := kappa_pos_of_two_lt hc
  have hk_lt_one : kappa c < 1 := kappa_lt_one_of_two_lt hc
  have hck_pos : 0 < c - kappa c := by linarith
  let a0 : ℝ := (c - kappa c) / 2
  have ha0_pos : 0 < a0 := by
    dsimp [a0]
    linarith
  have hMChi_pos : 0 < MChi p :=
    lt_of_lt_of_le (hbound.pos 0) (hbound.le_MChi 0)
  have hMChi_ge_one : 1 ≤ MChi p :=
    MChi_ge_one_of_travelingWave hTW hbound
  have hU_nn : ∀ x, 0 ≤ U x := fun x => (hbound.pos x).le
  have hU_le : ∀ x, U x ≤ MChi p := fun x => hbound.le_MChi x
  let K : ℝ := 1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)
  have hK_nonneg : 0 ≤ K := by
    have h := (hV_exp 0).2
    simp only [mul_zero, Real.exp_zero, mul_one] at h
    exact le_trans (abs_nonneg (deriv V 0)) h
  let A : ℝ := |p.χ| * p.m * (MChi p) ^ (p.m - 1)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg (abs_nonneg _) (le_trans zero_le_one p.hm))
      (Real.rpow_nonneg hMChi_pos.le _)
  let P : ℝ := A * K
  have hP_nonneg : 0 ≤ P := mul_nonneg hA_nonneg hK_nonneg
  have hcoef : ∀ x,
      |p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x| ≤
        P * Real.exp (-(kappa c) * p.γ * x) := by
    intro x
    have hm_pos : 0 < p.m := lt_of_lt_of_le zero_lt_one p.hm
    have hUm_nonneg : 0 ≤ (U x) ^ (p.m - 1) :=
      Real.rpow_nonneg (hU_nn x) _
    have hUm_le : (U x) ^ (p.m - 1) ≤
        (MChi p) ^ (p.m - 1) :=
      Real.rpow_le_rpow (hU_nn x) (hU_le x) (by linarith [p.hm])
    have hleft : |p.χ| * p.m * (U x) ^ (p.m - 1) ≤ A := by
      dsimp [A]
      exact mul_le_mul_of_nonneg_left hUm_le
        (mul_nonneg (abs_nonneg _) hm_pos.le)
    have hright : |deriv V x| ≤
        K * Real.exp (-(kappa c) * p.γ * x) := by
      simpa [K] using (hV_exp x).2
    calc
      |p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x| =
          (|p.χ| * p.m * (U x) ^ (p.m - 1)) * |deriv V x| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hm_pos,
          abs_of_nonneg hUm_nonneg]
      _ ≤ A * (K * Real.exp (-(kappa c) * p.γ * x)) :=
        mul_le_mul hleft hright (abs_nonneg _) hA_nonneg
      _ = P * Real.exp (-(kappa c) * p.γ * x) := by
        dsimp [P]
        ring
  have hrate_pos : 0 < kappa c * p.γ :=
    mul_pos hk_pos (lt_of_lt_of_le zero_lt_one p.hγ)
  have hrate_atTop :
      Tendsto (fun x : ℝ => (kappa c * p.γ) * x) atTop atTop :=
    (Filter.tendsto_id.atTop_mul_const hrate_pos).congr
      (fun x => mul_comm x (kappa c * p.γ))
  have hexp_zero :
      Tendsto (fun x : ℝ => Real.exp (-(kappa c) * p.γ * x))
        atTop (𝓝 0) := by
    have hraw := Real.tendsto_exp_atBot.comp
      (Filter.tendsto_neg_atTop_atBot.comp hrate_atTop)
    convert hraw using 1
    ext x
    simp only [Function.comp_apply]
    congr 1
    ring
  have hweighted_zero :
      Tendsto (fun x : ℝ =>
        P * Real.exp (-(kappa c) * p.γ * x)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hexp_zero)
  have heventual_small : ∀ᶠ x in atTop,
      P * Real.exp (-(kappa c) * p.γ * x) < a0 :=
    hweighted_zero.eventually (Iio_mem_nhds ha0_pos)
  obtain ⟨X0, hX0⟩ := eventually_atTop.1 heventual_small
  let X : ℝ := max 0 X0
  have hX_nonneg : 0 ≤ X := le_max_left _ _
  have hsmall : ∀ x, X ≤ x →
      P * Real.exp (-(kappa c) * p.γ * x) < a0 := by
    intro x hx
    exact hX0 x (le_trans (le_max_right 0 X0) hx)
  set w : ℝ → ℝ := fun x =>
    deriv U x * Real.exp (kappa c * x) with hw_def
  set a_w : ℝ → ℝ := fun x =>
    c - kappa c -
      p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x with ha_w_def
  set g_w : ℝ → ℝ := fun x =>
    (p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ) -
      U x * (1 - (U x) ^ p.α)) * Real.exp (kappa c * x) with hg_w_def
  have hw_ode : ∀ x, deriv w x = -a_w x * w x + g_w x := by
    intro x
    have hode := wave_weighted_derivative_ode p c U V hTW hreg x
    simpa only [hw_def, ha_w_def, hg_w_def] using hode
  have ha_lb : ∀ x, X ≤ x → a0 ≤ a_w x := by
    intro x hx
    have hchem_abs := hcoef x
    have hchem_lt :
        |p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x| < a0 :=
      lt_of_le_of_lt hchem_abs (hsmall x hx)
    have hchem :
        p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x < a0 :=
      lt_of_le_of_lt (le_abs_self _) hchem_lt
    simp only [ha_w_def]
    dsimp [a0] at hchem ⊢
    linarith
  set G : ℝ :=
    max (remark51MPrime p)
      (max 0 (|p.χ| *
        (1 / (1 - kappa c ^ 2 * p.γ ^ 2) + 1) + 2)) with hG_def
  have hG_nonneg : 0 ≤ G := by
    simp only [hG_def]
    exact le_trans (le_max_left 0 _)
      (le_max_right (remark51MPrime p) _)
  have hG_bound : ∀ x, |g_w x| ≤ G := by
    intro x
    simpa only [hg_w_def, hG_def] using
      (wave_weighted_source_upper_bound_global hU_nn hU_le
        hMChi_pos hMChi_ge_one hreg.V_nn
        (fun y => (hreg.V_bound y).1) hbound
        (fun y => (hV_exp y).1) hk_pos x)
  have hw_diff : Differentiable ℝ w := by
    intro x
    have hexp_diff : DifferentiableAt ℝ
        (fun y : ℝ => Real.exp (kappa c * y)) x := by
      fun_prop
    exact (hreg.deriv_U_diff x).mul hexp_diff
  obtain ⟨D, hD_nonneg, hD⟩ :=
    exists_nonneg_abs_bound_of_continuous_tendsto_zero_both_ends'
      hreg.deriv_U_cont hreg.deriv_U_tendszero.1
        hreg.deriv_U_tendszero.2
  let C : ℝ := |w X| + G / a0
  have hC_nonneg : 0 ≤ C :=
    add_nonneg (abs_nonneg _) (div_nonneg hG_nonneg ha0_pos.le)
  have hw_tail : ∀ x, X ≤ x → |w x| ≤ C := by
    intro x hx
    have hduh := first_order_ode_duhamel_bound_on_Icc
      (v := w) (a := a_w) (g := g_w) (a₀ := a0) (G := G)
      X x ha0_pos hG_nonneg
      (fun y hy => ha_lb y hy.1)
      (fun y _ => hG_bound y)
      (fun y _ => hw_ode y) hw_diff hx
    have hdelta_nonneg : 0 ≤ x - X := sub_nonneg.mpr hx
    have hexp_le_one : Real.exp (-a0 * (x - X)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr ha0_pos.le) hdelta_nonneg
    have hfirst :
        |w X| * Real.exp (-a0 * (x - X)) ≤ |w X| :=
      mul_le_of_le_one_right (abs_nonneg _) hexp_le_one
    have hdiv_nonneg : 0 ≤ G / a0 :=
      div_nonneg hG_nonneg ha0_pos.le
    have hsecond :
        G / a0 * (1 - Real.exp (-a0 * (x - X))) ≤ G / a0 := by
      have hexp_nonneg : 0 ≤ Real.exp (-a0 * (x - X)) :=
        (Real.exp_pos _).le
      nlinarith
    dsimp [C]
    linarith
  have hU_tail : ∀ x, X ≤ x →
      |deriv U x| ≤ C * Real.exp (-(kappa c) * x) := by
    intro x hx
    have hw_abs : |w x| =
        |deriv U x| * Real.exp (kappa c * x) := by
      simp only [hw_def, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp_inv :
        Real.exp (kappa c * x) * Real.exp (-(kappa c) * x) = 1 := by
      rw [← Real.exp_add]
      rw [show kappa c * x + -(kappa c) * x = 0 by ring,
        Real.exp_zero]
    calc
      |deriv U x| = |deriv U x| * 1 := by ring
      _ = |deriv U x| *
          (Real.exp (kappa c * x) * Real.exp (-(kappa c) * x)) := by
        rw [hexp_inv]
      _ = |deriv U x| * Real.exp (kappa c * x) *
          Real.exp (-(kappa c) * x) := by ring
      _ = |w x| * Real.exp (-(kappa c) * x) := by rw [hw_abs]
      _ ≤ C * Real.exp (-(kappa c) * x) :=
        mul_le_mul_of_nonneg_right (hw_tail x hx) (Real.exp_pos _).le
  let B1 : ℝ := max (D * Real.exp (kappa c * X)) C
  refine ⟨B1, 0, ?_⟩
  intro x
  simp only [zero_mul, add_zero]
  by_cases hx : X ≤ x
  · exact (hU_tail x hx).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.exp_pos _).le)
  · have hx_le : x ≤ X := le_of_not_ge hx
    have harg_nonneg : 0 ≤ kappa c * (X - x) :=
      mul_nonneg hk_pos.le (sub_nonneg.mpr hx_le)
    have hone_exp : 1 ≤ Real.exp (kappa c * (X - x)) :=
      Real.one_le_exp harg_nonneg
    have hD_exp :
        D ≤ (D * Real.exp (kappa c * X)) *
          Real.exp (-(kappa c) * x) := by
      calc
        D = D * 1 := by ring
        _ ≤ D * Real.exp (kappa c * (X - x)) :=
          mul_le_mul_of_nonneg_left hone_exp hD_nonneg
        _ = (D * Real.exp (kappa c * X)) *
            Real.exp (-(kappa c) * x) := by
          rw [show kappa c * (X - x) =
              kappa c * X + (-(kappa c)) * x by ring,
            Real.exp_add]
          ring
    exact (hD x).trans (hD_exp.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.exp_pos _).le))

#print axioms Lemma_5_1_wave_derivative_exponential_bound_of_regularity

/-- The complete formal conclusion of Lemma 5.1 for an arbitrary regular
traveling wave with an identified elliptic resolver. -/
theorem Lemma_5_1_arbitrary_wave_full_conclusion
    {p : CMParams} {c : ℝ} (hc : 2 < c)
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hresolvent : V = frozenElliptic p U) :
    (∀ x,
      |V x| ≤ (MChi p) ^ p.γ ∧
        |deriv V x| ≤ (MChi p) ^ p.γ) ∧
    (p.γ + p.γ⁻¹ < c →
      ∀ x,
        |V x| ≤
          min ((MChi p) ^ p.γ)
            ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
              Real.exp (-(kappa c) * p.γ * x)) ∧
        |deriv V x| ≤
          min ((MChi p) ^ p.γ)
            ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
              Real.exp (-(kappa c) * p.γ * x))) ∧
    WaveDerivativeTendsZero U ∧
    (c > p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) →
      ∃ B > 0, ∀ x, |deriv U x| ≤ B) ∧
    (c > max (p.γ + p.γ⁻¹)
        (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) →
      ∃ B1 B2, ∀ x,
        |deriv U x| ≤
          B1 * Real.exp (-(kappa c) * x) +
            B2 * Real.exp (-(kappa c) * p.γ * x)) := by
  have hderiv_tends : WaveDerivativeTendsZero U :=
    ⟨hreg.deriv_U_tendszero.2, hreg.deriv_U_tendszero.1⟩
  have hderiv_bound :
      c > p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) →
        ∃ B > 0, ∀ x, |deriv U x| ≤ B := by
    intro _
    exact Lemma_5_1_wave_derivative_global_bound_of_regularity hreg
  have hderiv_exp :
      c > max (p.γ + p.γ⁻¹)
          (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) →
        ∃ B1 B2, ∀ x,
          |deriv U x| ≤
            B1 * Real.exp (-(kappa c) * x) +
              B2 * Real.exp (-(kappa c) * p.γ * x) := by
    intro hspeed
    have hgamma_speed : p.γ + p.γ⁻¹ < c :=
      lt_of_le_of_lt (le_max_left _ _) hspeed
    have hFE_exp :=
      Lemma_5_1_exponential_signal_bound_for_frozenElliptic_of_continuous
        p hc hgamma_speed hreg.U_cont hbound
    have hV_exp : ∀ x,
        |V x| ≤
          (1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
            Real.exp (-(kappa c) * p.γ * x) ∧
        |deriv V x| ≤
          (1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
            Real.exp (-(kappa c) * p.γ * x) := by
      intro x
      rw [hresolvent]
      exact
        ⟨(hFE_exp x).1.trans (min_le_right _ _),
          (hFE_exp x).2.trans (min_le_right _ _)⟩
    exact Lemma_5_1_wave_derivative_exponential_bound_of_regularity
      hc hTW hreg hbound hV_exp
  exact Lemma_5_1_resolvent_identified_direct hc hTW hresolvent
    hreg.U_cont hbound hderiv_tends hderiv_bound hderiv_exp

#print axioms Lemma_5_1_arbitrary_wave_full_conclusion

end


end ShenWork.Paper1
