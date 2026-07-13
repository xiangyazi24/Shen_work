/- Unconditional positive-attraction traveling-wave producer. -/
import ShenWork.Paper1.WavePositiveSelfStepClosedGraph
import ShenWork.Paper1.WavePositiveStrictBarrier
import ShenWork.Paper1.StationaryUpperTail

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- Barbalat on the right half-line: a differentiable profile with a finite
limit and globally Lipschitz first derivative has derivative tending to zero.
The Lipschitz estimate is supplied here by a uniform second-derivative bound. -/
theorem deriv_tendsto_atTop_zero_of_tail_of_second_bound
    {U : ℝ → ℝ} {L C : ℝ}
    (hlim : Tendsto U atTop (nhds L))
    (hU_diff : Differentiable ℝ U)
    (hU'_diff : Differentiable ℝ (deriv U))
    (hC_nonneg : 0 ≤ C)
    (hU''_bound : ∀ x, |deriv (deriv U) x| ≤ C) :
    Tendsto (deriv U) atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ : ℝ := ε / (2 * (C + 1)) with hδ_def
  have hC1_pos : 0 < C + 1 := by linarith
  have hden_pos : 0 < 2 * (C + 1) := by positivity
  have hδ_pos : 0 < δ := by
    rw [hδ_def]
    exact div_pos hε hden_pos
  have hCδ_le : C * δ ≤ ε / 2 := by
    rw [hδ_def]
    have hden_ne : 2 * (C + 1) ≠ 0 := ne_of_gt hden_pos
    field_simp [hden_ne]
    nlinarith [hC_nonneg, hε.le]
  set drop : ℝ := (ε / 2) * δ with hdrop_def
  have hdrop_pos : 0 < drop := by
    rw [hdrop_def]
    positivity
  set η : ℝ := drop / 4 with hη_def
  have hη_pos : 0 < η := by
    rw [hη_def]
    positivity
  have htail_event : ∀ᶠ x in atTop, dist (U x) L < η :=
    Metric.tendsto_nhds.mp hlim η hη_pos
  rcases Filter.eventually_atTop.mp htail_event with ⟨A, hA⟩
  rw [Filter.eventually_atTop]
  refine ⟨A, ?_⟩
  intro x hx
  rw [Real.dist_eq, sub_zero]
  by_contra hnot
  have hxabs : ε ≤ |deriv U x| := le_of_not_gt hnot
  let b : ℝ := x + δ
  have hxb : x < b := by simp [b, hδ_pos]
  have hbA : A ≤ b := le_trans hx hxb.le
  have hxclose : |U x - L| < η := by
    simpa [Real.dist_eq] using hA x hx
  have hbclose : |U b - L| < η := by
    simpa [Real.dist_eq] using hA b hbA
  have hub : |U b - U x| < drop := by
    have htri : |U b - U x| ≤ |U b - L| + |U x - L| := by
      calc
        |U b - U x| = |(U b - L) - (U x - L)| := by ring_nf
        _ ≤ |U b - L| + |U x - L| := abs_sub _ _
    have hsum : |U b - L| + |U x - L| < 2 * η := by linarith
    have heta_drop : 2 * η < drop := by rw [hη_def]; linarith
    exact lt_of_le_of_lt htri (lt_trans hsum heta_drop)
  obtain ⟨y, hy, hyderiv⟩ :=
    exists_deriv_eq_slope U hxb hU_diff.continuous.continuousOn
      hU_diff.differentiableOn
  have hderiv_lip : |deriv U y - deriv U x| ≤ C * |y - x| := by
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Set.univ) (f := deriv U) (C := C)
      (fun z _hz => hU'_diff z)
      (fun z _hz => by
        simpa [Real.norm_eq_abs] using hU''_bound z)
      convex_univ (by simp : y ∈ (Set.univ : Set ℝ))
      (by simp : x ∈ (Set.univ : Set ℝ))
    have hmv' : |deriv U x - deriv U y| ≤ C * |x - y| := by
      simpa [Real.norm_eq_abs] using hmv
    calc
      |deriv U y - deriv U x| = |deriv U x - deriv U y| :=
        abs_sub_comm _ _
      _ ≤ C * |x - y| := hmv'
      _ = C * |y - x| := by rw [abs_sub_comm x y]
  have hyx_lt : |y - x| < δ := by
    have hyx : x < y := hy.1
    have hyb : y < b := hy.2
    rw [abs_of_pos (sub_pos.mpr hyx)]
    dsimp [b] at hyb
    linarith
  have hderiv_close : |deriv U y - deriv U x| ≤ ε / 2 :=
    le_trans hderiv_lip
      (le_trans (mul_le_mul_of_nonneg_left hyx_lt.le hC_nonneg) hCδ_le)
  have hyabs : ε / 2 ≤ |deriv U y| := by
    have htri : |deriv U x| ≤
        |deriv U x - deriv U y| + |deriv U y| := by
      calc
        |deriv U x| =
            |(deriv U x - deriv U y) + deriv U y| := by ring_nf
        _ ≤ |deriv U x - deriv U y| + |deriv U y| := abs_add_le _ _
    have habsdiff : |deriv U x| - |deriv U y| ≤
        |deriv U x - deriv U y| := sub_le_iff_le_add.mpr htri
    have hsymm : |deriv U x - deriv U y| =
        |deriv U y - deriv U x| := by rw [abs_sub_comm]
    rw [hsymm] at habsdiff
    linarith
  have hslope_abs : |deriv U y| = |U b - U x| / δ := by
    have hbx : |b - x| = δ := by
      rw [abs_of_pos (sub_pos.mpr hxb)]
      dsimp [b]
      ring
    rw [hyderiv, abs_div, hbx]
  rw [hslope_abs] at hyabs
  have hlb : drop ≤ |U b - U x| := by
    rw [hdrop_def]
    exact (le_div_iff₀ hδ_pos).mp hyabs
  exact (not_lt_of_ge hlb) hub

/-- Left-half-line counterpart of
`deriv_tendsto_atTop_zero_of_tail_of_second_bound`. -/
theorem deriv_tendsto_atBot_zero_of_tail_of_second_bound
    {U : ℝ → ℝ} {L C : ℝ}
    (hlim : Tendsto U atBot (nhds L))
    (hU_diff : Differentiable ℝ U)
    (hU'_diff : Differentiable ℝ (deriv U))
    (hC_nonneg : 0 ≤ C)
    (hU''_bound : ∀ x, |deriv (deriv U) x| ≤ C) :
    Tendsto (deriv U) atBot (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ : ℝ := ε / (2 * (C + 1)) with hδ_def
  have hC1_pos : 0 < C + 1 := by linarith
  have hden_pos : 0 < 2 * (C + 1) := by positivity
  have hδ_pos : 0 < δ := by
    rw [hδ_def]
    exact div_pos hε hden_pos
  have hCδ_le : C * δ ≤ ε / 2 := by
    rw [hδ_def]
    have hden_ne : 2 * (C + 1) ≠ 0 := ne_of_gt hden_pos
    field_simp [hden_ne]
    nlinarith [hC_nonneg, hε.le]
  set drop : ℝ := (ε / 2) * δ with hdrop_def
  have hdrop_pos : 0 < drop := by
    rw [hdrop_def]
    positivity
  set η : ℝ := drop / 4 with hη_def
  have hη_pos : 0 < η := by
    rw [hη_def]
    positivity
  have htail_event : ∀ᶠ x in atBot, dist (U x) L < η :=
    Metric.tendsto_nhds.mp hlim η hη_pos
  rcases Filter.eventually_atBot.mp htail_event with ⟨A, hA⟩
  rw [Filter.eventually_atBot]
  refine ⟨A - δ, ?_⟩
  intro x hx
  rw [Real.dist_eq, sub_zero]
  by_contra hnot
  have hxabs : ε ≤ |deriv U x| := le_of_not_gt hnot
  let b : ℝ := x + δ
  have hxb : x < b := by simp [b, hδ_pos]
  have hxA : x ≤ A := by linarith
  have hbA : b ≤ A := by dsimp [b]; linarith
  have hxclose : |U x - L| < η := by
    simpa [Real.dist_eq] using hA x hxA
  have hbclose : |U b - L| < η := by
    simpa [Real.dist_eq] using hA b hbA
  have hub : |U b - U x| < drop := by
    have htri : |U b - U x| ≤ |U b - L| + |U x - L| := by
      calc
        |U b - U x| = |(U b - L) - (U x - L)| := by ring_nf
        _ ≤ |U b - L| + |U x - L| := abs_sub _ _
    have hsum : |U b - L| + |U x - L| < 2 * η := by linarith
    have heta_drop : 2 * η < drop := by rw [hη_def]; linarith
    exact lt_of_le_of_lt htri (lt_trans hsum heta_drop)
  obtain ⟨y, hy, hyderiv⟩ :=
    exists_deriv_eq_slope U hxb hU_diff.continuous.continuousOn
      hU_diff.differentiableOn
  have hderiv_lip : |deriv U y - deriv U x| ≤ C * |y - x| := by
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Set.univ) (f := deriv U) (C := C)
      (fun z _hz => hU'_diff z)
      (fun z _hz => by
        simpa [Real.norm_eq_abs] using hU''_bound z)
      convex_univ (by simp : y ∈ (Set.univ : Set ℝ))
      (by simp : x ∈ (Set.univ : Set ℝ))
    have hmv' : |deriv U x - deriv U y| ≤ C * |x - y| := by
      simpa [Real.norm_eq_abs] using hmv
    calc
      |deriv U y - deriv U x| = |deriv U x - deriv U y| :=
        abs_sub_comm _ _
      _ ≤ C * |x - y| := hmv'
      _ = C * |y - x| := by rw [abs_sub_comm x y]
  have hyx_lt : |y - x| < δ := by
    have hyx : x < y := hy.1
    have hyb : y < b := hy.2
    rw [abs_of_pos (sub_pos.mpr hyx)]
    dsimp [b] at hyb
    linarith
  have hderiv_close : |deriv U y - deriv U x| ≤ ε / 2 :=
    le_trans hderiv_lip
      (le_trans (mul_le_mul_of_nonneg_left hyx_lt.le hC_nonneg) hCδ_le)
  have hyabs : ε / 2 ≤ |deriv U y| := by
    have htri : |deriv U x| ≤
        |deriv U x - deriv U y| + |deriv U y| := by
      calc
        |deriv U x| =
            |(deriv U x - deriv U y) + deriv U y| := by ring_nf
        _ ≤ |deriv U x - deriv U y| + |deriv U y| := abs_add_le _ _
    have habsdiff : |deriv U x| - |deriv U y| ≤
        |deriv U x - deriv U y| := sub_le_iff_le_add.mpr htri
    have hsymm : |deriv U x - deriv U y| =
        |deriv U y - deriv U x| := by rw [abs_sub_comm]
    rw [hsymm] at habsdiff
    linarith
  have hslope_abs : |deriv U y| = |U b - U x| / δ := by
    have hbx : |b - x| = δ := by
      rw [abs_of_pos (sub_pos.mpr hxb)]
      dsimp [b]
      ring
    rw [hyderiv, abs_div, hbx]
  rw [hslope_abs] at hyabs
  have hlb : drop ≤ |U b - U x| := by
    rw [hdrop_def]
    exact (le_div_iff₀ hδ_pos).mp hyabs
  exact (not_lt_of_ge hlb) hub

/-- A bounded Green step whose profile has finite limits is flat at both
ends.  Boundedness of the Green source gives a global second-derivative bound,
so the two preceding Barbalat lemmas apply without any monotonicity premise. -/
theorem PaperStepAnalytic.deriv_tends_zero_of_profile_limits
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z W : ℝ → ℝ}
    (ha : PaperStepAnalytic p c lam M κ Λ u Z W)
    (hlam : 0 < lam) (hM : 0 ≤ M)
    (hWbound : ∀ x, |W x| ≤ M)
    (hW2 : ContDiff ℝ 2 W)
    {La Lb : ℝ}
    (hbot : Tendsto W atBot (nhds La))
    (htop : Tendsto W atTop (nhds Lb)) :
    Tendsto (deriv W) atTop (nhds 0) ∧
      Tendsto (deriv W) atBot (nhds 0) := by
  obtain ⟨B, hRbound, _hΛeq⟩ := ha.R_bound
  have hB : 0 ≤ B := le_trans (abs_nonneg (ha.R 0)) (hRbound 0)
  have hΛ : 0 ≤ Λ :=
    le_trans (abs_nonneg (deriv W 0))
      (paperStep_deriv_le (c := c) (lam := lam) hlam ha 0)
  let C : ℝ := |c| * Λ + lam * M + B
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hW_diff : Differentiable ℝ W := hW2.differentiable (by norm_num)
  have hW'_diff : Differentiable ℝ (deriv W) := by
    simpa [iteratedDeriv_one] using
      hW2.differentiable_iteratedDeriv 1 (by norm_num)
  have hW'' : ∀ x, |deriv (deriv W) x| ≤ C := by
    intro x
    have heq : deriv (deriv W) x =
        -c * deriv W x + lam * W x - ha.R x := by
      have hres := greenConv_variation_negative
        (c := c) (lam := lam) hlam ha.R_cont ha.R_hi ha.R_lo x
      have hiter : iteratedDeriv 2 (greenConv c lam ha.R) x =
          deriv (deriv (greenConv c lam ha.R)) x := by
        rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
          iteratedDeriv_one]
      rw [hiter] at hres
      have hval : W x = greenConv c lam ha.R x :=
        congrFun ha.green_repr x
      have hderiv : deriv W x = deriv (greenConv c lam ha.R) x :=
        congrArg (fun f : ℝ → ℝ => deriv f x) ha.green_repr
      have hderiv2 : deriv (deriv W) x =
          deriv (deriv (greenConv c lam ha.R)) x :=
        congrArg (fun f : ℝ → ℝ => deriv (deriv f) x) ha.green_repr
      rw [hderiv2, hderiv, hval]
      linarith
    rw [heq]
    have htri :
        |-c * deriv W x + lam * W x - ha.R x| ≤
          |-c * deriv W x| + |lam * W x| + |ha.R x| := by
      calc
        |-c * deriv W x + lam * W x - ha.R x|
            ≤ |-c * deriv W x + lam * W x| + |-ha.R x| :=
              abs_add_le _ _
        _ ≤ (|-c * deriv W x| + |lam * W x|) + |-ha.R x| :=
              add_le_add (abs_add_le _ _) le_rfl
        _ = |-c * deriv W x| + |lam * W x| + |ha.R x| := by
              rw [abs_neg]
    refine htri.trans ?_
    have hderiv := paperStep_deriv_le (c := c) (lam := lam) hlam ha x
    have hcabs : 0 ≤ |c| := abs_nonneg c
    have hlam0 : 0 ≤ lam := hlam.le
    calc
      |-c * deriv W x| + |lam * W x| + |ha.R x| =
          |c| * |deriv W x| + lam * |W x| + |ha.R x| := by
            rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg hlam0]
      _ ≤ |c| * Λ + lam * M + B :=
          add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_left hderiv hcabs)
              (mul_le_mul_of_nonneg_left (hWbound x) hlam0))
            (hRbound x)
      _ = C := rfl
  exact
    ⟨deriv_tendsto_atTop_zero_of_tail_of_second_bound
        htop hW_diff hW'_diff hC hW'',
      deriv_tendsto_atBot_zero_of_tail_of_second_bound
        hbot hW_diff hW'_diff hC hW''⟩

/-- The regularity package used in Section 5 is automatic for a stationary
profile produced by a bounded whole-line Green self-step. -/
theorem FrozenStationaryWaveProfile.travelingWaveRegularity_of_green_step
    {p : CMParams} {c lam κ Λ : ℝ} {U : ℝ → ℝ}
    (hprofile : FrozenStationaryWaveProfile p c U)
    (ha : PaperStepAnalytic p c lam (MChi p) κ Λ U U U)
    (hlam : 0 < lam)
    (htrap : InWaveTrapSet κ (MChi p) U)
    (hU2 : ContDiff ℝ 2 U)
    (hV2 : ContDiff ℝ 2 (frozenElliptic p U)) :
    TravelingWaveRegularity p c U (frozenElliptic p U) := by
  have hMpos : 0 < MChi p :=
    lt_of_lt_of_le (hprofile.U_pos 0) (htrap.le_M 0)
  have hUabs : ∀ x, |U x| ≤ MChi p := by
    intro x
    rw [abs_of_nonneg (htrap.nonneg x)]
    exact htrap.le_M x
  have htails : Tendsto (deriv U) atTop (nhds 0) ∧
      Tendsto (deriv U) atBot (nhds 0) :=
    ha.deriv_tends_zero_of_profile_limits hlam hMpos.le hUabs hU2
      hprofile.lim_neg_inf.1 hprofile.lim_pos_inf.1
  have hUdiff : Differentiable ℝ U := hU2.differentiable (by norm_num)
  have hUderivDiff : Differentiable ℝ (deriv U) := by
    simpa [iteratedDeriv_one] using
      hU2.differentiable_iteratedDeriv 1 (by norm_num)
  have hVdiff : Differentiable ℝ (frozenElliptic p U) :=
    hV2.differentiable (by norm_num)
  have hVderivDiff : Differentiable ℝ (deriv (frozenElliptic p U)) := by
    simpa [iteratedDeriv_one] using
      hV2.differentiable_iteratedDeriv 1 (by norm_num)
  refine
    { U_diff := hUdiff
      U_cont := hUdiff.continuous
      V_diff := hVdiff
      V_deriv_diff := hVderivDiff
      deriv_U_cont := hUderivDiff.continuous
      deriv_U_diff := hUderivDiff
      deriv_U_tendszero := htails
      V_nn := ?_
      V_bound := ?_ }
  · exact fun x => frozenElliptic_nonneg_of_inWaveTrapSet p htrap x
  · intro x
    have hVnn : 0 ≤ frozenElliptic p U x :=
      frozenElliptic_nonneg_of_inWaveTrapSet p htrap x
    have hVle : frozenElliptic p U x ≤ (MChi p) ^ p.γ :=
      frozenElliptic_le_rpow_of_inWaveTrapSet p hMpos htrap x
    constructor
    · simpa [abs_of_nonneg hVnn] using hVle
    · exact (frozenElliptic_deriv_abs_le p
        htrap.cunif_bdd htrap.nonneg x).trans hVle

/-- Genuine positive headline construction from the compact-convex
nonmonotone lower-pinned trap and the diagonal whole-line Green self-step.
All scalar choices, Schauder compactness, closed graph, endpoint selection,
strict upper comparison, and tail squeeze are internal theorems. -/
theorem paper1_positiveConstruction_selfStep :
    ∀ p : CMParams, p.α = p.m + p.γ - 1 →
      0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
      ∀ c : ℝ, 2 < c →
        ∃ U : ℝ → ℝ,
          FrozenStationaryWaveProfile p c U ∧
          ContDiff ℝ 2 U ∧
          ContDiff ℝ 2 (frozenElliptic p U) ∧
          TravelingWaveRegularity p c U (frozenElliptic p U) ∧
          ShenUpperBoundPositive p c U ∧
          ∀ κ₁, kappa c < κ₁ →
            κ₁ < min ((1 + p.α) * kappa c)
              (min (p.m * kappa c + 1 / 2) 1) →
            HasWaveRightTailAsymptotic c κ₁ U := by
  intro p hα hχ0 hχsmall c hc
  let hcond := positiveSelfStepExactConditions_of_branchCap
    p hα hχ0 hχsmall hc
  obtain ⟨D, hD1, hDmin, hplateau⟩ :=
    exists_positivePlateau_D p
      (lt_of_lt_of_le hχsmall (min_le_left _ _))
      hcond.hκ0 (sub_pos.mpr hcond.hgap)
  let s : Paper1PositiveLocalStepScalarData p c D :=
    Classical.choice (paper1PositiveLocalStepScalarData_exists p D
      (lt_of_lt_of_le zero_lt_one hcond.hM))
  obtain ⟨U, hU, _hfix, A, hstat, hU2⟩ :=
    paperPositive_fixed_stationary_of_selfStep
      hcond hDmin hD1 hplateau s
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hpos : ∀ x, 0 < U x := by
    intro x
    exact lt_of_lt_of_le
      (lowerBarrierPlateau_pos hcond.hκ0
        (sub_pos.mpr hcond.hgap) hDpos x)
      (hU.lower x)
  have hright : Tendsto U atTop (nhds 0) :=
    hU.bare.tendsto_atTop_zero hcond.hκ0
  have hleft : Tendsto U atBot (nhds 1) := by
    apply positiveStationary_tendsto_atBot_one p hα hχ0
      (lt_of_lt_of_le hχsmall (min_le_left _ _))
      (lt_of_lt_of_le zero_lt_one hcond.hM) hcond.hκ0
      (sub_pos.mpr hcond.hgap) hDpos
      (by simpa [paperPositiveSelfStepModulus] using hU)
      A s.hlam s.hΛ0 hstat
  have hprofile : FrozenStationaryWaveProfile p c U :=
    FrozenStationaryWaveProfile.mk_auto_limits
      (lt_trans two_pos hc) hpos hU.bare.cunif_bdd hstat hleft hright
  have hstrict : ∀ x,
      U x < upperBarrier (kappa c) (MChi p) x :=
    positiveStationary_strict_upperBarrier p hα hχ0 hχsmall hc
      hU.bare hpos hU2 hstat hright
  have hχ1 : p.χ < 1 := by
    have hhalf : p.χ < (1 / 2 : ℝ) :=
      lt_of_lt_of_le hχsmall (min_le_left _ _)
    linarith
  have hupper : ShenUpperBoundPositive p c U :=
    ShenUpperBoundPositive.of_pos_strict_upperBarrier_MChi
      hχ0 hχ1 hpos hstrict
  have htail : ∀ κ₁, kappa c < κ₁ →
      κ₁ < min ((1 + p.α) * kappa c)
        (min (p.m * kappa c + 1 / 2) 1) →
      HasWaveRightTailAsymptotic c κ₁ U :=
    lowerPinnedWaveTrap_tail_family_for_branch
      (p := p) (c := c) (κtilde := positiveBranchTailCap p c)
      (D := D) hDpos.le (by simp [positiveBranchTailCap])
      hU.bare hU.lower
  have hV2 : ContDiff ℝ 2 (frozenElliptic p U) :=
    frozenElliptic_contDiff_two_of_inWaveTrapSet p hU.bare
  have hreg : TravelingWaveRegularity p c U (frozenElliptic p U) :=
    hprofile.travelingWaveRegularity_of_green_step
      A s.hlam hU.bare hU2 hV2
  exact ⟨U, hprofile, hU2, hV2, hreg, hupper, htail⟩

/-- Concrete attraction-regime witness proving that the positive producer is
not an implication over an empty parameter class. -/
theorem paper1_positiveConstruction_selfStep_nonvacuous :
    ∃ p : CMParams, ∃ c : ℝ,
      p.α = p.m + p.γ - 1 ∧
      0 ≤ p.χ ∧ p.χ < min (1 / 2 : ℝ) (chiStar p) ∧
      2 < c ∧
      ∃ U : ℝ → ℝ,
        FrozenStationaryWaveProfile p c U ∧
        ContDiff ℝ 2 U ∧
        ContDiff ℝ 2 (frozenElliptic p U) ∧
        TravelingWaveRegularity p c U (frozenElliptic p U) ∧
        ShenUpperBoundPositive p c U ∧
        ∀ κ₁, kappa c < κ₁ →
          κ₁ < min ((1 + p.α) * kappa c)
            (min (p.m * kappa c + 1 / 2) 1) →
          HasWaveRightTailAsymptotic c κ₁ U := by
  let p : CMParams :=
    { m := 1
      α := 1
      γ := 1
      χ := 1 / 4
      hm := by norm_num
      hα := by norm_num
      hγ := by norm_num }
  have hα : p.α = p.m + p.γ - 1 := by norm_num [p]
  have hχ0 : 0 ≤ p.χ := by norm_num [p]
  have hχsmall : p.χ < min (1 / 2 : ℝ) (chiStar p) := by
    norm_num [p, chiStar]
  have hc : (2 : ℝ) < 3 := by norm_num
  exact ⟨p, 3, hα, hχ0, hχsmall, hc,
    paper1_positiveConstruction_selfStep p hα hχ0 hχsmall 3 hc⟩

section AxiomAudit

#print axioms deriv_tendsto_atTop_zero_of_tail_of_second_bound
#print axioms deriv_tendsto_atBot_zero_of_tail_of_second_bound
#print axioms PaperStepAnalytic.deriv_tends_zero_of_profile_limits
#print axioms FrozenStationaryWaveProfile.travelingWaveRegularity_of_green_step
#print axioms paper1_positiveConstruction_selfStep
#print axioms paper1_positiveConstruction_selfStep_nonvacuous

end AxiomAudit

end ShenWork.Paper1
