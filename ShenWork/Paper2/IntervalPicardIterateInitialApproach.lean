/-
  ShenWork/Paper2/IntervalPicardIterateInitialApproach.lean

  **The iterate initial approach (χ₀ = 0) — the `hcont`-at-`0` core, hand-written.**

  `picardIter p u₀ n s → u₀` in sup norm as `s → 0⁺`, for every level `n`:

  * level `n+1`: `picardIter (n+1) s = Φ(u₀, picardIter n) s`; at χ₀ = 0 the map is
    `S(s)(lift u₀) + ∫₀ˢ S(s−r) L(uₙ(r)) dr`.  The homogeneous leg is the G5
    strong-continuity block of `gradientMildSolutionData_initialApproach`
    (clipped extension + `intervalFullSemigroup_tendstoUniformlyOn`); the Duhamel
    leg is `≤ s·C_L` (`valueDuhamel_sup_bound_universal` on the time-windowed
    source family, bounded by the cone ball).  The chemotaxis correction of the
    original proof VANISHES at χ₀ = 0, so no flux machinery is needed.
  * level `0`: `picardIter 0 s = S(s)(lift u₀)` — the homogeneous leg alone.

  This is the iterate analog of the limit side's
  `gradientMildSolutionData_initialApproach`, with the mild-solution datum `D`
  replaced by the cone-returned iterate facts (ball + slice continuity).  It
  supplies the `s = 0` continuity of the PATCHED iterate source coefficients
  (the `hcont` field of the iterate `DuhamelSourceBddOn` package — the last
  analytic input of the `hsrc0` elimination).

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalMildPicardThreshold
import ShenWork.Paper2.IntervalPicardIterateRestart
import ShenWork.PDE.IntervalChemFluxLipschitz

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted intervalGradientDuhamelMap)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalMildPicardThreshold (unitClip unitClip_continuous unitClip_of_mem)
open ShenWork.IntervalPicardIterateRestart (intervalGradientDuhamelMap_eq_of_chi0_zero)

noncomputable section

namespace ShenWork.IntervalPicardIterateInitialApproach

/-! ## §1 — The homogeneous (G5) leg: `S(t)(lift u₀) → u₀` uniformly. -/

/-- **Homogeneous initial approach.**  For continuous `u₀` there is a horizon
`δ₁ > 0` with `|S(t)(lift u₀)(x) − u₀(x)| < ε` for all `0 < t < δ₁` and all
subtype points `x` (the G5 strong-continuity block, via the clipped extension). -/
theorem semigroup_initialApproach (_p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ} (hu₀_cont : Continuous u₀) :
    ∀ ε, 0 < ε → ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x : intervalDomainPoint,
        |intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 - u₀ x| < ε := by
  intro ε hε
  -- G5 horizon for the clipped extension.
  set f : ℝ → ℝ := fun y => u₀ (unitClip y) with hfdef
  have hf_cont : Continuous f := hu₀_cont.comp unitClip_continuous
  have hG5 :=
    ShenWork.IntervalSemigroupUniform.intervalFullSemigroup_tendstoUniformlyOn
      f hf_cont
  rw [Metric.tendstoUniformlyOn_iff] at hG5
  have hev := hG5 ε hε
  rw [Filter.eventually_iff, mem_nhdsGT_iff_exists_Ioo_subset] at hev
  obtain ⟨δ₁, hδ₁mem, hδ₁sub⟩ := hev
  have hδ₁ : 0 < δ₁ := hδ₁mem
  refine ⟨δ₁, hδ₁, ?_⟩
  intro t ht htδ x
  -- `S(t)(lift u₀) = S(t)f` (the integrand only reads `[0,1]`, where they agree).
  have hlift_eq_f : ∀ y ∈ Set.Icc (0:ℝ) 1, intervalDomainLift u₀ y = f y := by
    intro y hy
    simp only [intervalDomainLift, dif_pos hy, hfdef, unitClip_of_mem hy]
  have hSg_eq : intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
      = intervalFullSemigroupOperator t f x.1 := by
    unfold intervalFullSemigroupOperator
    apply MeasureTheory.integral_congr_ae
    have : ∀ᵐ y ∂(ShenWork.IntervalDomain.intervalMeasure 1),
        y ∈ Set.Icc (0:ℝ) 1 := by
      simp only [ShenWork.IntervalDomain.intervalMeasure,
        ShenWork.IntervalDomain.intervalSet]
      exact (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
        (Filter.Eventually.of_forall fun y hy => hy)
    filter_upwards [this] with y hy
    rw [hlift_eq_f y hy]
  rw [hSg_eq]
  have hfx : f x.1 = u₀ x := by
    simp only [hfdef, unitClip_of_mem x.2]
    rfl
  have hdist := hδ₁sub ⟨ht, htδ⟩ x.1 x.2
  rw [Real.dist_eq] at hdist
  calc |intervalFullSemigroupOperator t f x.1 - u₀ x|
      = |f x.1 - intervalFullSemigroupOperator t f x.1| := by
        rw [hfx, abs_sub_comm]
    _ < ε := hdist

/-! ## §2 — The generic χ₀ = 0 map approach over a ball-bounded family. -/

/-- **Initial approach of the χ₀ = 0 mild map over a ball-bounded family.**
For any slice family `w` bounded by `M` on `(0,T]`,
`|Φ(u₀, w) t x − u₀ x| < ε` for all small `t > 0`: the homogeneous leg by §1,
the value-Duhamel leg by `≤ t·C_L` (the chemotaxis term vanishes at χ₀ = 0). -/
theorem gradientDuhamelMap_initialApproach_of_ball (p : CM2Params)
    (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (hu₀_cont : Continuous u₀)
    {w : ℝ → intervalDomainPoint → ℝ} {M T : ℝ}
    (hTpos : 0 < T) (hM : 0 < M)
    (hball : ∀ s, 0 < s → s ≤ T → ∀ y : intervalDomainPoint, |w s y| ≤ M) :
    ∀ ε, 0 < ε → ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x : intervalDomainPoint,
        |intervalGradientDuhamelMap p u₀ w t x - u₀ x| < ε := by
  intro ε hε
  -- the source sup constant
  set C_L_val := M * (p.a + p.b * M ^ p.α) with hCLval
  have hC_L_val_nn : (0 : ℝ) ≤ C_L_val :=
    mul_nonneg hM.le (add_nonneg p.ha
      (mul_nonneg p.hb (Real.rpow_nonneg hM.le _)))
  -- δ₂: Duhamel horizon with 0·√t + C_L·t < ε/2.
  obtain ⟨δ₂, hδ₂, hδ₂small⟩ :=
    exists_small_contraction_time_target (le_refl (0:ℝ)) hC_L_val_nn
      (show (0:ℝ) < ε / 2 by linarith)
  -- δ₁: homogeneous horizon (§1).
  obtain ⟨δ₁, hδ₁, hδ₁close⟩ := semigroup_initialApproach p hu₀_cont (ε / 2)
    (by linarith)
  refine ⟨min (min δ₁ δ₂) T, lt_min (lt_min hδ₁ hδ₂) hTpos, ?_⟩
  intro t ht htδ x
  have htδ₁ : t < δ₁ := lt_of_lt_of_le htδ ((min_le_left _ _).trans (min_le_left _ _))
  have htδ₂ : t < δ₂ := lt_of_lt_of_le htδ ((min_le_left _ _).trans (min_le_right _ _))
  have htT : t ≤ T := le_of_lt (lt_of_lt_of_le htδ (min_le_right _ _))
  -- homogeneous leg < ε/2.
  have hSg_close : |intervalFullSemigroupOperator t
      (intervalDomainLift u₀) x.1 - u₀ x| < ε / 2 := hδ₁close t ht htδ₁ x
  -- Duhamel leg ≤ t·C_L via the time-windowed source family.
  set r_val : ℝ → ℝ → ℝ := fun s y =>
    if 0 < s ∧ s ≤ T then logisticLifted p (w s) y else 0 with hrval
  have hr_val_bound : ∀ s y, |r_val s y| ≤ C_L_val := by
    intro s y; simp only [hrval]
    split_ifs with h
    · exact ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound
        p hM (fun z => hball s h.1 h.2 z) y
    · simp; exact hC_L_val_nn
  have hval_eq : (∫ s in (0:ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1)
      = ∫ s in (0:ℝ)..t,
        intervalFullSemigroupOperator (t - s) (r_val s) x.1 := by
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    simp only [hrval, if_pos (And.intro hs.1 (hs.2.trans htT))]
  have hterm3 : |(∫ s in (0:ℝ)..t,
      intervalFullSemigroupOperator (t - s)
        (logisticLifted p (w s)) x.1)| ≤ t * C_L_val := by
    rw [hval_eq]
    exact ShenWork.IntervalDuhamelIntegrability.valueDuhamel_sup_bound_universal
      ht le_rfl hC_L_val_nn hr_val_bound x.1
  have hduh_close : |(∫ s in (0:ℝ)..t,
      intervalFullSemigroupOperator (t - s)
        (logisticLifted p (w s)) x.1)| < ε / 2 := by
    have hAB : (0:ℝ) * Real.sqrt t + C_L_val * t
        ≤ (0:ℝ) * Real.sqrt δ₂ + C_L_val * δ₂ := by
      have := mul_le_mul_of_nonneg_left htδ₂.le hC_L_val_nn
      simpa using this
    calc |(∫ s in (0:ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1)|
        ≤ t * C_L_val := hterm3
      _ = (0:ℝ) * Real.sqrt t + C_L_val * t := by ring
      _ ≤ (0:ℝ) * Real.sqrt δ₂ + C_L_val * δ₂ := hAB
      _ < ε / 2 := hδ₂small
  -- assemble through the χ₀ = 0 form of the map.
  rw [intervalGradientDuhamelMap_eq_of_chi0_zero p hχ0 u₀ w t x]
  calc |intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
        + (∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
            (logisticLifted p (w s)) x.1) - u₀ x|
      = |(intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 - u₀ x)
        + (∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
            (logisticLifted p (w s)) x.1)| := by congr 1; ring
    _ ≤ |intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 - u₀ x|
        + |(∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
            (logisticLifted p (w s)) x.1)| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hSg_close hduh_close
    _ = ε := by ring

/-! ## §3 — The per-level iterate initial approach. -/

/-- **Iterate initial approach (χ₀ = 0, all levels).**  For every level `n`,
`picardIter p u₀ n s → u₀` uniformly on the subtype as `s → 0⁺`: level `0` is
the homogeneous leg (§1); level `n+1` is the map approach (§2) at `w := uₙ`
with the cone ball. -/
theorem picardIter_initialApproach (p : CM2Params)
    (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (hu₀_cont : Continuous u₀)
    {M T : ℝ} (hTpos : 0 < T) (hM : 0 < M)
    (hball : ∀ (n : ℕ) (s : ℝ), 0 < s → s ≤ T → ∀ y : intervalDomainPoint,
      |picardIter p u₀ n s y| ≤ M)
    (n : ℕ) :
    ∀ ε, 0 < ε → ∃ δ > 0, ∀ s, 0 < s → s < δ →
      ∀ y : intervalDomainPoint, |picardIter p u₀ n s y - u₀ y| < ε := by
  cases n with
  | zero =>
    intro ε hε
    obtain ⟨δ, hδ, hclose⟩ := semigroup_initialApproach p hu₀_cont ε hε
    refine ⟨δ, hδ, ?_⟩
    intro s hs hsδ y
    have : picardIter p u₀ 0 s y
        = intervalFullSemigroupOperator s (intervalDomainLift u₀) y.1 := rfl
    rw [this]
    exact hclose s hs hsδ y
  | succ n =>
    intro ε hε
    obtain ⟨δ, hδ, hclose⟩ := gradientDuhamelMap_initialApproach_of_ball p hχ0
      hu₀_cont hTpos hM (hball n) ε hε
    refine ⟨δ, hδ, ?_⟩
    intro s hs hsδ y
    have : picardIter p u₀ (n + 1) s y
        = intervalGradientDuhamelMap p u₀ (picardIter p u₀ n) s y := rfl
    rw [this]
    exact hclose s hs hsδ y

end ShenWork.IntervalPicardIterateInitialApproach
