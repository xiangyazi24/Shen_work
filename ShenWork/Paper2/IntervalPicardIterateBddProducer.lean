/-
  ShenWork/Paper2/IntervalPicardIterateBddProducer.lean

  **Iterate-side patched bounded-source producer (K1-wall final brick).**

  A horizon-generic clone of
  `IntervalPicardLimitBddProducer.duhamelSourceBddOn_of_mildData`: instead of a
  `GradientMildSolutionData` it takes a bare slice family `u : ℝ → intervalDomainPoint
  → ℝ` and a horizon `T`.  Produces the satisfiable bounded-source package
  `DuhamelSourceBddOn (patchedSource p u₀ u) τ` from:

    * the slice sup bound (`hubt`) + the initial-datum source bound (`hu₀_src_bound`)
      → the constant `M`;
    * the per-slice cosine representation (`bc`/`hbsum`/`hagree`) + per-compact `K2`
      gradient/Hessian bounds (`hG1t`/`hG2t`) → the per-window quadratic-decay
      envelopes;
    * the patched-coefficient time continuity on `[0,τ]` (`hcontP`, satisfiable from
      `HasContinuousSlices`) → `hcont`.

  This is the iterate-side replacement for the canonical `DuhamelSourceTimeC1`
  residual `hsrc0`: every input is tower-internal data (`TowerLevel`/`TowerInputs`
  cone-returned facts), none is the unfillable global ℓ¹-at-`s=0` package.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardLimitBddProducer
import ShenWork.Paper2.IntervalPicardLimitBddHcontP

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalPicardLimitRestartBdd (DuhamelSourceBddOn)
open ShenWork.IntervalMildPicardRegularity
  (logisticSourceFun logisticLifted_eq_logisticSourceFun_on_Icc
   cosineCoeffs_abs_le_of_continuous_bounded cosineCoeffs_zero_abs_le_of_bound
   logisticSourceFun_abs_le_of_bound)
open ShenWork.IntervalLogisticSourceQuantBound
  (B_log logisticSourceFun_cosineCoeff_quadratic_decay_explicit)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)
open ShenWork.IntervalPicardLimitBddProducer
  (patchedSource patchedSource_eq_of_pos windowEnv windowEnv_summable
   patchedSource_windowEnv_bound)
open ShenWork.IntervalPicardLimitBddHcontP (lift_continuousOn_Icc)

noncomputable section

namespace ShenWork.IntervalPicardIterateBddProducer

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## 0. The `s ≤ 0` branch datum-source-coefficient bound (no positivity).

The patched family's `s ≤ 0` branch reads `cosineCoeffs (logisticLifted p u₀)`.
For the BddOn package we only need SOME finite bound on these coefficients.  Mere
subtype `Continuous u₀` suffices: `intervalDomainLift u₀` is continuous on the
compact `[0,1]`, hence bounded; `logisticSourceFun` of a bounded continuous profile
is continuous and bounded on `[0,1]` (the `rpow` leg uses the nonneg-exponent branch,
no positivity); `cosineCoeffs_abs_le_of_continuous_bounded` bounds the coefficients.
No `PositiveInitialDatum` data is consumed. -/
theorem exists_datum_source_coeff_bound
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (hα : 1 ≤ p.α) (_ha : 0 ≤ p.a) (_hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀) :
    ∃ M₀' : ℝ, 0 ≤ M₀' ∧ ∀ k, |cosineCoeffs (logisticLifted p u₀) k| ≤ M₀' := by
  have hαnn : (0 : ℝ) ≤ p.α := le_trans zero_le_one hα
  have hcontLift : ContinuousOn (intervalDomainLift u₀) (Set.Icc (0 : ℝ) 1) :=
    lift_continuousOn_Icc hu₀_cont
  -- continuity of the logistic source on [0,1] (nonneg-exponent rpow branch — no
  -- positivity needed).
  have hcontSrc : ContinuousOn
      (logisticSourceFun p.a p.b p.α (intervalDomainLift u₀)) (Set.Icc (0 : ℝ) 1) := by
    unfold logisticSourceFun
    apply ContinuousOn.mul hcontLift
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.mul continuousOn_const
    exact ContinuousOn.rpow_const hcontLift (fun x _ => Or.inr hαnn)
  -- sup bound on the source over the compact [0,1] via compactness of the image
  -- (continuous on compact ⟹ bounded — no explicit formula, no positivity).
  have hcompact : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  have habs_cont : ContinuousOn
      (fun x => |logisticSourceFun p.a p.b p.α (intervalDomainLift u₀) x|)
      (Set.Icc (0 : ℝ) 1) := hcontSrc.abs
  obtain ⟨B, hB⟩ : ∃ B, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |logisticSourceFun p.a p.b p.α (intervalDomainLift u₀) x| ≤ B := by
    obtain ⟨x₀, hx₀mem, hx₀⟩ := hcompact.exists_isMaxOn
      (Set.nonempty_Icc.mpr (by norm_num)) habs_cont
    exact ⟨|logisticSourceFun p.a p.b p.α (intervalDomainLift u₀) x₀|, fun x hx => hx₀ hx⟩
  have hB0 : 0 ≤ B :=
    le_trans (abs_nonneg _) (hB (0 : ℝ) (by constructor <;> norm_num))
  refine ⟨2 * B, by positivity, fun k => ?_⟩
  -- bridge logisticLifted = logisticSourceFun on [0,1] at the coefficient level.
  have hcoeff_eq : cosineCoeffs (logisticLifted p u₀) k
      = cosineCoeffs (logisticSourceFun p.a p.b p.α (intervalDomainLift u₀)) k :=
    cosineCoeffs_congr_on_Icc (logisticLifted_eq_logisticSourceFun_on_Icc p u₀) k
  rw [hcoeff_eq]
  exact cosineCoeffs_abs_le_of_continuous_bounded hcontSrc hB0 hB k

/-! ## 1. `T`-bounded per-window envelope.

`patchedSource_windowEnv_bound` requires the slice data UNCONDITIONALLY (`∀ σ, 0 < σ`)
because the limit-side family `D.u` is the genuine solution.  The iterate slice data
is only proven on `(0,T]`.  This `T`-bounded clone reads the slice data only at the
single window slice `s ∈ [a',τ]` with `τ < T`, so `s ≤ T` always holds.  The body is
the same quadratic-decay assembly. -/
theorem patchedSource_windowEnv_bound_on
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (u : ℝ → intervalDomainPoint → ℝ)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {Msup T : ℝ}
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ ≤ T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ ≤ T → Set.EqOn (intervalDomainLift (u σ))
        (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpost : ∀ σ, 0 < σ → σ ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u σ) x)
    (hubt : ∀ σ, 0 < σ → σ ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u σ) x ≤ Msup)
    {a' τ : ℝ} (ha' : 0 < a') (hτT : τ ≤ T) {G1 G2 : ℝ}
    (hG1 : ∀ σ ∈ Set.Icc a' τ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (u σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Set.Icc a' τ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2) :
    ∀ s, a' ≤ s → s ≤ τ → ∀ k,
      |patchedSource p u₀ u s k|
        ≤ windowEnv (max (2 * B_log p.a p.b p.α Msup G1 G2)
            (Msup * (p.a + p.b * Msup ^ p.α))) k := by
  -- restrict the bounded slice data to the window `[a', τ] ⊆ (0, T]` and forward to
  -- the unconditional limit-side lemma (its `∀ σ, 0 < σ` hyps are read only on the
  -- window, but Lean needs total lambdas; supply them by clamping the time argument
  -- to the window via `max a' (min σ τ)` — agreement at the actual `s ∈ [a',τ]`).
  intro s ha's hsτ k
  have hsT : s ≤ T := le_trans hsτ hτT
  have hspos : 0 < s := lt_of_lt_of_le ha' ha's
  rw [patchedSource_eq_of_pos p u₀ u hspos k]
  have hbsum_s := hbsum s hspos hsT
  have hagree_s := hagree s hspos hsT
  have hpos_s := hpost s hspos hsT
  have hub_s := hubt s hspos hsT
  -- the genuinely-`C²` cosine series for this slice.
  set cs : ℝ → ℝ := fun x => ∑' n, bc s n * cosineMode n x with hcs
  have hG1_s : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (intervalDomainLift (u s)) x| ≤ G1 :=
    hG1 s ⟨ha's, hsτ⟩
  have hG2_s : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (intervalDomainLift (u s))) x| ≤ G2 :=
    hG2 s ⟨ha's, hsτ⟩
  have hcsC2 : ContDiff ℝ 2 cs :=
    ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two hbsum_s
  have hcs_d_cont : Continuous (deriv cs) := hcsC2.continuous_deriv (by norm_num)
  have hcs_dd_cont : Continuous (deriv (deriv cs)) := by
    have h2 : ContDiff ℝ (1 + 1) cs := by simpa using hcsC2
    exact ((contDiff_succ_iff_deriv.mp h2).2.2).continuous_deriv le_rfl
  have hpos_cs : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < cs x := by
    intro x hx; rw [← hagree_s hx]; exact hpos_s x hx
  have hub_cs : ∀ x ∈ Set.Icc (0 : ℝ) 1, cs x ≤ Msup := by
    intro x hx; rw [← hagree_s hx]; exact hub_s x hx
  have hG1_cs : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv cs x| ≤ G1 := by
    refine ShenWork.IntervalDomainLimitSourceRepresentation.le_on_Icc_of_le_on_Ioo
      hcs_d_cont.abs (fun x hx => ?_)
    have hloc : intervalDomainLift (u s) =ᶠ[nhds x] cs := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hagree_s (Set.Ioo_subset_Icc_self hy)
    rw [← hloc.deriv_eq]
    exact hG1_s x (Set.Ioo_subset_Icc_self hx)
  have hG2_cs : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv cs) x| ≤ G2 := by
    refine ShenWork.IntervalDomainLimitSourceRepresentation.le_on_Icc_of_le_on_Ioo
      hcs_dd_cont.abs (fun x hx => ?_)
    have hloc : intervalDomainLift (u s) =ᶠ[nhds x] cs := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hagree_s (Set.Ioo_subset_Icc_self hy)
    have hloc' : deriv (intervalDomainLift (u s)) =ᶠ[nhds x] deriv cs := hloc.deriv
    rw [← hloc'.deriv_eq]
    exact hG2_s x (Set.Ioo_subset_Icc_self hx)
  have hN0_cs : deriv cs 0 = 0 :=
    ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_deriv_at_zero hbsum_s
  have hN1_cs : deriv cs 1 = 0 :=
    ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_deriv_at_one hbsum_s
  have hG1nn : 0 ≤ G1 := le_trans (abs_nonneg _) (hG1_s 0 (by constructor <;> norm_num))
  have hG2nn : 0 ≤ G2 := le_trans (abs_nonneg _) (hG2_s 0 (by constructor <;> norm_num))
  have hMnn : 0 ≤ Msup := by
    have h1 := hub_s 0 (by constructor <;> norm_num)
    have h2 := hpos_s 0 (by constructor <;> norm_num)
    linarith
  have hαpos : 0 < p.α := lt_of_lt_of_le one_pos hα
  set C : ℝ := max (2 * B_log p.a p.b p.α Msup G1 G2) (Msup * (p.a + p.b * Msup ^ p.α))
    with hCdef
  have hBnn : 0 ≤ B_log p.a p.b p.α Msup G1 G2 :=
    ShenWork.IntervalLogisticSourceQuantBound.B_log_nonneg hα ha hb hMnn hG1nn hG2nn
  have hsrc_eq : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      logisticSourceFun p.a p.b p.α (intervalDomainLift (u s)) x
        = logisticSourceFun p.a p.b p.α cs x := by
    intro x hx; simp only [logisticSourceFun]; rw [hagree_s hx]
  have hcoeff_eq : cosineCoeffs (logisticLifted p (u s)) k
      = cosineCoeffs (logisticSourceFun p.a p.b p.α (intervalDomainLift (u s))) k :=
    cosineCoeffs_congr_on_Icc (logisticLifted_eq_logisticSourceFun_on_Icc p (u s)) k
  rw [hcoeff_eq]
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    simp only [windowEnv]
    rw [cosineCoeffs_congr_on_Icc hsrc_eq 0]
    have hsup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |logisticSourceFun p.a p.b p.α cs x| ≤ Msup * (p.a + p.b * Msup ^ p.α) :=
      logisticSourceFun_abs_le_of_bound (B := Msup) hMnn hαpos ha hb
        (fun x hx => by rw [abs_of_pos (hpos_cs x hx)]; exact hub_cs x hx) hpos_cs
    have hgc : Continuous cs := hcsC2.continuous
    have hcont : ContinuousOn (logisticSourceFun p.a p.b p.α cs) (Set.Icc (0 : ℝ) 1) := by
      have hpos' : ∀ x, x ∈ Set.Icc (0:ℝ) 1 → cs x ≠ 0 :=
        fun x hx => ne_of_gt (hpos_cs x hx)
      unfold logisticSourceFun
      apply ContinuousOn.mul hgc.continuousOn
      apply ContinuousOn.sub continuousOn_const
      apply ContinuousOn.mul continuousOn_const
      exact ContinuousOn.rpow_const hgc.continuousOn (fun x hx => Or.inl (hpos' x hx))
    have hMa_nn : 0 ≤ Msup * (p.a + p.b * Msup ^ p.α) := by positivity
    exact le_trans
      (ShenWork.IntervalMildPicardRegularity.cosineCoeffs_zero_abs_le_of_bound
        hMa_nn hcont hsup) (le_max_right _ _)
  · have hk1 : 1 ≤ k := hkpos
    have hkne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hkpos
    simp only [windowEnv, if_neg hkne]
    rw [cosineCoeffs_congr_on_Icc hsrc_eq k]
    have hden : 0 < ((k : ℝ) * Real.pi) ^ 2 := by
      have hkpos' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
      positivity
    refine le_trans
      (logisticSourceFun_cosineCoeff_quadratic_decay_explicit
        hcsC2 hα ha hb hpos_cs hub_cs hG1_cs hG2_cs hN0_cs hN1_cs k hk1)
      ?_
    gcongr
    exact le_max_left _ _

/-! ## 2. The producer. -/

/-- **Horizon-generic `DuhamelSourceBddOn` producer for the patched source family.**

Same body as `IntervalPicardLimitBddProducer.duhamelSourceBddOn_of_mildData`, but over
a bare slice family `u` and horizon `T` (no `GradientMildSolutionData`), with the slice
data taken in the `T`-bounded form the tower carriers genuinely supply.  The iterate
instantiation is `u := picardIter p u₀ n`, `T := the tower horizon`. -/
noncomputable def duhamelSourceBddOn_of_slices
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    {T : ℝ}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    -- s ≤ 0 branch: bound on the initial-datum source coefficients
    {M₀' : ℝ} (hM₀'_nonneg : 0 ≤ M₀')
    (hu₀_src_bound : ∀ k, |cosineCoeffs (logisticLifted p u₀) k| ≤ M₀')
    -- per-slice cosine representation + K2 sup (T-bounded, the tower form)
    {Msup : ℝ}
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ ≤ T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ ≤ T → Set.EqOn (intervalDomainLift (u σ))
        (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpost : ∀ σ, 0 < σ → σ ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u σ) x)
    (hubt : ∀ σ, 0 < σ → σ ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u σ) x ≤ Msup)
    -- K2 gradient/Hessian bounds, PER-COMPACT (within (0,T])
    (hG1t : ∀ a' b', 0 < a' → b' ≤ T → ∃ G1, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (intervalDomainLift (u σ)) x| ≤ G1)
    (hG2t : ∀ a' b', 0 < a' → b' ≤ T → ∃ G2, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2)
    -- time continuity of the patched coefficient family
    {τ : ℝ} (_hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hcontP : ∀ k, ContinuousOn
      (fun s => patchedSource p u₀ u s k) (Set.Icc 0 τ)) :
    DuhamelSourceBddOn (patchedSource p u₀ u) τ where
  M := max M₀' (2 * (Msup * (p.a + p.b * Msup ^ p.α)))
  hM_nonneg := le_trans hM₀'_nonneg (le_max_left _ _)
  hM := by
    intro s hs hsτ k
    have hsT : s ≤ T := le_trans hsτ hτT
    rcases eq_or_lt_of_le hs with hs0 | hspos
    · -- s = 0: patched value is the initial-datum source.
      simp only [patchedSource, ← hs0, le_refl, if_pos]
      exact le_trans (hu₀_src_bound k) (le_max_left _ _)
    · -- s > 0: slice sup bound through the source-fun coefficient bound.
      rw [patchedSource_eq_of_pos p u₀ u hspos k]
      have hMnn : 0 ≤ Msup := by
        have h1 := hubt s hspos hsT 0 (by constructor <;> norm_num)
        have h2 := hpost s hspos hsT 0 (by constructor <;> norm_num)
        linarith
      have hαpos : 0 < p.α := lt_of_lt_of_le one_pos hα
      have hcoeff_eq : cosineCoeffs (logisticLifted p (u s)) k
          = cosineCoeffs (logisticSourceFun p.a p.b p.α (intervalDomainLift (u s))) k :=
        cosineCoeffs_congr_on_Icc (logisticLifted_eq_logisticSourceFun_on_Icc p (u s)) k
      rw [hcoeff_eq]
      have hbd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
          |logisticSourceFun p.a p.b p.α (intervalDomainLift (u s)) x|
            ≤ Msup * (p.a + p.b * Msup ^ p.α) :=
        logisticSourceFun_abs_le_of_bound (B := Msup) hMnn hαpos ha hb
          (fun x hx => by rw [abs_of_pos (hpost s hspos hsT x hx)]; exact hubt s hspos hsT x hx)
          (fun x hx => hpost s hspos hsT x hx)
      have hcont : ContinuousOn
          (logisticSourceFun p.a p.b p.α (intervalDomainLift (u s))) (Set.Icc (0 : ℝ) 1) := by
        have hgc : ContinuousOn (intervalDomainLift (u s)) (Set.Icc (0:ℝ) 1) := by
          have hcg : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u s) x
              = (fun x => ∑' n, bc s n * cosineMode n x) x :=
            fun x hx => hagree s hspos hsT hx
          refine ContinuousOn.congr ?_ hcg
          exact (ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two
            (hbsum s hspos hsT)).continuous.continuousOn
        have hpos' : ∀ x, x ∈ Set.Icc (0:ℝ) 1 → intervalDomainLift (u s) x ≠ 0 :=
          fun x hx => ne_of_gt (hpost s hspos hsT x hx)
        unfold logisticSourceFun
        apply ContinuousOn.mul hgc
        apply ContinuousOn.sub continuousOn_const
        apply ContinuousOn.mul continuousOn_const
        exact ContinuousOn.rpow_const hgc (fun x hx => Or.inl (hpos' x hx))
      have hMa_nn : 0 ≤ Msup * (p.a + p.b * Msup ^ p.α) := by positivity
      exact le_trans
        (cosineCoeffs_abs_le_of_continuous_bounded hcont hMa_nn hbd k)
        (le_max_right _ _)
  hcont := hcontP
  env := fun a' =>
    if ha' : 0 < a' then
      windowEnv (max (2 * B_log p.a p.b p.α Msup
        (Classical.choose (hG1t a' τ ha' hτT))
        (Classical.choose (hG2t a' τ ha' hτT)))
        (Msup * (p.a + p.b * Msup ^ p.α)))
    else fun _ => 0
  henv_summable := by
    intro a' ha' _
    rw [dif_pos ha']
    exact windowEnv_summable
  henv_bound := by
    intro a' ha' s ha's hsτ k
    rw [dif_pos ha']
    have hspecG1 := Classical.choose_spec (hG1t a' τ ha' hτT)
    have hspecG2 := Classical.choose_spec (hG2t a' τ ha' hτT)
    exact patchedSource_windowEnv_bound_on p u hα ha hb bc hbsum hagree hpost hubt
      ha' hτT hspecG1 hspecG2 s ha's hsτ k

end ShenWork.IntervalPicardIterateBddProducer
