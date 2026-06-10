/-
  ShenWork/Paper2/IntervalPicardLimitBddProducerInclusive.lean

  **Inclusive-horizon variant of the `DuhamelSourceBddOn` producer.**

  `IntervalPicardLimitBddProducer.duhamelSourceBddOn_of_mildData` builds the
  satisfiable bounded-source package `DuhamelSourceBddOn (patchedSource …) τ` for a
  STRICT window `0 < τ < D.T` — its per-compact K2 hypotheses `hG1t`/`hG2t` produce
  on `[a', b']` for `b' < T`, and the resulting envelope is valid only on `[a', τ]`.

  The χ₀ = 0 Provider (`IntervalDomainThm11ChiZeroCoreProvider`) needs the package at
  the EXACT horizon `τ = D.T`.  Tonight's commit made the Provider-side data
  `≤T`-INCLUSIVE (`hagreeF`/`hbsumF`/`hpostF`/`hubtF` quantify `∀ σ, 0 < σ → σ ≤ D.T`
  and `hG1tF`/`hG2tF` produce on `[a', b']` for `b' ≤ D.T`), so the only thing missing
  is a producer whose horizon is the closed `D.T` rather than a strict interior `τ`.

  This file provides exactly that: `duhamelSourceBddOn_of_mildData_inclusive` clones
  the strict producer with every `τ`-window hypothesis retyped from strict (`< D.T`)
  to inclusive (`≤ D.T`).  The three ingredients are:

  * `hM` — constant bound on `[0, D.T]` (incl. endpoints): `s ≤ 0` from the
    `M₀'`-controlled initial-datum source, `0 < s ≤ D.T` from the ≤T-inclusive sup
    data (`hubtF` shape) through `logisticSourceFun_abs_le_of_bound` +
    `cosineCoeffs_abs_le_of_continuous_bounded`.  Identical to the strict producer's
    `hM` block — `s` only ever appears with `0 ≤ s` and `s ≤ D.T`, never `< D.T`.

  * `env a'` — per-compact quadratic-decay envelope on `[a', D.T]` (INCLUSIVE of the
    `D.T` endpoint): `windowEnv C(a')` where `C(a')` comes from window-uniform
    gradient/Hessian bounds `G1`/`G2` on `Set.Icc a' D.T` (inclusive).  The strict
    producer's `patchedSource_windowEnv_bound` ALREADY takes `hG1`/`hG2` over the
    closed `Set.Icc a' τ`; we simply instantiate `τ := D.T`.  The window-uniform
    `G1`/`G2` on `[a', D.T]` are taken as the inclusive per-compact K2 hypotheses
    `hG1t`/`hG2t` (`∀ a' b', 0 < a' → b' ≤ D.T → ∃ G, …`) — the Provider produces
    them from the ≤-capable `BddAdapterPatched.deriv_lift_bound_on_compact_patched`
    (`hb'τ : b' ≤ τ`), which is INDEPENDENT of the env being built here.

  * `hcont` — NAMED SATISFIABLE, carried as a hypothesis exactly as the strict
    producer does.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalPicardLimitBddProducer

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalPicardLimitRestartBdd (DuhamelSourceBddOn)
open ShenWork.IntervalMildPicardRegularity
  (logisticSourceFun logisticLifted_eq_logisticSourceFun_on_Icc
   cosineCoeffs_abs_le_of_continuous_bounded
   cosineCoeffs_zero_abs_le_of_bound logisticSourceFun_abs_le_of_bound)
open ShenWork.IntervalLogisticSourceQuantBound
  (B_log B_log_nonneg)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)
open ShenWork.IntervalPicardLimitBddProducer
  (patchedSource patchedSource_eq_of_pos windowEnv windowEnv_summable
   patchedSource_windowEnv_bound)

noncomputable section

namespace ShenWork.IntervalPicardLimitBddProducer

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-- **Per-window envelope bound — INCLUSIVE slice-data variant.**

Identical to `patchedSource_windowEnv_bound`, but the per-slice cosine-representation
data (`hbsum`/`hagree`/`hpost`/`hubt`) is localized to the WINDOW slices
`σ ∈ Set.Icc a' τ` rather than quantified over all `0 < σ`.  This is what the
inclusive producer can supply at the closed horizon `τ = D.T`, where the slice data
is `≤ D.T`-bounded (never globally `∀ σ`).  The proof is the strict lemma's, applied
at the single window slice `s` (which satisfies `a' ≤ s ≤ τ`, hence `s ∈ Set.Icc a' τ`
and `0 < s`). -/
theorem patchedSource_windowEnv_bound_inclusive
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (u : ℝ → intervalDomainPoint → ℝ)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {Msup : ℝ}
    (bc : ℝ → ℕ → ℝ)
    {a' τ : ℝ} (ha' : 0 < a')
    (hbsum : ∀ σ ∈ Set.Icc a' τ,
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ ∈ Set.Icc a' τ, Set.EqOn (intervalDomainLift (u σ))
        (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpost : ∀ σ ∈ Set.Icc a' τ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (u σ) x)
    (hubt : ∀ σ ∈ Set.Icc a' τ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u σ) x ≤ Msup)
    {G1 G2 : ℝ}
    (hG1 : ∀ σ ∈ Set.Icc a' τ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (u σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Set.Icc a' τ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2) :
    ∀ s, a' ≤ s → s ≤ τ → ∀ k,
      |patchedSource p u₀ u s k|
        ≤ windowEnv (max (2 * B_log p.a p.b p.α Msup G1 G2)
            (Msup * (p.a + p.b * Msup ^ p.α))) k := by
  intro s ha's hsτ k
  have hsmem : s ∈ Set.Icc a' τ := ⟨ha's, hsτ⟩
  have hspos : 0 < s := lt_of_lt_of_le ha' ha's
  -- specialize the slice data to this window's slice `s`.
  have hbsum_s := hbsum s hsmem
  have hagree_s := hagree s hsmem
  have hpos_s := hpost s hsmem
  have hub_s := hubt s hsmem
  have hG1_s : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (intervalDomainLift (u s)) x| ≤ G1 :=
    hG1 s hsmem
  have hG2_s : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (intervalDomainLift (u s))) x| ≤ G2 :=
    hG2 s hsmem
  rw [patchedSource_eq_of_pos p u₀ u hspos k]
  -- the genuinely-`C²` cosine series for this slice.
  set cs : ℝ → ℝ := fun x => ∑' n, bc s n * cosineMode n x with hcs
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
  have hBnn : 0 ≤ B_log p.a p.b p.α Msup G1 G2 := B_log_nonneg hα ha hb hMnn hG1nn hG2nn
  have hCnn : 0 ≤ C :=
    le_trans (by linarith : (0:ℝ) ≤ 2 * B_log p.a p.b p.α Msup G1 G2) (le_max_left _ _)
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
    exact le_trans (cosineCoeffs_zero_abs_le_of_bound hMa_nn hcont hsup) (le_max_right _ _)
  · have hk1 : 1 ≤ k := hkpos
    have hkne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hkpos
    simp only [windowEnv, if_neg hkne]
    rw [cosineCoeffs_congr_on_Icc hsrc_eq k]
    have hden : 0 < ((k : ℝ) * Real.pi) ^ 2 := by
      have hkpos' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
      positivity
    have hquad :=
      ShenWork.IntervalLogisticSourceQuantBound.logisticSourceFun_cosineCoeff_quadratic_decay_explicit
        hcsC2 hα ha hb hpos_cs hub_cs hG1_cs hG2_cs hN0_cs hN1_cs k hk1
    refine le_trans hquad ?_
    gcongr
    exact le_max_left _ _

/-- **`DuhamelSourceBddOn` producer at the CLOSED horizon `τ = D.T` (INCLUSIVE).**

The inclusive-horizon clone of `duhamelSourceBddOn_of_mildData`.  Every window
hypothesis is retyped from strict (`< D.T`) to inclusive (`≤ D.T`): the slice
representation/positivity/sup data (`bc`/`hbsum`/`hagree`/`hpost`/`hubt`) quantify
`∀ σ, 0 < σ → σ ≤ D.T`, and the per-compact K2 gradient/Hessian producers
(`hG1t`/`hG2t`) produce on `[a', b']` for `b' ≤ D.T`.

The three ingredients are assembled exactly as in the strict producer:

* `hM` (constant bound on `[0, D.T]`): `s ≤ 0` from `M₀'`, `0 < s ≤ D.T` from the
  inclusive sup bound `hubt`.
* `env a'` (per-compact quadratic-decay envelope on the CLOSED `[a', D.T]`):
  `windowEnv (C a')` for `C a'` assembled from the inclusive K2 bounds via
  `patchedSource_windowEnv_bound` instantiated at `τ := D.T` (its `hG1`/`hG2`
  hypotheses are on the CLOSED `Set.Icc a' D.T`, so the `D.T` endpoint is included).
* `hcont` — NAMED SATISFIABLE hypothesis. -/
noncomputable def duhamelSourceBddOn_of_mildData_inclusive
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    -- s ≤ 0 branch: bound on the initial-datum source coefficients
    {M₀' : ℝ} (hM₀'_nonneg : 0 ≤ M₀')
    (hu₀_src_bound : ∀ k, |cosineCoeffs (logisticLifted p u₀) k| ≤ M₀')
    -- per-slice cosine representation + K2 sup (INCLUSIVE: σ ≤ D.T)
    {Msup : ℝ}
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ ≤ D.T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ ≤ D.T → Set.EqOn (intervalDomainLift (D.u σ))
        (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpost : ∀ σ, 0 < σ → σ ≤ D.T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (D.u σ) x)
    (hubt : ∀ σ, 0 < σ → σ ≤ D.T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (D.u σ) x ≤ Msup)
    -- K2 gradient/Hessian bounds, PER-COMPACT, INCLUSIVE (b' ≤ D.T)
    (hG1t : ∀ a' b', 0 < a' → b' ≤ D.T → ∃ G1, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (intervalDomainLift (D.u σ)) x| ≤ G1)
    (hG2t : ∀ a' b', 0 < a' → b' ≤ D.T → ∃ G2, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (intervalDomainLift (D.u σ))) x| ≤ G2)
    -- time continuity of the patched coefficient family (NAMED SATISFIABLE)
    (hcontP : ∀ k, ContinuousOn
      (fun s => patchedSource p u₀ D.u s k) (Set.Icc 0 D.T)) :
    DuhamelSourceBddOn (patchedSource p u₀ D.u) D.T where
  M := max M₀' (2 * (Msup * (p.a + p.b * Msup ^ p.α)))
  hM_nonneg := le_trans hM₀'_nonneg (le_max_left _ _)
  hM := by
    intro s hs hsτ k
    rcases eq_or_lt_of_le hs with hs0 | hspos
    · -- s = 0: patched value is the initial-datum source.
      simp only [patchedSource, ← hs0, le_refl, if_pos]
      exact le_trans (hu₀_src_bound k) (le_max_left _ _)
    · -- s > 0: slice sup bound through the source-fun coefficient bound.
      rw [patchedSource_eq_of_pos p u₀ D.u hspos k]
      have hMnn : 0 ≤ Msup := by
        have h1 := hubt s hspos hsτ 0 (by constructor <;> norm_num)
        have h2 := hpost s hspos hsτ 0 (by constructor <;> norm_num)
        linarith
      have hαpos : 0 < p.α := lt_of_lt_of_le one_pos hα
      have hcoeff_eq : cosineCoeffs (logisticLifted p (D.u s)) k
          = cosineCoeffs (logisticSourceFun p.a p.b p.α (intervalDomainLift (D.u s))) k :=
        cosineCoeffs_congr_on_Icc (logisticLifted_eq_logisticSourceFun_on_Icc p (D.u s)) k
      rw [hcoeff_eq]
      have hbd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
          |logisticSourceFun p.a p.b p.α (intervalDomainLift (D.u s)) x|
            ≤ Msup * (p.a + p.b * Msup ^ p.α) :=
        logisticSourceFun_abs_le_of_bound (B := Msup) hMnn hαpos ha hb
          (fun x hx => by rw [abs_of_pos (hpost s hspos hsτ x hx)]; exact hubt s hspos hsτ x hx)
          (fun x hx => hpost s hspos hsτ x hx)
      have hcont : ContinuousOn
          (logisticSourceFun p.a p.b p.α (intervalDomainLift (D.u s))) (Set.Icc (0 : ℝ) 1) := by
        have hgc : ContinuousOn (intervalDomainLift (D.u s)) (Set.Icc (0:ℝ) 1) := by
          have hcg : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (D.u s) x
              = (fun x => ∑' n, bc s n * cosineMode n x) x :=
            fun x hx => hagree s hspos hsτ hx
          refine ContinuousOn.congr ?_ hcg
          exact (ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two
            (hbsum s hspos hsτ)).continuous.continuousOn
        have hpos' : ∀ x, x ∈ Set.Icc (0:ℝ) 1 → intervalDomainLift (D.u s) x ≠ 0 :=
          fun x hx => ne_of_gt (hpost s hspos hsτ x hx)
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
        (Classical.choose (hG1t a' D.T ha' le_rfl))
        (Classical.choose (hG2t a' D.T ha' le_rfl)))
        (Msup * (p.a + p.b * Msup ^ p.α)))
    else fun _ => 0
  henv_summable := by
    intro a' ha' _
    rw [dif_pos ha']
    exact windowEnv_summable
  henv_bound := by
    intro a' ha' s ha's hsτ k
    rw [dif_pos ha']
    -- extract the window-uniform G1, G2 for the CLOSED window `[a', D.T]`.
    have hspecG1 := Classical.choose_spec (hG1t a' D.T ha' le_rfl)
    have hspecG2 := Classical.choose_spec (hG2t a' D.T ha' le_rfl)
    -- localize the inclusive slice data to the window `σ ∈ Icc a' D.T`.
    have hpos_of_mem : ∀ σ ∈ Set.Icc a' D.T, 0 < σ :=
      fun σ hσ => lt_of_lt_of_le ha' hσ.1
    exact patchedSource_windowEnv_bound_inclusive p D.u hα ha hb bc ha'
      (fun σ hσ => hbsum σ (hpos_of_mem σ hσ) hσ.2)
      (fun σ hσ => hagree σ (hpos_of_mem σ hσ) hσ.2)
      (fun σ hσ => hpost σ (hpos_of_mem σ hσ) hσ.2)
      (fun σ hσ => hubt σ (hpos_of_mem σ hσ) hσ.2)
      hspecG1 hspecG2 s ha's hsτ k

end ShenWork.IntervalPicardLimitBddProducer
