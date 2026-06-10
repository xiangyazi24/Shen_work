/-
  ShenWork/Paper2/IntervalPicardLimitBddProducer.lean

  **Producer for `DuhamelSourceBddOn` of the canonical limit-source family.**

  `IntervalPicardLimitRestartBdd` introduced the satisfiable engine-facing package
  `DuhamelSourceBddOn a τ` (constant k-uniform bound `M` on `[0, τ]` + per-compact
  decaying envelopes `env a'` valid on `[a', τ]`, `a' > 0`) as the replacement for
  the unsatisfiable global summable envelope of `DuhamelSourceL1ContOn`.  This file
  PRODUCES such a package for the canonical logistic-source coefficient family of a
  `GradientMildSolutionData`.

  ## The s = 0 obstruction and the patched family

  The structure quantifies `hM`/`hcont` over the CLOSED horizon `[0, τ]`, including
  `s = 0`.  For a `GradientMildSolutionData D`, the slice `D.u 0` is UNCONSTRAINED
  (`D.hbound`/`D.hpos` only cover `0 < t`), so the canonical family
  `s ↦ coeffs (logisticLifted p (D.u s))` has no a-priori bound at `s = 0`.  The
  design (`HANDOFF/hsrc0-splitenv-design.md`, ChatGPT cron verdict) resolves this by
  the PATCHED family

      `aP s k := if s ≤ 0 then coeffs (logisticLifted p u₀) k
                 else coeffs (logisticLifted p (D.u s)) k`,

  whose value at every `s ≤ 0` is the (bounded, `M₀'`-controlled) initial-datum
  source and which agrees with the canonical family on `(0, τ]`.  Consumers patch
  back to the canonical family by an `Ioo`-congruence adapter — that adapter pass is
  SEPARATE from this producer (the measure-invisible point `s = 0` only enters
  through interval integrals).

  ## The three ingredients

  1. **Constant bound `M`** on `[0, τ]`: on `(0, τ]` from the slice sup bound
     `hubt` through `logisticSourceFun_abs_le_of_bound` +
     `cosineCoeffs_abs_le_of_continuous_bounded` (`2·Msup·(a + b·Msup^α)`); at
     `s ≤ 0` from the supplied `M₀'`-bound on the initial-datum source coefficients.
  2. **Per-compact envelope `env a'`** on `[a', τ]`: the explicit quadratic-decay
     constant `C(a') = max (2·B_log Msup G1 G2) (Msup·(a + b·Msup^α))` assembled
     exactly as `IntervalDomainLimitSourceRepresentation.limitSource_..._of_representation`
     does (per-slice cosine representation `bc`/`hbsum`/`hagree` is genuinely `C²`;
     `K2` per-compact `hG1t a' τ`/`hG2t a' τ` give the window-uniform `G1`/`G2`),
     yielding `|coeff k| ≤ C(a')/(kπ)²` for `k ≥ 1` and `|coeff 0| ≤ C(a')`; summable
     by `∑ 1/k²`.
  3. **Time continuity `hcont`** on `[0, τ]`: NAMED SATISFIABLE — carried as a
     hypothesis exactly as the rest of the codebase does (e.g.
     `IntervalPicardLimitRestartWeak.limitSource_l1cont`'s `hcont` field).

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.Paper2.IntervalPicardLimitRestartBdd
import ShenWork.Paper2.IntervalDomainLimitSourceRepresentation
import ShenWork.Paper2.IntervalMildPicard

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
  (B_log B_log_nonneg logisticSourceFun_cosineCoeff_quadratic_decay_explicit)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)

noncomputable section

namespace ShenWork.IntervalPicardLimitBddProducer

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-- The patched canonical limit-source family: the initial-datum source at `s ≤ 0`,
the slice source for `s > 0`.  Agrees with `s ↦ coeffs (logisticLifted p (D.u s))`
on `(0, ∞)`. -/
def patchedSource (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ) (k : ℕ) : ℝ :=
  if s ≤ 0 then cosineCoeffs (logisticLifted p u₀) k
  else cosineCoeffs (logisticLifted p (u s)) k

/-- On `(0, ∞)` the patched family equals the canonical one. -/
theorem patchedSource_eq_of_pos (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) {s : ℝ} (hs : 0 < s) (k : ℕ) :
    patchedSource p u₀ u s k = cosineCoeffs (logisticLifted p (u s)) k := by
  simp [patchedSource, not_le.mpr hs]

/-! ## The per-window quadratic-decay envelope.

For a window `[a', τ] ⋐ (0, T)` the per-compact `K2` data gives window-uniform
gradient/Hessian bounds `G1`/`G2`; with the global sup bound `Msup` they feed the
explicit constant `C = max (2·B_log Msup G1 G2) (Msup·(a + b·Msup^α))` and the
quadratic decay `|coeff k| ≤ C/(kπ)²` (`k ≥ 1`), `|coeff 0| ≤ C`. -/

/-- The window envelope value: `C` at `k = 0`, `C/(kπ)²` for `k ≥ 1`. -/
def windowEnv (C : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then C else C / ((k : ℝ) * Real.pi) ^ 2

theorem windowEnv_summable {C : ℝ} : Summable (windowEnv C) := by
  -- tail comparison with `∑ C/((k+1)π)²`, then re-add the head.
  have htail : Summable (fun k : ℕ => windowEnv C (k + 1)) := by
    have hbase : Summable (fun k : ℕ => C * (1 / Real.pi ^ 2) * (1 / ((k : ℝ) + 1) ^ 2)) := by
      have hp2 : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
        have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
        simpa using (summable_nat_add_iff (f := fun k : ℕ => 1 / (k : ℝ) ^ 2) 1).2 this
      exact hp2.mul_left (C * (1 / Real.pi ^ 2))
    refine hbase.congr (fun k => ?_)
    simp only [windowEnv, Nat.succ_ne_zero, if_false]
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    push_cast
    field_simp
  exact (summable_nat_add_iff (f := windowEnv C) 1).mp htail

/-- **Per-window envelope bound for the patched family.**

On the window `[a', τ]` (with `0 < a'`, `τ < T`) the patched family's coefficients
are dominated by `windowEnv C` for the explicit window constant `C`.  The proof is
the quadratic-decay assembly of
`IntervalDomainLimitSourceRepresentation.limitSource_duhamelSourceTimeC1_of_representation`,
specialized to the single window. -/
theorem patchedSource_windowEnv_bound
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (u : ℝ → intervalDomainPoint → ℝ)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {Msup : ℝ}
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → Set.EqOn (intervalDomainLift (u σ))
        (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpost : ∀ σ, 0 < σ → ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u σ) x)
    (hubt : ∀ σ, 0 < σ → ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u σ) x ≤ Msup)
    {a' τ : ℝ} (ha' : 0 < a') {G1 G2 : ℝ}
    (hG1 : ∀ σ ∈ Set.Icc a' τ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (u σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Set.Icc a' τ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2) :
    ∀ s, a' ≤ s → s ≤ τ → ∀ k,
      |patchedSource p u₀ u s k|
        ≤ windowEnv (max (2 * B_log p.a p.b p.α Msup G1 G2)
            (Msup * (p.a + p.b * Msup ^ p.α))) k := by
  intro s ha's hsτ k
  have hspos : 0 < s := lt_of_lt_of_le ha' ha's
  rw [patchedSource_eq_of_pos p u₀ u hspos k]
  -- specialize the slice data to this window's slice `s`.
  have hbsum_s := hbsum s hspos
  have hagree_s := hagree s hspos
  have hpos_s := hpost s hspos
  have hub_s := hubt s hspos
  have hG1_s : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (intervalDomainLift (u s)) x| ≤ G1 :=
    hG1 s ⟨ha's, hsτ⟩
  have hG2_s : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (intervalDomainLift (u s))) x| ≤ G2 :=
    hG2 s ⟨ha's, hsτ⟩
  -- the genuinely-`C²` cosine series for this slice.
  set cs : ℝ → ℝ := fun x => ∑' n, bc s n * cosineMode n x with hcs
  have hcsC2 : ContDiff ℝ 2 cs :=
    ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two hbsum_s
  have hcs_d_cont : Continuous (deriv cs) := hcsC2.continuous_deriv (by norm_num)
  have hcs_dd_cont : Continuous (deriv (deriv cs)) := by
    have h2 : ContDiff ℝ (1 + 1) cs := by simpa using hcsC2
    exact ((contDiff_succ_iff_deriv.mp h2).2.2).continuous_deriv le_rfl
  -- transfer of `K2` data to the series (pointwise agreement on `[0,1]`).
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
  -- bookkeeping constants.
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
  -- the lift's logistic source equals the series' on `[0,1]`.
  have hsrc_eq : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      logisticSourceFun p.a p.b p.α (intervalDomainLift (u s)) x
        = logisticSourceFun p.a p.b p.α cs x := by
    intro x hx; simp only [logisticSourceFun]; rw [hagree_s hx]
  -- the patched coeff (= canonical at s>0) equals the source-fun coeff.
  have hcoeff_eq : cosineCoeffs (logisticLifted p (u s)) k
      = cosineCoeffs (logisticSourceFun p.a p.b p.α (intervalDomainLift (u s))) k :=
    cosineCoeffs_congr_on_Icc (logisticLifted_eq_logisticSourceFun_on_Icc p (u s)) k
  rw [hcoeff_eq]
  -- split on k = 0 vs k ≥ 1.
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- k = 0: `windowEnv C 0 = C`, and the zeroth coeff is bounded by `Msup·(a+b·Msup^α) ≤ C`.
    subst hk0
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
  · -- k ≥ 1: quadratic decay `≤ 2·B_log/(kπ)² ≤ C/(kπ)²`.
    have hk1 : 1 ≤ k := hkpos
    have hkne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hkpos
    simp only [windowEnv, if_neg hkne]
    rw [cosineCoeffs_congr_on_Icc hsrc_eq k]
    have hden : 0 < ((k : ℝ) * Real.pi) ^ 2 := by
      have hkpos' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
      positivity
    refine le_trans
      (logisticSourceFun_cosineCoeff_quadratic_decay_explicit hcsC2 hα ha hb
        hpos_cs hub_cs hG1_cs hG2_cs hN0_cs hN1_cs k hk1) ?_
    gcongr
    exact le_max_left _ _

/-! ## The producer. -/

/-- **`DuhamelSourceBddOn` producer for the patched canonical limit-source family.**

Assembles the satisfiable bounded-source package on a window `[0, τ]`, `0 < τ < D.T`,
for the PATCHED family `patchedSource p u₀ D.u` (canonical on `(0, τ]`, initial-datum
source at `s = 0`).  The three ingredients:

* `hM` — constant bound from the slice sup bound `hubt` on `(0, τ]` and the supplied
  initial-source bound `M₀'` at `s ≤ 0`;
* `env` — the per-compact quadratic-decay envelopes from the per-slice cosine
  representation (`bc`/`hbsum`/`hagree`) + the per-compact `K2` gradient/Hessian
  bounds `hG1t`/`hG2t` (V2 ledger shapes);
* `hcont` — NAMED SATISFIABLE: carried as a hypothesis exactly as
  `IntervalPicardLimitRestartWeak.limitSource_l1cont` does.

(The `0 < τ < D.T` restriction keeps the window away from the `T`-endpoint data gap;
consumers at target `t < T` instantiate `τ := (t + T)/2`.) -/
noncomputable def duhamelSourceBddOn_of_mildData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    -- s ≤ 0 branch: bound on the initial-datum source coefficients
    {M₀' : ℝ} (hM₀'_nonneg : 0 ≤ M₀')
    (hu₀_src_bound : ∀ k, |cosineCoeffs (logisticLifted p u₀) k| ≤ M₀')
    -- per-slice cosine representation + K2 sup (V2 ledger shapes, localized to (0,T))
    {Msup : ℝ}
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → Set.EqOn (intervalDomainLift (D.u σ))
        (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpost : ∀ σ, 0 < σ → ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (D.u σ) x)
    (hubt : ∀ σ, 0 < σ → ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (D.u σ) x ≤ Msup)
    -- K2 gradient/Hessian bounds, PER-COMPACT (V2 ledger shapes)
    (hG1t : ∀ a' b', 0 < a' → b' < D.T → ∃ G1, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (intervalDomainLift (D.u σ)) x| ≤ G1)
    (hG2t : ∀ a' b', 0 < a' → b' < D.T → ∃ G2, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (intervalDomainLift (D.u σ))) x| ≤ G2)
    -- time continuity of the patched coefficient family (NAMED SATISFIABLE)
    {τ : ℝ} (_hτ0 : 0 < τ) (hτT : τ < D.T)
    (hcontP : ∀ k, ContinuousOn
      (fun s => patchedSource p u₀ D.u s k) (Set.Icc 0 τ)) :
    DuhamelSourceBddOn (patchedSource p u₀ D.u) τ where
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
        have h1 := hubt s hspos 0 (by constructor <;> norm_num)
        have h2 := hpost s hspos 0 (by constructor <;> norm_num)
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
          (fun x hx => by rw [abs_of_pos (hpost s hspos x hx)]; exact hubt s hspos x hx)
          (fun x hx => hpost s hspos x hx)
      have hcont : ContinuousOn
          (logisticSourceFun p.a p.b p.α (intervalDomainLift (D.u s))) (Set.Icc (0 : ℝ) 1) := by
        have hgc : ContinuousOn (intervalDomainLift (D.u s)) (Set.Icc (0:ℝ) 1) := by
          have hcg : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (D.u s) x
              = (fun x => ∑' n, bc s n * cosineMode n x) x :=
            fun x hx => hagree s hspos hx
          refine ContinuousOn.congr ?_ hcg
          exact (ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two
            (hbsum s hspos)).continuous.continuousOn
        have hpos' : ∀ x, x ∈ Set.Icc (0:ℝ) 1 → intervalDomainLift (D.u s) x ≠ 0 :=
          fun x hx => ne_of_gt (hpost s hspos x hx)
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
    -- extract the window-uniform G1, G2 for this window `[a', τ]`.
    have hspecG1 := Classical.choose_spec (hG1t a' τ ha' hτT)
    have hspecG2 := Classical.choose_spec (hG2t a' τ ha' hτT)
    exact patchedSource_windowEnv_bound p D.u hα ha hb bc hbsum hagree hpost hubt
      ha' hspecG1 hspecG2 s ha's hsτ k

end ShenWork.IntervalPicardLimitBddProducer
