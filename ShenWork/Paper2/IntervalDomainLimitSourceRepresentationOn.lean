import ShenWork.Paper2.IntervalDomainLimitSourceRepresentation
import ShenWork.PDE.IntervalDuhamelSourceTimeC1On

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicardRegularity
  (logisticSourceFun logisticLifted_eq_logisticSourceFun_on_Icc
   cosineCoeffs_zero_abs_le_of_bound logisticSourceFun_abs_le_of_bound)
open ShenWork.IntervalLogisticSourceQuantBound
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)

noncomputable section

namespace ShenWork.IntervalDomainLimitSourceRepresentationOn

/-- Representation-fed closed-window logistic-source `DuhamelSourceTimeC1On`.

This is the `On` analogue of
`IntervalDomainLimitSourceRepresentation.limitSource_duhamelSourceTimeC1_of_representation`.
The time-derivative and derivative-continuity legs are supplied on the target
window; the spatial representation/K2 facts build the same quadratic-decay
envelope as the global producer, but only for times in `[lo, hi]`. -/
noncomputable def limitSource_duhamelSourceTimeC1On_of_representation
    (p : CM2Params)
    (w : ℝ → intervalDomainPoint → ℝ)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {lo hi M G1 G2 : ℝ}
    (hlohi : lo ≤ hi)
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ ∈ Set.Icc lo hi,
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ ∈ Set.Icc lo hi, Set.EqOn (intervalDomainLift (w σ))
        (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ σ ∈ Set.Icc lo hi,
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (w σ) x)
    (hub : ∀ σ ∈ Set.Icc lo hi,
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (w σ) x ≤ M)
    (hG1 : ∀ σ ∈ Set.Icc lo hi,
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (intervalDomainLift (w σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Set.Icc lo hi,
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (deriv (intervalDomainLift (w σ))) x| ≤ G2)
    (adot : ℝ → ℕ → ℝ)
    (hderiv : ∀ σ ∈ Set.Icc lo hi, ∀ k, HasDerivWithinAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (w r))) k)
      (adot σ k) (Set.Icc lo hi) σ)
    (hadotcont : ∀ k, ContinuousOn (fun σ => adot σ k) (Set.Icc lo hi))
    {Mdot : ℝ}
    (hMdot : ∀ σ ∈ Set.Icc lo hi, ∀ k, |adot σ k| ≤ Mdot) :
    DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (w s)) k) lo hi := by
  classical
  have hcsC2 : ∀ σ ∈ Set.Icc lo hi,
      ContDiff ℝ 2 (fun x => ∑' n, bc σ n * cosineMode n x) :=
    fun σ hσ =>
      ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two
        (hbsum σ hσ)
  have hcs_d_cont : ∀ σ ∈ Set.Icc lo hi,
      Continuous (deriv (fun x => ∑' n, bc σ n * cosineMode n x)) :=
    fun σ hσ => (hcsC2 σ hσ).continuous_deriv (by norm_num)
  have hcs_dd_cont : ∀ σ ∈ Set.Icc lo hi,
      Continuous (deriv (deriv (fun x => ∑' n, bc σ n * cosineMode n x))) := by
    intro σ hσ
    have h2 : ContDiff ℝ (1 + 1) (fun x => ∑' n, bc σ n * cosineMode n x) := by
      simpa using hcsC2 σ hσ
    exact ((contDiff_succ_iff_deriv.mp h2).2.2).continuous_deriv le_rfl
  have hpos_cs : ∀ σ ∈ Set.Icc lo hi,
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        0 < (fun x => ∑' n, bc σ n * cosineMode n x) x := by
    intro σ hσ x hx
    rw [← hagree σ hσ hx]
    exact hpos σ hσ x hx
  have hub_cs : ∀ σ ∈ Set.Icc lo hi,
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        (fun x => ∑' n, bc σ n * cosineMode n x) x ≤ M := by
    intro σ hσ x hx
    rw [← hagree σ hσ hx]
    exact hub σ hσ x hx
  have hG1nn : 0 ≤ G1 := by
    have hlo_mem : lo ∈ Set.Icc lo hi := ⟨le_rfl, hlohi⟩
    exact le_trans (abs_nonneg _) (hG1 lo hlo_mem 0 (by constructor <;> norm_num))
  have hG2nn : 0 ≤ G2 := by
    have hlo_mem : lo ∈ Set.Icc lo hi := ⟨le_rfl, hlohi⟩
    exact le_trans (abs_nonneg _) (hG2 lo hlo_mem 0 (by constructor <;> norm_num))
  have hG1_cs : ∀ σ ∈ Set.Icc lo hi,
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun x => ∑' n, bc σ n * cosineMode n x) x| ≤ G1 := by
    intro σ hσ
    refine ShenWork.IntervalDomainLimitSourceRepresentation.le_on_Icc_of_le_on_Ioo
      (hcs_d_cont σ hσ).abs (fun x hx => ?_)
    have hloc : intervalDomainLift (w σ)
        =ᶠ[nhds x] (fun x => ∑' n, bc σ n * cosineMode n x) := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hagree σ hσ (Set.Ioo_subset_Icc_self hy)
    rw [← hloc.deriv_eq]
    exact hG1 σ hσ x (Set.Ioo_subset_Icc_self hx)
  have hG2_cs : ∀ σ ∈ Set.Icc lo hi,
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (deriv (fun x => ∑' n, bc σ n * cosineMode n x)) x| ≤ G2 := by
    intro σ hσ
    refine ShenWork.IntervalDomainLimitSourceRepresentation.le_on_Icc_of_le_on_Ioo
      (hcs_dd_cont σ hσ).abs (fun x hx => ?_)
    have hloc : intervalDomainLift (w σ)
        =ᶠ[nhds x] (fun x => ∑' n, bc σ n * cosineMode n x) := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hagree σ hσ (Set.Ioo_subset_Icc_self hy)
    have hloc' : deriv (intervalDomainLift (w σ))
        =ᶠ[nhds x] deriv (fun x => ∑' n, bc σ n * cosineMode n x) := hloc.deriv
    rw [← hloc'.deriv_eq]
    exact hG2 σ hσ x (Set.Ioo_subset_Icc_self hx)
  have hN0_cs : ∀ σ ∈ Set.Icc lo hi,
      deriv (fun x => ∑' n, bc σ n * cosineMode n x) 0 = 0 :=
    fun σ hσ =>
      ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_deriv_at_zero
        (hbsum σ hσ)
  have hN1_cs : ∀ σ ∈ Set.Icc lo hi,
      deriv (fun x => ∑' n, bc σ n * cosineMode n x) 1 = 0 :=
    fun σ hσ =>
      ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_deriv_at_one
        (hbsum σ hσ)
  have hMnn : 0 ≤ M := by
    have hlo_mem : lo ∈ Set.Icc lo hi := ⟨le_rfl, hlohi⟩
    have h1 := hub lo hlo_mem 0 (by constructor <;> norm_num)
    have h2 := hpos lo hlo_mem 0 (by constructor <;> norm_num)
    linarith
  have hαpos : 0 < p.α := lt_of_lt_of_le one_pos hα
  set C : ℝ := max (2 * B_log p.a p.b p.α M G1 G2)
    (M * (p.a + p.b * M ^ p.α)) with hCdef
  have hBnn : 0 ≤ B_log p.a p.b p.α M G1 G2 :=
    B_log_nonneg hα ha hb hMnn hG1nn hG2nn
  have hCnn : 0 ≤ C :=
    le_trans (by linarith : (0 : ℝ) ≤ 2 * B_log p.a p.b p.α M G1 G2)
      (le_max_left _ _)
  have hsrc_eq : ∀ σ ∈ Set.Icc lo hi,
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        logisticSourceFun p.a p.b p.α (intervalDomainLift (w σ)) x
          = logisticSourceFun p.a p.b p.α
              (fun x => ∑' n, bc σ n * cosineMode n x) x := by
    intro σ hσ x hx
    simp only [logisticSourceFun]
    rw [hagree σ hσ hx]
  have hdecay : ∀ σ ∈ Set.Icc lo hi, ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (logisticSourceFun p.a p.b p.α (intervalDomainLift (w σ))) k|
        ≤ C / ((k : ℝ) * Real.pi) ^ 2 := by
    intro σ hσ k hk
    rw [cosineCoeffs_congr_on_Icc (hsrc_eq σ hσ) k]
    refine le_trans
      (logisticSourceFun_cosineCoeff_quadratic_decay_explicit
        (hcsC2 σ hσ) hα ha hb (hpos_cs σ hσ) (hub_cs σ hσ)
        (hG1_cs σ hσ) (hG2_cs σ hσ) (hN0_cs σ hσ) (hN1_cs σ hσ) k hk) ?_
    have hden : 0 < ((k : ℝ) * Real.pi) ^ 2 := by
      have hkpos : (0 : ℝ) < (k : ℝ) :=
        by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
      positivity
    gcongr
    exact le_max_left _ _
  have ha0 : ∀ σ ∈ Set.Icc lo hi,
      |cosineCoeffs (logisticSourceFun p.a p.b p.α (intervalDomainLift (w σ))) 0|
        ≤ C := by
    intro σ hσ
    rw [cosineCoeffs_congr_on_Icc (hsrc_eq σ hσ) 0]
    have hsup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |logisticSourceFun p.a p.b p.α
            (fun x => ∑' n, bc σ n * cosineMode n x) x|
          ≤ M * (p.a + p.b * M ^ p.α) :=
      logisticSourceFun_abs_le_of_bound (B := M) hMnn hαpos ha hb
        (fun x hx => by rw [abs_of_pos (hpos_cs σ hσ x hx)]; exact hub_cs σ hσ x hx)
        (hpos_cs σ hσ)
    have hgc : Continuous (fun x => ∑' n, bc σ n * cosineMode n x) :=
      (hcsC2 σ hσ).continuous
    have hcont : ContinuousOn
        (logisticSourceFun p.a p.b p.α
          (fun x => ∑' n, bc σ n * cosineMode n x))
        (Set.Icc (0 : ℝ) 1) := by
      have hpos' : ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
          (fun x => ∑' n, bc σ n * cosineMode n x) x ≠ 0 :=
        fun x hx => ne_of_gt (hpos_cs σ hσ x hx)
      unfold logisticSourceFun
      apply ContinuousOn.mul hgc.continuousOn
      apply ContinuousOn.sub continuousOn_const
      apply ContinuousOn.mul continuousOn_const
      exact ContinuousOn.rpow_const hgc.continuousOn (fun x hx => Or.inl (hpos' x hx))
    have hMa_nn : 0 ≤ M * (p.a + p.b * M ^ p.α) := by positivity
    exact le_trans (cosineCoeffs_zero_abs_le_of_bound hMa_nn hcont hsup)
      (le_max_right _ _)
  have hfam : (fun s k => cosineCoeffs (logisticLifted p (w s)) k)
      = (fun σ n => cosineCoeffs
          (logisticSourceFun p.a p.b p.α (intervalDomainLift (w σ))) n) := by
    funext s k
    exact cosineCoeffs_congr_on_Icc
      (logisticLifted_eq_logisticSourceFun_on_Icc p (w s)) k
  rw [hfam]
  refine
    { adot := adot
      hderiv := hderiv
      hadotcont := hadotcont
      envelope := fun n => if n = 0 then C else C / ((n : ℝ) * Real.pi) ^ 2
      henv_summable := ?_
      henv_bound := ?_
      derivBound := Mdot
      hderivBound := hMdot }
  · refine Summable.of_norm_bounded_eventually_nat
      (ShenWork.IntervalDomainRegularityBootstrap.reciprocalSquareTerm_summable.mul_left
        (C / Real.pi ^ 2)) ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    simp only [Real.norm_eq_abs]
    have hn0 : n ≠ 0 := by omega
    rw [if_neg hn0]
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    calc |C / ((n : ℝ) * Real.pi) ^ 2|
        = C / ((n : ℝ) * Real.pi) ^ 2 := by
          rw [abs_of_nonneg (div_nonneg hCnn (by positivity))]
      _ = C / Real.pi ^ 2
            * ShenWork.IntervalDomainRegularityBootstrap.reciprocalSquareTerm n := by
          rw [ShenWork.IntervalDomainRegularityBootstrap.reciprocalSquareTerm, mul_pow]
          field_simp [ne_of_gt hn_pos, Real.pi_ne_zero]
      _ ≤ C / Real.pi ^ 2
            * ShenWork.IntervalDomainRegularityBootstrap.reciprocalSquareTerm n := le_rfl
  · intro s hs n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
      exact ha0 s hs
    · simp [show n ≠ 0 from Nat.pos_iff_ne_zero.mp hn]
      exact hdecay s hs n hn

end ShenWork.IntervalDomainLimitSourceRepresentationOn

