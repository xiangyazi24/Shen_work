/-
  ShenWork/Paper2/IntervalDomainLimitSourceRepresentation.lean

  Representation-fed limit-source `DuhamelSourceTimeC1` producer.

  This replaces the global-`C²` hypothesis on the zero-extension lift — which is
  UNSATISFIABLE for a profile positive at the Neumann endpoints (see
  `IntervalDomainThm11ChiZeroCoreProvider`) — by the per-slice cosine
  representation
      `lift (w σ) =ᴵᶜᶜ (x ↦ ∑ₙ bc σ n · cos(nπx))`  with  `∑ₙ λₙ |bc σ n| < ∞`.

  The series `cs σ x = ∑ₙ bc σ n cos(nπx)` is genuinely globally `C²`
  (`cosineCoeffSeries_contDiff_two`), so the EXISTING explicit quadratic-decay
  machinery (`logisticSourceFun_cosineCoeff_quadratic_decay_explicit`) applies to
  `cs σ`, yielding the UNIFORM constant `2·B_log(M,G1,G2)`.  The lift's cosine
  coefficients agree with `cs σ`'s on `[0,1]` (`cosineCoeffs_congr_on_Icc`), so
  the decay and the zeroth-coefficient bound transfer to the lift.  The `K2`
  gradient/Hessian bounds (`hG1`/`hG2`) are stated on the lift; they transfer to
  `cs σ` on `[0,1]` because the two functions agree on the open interval `(0,1)`
  (so their derivatives agree there) and `deriv (cs σ)` / `deriv (deriv (cs σ))`
  are continuous (`cs σ` is `C²`), extending the bound to the closed `[0,1]`.
  The Neumann endpoints of `cs σ` come for free from the series
  (`cosineCoeffSeries_deriv_at_zero` / `_at_one`).

  Final assembly via the additive adapter
  `logisticSource_duhamelSourceTimeC1_of_representation`.

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.Paper2.IntervalDomainLogisticWeakH2Adapter
import ShenWork.PDE.IntervalLogisticSourceQuantBound
import ShenWork.Paper2.IntervalDomainL2StaticVDifference

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicardRegularity
  (logisticSourceFun logisticLifted_eq_logisticSourceFun_on_Icc
   cosineCoeffs_zero_abs_le_of_bound logisticSourceFun_abs_le_of_bound)
open ShenWork.IntervalLogisticSourceQuantBound
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)

noncomputable section

namespace ShenWork.IntervalDomainLimitSourceRepresentation

/-- **A pointwise bound that holds on `(0,1)` for a continuous function extends to
the closed `[0,1]`.**  `{x | φ x ≤ G}` is closed, contains the dense `Ioo 0 1`,
hence contains its closure `Icc 0 1`. -/
lemma le_on_Icc_of_le_on_Ioo {φ : ℝ → ℝ} {G : ℝ} (hcont : Continuous φ)
    (hIoo : ∀ x ∈ Set.Ioo (0 : ℝ) 1, φ x ≤ G) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, φ x ≤ G := by
  have hclosed : IsClosed {x : ℝ | φ x ≤ G} := isClosed_le hcont continuous_const
  have hsub : Set.Icc (0 : ℝ) 1 ⊆ {x | φ x ≤ G} := by
    rw [← closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact hclosed.closure_subset_iff.mpr (fun x hx => hIoo x hx)
  exact fun x hx => hsub hx

/-- **Representation-fed limit-source `DuhamelSourceTimeC1`.**

The additive, cosine-representation analogue of
`IntervalPicardLimitSourceData.limitSource_duhamelSourceTimeC1`: it discharges the
same `DuhamelSourceTimeC1` conclusion for the logistic-source coefficient family
of an arbitrary trajectory `w`, but with the (UNSATISFIABLE) global-`C²` field
replaced by the per-slice cosine representation `(bc, hbsum, hagree)`.  The `K2`
sup/gradient/Hessian bounds (`hub`/`hG1`/`hG2`) are retained verbatim; the Neumann
endpoint fields are no longer required (the series supplies them). -/
noncomputable def limitSource_duhamelSourceTimeC1_of_representation
    (p : CM2Params)
    (w : ℝ → intervalDomainPoint → ℝ)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {M G1 G2 : ℝ}
    -- per-slice cosine representation (genuinely `C²`; replaces global-`C²`)
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, Set.EqOn (intervalDomainLift (w σ))
        (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    -- `K2` spatial slice bounds on the lift
    (hpos : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (w σ) x)
    (hub : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (w σ) x ≤ M)
    (hG1 : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (w σ)) x| ≤ G1)
    (hG2 : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (w σ))) x| ≤ G2)
    -- `K1` source-coefficient time-`C¹` data
    (adot : ℝ → ℕ → ℝ)
    (hderiv : ∀ σ k, HasDerivAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (w r))) k) (adot σ k) σ)
    (hadotcont : ∀ k, Continuous (fun σ => adot σ k))
    {Mdot : ℝ}
    (hMdot : ∀ σ, 0 ≤ σ → ∀ k, |adot σ k| ≤ Mdot) :
    DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (w s)) k) := by
  -- The genuinely-`C²` cosine series per slice.
  have hcsC2 : ∀ σ, ContDiff ℝ 2 (fun x => ∑' n, bc σ n * cosineMode n x) :=
    fun σ => ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two (hbsum σ)
  -- continuity of `deriv` and `deriv (deriv ·)` of the series.
  have hcs_d_cont : ∀ σ,
      Continuous (deriv (fun x => ∑' n, bc σ n * cosineMode n x)) :=
    fun σ => (hcsC2 σ).continuous_deriv (by norm_num)
  have hcs_dd_cont : ∀ σ,
      Continuous (deriv (deriv (fun x => ∑' n, bc σ n * cosineMode n x))) := by
    intro σ
    have h2 : ContDiff ℝ (1 + 1) (fun x => ∑' n, bc σ n * cosineMode n x) := by
      simpa using hcsC2 σ
    exact ((contDiff_succ_iff_deriv.mp h2).2.2).continuous_deriv le_rfl
  -- positivity / sup bound transfer to the series on `[0,1]` (pointwise agreement).
  have hpos_cs : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < (fun x => ∑' n, bc σ n * cosineMode n x) x := by
    intro σ x hx; rw [← hagree σ hx]; exact hpos σ x hx
  have hub_cs : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (fun x => ∑' n, bc σ n * cosineMode n x) x ≤ M := by
    intro σ x hx; rw [← hagree σ hx]; exact hub σ x hx
  -- gradient bound transfer: on `(0,1)` the series and the lift agree on an open
  -- neighbourhood, so their derivatives agree there; extend by continuity.
  have hG1nn : 0 ≤ G1 := le_trans (abs_nonneg _) (hG1 0 0 (by constructor <;> norm_num))
  have hG2nn : 0 ≤ G2 := le_trans (abs_nonneg _) (hG2 0 0 (by constructor <;> norm_num))
  have hG1_cs : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (fun x => ∑' n, bc σ n * cosineMode n x) x| ≤ G1 := by
    intro σ
    refine le_on_Icc_of_le_on_Ioo (hcs_d_cont σ).abs (fun x hx => ?_)
    have hloc : intervalDomainLift (w σ)
        =ᶠ[nhds x] (fun x => ∑' n, bc σ n * cosineMode n x) := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hagree σ (Set.Ioo_subset_Icc_self hy)
    rw [← hloc.deriv_eq]
    exact hG1 σ x (Set.Ioo_subset_Icc_self hx)
  have hG2_cs : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (fun x => ∑' n, bc σ n * cosineMode n x)) x| ≤ G2 := by
    intro σ
    refine le_on_Icc_of_le_on_Ioo (hcs_dd_cont σ).abs (fun x hx => ?_)
    have hloc : intervalDomainLift (w σ)
        =ᶠ[nhds x] (fun x => ∑' n, bc σ n * cosineMode n x) := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hagree σ (Set.Ioo_subset_Icc_self hy)
    have hloc' : deriv (intervalDomainLift (w σ))
        =ᶠ[nhds x] deriv (fun x => ∑' n, bc σ n * cosineMode n x) := hloc.deriv
    rw [← hloc'.deriv_eq]
    exact hG2 σ x (Set.Ioo_subset_Icc_self hx)
  -- Neumann endpoints of the series (free from summability).
  have hN0_cs : ∀ σ, deriv (fun x => ∑' n, bc σ n * cosineMode n x) 0 = 0 :=
    fun σ => ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_deriv_at_zero (hbsum σ)
  have hN1_cs : ∀ σ, deriv (fun x => ∑' n, bc σ n * cosineMode n x) 1 = 0 :=
    fun σ => ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_deriv_at_one (hbsum σ)
  -- bookkeeping constants.
  have hMnn : 0 ≤ M := by
    have h1 := hub 0 0 (by constructor <;> norm_num)
    have h2 := hpos 0 0 (by constructor <;> norm_num)
    linarith
  have hαpos : 0 < p.α := lt_of_lt_of_le one_pos hα
  set C : ℝ := max (2 * B_log p.a p.b p.α M G1 G2) (M * (p.a + p.b * M ^ p.α)) with hCdef
  have hBnn : 0 ≤ B_log p.a p.b p.α M G1 G2 := B_log_nonneg hα ha hb hMnn hG1nn hG2nn
  have hCnn : 0 ≤ C := le_trans (by linarith : (0:ℝ) ≤ 2 * B_log p.a p.b p.α M G1 G2)
    (le_max_left _ _)
  -- the lift's logistic source equals the series' on `[0,1]` (pointwise).
  have hsrc_eq : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      logisticSourceFun p.a p.b p.α (intervalDomainLift (w σ)) x
        = logisticSourceFun p.a p.b p.α (fun x => ∑' n, bc σ n * cosineMode n x) x := by
    intro σ x hx; simp only [logisticSourceFun]; rw [hagree σ hx]
  -- uniform quadratic decay (k ≥ 1) of the lift's source coefficients.
  have hdecay : ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (logisticSourceFun p.a p.b p.α (intervalDomainLift (w σ))) k|
        ≤ C / ((k : ℝ) * Real.pi) ^ 2 := by
    intro σ _ k hk
    rw [cosineCoeffs_congr_on_Icc (hsrc_eq σ) k]
    refine le_trans
      (logisticSourceFun_cosineCoeff_quadratic_decay_explicit (hcsC2 σ) hα ha hb
        (hpos_cs σ) (hub_cs σ) (hG1_cs σ) (hG2_cs σ) (hN0_cs σ) (hN1_cs σ) k hk) ?_
    have hden : 0 < ((k : ℝ) * Real.pi) ^ 2 := by
      have hkpos : (0 : ℝ) < (k : ℝ) :=
        by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
      positivity
    gcongr
    exact le_max_left _ _
  -- zeroth-coefficient bound of the lift's source coefficients.
  have ha0 : ∀ σ, 0 ≤ σ →
      |cosineCoeffs (logisticSourceFun p.a p.b p.α (intervalDomainLift (w σ))) 0| ≤ C := by
    intro σ _
    rw [cosineCoeffs_congr_on_Icc (hsrc_eq σ) 0]
    have hsup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |logisticSourceFun p.a p.b p.α (fun x => ∑' n, bc σ n * cosineMode n x) x|
          ≤ M * (p.a + p.b * M ^ p.α) :=
      logisticSourceFun_abs_le_of_bound (B := M) hMnn hαpos ha hb
        (fun x hx => by rw [abs_of_pos (hpos_cs σ x hx)]; exact hub_cs σ x hx)
        (hpos_cs σ)
    have hgc : Continuous (fun x => ∑' n, bc σ n * cosineMode n x) := (hcsC2 σ).continuous
    have hcont : ContinuousOn
        (logisticSourceFun p.a p.b p.α (fun x => ∑' n, bc σ n * cosineMode n x))
        (Set.Icc (0 : ℝ) 1) := by
      have hpos' : ∀ x, x ∈ Set.Icc (0:ℝ) 1 →
          (fun x => ∑' n, bc σ n * cosineMode n x) x ≠ 0 :=
        fun x hx => ne_of_gt (hpos_cs σ x hx)
      unfold logisticSourceFun
      apply ContinuousOn.mul hgc.continuousOn
      apply ContinuousOn.sub continuousOn_const
      apply ContinuousOn.mul continuousOn_const
      exact ContinuousOn.rpow_const hgc.continuousOn (fun x hx => Or.inl (hpos' x hx))
    have hMa_nn : 0 ≤ M * (p.a + p.b * M ^ p.α) := by positivity
    exact le_trans (cosineCoeffs_zero_abs_le_of_bound hMa_nn hcont hsup) (le_max_right _ _)
  -- assemble via the additive representation adapter, then transport to
  -- the `logisticLifted` family (equal on `[0,1]`, hence equal cosine coeffs).
  have hfam : (fun s k => cosineCoeffs (logisticLifted p (w s)) k)
      = (fun σ n => cosineCoeffs
          (logisticSourceFun p.a p.b p.α (intervalDomainLift (w σ))) n) := by
    funext s k
    exact cosineCoeffs_congr_on_Icc (logisticLifted_eq_logisticSourceFun_on_Icc p (w s)) k
  rw [hfam]
  exact ShenWork.IntervalDomainLogisticWeakH2Adapter.logisticSource_duhamelSourceTimeC1_of_representation
    bc hbsum hagree hpos hCnn hdecay ha0 hderiv hadotcont hMdot

end ShenWork.IntervalDomainLimitSourceRepresentation
