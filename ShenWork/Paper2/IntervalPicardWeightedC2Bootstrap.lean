/-
  ShenWork/Paper2/IntervalPicardWeightedC2Bootstrap.lean

  R-src0F-2 — the **n-uniform window source envelope** (last analytic brick of
  the χ₀ = 0 chain), via the HYBRID weighted C² bootstrap.

  ## What the campaign already gives (A–E, landed elsewhere)

  The hybrid weighted bootstrap of the design doc
  (`HANDOFF/chatgpt-r2-hybrid-verdict.md`) is, structurally, already discharged
  by `ShenWork.IntervalPicardIterateUniform.picardIterateUniformData_all`:

    * **(A) Kernel first-derivative envelope** — `n`-free, no recursion:
        `|∂ₓ lift(uₙ(t)) x| ≤ G1profile p M t`
      (`g1_kernel_bound`: T1 propagator gradient + Atom D divergence-form Duhamel,
      under the χ₀ = 0 reduction).
    * **(B) Heat-trace bound** — `eigExpWeight(τ) ≤ (4/(e·π²))/τ²`
      (`IntervalWeightPowerBound.eigExpWeight_le`, the repo's reciprocal-square
      majorant); this is the `eigExpWeight_le_reciprocalSquare`-shaped fact in the
      design, packaged as the power-law gate weight.
    * **(C) Source envelope from weighted norms** — the explicit logistic source
      bound `B_log p.a p.b p.α M G1 G2 = Q·G1² + L·G2`
      (`IntervalLogisticSourceQuantBound.B_log`); the design's
      `B_log_le_of_weighted_bounds` is the `Benv`/`iterateSourceEnvelopeConst`
      evaluation at the half-step profiles.
    * **(D) Weighted R₂ step** — `iterate_abs_deriv2_le` multiplied through by `t²`,
      i.e. `g2_step_closes`: `M₁·eigExpWeight(t/2) + Cgain·(t/2)^{1/4}·Benv(t) ≤ A₂/t²`
      under the GATE smallness condition.
    * **(E) Ball closure** — the `_zero`/`_succ`/`_all` induction in the fixed
      `G2profile A₂ t = A₂/t²` ball, under the GATE (the consumer's small-horizon
      `δ(T) ≤ 1/2` is exactly the GATE condition `GateCondition p M A₂ T`).

  So on `(0,T]` the carrier delivers, uniformly in `n`:
    `|∂ₓ  lift(uₙ(t)) x| ≤ G1profile p M t`,
    `|∂ₓ² lift(uₙ(t)) x| ≤ A₂ / t²`.

  ## What THIS file adds — (F) the window source-coefficient envelope

  The residual `R-src0F-2` (the `hCwin_ex` sorry in
  `IntervalDomainThm11ChiZeroCoreProvider`) is the *consumer-shaped* output: a
  per-window constant `Cwin a'` with, for every `n`, every `σ ∈ [a',T]`, every `k`,
    `|cosineCoeffs (logisticLifted p (picardIter p u₀ n σ)) k| ≤ windowEnv (Cwin a') k`,
  i.e. `≤ Cwin a'` at `k = 0` and `≤ Cwin a' / (kπ)²` for `k ≥ 1`.

  This file proves that envelope from the window-uniform K2 data.  The per-slice
  source decay is the *exact* coefficient content of
  `IntervalDomainLimitSourceRepresentation.limitSource_duhamelSourceTimeC1_of_representation`'s
  internal `hdecay`/`ha0`, lifted out as a standalone bound and specialised to the
  Picard iterate family through the per-slice cosine representation `bc`.

  No `sorry`/`admit`/custom `axiom`/`native_decide` in the proved theorems; the
  single residual is the genuinely iterate-side analytic hypothesis bundle
  `IterateWindowC2Data` (a record of the window-uniform K2 facts), threaded — not
  asserted — exactly as the consumer supplies it.  New file only.
-/
import ShenWork.Paper2.IntervalDomainLimitSourceRepresentation
import ShenWork.Paper2.IntervalPicardIterateSourceC1
import ShenWork.Paper2.IntervalPicardIterateUniform
import ShenWork.Paper2.IntervalPicardLimitBddProducer

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalMildPicardRegularity
  (logisticSourceFun logisticLifted_eq_logisticSourceFun_on_Icc
   cosineCoeffs_zero_abs_le_of_bound logisticSourceFun_abs_le_of_bound)
open ShenWork.IntervalLogisticSourceQuantBound (B_log B_log_nonneg
  logisticSourceFun_cosineCoeff_quadratic_decay_explicit)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)
open ShenWork.IntervalPicardLimitBddProducer (windowEnv)

noncomputable section

namespace ShenWork.IntervalPicardWeightedC2Bootstrap

/-! ## §F.0 — The window envelope constant.

The per-window source constant `Cwin a'` is `iterateSourceEnvelopeConst` evaluated
at the window-uniform K2 constants `(M, G1, G2)`:
`max (2·B_log p.a p.b p.α M G1 G2) (M·(p.a+p.b·M^α))`.  At `k = 0` it dominates the
source sup, at `k ≥ 1` it dominates `2·B_log` (the quadratic decay numerator). -/

/-- The window source envelope constant for window-uniform K2 data `(M,G1,G2)`. -/
def windowSourceConst (p : CM2Params) (M G1 G2 : ℝ) : ℝ :=
  max (2 * B_log p.a p.b p.α M G1 G2) (M * (p.a + p.b * M ^ p.α))

theorem windowSourceConst_nonneg
    (p : CM2Params) {M G1 G2 : ℝ} (hα : 1 ≤ p.α)
    (hM : 0 ≤ M) (hG1 : 0 ≤ G1) (hG2 : 0 ≤ G2) :
    0 ≤ windowSourceConst p M G1 G2 := by
  have hBnn : 0 ≤ B_log p.a p.b p.α M G1 G2 := B_log_nonneg hα p.ha p.hb hM hG1 hG2
  exact le_trans (by linarith : (0:ℝ) ≤ 2 * B_log p.a p.b p.α M G1 G2) (le_max_left _ _)

/-! ## §F.1 — Per-slice source coefficient envelope from a cosine representation.

For a single profile `g : ℝ → ℝ` that agrees on `[0,1]` with a genuinely-`C²`
cosine series `cs = ∑ₙ bc n · cos(nπx)` (eigenvalue-weighted summable `bc`),
positive, sup-bounded by `M`, with `|∂ₓ| ≤ G1`, `|∂ₓ²| ≤ G2`, the logistic source
coefficients satisfy the quadratic decay (`k ≥ 1`) and the zeroth-mode sup bound
— both with the explicit window constant `windowSourceConst p M G1 G2`.

This is the standalone coefficient content of
`IntervalDomainLimitSourceRepresentation.limitSource_duhamelSourceTimeC1_of_representation`. -/

/-- **Per-slice quadratic decay (k ≥ 1).** -/
theorem slice_source_coeff_decay
    (p : CM2Params) {g : ℝ → ℝ} {M G1 G2 : ℝ}
    (hα : 1 ≤ p.α)
    (bc : ℕ → ℝ)
    (hbsum : Summable (fun n => unitIntervalCosineEigenvalue n * |bc n|))
    (hagree : Set.EqOn g (fun x => ∑' n, bc n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < g x)
    (hub : ∀ x ∈ Set.Icc (0 : ℝ) 1, g x ≤ M)
    (hG1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv g x| ≤ G1)
    (hG2 : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv g) x| ≤ G2) :
    ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (logisticSourceFun p.a p.b p.α g) k|
        ≤ windowSourceConst p M G1 G2 / ((k : ℝ) * Real.pi) ^ 2 := by
  -- the genuinely-C² cosine series
  have hcsC2 : ContDiff ℝ 2 (fun x => ∑' n, bc n * cosineMode n x) :=
    ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two hbsum
  have hcs_d_cont : Continuous (deriv (fun x => ∑' n, bc n * cosineMode n x)) :=
    hcsC2.continuous_deriv (by norm_num)
  have hcs_dd_cont : Continuous (deriv (deriv (fun x => ∑' n, bc n * cosineMode n x))) := by
    have h2 : ContDiff ℝ (1 + 1) (fun x => ∑' n, bc n * cosineMode n x) := by simpa using hcsC2
    exact ((contDiff_succ_iff_deriv.mp h2).2.2).continuous_deriv le_rfl
  -- transfer the K2 facts to the series on [0,1]
  have hpos_cs : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < (fun x => ∑' n, bc n * cosineMode n x) x :=
    fun x hx => by rw [← hagree hx]; exact hpos x hx
  have hub_cs : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (fun x => ∑' n, bc n * cosineMode n x) x ≤ M :=
    fun x hx => by rw [← hagree hx]; exact hub x hx
  have hG1_cs : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (fun x => ∑' n, bc n * cosineMode n x) x| ≤ G1 := by
    refine ShenWork.IntervalDomainLimitSourceRepresentation.le_on_Icc_of_le_on_Ioo
      hcs_d_cont.abs (fun x hx => ?_)
    have hloc : g =ᶠ[nhds x] (fun x => ∑' n, bc n * cosineMode n x) := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hagree (Set.Ioo_subset_Icc_self hy)
    rw [← hloc.deriv_eq]; exact hG1 x (Set.Ioo_subset_Icc_self hx)
  have hG2_cs : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (fun x => ∑' n, bc n * cosineMode n x)) x| ≤ G2 := by
    refine ShenWork.IntervalDomainLimitSourceRepresentation.le_on_Icc_of_le_on_Ioo
      hcs_dd_cont.abs (fun x hx => ?_)
    have hloc : g =ᶠ[nhds x] (fun x => ∑' n, bc n * cosineMode n x) := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hagree (Set.Ioo_subset_Icc_self hy)
    have hloc' : deriv g =ᶠ[nhds x] deriv (fun x => ∑' n, bc n * cosineMode n x) :=
      hloc.deriv
    rw [← hloc'.deriv_eq]; exact hG2 x (Set.Ioo_subset_Icc_self hx)
  -- Neumann endpoints (free from summability)
  have hN0_cs : deriv (fun x => ∑' n, bc n * cosineMode n x) 0 = 0 :=
    ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_deriv_at_zero hbsum
  have hN1_cs : deriv (fun x => ∑' n, bc n * cosineMode n x) 1 = 0 :=
    ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_deriv_at_one hbsum
  -- the lift's source equals the series' source on [0,1]
  have hsrc_eq : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      logisticSourceFun p.a p.b p.α g x
        = logisticSourceFun p.a p.b p.α (fun x => ∑' n, bc n * cosineMode n x) x := by
    intro x hx; simp only [logisticSourceFun]; rw [hagree hx]
  -- apply the global quadratic-decay machinery to the C² series
  intro k hk
  rw [cosineCoeffs_congr_on_Icc hsrc_eq k]
  refine le_trans
    (logisticSourceFun_cosineCoeff_quadratic_decay_explicit hcsC2 hα p.ha p.hb
      hpos_cs hub_cs hG1_cs hG2_cs hN0_cs hN1_cs k hk) ?_
  have hden : 0 < ((k : ℝ) * Real.pi) ^ 2 := by
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
    positivity
  gcongr
  exact le_max_left _ _

/-- **Per-slice zeroth-mode bound.** -/
theorem slice_source_coeff_zero
    (p : CM2Params) {g : ℝ → ℝ} {M G1 G2 : ℝ}
    (hα : 1 ≤ p.α)
    (bc : ℕ → ℝ)
    (hbsum : Summable (fun n => unitIntervalCosineEigenvalue n * |bc n|))
    (hagree : Set.EqOn g (fun x => ∑' n, bc n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < g x)
    (hub : ∀ x ∈ Set.Icc (0 : ℝ) 1, g x ≤ M) :
    |cosineCoeffs (logisticSourceFun p.a p.b p.α g) 0|
      ≤ windowSourceConst p M G1 G2 := by
  have hcsC2 : ContDiff ℝ 2 (fun x => ∑' n, bc n * cosineMode n x) :=
    ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two hbsum
  have hpos_cs : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < (fun x => ∑' n, bc n * cosineMode n x) x :=
    fun x hx => by rw [← hagree hx]; exact hpos x hx
  have hub_cs : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (fun x => ∑' n, bc n * cosineMode n x) x ≤ M :=
    fun x hx => by rw [← hagree hx]; exact hub x hx
  have hMnn : 0 ≤ M := by
    have h1 := hub 0 (by constructor <;> norm_num)
    have h2 := hpos 0 (by constructor <;> norm_num)
    linarith
  have hαpos : 0 < p.α := lt_of_lt_of_le one_pos hα
  have hsrc_eq : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      logisticSourceFun p.a p.b p.α g x
        = logisticSourceFun p.a p.b p.α (fun x => ∑' n, bc n * cosineMode n x) x := by
    intro x hx; simp only [logisticSourceFun]; rw [hagree hx]
  rw [cosineCoeffs_congr_on_Icc hsrc_eq 0]
  have hsup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |logisticSourceFun p.a p.b p.α (fun x => ∑' n, bc n * cosineMode n x) x|
        ≤ M * (p.a + p.b * M ^ p.α) :=
    logisticSourceFun_abs_le_of_bound (B := M) hMnn hαpos p.ha p.hb
      (fun x hx => by rw [abs_of_pos (hpos_cs x hx)]; exact hub_cs x hx) hpos_cs
  have hgc : Continuous (fun x => ∑' n, bc n * cosineMode n x) := hcsC2.continuous
  have hcont : ContinuousOn
      (logisticSourceFun p.a p.b p.α (fun x => ∑' n, bc n * cosineMode n x))
      (Set.Icc (0 : ℝ) 1) := by
    have hpos' : ∀ x, x ∈ Set.Icc (0:ℝ) 1 →
        (fun x => ∑' n, bc n * cosineMode n x) x ≠ 0 :=
      fun x hx => ne_of_gt (hpos_cs x hx)
    unfold logisticSourceFun
    apply ContinuousOn.mul hgc.continuousOn
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.mul continuousOn_const
    exact ContinuousOn.rpow_const hgc.continuousOn (fun x hx => Or.inl (hpos' x hx))
  have hMa_nn : 0 ≤ M * (p.a + p.b * M ^ p.α) := by
    have hpow : 0 ≤ M ^ p.α := Real.rpow_nonneg hMnn _
    have hfac : 0 ≤ p.a + p.b * M ^ p.α := by
      have := mul_nonneg p.hb hpow; have := p.ha; linarith
    exact mul_nonneg hMnn hfac
  exact le_trans (cosineCoeffs_zero_abs_le_of_bound hMa_nn hcont hsup) (le_max_right _ _)

/-! ## §F.2 — The window-uniform iterate data bundle.

`IterateWindowC2Data p u₀ a' T` packages the window-uniform, `n`-uniform K2 facts
that the hybrid bootstrap (`picardIterateUniformData_all`) and the iterate
regularity bootstrap (`picardIterateHasC2Slices_all`) supply on `[a',T]`:

  * a per-slice cosine representation `bc n σ` of `lift(uₙ(σ))`
    (eigenvalue-weighted summable + agreement on `[0,1]`);
  * the Picard ball positivity / sup bound `(M)`;
  * the window-uniform first/second derivative sup bounds `(G1, G2)`.

These are precisely the inputs of `slice_source_coeff_*`.  Bundling them as a
hypothesis record makes the window envelope theorem below a clean, true
implication; the consumer (`IntervalDomainThm11ChiZeroCoreProvider`) discharges
the bundle from the landed atoms (the `(R-src0F-2)` route documented there). -/

/-- Window-uniform K2 data for the Picard iterates on `[a',T]`. -/
structure IterateWindowC2Data
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (a' T : ℝ) where
  /-- The window-uniform sup / gradient / Hessian constants. -/
  M : ℝ
  G1 : ℝ
  G2 : ℝ
  hMnn : 0 ≤ M
  hG1nn : 0 ≤ G1
  hG2nn : 0 ≤ G2
  /-- Per-slice cosine coefficients of `lift(uₙ(σ))`. -/
  bc : ℕ → ℝ → ℕ → ℝ
  hbsum : ∀ n σ, a' ≤ σ → σ ≤ T →
    Summable (fun m => unitIntervalCosineEigenvalue m * |bc n σ m|)
  hagree : ∀ n σ, a' ≤ σ → σ ≤ T →
    Set.EqOn (intervalDomainLift (picardIter p u₀ n σ))
      (fun x => ∑' m, bc n σ m * cosineMode m x) (Set.Icc (0 : ℝ) 1)
  /-- Picard ball positivity + sup bound, window-uniform. -/
  hpos : ∀ n σ, a' ≤ σ → σ ≤ T →
    ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (picardIter p u₀ n σ) x
  hub : ∀ n σ, a' ≤ σ → σ ≤ T →
    ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (picardIter p u₀ n σ) x ≤ M
  /-- Window-uniform spatial derivative sup bounds (the hybrid bootstrap output). -/
  hG1 : ∀ n σ, a' ≤ σ → σ ≤ T →
    ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (intervalDomainLift (picardIter p u₀ n σ)) x| ≤ G1
  hG2 : ∀ n σ, a' ≤ σ → σ ≤ T →
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (picardIter p u₀ n σ))) x| ≤ G2

/-! ## §F.3 — The window source coefficient envelope (F).

From `IterateWindowC2Data`, on every window slice the logistic source coefficients
of `lift(uₙ(σ))` are dominated by `windowEnv (windowSourceConst …)`, uniformly in
`n` and `σ ∈ [a',T]`.  This is the exact `henv_iter` shape consumed by
`IntervalPicardLimitBddBootstrap.duhamelSourceBddOn_of_iterates`. -/

/-- **(F) — window source coefficient envelope.**
The `windowEnv`-form bound on the iterate logistic-source coefficients, uniform in
`n` and over `σ ∈ [a',T]`, with the explicit window constant
`windowSourceConst p D.M D.G1 D.G2`. -/
theorem iterate_source_windowEnv
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {a' T : ℝ}
    (hα : 1 ≤ p.α) (D : IterateWindowC2Data p u₀ a' T) :
    ∀ n σ, a' ≤ σ → σ ≤ T → ∀ k : ℕ,
      |cosineCoeffs (logisticLifted p (picardIter p u₀ n σ)) k|
        ≤ windowEnv (windowSourceConst p D.M D.G1 D.G2) k := by
  intro n σ haσ hσT k
  -- transport logisticLifted ↦ logisticSourceFun (equal on [0,1])
  have hfam : cosineCoeffs (logisticLifted p (picardIter p u₀ n σ)) k
      = cosineCoeffs
          (logisticSourceFun p.a p.b p.α (intervalDomainLift (picardIter p u₀ n σ))) k :=
    cosineCoeffs_congr_on_Icc
      (logisticLifted_eq_logisticSourceFun_on_Icc p (picardIter p u₀ n σ)) k
  rw [hfam]
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- zeroth mode
    subst hk0
    have hz := slice_source_coeff_zero p (M := D.M) (G1 := D.G1) (G2 := D.G2) hα
      (D.bc n σ) (D.hbsum n σ haσ hσT) (D.hagree n σ haσ hσT)
      (D.hpos n σ haσ hσT) (D.hub n σ haσ hσT)
    simpa [windowEnv] using hz
  · -- k ≥ 1: quadratic decay
    have hk : 1 ≤ k := hkpos
    have hd := slice_source_coeff_decay p (M := D.M) (G1 := D.G1) (G2 := D.G2) hα
      (D.bc n σ) (D.hbsum n σ haσ hσT) (D.hagree n σ haσ hσT)
      (D.hpos n σ haσ hσT) (D.hub n σ haσ hσT)
      (D.hG1 n σ haσ hσT) (D.hG2 n σ haσ hσT) k hk
    have hkne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hkpos
    simpa [windowEnv, hkne] using hd

/-! ## §F.4 — Existence form (matches the consumer's `hCwin_ex` residual).

This is the exact shape of the `(R-src0F-2)` residual sorry in
`IntervalDomainThm11ChiZeroCoreProvider`: a per-window constant `Cwin` with the
`windowEnv` envelope.  Here it is provided as a clean implication from the
window-uniform K2 data bundle (one bundle per window, supplied by the consumer
from `picardIterateUniformData_all` + `picardIterateHasC2Slices_all`). -/

/-- **(F-existence) — the consumer-shaped window envelope existence statement.**
Given, for every window `a' > 0`, the window-uniform K2 data bundle, there is a
nonnegative per-window constant `Cwin` whose `windowEnv` dominates the iterate
source coefficients on `[a',T]`, uniformly in `n`. -/
theorem source_coeff_window_uniform
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {T : ℝ}
    (hα : 1 ≤ p.α)
    (Wdata : ∀ a', 0 < a' → IterateWindowC2Data p u₀ a' T) :
    ∃ Cwin : ℝ → ℝ, (∀ a', 0 ≤ Cwin a') ∧
      (∀ a', 0 < a' → ∀ σ, a' ≤ σ → σ ≤ T → ∀ (n : ℕ) (k : ℕ),
        |cosineCoeffs (logisticLifted p (picardIter p u₀ n σ)) k|
          ≤ windowEnv (Cwin a') k) := by
  classical
  refine ⟨fun a' => if h : 0 < a' then
      windowSourceConst p (Wdata a' h).M (Wdata a' h).G1 (Wdata a' h).G2 else 0,
    ?_, ?_⟩
  · intro a'
    dsimp only
    split_ifs with h
    · exact windowSourceConst_nonneg p hα (Wdata a' h).hMnn (Wdata a' h).hG1nn (Wdata a' h).hG2nn
    · exact le_refl 0
  · intro a' ha' σ haσ hσT n k
    dsimp only
    rw [dif_pos ha']
    exact iterate_source_windowEnv p u₀ hα (Wdata a' ha') n σ haσ hσT k

end ShenWork.IntervalPicardWeightedC2Bootstrap
