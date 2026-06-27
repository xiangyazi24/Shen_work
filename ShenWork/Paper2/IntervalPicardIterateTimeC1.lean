/-
  ShenWork/Paper2/IntervalPicardIterateTimeC1.lean

  Phase-0 / M3b — **K1 discharge**: time-`C¹` source-coefficient data from the
  restart representation of the iterate slice.

  Goal.  Produce the `K1` hypothesis block consumed by M3
  (`ShenWork.IntervalPicardIterateSourceC1.picardIterate_source_duhamelSourceTimeC1`):
  the family

      adot σ k := cosineCoeffs (∂_σ L(w σ)) k

  with its `HasDerivAt`, time-continuity, and an EXPLICIT uniform bound `Mdot`,
  derived from a **restart representation** of the iterate-slice profile

      lift(w σ) = ∑'ₙ localRestartCoeff a₀ a (σ − offset) n · cos(nπ·)   on [0,1]

  (`(R)`, the `HasTimeNeighborhoodSpectralAgreement`-shape), together with the
  `(K2)` slice data (positivity floor, sup bound, `C²`-Neumann).

  ## Quantitative core (all atoms proved upstream)

  * **Pointwise time derivative of the field.**  From `(R)` + G4i
    (`restartCosineSeries_hasDerivAt_time`, time-shifted by `offset`), at each
    `σ` in the window and each `x`,
        HasDerivAt (fun r => lift(w r) x) (restartFieldTimeDeriv … σ x) σ,
    where the value is the spectral derivative
        ∑'ₙ (a(σ−offset)ₙ − λₙ·localRestartCoeff a₀ a (σ−offset) n)·cos(nπx).
    Its absolute value is bounded by
        Mdot_u(τ) := (∑'ₖ envelope k) + M₀·eigExpWeight τ
                       + duhamelGainConst·τ^{1/4}·B           (τ = σ − offset),
    using `|∂field| ≤ ∑'|aₖ| + ∑'λₖ|cₖ|` and the three quantitative atoms:
    `src.henv_bound` (the ℓ¹ envelope), `homogeneous_eigenvalue_tsum_le`
    (`M₀·E₂(τ)`), and `duhamelSpectralCoeff_eigenvalue_tsum_tauQuarter_bound`
    (`…·τ^{1/4}·B`).  On a window `σ ∈ Icc t₁ t₂` with `offset < t₁` we make the
    bound uniform via `eigExpWeight_antitone` (`E₂(τ) ≤ E₂(τmin)`, `τmin = t₁−offset`)
    and `τ^{1/4} ≤ τmax^{1/4}` (`τmax = t₂−offset`), giving the constant
        UMdot := (∑'ₖ envelope k) + M₀·E₂(τmin) + duhamelGainConst·τmax^{1/4}·B.

  * **Joint continuity of `∂field`.**  `restartDerivField_continuousOn_joint`.

  * **The logistic `K1` package.**  `adot σ k := cosineCoeffs (f' σ) k` with
    `f' σ x := restartFieldTimeDeriv … σ x · (a − b(1+α)(lift(w σ) x)^α)`
    (chain rule `logisticSourceFun_hasDerivAt_time`), the `HasDerivAt` of the
    source coefficient from the time-Leibniz rule
    `cosineCoeffs_hasDerivAt_of_smooth_param`, and the uniform bound
        Mdot := 2·(a + b(1+α)·M^α)·UMdot
    via `cosineCoeffs_abs_le_of_continuous_bounded` (`|cosineCoeffs h k| ≤ 2·sup|h|`)
    and `|a − b(1+α)z^α| ≤ a + b(1+α)M^α` on `(0,M]`.

  ## Named satisfiable hypothesis (header justification)

  The time-Leibniz atom needs joint continuity of the *profile slice* factor
  `(s,x) ↦ (lift(w s) x)^α` on `window ×ˢ [0,1]`.  Whereas the *derivative* field
  is jointly continuous by `restartDerivField_continuousOn_joint`, the *value*
  field's joint continuity is not a packaged atom here, so we take it as the
  hypothesis `hprofile_joint`:

      ContinuousOn (Function.uncurry (fun s x => lift(w s) x)) (window ×ˢ Icc 0 1).

  It is satisfied for the real iterate slice because, on the window, `lift(w s)`
  equals the restart cosine series `∑'ₙ localRestartCoeff a₀ a (s−offset) n·cos`,
  whose summands are jointly continuous in `(s,x)` and which is locally uniformly
  summable on `Ioi 0 ×ˢ univ` (the same machinery as the derivative field in
  `IntervalRestartDerivJointContinuity`).

  STATUS (DISCHARGED).  `hprofile_joint` is no longer a genuine residual.  The
  value-field joint continuity is now proved here as
  `restartValueSeries_continuousOn_joint` (offset-shift of the value-series atom
  `ShenWork.IntervalSourceCoefficientTimeC1.restartSeries_jointContinuousOn`, the
  exact analogue of `restartDerivField_continuousOn_joint`), and the slab-level
  `hprofile_joint` is constructed from the restart agreement `(R)` in
  `restartProfile_jointContinuousOn`.  The master theorem
  `picardIterate_K1_from_restart_of_representation` takes ONLY Front A's
  satisfiable inputs (the `(R)` triple + `(K2)` slice data) and discharges
  `hprofile_joint` internally; the original `picardIterate_K1_from_restart`
  (which still names `hprofile_joint` as an explicit input) is kept additively so
  its existing consumers are unchanged.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalPicardIterateSourceC1
import ShenWork.PDE.IntervalHomogeneousQuantBound
import ShenWork.PDE.IntervalDuhamelQuantGain
import ShenWork.PDE.IntervalRestartDerivJointContinuity

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1 duhamelSpectralCoeff)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalSourceCoefficientTimeC1
  (localRestartCoeff restartCosineSeries_hasDerivAt_time)
open ShenWork.IntervalHomogeneousQuantBound
  (eigExpWeight homogeneous_eigenvalue_tsum_le)
open ShenWork.IntervalDuhamelQuantGain
  (duhamelSpectralCoeff_eigenvalue_tsum_tauQuarter_bound)
open ShenWork.IntervalRestartDerivJointContinuity (restartDerivField_continuousOn_joint)
open ShenWork.IntervalMildPicardRegularity
  (logisticSourceFun logisticSourceFun_hasDerivAt_time
   cosineCoeffs_hasDerivAt_of_smooth_param cosineCoeffs_abs_le_of_continuous_bounded)

noncomputable section

namespace ShenWork.IntervalPicardIterateTimeC1

open ShenWork.IntervalSourceCoefficientTimeC1 in
/-- `unitIntervalCosineEigenvalue n ≥ 0`. -/
private theorem eig_nonneg (n : ℕ) : 0 ≤ unitIntervalCosineEigenvalue n := by
  unfold unitIntervalCosineEigenvalue; positivity

/-! ## Step 1 — the homogeneous λ-weight `eigExpWeight` is antitone. -/

/-- `E₂(τ) = ∑'ₙ λₙ e^{−τλₙ}` is antitone on `(0,∞)`: enlarging `τ` shrinks each
summand `λₙ e^{−τλₙ}`, and both series are summable. -/
theorem eigExpWeight_antitone {τ₁ τ₂ : ℝ} (hτ₁ : 0 < τ₁) (hle : τ₁ ≤ τ₂) :
    eigExpWeight τ₂ ≤ eigExpWeight τ₁ := by
  simp only [eigExpWeight]
  refine Summable.tsum_le_tsum (fun n => ?_)
    (ShenWork.IntervalMildRegularityBootstrap.unitIntervalCosineEigenvalue_mul_exp_summable
      (lt_of_lt_of_le hτ₁ hle))
    (ShenWork.IntervalMildRegularityBootstrap.unitIntervalCosineEigenvalue_mul_exp_summable hτ₁)
  have hlam := eig_nonneg n
  refine mul_le_mul_of_nonneg_left ?_ hlam
  exact Real.exp_le_exp_of_le (by nlinarith)

/-! ## Step 2 — the restart time-derivative field, its `HasDerivAt`, and bound. -/

/-- The spectral time-derivative field of the restart representation:
`∂_σ field = ∑'ₙ (a(σ−offset)ₙ − λₙ·localRestartCoeff a₀ a (σ−offset) n)·cos(nπx)`. -/
def restartFieldTimeDeriv (a₀ : ℕ → ℝ) (a : ℝ → ℕ → ℝ) (offset : ℝ)
    (σ x : ℝ) : ℝ :=
  ∑' n, (a (σ - offset) n - unitIntervalCosineEigenvalue n *
    localRestartCoeff a₀ a (σ - offset) n) * cosineMode n x

/-- **Pointwise time derivative of the field.**  Under the restart agreement
`(R)` holding eventually in time, the lifted profile slice is differentiable in
time with derivative the spectral field. -/
theorem restartField_hasDerivAt
    {w : ℝ → intervalDomainPoint → ℝ}
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {offset : ℝ} {σ : ℝ} (hτ : 0 < σ - offset)
    (hagree : ∀ᶠ s in 𝓝 σ, ∀ x : intervalDomainPoint,
      intervalDomainLift (w s) x.1 = ∑' n,
        localRestartCoeff a₀ a (s - offset) n * cosineMode n x.1)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun r => intervalDomainLift (w r) x)
      (restartFieldTimeDeriv a₀ a offset σ x) σ := by
  have hspec := restartCosineSeries_hasDerivAt_time hM₀ ha₀ src hτ x
  have hsub : HasDerivAt (· - offset) 1 σ :=
    (hasDerivAt_id σ).add_const (-offset)
  have hshift := hspec.scomp σ hsub
  simp only [smul_eq_mul, one_mul] at hshift
  -- hshift : HasDerivAt (fun s => ∑' n, localRestartCoeff … (s-offset) … ) (field) σ
  refine hshift.congr_of_eventuallyEq ?_
  refine hagree.mono (fun s hs => ?_)
  have hh := hs ⟨x, hx⟩
  simpa using hh

/-- The explicit Duhamel-gain constant `2·(∑'ₖ 1/((k:ℝ)+1)^{3/2})/π^{3/2}`. -/
def duhamelGainConst : ℝ :=
  2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) / Real.pi ^ ((3 : ℝ) / 2)

/-- The explicit per-`τ` field-derivative bound
`Mdot_u(τ) = (∑'ₖ envelope k) + M₀·E₂(τ) + duhamelGainConst·τ^{1/4}·B`. -/
def restartFieldDerivBound (envSum M₀ B : ℝ) (τ : ℝ) : ℝ :=
  envSum + M₀ * eigExpWeight τ + duhamelGainConst * τ ^ ((1 : ℝ) / 4) * B

/-- **Field-derivative bound (per `τ = σ−offset`).**
`|∂_σ field| ≤ (∑'ₖ envelope k) + M₀·E₂(τ) + duhamelGainConst·τ^{1/4}·B`, using
the ℓ¹ envelope, `homogeneous_eigenvalue_tsum_le`, and
`duhamelSpectralCoeff_eigenvalue_tsum_tauQuarter_bound`. -/
theorem restartFieldTimeDeriv_abs_le
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {B : ℝ} (hB : 0 ≤ B)
    (hdecay : ∀ s, 0 ≤ s → ∀ k : ℕ, 1 ≤ k → |a s k| ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2)
    (hcont : ∀ k, Continuous (fun s => a s k))
    {offset σ : ℝ} (hτ : 0 < σ - offset) (hσnn : 0 ≤ σ - offset)
    (x : ℝ) :
    |restartFieldTimeDeriv a₀ a offset σ x|
      ≤ restartFieldDerivBound (∑' k, src.envelope k) M₀ B (σ - offset) := by
  set τ := σ - offset with hτdef
  have hcos_le : ∀ n, |cosineMode n x| ≤ 1 := fun n => by
    unfold cosineMode; exact Real.abs_cos_le_one _
  have henv_nn : ∀ n, 0 ≤ src.envelope n :=
    fun n => le_trans (abs_nonneg _) (src.henv_bound 0 le_rfl n)
  -- per-mode majorant Sₙ
  set S : ℕ → ℝ := fun n => src.envelope n +
    unitIntervalCosineEigenvalue n *
      |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n| +
    unitIntervalCosineEigenvalue n * |duhamelSpectralCoeff a τ n| with hSdef
  -- summability of the three pieces
  have hsum_env : Summable src.envelope := src.henv_summable
  have hsum_hom : Summable (fun n => unitIntervalCosineEigenvalue n *
      |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|) :=
    ShenWork.IntervalMildRegularityBootstrap.restartHomogeneousCoeff_eigenvalue_summable hτ ha₀
  have hsum_duh : Summable (fun n => unitIntervalCosineEigenvalue n *
      |duhamelSpectralCoeff a τ n|) :=
    ShenWork.IntervalDuhamelClosedC2.duhamelSpectralCoeff_eigenvalue_summable src hτ
  have hsum_S : Summable S := (hsum_env.add hsum_hom).add hsum_duh
  -- termwise: |(aτₙ − λₙcₙ)cos| ≤ Sₙ
  have hterm : ∀ n, |(a τ n - unitIntervalCosineEigenvalue n *
      localRestartCoeff a₀ a τ n) * cosineMode n x| ≤ S n := by
    intro n
    have hlam := eig_nonneg n
    rw [abs_mul]
    refine le_trans (mul_le_of_le_one_right (abs_nonneg _) (hcos_le n)) ?_
    -- |aτₙ − λₙcₙ| ≤ |aτₙ| + λₙ(|e^{-τλ}a₀ₙ| + |duhamelₙ|)
    have hsplit : a τ n - unitIntervalCosineEigenvalue n * localRestartCoeff a₀ a τ n
        = a τ n - unitIntervalCosineEigenvalue n *
            (Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n)
          - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a τ n := by
      simp only [localRestartCoeff]; ring
    rw [hsplit]
    have hb1 : |a τ n| ≤ src.envelope n := src.henv_bound τ hσnn n
    calc |a τ n - unitIntervalCosineEigenvalue n *
              (Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n)
            - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a τ n|
        ≤ |a τ n - unitIntervalCosineEigenvalue n *
              (Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n)|
            + |unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a τ n| :=
          abs_sub _ _
      _ ≤ (|a τ n| + |unitIntervalCosineEigenvalue n *
              (Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n)|)
            + |unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a τ n| := by
          gcongr; exact abs_sub _ _
      _ = (|a τ n| + unitIntervalCosineEigenvalue n *
              |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|)
            + unitIntervalCosineEigenvalue n * |duhamelSpectralCoeff a τ n| := by
          rw [abs_mul (unitIntervalCosineEigenvalue n), abs_of_nonneg hlam,
            abs_mul (unitIntervalCosineEigenvalue n), abs_of_nonneg hlam]
      _ ≤ S n := by
          rw [hSdef]
          exact add_le_add (add_le_add hb1 le_rfl) le_rfl
  -- bound the field's abs by ∑' S
  have hsum_absg : Summable (fun n => ‖(a τ n - unitIntervalCosineEigenvalue n *
      localRestartCoeff a₀ a τ n) * cosineMode n x‖) := by
    refine hsum_S.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    rw [Real.norm_eq_abs]; exact hterm n
  have hfield_le : |restartFieldTimeDeriv a₀ a offset σ x| ≤ ∑' n, S n := by
    unfold restartFieldTimeDeriv
    rw [← hτdef, ← Real.norm_eq_abs]
    refine le_trans (norm_tsum_le_tsum_norm hsum_absg) ?_
    refine Summable.tsum_le_tsum (fun n => ?_) hsum_absg hsum_S
    rw [Real.norm_eq_abs]; exact hterm n
  refine le_trans hfield_le ?_
  -- ∑' S = envSum + ∑'λ|hom| + ∑'λ|duh| ≤ envSum + M₀E₂ + gain·τ^{1/4}·B
  rw [hSdef]
  rw [(hsum_env.add hsum_hom).tsum_add hsum_duh, hsum_env.tsum_add hsum_hom]
  unfold restartFieldDerivBound
  have hhom_le := homogeneous_eigenvalue_tsum_le (τ := τ) (M := M₀) hτ ha₀
  have hduh_le := duhamelSpectralCoeff_eigenvalue_tsum_tauQuarter_bound
    (a := a) (τ := τ) (B := B) hτ hB hdecay hcont
  have hgain_eq : (2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2))
      / Real.pi ^ ((3 : ℝ) / 2)) * τ ^ ((1 : ℝ) / 4) * B
      = duhamelGainConst * τ ^ ((1 : ℝ) / 4) * B := by
    unfold duhamelGainConst; ring
  rw [hgain_eq] at hduh_le
  linarith [hhom_le, hduh_le]

/-- `duhamelGainConst ≥ 0`. -/
theorem duhamelGainConst_nonneg : 0 ≤ duhamelGainConst := by
  unfold duhamelGainConst
  have hpos : 0 ≤ ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2) :=
    tsum_nonneg (fun k => by positivity)
  positivity

/-- The explicit UNIFORM field-derivative bound on the window `σ ∈ Icc t₁ t₂`,
keyed to `τmin = t₁−offset` and `τmax = t₂−offset`:
`UMdot := envSum + M₀·E₂(τmin) + duhamelGainConst·τmax^{1/4}·B`. -/
def restartFieldDerivBoundUnif (envSum M₀ B τmin τmax : ℝ) : ℝ :=
  envSum + M₀ * eigExpWeight τmin + duhamelGainConst * τmax ^ ((1 : ℝ) / 4) * B

/-- **Uniform field-derivative bound on a window.**  For `offset < t₁ ≤ σ ≤ t₂`
the per-`τ` bound is dominated by `restartFieldDerivBoundUnif` evaluated at the
window endpoints, using `eigExpWeight_antitone` and `rpow` monotonicity. -/
theorem restartFieldTimeDeriv_abs_le_unif
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {B : ℝ} (hB : 0 ≤ B)
    (hdecay : ∀ s, 0 ≤ s → ∀ k : ℕ, 1 ≤ k → |a s k| ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2)
    (hcont : ∀ k, Continuous (fun s => a s k))
    {offset t₁ t₂ σ : ℝ} (hoff : offset < t₁) (hσ : σ ∈ Set.Icc t₁ t₂)
    (x : ℝ) :
    |restartFieldTimeDeriv a₀ a offset σ x|
      ≤ restartFieldDerivBoundUnif (∑' k, src.envelope k) M₀ B
          (t₁ - offset) (t₂ - offset) := by
  obtain ⟨hσ1, hσ2⟩ := hσ
  have hτminpos : 0 < t₁ - offset := by linarith
  have hτpos : 0 < σ - offset := by linarith
  have hτnn : 0 ≤ σ - offset := le_of_lt hτpos
  refine le_trans
    (restartFieldTimeDeriv_abs_le ha₀ src hB hdecay hcont hτpos hτnn x) ?_
  unfold restartFieldDerivBound restartFieldDerivBoundUnif
  have hE2 : eigExpWeight (σ - offset) ≤ eigExpWeight (t₁ - offset) :=
    eigExpWeight_antitone hτminpos (by linarith)
  have hpow : (σ - offset) ^ ((1 : ℝ) / 4) ≤ (t₂ - offset) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow hτnn (by linarith) (by norm_num)
  have h1 : M₀ * eigExpWeight (σ - offset) ≤ M₀ * eigExpWeight (t₁ - offset) :=
    mul_le_mul_of_nonneg_left hE2 hM₀
  have h2 : duhamelGainConst * (σ - offset) ^ ((1 : ℝ) / 4) * B
      ≤ duhamelGainConst * (t₂ - offset) ^ ((1 : ℝ) / 4) * B := by
    apply mul_le_mul_of_nonneg_right _ hB
    exact mul_le_mul_of_nonneg_left hpow duhamelGainConst_nonneg
  linarith

/-! ## Step 3 — joint continuity of the field derivative. -/

/-- **Joint continuity of `∂_σ field`.**  The restart time-derivative field
`(σ,x) ↦ restartFieldTimeDeriv a₀ a offset σ x` is jointly continuous on
`Ioi offset ×ˢ univ`, by composing `restartDerivField_continuousOn_joint`
with the affine shift `σ ↦ σ − offset`. -/
theorem restartFieldTimeDeriv_continuousOn_joint
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a) (offset : ℝ) :
    ContinuousOn (Function.uncurry (fun σ x => restartFieldTimeDeriv a₀ a offset σ x))
      (Set.Ioi offset ×ˢ Set.univ) := by
  have hbase := restartDerivField_continuousOn_joint hM₀ ha₀ src
  -- shift map (σ,x) ↦ (σ-offset, x)
  have hshift : ContinuousOn
      (fun p : ℝ × ℝ => ((p.1 - offset, p.2) : ℝ × ℝ))
      (Set.Ioi offset ×ˢ Set.univ) :=
    ((continuous_fst.sub continuous_const).prodMk continuous_snd).continuousOn
  have hmaps : Set.MapsTo (fun p : ℝ × ℝ => ((p.1 - offset, p.2) : ℝ × ℝ))
      (Set.Ioi offset ×ˢ Set.univ) (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
    intro p hp
    refine Set.mk_mem_prod ?_ (Set.mem_univ _)
    exact Set.mem_Ioi.2 (by have := (Set.mem_prod.1 hp).1; simp only [Set.mem_Ioi] at this ⊢; linarith)
  have hcomp := hbase.comp hshift hmaps
  refine hcomp.congr (fun p hp => ?_)
  rfl

/-- **Joint continuity of the restart VALUE series field.**  The offset-shifted
restart cosine series `(σ,x) ↦ ∑'ₙ localRestartCoeff a₀ a (σ−offset) n·cos(nπx)`
is jointly continuous on `Ioi offset ×ˢ univ`, by composing the value-series
joint-continuity atom
`ShenWork.IntervalSourceCoefficientTimeC1.restartSeries_jointContinuousOn`
(the value-field analogue of `restartDerivField_continuousOn_joint`) with the
affine shift `σ ↦ σ − offset`.  This is the same machinery as the derivative
field, exactly as anticipated in the header §"Named satisfiable hypothesis". -/
theorem restartValueSeries_continuousOn_joint
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a) (offset : ℝ) :
    ContinuousOn (Function.uncurry (fun σ x =>
        ∑' n, localRestartCoeff a₀ a (σ - offset) n * cosineMode n x))
      (Set.Ioi offset ×ˢ Set.univ) := by
  have hbase :=
    ShenWork.IntervalSourceCoefficientTimeC1.restartSeries_jointContinuousOn hM₀ ha₀ src
  -- shift map (σ,x) ↦ (σ-offset, x)
  have hshift : ContinuousOn
      (fun p : ℝ × ℝ => ((p.1 - offset, p.2) : ℝ × ℝ))
      (Set.Ioi offset ×ˢ Set.univ) :=
    ((continuous_fst.sub continuous_const).prodMk continuous_snd).continuousOn
  have hmaps : Set.MapsTo (fun p : ℝ × ℝ => ((p.1 - offset, p.2) : ℝ × ℝ))
      (Set.Ioi offset ×ˢ Set.univ) (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
    intro p hp
    refine Set.mk_mem_prod ?_ (Set.mem_univ _)
    exact Set.mem_Ioi.2 (by have := (Set.mem_prod.1 hp).1; simp only [Set.mem_Ioi] at this ⊢; linarith)
  have hcomp := hbase.comp hshift hmaps
  refine hcomp.congr (fun p hp => ?_)
  rfl

/-- **Discharge of `hprofile_joint`.**  On a closed slab `Icc (σ-δ) (σ+δ) ⊆ U`
inside an open restart window `U ⊆ Ioi offset`, the lifted profile slice
`(s,x) ↦ intervalDomainLift (w s) x` is jointly continuous on
`Icc (σ-δ) (σ+δ) ×ˢ Icc 0 1`.  This is the previously named hypothesis
`hprofile_joint`, now proved: the restart agreement `(R)` rewrites the lifted
slice to the value series on the slab, whose joint continuity is
`restartValueSeries_continuousOn_joint`. -/
theorem restartProfile_jointContinuousOn
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {w : ℝ → intervalDomainPoint → ℝ} {offset σ δ : ℝ}
    (hslab_off : Set.Icc (σ - δ) (σ + δ) ⊆ Set.Ioi offset)
    (hagree : ∀ s ∈ Set.Icc (σ - δ) (σ + δ), ∀ x : intervalDomainPoint,
      intervalDomainLift (w s) x.1 = ∑' n,
        localRestartCoeff a₀ a (s - offset) n * cosineMode n x.1) :
    ContinuousOn
      (Function.uncurry (fun s x => intervalDomainLift (w s) x))
      (Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0 : ℝ) 1) := by
  -- restrict the value-series joint continuity to the slab×[0,1]
  have hseries : ContinuousOn
      (Function.uncurry (fun s x =>
        ∑' n, localRestartCoeff a₀ a (s - offset) n * cosineMode n x))
      (Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0 : ℝ) 1) := by
    refine (restartValueSeries_continuousOn_joint hM₀ ha₀ src offset).mono ?_
    intro q hq
    obtain ⟨hq1, _⟩ := Set.mem_prod.1 hq
    exact Set.mk_mem_prod (hslab_off hq1) (Set.mem_univ _)
  -- congr: on the slab×[0,1], the lifted slice equals the series (via `hagree`)
  refine hseries.congr (fun q hq => ?_)
  obtain ⟨hq1, hq2⟩ := Set.mem_prod.1 hq
  simpa only [Function.uncurry] using hagree q.1 hq1 ⟨q.2, hq2⟩

/-! ## Step 4 — the logistic `K1` package via the chain rule. -/

/-- The explicit time-derivative of the logistic source slice:
`∂_σ L(w σ)(x) = ∂_σ field(σ,x) · (a − b(1+α)(lift(w σ) x)^α)`. -/
def logisticSourceDot (a₀ : ℕ → ℝ) (a : ℝ → ℕ → ℝ) (p : CM2Params)
    (w : ℝ → intervalDomainPoint → ℝ) (offset : ℝ) (σ x : ℝ) : ℝ :=
  restartFieldTimeDeriv a₀ a offset σ x *
    (p.a - p.b * (1 + p.α) * (intervalDomainLift (w σ) x) ^ p.α)

/-- **The logistic `K1` `HasDerivAt`.**  For each `σ` in an open restart window
`U` and each mode `k`, the source coefficient `cosineCoeffs (L(w·)) k` is
differentiable in time with derivative `cosineCoeffs (logisticSourceDot … σ ·) k`.

Inputs: open `U ∋ σ`, `U ⊆ Ioi offset`, the restart agreement on `U`, the
positivity floor on the window×Icc, and the named profile joint-continuity
`hprofile_joint` (header §"Named satisfiable hypothesis"). -/
theorem logisticSource_adot_hasDerivAt
    {p : CM2Params} (hα : 0 < p.α)
    {w : ℝ → intervalDomainPoint → ℝ}
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {offset σ : ℝ}
    {U : Set ℝ} (hU_open : IsOpen U) (hσU : σ ∈ U) (hU_off : U ⊆ Set.Ioi offset)
    (hagree : ∀ s ∈ U, ∀ x : intervalDomainPoint,
      intervalDomainLift (w s) x.1 = ∑' n,
        localRestartCoeff a₀ a (s - offset) n * cosineMode n x.1)
    (hpos : ∀ s ∈ U, ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (w s) x)
    (hC2cont : ∀ s ∈ U, ContinuousOn (intervalDomainLift (w s)) (Set.Icc (0 : ℝ) 1))
    {δ : ℝ} (hδ : 0 < δ) (hball : Metric.ball σ δ ⊆ U)
    (hslab : Set.Icc (σ - δ) (σ + δ) ⊆ U)
    (hprofile_joint : ContinuousOn
      (Function.uncurry (fun s x => intervalDomainLift (w s) x))
      (Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0 : ℝ) 1))
    (k : ℕ) :
    HasDerivAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (w r))) k)
      (cosineCoeffs (fun x => logisticSourceDot a₀ a p w offset σ x) k) σ := by
  set f : ℝ → ℝ → ℝ := fun s x =>
    logisticSourceFun p.a p.b p.α (intervalDomainLift (w s)) x with hfdef
  set f' : ℝ → ℝ → ℝ := fun s x => logisticSourceDot a₀ a p w offset s x with hf'def
  -- (hf_cont) slice continuity near σ
  have hf_cont : ∀ᶠ s in 𝓝 σ, ContinuousOn (f s) (Set.Icc (0 : ℝ) 1) := by
    refine Filter.eventually_of_mem (hU_open.mem_nhds hσU) (fun s hs => ?_)
    have hgc : ContinuousOn (intervalDomainLift (w s)) (Set.Icc (0:ℝ) 1) := hC2cont s hs
    have hpos' : ∀ x, x ∈ Set.Icc (0:ℝ) 1 → intervalDomainLift (w s) x ≠ 0 :=
      fun x hx => ne_of_gt (hpos s hs x hx)
    simp only [hfdef, logisticSourceFun]
    apply ContinuousOn.mul hgc
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.mul continuousOn_const
    exact ContinuousOn.rpow_const hgc (fun x hx => Or.inl (hpos' x hx))
  -- convert per-slice ContinuousOn to IntervalIntegrable for the engine
  have hf_int : ∀ᶠ s in 𝓝 σ, IntervalIntegrable (f s) MeasureTheory.volume (0 : ℝ) 1 := by
    filter_upwards [hf_cont] with s hs
    rw [← Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    exact hs.intervalIntegrable
  -- (h_diff) pointwise HasDerivAt of f via the chain rule
  have h_diff : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball σ δ,
      HasDerivAt (fun r => f r x) (f' s x) s := by
    intro x hx s hs
    have hsU : s ∈ U := hball hs
    have hxIcc : x ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hx
    have hτ : 0 < s - offset := by
      have := hU_off hsU; exact sub_pos.2 (Set.mem_Ioi.1 this)
    -- field HasDerivAt at s (agreement holds on a neighborhood of s)
    have hfield : HasDerivAt (fun r => intervalDomainLift (w r) x)
        (restartFieldTimeDeriv a₀ a offset s x) s := by
      refine restartField_hasDerivAt hM₀ ha₀ src hτ ?_ x hxIcc
      exact Filter.eventually_of_mem (hU_open.mem_nhds hsU)
        (fun s' hs' => hagree s' hs')
    have hpos_s : 0 < intervalDomainLift (w s) x := hpos s hsU x hxIcc
    have hchain := logisticSourceFun_hasDerivAt_time (a := p.a) (b := p.b)
      (α := p.α) hα (f := fun r => intervalDomainLift (w r) x)
      (f' := restartFieldTimeDeriv a₀ a offset s x) (σ := s) hpos_s hfield
    simp only [hfdef, hf'def, logisticSourceFun, logisticSourceDot]
    exact hchain
  -- (h_cont_deriv) joint continuity of f' on the slab
  have h_cont_deriv : ContinuousOn (Function.uncurry f')
      (Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0 : ℝ) 1) := by
    have hfieldjoint : ContinuousOn
        (Function.uncurry (fun s x => restartFieldTimeDeriv a₀ a offset s x))
        (Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0 : ℝ) 1) := by
      refine (restartFieldTimeDeriv_continuousOn_joint hM₀ ha₀ src offset).mono ?_
      intro q hq
      obtain ⟨hq1, _⟩ := Set.mem_prod.1 hq
      have hqU : q.1 ∈ U := hslab hq1
      exact Set.mk_mem_prod (hU_off hqU) (Set.mem_univ _)
    have hpowjoint : ContinuousOn
        (Function.uncurry (fun s x => (intervalDomainLift (w s) x) ^ p.α))
        (Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0 : ℝ) 1) := by
      have hne : ∀ q ∈ Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0 : ℝ) 1,
          intervalDomainLift (w q.1) q.2 ≠ 0 := by
        intro q hq
        obtain ⟨hq1, hq2⟩ := Set.mem_prod.1 hq
        exact ne_of_gt (hpos q.1 (hslab hq1) q.2 hq2)
      exact ContinuousOn.rpow_const hprofile_joint (fun q hq => Or.inl (hne q hq))
    simp only [hf'def, logisticSourceDot]
    change ContinuousOn (fun q : ℝ × ℝ =>
        restartFieldTimeDeriv a₀ a offset q.1 q.2 *
          (p.a - p.b * (1 + p.α) * (intervalDomainLift (w q.1) q.2) ^ p.α)) _
    exact hfieldjoint.mul
      ((continuousOn_const).sub (continuousOn_const.mul hpowjoint))
  -- assemble via the time-Leibniz rule
  have hkey := cosineCoeffs_hasDerivAt_of_smooth_param (f := f) (f' := f')
    (τ := σ) (δ := δ) (n := k) hδ hf_int h_diff h_cont_deriv
  simpa only [hfdef, hf'def] using hkey

/-- The logistic derivative coefficient `L'(z) = a − b(1+α)z^α` is bounded by
`a + b(1+α)M^α` in absolute value on `(0,M]`. -/
theorem logisticDerivFactor_abs_le
    {p : CM2Params} (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {M z : ℝ} (hz0 : 0 < z) (hzM : z ≤ M) :
    |p.a - p.b * (1 + p.α) * z ^ p.α| ≤ p.a + p.b * (1 + p.α) * M ^ p.α := by
  have hαnn : 0 ≤ p.α := le_trans zero_le_one hα
  have h1α : 0 ≤ 1 + p.α := by linarith
  have hMpos : 0 < M := lt_of_lt_of_le hz0 hzM
  have hzpow_nn : 0 ≤ z ^ p.α := Real.rpow_nonneg (le_of_lt hz0) _
  have hpow_le : z ^ p.α ≤ M ^ p.α := Real.rpow_le_rpow (le_of_lt hz0) hzM hαnn
  have hterm_nn : 0 ≤ p.b * (1 + p.α) * z ^ p.α := by positivity
  have hterm_le : p.b * (1 + p.α) * z ^ p.α ≤ p.b * (1 + p.α) * M ^ p.α := by
    apply mul_le_mul_of_nonneg_left hpow_le; positivity
  rw [abs_le]
  constructor
  · have : p.a + p.b * (1 + p.α) * M ^ p.α ≥ 0 := by positivity
    linarith
  · linarith

/-- Continuity of the logistic source slice derivative `logisticSourceDot … σ ·`
on `[0,1]` (the slab joint-continuity restricted to the time `σ`). -/
theorem logisticSourceDot_continuousOn
    {p : CM2Params}
    {w : ℝ → intervalDomainPoint → ℝ}
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {offset σ : ℝ} (_hσoff : offset < σ)
    {δ : ℝ} (_hδ : 0 < δ) (hσδ : σ ∈ Set.Icc (σ - δ) (σ + δ))
    (hslab_off : Set.Icc (σ - δ) (σ + δ) ⊆ Set.Ioi offset)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (w σ) x)
    (hprofile_joint : ContinuousOn
      (Function.uncurry (fun s x => intervalDomainLift (w s) x))
      (Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun x => logisticSourceDot a₀ a p w offset σ x)
      (Set.Icc (0 : ℝ) 1) := by
  -- field-deriv part: slab joint continuity restricted to {σ}
  have hfield_x : ContinuousOn
      (fun x => restartFieldTimeDeriv a₀ a offset σ x) (Set.Icc (0 : ℝ) 1) := by
    have hjoint := restartFieldTimeDeriv_continuousOn_joint hM₀ ha₀ src offset
    have hsub : ContinuousOn
        (Function.uncurry (fun s x => restartFieldTimeDeriv a₀ a offset s x))
        (Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0 : ℝ) 1) := by
      refine hjoint.mono ?_
      intro q hq
      obtain ⟨hq1, _⟩ := Set.mem_prod.1 hq
      exact Set.mk_mem_prod (hslab_off hq1) (Set.mem_univ _)
    have := hsub.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x hx => Set.mk_mem_prod hσδ hx)
    exact this
  -- profile slice part
  have hprof_x : ContinuousOn (fun x => intervalDomainLift (w σ) x)
      (Set.Icc (0 : ℝ) 1) := by
    have := hprofile_joint.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x hx => Set.mk_mem_prod hσδ hx)
    exact this
  have hne : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (w σ) x ≠ 0 :=
    fun x hx => ne_of_gt (hpos x hx)
  simp only [logisticSourceDot]
  apply hfield_x.mul
  apply ContinuousOn.sub continuousOn_const
  apply ContinuousOn.mul continuousOn_const
  exact ContinuousOn.rpow_const hprof_x (fun x hx => Or.inl (hne x hx))

/-- The explicit uniform source-coefficient derivative bound on the window:
`Mdot := 2·(a + b(1+α)·M^α)·UMdot`. -/
def logisticSourceMdot (p : CM2Params) (M UMdot : ℝ) : ℝ :=
  2 * (p.a + p.b * (1 + p.α) * M ^ p.α) * UMdot

/-- **Uniform bound on the logistic `K1` derivative coefficient.**
`|adot σ k| = |cosineCoeffs (logisticSourceDot … σ ·) k| ≤ 2·(a + b(1+α)M^α)·UMdot`
via `cosineCoeffs_abs_le_of_continuous_bounded`, the slice-derivative sup bound
`UMdot`, and `logisticDerivFactor_abs_le`. -/
theorem logisticSource_adot_abs_le
    {p : CM2Params} (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {w : ℝ → intervalDomainPoint → ℝ}
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {B : ℝ} (hB : 0 ≤ B)
    (hdecay : ∀ s, 0 ≤ s → ∀ k : ℕ, 1 ≤ k → |a s k| ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2)
    (hcont : ∀ k, Continuous (fun s => a s k))
    {offset t₁ t₂ σ : ℝ} (hoff : offset < t₁) (hσ : σ ∈ Set.Icc t₁ t₂)
    {M : ℝ}
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (w σ) x)
    (hub : ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (w σ) x ≤ M)
    {δ : ℝ} (hδ : 0 < δ) (hσδ : σ ∈ Set.Icc (σ - δ) (σ + δ))
    (hslab_off : Set.Icc (σ - δ) (σ + δ) ⊆ Set.Ioi offset)
    (hprofile_joint : ContinuousOn
      (Function.uncurry (fun s x => intervalDomainLift (w s) x))
      (Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0 : ℝ) 1))
    (k : ℕ) :
    |cosineCoeffs (fun x => logisticSourceDot a₀ a p w offset σ x) k|
      ≤ logisticSourceMdot p M
          (restartFieldDerivBoundUnif (∑' j, src.envelope j) M₀ B
            (t₁ - offset) (t₂ - offset)) := by
  set UMdot := restartFieldDerivBoundUnif (∑' j, src.envelope j) M₀ B
    (t₁ - offset) (t₂ - offset) with hUdef
  have hUnn : 0 ≤ UMdot := by
    have := restartFieldTimeDeriv_abs_le_unif hM₀ ha₀ src hB hdecay hcont hoff hσ 0
    exact le_trans (abs_nonneg _) (by rw [hUdef]; exact this)
  set Bfac : ℝ := p.a + p.b * (1 + p.α) * M ^ p.α with hBfacdef
  have hBfac_nn : 0 ≤ Bfac := by
    have hMnn : 0 ≤ M := le_trans (le_of_lt (hpos 0 (by constructor <;> norm_num)))
      (hub 0 (by constructor <;> norm_num))
    rw [hBfacdef]; positivity
  -- sup bound on the integrand
  have hsup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |logisticSourceDot a₀ a p w offset σ x| ≤ Bfac * UMdot := by
    intro x hx
    simp only [logisticSourceDot, abs_mul]
    have hfb : |restartFieldTimeDeriv a₀ a offset σ x| ≤ UMdot := by
      rw [hUdef]
      exact restartFieldTimeDeriv_abs_le_unif hM₀ ha₀ src hB hdecay hcont hoff hσ x
    have hfactor : |p.a - p.b * (1 + p.α) * (intervalDomainLift (w σ) x) ^ p.α|
        ≤ Bfac := by
      rw [hBfacdef]
      exact logisticDerivFactor_abs_le hα ha hb (hpos x hx) (hub x hx)
    calc |restartFieldTimeDeriv a₀ a offset σ x| *
            |p.a - p.b * (1 + p.α) * (intervalDomainLift (w σ) x) ^ p.α|
        ≤ UMdot * Bfac :=
          mul_le_mul hfb hfactor (abs_nonneg _) hUnn
      _ = Bfac * UMdot := by ring
  have hcont_dot : ContinuousOn (fun x => logisticSourceDot a₀ a p w offset σ x)
      (Set.Icc (0 : ℝ) 1) :=
    logisticSourceDot_continuousOn hM₀ ha₀ src (lt_of_lt_of_le hoff hσ.1)
      hδ hσδ hslab_off hpos hprofile_joint
  have hBU_nn : 0 ≤ Bfac * UMdot := mul_nonneg hBfac_nn hUnn
  have hcoeff := cosineCoeffs_abs_le_of_continuous_bounded
    (f := fun x => logisticSourceDot a₀ a p w offset σ x)
    hcont_dot hBU_nn hsup k
  rw [logisticSourceMdot, ← hBfacdef]
  calc |cosineCoeffs (fun x => logisticSourceDot a₀ a p w offset σ x) k|
      ≤ 2 * (Bfac * UMdot) := hcoeff
    _ = 2 * Bfac * UMdot := by ring

/-! ## Step 5 — master `K1` discharge over an open restart window. -/

/-- **M3b master: the `K1` package from a restart representation.**

Given an open restart window `U` (with `t₁ ≤ U`-points and `U ⊆ Ioi offset`),
the restart agreement `(R)` on `U`, the `(K2)` slice data (positivity floor, sup
bound `M`, slice continuity), and the named profile joint-continuity
`hprofile_joint` (header §"Named satisfiable hypothesis"), the logistic source
coefficient family

    a σ k = cosineCoeffs (logisticSourceFun p.a p.b p.α (lift(w σ))) k

is time-`C¹` on `U` with EXPLICIT derivative family
`adot σ k := cosineCoeffs (logisticSourceDot … σ ·) k`, EXPLICIT uniform bound
`Mdot := logisticSourceMdot p M UMdot`, and time-continuity on `U`.

These are exactly M3's `K1` fields restricted to the (interior) restart window;
the global statements M3 states for all `σ` follow by taking `U` to be the full
interior time interval of the iterate's restart representation. -/
theorem picardIterate_K1_from_restart
    {p : CM2Params} (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {w : ℝ → intervalDomainPoint → ℝ}
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {B : ℝ} (hB : 0 ≤ B)
    (hdecay : ∀ s, 0 ≤ s → ∀ k : ℕ, 1 ≤ k → |a s k| ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2)
    (hcont : ∀ k, Continuous (fun s => a s k))
    {offset t₁ t₂ : ℝ} (hoff : offset < t₁) (_ht : t₁ ≤ t₂)
    {U : Set ℝ} (hU_open : IsOpen U) (hU_sub : U ⊆ Set.Ioo t₁ t₂)
    (hU_off : U ⊆ Set.Ioi offset)
    (hagree : ∀ s ∈ U, ∀ x : intervalDomainPoint,
      intervalDomainLift (w s) x.1 = ∑' n,
        localRestartCoeff a₀ a (s - offset) n * cosineMode n x.1)
    {M : ℝ}
    (hpos : ∀ s ∈ U, ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (w s) x)
    (hub : ∀ s ∈ U, ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (w s) x ≤ M)
    (hC2cont : ∀ s ∈ U, ContinuousOn (intervalDomainLift (w s)) (Set.Icc (0 : ℝ) 1))
    (hprofile_joint : ContinuousOn
      (Function.uncurry (fun s x => intervalDomainLift (w s) x))
      (U ×ˢ Set.Icc (0 : ℝ) 1)) :
    -- the explicit derivative family
    (∀ σ ∈ U, ∀ k, HasDerivAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (w r))) k)
      (cosineCoeffs (fun x => logisticSourceDot a₀ a p w offset σ x) k) σ)
    ∧ (∀ σ ∈ U, ∀ k,
        |cosineCoeffs (fun x => logisticSourceDot a₀ a p w offset σ x) k|
          ≤ logisticSourceMdot p M
              (restartFieldDerivBoundUnif (∑' j, src.envelope j) M₀ B
                (t₁ - offset) (t₂ - offset))) := by
  have hαpos : 0 < p.α := lt_of_lt_of_le one_pos hα
  refine ⟨?_, ?_⟩
  · -- HasDerivAt: extract δ from U open at σ, build a closed slab inside U
    intro σ hσU k
    obtain ⟨ε, hεpos, hball_ε⟩ := Metric.isOpen_iff.1 hU_open σ hσU
    set δ := ε / 2 with hδdef
    have hδ : 0 < δ := by positivity
    have hslab : Set.Icc (σ - δ) (σ + δ) ⊆ U := by
      intro y hy
      apply hball_ε
      rw [Metric.mem_ball, Real.dist_eq]
      obtain ⟨hy1, hy2⟩ := hy
      rw [abs_lt]; rw [hδdef] at hy1 hy2; constructor <;> linarith
    have hball : Metric.ball σ δ ⊆ U :=
      (Metric.ball_subset_ball (by rw [hδdef]; linarith)).trans hball_ε
    exact logisticSource_adot_hasDerivAt hαpos hM₀ ha₀ src hU_open hσU hU_off
      hagree hpos hC2cont hδ hball hslab
      (hprofile_joint.mono (Set.prod_mono hslab (subset_refl _))) k
  · -- bound: instantiate the uniform window bound at σ
    intro σ hσU k
    obtain ⟨ε, hεpos, hball_ε⟩ := Metric.isOpen_iff.1 hU_open σ hσU
    set δ := ε / 2 with hδdef
    have hδ : 0 < δ := by positivity
    have hslab : Set.Icc (σ - δ) (σ + δ) ⊆ U := by
      intro y hy
      apply hball_ε
      rw [Metric.mem_ball, Real.dist_eq]
      obtain ⟨hy1, hy2⟩ := hy
      rw [abs_lt]; rw [hδdef] at hy1 hy2; constructor <;> linarith
    have hσδ : σ ∈ Set.Icc (σ - δ) (σ + δ) := ⟨by linarith, by linarith⟩
    have hσIcc : σ ∈ Set.Icc t₁ t₂ := by
      have := hU_sub hσU; exact ⟨le_of_lt this.1, le_of_lt this.2⟩
    exact logisticSource_adot_abs_le hα ha hb hM₀ ha₀ src hB hdecay hcont
      hoff hσIcc (hpos σ hσU) (hub σ hσU) hδ hσδ
      (hslab.trans hU_off)
      (hprofile_joint.mono (Set.prod_mono hslab (subset_refl _))) k

/-- **M3b master, `hprofile_joint`-free.**  Identical to
`picardIterate_K1_from_restart` but with the previously-named profile
joint-continuity hypothesis DISCHARGED internally: on each open-window point `σ`
we build the slab and obtain `hprofile_joint` on the slab from the restart
agreement via `restartProfile_jointContinuousOn` (Step 3).  This is the
additive `_of_representation` form taking only Front A's satisfiable inputs
(the restart representation `(R)` + the `(K2)` slice data); the global
`U ×ˢ Icc 0 1` joint-continuity input is no longer required. -/
theorem picardIterate_K1_from_restart_of_representation
    {p : CM2Params} (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {w : ℝ → intervalDomainPoint → ℝ}
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {B : ℝ} (hB : 0 ≤ B)
    (hdecay : ∀ s, 0 ≤ s → ∀ k : ℕ, 1 ≤ k → |a s k| ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2)
    (hcont : ∀ k, Continuous (fun s => a s k))
    {offset t₁ t₂ : ℝ} (hoff : offset < t₁) (_ht : t₁ ≤ t₂)
    {U : Set ℝ} (hU_open : IsOpen U) (hU_sub : U ⊆ Set.Ioo t₁ t₂)
    (hU_off : U ⊆ Set.Ioi offset)
    (hagree : ∀ s ∈ U, ∀ x : intervalDomainPoint,
      intervalDomainLift (w s) x.1 = ∑' n,
        localRestartCoeff a₀ a (s - offset) n * cosineMode n x.1)
    {M : ℝ}
    (hpos : ∀ s ∈ U, ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (w s) x)
    (hub : ∀ s ∈ U, ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (w s) x ≤ M)
    (hC2cont : ∀ s ∈ U, ContinuousOn (intervalDomainLift (w s)) (Set.Icc (0 : ℝ) 1)) :
    (∀ σ ∈ U, ∀ k, HasDerivAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (w r))) k)
      (cosineCoeffs (fun x => logisticSourceDot a₀ a p w offset σ x) k) σ)
    ∧ (∀ σ ∈ U, ∀ k,
        |cosineCoeffs (fun x => logisticSourceDot a₀ a p w offset σ x) k|
          ≤ logisticSourceMdot p M
              (restartFieldDerivBoundUnif (∑' j, src.envelope j) M₀ B
                (t₁ - offset) (t₂ - offset))) := by
  have hαpos : 0 < p.α := lt_of_lt_of_le one_pos hα
  -- per-σ slab + the discharged profile joint-continuity on that slab
  have hslab_of : ∀ σ ∈ U, ∃ δ : ℝ, 0 < δ ∧
      Metric.ball σ δ ⊆ U ∧ Set.Icc (σ - δ) (σ + δ) ⊆ U ∧
      ContinuousOn (Function.uncurry (fun s x => intervalDomainLift (w s) x))
        (Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro σ hσU
    obtain ⟨ε, hεpos, hball_ε⟩ := Metric.isOpen_iff.1 hU_open σ hσU
    refine ⟨ε / 2, by positivity, ?_, ?_, ?_⟩
    · exact (Metric.ball_subset_ball (by linarith)).trans hball_ε
    · intro y hy
      apply hball_ε
      rw [Metric.mem_ball, Real.dist_eq]
      obtain ⟨hy1, hy2⟩ := hy; rw [abs_lt]; constructor <;> linarith
    · have hslab : Set.Icc (σ - ε / 2) (σ + ε / 2) ⊆ U := by
        intro y hy
        apply hball_ε
        rw [Metric.mem_ball, Real.dist_eq]
        obtain ⟨hy1, hy2⟩ := hy; rw [abs_lt]; constructor <;> linarith
      exact restartProfile_jointContinuousOn hM₀ ha₀ src (hslab.trans hU_off)
        (fun s hs x => hagree s (hslab hs) x)
  refine ⟨?_, ?_⟩
  · intro σ hσU k
    obtain ⟨δ, hδ, hball, hslab, hpj⟩ := hslab_of σ hσU
    exact logisticSource_adot_hasDerivAt hαpos hM₀ ha₀ src hU_open hσU hU_off
      hagree hpos hC2cont hδ hball hslab hpj k
  · intro σ hσU k
    obtain ⟨δ, hδ, _hball, hslab, hpj⟩ := hslab_of σ hσU
    have hσδ : σ ∈ Set.Icc (σ - δ) (σ + δ) := ⟨by linarith, by linarith⟩
    have hσIcc : σ ∈ Set.Icc t₁ t₂ := by
      have := hU_sub hσU; exact ⟨le_of_lt this.1, le_of_lt this.2⟩
    exact logisticSource_adot_abs_le hα ha hb hM₀ ha₀ src hB hdecay hcont
      hoff hσIcc (hpos σ hσU) (hub σ hσU) hδ hσδ (hslab.trans hU_off) hpj k

end ShenWork.IntervalPicardIterateTimeC1
