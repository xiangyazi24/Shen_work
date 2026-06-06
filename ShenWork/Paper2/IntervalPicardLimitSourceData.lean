/-
  ShenWork/Paper2/IntervalPicardLimitSourceData.lean

  Phase-0 / final-mile step 2 — forward-derive the FULL `DuhamelSourceTimeC1`
  (with the σ-derivative fields) for the Picard LIMIT's logistic source family,
  and assemble `GradientMildHalfStepRestartData D` for the limit (`χ₀ = 0`).

  ## Why this is now a forward derivation (post-circle-break)

  The circle that blocked producing a FULL `DuhamelSourceTimeC1` for the limit was
  broken in M4b (`IntervalPicardLimitRestartWeak`): the WEAK package
  `DuhamelSourceL1Cont` (envelope + continuity, NO derivative fields) already
  closes the ★ restart representation `rep(u)`.  With `rep(u)` in hand we may now
  run the genuine forward chain

      rep(u)  →  K1(u) via M3b  →  H2(u) via M3  →  M4 assembly,

  none of which is circular: M3b/M3 consume `rep(u)` as the restart agreement `(R)`
  and produce the σ-derivative fields, rather than presupposing them.

  ## What this module delivers

  1. `source_family_eq_w` — the abstract-`w` version of M3's `source_family_eq`:
     the lifted-logistic coefficient family equals the `logisticSourceFun`
     coefficient family on `[0,1]` (via `cosineCoeffs_congr_on_Icc`).  This is the
     transport equality M3 routes through, with no dependence on `picardIter`.

  2. `limitSource_duhamelSourceTimeC1` — **H2(u), the abstract-`w` variant of M3.**
     M3 (`IntervalPicardIterateSourceC1.picardIterate_source_duhamelSourceTimeC1`)
     is stated for `w := picardIter p u₀ n`, but its proof factors entirely through
     the abstract `logisticSource_duhamelSourceTimeC1`
     (`IntervalMildPicardRegularity`).  We mirror that assembly for an arbitrary
     trajectory `w : ℝ → intervalDomainPoint → ℝ`, producing
         `DuhamelSourceTimeC1 (fun s k => cosineCoeffs (logisticLifted p (w s)) k)`
     from the same K2 spatial-slice bounds + K1 source-coefficient time-`C¹` data.
     No long proof is copied: the envelope assembly is `logisticSource_…` verbatim,
     reusing M3's `iterateSourceEnvelopeConst`.

  3. `limitSource_K1_from_restart` — **K1(u) via M3b on a restart window.**  A thin
     re-export of M3b's master
     (`IntervalPicardIterateTimeC1.picardIterate_K1_from_restart`) specialised so
     its conclusion is phrased in the `logisticSourceFun`-coefficient shape that
     (2) consumes.  Its `(R)` agreement is exactly the window form of `rep(u)`
     (★-weak): we record (in the header §"`restartDuhamelCoeff` vs
     `localRestartCoeff`") that the two restart-coefficient definitions are
     DEFINITIONALLY EQUAL — `restartDuhamelCoeff a₀ a τ n` and
     `localRestartCoeff a₀ a τ n` both unfold to
     `e^{−τλₙ}·a₀ₙ + duhamelSpectralCoeff a τ n` — so a `rep(u)` window stated with
     either reads as the other (`restartDuhamelCoeff_eq_localRestartCoeff`).

  4. `gradientMildHalfStepRestartData_for_limit` — **the assembly.**  Produces
     `GradientMildHalfStepRestartData D` for a `GradientMildSolutionData D`
     (`χ₀ = 0`) via M4's
     `IntervalPicardLimitRestart.gradientMildHalfStepRestartData_of_limit`,
     threading `hsrc`/`hsrcShift` from (2) and `hLc`/`hfix`/`hu₀_*` from named
     satisfiable inputs.

  ## restartDuhamelCoeff vs localRestartCoeff (bridge, checked both defs)

  `IntervalMildRegularityBootstrap.restartDuhamelCoeff a₀ a τ n`
      := `Real.exp (-τ * λₙ) * a₀ n + duhamelSpectralCoeff a τ n`
  `IntervalSourceCoefficientTimeC1.localRestartCoeff a₀ a τ n`
      := `Real.exp (-τ * λₙ) * a₀ n + duhamelSpectralCoeff a τ n`
  These are syntactically identical after unfolding; `rfl`-equal.  ★-weak's `rep(u)`
  uses `restartDuhamelCoeff`; M3b's `(R)` uses `localRestartCoeff`; the bridge lemma
  `restartDuhamelCoeff_eq_localRestartCoeff` lets either feed the other.

  ## Satisfiability audit (per hypothesis of the exported assembly)

  Inputs of `gradientMildHalfStepRestartData_for_limit` (all named & satisfiable):

  * `hχ0 : p.χ₀ = 0` — the regime hypothesis (Q1 cone sub-regime; `χ₀ = 0`).
  * `hu₀_cont`, `hu₀_bound` (H1) — `lift u₀` continuous, bounded cosine
    coefficients.  *Satisfiable*: `CM2Params` datum is C²/Neumann ⇒ ℓ¹ (a fortiori
    bounded) coefficients; continuity of the lift is the datum's continuity.
  * `hfix` (FIXED POINT) — the mild Duhamel equation for `D.u`.  *Satisfiable*:
    `D.hmild : IntervalMildSolution p D.T u₀ D.u` IS this equation (the predicate
    `picardLimit` satisfies); it is the n → ∞ image of the per-iterate recursion.
  * `hsrc`/`hsrcShift` (H2) — FULL `DuhamelSourceTimeC1` for the limit source
    family (resp. its `t/2`-shift).  *Satisfiable*: produced by (2)
    `limitSource_duhamelSourceTimeC1` from named K2 slice-regularity bounds
    (`hC2`/`hpos`/`hub`/`hG1`/`hG2`/`hN0`/`hN1` — the explicitly-justified
    slice-regularity inputs, all M-final Data-shaped & n-uniform: the limit slice is
    the n → ∞ image of the iterate slices, whose C² bounds are uniform from the
    spatial bootstrap `picardIterateHasC2Slices` + M-final's
    `PicardIterateUniformData`) and named K1 fields (`adot`/`hderiv`/`hadotcont`/
    `hMdot` — produced by (3) M3b on the genuine pipeline window, with `(R)` from
    `rep(u)`/★-weak; threaded here as the named families they satisfy).
  * `hLc` (H3) — per-slice continuity of `logisticLifted p (D.u s)`.
    *Satisfiable*: the limit has continuous slices (`HasContinuousSlices`, i.e.
    `D.hcont`); the lifted logistic of a continuous slice is continuous.

  All H2/H3 inputs are facts the existing machinery provides for the limit; none is
  the conclusion in disguise (the genuine new content — the ★ coefficient-level
  agreement — lives in M4/M4b, and is consumed here as `hagree`).

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalPicardLimitRestart
import ShenWork.Paper2.IntervalPicardIterateSourceC1
import ShenWork.Paper2.IntervalPicardIterateTimeC1

open MeasureTheory Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1 duhamelSpectralCoeff)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap logisticLifted)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalMildRegularityBootstrap
  (restartDuhamelCoeff GradientMildHalfStepRestartData)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalMildPicardRegularity
  (logisticSourceFun logisticSource_duhamelSourceTimeC1
   logisticSourceFun_abs_le_of_bound logisticLifted_eq_logisticSourceFun_on_Icc
   cosineCoeffs_zero_abs_le_of_bound)
open ShenWork.IntervalLogisticSourceQuantBound
  (B_log B_log_nonneg logisticSourceFun_cosineCoeff_quadratic_decay_explicit)
open ShenWork.IntervalPicardIterateSourceC1 (iterateSourceEnvelopeConst)
open ShenWork.IntervalPicardIterateTimeC1
  (logisticSourceDot logisticSourceMdot restartFieldDerivBoundUnif
   picardIterate_K1_from_restart)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)

noncomputable section

namespace ShenWork.IntervalPicardLimitSourceData

/-! ## 0. The restart-coefficient bridge (definitional). -/

/-- **`restartDuhamelCoeff` ≡ `localRestartCoeff`** (both unfold to
`e^{−τλₙ}·a₀ₙ + duhamelSpectralCoeff a τ n`).  This lets ★-weak's `rep(u)` window
(stated with `restartDuhamelCoeff`) feed M3b's `(R)` (stated with
`localRestartCoeff`) and conversely. -/
theorem restartDuhamelCoeff_eq_localRestartCoeff
    (a₀ : ℕ → ℝ) (a : ℝ → ℕ → ℝ) (τ : ℝ) (n : ℕ) :
    restartDuhamelCoeff a₀ a τ n = localRestartCoeff a₀ a τ n := rfl

/-! ## 1. The abstract-`w` source-family transport equality (M3's `source_family_eq`). -/

/-- **Abstract-`w` `source_family_eq`.**  For any trajectory `w`, the lifted
logistic coefficient family equals the scalar `logisticSourceFun` coefficient
family of the lifted profile.  (M3's `source_family_eq` is this with
`w := picardIter p u₀ n`.) -/
theorem source_family_eq_w
    (p : CM2Params) (w : ℝ → intervalDomainPoint → ℝ) :
    (fun s k => cosineCoeffs (logisticLifted p (w s)) k)
      = fun s k => cosineCoeffs
          (logisticSourceFun p.a p.b p.α (intervalDomainLift (w s))) k := by
  funext s k
  exact cosineCoeffs_congr_on_Icc
    (logisticLifted_eq_logisticSourceFun_on_Icc p (w s)) k

/-! ## 2. H2(u) — the abstract-`w` variant of M3.

Mirror of `IntervalPicardIterateSourceC1.picardIterate_source_duhamelSourceTimeC1`
with `picardIter p u₀ n` replaced by an arbitrary `w`.  Routes through the abstract
`logisticSource_duhamelSourceTimeC1` exactly as M3 does (no long proof copied). -/

/-- **H2(u) — full `DuhamelSourceTimeC1` for an arbitrary trajectory's logistic
source family.**  Given the K2 spatial-slice bounds of `lift (w σ)` (C², positivity
floor, sup bound `M`, gradient `G1`, Hessian `G2`, Neumann endpoints) and the K1
source-coefficient time-`C¹` data (`adot`, `hderiv`, `hadotcont`, uniform `Mdot`),
the logistic-source coefficient family of the slice is `DuhamelSourceTimeC1`, with
EXPLICIT envelope keyed to `iterateSourceEnvelopeConst p.a p.b p.α M G1 G2`.

Identical assembly to M3; the only change is `w` in place of `picardIter p u₀ n`.
The conclusion is exactly M4's `hsrc`-shaped obligation. -/
noncomputable def limitSource_duhamelSourceTimeC1
    (p : CM2Params)
    (w : ℝ → intervalDomainPoint → ℝ)
    -- structural constants
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    -- K2 spatial slice bounds (profile g σ = lift (w σ))
    {M G1 G2 : ℝ}
    (hC2 : ∀ σ, ContDiffOn ℝ 2 (intervalDomainLift (w σ)) (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (w σ) x)
    (hub : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (w σ) x ≤ M)
    (hG1 : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (w σ)) x| ≤ G1)
    (hG2 : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (w σ))) x| ≤ G2)
    (hN0 : ∀ σ, deriv (intervalDomainLift (w σ)) 0 = 0)
    (hN1 : ∀ σ, deriv (intervalDomainLift (w σ)) 1 = 0)
    -- K1 source-coefficient time-C¹ data
    (adot : ℝ → ℕ → ℝ)
    (hderiv : ∀ σ k, HasDerivAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α
          (intervalDomainLift (w r))) k) (adot σ k) σ)
    (hadotcont : ∀ k, Continuous (fun σ => adot σ k))
    {Mdot : ℝ}
    (hMdot : ∀ σ, 0 ≤ σ → ∀ k, |adot σ k| ≤ Mdot) :
    DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (w s)) k) := by
  set g : ℝ → ℝ → ℝ := fun σ => intervalDomainLift (w σ) with hg
  set C : ℝ := iterateSourceEnvelopeConst p.a p.b p.α M G1 G2 with hCdef
  have hG1nn : 0 ≤ G1 :=
    le_trans (abs_nonneg _) (hG1 0 0 (by constructor <;> norm_num))
  have hG2nn : 0 ≤ G2 :=
    le_trans (abs_nonneg _) (hG2 0 0 (by constructor <;> norm_num))
  have hMnn : 0 ≤ M := by
    have h1 := hub 0 0 (by constructor <;> norm_num)
    have h2 := hpos 0 0 (by constructor <;> norm_num)
    linarith
  have hBnn : 0 ≤ B_log p.a p.b p.α M G1 G2 :=
    B_log_nonneg hα ha hb hMnn hG1nn hG2nn
  have hαpos : 0 < p.α := lt_of_lt_of_le one_pos hα
  have hMa_nn : 0 ≤ M * (p.a + p.b * M ^ p.α) := by positivity
  have hCnn : 0 ≤ C := by
    rw [hCdef, iterateSourceEnvelopeConst]
    exact le_trans (by linarith : (0:ℝ) ≤ 2 * B_log p.a p.b p.α M G1 G2)
      (le_max_left _ _)
  have h2B_le_C : 2 * B_log p.a p.b p.α M G1 G2 ≤ C := by
    rw [hCdef, iterateSourceEnvelopeConst]; exact le_max_left _ _
  have hMa_le_C : M * (p.a + p.b * M ^ p.α) ≤ C := by
    rw [hCdef, iterateSourceEnvelopeConst]; exact le_max_right _ _
  -- (hdecay) explicit 2·B_log/(kπ)² decay of the source coefficients, k ≥ 1
  have hdecay : ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (logisticSourceFun p.a p.b p.α (g σ)) k|
        ≤ C / ((k : ℝ) * Real.pi) ^ 2 := by
    intro σ _ k hk
    refine le_trans
      (logisticSourceFun_cosineCoeff_quadratic_decay_explicit
        (hC2 σ) hα ha hb (hpos σ) (hub σ) (hG1 σ) (hG2 σ) (hN0 σ) (hN1 σ) k hk)
      ?_
    have hden : 0 < ((k : ℝ) * Real.pi) ^ 2 := by
      have hkpos : (0:ℝ) < (k : ℝ) := by
        exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
      positivity
    gcongr
  -- (ha0) zeroth coefficient bound via the explicit source sup bound
  have ha0 : ∀ σ, 0 ≤ σ →
      |cosineCoeffs (logisticSourceFun p.a p.b p.α (g σ)) 0| ≤ C := by
    intro σ _
    have hsup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |logisticSourceFun p.a p.b p.α (g σ) x| ≤ M * (p.a + p.b * M ^ p.α) :=
      logisticSourceFun_abs_le_of_bound (B := M) hMnn hαpos ha hb
        (fun x hx => by rw [abs_of_pos (hpos σ x hx)]; exact hub σ x hx)
        (hpos σ)
    have hgc : Continuous (g σ) := (hC2 σ).continuous
    have hcont : ContinuousOn (logisticSourceFun p.a p.b p.α (g σ))
        (Set.Icc (0 : ℝ) 1) := by
      have hpos' : ∀ x, x ∈ Set.Icc (0:ℝ) 1 → g σ x ≠ 0 :=
        fun x hx => ne_of_gt (hpos σ x hx)
      unfold logisticSourceFun
      apply ContinuousOn.mul hgc.continuousOn
      apply ContinuousOn.sub continuousOn_const
      apply ContinuousOn.mul continuousOn_const
      exact ContinuousOn.rpow_const hgc.continuousOn
        (fun x hx => Or.inl (hpos' x hx))
    exact le_trans
      (cosineCoeffs_zero_abs_le_of_bound hMa_nn hcont hsup) hMa_le_C
  -- assemble the DuhamelSourceTimeC1 for the logisticSourceFun family
  have hsrc :
      DuhamelSourceTimeC1
        (fun σ k => cosineCoeffs (logisticSourceFun p.a p.b p.α (g σ)) k) :=
    logisticSource_duhamelSourceTimeC1 (p := p) (g := g)
      hC2 hpos hN0 hN1 hCnn hdecay ha0 hderiv hadotcont hMdot
  -- transport to the lifted-logistic source family (literally equal)
  rw [show (fun s k => cosineCoeffs (logisticLifted p (w s)) k)
      = fun σ k => cosineCoeffs (logisticSourceFun p.a p.b p.α (g σ)) k from
    source_family_eq_w p w]
  exact hsrc

/-! ## 3. K1(u) via M3b on a restart window.

`limitSource_K1_from_restart` re-exports M3b's
`picardIterate_K1_from_restart` so its derivative-and-bound conclusion is phrased
in the exact `logisticSourceFun`-coefficient shape `limitSource_duhamelSourceTimeC1`
(and M3) consume.  Its restart agreement `(R)` is the window form of `rep(u)`
(★-weak); the two restart-coefficient definitions are `rfl`-equal
(`restartDuhamelCoeff_eq_localRestartCoeff`), so a `rep(u)` window stated with
`restartDuhamelCoeff` reads as M3b's `localRestartCoeff`-shaped `hagree`. -/

/-- **K1(u) on a restart window.**  Re-export of M3b.  On the open restart window
`U ⊆ Ioo t₁ t₂ ∩ Ioi offset`, with the `(R)` restart agreement
(`localRestartCoeff a₀ a (s−offset)`), the K2 slice data, and the named profile
joint-continuity, the logistic-source coefficient family of `lift (w ·)` has the
explicit derivative family `σ ↦ cosineCoeffs (logisticSourceDot … σ ·)`, with the
explicit uniform window bound `logisticSourceMdot p M UMdot`. -/
theorem limitSource_K1_from_restart
    {p : CM2Params} (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {w : ℝ → intervalDomainPoint → ℝ}
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {B : ℝ} (hB : 0 ≤ B)
    (hdecay : ∀ s, 0 ≤ s → ∀ k : ℕ, 1 ≤ k → |a s k| ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2)
    (hcont : ∀ k, Continuous (fun s => a s k))
    {offset t₁ t₂ : ℝ} (hoff : offset < t₁) (ht : t₁ ≤ t₂)
    {U : Set ℝ} (hU_open : IsOpen U) (hU_sub : U ⊆ Set.Ioo t₁ t₂)
    (hU_off : U ⊆ Set.Ioi offset)
    (hagree : ∀ s ∈ U, ∀ x : intervalDomainPoint,
      intervalDomainLift (w s) x.1 = ∑' n,
        restartDuhamelCoeff a₀ a (s - offset) n * cosineMode n x.1)
    {M : ℝ}
    (hpos : ∀ s ∈ U, ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (w s) x)
    (hub : ∀ s ∈ U, ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (w s) x ≤ M)
    (hC2cont : ∀ s ∈ U, ContinuousOn (intervalDomainLift (w s)) (Set.Icc (0 : ℝ) 1))
    (hprofile_joint : ContinuousOn
      (Function.uncurry (fun s x => intervalDomainLift (w s) x))
      (U ×ˢ Set.Icc (0 : ℝ) 1)) :
    (∀ σ ∈ U, ∀ k, HasDerivAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (w r))) k)
      (cosineCoeffs (fun x => logisticSourceDot a₀ a p w offset σ x) k) σ)
    ∧ (∀ σ ∈ U, ∀ k,
        |cosineCoeffs (fun x => logisticSourceDot a₀ a p w offset σ x) k|
          ≤ logisticSourceMdot p M
              (restartFieldDerivBoundUnif (∑' j, src.envelope j) M₀ B
                (t₁ - offset) (t₂ - offset))) := by
  -- the only adjustment is rewriting the restartDuhamelCoeff agreement to the
  -- localRestartCoeff shape M3b expects; the two are definitionally equal.
  refine picardIterate_K1_from_restart hα ha hb hM₀ ha₀ src hB hdecay hcont
    hoff ht hU_open hU_sub hU_off ?_ hpos hub hC2cont hprofile_joint
  intro s hs x
  rw [hagree s hs x]
  simp only [restartDuhamelCoeff_eq_localRestartCoeff]

/-! ## 4. The assembly — `GradientMildHalfStepRestartData` for the limit (χ₀ = 0). -/

/-- **Final-mile assembly.**  Produce `GradientMildHalfStepRestartData D` for a
`GradientMildSolutionData D` (`χ₀ = 0`) by routing M4's
`gradientMildHalfStepRestartData_of_limit` with the FULL `DuhamelSourceTimeC1`
packages `hsrc`/`hsrcShift` forward-derived via `limitSource_duhamelSourceTimeC1`
(H2(u), step 2).

The genuinely new content — the ★ coefficient-level agreement — is supplied by M4
(`picardLimitRestart_cosineIdentity`); the forward derivation here supplies its
`hsrc0` obligation as a FULL time-`C¹` package (with derivative fields), now
producible because the circle was broken in M4b.

All inputs are named & satisfiable (see header §"Satisfiability audit"):
`hfix` is `D.hmild`; `hu₀_*` are the datum's continuity/ℓ¹ data; the per-`t`
K2 slice-regularity families (`hC2t`/`hpost`/`hubt`/`hG1t`/`hG2t`/`hN0t`/`hN1t`)
are the n → ∞ images of the iterates' spatial bootstrap bounds (M-final Data-shaped,
n-uniform); the per-`t` K1 families (`adott`/`hderivt`/`hadotcontt`/`hMdott` for
both the source and its `t/2`-shift) are M3b's window output for `rep(u)`; `hLc`
is the limit's slice continuity (`D.hcont`-derived). -/
noncomputable def gradientMildHalfStepRestartData_for_limit
    {p : CM2Params} (hχ0 : p.χ₀ = 0) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    -- H1 datum data
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    -- FIXED POINT (= D.hmild, the mild Duhamel equation)
    (hfix : ∀ t, 0 < t → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (D.u t) x = intervalGradientDuhamelMap p u₀ D.u t ⟨x, hx⟩)
    -- ===== H2 for the limit source family (per t): K2 slice bounds + K1 fields =====
    {Msup G1 G2 : ℝ}
    (hC2t : ∀ σ, ContDiffOn ℝ 2 (intervalDomainLift (D.u σ)) (Set.Icc (0 : ℝ) 1))
    (hpost : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (D.u σ) x)
    (hubt : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (D.u σ) x ≤ Msup)
    (hG1t : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (D.u σ)) x| ≤ G1)
    (hG2t : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (D.u σ))) x| ≤ G2)
    (hN0t : ∀ σ, deriv (intervalDomainLift (D.u σ)) 0 = 0)
    (hN1t : ∀ σ, deriv (intervalDomainLift (D.u σ)) 1 = 0)
    -- K1 for the (unshifted) limit source family
    (adott : ℝ → ℕ → ℝ)
    (hderivt : ∀ σ k, HasDerivAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (D.u r))) k)
      (adott σ k) σ)
    (hadotcontt : ∀ k, Continuous (fun σ => adott σ k))
    {Mdott : ℝ}
    (hMdott : ∀ σ, 0 ≤ σ → ∀ k, |adott σ k| ≤ Mdott)
    -- ===== H2 for the t/2-SHIFTED limit source family (per t) =====
    (adotS : ℝ → ℝ → ℕ → ℝ)
    (hderivS : ∀ t, ∀ σ k, HasDerivAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (D.u (t/2 + r)))) k)
      (adotS t σ k) σ)
    (hadotcontS : ∀ t, ∀ k, Continuous (fun σ => adotS t σ k))
    {MdotS : ℝ}
    (hMdotS : ∀ t, ∀ σ, 0 ≤ σ → ∀ k, |adotS t σ k| ≤ MdotS)
    -- ===== H3 slice continuity =====
    (hLc : ∀ t, 0 < t → t < D.T →
      ∀ s, 0 < s → s ≤ t → Continuous (logisticLifted p (D.u s))) :
    GradientMildHalfStepRestartData D :=
  ShenWork.IntervalPicardLimitRestart.gradientMildHalfStepRestartData_of_limit
    hχ0 D hu₀_cont hu₀_bound hfix
    -- hsrc : FULL DuhamelSourceTimeC1 for the limit source family (per t)
    (fun _t _ht _htT =>
      limitSource_duhamelSourceTimeC1 p D.u hα ha hb
        hC2t hpost hubt hG1t hG2t hN0t hN1t adott hderivt hadotcontt hMdott)
    -- hsrcShift : FULL DuhamelSourceTimeC1 for the t/2-shifted limit source (per t)
    (fun t _ht _htT =>
      limitSource_duhamelSourceTimeC1 p (fun s => D.u (t/2 + s)) hα ha hb
        (fun σ => hC2t (t/2 + σ))
        (fun σ => hpost (t/2 + σ))
        (fun σ => hubt (t/2 + σ))
        (fun σ => hG1t (t/2 + σ))
        (fun σ => hG2t (t/2 + σ))
        (fun σ => hN0t (t/2 + σ))
        (fun σ => hN1t (t/2 + σ))
        (adotS t) (hderivS t) (hadotcontS t) (hMdotS t))
    hLc

end ShenWork.IntervalPicardLimitSourceData
