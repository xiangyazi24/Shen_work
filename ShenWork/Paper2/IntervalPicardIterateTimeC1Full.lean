/-
  ShenWork/Paper2/IntervalPicardIterateTimeC1Full.lean

  **Tower campaign stage 1 — File D (items 9–10).**

  (9) `picardIterate_K1_full_from_restart_of_representation` — extends
      `picardIterate_K1_from_restart_of_representation` with the MISSING
      `hadotcont` leg: `∀ σ ∈ U, ∀ k, ContinuousOn (fun r => adot r k) U` for the
      logistic source derivative coefficient `adot σ k = cosineCoeffs
      (logisticSourceDot a₀ a p w offset σ ·) k`.  The source-package producer
      needs all THREE legs (HasDerivAt + abs bound + cont) to build a
      `DuhamelSourceTimeC1`.  Proof: per-window-point slab + joint continuity of
      `logisticSourceDot` on the slab (the same construction as
      `logisticSource_adot_hasDerivAt`'s `h_cont_deriv`) + cosine-coefficient
      continuity under the `∫₀¹` via `continuousAt_of_dominated_interval` (the
      K1-weak `hadotcont` pattern).

  (10) `clampedIterateSource_duhamelSourceTimeC1` — window-local representation
      inputs → a GLOBAL clamped `DuhamelSourceTimeC1` agreeing with the canonical
      level-`n` source coefficients on `[lo,hi]`.  Mirrors
      `clampedSource_duhamelSourceTimeC1` with `w := picardIter p u₀ n`.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardIterateTimeC1
import ShenWork.Paper2.IntervalDomainClampedSourceRepresentation

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1 duhamelSpectralCoeff)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalRestartDerivJointContinuity (restartDerivField_continuousOn_joint)
open ShenWork.IntervalMildPicardRegularity
  (logisticSourceFun cosineCoeffs_eq_factor_mul_integral)
open ShenWork.IntervalPicardIterateTimeC1
  (logisticSourceDot logisticSourceMdot restartFieldTimeDeriv restartFieldDerivBoundUnif
   restartFieldTimeDeriv_continuousOn_joint restartProfile_jointContinuousOn
   picardIterate_K1_from_restart_of_representation)

noncomputable section

namespace ShenWork.IntervalPicardIterateTimeC1Full

/-! ## §D.1 — (9) The full K1 package with the `hadotcont` leg. -/

/-- **Joint continuity of `logisticSourceDot` on a slab.**
The slice-derivative field `(s,x) ↦ logisticSourceDot a₀ a p w offset s x` is
jointly continuous on `Icc (σ-δ) (σ+δ) ×ˢ Icc 0 1`, given the profile
joint-continuity on the same slab and the positivity floor (needed for the `^α`
factor).  This is the `h_cont_deriv` block of `logisticSource_adot_hasDerivAt`,
factored out for the `hadotcont` integral-domination argument. -/
theorem logisticSourceDot_continuousOn_joint
    {p : CM2Params}
    {w : ℝ → intervalDomainPoint → ℝ}
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {offset σ δ : ℝ}
    (hslab_off : Set.Icc (σ - δ) (σ + δ) ⊆ Set.Ioi offset)
    (hpos : ∀ s ∈ Set.Icc (σ - δ) (σ + δ), ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (w s) x)
    (hprofile_joint : ContinuousOn
      (Function.uncurry (fun s x => intervalDomainLift (w s) x))
      (Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn
      (Function.uncurry (fun s x => logisticSourceDot a₀ a p w offset s x))
      (Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hfieldjoint : ContinuousOn
      (Function.uncurry (fun s x => restartFieldTimeDeriv a₀ a offset s x))
      (Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0 : ℝ) 1) := by
    refine (restartFieldTimeDeriv_continuousOn_joint hM₀ ha₀ src offset).mono ?_
    intro q hq
    obtain ⟨hq1, _⟩ := Set.mem_prod.1 hq
    exact Set.mk_mem_prod (hslab_off hq1) (Set.mem_univ _)
  have hpowjoint : ContinuousOn
      (Function.uncurry (fun s x => (intervalDomainLift (w s) x) ^ p.α))
      (Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0 : ℝ) 1) := by
    have hne : ∀ q ∈ Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0 : ℝ) 1,
        intervalDomainLift (w q.1) q.2 ≠ 0 := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := Set.mem_prod.1 hq
      exact ne_of_gt (hpos q.1 hq1 q.2 hq2)
    exact ContinuousOn.rpow_const hprofile_joint (fun q hq => Or.inl (hne q hq))
  simp only [logisticSourceDot]
  change ContinuousOn (fun q : ℝ × ℝ =>
      restartFieldTimeDeriv a₀ a offset q.1 q.2 *
        (p.a - p.b * (1 + p.α) * (intervalDomainLift (w q.1) q.2) ^ p.α)) _
  exact hfieldjoint.mul
    ((continuousOn_const).sub (continuousOn_const.mul hpowjoint))

/-- **(9) Full M3b K1 package — adds the `hadotcont` leg.**
Identical inputs to `picardIterate_K1_from_restart_of_representation`, but the
conclusion now carries the THIRD leg — continuity of `σ ↦ adot σ k` on the window
`U` — required by the source producer to build a `DuhamelSourceTimeC1`.  The
derivative-and-bound legs are delegated to the base theorem; the new continuity
leg is the slab + dominated-integral argument. -/
theorem picardIterate_K1_full_from_restart_of_representation
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
                (t₁ - offset) (t₂ - offset)))
    ∧ (∀ k, ContinuousOn
        (fun σ => cosineCoeffs (fun x => logisticSourceDot a₀ a p w offset σ x) k) U) := by
  -- the two original legs, from the base theorem
  obtain ⟨hderiv, hbound⟩ := picardIterate_K1_from_restart_of_representation
    hα ha hb hM₀ ha₀ src hB hdecay hcont hoff ht hU_open hU_sub hU_off hagree
    hpos hub hC2cont
  refine ⟨hderiv, hbound, ?_⟩
  -- the new `hadotcont` leg: pointwise continuity of the coefficient in σ.
  intro k σ₀ hσ₀U
  -- build a slab around σ₀ inside U, with profile joint-continuity on it
  obtain ⟨ε, hεpos, hball_ε⟩ := Metric.isOpen_iff.1 hU_open σ₀ hσ₀U
  set δ : ℝ := ε / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hslab : Set.Icc (σ₀ - δ) (σ₀ + δ) ⊆ U := by
    intro y hy
    apply hball_ε
    rw [Metric.mem_ball, Real.dist_eq]
    obtain ⟨hy1, hy2⟩ := hy; rw [abs_lt]
    constructor <;> (rw [hδdef] at *; linarith)
  have hσ₀mem : σ₀ ∈ Set.Icc (σ₀ - δ) (σ₀ + δ) := ⟨by linarith, by linarith⟩
  have hslab_off : Set.Icc (σ₀ - δ) (σ₀ + δ) ⊆ Set.Ioi offset := hslab.trans hU_off
  have hprofile_joint : ContinuousOn
      (Function.uncurry (fun s x => intervalDomainLift (w s) x))
      (Set.Icc (σ₀ - δ) (σ₀ + δ) ×ˢ Set.Icc (0 : ℝ) 1) :=
    restartProfile_jointContinuousOn hM₀ ha₀ src hslab_off
      (fun s hs x => hagree s (hslab hs) x)
  have hpos_slab : ∀ s ∈ Set.Icc (σ₀ - δ) (σ₀ + δ), ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (w s) x := fun s hs x hx => hpos s (hslab hs) x hx
  -- joint continuity of the dot field on the slab
  have hdotjoint := logisticSourceDot_continuousOn_joint (p := p) (w := w)
    hM₀ ha₀ src hslab_off hpos_slab hprofile_joint
  -- the integrand `F σ x = cos(kπx)·logisticSourceDot … σ x`
  set I : Set ℝ := Set.Icc (σ₀ - δ) (σ₀ + δ) with hIdef
  set F : ℝ → ℝ → ℝ := fun σ x =>
    Real.cos ((k : ℝ) * Real.pi * x) * logisticSourceDot a₀ a p w offset σ x with hFdef
  have hcos_cont : Continuous (fun x : ℝ => Real.cos ((k : ℝ) * Real.pi * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id')
  have hFcont : ContinuousOn (Function.uncurry F) (I ×ˢ Set.Icc (0:ℝ) 1) :=
    (hcos_cont.comp continuous_snd).continuousOn.mul hdotjoint
  have hKcompact : IsCompact (I ×ˢ Set.Icc (0:ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨Bbd, hBbd⟩ := (hKcompact.bddAbove_image hFcont.norm)
  set B' := max Bbd 0 with hB'def
  have hB'nn : 0 ≤ B' := le_max_right _ _
  have hFbd : ∀ σ ∈ I, ∀ x ∈ Set.Icc (0:ℝ) 1, ‖F σ x‖ ≤ B' := by
    intro σ hσ x hx
    have : ‖Function.uncurry F (σ, x)‖ ≤ Bbd :=
      hBbd (Set.mem_image_of_mem _ (Set.mem_prod.mpr ⟨hσ, hx⟩))
    exact le_trans this (le_max_left _ _)
  have hsec_cont : ∀ σ ∈ I, ContinuousOn (F σ) (Set.Icc (0:ℝ) 1) := by
    intro σ hσ
    have hsslice : ContinuousOn (fun x => logisticSourceDot a₀ a p w offset σ x)
        (Set.Icc (0:ℝ) 1) :=
      hdotjoint.comp (continuousOn_const.prodMk continuousOn_id)
        (fun x hx => Set.mem_prod.mpr ⟨hσ, hx⟩)
    exact (hcos_cont.continuousOn).mul hsslice
  have hInhds : I ∈ 𝓝 σ₀ := by
    have hsub : Set.Ioo (σ₀ - δ) (σ₀ + δ) ⊆ I := fun y hy => ⟨hy.1.le, hy.2.le⟩
    exact Filter.mem_of_superset
      (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩) hsub
  have hint_cont : ContinuousAt (fun σ => ∫ x in (0:ℝ)..1, F σ x) σ₀ := by
    refine intervalIntegral.continuousAt_of_dominated_interval
      (bound := fun _ => B') ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [hInhds] with σ hσ
      have : ContinuousOn (F σ) (Set.uIcc (0:ℝ) 1) := by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hsec_cont σ hσ
      exact (this.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
    · filter_upwards [hInhds] with σ hσ
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
      exact hFbd σ hσ x ⟨hx.1.le, hx.2⟩
    · refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
      have hxIcc : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx.1.le, hx.2⟩
      have hcwa : ContinuousWithinAt (fun σ => F σ x) I σ₀ := by
        have := (hFcont.comp (continuousOn_id.prodMk continuousOn_const)
          (fun σ hσ => Set.mem_prod.mpr ⟨hσ, hxIcc⟩)).continuousWithinAt hσ₀mem
        simpa [Function.uncurry] using this
      exact hcwa.continuousAt hInhds
  have hadeq : ∀ σ, cosineCoeffs (fun x => logisticSourceDot a₀ a p w offset σ x) k =
      (if k = 0 then (1:ℝ) else 2) * ∫ x in (0:ℝ)..1, F σ x := by
    intro σ; rw [cosineCoeffs_eq_factor_mul_integral]
  have hcont_at : ContinuousAt
      (fun σ => cosineCoeffs (fun x => logisticSourceDot a₀ a p w offset σ x) k) σ₀ := by
    have hfun :
        (fun σ => cosineCoeffs (fun x => logisticSourceDot a₀ a p w offset σ x) k)
          = (fun σ => (if k = 0 then (1:ℝ) else 2) * ∫ x in (0:ℝ)..1, F σ x) :=
      funext hadeq
    rw [hfun]
    exact hint_cont.const_mul _
  exact hcont_at.continuousWithinAt

/-! ## §D.2 — (10) Window-local → global clamped iterate source. -/

section ClampedIterate

open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.Paper2.ClampedSourceRepresentation
  (clampedSource_duhamelSourceTimeC1 clampedFamily_eq_on)
open ShenWork.IntervalMildPicardRegularity (logisticLifted_eq_logisticSourceFun_on_Icc)
open ShenWork.IntervalTimeSoftClamp (φ φ_eq_id_on)

/-- **(10) Clamped level-`n` iterate source: window-local inputs → GLOBAL package.**

From the per-slice cosine representation / `K2` sup-gradient-Hessian bounds /
time-`C¹` coefficient data for the `n`-th Picard iterate `w := picardIter p u₀ n`,
known ONLY on the window `[c', d'] ⊇ [lo, hi]` (with `c' < lo ≤ hi < d'`), this
builds a GLOBAL `DuhamelSourceTimeC1` whose source family is the clamped iterate
logistic source, together with the agreement on `[lo, hi]` with the CANONICAL
level-`n` source coefficients `cosineCoeffs (logisticLifted p (picardIter p u₀ n ·))`.

Window/id-zone setup: `τ := 0`, active id-zone `[c, d] := [lo, hi]`, padded range
`[c', d']`.  The producer is `clampedSource_duhamelSourceTimeC1`; the id-zone
agreement is `clampedFamily_eq_on` (clamp is the identity there) bridged to
`logisticLifted` via `logisticLifted_eq_logisticSourceFun_on_Icc`. -/
theorem clampedIterateSource_duhamelSourceTimeC1
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {lo hi c' d' : ℝ} (hc' : c' < lo) (hlohi : lo ≤ hi) (hd' : hi < d')
    {M G1 G2 : ℝ}
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ ∈ Set.Icc c' d',
      Summable (fun k => unitIntervalCosineEigenvalue k * |bc σ k|))
    (hagree : ∀ σ ∈ Set.Icc c' d',
      Set.EqOn (intervalDomainLift (picardIter p u₀ n σ))
        (fun x => ∑' k, bc σ k * cosineMode k x) (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ n σ) x)
    (hub : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (picardIter p u₀ n σ) x ≤ M)
    (hG1 : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (picardIter p u₀ n σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (picardIter p u₀ n σ))) x| ≤ G2)
    (adot : ℝ → ℕ → ℝ)
    (hderiv : ∀ σ ∈ Set.Icc c' d', ∀ k, HasDerivAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (picardIter p u₀ n r))) k)
      (adot σ k) σ)
    (hadotcont : ∀ k, ContinuousOn (fun σ => adot σ k) (Set.Icc c' d'))
    {Mdot : ℝ} (hMdot : ∀ σ ∈ Set.Icc c' d', ∀ k, |adot σ k| ≤ Mdot) :
    ∃ asrc : ℝ → ℕ → ℝ, ∃ _ : DuhamelSourceTimeC1 asrc,
      ∀ σ ∈ Set.Icc lo hi, ∀ k,
        asrc σ k = cosineCoeffs (logisticLifted p (picardIter p u₀ n σ)) k := by
  have hcd : lo ≤ hi := hlohi
  -- Build the GLOBAL clamped package via the producer, `τ = 0`, id-zone `[lo,hi]`.
  have hpkg := clampedSource_duhamelSourceTimeC1 p (picardIter p u₀ n) hα ha hb
    (τ := 0) (c' := c') (c := lo) (d := hi) (d' := d') hc' hcd hd'
    bc hbsum hagree hpos hub hG1 hG2 adot hderiv hadotcont hMdot
  refine ⟨_, hpkg, ?_⟩
  -- Agreement on the id-zone `[lo,hi]` (`τ + σ = σ ∈ [lo,hi] = [c,d]`).
  intro σ hσ k
  have hσcd : (0 : ℝ) + σ ∈ Set.Icc lo hi := by simpa using hσ
  -- clamp is identity → equals the genuine level-n logisticSourceFun coeff
  have hclamp := clampedFamily_eq_on p (picardIter p u₀ n)
    (τ := 0) (c' := c') (c := lo) (d := hi) (d' := d') hc' hd' hσcd k
  -- bridge logisticSourceFun ∘ lift ↔ logisticLifted on [0,1] (equal cosine coeffs)
  have hbridge :
      cosineCoeffs (logisticSourceFun p.a p.b p.α
          (intervalDomainLift (picardIter p u₀ n ((0 : ℝ) + σ)))) k
        = cosineCoeffs (logisticLifted p (picardIter p u₀ n σ)) k := by
    have h0 : (0 : ℝ) + σ = σ := by ring
    rw [h0]
    exact (ShenWork.Paper2.cosineCoeffs_congr_on_Icc
      (logisticLifted_eq_logisticSourceFun_on_Icc p (picardIter p u₀ n σ)) k).symm
  -- the package's source value at σ is the clamped coeff; rewrite to canonical
  show cosineCoeffs (logisticSourceFun p.a p.b p.α
      (intervalDomainLift (picardIter p u₀ n (φ c' lo hi d' ((0 : ℝ) + σ))))) k
    = cosineCoeffs (logisticLifted p (picardIter p u₀ n σ)) k
  rw [hclamp, hbridge]

end ClampedIterate

end ShenWork.IntervalPicardIterateTimeC1Full
