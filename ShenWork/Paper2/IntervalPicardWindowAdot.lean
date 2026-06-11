/-
  ShenWork/Paper2/IntervalPicardWindowAdot.lean

  **K1-wall closure — the per-level window adot legs.**

  This file builds the per-level WINDOW source-derivative legs `WindowAdotLegs`:
  for every read window `[lo,hi] ⊂ (0,T)`, the three K1 legs of the level-`n`
  logistic source-coefficient family (the `HasDerivAt` derivative `adot`, a uniform
  window bound `Mdot`, and the per-mode window continuity) — exactly the data the
  clamped global source producer (`clampedIterateSource_duhamelSourceTimeC1`)
  consumes to build a `SourceWin`.

  Both legs instantiate `picardIterate_K1_full_from_restart_of_representation`
  (File D, item 9) on the window: the restart representation of the level-`n`
  iterate slice at a FIXED positive offset feeds the three legs with explicit
  `adot σ k = cosineCoeffs (logisticSourceDot …) k`.

  * `windowAdotLegs_zero` — level `0` is the homogeneous heat slice `S(r)u₀`, whose
    restart representation at offset `0` is `localRestartCoeff (û₀) 0 r`, i.e. the
    damped cosine series with the TRIVIAL ZERO source package.  WALL-FREE.

  * `windowAdotLegs_succ` — level `n+1` uses the M1 restart cosine identity
    (`picardIterateRestart_cosineIdentity`) at the FIXED offset `lo/2`, bridged to
    the GLOBAL CLAMPED level-`n` source family via the clamp congruence
    (`clampedFamily_eq_on`, `localRestartCoeff_congr_on_Icc`).  The clamped family is
    a genuine `DuhamelSourceTimeC1` (built by `clampedSource_duhamelSourceTimeC1`
    from the level-`n` window facts carried by `TowerLevel`), whose quadratic decay
    on `[0,∞)` follows from the stage-F per-slice decay at the clamped (id-zone)
    times.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardIterateTimeC1Full
import ShenWork.Paper2.IntervalPicardIterateRepresentation
import ShenWork.Paper2.IntervalPicardSliceWitnessSupply
import ShenWork.Paper2.IntervalDuhamelSourceShift
import ShenWork.Paper2.IntervalPicardLimitTimeNhd
import ShenWork.Paper2.IntervalPicardWdataAssembly
import ShenWork.Paper2.IntervalPicardIterateRestartLocal
import ShenWork.Paper2.IntervalPicardSourceSubtypeCont

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1 duhamelSpectralCoeff)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalMildRegularityBootstrap (restartDuhamelCoeff)
open ShenWork.IntervalMildPicardRegularity (logisticSourceFun)
open ShenWork.IntervalPicardIterateTimeC1
  (logisticSourceDot picardIterate_K1_from_restart_of_representation)
open ShenWork.IntervalPicardIterateTimeC1Full
  (picardIterate_K1_full_from_restart_of_representation
   clampedIterateSource_duhamelSourceTimeC1)
open ShenWork.IntervalPicardIterateRepresentation
  (iterateReprCoeff hbsum_zero hagree_zero)
open ShenWork.IntervalPicardIterateRestart (picardIterateRestart_cosineIdentity)
open ShenWork.IntervalPicardSliceWitnessSupply (shifted_source_windowDecay)
open ShenWork.IntervalDuhamelSourceShift (localRestartCoeff_congr_on_Icc)
open ShenWork.Paper2.ClampedSourceRepresentation
  (clampedSource_duhamelSourceTimeC1 clampedFamily_eq_on)
open ShenWork.IntervalTimeSoftClamp (φ φ_mem_range)

noncomputable section

namespace ShenWork.IntervalPicardWindowAdot

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## §1 — The window adot legs predicate. -/

/-- **The per-level window source-derivative legs.**  For the level-`n` iterate
slice's logistic source coefficient family, on the read window `[lo,hi]`: an `adot`
function with the `HasDerivAt` derivative leg, a uniform window bound, and per-mode
window continuity.  This is exactly the K1 data
`clampedIterateSource_duhamelSourceTimeC1` consumes (its `adot`/`hderiv`/`hadotcont`/
`hMdot` inputs) on the padded window. -/
def WindowAdotLegs (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (lo hi : ℝ) : Prop :=
  ∃ adot : ℝ → ℕ → ℝ,
    (∀ σ ∈ Set.Icc lo hi, ∀ k, HasDerivAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (picardIter p u₀ n r))) k)
      (adot σ k) σ)
    ∧ (∃ Mdot : ℝ, ∀ σ ∈ Set.Icc lo hi, ∀ k, |adot σ k| ≤ Mdot)
    ∧ (∀ k, ContinuousOn (fun σ => adot σ k) (Set.Icc lo hi))

/-! ## §2 — The trivial zero source package. -/

/-- **The trivial zero `DuhamelSourceTimeC1`.**  `a := 0`, `adot := 0`, `envelope :=
0`; all fields hold by `simp`/`norm_num`.  This is the level-0 restart source (the
homogeneous heat slice carries no Duhamel term). -/
def zeroDuhamelSource : DuhamelSourceTimeC1 (fun _ _ => (0 : ℝ)) where
  adot := fun _ _ => 0
  hderiv := fun _ _ => hasDerivAt_const _ _
  hadotcont := fun _ => continuous_const
  envelope := fun _ => 0
  henv_summable := summable_zero
  henv_bound := by intro s _ n; simp
  derivBound := 0
  hderivBound := by intro s _ n; simp

/-- `duhamelSpectralCoeff` of the zero family vanishes. -/
theorem duhamelSpectralCoeff_zero (τ : ℝ) (k : ℕ) :
    duhamelSpectralCoeff (fun _ _ => (0 : ℝ)) τ k = 0 := by
  unfold duhamelSpectralCoeff
  simp

/-! ## §3 — Level 0 (wall-free). -/

/-- **`windowAdotLegs_zero` — the level-0 window adot legs.**  The homogeneous heat
slice `lift(iter 0 r) = ∑' (e^{−rλ}û₀)·cos` is the restart series at offset `0`,
base `a₀ := cosineCoeffs(lift u₀)`, with the TRIVIAL zero source.  Feeding this to
`picardIterate_K1_full_from_restart_of_representation` on the open window
`Ioo (lo/2) ((hi+T)/2) ⊇ [lo,hi]` produces the three legs. -/
theorem windowAdotLegs_zero
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {M T : ℝ}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hMnn : 0 ≤ M)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M)
    (hpos : ∀ (σ : ℝ), 0 < σ → σ ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ 0 σ) x)
    (hub : ∀ (σ : ℝ), 0 < σ → σ ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (picardIter p u₀ 0 σ) x ≤ M)
    (hcontSlice : ∀ (σ : ℝ), 0 < σ → σ ≤ T →
      ContinuousOn (intervalDomainLift (picardIter p u₀ 0 σ)) (Set.Icc (0 : ℝ) 1)) :
    ∀ lo hi, 0 < lo → lo ≤ hi → hi < T → WindowAdotLegs p u₀ 0 lo hi := by
  intro lo hi hlo hlohi hhiT
  classical
  -- window arithmetic: offset 0, open nbhd `Ioo (lo/2) ((hi+T)/2) ⊇ [lo,hi]`.
  set t₁ : ℝ := lo / 2 with ht₁def
  set t₂ : ℝ := (hi + T) / 2 with ht₂def
  have ht₁pos : 0 < t₁ := by rw [ht₁def]; linarith
  have ht₁lo : t₁ < lo := by rw [ht₁def]; linarith
  have hhit₂ : hi < t₂ := by rw [ht₂def]; linarith
  have ht₂T : t₂ ≤ T := by rw [ht₂def]; linarith
  have ht₁₂ : t₁ ≤ t₂ := by
    have : lo ≤ hi := hlohi
    rw [ht₁def, ht₂def]; linarith
  set U : Set ℝ := Set.Ioo t₁ t₂ with hUdef
  have hU_open : IsOpen U := isOpen_Ioo
  have hU_sub : U ⊆ Set.Ioo t₁ t₂ := le_refl _
  have hU_off : U ⊆ Set.Ioi (0 : ℝ) := fun s hs => lt_trans ht₁pos hs.1
  -- members of `U` are in `(0,T]`.
  have hUmem : ∀ s ∈ U, 0 < s ∧ s ≤ T := fun s hs =>
    ⟨lt_trans ht₁pos hs.1, le_of_lt (lt_of_lt_of_le hs.2 ht₂T)⟩
  -- `[lo,hi] ⊆ U`.
  have hsubLoHi : Set.Icc lo hi ⊆ U := by
    intro s hs
    exact ⟨lt_of_lt_of_le ht₁lo hs.1, lt_of_le_of_lt hs.2 hhit₂⟩
  -- base coefficients and their bound.
  set a₀ : ℕ → ℝ := cosineCoeffs (intervalDomainLift u₀) with ha₀def
  -- restart agreement on `U`: `lift(iter 0 s) = ∑' localRestartCoeff a₀ 0 (s−0) k cos`.
  have hagree : ∀ s ∈ U, ∀ x : intervalDomainPoint,
      intervalDomainLift (picardIter p u₀ 0 s) x.1
        = ∑' k, localRestartCoeff a₀ (fun _ _ => (0 : ℝ)) (s - 0) k * cosineMode k x.1 := by
    intro s hs x
    have hsmem := hUmem s hs
    have hx : x.1 ∈ Set.Icc (0 : ℝ) 1 := x.2
    have h0 := hagree_zero p u₀ hsmem.1 hu₀_cont hu₀_bound hx
    rw [h0]
    refine tsum_congr (fun k => ?_)
    -- `localRestartCoeff a₀ 0 (s−0) k = e^{−sλ}·a₀ k + 0 = iterateReprCoeff … 0 s k`.
    have hlr : localRestartCoeff a₀ (fun _ _ => (0 : ℝ)) (s - 0) k
        = iterateReprCoeff p u₀ 0 s k := by
      unfold localRestartCoeff iterateReprCoeff
      rw [duhamelSpectralCoeff_zero, sub_zero, add_zero, ha₀def]
    rw [hlr]
  -- the K2 slice facts on `U`.
  have hposU : ∀ s ∈ U, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ 0 s) x :=
    fun s hs x hx => hpos s (hUmem s hs).1 (hUmem s hs).2 x hx
  have hubU : ∀ s ∈ U, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (picardIter p u₀ 0 s) x ≤ M :=
    fun s hs x hx => hub s (hUmem s hs).1 (hUmem s hs).2 x hx
  have hC2contU : ∀ s ∈ U,
      ContinuousOn (intervalDomainLift (picardIter p u₀ 0 s)) (Set.Icc (0 : ℝ) 1) :=
    fun s hs => hcontSlice s (hUmem s hs).1 (hUmem s hs).2
  -- the K1-full producer at offset 0 with the trivial zero source.
  obtain ⟨hderiv, hbound, hcont⟩ :=
    picardIterate_K1_full_from_restart_of_representation
      (p := p) (w := picardIter p u₀ 0) hα ha hb hMnn hu₀_bound
      zeroDuhamelSource (B := 0) (le_refl 0)
      (fun s _ k _ => by simp)
      (fun k => continuous_const)
      (offset := 0) (t₁ := t₁) (t₂ := t₂) ht₁pos ht₁₂
      hU_open hU_sub hU_off hagree (M := M) hposU hubU hC2contU
  -- restrict the three legs to `[lo,hi] ⊆ U`.
  refine ⟨fun σ k => cosineCoeffs
      (fun x => logisticSourceDot a₀ (fun _ _ => (0 : ℝ)) p (picardIter p u₀ 0) 0 σ x) k,
    ?_, ?_, ?_⟩
  · intro σ hσ k; exact hderiv σ (hsubLoHi hσ) k
  · refine ⟨_, fun σ hσ k => hbound σ (hsubLoHi hσ) k⟩
  · intro k; exact (hcont k).mono hsubLoHi

/-! ## §4 — The general-offset iterate restart identity (succ).

For the `(n+1)`-st Picard iterate and a FIXED positive offset `τ`, the iterate slice
is the restart cosine series at base `coeffs(lift(iter(n+1) τ))` and source the
`τ`-shifted CANONICAL level-`n` logistic source, at horizon `s − τ`.  This is the
`τ ≠ s/2` generalisation of M1's `picardIterateRestart_cosineIdentity`, proved by
the from-zero representation (`iterate_lift_eq_cosineSeries`) plus the general
Duhamel split (`duhamelSpectralCoeff_general_split`). -/
theorem picardIterateRestart_general
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k))
    {τ s : ℝ} (hτ : 0 < τ) (hτs : τ < s)
    (hLs_cont : ∀ r, 0 < r → r ≤ s →
      Continuous (intervalLogisticSource p (picardIter p u₀ n r))) :
    Set.EqOn (intervalDomainLift (picardIter p u₀ (n + 1) s))
      (fun x => ∑' k,
        localRestartCoeff
          (cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) τ)))
          (fun σ k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (τ + σ))) k)
          (s - τ) k * cosineMode k x)
      (Set.Icc (0 : ℝ) 1) := by
  have hs : 0 < s := lt_trans hτ hτs
  -- canonical source family coefficients continuous in `s`.
  have ha_cont : ∀ k, Continuous
      (fun r => cosineCoeffs (logisticLifted p (picardIter p u₀ n r)) k) := fun k =>
    continuous_iff_continuousAt.2 (fun r => (hsrc0.hderiv r k).continuousAt)
  intro x hx
  -- from-zero representation of `iter(n+1) s` (subtype-continuity route).
  rw [ShenWork.IntervalPicardSourceSubtypeCont.iterate_lift_eq_cosineSeries_of_sourceSubtypeCont
        p hχ0 u₀ n hu₀_cont hu₀_bound hsrc0 hs hLs_cont hx]
  refine tsum_congr (fun k => ?_)
  congr 1
  -- `iterateCoeff p u₀ n s k = localRestartCoeff (coeffs iter(n+1) τ) (shifted) (s−τ) k`.
  unfold ShenWork.IntervalPicardIterateRestart.iterateCoeff localRestartCoeff
  -- base coefficient: `coeffs(lift(iter(n+1) τ)) = iterateCoeff p u₀ n τ`.
  have hbase : cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) τ)) k
      = ShenWork.IntervalPicardIterateRestart.iterateCoeff p u₀ n τ k :=
    ShenWork.IntervalPicardSourceSubtypeCont.cosineCoeffs_halfstep_eq_iterateCoeff_of_sourceSubtypeCont
      p hχ0 u₀ n hu₀_cont hu₀_bound hsrc0 hτ
      (fun r hr hrτ => hLs_cont r hr (le_trans hrτ hτs.le)) k
  rw [hbase]
  unfold ShenWork.IntervalPicardIterateRestart.iterateCoeff
  -- general Duhamel split of the canonical source at base `τ`, horizon `s − τ`.
  have hsplit := ShenWork.IntervalPicardLimitTimeNhd.duhamelSpectralCoeff_general_split
    (a := fun r k => cosineCoeffs (logisticLifted p (picardIter p u₀ n r)) k)
    ha_cont τ s k
  -- factor the homogeneous heat term: `e^{−sλ} = e^{−(s−τ)λ}·e^{−τλ}`.
  have hexp : Real.exp (-s * (λ_ k))
      = Real.exp (-(s - τ) * (λ_ k)) * Real.exp (-τ * (λ_ k)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp, hsplit]
  ring

/-! ## §5 — The inductive step `windowAdotLegs_step`.

`WindowAdotLegs … n c' d' → WindowAdotLegs … (n+1) lo hi`, where `[c',d'] ⊃ [lo,hi]`
is the padded window of the clamp.  The level-`n` legs (`prev`) feed the clamped
global source producer; the clamped family's restart representation of `iter(n+1)`
on the read window feeds `picardIterate_K1_full_from_restart_of_representation` to
produce the level-`(n+1)` legs.

The window facts on `[c',d']` (representation triple, ball, scalar `G1`/`G2`) are the
level-`n` carrier data (`TowerLevel.hrepr_*`/`hG1`/`hG2` evaluated on the compact
window); the canonical-source `DuhamelSourceTimeC1` `hsrc0_n` is taken explicitly
(see file footer for the honest narrowing). -/
theorem windowAdotLegs_step
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    {M T A₂ : ℝ}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hMnn : 0 ≤ M) (hA₂nn : 0 ≤ A₂)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M)
    -- canonical level-`n` source package (the residual; see footer).
    (hsrc0_n : DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k))
    -- per-slice continuity of the level-`n` logistic source (for the restart rep).
    (hLs_cont : ∀ r, 0 < r → r ≤ T →
      Continuous (intervalLogisticSource p (picardIter p u₀ n r)))
    -- level-`n` representation triple / ball on `(0,T]` (the `TowerLevel n` data).
    (hrepr_sum : ∀ σ, 0 < σ → σ ≤ T →
      Summable (fun k => (λ_ k) * |iterateReprCoeff p u₀ n σ k|))
    (hrepr_agree : ∀ σ, 0 < σ → σ ≤ T →
      Set.EqOn (intervalDomainLift (picardIter p u₀ n σ))
        (fun x => ∑' k, iterateReprCoeff p u₀ n σ k * cosineMode k x)
        (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ σ, 0 < σ → σ ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ n σ) x)
    (hub : ∀ σ, 0 < σ → σ ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (picardIter p u₀ n σ) x ≤ M)
    (hG1 : ∀ σ, 0 < σ → σ ≤ T → ∀ x : ℝ,
      |deriv (intervalDomainLift (picardIter p u₀ n σ)) x|
        ≤ ShenWork.IntervalPicardIterateUniform.G1profile p M σ)
    (hG2 : ∀ σ, 0 < σ → σ ≤ T → ∀ x : ℝ,
      |deriv (deriv (intervalDomainLift (picardIter p u₀ n σ))) x|
        ≤ ShenWork.IntervalPicardIterateUniform.G2profile A₂ σ)
    -- (n+1)-level ball / slice continuity on `(0,T]` (for the K1-full producer's K2).
    (hpos1 : ∀ σ, 0 < σ → σ ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ (n + 1) σ) x)
    (hub1 : ∀ σ, 0 < σ → σ ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (picardIter p u₀ (n + 1) σ) x ≤ M)
    (hcontSlice1 : ∀ σ, 0 < σ → σ ≤ T →
      ContinuousOn (intervalDomainLift (picardIter p u₀ (n + 1) σ)) (Set.Icc (0 : ℝ) 1))
    -- the level-`n` adot legs on the padded window (the induction hypothesis).
    (prev : ∀ c' d', 0 < c' → c' ≤ d' → d' < T → WindowAdotLegs p u₀ n c' d') :
    ∀ lo hi, 0 < lo → lo ≤ hi → hi < T → WindowAdotLegs p u₀ (n + 1) lo hi := by
  intro lo hi hlo hlohi hhiT
  classical
  -- offset / clamp windows: offset τ = lo/2, id-zone [c,d]=[lo/2,(hi+T)/2],
  -- padded [c',d']=[lo/4,(hi+3T)/4], producer window (t₁,t₂)=(3lo/4,(hi+T)/2).
  set τ : ℝ := lo / 2 with hτdef
  set c' : ℝ := lo / 4 with hc'def
  set d : ℝ := (hi + T) / 2 with hddef
  set d' : ℝ := (hi + 3 * T) / 4 with hd'def
  set t₁ : ℝ := 3 * lo / 4 with ht₁def
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hc'pos : 0 < c' := by rw [hc'def]; linarith
  have hc'τ : c' < τ := by rw [hc'def, hτdef]; linarith
  have hcd : τ ≤ d := by rw [hτdef, hddef]; linarith
  have hdd' : d < d' := by rw [hddef, hd'def]; linarith
  have hd'Tlt : d' < T := by rw [hd'def]; linarith
  have hd'T : d' ≤ T := le_of_lt hd'Tlt
  have hc'd' : c' ≤ d' := le_of_lt (lt_trans hc'τ (lt_of_le_of_lt hcd hdd'))
  have hτt₁ : τ < t₁ := by rw [hτdef, ht₁def]; linarith
  have ht₁lo : t₁ < lo := by rw [ht₁def]; linarith
  have ht₁pos : 0 < t₁ := lt_trans hτpos hτt₁
  have hhid : hi < d := by rw [hddef]; linarith
  have ht₁d : t₁ ≤ d := le_of_lt (lt_trans ht₁lo (lt_of_le_of_lt hlohi hhid))
  -- window membership helpers on [c',d'] ⊆ (0,T].
  have hcd'_pos : ∀ σ ∈ Set.Icc c' d', 0 < σ := fun σ hσ => lt_of_lt_of_le hc'pos hσ.1
  have hcd'_T : ∀ σ ∈ Set.Icc c' d', σ ≤ T := fun σ hσ => le_trans hσ.2 hd'T
  -- window-uniform scalar G1/G2 on [c',d'].
  set G1s : ℝ := ShenWork.IntervalPicardWdataAssembly.G1win p M c' d' with hG1sdef
  set G2s : ℝ := ShenWork.IntervalPicardWdataAssembly.G2win A₂ c' with hG2sdef
  have hG1w : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (picardIter p u₀ n σ)) x| ≤ G1s := by
    intro σ hσ x _hx
    exact le_trans (hG1 σ (hcd'_pos σ hσ) (hcd'_T σ hσ) x)
      (ShenWork.IntervalPicardWdataAssembly.G1profile_le_G1win hMnn hc'pos hσ.1 hσ.2)
  have hG2w : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (picardIter p u₀ n σ))) x| ≤ G2s := by
    intro σ hσ x _hx
    exact le_trans (hG2 σ (hcd'_pos σ hσ) (hcd'_T σ hσ) x)
      (ShenWork.IntervalPicardWdataAssembly.G2profile_le_G2win hA₂nn hc'pos hσ.1)
  -- the level-n adot legs on [c',d'] (induction hypothesis).
  obtain ⟨adotn, hadotn_deriv, ⟨Mdotn, hadotn_bound⟩, hadotn_cont⟩ :=
    prev c' d' hc'pos hc'd' hd'Tlt
  -- representation triple on [c',d'] (from the (0,T] form).
  have hbsumW : ∀ σ ∈ Set.Icc c' d',
      Summable (fun k => unitIntervalCosineEigenvalue k * |iterateReprCoeff p u₀ n σ k|) :=
    fun σ hσ => hrepr_sum σ (hcd'_pos σ hσ) (hcd'_T σ hσ)
  have hagreeW : ∀ σ ∈ Set.Icc c' d',
      Set.EqOn (intervalDomainLift (picardIter p u₀ n σ))
        (fun x => ∑' k, iterateReprCoeff p u₀ n σ k * cosineMode k x) (Set.Icc (0 : ℝ) 1) :=
    fun σ hσ => hrepr_agree σ (hcd'_pos σ hσ) (hcd'_T σ hσ)
  have hposW : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ n σ) x :=
    fun σ hσ x hx => hpos σ (hcd'_pos σ hσ) (hcd'_T σ hσ) x hx
  have hubW : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (picardIter p u₀ n σ) x ≤ M :=
    fun σ hσ x hx => hub σ (hcd'_pos σ hσ) (hcd'_T σ hσ) x hx
  -- ════ the EXPLICIT clamped level-n source family, with τ = offset ════
  set aC : ℝ → ℕ → ℝ := fun σ k => cosineCoeffs (logisticSourceFun p.a p.b p.α
      (intervalDomainLift (picardIter p u₀ n (φ c' τ d d' (τ + σ))))) k with haCdef
  have srcC : DuhamelSourceTimeC1 aC :=
    clampedSource_duhamelSourceTimeC1 p (picardIter p u₀ n) hα ha hb
      (τ := τ) (c' := c') (c := τ) (d := d) (d' := d') hc'τ hcd hdd'
      (iterateReprCoeff p u₀ n) hbsumW hagreeW hposW hubW hG1w hG2w
      adotn hadotn_deriv hadotn_cont hadotn_bound
  -- the K1-full producer window `U := Ioo t₁ t₂` with `t₂ := d` (the id-zone right end).
  set U : Set ℝ := Set.Ioo t₁ d with hUdef
  have hU_open : IsOpen U := isOpen_Ioo
  have hU_sub : U ⊆ Set.Ioo t₁ d := le_refl _
  have hU_off : U ⊆ Set.Ioi τ := fun s hs => lt_trans hτt₁ hs.1
  have hUmem : ∀ s ∈ U, 0 < s ∧ s ≤ T := fun s hs =>
    ⟨lt_trans ht₁pos hs.1, le_of_lt (lt_of_lt_of_le hs.2 (hdd'.le.trans hd'T))⟩
  have hsubLoHi : Set.Icc lo hi ⊆ U := fun s hs =>
    ⟨lt_of_lt_of_le ht₁lo hs.1, lt_of_le_of_lt hs.2 hhid⟩
  -- base coefficients of the restart.
  set a₀ : ℕ → ℝ := cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) τ)) with ha₀def
  -- ════ hcont: σ-continuity of the clamped family coefficients ════
  have hcontC : ∀ k, Continuous (fun s => aC s k) := fun k =>
    continuous_iff_continuousAt.2 (fun s => (srcC.hderiv s k).continuousAt)
  -- ════ hdecay: quadratic decay of the clamped family for all s ≥ 0 ════
  have hTpos : 0 < T := lt_of_lt_of_le hτpos (hcd.trans (hdd'.le.trans hd'T))
  have hG1s_nn : 0 ≤ G1s :=
    ShenWork.IntervalPicardWdataAssembly.G1win_nonneg hMnn hc'pos (le_trans hc'pos.le hc'd')
  have hG2s_nn : 0 ≤ G2s :=
    ShenWork.IntervalPicardWdataAssembly.G2win_nonneg hA₂nn hc'pos
  set Bwin : ℝ :=
    ShenWork.IntervalPicardWeightedC2Bootstrap.windowSourceConst p M G1s G2s with hBwindef
  have hBwin_nn : 0 ≤ Bwin :=
    ShenWork.IntervalPicardWeightedC2Bootstrap.windowSourceConst_nonneg p hα hMnn
      hG1s_nn hG2s_nn
  have hdecay : ∀ s, 0 ≤ s → ∀ k : ℕ, 1 ≤ k →
      |aC s k| ≤ 2 * (Bwin / 2) / ((k : ℝ) * Real.pi) ^ 2 := by
    intro s _hs k hk
    rw [show (2 : ℝ) * (Bwin / 2) = Bwin by ring]
    -- the clamped slice index lies in `[c',d']`.
    have hΦmem : φ c' τ d d' (τ + s) ∈ Set.Icc c' d' := φ_mem_range hc'τ hcd hdd' (τ + s)
    set σΦ := φ c' τ d d' (τ + s) with hσΦdef
    have hΦpos : 0 < σΦ := hcd'_pos σΦ hΦmem
    have hΦT : σΦ ≤ T := hcd'_T σΦ hΦmem
    -- stage-F per-slice decay at the clamped slice.
    have hdec := ShenWork.IntervalPicardWeightedC2Bootstrap.slice_source_coeff_decay
      p (M := M) (G1 := G1s) (G2 := G2s) hα
      (iterateReprCoeff p u₀ n σΦ) (hbsumW σΦ hΦmem) (hagreeW σΦ hΦmem)
      (hposW σΦ hΦmem) (hubW σΦ hΦmem)
      (fun x hx => hG1w σΦ hΦmem x hx) (fun x hx => hG2w σΦ hΦmem x hx) k hk
    -- `aC s k = coeffs(logisticSourceFun … (lift(iter n σΦ))) k` by def.
    exact hdec
  -- ════ hagree: the clamped restart representation of `iter(n+1)` on `U` ════
  have hagreeU : ∀ s ∈ U, ∀ x : intervalDomainPoint,
      intervalDomainLift (picardIter p u₀ (n + 1) s) x.1
        = ∑' k, localRestartCoeff a₀ aC (s - τ) k * cosineMode k x.1 := by
    intro s hs x
    have hsmem := hUmem s hs
    have hτs : τ < s := lt_trans hτt₁ hs.1
    have hsd : s < d := hs.2
    have hx : x.1 ∈ Set.Icc (0 : ℝ) 1 := x.2
    -- canonical general iterate restart at base τ.
    have hgen := picardIterateRestart_general p hχ0 u₀ n hu₀_cont hu₀_bound hsrc0_n
      hτpos hτs (fun r hr hrs => hLs_cont r hr (le_trans hrs hsmem.2)) hx
    rw [hgen]
    refine tsum_congr (fun k => ?_)
    congr 1
    -- bridge canonical-shifted → clamped on the read range `[0, s−τ]`.
    refine localRestartCoeff_congr_on_Icc (by linarith) (fun σ hσ m => ?_) k
    -- `τ+σ ∈ [τ, s] ⊆ [c,d]`, so `φ(τ+σ)=τ+σ`; logisticLifted = logisticSourceFun∘lift.
    have hmem_cd : τ + σ ∈ Set.Icc τ d :=
      ⟨by linarith [hσ.1], by linarith [hσ.2, hsd.le]⟩
    change cosineCoeffs (logisticLifted p (picardIter p u₀ n (τ + σ))) m = aC σ m
    rw [haCdef]
    simp only
    rw [ShenWork.IntervalTimeSoftClamp.φ_eq_id_on hc'τ hdd' hmem_cd]
    exact ShenWork.Paper2.cosineCoeffs_congr_on_Icc
      (ShenWork.IntervalMildPicardRegularity.logisticLifted_eq_logisticSourceFun_on_Icc
        p (picardIter p u₀ n (τ + σ))) m
  -- base coefficient bound `|a₀ k| ≤ 2M` (from the (n+1)-slice continuity + ball sup).
  have ha₀_bound : ∀ k, |a₀ k| ≤ 2 * M := by
    intro k
    rw [ha₀def]
    have hgc : ContinuousOn (intervalDomainLift (picardIter p u₀ (n + 1) τ))
        (Set.Icc (0 : ℝ) 1) := hcontSlice1 τ hτpos (hcd.trans (hdd'.le.trans hd'T))
    have hbd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |intervalDomainLift (picardIter p u₀ (n + 1) τ) x| ≤ M := by
      intro x hx
      rw [abs_of_pos (hpos1 τ hτpos (hcd.trans (hdd'.le.trans hd'T)) x hx)]
      exact hub1 τ hτpos (hcd.trans (hdd'.le.trans hd'T)) x hx
    exact ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
      hgc hMnn hbd k
  -- K2 slice facts of `iter(n+1)` on `U`.
  have hposU : ∀ s ∈ U, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ (n + 1) s) x :=
    fun s hs x hx => hpos1 s (hUmem s hs).1 (hUmem s hs).2 x hx
  have hubU : ∀ s ∈ U, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (picardIter p u₀ (n + 1) s) x ≤ M :=
    fun s hs x hx => hub1 s (hUmem s hs).1 (hUmem s hs).2 x hx
  have hC2contU : ∀ s ∈ U,
      ContinuousOn (intervalDomainLift (picardIter p u₀ (n + 1) s)) (Set.Icc (0 : ℝ) 1) :=
    fun s hs => hcontSlice1 s (hUmem s hs).1 (hUmem s hs).2
  -- ════ the K1-full producer at offset τ with the clamped source ════
  obtain ⟨hderiv, hbound, hcont⟩ :=
    picardIterate_K1_full_from_restart_of_representation
      (p := p) (w := picardIter p u₀ (n + 1)) hα ha hb
      (M₀ := 2 * M) (by linarith) ha₀_bound
      srcC (B := Bwin / 2) (by linarith)
      hdecay hcontC
      (offset := τ) (t₁ := t₁) (t₂ := d) hτt₁ ht₁d
      hU_open hU_sub hU_off hagreeU (M := M) hposU hubU hC2contU
  -- restrict the three legs to `[lo,hi] ⊆ U`.
  refine ⟨fun σ k => cosineCoeffs
      (fun x => logisticSourceDot a₀ aC p (picardIter p u₀ (n + 1)) τ σ x) k, ?_, ?_, ?_⟩
  · intro σ hσ k; exact hderiv σ (hsubLoHi hσ) k
  · refine ⟨_, fun σ hσ k => hbound σ (hsubLoHi hσ) k⟩
  · intro k; exact (hcont k).mono hsubLoHi

/-! ## §6 — The all-levels wrapper `windowAdotLegs_all`.

Strong induction over the level `n`: the base is `windowAdotLegs_zero`, the step is
`windowAdotLegs_step` fed with the previous level's legs (the recursion).  All
hypotheses are taken level-uniformly (`∀ n, …`), in exactly the shapes the tower's
`TowerLevel`/cone genuinely return — no residual import. -/
theorem windowAdotLegs_all
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (u₀ : intervalDomainPoint → ℝ)
    {M T A₂ : ℝ}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hMnn : 0 ≤ M) (hA₂nn : 0 ≤ A₂)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M)
    (hsrc0 : ∀ n : ℕ, DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k))
    (hLs_cont : ∀ (n : ℕ) (r : ℝ), 0 < r → r ≤ T →
      Continuous (intervalLogisticSource p (picardIter p u₀ n r)))
    (hrepr_sum : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ T →
      Summable (fun k => (λ_ k) * |iterateReprCoeff p u₀ n σ k|))
    (hrepr_agree : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ T →
      Set.EqOn (intervalDomainLift (picardIter p u₀ n σ))
        (fun x => ∑' k, iterateReprCoeff p u₀ n σ k * cosineMode k x)
        (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ n σ) x)
    (hub : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (picardIter p u₀ n σ) x ≤ M)
    (hG1 : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ T → ∀ x : ℝ,
      |deriv (intervalDomainLift (picardIter p u₀ n σ)) x|
        ≤ ShenWork.IntervalPicardIterateUniform.G1profile p M σ)
    (hG2 : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ T → ∀ x : ℝ,
      |deriv (deriv (intervalDomainLift (picardIter p u₀ n σ))) x|
        ≤ ShenWork.IntervalPicardIterateUniform.G2profile A₂ σ)
    (hcontSlice : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ T →
      ContinuousOn (intervalDomainLift (picardIter p u₀ n σ)) (Set.Icc (0 : ℝ) 1)) :
    ∀ n lo hi, 0 < lo → lo ≤ hi → hi < T → WindowAdotLegs p u₀ n lo hi := by
  intro n
  induction n with
  | zero =>
    exact windowAdotLegs_zero p u₀ hα ha hb hMnn hu₀_cont hu₀_bound
      (hpos 0) (hub 0) (hcontSlice 0)
  | succ n ih =>
    exact windowAdotLegs_step p hχ0 u₀ n hα ha hb hMnn hA₂nn hu₀_cont hu₀_bound
      (hsrc0 n) (hLs_cont n) (hrepr_sum n) (hrepr_agree n) (hpos n) (hub n)
      (hG1 n) (hG2 n) (hpos (n + 1)) (hub (n + 1)) (hcontSlice (n + 1))
      (fun c' d' hc' hc'd' hd'T => ih c' d' hc' hc'd' hd'T)

end ShenWork.IntervalPicardWindowAdot
