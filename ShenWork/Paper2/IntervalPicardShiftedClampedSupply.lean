/-
  ShenWork/Paper2/IntervalPicardShiftedClampedSupply.lean

  **K1 endgame W3 — the σ/2-shifted clamped source brick (`hsrc0`-free).**

  The tower's `tower_succ` site `hsrcσ` builds the `σ/2`-shifted canonical level-`n`
  source `DuhamelSourceTimeC1` by `shiftedSource_timeC1` applied to the GLOBAL
  canonical package `hsrc0` — the unfillable ℓ¹-at-`s = 0` residual.  This file
  dissolves that dependency for the two `hsrcσ` consumers (`hbsum_succ` and the G2
  engine `iterate_abs_deriv2_le_of_windowDecay`) by building a GLOBAL CLAMPED
  `DuhamelSourceTimeC1` whose family AGREES with the `σ/2`-shifted canonical source
  on the read window `[0, σ/2]`, using only the level-`n` `winAdot` data.

  KEY: the shift offset `τ = σ/2` keeps the read times `τ + s ∈ [σ/2, σ] ⊆ (0,T]`,
  i.e. no `t → 0` disease.  This is exactly
  `clampedIterateSource_duhamelSourceTimeC1` in the shifted frame: we instantiate
  the underlying generic producer `clampedSource_duhamelSourceTimeC1` with shift
  `τ := σ/2`, id-zone `[c,d] := [σ/2, σ]`, padded window `[c',d'] := [σ/4, (σ+T)/2]`
  (`⊂ (0,T)`).  The id-zone agreement (`clampedFamily_eq_on`) at the shifted times
  `τ + s = σ/2 + s ∈ [σ/2, σ] = [c,d]` plus the `logisticSourceFun ↔ logisticLifted`
  bridge (`cosineCoeffs_congr_on_Icc` + `logisticLifted_eq_logisticSourceFun_on_Icc`)
  gives the read-window agreement, mirroring `clampedIterateSource…`.

  The window facts on `[c',d']` (representation triple, ball, scalar `G1`/`G2`) and
  the `winAdot` legs are the level-`n` carrier data fed in exactly as
  `windowAdotLegs_step` feeds the clamp producer at offset `lo/2`.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardIterateTimeC1Full
import ShenWork.Paper2.IntervalPicardWindowAdot
import ShenWork.Paper2.IntervalPicardWdataAssembly
import ShenWork.Paper2.IntervalPicardWeightedC2Bootstrap

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalMildPicardRegularity (logisticSourceFun)
open ShenWork.IntervalPicardIterateRepresentation (iterateReprCoeff)
open ShenWork.IntervalPicardWindowAdot (WindowAdotLegs)
open ShenWork.Paper2.ClampedSourceRepresentation
  (clampedSource_duhamelSourceTimeC1 clampedFamily_eq_on)
open ShenWork.IntervalTimeSoftClamp (φ φ_mem_range)

noncomputable section

namespace ShenWork.IntervalPicardShiftedClampedSupply

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## §1 — The σ/2-shifted clamped level-`n` source package, wall-free.

For a fixed positive horizon `σ ≤ T`, the read window is `[0, σ/2]`, i.e. shifted
times `[σ/2, σ]`.  Padding to `[σ/4, (σ+T)/2] ⊂ (0,T)` and clamping with offset
`τ = σ/2` and id-zone `[σ/2, σ]`, the generic producer
`clampedSource_duhamelSourceTimeC1` returns a GLOBAL `DuhamelSourceTimeC1` whose
family agrees with the shifted canonical source on `[0, σ/2]`. -/

/-- **`clampedShiftedSource_duhamelSourceTimeC1`.**

The level-`n` window data (representation triple `bc`/`hbsum`/`hagree`, ball facts
`hpos`/`hub`, spatial profiles `hG1`/`hG2`, and the `winAdot` legs) on the padded
window `[σ/4, (σ+T)/2]` produce a GLOBAL clamped `DuhamelSourceTimeC1` of the
`σ/2`-shifted level-`n` canonical source, AGREEING with the canonical shifted family
`s ↦ cosineCoeffs (logisticLifted p (picardIter p u₀ n (σ/2 + s)))` on `[0, σ/2]`
(the read window of `hbsum_succ`/the G2 windowDecay engine).  No `hsrc0`. -/
theorem clampedShiftedSource_duhamelSourceTimeC1
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    {M T A₂ : ℝ}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hMnn : 0 ≤ M) (hA₂nn : 0 ≤ A₂)
    {σ : ℝ} (hσ : 0 < σ) (hσT : σ < T)
    -- level-`n` representation triple on `(0,T]` (the `TowerLevel n` data).
    (hrepr_sum : ∀ s, 0 < s → s ≤ T →
      Summable (fun k => (λ_ k) * |iterateReprCoeff p u₀ n s k|))
    (hrepr_agree : ∀ s, 0 < s → s ≤ T →
      Set.EqOn (intervalDomainLift (picardIter p u₀ n s))
        (fun x => ∑' k, iterateReprCoeff p u₀ n s k * cosineMode k x)
        (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ s, 0 < s → s ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ n s) x)
    (hub : ∀ s, 0 < s → s ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (picardIter p u₀ n s) x ≤ M)
    (hG1 : ∀ s, 0 < s → s ≤ T → ∀ x : ℝ,
      |deriv (intervalDomainLift (picardIter p u₀ n s)) x|
        ≤ ShenWork.IntervalPicardIterateUniform.G1profile p M s)
    (hG2 : ∀ s, 0 < s → s ≤ T → ∀ x : ℝ,
      |deriv (deriv (intervalDomainLift (picardIter p u₀ n s))) x|
        ≤ ShenWork.IntervalPicardIterateUniform.G2profile A₂ s)
    -- the level-`n` adot legs on the padded window (the `winAdot` supply).
    (winAdot : ∀ lo hi, 0 < lo → lo ≤ hi → hi < T → WindowAdotLegs p u₀ n lo hi) :
    ∃ asrc : ℝ → ℕ → ℝ, ∃ _ : DuhamelSourceTimeC1 asrc,
      ∀ s ∈ Set.Icc (0 : ℝ) (σ / 2), ∀ k,
        asrc s k = cosineCoeffs (logisticLifted p (picardIter p u₀ n (σ / 2 + s))) k := by
  classical
  -- offset τ = σ/2, id-zone [c,d] = [σ/2, σ], padded [c',d'] = [σ/4, (σ+T)/2].
  set τ : ℝ := σ / 2 with hτdef
  set c' : ℝ := σ / 4 with hc'def
  set d' : ℝ := (σ + T) / 2 with hd'def
  have hτpos : 0 < τ := by rw [hτdef]; positivity
  have hc'pos : 0 < c' := by rw [hc'def]; positivity
  have hc'τ : c' < τ := by rw [hc'def, hτdef]; linarith
  have hcd : τ ≤ σ := by rw [hτdef]; linarith
  have hdd' : σ < d' := by rw [hd'def]; linarith
  have hd'Tlt : d' < T := by rw [hd'def]; linarith
  have hd'T : d' ≤ T := le_of_lt hd'Tlt
  have hc'd' : c' ≤ d' := le_of_lt (lt_trans hc'τ (lt_of_le_of_lt hcd hdd'))
  -- window membership helpers on [c',d'] ⊆ (0,T].
  have hcd'_pos : ∀ s ∈ Set.Icc c' d', 0 < s := fun s hs => lt_of_lt_of_le hc'pos hs.1
  have hcd'_T : ∀ s ∈ Set.Icc c' d', s ≤ T := fun s hs => le_trans hs.2 hd'T
  -- window-uniform scalar G1/G2 on [c',d'].
  set G1s : ℝ := ShenWork.IntervalPicardWdataAssembly.G1win p M c' d' with hG1sdef
  set G2s : ℝ := ShenWork.IntervalPicardWdataAssembly.G2win A₂ c' with hG2sdef
  have hG1w : ∀ s ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (picardIter p u₀ n s)) x| ≤ G1s := by
    intro s hs x _hx
    exact le_trans (hG1 s (hcd'_pos s hs) (hcd'_T s hs) x)
      (ShenWork.IntervalPicardWdataAssembly.G1profile_le_G1win hMnn hc'pos hs.1 hs.2)
  have hG2w : ∀ s ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (picardIter p u₀ n s))) x| ≤ G2s := by
    intro s hs x _hx
    exact le_trans (hG2 s (hcd'_pos s hs) (hcd'_T s hs) x)
      (ShenWork.IntervalPicardWdataAssembly.G2profile_le_G2win hA₂nn hc'pos hs.1)
  -- the level-n adot legs on [c',d'] (the winAdot supply).
  obtain ⟨adotn, hadotn_deriv, ⟨Mdotn, hadotn_bound⟩, hadotn_cont⟩ :=
    winAdot c' d' hc'pos hc'd' hd'Tlt
  -- representation triple on [c',d'] (from the (0,T] form).
  have hbsumW : ∀ s ∈ Set.Icc c' d',
      Summable (fun k => unitIntervalCosineEigenvalue k * |iterateReprCoeff p u₀ n s k|) :=
    fun s hs => hrepr_sum s (hcd'_pos s hs) (hcd'_T s hs)
  have hagreeW : ∀ s ∈ Set.Icc c' d',
      Set.EqOn (intervalDomainLift (picardIter p u₀ n s))
        (fun x => ∑' k, iterateReprCoeff p u₀ n s k * cosineMode k x) (Set.Icc (0 : ℝ) 1) :=
    fun s hs => hrepr_agree s (hcd'_pos s hs) (hcd'_T s hs)
  have hposW : ∀ s ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ n s) x :=
    fun s hs x hx => hpos s (hcd'_pos s hs) (hcd'_T s hs) x hx
  have hubW : ∀ s ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (picardIter p u₀ n s) x ≤ M :=
    fun s hs x hx => hub s (hcd'_pos s hs) (hcd'_T s hs) x hx
  -- the GLOBAL clamped level-n source family at offset τ = σ/2, id-zone [τ, σ].
  refine ⟨fun s k => cosineCoeffs (logisticSourceFun p.a p.b p.α
      (intervalDomainLift (picardIter p u₀ n (φ c' τ σ d' (τ + s))))) k, ?_, ?_⟩
  · exact clampedSource_duhamelSourceTimeC1 p (picardIter p u₀ n) hα ha hb
      (τ := τ) (c' := c') (c := τ) (d := σ) (d' := d') hc'τ hcd hdd'
      (iterateReprCoeff p u₀ n) hbsumW hagreeW hposW hubW hG1w hG2w
      adotn hadotn_deriv hadotn_cont hadotn_bound
  · -- agreement on the read window [0, σ/2]: shifted times τ + s ∈ [σ/2, σ] = [c,d].
    intro s hs k
    have hmem_cd : τ + s ∈ Set.Icc τ σ :=
      ⟨by linarith [hs.1], by rw [hτdef]; linarith [hs.2]⟩
    -- clamp is the identity there → equals the genuine level-n logisticSourceFun coeff.
    have hclamp := clampedFamily_eq_on p (picardIter p u₀ n)
      (τ := τ) (c' := c') (c := τ) (d := σ) (d' := d') hc'τ hdd' hmem_cd k
    -- bridge logisticSourceFun ∘ lift ↔ logisticLifted on [0,1] (equal cosine coeffs).
    have hbridge :
        cosineCoeffs (logisticSourceFun p.a p.b p.α
            (intervalDomainLift (picardIter p u₀ n (τ + s)))) k
          = cosineCoeffs (logisticLifted p (picardIter p u₀ n (σ / 2 + s))) k := by
      rw [hτdef]
      exact (ShenWork.Paper2.cosineCoeffs_congr_on_Icc
        (ShenWork.IntervalMildPicardRegularity.logisticLifted_eq_logisticSourceFun_on_Icc
          p (picardIter p u₀ n (σ / 2 + s))) k).symm
    change cosineCoeffs (logisticSourceFun p.a p.b p.α
        (intervalDomainLift (picardIter p u₀ n (φ c' τ σ d' (τ + s))))) k
      = cosineCoeffs (logisticLifted p (picardIter p u₀ n (σ / 2 + s))) k
    rw [hclamp, hbridge]

end ShenWork.IntervalPicardShiftedClampedSupply
