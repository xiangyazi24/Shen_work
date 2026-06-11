/-
  ShenWork/Paper2/IntervalPicardIterateBddPackage.lean

  **W1b — the per-level patched-iterate-source `DuhamelSourceBddOn` package.**

  The old canonical-source route asked for a global `DuhamelSourceTimeC1` with an
  ℓ¹ envelope uniform down to `s = 0`, which is not the tower-produced object.
  This file uses the in-tower replacement: the satisfiable bounded-source package
  `DuhamelSourceBddOn (patchedSource p u₀ (picardIter p u₀ n)) τ`, whose
  time-continuity input lives on the closed window `[0, τ]` with the boundary
  handled by the unconditional initial approach.

  This file delivers the two W1b bricks:

  * **`patchedIterateSource_coeff_continuousOn`** — time-continuity of the patched
    iterate source coefficient family on `[0, τ]`, `0 < τ < T`.  This is the EXACT
    iterate mirror of
    `IntervalPicardLimitCoeffTimeCont.patchedSource_continuousWithinAt_zero`
    (boundary at `0`) glued to the interior legs, but:
      - the `s = 0` boundary uses the ITERATE initial approach
        `IntervalPicardIterateInitialApproach.picardIter_initialApproach`
        (W1a) instead of the limit-side `patchedSlice_timeContinuousAt_zero`;
      - the interior `s₀ ∈ (0, τ]` uses the `winAdot` legs
        (`IntervalPicardWindowAdot.WindowAdotLegs`) — the `HasDerivAt` leg gives
        `ContinuousAt` of the canonical coefficient, bridged to the patched family
        by `patchedSource_eq_of_pos` on the open right-neighborhood `Ioi (s₀/2)`.
    `τ < T` keeps the window `[s₀/2, τ]` strictly inside `(0, T)`, which the
    `WindowAdotLegs` predicate requires (`hi < T`).

  * **`iterateBddOn_of_facts`** — feeds
    `IntervalPicardIterateBddProducer.duhamelSourceBddOn_of_slices` with the
    continuity brick above, the datum-source-coefficient bound
    (`exists_datum_source_coeff_bound`), and the level-`n` representation /
    positivity / per-compact `K2` facts (taken in the `G1profile`/`G2profile`
    shapes the tower's `TowerLevel` carries, with a small per-compact adapter to
    the `∃ G1, ∀ σ ∈ Icc …` shape the producer wants).

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardIterateBddProducer
import ShenWork.Paper2.IntervalPicardIterateInitialApproach
import ShenWork.Paper2.IntervalPicardWindowAdot
import ShenWork.Paper2.IntervalPicardLimitCoeffConv
import ShenWork.Paper2.IntervalPicardWdataAssembly
import ShenWork.PDE.IntervalDuhamelSourceTimeC1On

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicardRegularity
  (logisticSourceFun logisticLifted_eq_logisticSourceFun_on_Icc)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalPicardLimitRestartBdd (DuhamelSourceBddOn)
open ShenWork.IntervalPicardLimitCoeffConv
  (cosineCoeffs_dist_le_of_sup logisticLifted_slice_dist_le)
open ShenWork.IntervalPicardLimitBddProducer (patchedSource patchedSource_eq_of_pos)
open ShenWork.IntervalPicardLimitBddHcontP
  (patchedSlice patchedSlice_of_nonpos patchedSlice_of_pos
   patchedSource_eq_coeff_slice lift_continuousOn_Icc)
open ShenWork.IntervalPicardWindowAdot (WindowAdotLegs)
open ShenWork.IntervalPicardIterateInitialApproach (picardIter_initialApproach)
open ShenWork.IntervalPicardIterateBddProducer
  (duhamelSourceBddOn_of_slices exists_datum_source_coeff_bound)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)

noncomputable section

namespace ShenWork.IntervalPicardIterateBddPackage

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## §0 — spatial continuity of the patched iterate slice's logistic source. -/

/-- **Continuity on `[0,1]` of the lifted logistic source of the patched iterate
slice.**  For `s > 0` (within `[0,τ] ⊆ [0,T]`) this is the cone's per-slice
`hcontSlice`; at `s = 0` it is the lifted datum.  The iterate analog of
`logisticLifted_patchedSlice_continuousOn` — no `GradientMildSolutionData`. -/
theorem logisticLifted_patchedIterateSlice_continuousOn
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ} (n : ℕ) {T : ℝ}
    (hu₀cont : Continuous u₀)
    (hcontSlice : ∀ (σ : ℝ), 0 < σ → σ ≤ T →
      ContinuousOn (intervalDomainLift (picardIter p u₀ n σ)) (Set.Icc (0 : ℝ) 1))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ContinuousOn (logisticLifted p (patchedSlice u₀ (picardIter p u₀ n) t))
      (Set.Icc (0 : ℝ) 1) := by
  -- `intervalDomainLift (patchedSlice …)` is continuous on `[0,1]`.
  have hcontLift : ContinuousOn
      (intervalDomainLift (patchedSlice u₀ (picardIter p u₀ n) t)) (Set.Icc (0 : ℝ) 1) := by
    rcases eq_or_lt_of_le ht.1 with ht0 | ht0
    · rw [patchedSlice_of_nonpos u₀ (picardIter p u₀ n) (le_of_eq ht0.symm)]
      exact lift_continuousOn_Icc hu₀cont
    · rw [patchedSlice_of_pos u₀ (picardIter p u₀ n) ht0]
      exact hcontSlice t ht0 ht.2
  -- `logisticLifted = logisticSourceFun (lift)` on `[0,1]`; the source is continuous.
  have hcontSrc : ContinuousOn
      (logisticSourceFun p.a p.b p.α
        (intervalDomainLift (patchedSlice u₀ (picardIter p u₀ n) t)))
      (Set.Icc (0 : ℝ) 1) := by
    unfold logisticSourceFun
    apply ContinuousOn.mul hcontLift
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.mul continuousOn_const
    exact ContinuousOn.rpow_const hcontLift (fun x _ => Or.inr p.hα.le)
  exact hcontSrc.congr
    (fun x hx => logisticLifted_eq_logisticSourceFun_on_Icc p
      (patchedSlice u₀ (picardIter p u₀ n) t) hx)

/-! ## §1 — the boundary leg at `s = 0` (iterate initial approach). -/

/-- **Boundary leg (`s = 0`), iterate side.**  Mirrors
`IntervalPicardLimitCoeffTimeCont.patchedSource_continuousWithinAt_zero` exactly,
swapping the sup-norm approach input from the limit-side
`patchedSlice_timeContinuousAt_zero` to the ITERATE
`picardIter_initialApproach` (W1a, level-uniform), and the slice spatial continuity
from `logisticLifted_patchedSlice_continuousOn` to the cone `hcontSlice`. -/
theorem patchedIterateSource_continuousWithinAt_zero
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (n : ℕ)
    (hu₀cont : Continuous u₀)
    {M T : ℝ} (hTpos : 0 < T) (hMpos : 0 < M)
    (hball : ∀ (m : ℕ) (s : ℝ), 0 < s → s ≤ T → ∀ y : intervalDomainPoint,
      |picardIter p u₀ m s y| ≤ M)
    (hpball : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y,
      |patchedSlice u₀ (picardIter p u₀ n) s y| ≤ M)
    (hpnn : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y,
      0 ≤ patchedSlice u₀ (picardIter p u₀ n) s y)
    (hcontSlice : ∀ (σ : ℝ), 0 < σ → σ ≤ T →
      ContinuousOn (intervalDomainLift (picardIter p u₀ n σ)) (Set.Icc (0 : ℝ) 1))
    {τ : ℝ} (hτT : τ ≤ T) (k : ℕ) :
    ContinuousWithinAt
      (fun s => patchedSource p u₀ (picardIter p u₀ n) s k) (Set.Icc 0 τ) 0 := by
  obtain ⟨Lc, hLc_pos, hLip⟩ := logisticLifted_slice_dist_le (p := p) hMpos
  -- the iterate sup-norm approach at level `n`: `picardIter n s → u₀` as `s → 0⁺`.
  have hApproach := picardIter_initialApproach p hχ0 hu₀cont hTpos hMpos hball n
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set η : ℝ := ε / (4 * Lc) with hηdef
  have hη_pos : 0 < η := by rw [hηdef]; positivity
  obtain ⟨δ, hδ_pos, hδ⟩ := hApproach η hη_pos
  refine ⟨δ, hδ_pos, ?_⟩
  intro s hsmem hsdist
  -- `s ∈ Icc 0 τ ⊆ Icc 0 T`.
  have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hsmem.1, le_trans hsmem.2 hτT⟩
  have h0T : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_refl 0, hTpos.le⟩
  rw [Real.dist_eq] at hsdist
  rw [Real.dist_eq, patchedSource_eq_coeff_slice, patchedSource_eq_coeff_slice]
  -- spatial continuity of both lifted patched profiles on `[0,1]`.
  have hcont_s := logisticLifted_patchedIterateSlice_continuousOn p n hu₀cont hcontSlice hsT
  have hcont_0 := logisticLifted_patchedIterateSlice_continuousOn p n hu₀cont hcontSlice h0T
  -- pointwise slice distance bound on `[0,1]`.
  have hsup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |logisticLifted p (patchedSlice u₀ (picardIter p u₀ n) s) x
        - logisticLifted p (patchedSlice u₀ (picardIter p u₀ n) 0) x| ≤ Lc * η := by
    intro x hx
    have hxlt : |patchedSlice u₀ (picardIter p u₀ n) s ⟨x, hx⟩
        - patchedSlice u₀ (picardIter p u₀ n) 0 ⟨x, hx⟩| ≤ η := by
      -- `patchedSlice … 0 = u₀`; for `0 < s`, `patchedSlice … s = picardIter n s`,
      -- and the approach gives `|picardIter n s ⟨x⟩ − u₀ ⟨x⟩| < η`.
      rw [patchedSlice_of_nonpos u₀ (picardIter p u₀ n) (le_refl 0)]
      rcases eq_or_lt_of_le hsmem.1 with hs0 | hs0
      · rw [← hs0, patchedSlice_of_nonpos u₀ (picardIter p u₀ n) (le_refl 0)]
        simp only [sub_self, abs_zero]; exact hη_pos.le
      · rw [patchedSlice_of_pos u₀ (picardIter p u₀ n) hs0]
        have hsltδ : s < δ := by
          have : |s| < δ := by simpa using hsdist
          rwa [abs_of_pos hs0] at this
        exact (hδ s hs0 hsltδ ⟨x, hx⟩).le
    calc |logisticLifted p (patchedSlice u₀ (picardIter p u₀ n) s) x
            - logisticLifted p (patchedSlice u₀ (picardIter p u₀ n) 0) x|
        ≤ Lc * |patchedSlice u₀ (picardIter p u₀ n) s ⟨x, hx⟩
                - patchedSlice u₀ (picardIter p u₀ n) 0 ⟨x, hx⟩| :=
          hLip (patchedSlice u₀ (picardIter p u₀ n) s)
            (patchedSlice u₀ (picardIter p u₀ n) 0)
            (hpball s hsT) (hpnn s hsT) (hpball 0 h0T) (hpnn 0 h0T) hx
      _ ≤ Lc * η := mul_le_mul_of_nonneg_left hxlt hLc_pos.le
  have hLcη_nn : (0 : ℝ) ≤ Lc * η := mul_nonneg hLc_pos.le hη_pos.le
  have hbound := cosineCoeffs_dist_le_of_sup hcont_s hcont_0 hLcη_nn hsup k
  have hlt : 2 * (Lc * η) < ε := by
    rw [hηdef]
    have hsimp : 2 * (Lc * (ε / (4 * Lc))) = ε / 2 := by
      field_simp; ring
    rw [hsimp]; linarith
  exact lt_of_le_of_lt hbound hlt

/-! ## §2 — the glue: `hcontP` on `[0, τ]` from boundary + winAdot interior. -/

/-- **Deliverable 1 — patched iterate source coefficient time-continuity on
`[0, τ]`.**  For `0 < τ < T`, the patched level-`n` iterate source coefficient is
time-continuous on the CLOSED window `[0, τ]`:

* at `s = 0` by `patchedIterateSource_continuousWithinAt_zero` (W1a);
* at `s₀ ∈ (0, τ]` by the `winAdot` legs on `[s₀/2, τ] ⊂ (0, T)`: the `HasDerivAt`
  leg gives `ContinuousAt σ` of the canonical `logisticSourceFun ∘ lift`
  coefficient; bridge to `logisticLifted` (`cosineCoeffs_congr_on_Icc`) and to the
  patched family (`patchedSource_eq_of_pos`) on the open right-neighborhood
  `Ioi (s₀/2)`, then push `ContinuousWithinAt` to `𝓝[Icc 0 τ] s₀`.

`τ < T` is exactly what keeps every interior window `[s₀/2, τ]` strictly inside
`(0, T)` so `WindowAdotLegs` (which requires `hi < T`) applies. -/
theorem patchedIterateSource_coeff_continuousOn
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (n : ℕ)
    (hu₀cont : Continuous u₀)
    {M T : ℝ} (hTpos : 0 < T) (hMpos : 0 < M)
    (hball : ∀ (m : ℕ) (s : ℝ), 0 < s → s ≤ T → ∀ y : intervalDomainPoint,
      |picardIter p u₀ m s y| ≤ M)
    (hpball : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y,
      |patchedSlice u₀ (picardIter p u₀ n) s y| ≤ M)
    (hpnn : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y,
      0 ≤ patchedSlice u₀ (picardIter p u₀ n) s y)
    (hcontSlice : ∀ (σ : ℝ), 0 < σ → σ ≤ T →
      ContinuousOn (intervalDomainLift (picardIter p u₀ n σ)) (Set.Icc (0 : ℝ) 1))
    -- the level-`n` window source-derivative legs (the tower's `TowerLevel.winAdot`).
    (winAdot : ∀ lo hi, 0 < lo → lo ≤ hi → hi < T → WindowAdotLegs p u₀ n lo hi)
    {τ : ℝ} (_hτ : 0 < τ) (hτT : τ < T) (k : ℕ) :
    ContinuousOn (fun s => patchedSource p u₀ (picardIter p u₀ n) s k) (Set.Icc 0 τ) := by
  -- pointwise `ContinuousWithinAt` on `[0, τ]`.
  intro s₀ hs₀
  rcases eq_or_lt_of_le hs₀.1 with hs₀0 | hs₀pos
  · -- boundary: `s₀ = 0`.
    subst hs₀0
    exact patchedIterateSource_continuousWithinAt_zero p hχ0 n hu₀cont hTpos hMpos
      hball hpball hpnn hcontSlice hτT.le k
  · -- interior: `s₀ ∈ (0, τ]`; window `[s₀/2, τ] ⊂ (0, T)`.
    set lo : ℝ := s₀ / 2 with hlodef
    have hlopos : 0 < lo := by rw [hlodef]; linarith
    have hlos₀ : lo < s₀ := by rw [hlodef]; linarith
    have hloτ : lo ≤ τ := le_trans hlos₀.le hs₀.2
    have hs₀τ : s₀ ≤ τ := hs₀.2
    -- the winAdot legs on `[lo, τ]`: extract the `HasDerivAt` derivative leg.
    obtain ⟨adot, hderiv, _hbound, _hcont⟩ := winAdot lo τ hlopos hloτ hτT
    -- `ContinuousAt s₀` of the canonical `logisticSourceFun ∘ lift` coefficient.
    have hcanonCA : ContinuousAt
        (fun r => cosineCoeffs
          (logisticSourceFun p.a p.b p.α (intervalDomainLift (picardIter p u₀ n r))) k) s₀ :=
      (hderiv s₀ ⟨hlos₀.le, hs₀τ⟩ k).continuousAt
    -- bridge to the `logisticLifted` coefficient (pointwise on ℝ, congruence on [0,1]).
    have hbridge : (fun r => cosineCoeffs
          (logisticSourceFun p.a p.b p.α (intervalDomainLift (picardIter p u₀ n r))) k)
        = (fun r => cosineCoeffs (logisticLifted p (picardIter p u₀ n r)) k) := by
      funext r
      exact (ShenWork.Paper2.cosineCoeffs_congr_on_Icc
        (fun x hx => (logisticLifted_eq_logisticSourceFun_on_Icc p
          (picardIter p u₀ n r) hx).symm) k)
    rw [hbridge] at hcanonCA
    -- equal to `patchedSource` on the open right-neighborhood `Ioi lo` of `s₀`.
    have hcwa_open : ContinuousWithinAt
        (fun s => patchedSource p u₀ (picardIter p u₀ n) s k) (Set.Ioi lo) s₀ := by
      have hEq : Set.EqOn
          (fun s => patchedSource p u₀ (picardIter p u₀ n) s k)
          (fun s => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
          (Set.Ioi lo) := by
        intro s hs
        have hspos : 0 < s := lt_trans hlopos hs
        change patchedSource p u₀ (picardIter p u₀ n) s k
          = cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k
        rw [patchedSource_eq_of_pos p u₀ (picardIter p u₀ n) hspos k]
      have hca : ContinuousWithinAt
          (fun s => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
          (Set.Ioi lo) s₀ := hcanonCA.continuousWithinAt
      exact hca.congr (fun s hs => hEq hs) (hEq hlos₀)
    -- push `ContinuousWithinAt (Ioi lo)` to `𝓝[Icc 0 τ] s₀`.
    refine hcwa_open.mono_of_mem_nhdsWithin ?_
    rw [mem_nhdsWithin]
    exact ⟨Set.Ioi lo, isOpen_Ioi, hlos₀, fun x hx => hx.1⟩

/-- Endpoint-inclusive patched source coefficient continuity on `[0, τ]`.

The positive-time points use the already-produced closed-window source
`TimeC1On` package on `[s₀ / 2, T]`; the `s₀ = 0` boundary is the same initial
approach leg as the strict-interior package. -/
theorem patchedIterateSource_coeff_continuousOn_endpoint
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (n : ℕ)
    (hu₀cont : Continuous u₀)
    {M T : ℝ} (hTpos : 0 < T) (hMpos : 0 < M)
    (hball : ∀ (m : ℕ) (s : ℝ), 0 < s → s ≤ T → ∀ y : intervalDomainPoint,
      |picardIter p u₀ m s y| ≤ M)
    (hpball : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y,
      |patchedSlice u₀ (picardIter p u₀ n) s y| ≤ M)
    (hpnn : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y,
      0 ≤ patchedSlice u₀ (picardIter p u₀ n) s y)
    (hcontSlice : ∀ (σ : ℝ), 0 < σ → σ ≤ T →
      ContinuousOn (intervalDomainLift (picardIter p u₀ n σ)) (Set.Icc (0 : ℝ) 1))
    (srcOn : ∀ c, 0 < c → c < T →
      DuhamelSourceTimeC1On
        (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
        c T)
    {τ : ℝ} (_hτ : 0 < τ) (hτT : τ ≤ T) (k : ℕ) :
    ContinuousOn (fun s => patchedSource p u₀ (picardIter p u₀ n) s k)
      (Set.Icc 0 τ) := by
  intro s₀ hs₀
  rcases eq_or_lt_of_le hs₀.1 with hs₀0 | hs₀pos
  · subst hs₀0
    exact patchedIterateSource_continuousWithinAt_zero p hχ0 n hu₀cont hTpos hMpos
      hball hpball hpnn hcontSlice hτT k
  · set c : ℝ := s₀ / 2 with hcdef
    have hcpos : 0 < c := by rw [hcdef]; linarith
    have hcs₀ : c < s₀ := by rw [hcdef]; linarith
    have hs₀T : s₀ ≤ T := le_trans hs₀.2 hτT
    have hcT : c < T := lt_of_lt_of_le hcs₀ hs₀T
    have src := srcOn c hcpos hcT
    have hs₀cT : s₀ ∈ Set.Icc c T := ⟨hcs₀.le, hs₀T⟩
    have hcanon : ContinuousWithinAt
        (fun s => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
        (Set.Icc c T) s₀ :=
      (src.hderiv s₀ hs₀cT k).continuousWithinAt
    have hpatch : ContinuousWithinAt
        (fun s => patchedSource p u₀ (picardIter p u₀ n) s k)
        (Set.Icc c T) s₀ := by
      have hEq : Set.EqOn
          (fun s => patchedSource p u₀ (picardIter p u₀ n) s k)
          (fun s => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
          (Set.Icc c T) := by
        intro s hs
        exact patchedSource_eq_of_pos p u₀ (picardIter p u₀ n)
          (lt_of_lt_of_le hcpos hs.1) k
      exact hcanon.congr (fun s hs => hEq hs) (hEq hs₀cT)
    refine hpatch.mono_of_mem_nhdsWithin ?_
    rw [mem_nhdsWithin]
    exact ⟨Set.Ioi c, isOpen_Ioi, hcs₀, fun x hx =>
      ⟨hx.1.le, le_trans hx.2.2 hτT⟩⟩

/-! ## §3 — Deliverable 2: the `DuhamelSourceBddOn` package. -/

/-- **Per-compact `K2` adapter (gradient).**  Turns the `G1profile`-shaped tower
bound into the `∃ G1, ∀ σ ∈ Icc a' b', …` shape `duhamelSourceBddOn_of_slices`
wants, using `G1profile_le_G1win` on the compact `[a', b'] ⊆ (0, T)`. -/
theorem hG1t_of_profile
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ} (n : ℕ) {M T : ℝ} (hMnn : 0 ≤ M)
    (hG1 : ∀ (σ : ℝ), 0 < σ → σ ≤ T → ∀ x : ℝ,
      |deriv (intervalDomainLift (picardIter p u₀ n σ)) x|
        ≤ ShenWork.IntervalPicardIterateUniform.G1profile p M σ)
    (a' b' : ℝ) (ha' : 0 < a') (hb'T : b' ≤ T) :
    ∃ G1, ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (picardIter p u₀ n σ)) x| ≤ G1 := by
  refine ⟨ShenWork.IntervalPicardWdataAssembly.G1win p M a' b', fun σ hσ x _hx => ?_⟩
  have hσpos : 0 < σ := lt_of_lt_of_le ha' hσ.1
  have hσT : σ ≤ T := le_trans hσ.2 hb'T
  exact le_trans (hG1 σ hσpos hσT x)
    (ShenWork.IntervalPicardWdataAssembly.G1profile_le_G1win hMnn ha' hσ.1 hσ.2)

/-- **Per-compact `K2` adapter (Hessian).**  Same as `hG1t_of_profile` for the
second derivative via `G2profile_le_G2win`. -/
theorem hG2t_of_profile
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ} (n : ℕ) {A₂ T : ℝ}
    (hA₂nn : 0 ≤ A₂)
    (hG2 : ∀ (σ : ℝ), 0 < σ → σ ≤ T → ∀ x : ℝ,
      |deriv (deriv (intervalDomainLift (picardIter p u₀ n σ))) x|
        ≤ ShenWork.IntervalPicardIterateUniform.G2profile A₂ σ)
    (a' b' : ℝ) (ha' : 0 < a') (hb'T : b' ≤ T) :
    ∃ G2, ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (picardIter p u₀ n σ))) x| ≤ G2 := by
  refine ⟨ShenWork.IntervalPicardWdataAssembly.G2win A₂ a', fun σ hσ x _hx => ?_⟩
  have hσpos : 0 < σ := lt_of_lt_of_le ha' hσ.1
  have hσT : σ ≤ T := le_trans hσ.2 hb'T
  exact le_trans (hG2 σ hσpos hσT x)
    (ShenWork.IntervalPicardWdataAssembly.G2profile_le_G2win hA₂nn ha' hσ.1)

/-- **Deliverable 2 — the per-level iterate `DuhamelSourceBddOn` package.**
For `0 < τ < T`, the patched level-`n` iterate source family is a satisfiable
`DuhamelSourceBddOn` on `[0, τ]`, assembled from
`duhamelSourceBddOn_of_slices` fed with:

* the datum-source-coefficient bound (`exists_datum_source_coeff_bound`) for the
  `s ≤ 0` branch;
* the level-`n` cosine representation triple (`bc`/`hbsum`/`hagree`) + slice
  positivity/sup (`hpost`/`hubt`) — the `TowerLevel n` carrier data;
* the per-compact `K2` gradient/Hessian bounds via the `G1profile`/`G2profile`
  adapters above;
* deliverable 1 (`patchedIterateSource_coeff_continuousOn`) as the `hcontP` input.

  All hypotheses are tower-internal; no global ℓ¹-at-`s=0` source package is
  assumed. -/
noncomputable def iterateBddOn_of_facts
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (n : ℕ)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀cont : Continuous u₀)
    {M T A₂ Msup : ℝ} (hTpos : 0 < T) (hMpos : 0 < M)
    (hMsup_nn : 0 ≤ Msup) (hA₂nn : 0 ≤ A₂)
    -- ball facts on `(0,T]`, for the boundary leg's initial approach.
    (hball : ∀ (m : ℕ) (s : ℝ), 0 < s → s ≤ T → ∀ y : intervalDomainPoint,
      |picardIter p u₀ m s y| ≤ M)
    (hpball : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y,
      |patchedSlice u₀ (picardIter p u₀ n) s y| ≤ M)
    (hpnn : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y,
      0 ≤ patchedSlice u₀ (picardIter p u₀ n) s y)
    (hcontSlice : ∀ (σ : ℝ), 0 < σ → σ ≤ T →
      ContinuousOn (intervalDomainLift (picardIter p u₀ n σ)) (Set.Icc (0 : ℝ) 1))
    -- level-`n` cosine representation triple + slice positivity/sup on `(0,T]`.
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ ≤ T →
      Summable (fun m => unitIntervalCosineEigenvalue m * |bc σ m|))
    (hagree : ∀ σ, 0 < σ → σ ≤ T → Set.EqOn (intervalDomainLift (picardIter p u₀ n σ))
        (fun x => ∑' m, bc σ m * cosineMode m x) (Set.Icc (0 : ℝ) 1))
    (hpost : ∀ σ, 0 < σ → σ ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ n σ) x)
    (hubt : ∀ σ, 0 < σ → σ ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (picardIter p u₀ n σ) x ≤ Msup)
    -- per-compact `K2` in the `G1profile`/`G2profile` tower shapes.
    (hG1 : ∀ (σ : ℝ), 0 < σ → σ ≤ T → ∀ x : ℝ,
      |deriv (intervalDomainLift (picardIter p u₀ n σ)) x|
        ≤ ShenWork.IntervalPicardIterateUniform.G1profile p Msup σ)
    (hG2 : ∀ (σ : ℝ), 0 < σ → σ ≤ T → ∀ x : ℝ,
      |deriv (deriv (intervalDomainLift (picardIter p u₀ n σ))) x|
        ≤ ShenWork.IntervalPicardIterateUniform.G2profile A₂ σ)
    -- the level-`n` window source-derivative legs (the tower's `TowerLevel.winAdot`).
    (winAdot : ∀ lo hi, 0 < lo → lo ≤ hi → hi < T → WindowAdotLegs p u₀ n lo hi)
    {τ : ℝ} (hτ : 0 < τ) (hτT : τ < T) :
    DuhamelSourceBddOn (patchedSource p u₀ (picardIter p u₀ n)) τ :=
  -- the `s ≤ 0` datum-source-coefficient bound (via `Classical.choose`, since the
  -- conclusion is data — `obtain` on the Prop-existential cannot eliminate here).
  duhamelSourceBddOn_of_slices p u₀ (picardIter p u₀ n) hα ha hb
    (Classical.choose_spec (exists_datum_source_coeff_bound p u₀ hα ha hb hu₀cont)).1
    (Classical.choose_spec (exists_datum_source_coeff_bound p u₀ hα ha hb hu₀cont)).2
    bc hbsum hagree hpost hubt
    (hG1t_of_profile p n hMsup_nn hG1)
    (hG2t_of_profile p n hA₂nn hG2)
    hτ hτT.le
    -- deliverable 1: the patched-coefficient time-continuity on `[0,τ]`.
    (fun k => patchedIterateSource_coeff_continuousOn p hχ0 n hu₀cont hTpos hMpos
      hball hpball hpnn hcontSlice winAdot hτ hτT k)

/-- **Endpoint-inclusive per-level iterate `DuhamelSourceBddOn` package.**

This variant reaches `τ = T`.  Its positive-time coefficient continuity is read
from the in-tower `TimeC1On` source package on `[c,T]`; all bounds and
representation inputs are the same closed-horizon tower facts as
`iterateBddOn_of_facts`. -/
noncomputable def iterateBddOn_endpoint_of_facts
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (n : ℕ)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀cont : Continuous u₀)
    {M T A₂ Msup : ℝ} (hTpos : 0 < T) (hMpos : 0 < M)
    (hMsup_nn : 0 ≤ Msup) (hA₂nn : 0 ≤ A₂)
    (hball : ∀ (m : ℕ) (s : ℝ), 0 < s → s ≤ T → ∀ y : intervalDomainPoint,
      |picardIter p u₀ m s y| ≤ M)
    (hpball : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y,
      |patchedSlice u₀ (picardIter p u₀ n) s y| ≤ M)
    (hpnn : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y,
      0 ≤ patchedSlice u₀ (picardIter p u₀ n) s y)
    (hcontSlice : ∀ (σ : ℝ), 0 < σ → σ ≤ T →
      ContinuousOn (intervalDomainLift (picardIter p u₀ n σ)) (Set.Icc (0 : ℝ) 1))
    (srcOn : ∀ c, 0 < c → c < T →
      DuhamelSourceTimeC1On
        (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
        c T)
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ ≤ T →
      Summable (fun m => unitIntervalCosineEigenvalue m * |bc σ m|))
    (hagree : ∀ σ, 0 < σ → σ ≤ T → Set.EqOn (intervalDomainLift (picardIter p u₀ n σ))
        (fun x => ∑' m, bc σ m * cosineMode m x) (Set.Icc (0 : ℝ) 1))
    (hpost : ∀ σ, 0 < σ → σ ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ n σ) x)
    (hubt : ∀ σ, 0 < σ → σ ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (picardIter p u₀ n σ) x ≤ Msup)
    (hG1 : ∀ (σ : ℝ), 0 < σ → σ ≤ T → ∀ x : ℝ,
      |deriv (intervalDomainLift (picardIter p u₀ n σ)) x|
        ≤ ShenWork.IntervalPicardIterateUniform.G1profile p Msup σ)
    (hG2 : ∀ (σ : ℝ), 0 < σ → σ ≤ T → ∀ x : ℝ,
      |deriv (deriv (intervalDomainLift (picardIter p u₀ n σ))) x|
        ≤ ShenWork.IntervalPicardIterateUniform.G2profile A₂ σ)
    {τ : ℝ} (hτ : 0 < τ) (hτT : τ ≤ T) :
    DuhamelSourceBddOn (patchedSource p u₀ (picardIter p u₀ n)) τ :=
  duhamelSourceBddOn_of_slices p u₀ (picardIter p u₀ n) hα ha hb
    (Classical.choose_spec (exists_datum_source_coeff_bound p u₀ hα ha hb hu₀cont)).1
    (Classical.choose_spec (exists_datum_source_coeff_bound p u₀ hα ha hb hu₀cont)).2
    bc hbsum hagree hpost hubt
    (hG1t_of_profile p n hMsup_nn hG1)
    (hG2t_of_profile p n hA₂nn hG2)
    hτ hτT
    (fun k => patchedIterateSource_coeff_continuousOn_endpoint p hχ0 n hu₀cont
      hTpos hMpos hball hpball hpnn hcontSlice srcOn hτ hτT k)

end ShenWork.IntervalPicardIterateBddPackage
