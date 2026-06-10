/-
  ShenWork/Paper2/IntervalPicardSourceTower.lean

  **Tower campaign stage 2 — the tower carrier + induction (items 11–13).**

  The executable WINDOW/LOCAL-WITNESS tower of the ChatGPT tower verdict
  (`HANDOFF/chatgpt-tower-verdict.md`).  For each Picard level `n`, `TowerLevel`
  packages exactly the per-level reproducible content the endgame consumes:

    * `hrepr_sum`/`hrepr_agree` — the horizon-local cosine representation triple
      (`iterateReprCoeff`), eigenvalue-weighted summable + `[0,1]` agreement, on
      `0 < σ ≤ T`;
    * `hG1`/`hG2` — the spatial first/second-derivative sup profiles
      (`G1profile p M σ` / `G2profile A₂ σ`) on `(0,T]`;
    * `srcWin` — for every read window `[lo,hi] ⊆ (0,T]`, a GLOBAL clamped
      `DuhamelSourceTimeC1` package agreeing with the canonical level-`n` source
      coefficients on `[lo,hi]` (`SourceWin`).

  Per the verdict's traps: NO raw global `TimeC1` and NO `K1` are carried in the
  carrier; the `srcWin` window package is *derived inside the level* from the
  level's own repr + ball + K2 facts via `clampedIterateSource_duhamelSourceTimeC1`
  (stage-1 File D, item 10), and the half-step / G2-step reproduction is the
  `ShiftedSourceWitness` route (stage-1 Files B/C) closed by `g2_step_closes`.

  The carrier's analytic inputs (gate, ball positivity/sup, the per-level shifted
  source witnesses, the kernel-G1 line, the homogeneous-heat G2 base) are taken as
  a single hypothesis bundle `TowerInputs` — the cone-exposable surface returned by
  `coneGradientMildSolutionData_exists_with_gate_data` plus the per-level witness
  packages of the discharge stack.  These are exactly the inputs `uniformWiring_*`
  already consumes; the tower reorganises them into the per-`n` carrier the
  projection (`IntervalPicardTowerProjection`) reads.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalDuhamelSourceShift
import ShenWork.Paper2.IntervalPicardIterateRestartLocal
import ShenWork.Paper2.IntervalPicardIterateC2BoundLocal
import ShenWork.Paper2.IntervalPicardIterateTimeC1Full
import ShenWork.Paper2.IntervalPicardIterateRepresentation
import ShenWork.Paper2.IntervalPicardIterateUniform
import ShenWork.Paper2.IntervalPicardUniformWiringClosure
import ShenWork.Paper2.IntervalPicardUniformWiring
import ShenWork.Paper2.IntervalPicardWdataAssembly

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter HasContinuousSlices)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalMildPicardRegularity
  (logisticSourceFun cosineCoeffs_abs_le_of_continuous_bounded)
open ShenWork.IntervalHomogeneousQuantBound (eigExpWeight)
open ShenWork.IntervalPicardIterateUniform
  (G1profile G2profile Benv GateCondition CL g2_step_closes
   G1profile_nonneg G2profile homWeightBound)
open ShenWork.IntervalPicardIterateRepresentation
  (iterateReprCoeff hbsum_zero hagree_zero)
open ShenWork.IntervalPicardIterateC2BoundLocal (iterate_abs_deriv2_le_of_shiftedWitness)
open ShenWork.IntervalPicardIterateRestartLocal
  (ShiftedSourceWitness canonicalShiftedSource hagree_succ_of_subtypeCont)
open ShenWork.IntervalPicardIterateTimeC1Full (clampedIterateSource_duhamelSourceTimeC1)
open ShenWork.IntervalPicardWdataAssembly
  (G1win G2win G1profile_le_G1win G2profile_le_G2win)
open ShenWork.IntervalPicardUniformWiring
  (lift_deriv2_abs_le_of_eqOn_Ioo lift_deriv2_eq_zero_of_not_mem)
open ShenWork.IntervalPicardUniformWiringDischarge (Benv_nonneg)
open ShenWork.IntervalPicardIterateC2Bound (restartIterateCoeff)

noncomputable section

namespace ShenWork.IntervalPicardSourceTower

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## §1 — The window source carrier `SourceWin`.

`SourceWin p u₀ n lo hi` is the verdict's window-local source package: a GLOBAL
`DuhamelSourceTimeC1` family `a` (so the consumers' global `henv`/`hderiv` legs are
honestly satisfied) that *agrees* with the canonical level-`n` logistic source
coefficients on the read window `[lo,hi]`.  The agreement on `[lo,hi]` is all the
restart/clamp consumers read (`localRestartCoeff_congr_on_Icc`, File A).  The
`cont` value-family continuity is carried explicitly (NOT projected from
`src.hadotcont`, per the verdict's trap 5). -/
structure SourceWin (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (lo hi : ℝ) where
  /-- The global witness source family. -/
  a : ℝ → ℕ → ℝ
  /-- It is an honest time-`C¹` package (global envelope + derivative bounds). -/
  src : DuhamelSourceTimeC1 a
  /-- It agrees with the canonical level-`n` logistic source coefficients on the
  read window `[lo,hi]`. -/
  hagree : ∀ σ ∈ Set.Icc lo hi, ∀ k,
    a σ k = cosineCoeffs (logisticLifted p (picardIter p u₀ n σ)) k
  /-- Value-family `σ`-continuity on the read window (carried explicitly). -/
  hcont : ∀ k, ContinuousOn (fun σ => a σ k) (Set.Icc lo hi)

/-! ## §2 — The tower level carrier `TowerLevel`. -/

/-- **The per-level tower carrier.**  For level `n`, horizon `T`, mass `M`, and
second-derivative budget `A₂`, this packages the four reproducible facts of the
verdict: the horizon-local representation triple, the G1/G2 profiles, and the
per-window source package. -/
structure TowerLevel (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (M A₂ T : ℝ) (n : ℕ) where
  /-- Eigenvalue-weighted summability of the level-`n` representation coefficients. -/
  hrepr_sum : ∀ σ, 0 < σ → σ ≤ T →
    Summable (fun k => (λ_ k) * |iterateReprCoeff p u₀ n σ k|)
  /-- `[0,1]` agreement of the level-`n` slice with its representation series. -/
  hrepr_agree : ∀ σ, 0 < σ → σ ≤ T →
    Set.EqOn (intervalDomainLift (picardIter p u₀ n σ))
      (fun x => ∑' k, iterateReprCoeff p u₀ n σ k * cosineMode k x)
      (Set.Icc (0 : ℝ) 1)
  /-- Kernel G1-line: first-derivative sup bound along `G1profile p M`. -/
  hG1 : ∀ σ, 0 < σ → σ ≤ T → ∀ x : ℝ,
    |deriv (intervalDomainLift (picardIter p u₀ n σ)) x| ≤ G1profile p M σ
  /-- Coefficient G2-line: second-derivative sup bound along `G2profile A₂`. -/
  hG2 : ∀ σ, 0 < σ → σ ≤ T → ∀ x : ℝ,
    |deriv (deriv (intervalDomainLift (picardIter p u₀ n σ))) x| ≤ G2profile A₂ σ
  /-- Per-window source package on every read window `[lo,hi]` strictly inside
  `(0,T)` (`0 < lo ≤ hi < T`).  Strictness in `hi < T` is what the clamped global
  producer needs (it pads to `[c',d']` with `c' < lo ≤ hi < d' ≤ T`). -/
  srcWin : ∀ lo hi, 0 < lo → lo ≤ hi → hi < T → SourceWin p u₀ n lo hi

/-! ## §3 — The carrier's analytic input bundle `TowerInputs`.

These are the cone-exposable / discharge-stack inputs the tower induction consumes,
in exactly the shapes the stage-1 machinery and `uniformWiring_closure` already use.
Bundling them as one hypothesis record keeps `tower_zero`/`tower_succ`/`tower_all`
clean implications. -/

/-- The analytic input bundle the tower induction consumes.  Carries data fields
(`hsrc0`/`witness`/`adot`), so it is `Type`-valued. -/
structure TowerInputs (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (M A₂ T : ℝ) where
  /-- `χ₀ = 0` (the homogeneous-propagator regime). -/
  hχ0 : p.χ₀ = 0
  /-- Structural reaction constants. -/
  hα : 1 ≤ p.α
  ha : 0 ≤ p.a
  hb : 0 ≤ p.b
  /-- Ball radius / horizon basics. -/
  hMnn : 0 ≤ M
  hTpos : 0 < T
  hT1 : T ≤ 1
  hA₂nn : 0 ≤ A₂
  /-- The GATE smallness condition. -/
  hgate : GateCondition p M A₂ T
  /-- The paper-faithful subtype continuity of the datum. -/
  hu₀_cont : Continuous u₀
  /-- Datum coefficient sup. -/
  hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M
  /-- The level-0 source package (needed by `hagree_succ` chains and `srcWin`). -/
  hsrc0 : ∀ n : ℕ, DuhamelSourceTimeC1
    (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
  /-- Value-family continuity of the canonical logistic source slices. -/
  hL_cont : ∀ (n : ℕ) (s : ℝ), 0 < s → Continuous (logisticLifted p (picardIter p u₀ n s))
  /-- Kernel-G1 line, all levels (the `n`-free homogeneous-split bound). -/
  hG1all : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ T → ∀ x : ℝ,
    |deriv (intervalDomainLift (picardIter p u₀ n σ)) x| ≤ G1profile p M σ
  /-- Homogeneous-heat G2 base bound (`n = 0`). -/
  hG2base : ∀ (σ : ℝ), 0 < σ → σ ≤ T → ∀ x : ℝ,
    |deriv (deriv (intervalDomainLift (picardIter p u₀ 0 σ))) x| ≤ G2profile A₂ σ
  /-- The per-level half-step shifted-source witness (stage-1 File B/C), supplying
  the M2-uniform G2-step budget through `iterate_abs_deriv2_le_of_shiftedWitness`. -/
  witness : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ShiftedSourceWitness p u₀ n t M A₂
  /-- Per-iterate slice continuity (cone-returned `HasContinuousSlices`, n-uniform).
  Replaces the former `hM₁` coefficient field: the half-step coefficient bound
  `M₁ ≤ 2M` (verdict trap 7) is now DERIVED in-tower from this slice continuity plus
  the ball sup `hub` via `cosineCoeffs_abs_le_of_continuous_bounded` — see
  `halfStep_coeff_le_twoM`.  This is NOT an analytic-wall leg: it is exactly the
  `HasContinuousSlices` data returned by the gate-data cone. -/
  hcontSlice : ∀ n : ℕ, HasContinuousSlices T (picardIter p u₀ n)
  /-- The two endpoint G2-step budgets (`x ∈ {0,1}`), carried as the honest
  endpoint residual exactly as `hEnd0`/`hEnd1` in the discharge stack: the
  slice↔restart-series agreement only transports the second derivative on the OPEN
  interior `Ioo 0 1`, so the boundary points need the per-endpoint budget facts.
  Each is in the `g2_step_closes`-consumable shape (`M₁' ≤ 2M ∧ |∂ₓₓ| ≤ budget`). -/
  hG2end : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x ∈ ({0, 1} : Set ℝ),
    ∃ M₁' : ℝ, M₁' ≤ 2 * M ∧
      |deriv (deriv (intervalDomainLift (picardIter p u₀ (n + 1) t))) x|
        ≤ M₁' * eigExpWeight (t / 2)
          + ShenWork.IntervalPicardIterateTimeC1.duhamelGainConst
            * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t
  /-- Ball positivity / sup bound, all levels, on `(0,T]`. -/
  hpos : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
    0 < intervalDomainLift (picardIter p u₀ n σ) x
  hub : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
    intervalDomainLift (picardIter p u₀ n σ) x ≤ M
  /-- The level-`n` source-derivative `adot` data on every window (for the clamped
  source producer's K1 leg): derivative-has + window continuity + uniform bound. -/
  adot : ℕ → ℝ → ℕ → ℝ
  hadot_deriv : ∀ (n : ℕ) (c' d' : ℝ), ∀ σ ∈ Set.Icc c' d', ∀ k, HasDerivAt
    (fun r => cosineCoeffs
      (logisticSourceFun p.a p.b p.α (intervalDomainLift (picardIter p u₀ n r))) k)
    (adot n σ k) σ
  hadot_cont : ∀ (n : ℕ) (c' d' : ℝ), ∀ k,
    ContinuousOn (fun σ => adot n σ k) (Set.Icc c' d')
  /-- The per-window uniform `adot` bound constant (data, so it is usable in the
  data-valued `sourceWin_of_level`). -/
  adotBound : ℕ → ℝ → ℝ → ℝ
  hadot_bound : ∀ (n : ℕ) (c' d' : ℝ), ∀ σ ∈ Set.Icc c' d', ∀ k,
    |adot n σ k| ≤ adotBound n c' d'

/-- **In-tower derivation of the half-step coefficient bound `M₁ ≤ 2M`.**
For any level `m` and time `s ∈ (0,T]`, the slice `picardIter p u₀ m s` is
continuous on the subtype (`hcontSlice`), hence its zero-extension lift is
`ContinuousOn (Icc 0 1)`; bounded there by the ball sup `hub … ≤ M`, so each cosine
coefficient is `≤ 2M` by `cosineCoeffs_abs_le_of_continuous_bounded`.  This replaces
the former external `hM₁` field of `TowerInputs`. -/
theorem halfStep_coeff_le_twoM
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (H : TowerInputs p u₀ M A₂ T) (m : ℕ) {s : ℝ} (hs : 0 < s) (hsT : s ≤ T) :
    ∀ k, |cosineCoeffs (intervalDomainLift (picardIter p u₀ m s)) k| ≤ 2 * M := by
  have hcont_s : Continuous (picardIter p u₀ m s) := H.hcontSlice m s hs hsT
  -- The lift restricted to `Icc 0 1` is the subtype slice, hence `ContinuousOn`.
  have hgc : ContinuousOn (intervalDomainLift (picardIter p u₀ m s)) (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : (Set.Icc (0 : ℝ) 1).restrict (intervalDomainLift (picardIter p u₀ m s))
        = picardIter p u₀ m s := by
      funext y
      simp only [Set.restrict_apply, intervalDomainLift]
      rw [dif_pos y.2]
      exact congr_arg (picardIter p u₀ m s) (Subtype.ext rfl)
    rw [heq]; exact hcont_s
  -- Bounded by `M` on `Icc 0 1` from the ball sup.
  have hbd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |intervalDomainLift (picardIter p u₀ m s) x| ≤ M := by
    intro x hx
    have hpos := H.hpos m s hs hsT x hx
    have hub := H.hub m s hs hsT x hx
    rw [abs_of_pos hpos]; exact hub
  exact cosineCoeffs_abs_le_of_continuous_bounded hgc H.hMnn hbd

/-! ## §4 — The window source package builder.

The verdict's `srcWin` construction: from the level-`n` repr triple + ball + K2
facts on a padded window `[c',d'] ⊇ [lo,hi]`, build a GLOBAL clamped
`DuhamelSourceTimeC1` agreeing on `[lo,hi]` with the canonical level-`n` source
coefficients.  This is `clampedIterateSource_duhamelSourceTimeC1` (File D, item 10)
with the carrier facts supplied. -/

/-- **Window source package from the level facts.**  Given the level-`n`
representation triple, ball, and G1/G2 facts on the padded window `[c',d']`
(with `c' < lo ≤ hi < d' ≤ T`, `0 < c'`), and the `adot` data, build the
`SourceWin`.  The window agreement is the producer's `[lo,hi]` agreement; the value
continuity is the canonical source σ-continuity restricted to `[lo,hi]`. -/
def sourceWin_of_level
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (H : TowerInputs p u₀ M A₂ T)
    {lo hi c' d' G1s G2s : ℝ} (hc'pos : 0 < c') (hc' : c' < lo) (hlohi : lo ≤ hi)
    (hd' : hi < d') (hd'T : d' ≤ T)
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ ∈ Set.Icc c' d',
      Summable (fun k => unitIntervalCosineEigenvalue k * |bc σ k|))
    (hagree : ∀ σ ∈ Set.Icc c' d',
      Set.EqOn (intervalDomainLift (picardIter p u₀ n σ))
        (fun x => ∑' k, bc σ k * cosineMode k x) (Set.Icc (0 : ℝ) 1))
    (hG1 : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (picardIter p u₀ n σ)) x| ≤ G1s)
    (hG2 : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (picardIter p u₀ n σ))) x| ≤ G2s) :
    SourceWin p u₀ n lo hi := by
  classical
  -- The producer returns an existential `∃ asrc, ∃ _ : DuhamelSourceTimeC1 asrc, …`;
  -- extract the data via choice (the whole carrier is noncomputable).
  have hex := clampedIterateSource_duhamelSourceTimeC1
    p u₀ n H.hα H.ha H.hb hc' hlohi hd'
    (M := M) (G1 := G1s) (G2 := G2s)
    bc hbsum hagree
    (fun σ hσ x hx => H.hpos n σ (lt_of_lt_of_le hc'pos hσ.1) (le_trans hσ.2 hd'T) x hx)
    (fun σ hσ x hx => H.hub n σ (lt_of_lt_of_le hc'pos hσ.1) (le_trans hσ.2 hd'T) x hx)
    hG1 hG2
    (H.adot n) (H.hadot_deriv n c' d') (H.hadot_cont n c' d') (H.hadot_bound n c' d')
  set asrc := hex.choose with hasrc
  have hspec := hex.choose_spec
  set hsrc := hspec.choose with hhsrc
  have hwin := hspec.choose_spec
  refine ⟨asrc, hsrc, ?_, ?_⟩
  · intro σ hσ k
    exact hwin σ hσ k
  · -- value continuity on `[lo,hi]`: equal to the canonical source coeff there,
    -- which is `σ`-continuous (from the canonical source package `hsrc0`).
    intro k
    have hcanon : Continuous
        (fun σ => cosineCoeffs (logisticLifted p (picardIter p u₀ n σ)) k) :=
      continuous_iff_continuousAt.2 (fun σ => ((H.hsrc0 n).hderiv σ k).continuousAt)
    refine (hcanon.continuousOn).congr ?_
    intro σ hσ
    exact hwin σ hσ k

/-! ## §5 — The `srcWin` field builder (shared by base/step).

For any read window `[lo,hi]` strictly inside `(0,T)`, pick the padded window
`[c',d'] := [lo/2, (hi+T)/2]` (so `0 < c' < lo ≤ hi < d' ≤ T`), supply the level
repr triple on `[c',d']` and the window-uniform scalar G1/G2 bounds
`G1win p M c' d'` / `G2win A₂ c'`, and run `sourceWin_of_level`. -/

/-- **`srcWin` from the level repr + G1/G2 facts (all-σ form).**  Consumes the
canonical-`σ` representation triple and the G1/G2 profile bounds of the level
(`∀ σ, 0 < σ → σ ≤ T → …`), and produces the full `srcWin` field. -/
def srcWin_of_levelData
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (H : TowerInputs p u₀ M A₂ T)
    (bcfun : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ ≤ T →
      Summable (fun k => unitIntervalCosineEigenvalue k * |bcfun σ k|))
    (hagree : ∀ σ, 0 < σ → σ ≤ T →
      Set.EqOn (intervalDomainLift (picardIter p u₀ n σ))
        (fun x => ∑' k, bcfun σ k * cosineMode k x) (Set.Icc (0 : ℝ) 1))
    (hG1 : ∀ σ, 0 < σ → σ ≤ T → ∀ x : ℝ,
      |deriv (intervalDomainLift (picardIter p u₀ n σ)) x| ≤ G1profile p M σ)
    (hG2 : ∀ σ, 0 < σ → σ ≤ T → ∀ x : ℝ,
      |deriv (deriv (intervalDomainLift (picardIter p u₀ n σ))) x| ≤ G2profile A₂ σ) :
    ∀ lo hi, 0 < lo → lo ≤ hi → hi < T → SourceWin p u₀ n lo hi := by
  intro lo hi hlo hlohi hhiT
  set c' := lo / 2 with hc'def
  set d' := (hi + T) / 2 with hd'def
  have hc'pos : 0 < c' := by rw [hc'def]; linarith
  have hc' : c' < lo := by rw [hc'def]; linarith
  have hd' : hi < d' := by rw [hd'def]; linarith
  have hd'T : d' ≤ T := by rw [hd'def]; linarith
  -- on `[c',d']`: `0 < c' ≤ σ` and `σ ≤ d' ≤ T`.
  have hσpos : ∀ σ ∈ Set.Icc c' d', 0 < σ := fun σ hσ => lt_of_lt_of_le hc'pos hσ.1
  have hσT : ∀ σ ∈ Set.Icc c' d', σ ≤ T := fun σ hσ => le_trans hσ.2 hd'T
  refine sourceWin_of_level p u₀ n H hc'pos hc' hlohi hd' hd'T bcfun
    (fun σ hσ => hbsum σ (hσpos σ hσ) (hσT σ hσ))
    (fun σ hσ => hagree σ (hσpos σ hσ) (hσT σ hσ))
    (G1s := G1win p M c' d') (G2s := G2win A₂ c') ?_ ?_
  · intro σ hσ x _hx
    exact le_trans (hG1 σ (hσpos σ hσ) (hσT σ hσ) x)
      (G1profile_le_G1win H.hMnn hc'pos hσ.1 hσ.2)
  · intro σ hσ x _hx
    exact le_trans (hG2 σ (hσpos σ hσ) (hσT σ hσ) x)
      (G2profile_le_G2win H.hA₂nn hc'pos hσ.1)

/-! ## §6 — The tower induction. -/

/-- **Base case `tower_zero`.**  The level-0 carrier holds: representation from
`hbsum_zero`/`hagree_zero` (homogeneous heat slice); G1 from the `n`-free kernel
line (`H.hG1all 0`); G2 from the homogeneous-heat base (`H.hG2base`); `srcWin` from
the level-0 repr triple via `srcWin_of_levelData`. -/
def tower_zero
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {M A₂ T : ℝ}
    (H : TowerInputs p u₀ M A₂ T) :
    TowerLevel p u₀ M A₂ T 0 where
  hrepr_sum := fun _ hσ _ => hbsum_zero p u₀ hσ H.hu₀_bound
  hrepr_agree := fun _ hσ _ => hagree_zero p u₀ hσ H.hu₀_cont H.hu₀_bound
  hG1 := H.hG1all 0
  hG2 := H.hG2base
  srcWin := srcWin_of_levelData p u₀ 0 H (iterateReprCoeff p u₀ 0)
    (fun _ hσ _ => hbsum_zero p u₀ hσ H.hu₀_bound)
    (fun _ hσ _ => hagree_zero p u₀ hσ H.hu₀_cont H.hu₀_bound)
    (H.hG1all 0) H.hG2base

/-- **Inductive step `tower_succ` (under the GATE).**  `TowerLevel … n →
TowerLevel … (n+1)`:

  * representation: `hbsum_succ_of_shiftedWitness` + `hagree_succ_of_subtypeCont`
    (the witness / subtype variants, stage-1 File B);
  * G1: the `n`-free kernel line (`H.hG1all (n+1)`);
  * G2: `iterate_abs_deriv2_le_of_shiftedWitness` (stage-1 File C) gives the
    half-step budget on the canonical restart series, bridged to
    `lift(uₙ₊₁(σ))` via the level-(n+1) agreement, then closed into `A₂/σ²` by
    `g2_step_closes` (with `M₁ ≤ 2M`);
  * `srcWin`: from the level-(n+1) repr triple via `srcWin_of_levelData`. -/
def tower_succ
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {M A₂ T : ℝ}
    (H : TowerInputs p u₀ M A₂ T) {n : ℕ}
    (_L : TowerLevel p u₀ M A₂ T n) :
    TowerLevel p u₀ M A₂ T (n + 1) := by
  -- The half-step coefficient bound `M₁ ≤ 2M` is now DERIVED in-tower (no longer an
  -- external `TowerInputs` field) from the cone-returned slice continuity + ball sup.
  have hM₁ : ∀ σ, 0 < σ → σ ≤ T → ∀ k,
      |cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (σ / 2))) k| ≤ 2 * M := by
    intro σ hσ hσT k
    exact halfStep_coeff_le_twoM p u₀ H (n + 1) (by positivity)
      (by linarith) k
  -- representation summability via the shifted-source witness.
  have hrepr_sum : ∀ σ, 0 < σ → σ ≤ T →
      Summable (fun k => (λ_ k) * |iterateReprCoeff p u₀ (n + 1) σ k|) := by
    intro σ hσ hσT
    exact ShenWork.IntervalPicardIterateRestartLocal.hbsum_succ_of_shiftedWitness
      p u₀ n hσ (fun k => hM₁ σ hσ hσT k) (H.witness n σ hσ hσT)
  -- representation agreement via the subtype-continuity variant.
  have hrepr_agree : ∀ σ, 0 < σ → σ ≤ T →
      Set.EqOn (intervalDomainLift (picardIter p u₀ (n + 1) σ))
        (fun x => ∑' k, iterateReprCoeff p u₀ (n + 1) σ k * cosineMode k x)
        (Set.Icc (0 : ℝ) 1) := by
    intro σ hσ hσT
    exact hagree_succ_of_subtypeCont p H.hχ0 u₀ n hσ H.hu₀_cont H.hu₀_bound
      (H.hsrc0 n) (fun s hs _ => H.hL_cont n s hs)
  -- G2 line: witness deriv² bound on the restart series, transported to the slice
  -- (interior via the Ioo agreement, endpoints via the carried budget, exterior
  -- trivially zero), then closed into `A₂/σ²` by `g2_step_closes`.
  have hG2 : ∀ σ, 0 < σ → σ ≤ T → ∀ x : ℝ,
      |deriv (deriv (intervalDomainLift (picardIter p u₀ (n + 1) σ))) x|
        ≤ G2profile A₂ σ := by
    intro σ hσ hσT x
    have hBenv : 0 ≤ Benv p M A₂ σ := Benv_nonneg H.hMnn
    -- the budget shape `M₁' ≤ 2M ∧ |∂ₓₓ slice| ≤ M₁'·eig + Cgain·(σ/2)^{1/4}·Benv`,
    -- at every real `x`, three-way split.
    have hbudget : ∃ M₁' : ℝ, M₁' ≤ 2 * M ∧
        |deriv (deriv (intervalDomainLift (picardIter p u₀ (n + 1) σ))) x|
          ≤ M₁' * eigExpWeight (σ / 2)
            + ShenWork.IntervalPicardIterateTimeC1.duhamelGainConst
              * (σ / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ σ := by
      by_cases hxIcc : x ∈ Set.Icc (0 : ℝ) 1
      · rcases eq_or_lt_of_le hxIcc.1 with hx0 | hx0
        · -- left endpoint x = 0
          obtain ⟨M₁', h1, h2⟩ := H.hG2end n σ hσ hσT 0 (by simp)
          exact ⟨M₁', h1, by rw [← hx0]; exact h2⟩
        rcases eq_or_lt_of_le hxIcc.2 with hx1 | hx1
        · -- right endpoint x = 1
          obtain ⟨M₁', h1, h2⟩ := H.hG2end n σ hσ hσT 1 (by simp)
          exact ⟨M₁', h1, by rw [hx1]; exact h2⟩
        · -- interior x ∈ Ioo 0 1: witness deriv² on the restart series + Ioo transport
          refine ⟨2 * M, le_refl _, ?_⟩
          have hbound := iterate_abs_deriv2_le_of_shiftedWitness p u₀ n hσ hBenv
            (fun k => hM₁ σ hσ hσT k) (H.witness n σ hσ hσT) x
          -- the witness gives the bound with the half-step coefficient `M₁`; here we
          -- absorb `M₁ ≤ 2M`'s slack into the leading `2M·eig` term.
          have hM₁le : ∀ k, |cosineCoeffs
              (intervalDomainLift (picardIter p u₀ (n + 1) (σ / 2))) k| ≤ 2 * M :=
            fun k => hM₁ σ hσ hσT k
          -- restart-series ↔ slice agreement on the open interior.
          have hEq : Set.EqOn (intervalDomainLift (picardIter p u₀ (n + 1) σ))
              (fun z => ∑' k, restartIterateCoeff p u₀ n σ k * cosineMode k z)
              (Set.Ioo (0 : ℝ) 1) := by
            intro z hz
            have := hrepr_agree σ hσ hσT (Set.Ioo_subset_Icc_self hz)
            simpa only [iterateReprCoeff] using this
          -- the witness's explicit Cgain constant is `duhamelGainConst` (definitional).
          have hser : |deriv (deriv
                (fun z => ∑' k, restartIterateCoeff p u₀ n σ k * cosineMode k z)) x|
              ≤ 2 * M * eigExpWeight (σ / 2)
                + ShenWork.IntervalPicardIterateTimeC1.duhamelGainConst
                  * (σ / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ σ := by
            have hgain_eq : ShenWork.IntervalPicardIterateTimeC1.duhamelGainConst
                = 2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2))
                    / Real.pi ^ ((3 : ℝ) / 2) := rfl
            rw [hgain_eq]
            -- the witness bound has leading `M₁·eig`; bound `M₁·eig ≤ 2M·eig` needs
            -- `M₁ ≤ 2M`, but the witness uses the SUP `M₁`-form already with `2M`.
            -- `iterate_abs_deriv2_le_of_shiftedWitness` is stated with `M₁` as the
            -- explicit hypothesis bound, which here is `2M`.
            exact hbound
          exact lift_deriv2_abs_le_of_eqOn_Ioo hEq ⟨hx0, hx1⟩ hser
      · -- exterior x ∉ Icc 0 1: slice deriv² = 0
        refine ⟨0, by linarith [H.hMnn], ?_⟩
        rw [lift_deriv2_eq_zero_of_not_mem _ hxIcc, abs_zero]
        have hτ : 0 < σ / 2 := by positivity
        have : 0 ≤ ShenWork.IntervalPicardIterateTimeC1.duhamelGainConst
            * (σ / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ σ :=
          mul_nonneg (mul_nonneg
            ShenWork.IntervalPicardIterateTimeC1.duhamelGainConst_nonneg
            (Real.rpow_nonneg hτ.le _)) hBenv
        simpa using this
    obtain ⟨M₁', hM₁'le, hM₁'bound⟩ := hbudget
    exact g2_step_closes H.hMnn hσ hσT hM₁'le H.hgate hM₁'bound
  refine
    { hrepr_sum := hrepr_sum
      hrepr_agree := hrepr_agree
      hG1 := H.hG1all (n + 1)
      hG2 := hG2
      srcWin := srcWin_of_levelData p u₀ (n + 1) H (iterateReprCoeff p u₀ (n + 1))
        hrepr_sum hrepr_agree (H.hG1all (n + 1)) hG2 }

/-- **The full tower induction (under the GATE).**  For every `n`, the carrier
holds. -/
def tower_all
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {M A₂ T : ℝ}
    (H : TowerInputs p u₀ M A₂ T) :
    ∀ n : ℕ, TowerLevel p u₀ M A₂ T n
  | 0 => tower_zero p u₀ H
  | n + 1 => tower_succ p u₀ H (tower_all p u₀ H n)

end ShenWork.IntervalPicardSourceTower
