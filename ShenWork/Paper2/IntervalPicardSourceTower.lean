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
import ShenWork.Paper2.IntervalPicardSliceWitnessSupply
import ShenWork.Paper2.IntervalPicardIterateTimeC1Full
import ShenWork.Paper2.IntervalPicardIterateRepresentation
import ShenWork.Paper2.IntervalPicardWindowAdot
import ShenWork.Paper2.IntervalHomogeneousG2Base
import ShenWork.Paper2.IntervalPicardIterateUniform
import ShenWork.Paper2.IntervalPicardUniformWiringClosure
import ShenWork.Paper2.IntervalPicardUniformWiring
import ShenWork.Paper2.IntervalPicardWdataAssembly
import ShenWork.Paper2.IntervalPicardSourceSubtypeCont
import ShenWork.Paper2.IntervalPicardWindowAdotOn
import ShenWork.Paper2.IntervalPicardSuccLegsOn
import ShenWork.Paper2.IntervalPicardShiftedBddSupply
import ShenWork.Paper2.IntervalPicardIterateBddPackage
import ShenWork.Paper2.IntervalPicardSourceTimeC1OnRecursion
import ShenWork.Paper2.IntervalPicardIterateTimeC1JointEndpoint

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
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
open ShenWork.IntervalPicardSliceWitnessSupply
  (iterate_abs_deriv2_le_of_windowDecay shiftedSource_timeC1 shifted_source_windowDecay)
open ShenWork.IntervalPicardIterateRepresentation (hbsum_succ)
open ShenWork.IntervalPicardIterateRestartLocal
  (ShiftedSourceWitness canonicalShiftedSource hagree_succ_of_subtypeCont)
open ShenWork.IntervalPicardSourceSubtypeCont
  (logisticSource_subtypeCont hagree_succ_of_sourceSubtypeCont)
open ShenWork.IntervalPicardShiftedBddSupply (hagree_succ_of_sourceBdd)
open ShenWork.IntervalPicardIterateTimeC1Full (clampedIterateSource_duhamelSourceTimeC1)
open ShenWork.IntervalPicardWindowAdot
  (WindowAdotLegs windowAdotLegs_zero windowAdotLegs_step_on)
open ShenWork.IntervalPicardSuccLegsOn
  (hbsum_succ_on iterate_abs_deriv2_le_of_windowDecay_on)
open ShenWork.IntervalPicardWdataAssembly
  (G1win G2win G1profile_le_G1win G2profile_le_G2win)
open ShenWork.IntervalPicardUniformWiring
  (lift_deriv2_abs_le_of_eqOn_Ioo lift_deriv2_eq_zero_of_not_mem)
open ShenWork.IntervalPicardUniformWiringDischarge (Benv_nonneg)
open ShenWork.IntervalPicardIterateC2Bound (restartIterateCoeff)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalPicardLimitRestartBdd (DuhamelSourceBddOn)
open ShenWork.IntervalPicardLimitBddProducer (patchedSource)
open ShenWork.IntervalPicardLimitBddHcontP
  (patchedSlice patchedSlice_of_nonpos patchedSlice_of_pos)
open ShenWork.IntervalPicardIterateBddPackage (iterateBddOn_endpoint_of_facts)
open ShenWork.IntervalPicardSourceTimeC1OnRecursion
  (LevelSourceTimeC1OnUpTo sourceTimeC1On_succ_of_sourceTimeC1On)
open ShenWork.IntervalPicardLevel0SourceTimeC1On
  (heatCoeff level0Source_timeC1On)
open ShenWork.IntervalPicardIterateBddRepr (picardIterateRestart_general_of_sourceBdd)
open ShenWork.IntervalPicardIterateTimeC1JointEndpoint
  (restartProfile_jointContinuousOn_On_shift)

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
  /-- The window `adot` legs (time-`C¹` of the level's source coefficients) on every
  read window strictly inside `(0,T)` — PRODUCED level-by-level (K1 wall closure):
  base via `windowAdotLegs_zero`, step via `windowAdotLegs_step`. -/
  winAdot : ∀ lo hi, 0 < lo → lo ≤ hi → hi < T → WindowAdotLegs p u₀ n lo hi
  /-- Endpoint-inclusive positive-window source package, produced in tower. -/
  srcOn : LevelSourceTimeC1OnUpTo p u₀ n T
  /-- Endpoint-inclusive patched bounded-source package on the full horizon. -/
  srcBdd : DuhamelSourceBddOn (patchedSource p u₀ (picardIter p u₀ n)) T

/-! ## §3 — The carrier's analytic input bundle `TowerInputs`.

These are the cone-exposable / discharge-stack inputs the tower induction consumes,
in exactly the shapes the stage-1 machinery and `uniformWiring_closure` already use.
Bundling them as one hypothesis record keeps `tower_zero`/`tower_succ`/`tower_all`
clean implications. -/

/-- The analytic input bundle the tower induction consumes.  Carries data fields and
proof-producing windows, so it is `Type`-valued. -/
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
  /-- Datum nonnegativity on the closed interval. -/
  hu₀_nonneg : ∀ y : intervalDomainPoint, 0 ≤ u₀ y
  /-- Datum pointwise bound at the tower mass. -/
  hu₀_abs_bound : ∀ y : intervalDomainPoint, |u₀ y| ≤ M
  /-- Kernel-G1 line, all levels (the `n`-free homogeneous-split bound). -/
  hG1all : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ T → ∀ x : ℝ,
    |deriv (intervalDomainLift (picardIter p u₀ n σ)) x| ≤ G1profile p M σ
  /-- Per-iterate slice continuity (cone-returned `HasContinuousSlices`, n-uniform).
  Replaces the former `hM₁` coefficient field: the half-step coefficient bound
  `M₁ ≤ 2M` (verdict trap 7) is now DERIVED in-tower from this slice continuity plus
  the ball sup `hub` via `cosineCoeffs_abs_le_of_continuous_bounded` — see
  `halfStep_coeff_le_twoM`.  This is NOT an analytic-wall leg: it is exactly the
  `HasContinuousSlices` data returned by the gate-data cone. -/
  hcontSlice : ∀ n : ℕ, HasContinuousSlices T (picardIter p u₀ n)
  /-- The two endpoint G2-step budgets (`x ∈ {0,1}`), carried in the tower input:
  slice↔restart-series agreement only transports the second derivative on the
  OPEN interior `Ioo 0 1`, so the boundary points need the per-endpoint budget facts.
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

/-- **Subtype slice continuity ⟹ lift `ContinuousOn (Icc 0 1)`** (the `hgc`
pattern of `halfStep_coeff_le_twoM`, extracted for the `winAdot` builders). -/
theorem lift_slice_continuousOn
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (H : TowerInputs p u₀ M A₂ T) (m : ℕ) :
    ∀ σ, 0 < σ → σ ≤ T →
      ContinuousOn (intervalDomainLift (picardIter p u₀ m σ)) (Set.Icc (0 : ℝ) 1) := by
  intro s hs hsT
  have hcont_s : Continuous (picardIter p u₀ m s) := H.hcontSlice m s hs hsT
  rw [continuousOn_iff_continuous_restrict]
  have heq : (Set.Icc (0 : ℝ) 1).restrict (intervalDomainLift (picardIter p u₀ m s))
      = picardIter p u₀ m s := by
    funext y
    simp only [Set.restrict_apply, intervalDomainLift]
    rw [dif_pos y.2]
    exact congr_arg (picardIter p u₀ m s) (Subtype.ext rfl)
  rw [heq]; exact hcont_s

/-- The tower mass is positive once the positive-time ball is nonempty. -/
theorem towerInputs_Mpos
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (H : TowerInputs p u₀ M A₂ T) : 0 < M := by
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hp := H.hpos 0 T H.hTpos le_rfl 0 h0mem
  have hu := H.hub 0 T H.hTpos le_rfl 0 h0mem
  exact lt_of_lt_of_le hp hu

/-- Patched iterate slices are bounded by the tower mass on `[0,T]`. -/
theorem patchedIterateSlice_abs_bound_of_tower
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (H : TowerInputs p u₀ M A₂ T) (n : ℕ) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y : intervalDomainPoint,
      |patchedSlice u₀ (picardIter p u₀ n) s y| ≤ M := by
  intro s hs y
  rcases eq_or_lt_of_le hs.1 with hs0 | hspos
  · rw [← hs0, patchedSlice_of_nonpos u₀ (picardIter p u₀ n) (le_refl 0)]
    exact H.hu₀_abs_bound y
  · rw [patchedSlice_of_pos u₀ (picardIter p u₀ n) hspos]
    have hp := H.hpos n s hspos hs.2 y.1 y.2
    have hu := H.hub n s hspos hs.2 y.1 y.2
    have hp' : 0 < picardIter p u₀ n s y := by
      simpa [intervalDomainLift, y.2] using hp
    have hu' : picardIter p u₀ n s y ≤ M := by
      simpa [intervalDomainLift, y.2] using hu
    rw [abs_of_pos hp']
    exact hu'

/-- Patched iterate slices are nonnegative on `[0,T]`. -/
theorem patchedIterateSlice_nonneg_of_tower
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (H : TowerInputs p u₀ M A₂ T) (n : ℕ) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y : intervalDomainPoint,
      0 ≤ patchedSlice u₀ (picardIter p u₀ n) s y := by
  intro s hs y
  rcases eq_or_lt_of_le hs.1 with hs0 | hspos
  · rw [← hs0, patchedSlice_of_nonpos u₀ (picardIter p u₀ n) (le_refl 0)]
    exact H.hu₀_nonneg y
  · rw [patchedSlice_of_pos u₀ (picardIter p u₀ n) hspos]
    have hp := H.hpos n s hspos hs.2 y.1 y.2
    have hp' : 0 < picardIter p u₀ n s y := by
      simpa [intervalDomainLift, y.2] using hp
    exact hp'.le

/-- Level-0 endpoint-inclusive source package on all positive windows. -/
noncomputable def level0SourceOnUpTo_of_tower
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {M A₂ T : ℝ}
    (H : TowerInputs p u₀ M A₂ T) :
    LevelSourceTimeC1OnUpTo p u₀ 0 T := by
  intro c hc hcT
  refine level0Source_timeC1On p (M := M) (G1 := G1win p M c T)
    (G2 := G2win A₂ c) (Udot := A₂ / c ^ 2) (M₀ := M)
    hc hcT H.hα H.ha H.hb
    H.hu₀_cont H.hu₀_bound ?_ ?_ ?_ ?_ ?_
  · intro σ hσ x hx
    exact H.hpos 0 σ (lt_of_lt_of_le hc hσ.1) hσ.2 x hx
  · intro σ hσ x hx
    exact H.hub 0 σ (lt_of_lt_of_le hc hσ.1) hσ.2 x hx
  · intro σ hσ x _hx
    exact le_trans (H.hG1all 0 σ (lt_of_lt_of_le hc hσ.1) hσ.2 x)
      (G1profile_le_G1win H.hMnn hc hσ.1 hσ.2)
  · intro σ hσ x _hx
    exact le_trans
      (ShenWork.IntervalHomogeneousG2Base.hG2base_of_gate p u₀
        H.hMnn H.hA₂nn H.hu₀_cont H.hu₀_bound H.hgate
        σ (lt_of_lt_of_le hc hσ.1) hσ.2 x)
      (G2profile_le_G2win H.hA₂nn hc hσ.1)
  · intro σ hσ x _hx
    have hσpos : 0 < σ := lt_of_lt_of_le hc hσ.1
    calc |ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondValue
            σ (heatCoeff u₀) x|
        ≤ M * eigExpWeight σ :=
          ShenWork.IntervalHomogeneousG2Base.secondValue_abs_le hσpos H.hu₀_bound x
      _ ≤ homWeightBound M σ :=
          ShenWork.IntervalHomogeneousG2Base.eigExpWeight_le_homWeightBound
            H.hMnn hσpos
      _ ≤ A₂ / σ ^ 2 :=
          ShenWork.IntervalHomogeneousG2Base.homWeightBound_le_of_gate
            H.hMnn hσpos hσ.2 H.hgate
      _ ≤ A₂ / c ^ 2 := by
          have hc2 : 0 < c ^ 2 := by positivity
          have hσ2 : 0 < σ ^ 2 := by positivity
          have hcσ2 : c ^ 2 ≤ σ ^ 2 := by nlinarith [hσ.1]
          field_simp [hc2.ne', hσ2.ne']
          nlinarith [H.hA₂nn, hcσ2]

/-- Endpoint `DuhamelSourceBddOn` package assembled from tower facts. -/
noncomputable def sourceBdd_of_levelData
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    {M A₂ T : ℝ} (H : TowerInputs p u₀ M A₂ T)
    (srcOn : LevelSourceTimeC1OnUpTo p u₀ n T)
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
    DuhamelSourceBddOn (patchedSource p u₀ (picardIter p u₀ n)) T :=
  iterateBddOn_endpoint_of_facts p H.hχ0 n H.hα H.ha H.hb H.hu₀_cont
    H.hTpos (towerInputs_Mpos p u₀ H) H.hMnn H.hA₂nn
    (fun m s hs hsT y => by
      have hp := H.hpos m s hs hsT y.1 y.2
      have hu := H.hub m s hs hsT y.1 y.2
      have hp' : 0 < picardIter p u₀ m s y := by
        simpa [intervalDomainLift, y.2] using hp
      have hu' : picardIter p u₀ m s y ≤ M := by
        simpa [intervalDomainLift, y.2] using hu
      rw [abs_of_pos hp']; exact hu')
    (patchedIterateSlice_abs_bound_of_tower p u₀ H n)
    (patchedIterateSlice_nonneg_of_tower p u₀ H n)
    (lift_slice_continuousOn p u₀ H n)
    srcOn bcfun hbsum hagree (H.hpos n) (H.hub n) hG1 hG2 H.hTpos le_rfl

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
      |deriv (deriv (intervalDomainLift (picardIter p u₀ n σ))) x| ≤ G2s)
    (hlegs : WindowAdotLegs p u₀ n c' d') :
    SourceWin p u₀ n lo hi := by
  classical
  -- extract the legs via choice (the goal `SourceWin` is data-valued).
  have hspec := hlegs.choose_spec
  have hderiv := hspec.1
  have hadotcont := hspec.2.2
  have hMdot := hspec.2.1.choose_spec
  -- The producer returns an existential `∃ asrc, ∃ _ : DuhamelSourceTimeC1 asrc, …`;
  -- extract the data via choice (the whole carrier is noncomputable).
  have hex := clampedIterateSource_duhamelSourceTimeC1
    p u₀ n H.hα H.ha H.hb hc' hlohi hd'
    (M := M) (G1 := G1s) (G2 := G2s)
    bc hbsum hagree
    (fun σ hσ x hx => H.hpos n σ (lt_of_lt_of_le hc'pos hσ.1) (le_trans hσ.2 hd'T) x hx)
    (fun σ hσ x hx => H.hub n σ (lt_of_lt_of_le hc'pos hσ.1) (le_trans hσ.2 hd'T) x hx)
    hG1 hG2
    hlegs.choose hderiv hadotcont hMdot
  set asrc := hex.choose with hasrc
  have hspec := hex.choose_spec
  set hsrc := hspec.choose with hhsrc
  have hwin := hspec.choose_spec
  refine ⟨asrc, hsrc, ?_, ?_⟩
  · intro σ hσ k
    exact hwin σ hσ k
  · -- value continuity on `[lo,hi]`: equal to the canonical source coeff there,
    -- which is `σ`-continuous on `[lo,hi] ⊆ [c',d']` from the `winAdot` legs
    -- (`HasDerivAt ⟹ ContinuousAt`), without a global canonical source package.
    intro k
    -- the `[lo,hi] ⊆ [c',d']` inclusion (`c' < lo ≤ hi < d'`).
    have hsubLoHi : Set.Icc lo hi ⊆ Set.Icc c' d' :=
      Set.Icc_subset_Icc (le_of_lt hc') (le_of_lt hd')
    -- the source-function-form coefficient is `σ`-continuous on `[c',d']` via the legs.
    have hderivCD := hderiv
    have hcontSF : ContinuousOn
        (fun σ => cosineCoeffs
          (logisticSourceFun p.a p.b p.α (intervalDomainLift (picardIter p u₀ n σ))) k)
        (Set.Icc lo hi) := by
      intro σ hσ
      exact ((hderivCD σ (hsubLoHi hσ) k).continuousAt).continuousWithinAt
    -- bridge `logisticSourceFun ∘ lift` → `logisticLifted` (pointwise on ℝ).
    have hbridge : (fun σ => cosineCoeffs
          (logisticSourceFun p.a p.b p.α (intervalDomainLift (picardIter p u₀ n σ))) k)
        = (fun σ => cosineCoeffs (logisticLifted p (picardIter p u₀ n σ)) k) := by
      funext σ
      refine ShenWork.Paper2.cosineCoeffs_congr_on_Icc (fun x hx => ?_) k
      exact (ShenWork.IntervalMildPicardRegularity.logisticLifted_eq_logisticSourceFun_on_Icc
        p (picardIter p u₀ n σ) hx).symm
    rw [hbridge] at hcontSF
    refine hcontSF.congr ?_
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
      |deriv (deriv (intervalDomainLift (picardIter p u₀ n σ))) x| ≤ G2profile A₂ σ)
    (hwin : ∀ lo hi, 0 < lo → lo ≤ hi → hi < T → WindowAdotLegs p u₀ n lo hi) :
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
  have hc'd' : c' ≤ d' := by rw [hc'def, hd'def]; linarith
  have hd'Tlt : d' < T := by rw [hd'def]; linarith
  refine sourceWin_of_level p u₀ n H hc'pos hc' hlohi hd' hd'T bcfun
    (fun σ hσ => hbsum σ (hσpos σ hσ) (hσT σ hσ))
    (fun σ hσ => hagree σ (hσpos σ hσ) (hσT σ hσ))
    (G1s := G1win p M c' d') (G2s := G2win A₂ c') ?_ ?_
    (hwin c' d' hc'pos hc'd' hd'Tlt)
  · intro σ hσ x _hx
    exact le_trans (hG1 σ (hσpos σ hσ) (hσT σ hσ) x)
      (G1profile_le_G1win H.hMnn hc'pos hσ.1 hσ.2)
  · intro σ hσ x _hx
    exact le_trans (hG2 σ (hσpos σ hσ) (hσT σ hσ) x)
      (G2profile_le_G2win H.hA₂nn hc'pos hσ.1)

/-! ## §6 — The tower induction. -/

/-- **Base case `tower_zero`.**  The level-0 carrier holds: representation from
`hbsum_zero`/`hagree_zero` (homogeneous heat slice); G1 from the `n`-free kernel
line (`H.hG1all 0`); G2 DERIVED from the gate (`hG2base_of_gate`); `srcWin` from
the level-0 repr triple via `srcWin_of_levelData`. -/
def tower_zero
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {M A₂ T : ℝ}
    (H : TowerInputs p u₀ M A₂ T) :
    TowerLevel p u₀ M A₂ T 0 :=
  let wA : ∀ lo hi, 0 < lo → lo ≤ hi → hi < T → WindowAdotLegs p u₀ 0 lo hi :=
    windowAdotLegs_zero p u₀ H.hα H.ha H.hb H.hMnn H.hu₀_cont H.hu₀_bound
      (H.hpos 0) (H.hub 0) (lift_slice_continuousOn p u₀ H 0)
  let src0 : LevelSourceTimeC1OnUpTo p u₀ 0 T :=
    level0SourceOnUpTo_of_tower p u₀ H
  let bdd0 : DuhamelSourceBddOn (patchedSource p u₀ (picardIter p u₀ 0)) T :=
    sourceBdd_of_levelData p u₀ 0 H src0 (iterateReprCoeff p u₀ 0)
      (fun _ hσ _ => hbsum_zero p u₀ hσ H.hu₀_bound)
      (fun _ hσ _ => hagree_zero p u₀ hσ H.hu₀_cont H.hu₀_bound)
      (H.hG1all 0)
      (ShenWork.IntervalHomogeneousG2Base.hG2base_of_gate p u₀
        H.hMnn H.hA₂nn H.hu₀_cont H.hu₀_bound H.hgate)
  { hrepr_sum := fun _ hσ _ => hbsum_zero p u₀ hσ H.hu₀_bound
    hrepr_agree := fun _ hσ _ => hagree_zero p u₀ hσ H.hu₀_cont H.hu₀_bound
    hG1 := H.hG1all 0
    hG2 := ShenWork.IntervalHomogeneousG2Base.hG2base_of_gate p u₀
      H.hMnn H.hA₂nn H.hu₀_cont H.hu₀_bound H.hgate
    srcWin := srcWin_of_levelData p u₀ 0 H (iterateReprCoeff p u₀ 0)
      (fun _ hσ _ => hbsum_zero p u₀ hσ H.hu₀_bound)
      (fun _ hσ _ => hagree_zero p u₀ hσ H.hu₀_cont H.hu₀_bound)
      (H.hG1all 0)
      (ShenWork.IntervalHomogeneousG2Base.hG2base_of_gate p u₀
        H.hMnn H.hA₂nn H.hu₀_cont H.hu₀_bound H.hgate)
      wA
    winAdot := wA
    srcOn := src0
    srcBdd := bdd0 }

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
    (L : TowerLevel p u₀ M A₂ T n) :
    TowerLevel p u₀ M A₂ T (n + 1) := by
  -- The half-step coefficient bound `M₁ ≤ 2M` is now DERIVED in-tower (no longer an
  -- external `TowerInputs` field) from the cone-returned slice continuity + ball sup.
  have hM₁ : ∀ σ, 0 < σ → σ ≤ T → ∀ k,
      |cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (σ / 2))) k| ≤ 2 * M := by
    intro σ hσ hσT k
    exact halfStep_coeff_le_twoM p u₀ H (n + 1) (by positivity)
      (by linarith) k
  -- The σ-shifted canonical source time-`C¹` package on `[0, σ/2]`, produced from
  -- the level-`n` ledger on a strict larger horizon.
  have hsrcσ : ∀ σ, 0 < σ → σ ≤ T → DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (σ / 2 + s))) k)
      0 (σ / 2) :=
    fun σ hσ hσT => by
      have hhalf : 0 < σ / 2 := by positivity
      have hhalfσ : σ / 2 < σ := by linarith
      have hhalfT : σ / 2 < T := lt_of_lt_of_le hhalfσ hσT
      have hphysT := L.srcOn (σ / 2) hhalf hhalfT
      have hphys : DuhamelSourceTimeC1On
          (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
          (σ / 2) σ :=
        hphysT.restrict_hi hσT
      have hsum : σ / 2 + σ / 2 = σ := by ring
      have hphys' : DuhamelSourceTimeC1On
          (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
          (σ / 2) (σ / 2 + σ / 2) := by
        rw [hsum]
        exact hphys
      simpa [add_comm] using
        ShenWork.IntervalDuhamelSourceTimeC1On.DuhamelSourceTimeC1On.shift_zero
          (offset := σ / 2) (W := σ / 2) hphys'
  -- The WALL-FREE windowed decay of the shifted source on `[0, σ/2]`, DERIVED in-tower
  -- from the level-`n` representation triple + ball + K2 facts (`L.hrepr_*`/`L.hG1`/
  -- `L.hG2`, ball from `H.hpos`/`H.hub`) via stage F (`shifted_source_windowDecay`).
  -- This replaces the former external `H.witness.hdecay` field.
  have hdecayW : ∀ σ, 0 < σ → σ ≤ T →
      ∀ s ∈ Set.Icc (0 : ℝ) (σ / 2), ∀ k : ℕ, 1 ≤ k →
        |cosineCoeffs (logisticLifted p (picardIter p u₀ n (σ / 2 + s))) k|
          ≤ 2 * Benv p M A₂ σ / ((k : ℝ) * Real.pi) ^ 2 :=
    fun σ hσ hσT => shifted_source_windowDecay p u₀ n H.hα H.hMnn H.hA₂nn hσ hσT
      (iterateReprCoeff p u₀ n)
      (fun s hs hsT => L.hrepr_sum s hs hsT)
      (fun s hs hsT => L.hrepr_agree s hs hsT)
      (fun s hs hsT => H.hpos n s hs hsT)
      (fun s hs hsT => H.hub n s hs hsT)
      (fun s hs hsT => L.hG1 s hs hsT)
      (fun s hs hsT => L.hG2 s hs hsT)
  -- representation summability via the shifted-source `TimeC1On` package.
  have hrepr_sum : ∀ σ, 0 < σ → σ ≤ T →
      Summable (fun k => (λ_ k) * |iterateReprCoeff p u₀ (n + 1) σ k|) := by
    intro σ hσ hσT
    exact hbsum_succ_on p u₀ n hσ (fun k => hM₁ σ hσ hσT k)
      (hsrcσ σ hσ hσT)
  -- representation agreement via the subtype-continuity variant.
  have hrepr_agree : ∀ σ, 0 < σ → σ ≤ T →
      Set.EqOn (intervalDomainLift (picardIter p u₀ (n + 1) σ))
        (fun x => ∑' k, iterateReprCoeff p u₀ (n + 1) σ k * cosineMode k x)
        (Set.Icc (0 : ℝ) 1) := by
    intro σ hσ hσT
    -- The SATISFIABLE source-slice subtype continuity (replacing the false `hL_cont`
    -- lift-continuity): from the cone-returned per-iterate slice continuity
    -- `H.hcontSlice n` + `1 ≤ p.α` via `logisticSource_subtypeCont`, on `s ≤ σ ≤ T`.
    have hLs : ∀ s, 0 < s → s ≤ σ →
        Continuous (intervalLogisticSource p (picardIter p u₀ n s)) := fun s hs hsσ =>
      logisticSource_subtypeCont p u₀ n H.hα (H.hcontSlice n) s hs (le_trans hsσ hσT)
    exact hagree_succ_of_sourceBdd p H.hχ0 u₀ n hσ H.hu₀_cont H.hu₀_bound
      L.srcBdd hσT hLs
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
        · -- interior x ∈ Ioo 0 1: window-decay deriv² on the restart series + Ioo
          -- transport.  WALL-FREE: the bound comes from the σ-shifted source package
          -- (`hsrcσ`) + the stage-F windowed decay (`hdecayW`), not an external witness.
          refine ⟨2 * M, le_refl _, ?_⟩
          -- restart-series ↔ slice agreement on the open interior.
          have hEq : Set.EqOn (intervalDomainLift (picardIter p u₀ (n + 1) σ))
              (fun z => ∑' k, restartIterateCoeff p u₀ n σ k * cosineMode k z)
              (Set.Ioo (0 : ℝ) 1) := by
            intro z hz
            have := hrepr_agree σ hσ hσT (Set.Ioo_subset_Icc_self hz)
            simpa only [iterateReprCoeff] using this
          have hser : |deriv (deriv
                (fun z => ∑' k, restartIterateCoeff p u₀ n σ k * cosineMode k z)) x|
              ≤ 2 * M * eigExpWeight (σ / 2)
                + ShenWork.IntervalPicardIterateTimeC1.duhamelGainConst
                  * (σ / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ σ := by
            have hgain_eq : ShenWork.IntervalPicardIterateTimeC1.duhamelGainConst
                = 2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2))
                    / Real.pi ^ ((3 : ℝ) / 2) := rfl
            rw [hgain_eq]
            exact iterate_abs_deriv2_le_of_windowDecay_on p u₀ n hσ hBenv
              (fun k => hM₁ σ hσ hσT k) (hsrcσ σ hσ hσT)
              (hdecayW σ hσ hσT) x
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
  -- the level-(n+1) window adot legs — the K1 induction step.  The from-zero
  -- representation substep consumes only the ledger's bounded source package.
  have hLsT : ∀ r, 0 < r → r ≤ T →
      Continuous (intervalLogisticSource p (picardIter p u₀ n r)) := fun r hr hrT =>
    logisticSource_subtypeCont p u₀ n H.hα (H.hcontSlice n) r hr hrT
  have wA1 : ∀ lo hi, 0 < lo → lo ≤ hi → hi < T →
      WindowAdotLegs p u₀ (n + 1) lo hi :=
    windowAdotLegs_step_on p H.hχ0 u₀ n H.hα H.ha H.hb H.hMnn H.hA₂nn H.hu₀_cont
      H.hu₀_bound L.srcBdd hLsT L.hrepr_sum L.hrepr_agree
      (H.hpos n) (H.hub n) L.hG1 L.hG2
      (H.hpos (n + 1)) (H.hub (n + 1))
      (lift_slice_continuousOn p u₀ H (n + 1))
      L.winAdot
  have srcOn1 : LevelSourceTimeC1OnUpTo p u₀ (n + 1) T := by
    intro c hc hcT
    set offset : ℝ := c / 2 with hoffdef
    set W : ℝ := T - offset with hWdef
    have hoffpos : 0 < offset := by rw [hoffdef]; linarith
    have hoffc : offset < c := by rw [hoffdef]; linarith
    have hoffT : offset < T := lt_trans hoffc hcT
    have hWpos : 0 < W := by rw [hWdef]; linarith
    have hoffW : offset ≤ W := by rw [hoffdef, hWdef]; linarith
    have hprevT := L.srcOn offset hoffpos hoffT
    have hsumTW : offset + W = T := by rw [hWdef]; ring
    have hprevTW : DuhamelSourceTimeC1On
        (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
        offset (offset + W) := by
      rw [hsumTW]
      exact hprevT
    have srcPrev : DuhamelSourceTimeC1On
        (fun s k =>
          cosineCoeffs (logisticLifted p (picardIter p u₀ n (offset + s))) k)
        0 W := by
      simpa [add_comm] using
        ShenWork.IntervalDuhamelSourceTimeC1On.DuhamelSourceTimeC1On.shift_zero
          (offset := offset) (W := W) hprevTW
    have ha₀ : ∀ k,
        |cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) offset)) k|
          ≤ 2 * M :=
      halfStep_coeff_le_twoM p u₀ H (n + 1) hoffpos (le_of_lt hoffT)
    have hshift : Set.MapsTo (fun s : ℝ => s - offset)
        (Set.Icc c T) (Set.Icc offset W) := by
      intro s hs
      exact ⟨by linarith [hs.1, hoffdef], by rw [hWdef]; linarith [hs.2]⟩
    have hrestart : ∀ s ∈ Set.Icc c T, ∀ x : intervalDomainPoint,
        intervalDomainLift (picardIter p u₀ (n + 1) s) x.1 =
          ∑' k, ShenWork.IntervalSourceCoefficientTimeC1.localRestartCoeff
            (cosineCoeffs (intervalDomainLift
              (picardIter p u₀ (n + 1) offset)))
            (fun σ k =>
              cosineCoeffs (logisticLifted p
                (picardIter p u₀ n (offset + σ))) k)
            (s - offset) k * cosineMode k x.1 := by
      intro s hs x
      have hτs : offset < s := lt_of_lt_of_le hoffc hs.1
      have hLs_s : ∀ r, 0 < r → r ≤ s →
          Continuous (intervalLogisticSource p (picardIter p u₀ n r)) := by
        intro r hr hrs
        exact logisticSource_subtypeCont p u₀ n H.hα (H.hcontSlice n)
          r hr (le_trans hrs hs.2)
      have hgen := picardIterateRestart_general_of_sourceBdd p H.hχ0 u₀ n
        H.hu₀_cont H.hu₀_bound L.srcBdd hoffpos hτs hs.2 hLs_s
      exact hgen x.2
    have hprofile_joint : ContinuousOn
        (Function.uncurry
          (fun s x => intervalDomainLift (picardIter p u₀ (n + 1) s) x))
        (Set.Icc c T ×ˢ Set.Icc (0 : ℝ) 1) :=
      restartProfile_jointContinuousOn_On_shift
        (M₀ := 2 * M) (by linarith [H.hMnn]) ha₀ srcPrev
        hoffpos hoffW hshift hrestart
    refine sourceTimeC1On_succ_of_sourceTimeC1On H.hα H.ha H.hb
      (M := M) (G1 := G1win p M c T) (G2 := G2win A₂ c)
      (M₀ := 2 * M) (by linarith [H.hMnn]) ha₀ srcPrev
      hcT.le hoffpos hshift (iterateReprCoeff p u₀ (n + 1)) ?_ ?_ ?_ ?_ ?_ ?_
      hrestart ?_ hprofile_joint
    · intro σ hσ
      exact hrepr_sum σ (lt_of_lt_of_le hc hσ.1) hσ.2
    · intro σ hσ
      exact hrepr_agree σ (lt_of_lt_of_le hc hσ.1) hσ.2
    · intro σ hσ x hx
      exact H.hpos (n + 1) σ (lt_of_lt_of_le hc hσ.1) hσ.2 x hx
    · intro σ hσ x hx
      exact H.hub (n + 1) σ (lt_of_lt_of_le hc hσ.1) hσ.2 x hx
    · intro σ hσ x _hx
      exact le_trans (H.hG1all (n + 1) σ (lt_of_lt_of_le hc hσ.1) hσ.2 x)
        (G1profile_le_G1win H.hMnn hc hσ.1 hσ.2)
    · intro σ hσ x _hx
      exact le_trans (hG2 σ (lt_of_lt_of_le hc hσ.1) hσ.2 x)
        (G2profile_le_G2win H.hA₂nn hc hσ.1)
    · intro σ hσ
      exact lift_slice_continuousOn p u₀ H (n + 1) σ
        (lt_of_lt_of_le hc hσ.1) hσ.2
  have srcBdd1 : DuhamelSourceBddOn
      (patchedSource p u₀ (picardIter p u₀ (n + 1))) T :=
    sourceBdd_of_levelData p u₀ (n + 1) H srcOn1
      (iterateReprCoeff p u₀ (n + 1)) hrepr_sum hrepr_agree
      (H.hG1all (n + 1)) hG2
  refine
    { hrepr_sum := hrepr_sum
      hrepr_agree := hrepr_agree
      hG1 := H.hG1all (n + 1)
      hG2 := hG2
      srcWin := srcWin_of_levelData p u₀ (n + 1) H (iterateReprCoeff p u₀ (n + 1))
        hrepr_sum hrepr_agree (H.hG1all (n + 1)) hG2 wA1
      winAdot := wA1
      srcOn := srcOn1
      srcBdd := srcBdd1 }

/-- **The full tower induction (under the GATE).**  For every `n`, the carrier
holds. -/
def tower_all
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {M A₂ T : ℝ}
    (H : TowerInputs p u₀ M A₂ T) :
    ∀ n : ℕ, TowerLevel p u₀ M A₂ T n
  | 0 => tower_zero p u₀ H
  | n + 1 => tower_succ p u₀ H (tower_all p u₀ H n)

end ShenWork.IntervalPicardSourceTower
