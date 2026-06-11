/-
  ShenWork/Paper2/IntervalPicardTowerSupply.lean

  **Tower campaign — the cone-side supply (`towerInputs_of_cone`).**

  The capstone `paper2_theorem_1_1_chiZero_unconditional`
  (`IntervalDomainThm11ChiZeroCoreProvider`) consumes a single residual leg

      HWdata : ∀ u₀, PID u₀ → ∀ D, D.u = picardLimit p u₀ D.T → WdataProvider p u₀ D

  which `IntervalPicardTowerProjection.HWdata_of_tower` discharges from a per-datum
  tower-input bundle

      HTower : ∀ u₀ D, D.u = picardLimit … → Σ' M A₂, TowerInputs p u₀ M A₂ D.T .

  This file SUPPLIES `HTower` at a cone-constructed datum.  `TowerInputs`
  (`IntervalPicardSourceTower`) is read FIELD BY FIELD; the fields split into:

  ## (a) Cone-returned / cheaply-provable legs — DISCHARGED here.
    * `hχ0`/`hα`/`ha`/`hb` — regime constants (hypotheses).
    * `hMnn`/`hTpos`/`hT1`/`hA₂nn` — `0 ≤ M`, `0 < D.T`, `D.T ≤ 1`, `0 ≤ A₂`: the
      mass/horizon basics returned by the gate-data cone.
    * `hgate` — `GateCondition p D.M A₂ D.T`: RETURNED, discharged, by
      `coneGradientMildSolutionData_exists_with_gate_data`.
    * `hu₀_cont`/`hu₀_bound` — datum continuity + bounded cosine coefficients, from
      the PID (`hu₀.admissible`) via `cosineCoeffs_abs_le_of_continuous_bounded`.
    * `hpos` — per-iterate strict positivity on `Icc 0 1`: the ROUND-3 strict
      positivity tail RETURNED by the gate-data cone.
    * `hG2end` — the two endpoint G2-step budgets (`x ∈ {0,1}`): PROVED
      unconditionally by `hStepEnd0_proved`/`hStepEnd1_proved` (the zero-extension
      junk-derivative fact — `∂ₓₓ lift = 0` at `0`/`1`), so they are NOT residual.
    * `hcontSlice` — per-iterate slice continuity (`HasContinuousSlices`, n-uniform):
      RETURNED by `coneGradientMildSolutionData_exists_with_gate_data`, so it is a
      cone leg, NOT an analytic residual.  It REPLACES the former `hM₁` residual field:
      the half-step coefficient bound `M₁ ≤ 2M` is now DERIVED in-tower from this slice
      continuity + the ball sup `hub` via `cosineCoeffs_abs_le_of_continuous_bounded`
      (`IntervalPicardSourceTower.halfStep_coeff_le_twoM`).
    * `hub` — per-iterate ball sup on `Icc 0 1` (n-uniform): DERIVED in-tower from the
      cone-returned n-uniform SUBTYPE ball `hball` (`= PicardConvFacts.hball` with
      `F.M = M`, genuinely returned by `coneGradientMildSolutionData_exists_with_gate_data`).
      On `Icc 0 1` the lift collapses to the subtype value (`dif_pos`) and
      `a ≤ |a| ≤ M`, so the former `hub` field is no longer an analytic residual.

  ## (b) Genuinely-open analytic legs — the per-iterate spatial-`C²` bootstrap.
    `hsrc0` (the `adot` K1 stack has been DERIVED in-tower via the
    `WindowAdotLegs` induction — see IntervalPicardWindowAdot) ALL depend
    on the per-iterate spatial-`C²`/positivity/Neumann regularity of EVERY Picard
    level (`picardIterateHasC2Slices_all`), whose step data
    (`PicardRegularityStepData`) is itself a `DuhamelSourceTimeC1`-plus-spectral-
    agreement bundle: the bootstrap is circular at the level of the existing
    producers (the project's standing analytic wall — see `UNPROVED_TARGETS.md`).
    They are NOT faked: they are carried as ONE explicit named hypothesis package
    `TowerConeAnalyticResidual`, which IS the exact remaining analytic surface (the
    same family of facts `uniformWiring_closure` consumes — `hsrc0`/`hG1all`
    — the `adot` K1 data now derived in-tower
    the clamped source producer reads, restated at the cone datum's horizon).  The
    former `hub` leg has been REMOVED from the residual (derived in-tower from the
    cone-returned subtype ball `hball`; see (a)).  The
    former `witness` leg (the half-step shifted-source `ShiftedSourceWitness`) has
    been REMOVED from the residual: its `src`/`hagree_window` come WALL-FREE from the
    non-negative time-shift of `hsrc0`, and its `hdecay` is DERIVED in-tower from the
    level's representation triple + ball + K2 facts via the stage-F per-slice source
    decay (`IntervalPicardSliceWitnessSupply.shifted_source_windowDecay`), the
    downstream G2 bound only reading the decay on the integration window `[0,t/2]`.
    The former `hM₁` leg has been REMOVED from the residual (derived in-tower from the
    cone-returned slice continuity; see (a)).
    The former `hL_cont` leg has been REMOVED from the residual: it demanded GLOBAL
    ℝ-continuity of the ZERO-EXTENSION `logisticLifted = intervalDomainLift ∘
    intervalLogisticSource`, which is FALSE (UNSATISFIABLE) because the cone returns
    strict iterate positivity on ALL of `Icc 0 1` (endpoints included), so the source
    is generically nonzero at `0`/`1` and the zero-extension JUMPS.  It is replaced
    in-tower by the SATISFIABLE source-slice SUBTYPE continuity, derived from the
    cone-returned per-iterate slice continuity `hcontSlice` + `1 ≤ p.α` via
    `IntervalPicardSourceSubtypeCont.logisticSource_subtypeCont`, and consumed through
    the source-subtype agreement clone `hagree_succ_of_sourceSubtypeCont`.

  This is the project's standing discipline (TASK_QUEUE group C): a theorem that
  projects from an assumption package is honest IFF the field is the EXACT remaining
  analytic hypothesis.  `TowerConeAnalyticResidual` is that field; everything in (a)
  is genuinely discharged.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardTowerProjection
import ShenWork.Paper2.IntervalPicardG1All
import ShenWork.Paper2.IntervalPicardUniformWiringDischarge
import ShenWork.Paper2.IntervalMildPicardConeData
import ShenWork.Paper2.IntervalDomainThm11ChiZeroCoreProvider

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalDomain)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard
  (picardIter picardLimit GradientMildSolutionData HasContinuousSlices)
open ShenWork.IntervalPicardSourceTower (halfStep_coeff_le_twoM)
open ShenWork.IntervalMildPicardRegularity (logisticSourceFun)
open ShenWork.IntervalHomogeneousQuantBound (eigExpWeight)
open ShenWork.IntervalPicardIterateUniform
  (G1profile G2profile Benv GateCondition)
open ShenWork.IntervalPicardIterateRestartLocal (ShiftedSourceWitness)
open ShenWork.IntervalPicardIterateTimeC1 (duhamelGainConst)
open ShenWork.IntervalPicardSourceTower (TowerInputs)
open ShenWork.IntervalPicardUniformWiringDischarge (hStepEnd0_proved hStepEnd1_proved)
open ShenWork.Paper2 (PositiveInitialDatum)
open ShenWork.Paper2.HresWiring (WdataProvider)
open ShenWork.IntervalMildPicardConeData (coneGradientMildSolutionData_exists_with_gate_data)

noncomputable section

namespace ShenWork.IntervalPicardTowerSupply

/-! ## §1 — The exact remaining analytic surface `TowerConeAnalyticResidual`.

The per-iterate spatial-`C²`-bootstrap-dependent legs of `TowerInputs`, restated at
a datum `D` with horizon `D.T` and cone mass `M`, budget `A₂`.  Every field here is
exactly a `TowerInputs` field (same shape, `T := D.T`); the bundle is the honest
residual the cone construction does not already hand back. -/
structure TowerConeAnalyticResidual
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (D : GradientMildSolutionData p u₀) (M A₂ : ℝ) where
  /-- The level-`n` canonical logistic source time-`C¹` package (deliverable B). -/
  hsrc0 : ∀ n : ℕ, ShenWork.IntervalDuhamelClosedC2.DuhamelSourceTimeC1
    (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)

/-! ## §2 — `towerInputs_of_cone` — assembling `TowerInputs` at the cone datum.

The cheap legs are discharged from the cone-returned data (gate, round-3 positivity,
PID datum facts) and the proved endpoint discharges; the deep legs are forwarded from
the named residual `H`. -/

/-- **`towerInputs_of_cone`.**  At a cone-constructed datum `D` (with the gate, the
round-3 per-iterate strict positivity, and the basic mass/horizon facts), plus the
PID datum data and the named analytic residual `H`, assemble
`Σ' M A₂, TowerInputs p u₀ M A₂ D.T`.

The supplied `M`/`A₂` are the cone's own mass `M` and gate budget `A₂`. -/
def towerInputs_of_cone
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (u₀ : intervalDomainPoint → ℝ)
    (D : GradientMildSolutionData p u₀) {M A₂ : ℝ}
    (hMnn : 0 ≤ M) (hT1 : D.T ≤ 1) (hA₂nn : 0 ≤ A₂)
    (hgate : GateCondition p M A₂ D.T)
    -- PID datum facts:
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M)
    -- the cone's ROUND-3 per-iterate strict positivity (returned by the gate cone):
    (hpos : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ n σ) x)
    -- the cone's per-iterate slice continuity (returned `HasContinuousSlices`, NOT
    -- analytic-wall): feeds the in-tower `M₁ ≤ 2M` derivation (`halfStep_coeff_le_twoM`),
    -- so the former `hM₁` field is no longer an analytic residual:
    (hcontSlice : ∀ n : ℕ, HasContinuousSlices D.T (picardIter p u₀ n))
    -- the cone's per-iterate n-uniform ball bound (returned `PicardConvFacts.hball` with
    -- `F.M = M`, NOT an analytic wall): feeds the in-tower `hub` derivation, so the former
    -- `hub` field is no longer an analytic residual:
    (hball : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ D.T → ∀ y : intervalDomainPoint,
      |picardIter p u₀ n σ y| ≤ M)
    -- the cone's LIMIT ball (returned `PicardConvFacts.hlim_ball` with `F.M = M`, NOT
    -- an analytic wall): feeds the in-tower `hu₀_sup` derivation for `hG1all`:
    (hlim_ball : ∀ (s : ℝ), 0 < s → s ≤ D.T → ∀ y : intervalDomainPoint,
      |D.u s y| ≤ M)
    -- the genuinely-open per-iterate analytic surface:
    (H : TowerConeAnalyticResidual p u₀ D M A₂) :
    Σ' M A₂ : ℝ, TowerInputs p u₀ M A₂ D.T :=
  have h0mem : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := by norm_num
  have hMpos : 0 < M := by
    have hp := hpos 0 D.T D.hT le_rfl 0 h0mem
    have hb := hball 0 D.T D.hT le_rfl ⟨0, h0mem⟩
    have hlift : intervalDomainLift (picardIter p u₀ 0 D.T) 0
        = picardIter p u₀ 0 D.T ⟨0, h0mem⟩ := by
      simp [intervalDomainLift, h0mem]
    rw [hlift] at hp
    exact lt_of_lt_of_le hp (le_trans (le_abs_self _) hb)
  ⟨M, A₂,
  { hχ0 := hχ0
    hα := hα
    ha := ha
    hb := hb
    hMnn := hMnn
    hTpos := D.hT
    hT1 := hT1
    hA₂nn := hA₂nn
    hgate := hgate
    hu₀_cont := hu₀_cont
    hu₀_bound := hu₀_bound
    hsrc0 := H.hsrc0
    -- `hG1all` DERIVED (hand-written kernel line, windowed source family):
    hG1all := ShenWork.IntervalPicardG1All.hG1all_of_cone p hχ0 u₀ hMpos hu₀_cont
      (ShenWork.IntervalPicardG1All.u₀_lift_abs_le p hMpos.le hu₀_cont D hlim_ball)
      hball
    hcontSlice := hcontSlice
    -- endpoint G2-step budgets: PROVED (zero-extension junk-derivative), per `x∈{0,1}`.
    hG2end := by
      intro n t ht htT x hx
      rcases hx with hx0 | hx1
      · subst hx0; exact hStepEnd0_proved hMnn n t ht htT
      · rw [Set.mem_singleton_iff] at hx1; subst hx1
        exact hStepEnd1_proved hMnn n t ht htT
    hpos := hpos
    -- `hub` DERIVED from the cone-returned n-uniform subtype ball `hball` (NOT residual):
    -- on `Icc 0 1` the lift collapses to the subtype value (`dif_pos`), and
    -- `a ≤ |a| ≤ M`.
    hub := by
      intro n σ hσ hσT x hx
      have hsub := hball n σ hσ hσT ⟨x, hx⟩
      have hle : picardIter p u₀ n σ ⟨x, hx⟩ ≤ M :=
        le_trans (le_abs_self _) hsub
      simpa only [intervalDomainLift, dif_pos hx] using hle
    }⟩

/-! ## §3 — The capstone residual `HWdata` from a per-datum cone supply.

`HWdata_of_coneSupply` packages a per-datum `TowerConeAnalyticResidual` supply (plus
the cone-returned gate/positivity/mass facts) into the capstone's `HWdata` leg via
`towerInputs_of_cone` + `HWdata_of_tower`. -/

/-- The per-datum cone supply: for every datum `D` at the canonical Picard limit, the
cone-returned gate/positivity/mass facts and the named analytic residual `H`, packaged
as the `HTower` shape `HWdata_of_tower` consumes.  The datum continuity `hu₀_cont` is
carried in the supply bundle (it is available at the cone construction site). -/
def coneTowerSupply
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (HCone : ∀ (u₀ : intervalDomainPoint → ℝ),
      ∀ D : GradientMildSolutionData p u₀,
        D.u = picardLimit p u₀ D.T →
        Σ' (M A₂ : ℝ),
          (0 ≤ M) ×' (D.T ≤ 1) ×' (0 ≤ A₂) ×' (GateCondition p M A₂ D.T) ×'
          (Continuous u₀) ×'
          (∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M) ×'
          (∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
            0 < intervalDomainLift (picardIter p u₀ n σ) x) ×'
          (∀ n : ℕ, HasContinuousSlices D.T (picardIter p u₀ n)) ×'
          (∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ D.T → ∀ y : intervalDomainPoint,
            |picardIter p u₀ n σ y| ≤ M) ×'
          (∀ (s : ℝ), 0 < s → s ≤ D.T → ∀ y : intervalDomainPoint,
            |D.u s y| ≤ M) ×'
          TowerConeAnalyticResidual p u₀ D M A₂) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      ∀ D : GradientMildSolutionData p u₀,
        D.u = picardLimit p u₀ D.T →
        Σ' M A₂ : ℝ, TowerInputs p u₀ M A₂ D.T :=
  fun u₀ D hDu =>
    let S := HCone u₀ D hDu
    towerInputs_of_cone p hχ0 hα ha hb u₀ D
      S.2.2.1 S.2.2.2.1 S.2.2.2.2.1 S.2.2.2.2.2.1
      S.2.2.2.2.2.2.1 S.2.2.2.2.2.2.2.1 S.2.2.2.2.2.2.2.2.1
      S.2.2.2.2.2.2.2.2.2.1 S.2.2.2.2.2.2.2.2.2.2.1
      S.2.2.2.2.2.2.2.2.2.2.2.1 S.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`iterCoeffTimeCont_of_coneSupply` — the capstone `Hiter` from the cone supply.**

The per-datum cosine-coefficient TIME continuity (`IterCoeffTimeContProvider`) is
discharged from the same per-datum `TowerInputs` bundle the `WdataProvider` uses, via
`IntervalPicardTowerProjection.hiter_cont_of_tower` (which reads the time continuity
off the tower's canonical logistic-source `C¹` packages `H.hsrc0 n`).  No new field of
`HCone` is needed — the tower bundle already carries `hsrc0`. -/
def iterCoeffTimeCont_of_coneSupply
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (HCone : ∀ (u₀ : intervalDomainPoint → ℝ),
      ∀ D : GradientMildSolutionData p u₀,
        D.u = picardLimit p u₀ D.T →
        Σ' (M A₂ : ℝ),
          (0 ≤ M) ×' (D.T ≤ 1) ×' (0 ≤ A₂) ×' (GateCondition p M A₂ D.T) ×'
          (Continuous u₀) ×'
          (∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M) ×'
          (∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
            0 < intervalDomainLift (picardIter p u₀ n σ) x) ×'
          (∀ n : ℕ, HasContinuousSlices D.T (picardIter p u₀ n)) ×'
          (∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ D.T → ∀ y : intervalDomainPoint,
            |picardIter p u₀ n σ y| ≤ M) ×'
          (∀ (s : ℝ), 0 < s → s ≤ D.T → ∀ y : intervalDomainPoint,
            |D.u s y| ≤ M) ×'
          TowerConeAnalyticResidual p u₀ D M A₂) :
    ShenWork.Paper2.Thm11ChiZeroCoreProvider.IterCoeffTimeContProvider p :=
  fun u₀ _hu₀ D hDu =>
    ShenWork.IntervalPicardTowerProjection.hiter_cont_of_tower p u₀
      (coneTowerSupply p hχ0 hα ha hb HCone u₀ D hDu).2.2

/-- **`HWdata_of_coneSupply` — the capstone `HWdata` from the cone supply.** -/
def HWdata_of_coneSupply
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (HCone : ∀ (u₀ : intervalDomainPoint → ℝ),
      ∀ D : GradientMildSolutionData p u₀,
        D.u = picardLimit p u₀ D.T →
        Σ' (M A₂ : ℝ),
          (0 ≤ M) ×' (D.T ≤ 1) ×' (0 ≤ A₂) ×' (GateCondition p M A₂ D.T) ×'
          (Continuous u₀) ×'
          (∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M) ×'
          (∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
            0 < intervalDomainLift (picardIter p u₀ n σ) x) ×'
          (∀ n : ℕ, HasContinuousSlices D.T (picardIter p u₀ n)) ×'
          (∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ D.T → ∀ y : intervalDomainPoint,
            |picardIter p u₀ n σ y| ≤ M) ×'
          (∀ (s : ℝ), 0 < s → s ≤ D.T → ∀ y : intervalDomainPoint,
            |D.u s y| ≤ M) ×'
          TowerConeAnalyticResidual p u₀ D M A₂) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        D.u = picardLimit p u₀ D.T → WdataProvider p u₀ D :=
  ShenWork.IntervalPicardTowerProjection.HWdata_of_tower p
    (coneTowerSupply p hχ0 hα ha hb HCone)

/-! ## §4 — FINAL WIRING — Paper 2 Theorem 1.1 (χ₀ = 0) from the cone supply.

Feeds `HWdata_of_coneSupply` into the capstone
`paper2_theorem_1_1_chiZero_unconditional`.  The residual surface is now the regime
constants (`χ₀ = 0`, `0 < a`, `0 < b`, `1 ≤ α`, `1 ≤ γ`) plus the SINGLE per-datum
cone-supply package `HCone` — the cone-returned gate/positivity/mass facts (genuinely
returned by `coneGradientMildSolutionData_exists_with_gate_data`) bundled with the
exact remaining analytic surface `TowerConeAnalyticResidual` (the per-iterate
spatial-`C²`-bootstrap legs). -/

/-- **Paper 2 Theorem 1.1 (χ₀ = 0) from the cone supply.**  The capstone with its
`HWdata` leg discharged via the tower projection + `towerInputs_of_cone`. -/
theorem paper2_theorem_1_1_chiZero_from_coneSupply
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (HCone : ∀ (u₀ : intervalDomainPoint → ℝ),
      ∀ D : GradientMildSolutionData p u₀,
        D.u = picardLimit p u₀ D.T →
        Σ' (M A₂ : ℝ),
          (0 ≤ M) ×' (D.T ≤ 1) ×' (0 ≤ A₂) ×' (GateCondition p M A₂ D.T) ×'
          (Continuous u₀) ×'
          (∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M) ×'
          (∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
            0 < intervalDomainLift (picardIter p u₀ n σ) x) ×'
          (∀ n : ℕ, HasContinuousSlices D.T (picardIter p u₀ n)) ×'
          (∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ D.T → ∀ y : intervalDomainPoint,
            |picardIter p u₀ n σ y| ≤ M) ×'
          (∀ (s : ℝ), 0 < s → s ≤ D.T → ∀ y : intervalDomainPoint,
            |D.u s y| ≤ M) ×'
          TowerConeAnalyticResidual p u₀ D M A₂) :
    ShenWork.Paper2.Theorem_1_1 intervalDomain p :=
  ShenWork.Paper2.Thm11ChiZeroCoreProvider.paper2_theorem_1_1_chiZero_unconditional
    p hχ0 ha hb hα hγ
    (iterCoeffTimeCont_of_coneSupply p hχ0 hα ha.le hb.le HCone)
    (HWdata_of_coneSupply p hχ0 hα ha.le hb.le HCone)

end ShenWork.IntervalPicardTowerSupply
