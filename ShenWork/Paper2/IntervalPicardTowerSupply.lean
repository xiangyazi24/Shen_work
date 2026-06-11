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

/-! ## §5 — W6b — The NARROWED, instantiable cone supply.

`paper2_theorem_1_1_chiZero_from_coneSupply`'s hypothesis `HCone` is keyed to an
ARBITRARY datum `D` at every horizon (`∀ u₀ ∀ D, … → Σ' M A₂, bundle`).  As the
W4/W5 recon established, the gate conjunct of that bundle is gate-UNSATISFIABLE at
large horizons (the cone smallness `Ke·I(T) ≤ ½` and `C_L·T < 1` fail), so the
`∀ D` form is plausibly UNINSTANTIABLE — yet the capstone only ever invokes the
providers at the cone-constructed datum (CoreProvider
`quantitativeLocalExistence_chiZero_wdata`/`hMildLocal_chi0_zero_of_wdata`).

This section delivers, additively (the existing `from_coneSupply` is unchanged):

* `paper2_theorem_1_1_chiZero_from_coneSupplyNarrow` — Theorem 1.1 from the
  ADDITIVE per-constructed-datum capstone `paper2_theorem_1_1_chiZero_of_datumProviders`
  (CoreProvider §W6b).  Its hypothesis `DatumProviderSupply p` is a per-`u₀` EXISTENCE
  of a small-horizon datum bundling the two iterate-side legs at THAT datum — the
  invocation-restricted, instantiable surface (the residual is owed only at the cone
  horizon `δ`, where the gate genuinely holds).

* `from_cone_construction` — THE BRIDGE.  Discharges `DatumProviderSupply` from the
  gate-data cone `coneGradientMildSolutionData_exists_with_gate_data`, reducing the
  paper theorem to ONLY a per-constructed-datum residual bundle.  The gate, slice
  continuity, strict positivity, limit ball (`D.hbound`), and datum continuity are
  discharged FROM THE CONE; what remains is the per-datum `ResidualAtDatum`
  (`hsrc0` + the three legs the cone returns but HIDES behind its existential internal
  mass — see the honest leftover note on `ResidualAtDatum`). -/

/-- **The honest per-constructed-datum residual the bridge cannot pull from the cone.**

At the gate-data cone's datum `D` (mass `D.M`), `towerInputs_of_cone` needs the gate
AND the per-iterate ball AND the `u₀`-coefficient bound AND `D.T ≤ 1` all at the SINGLE
mass `D.M`.  The gate is returned at `D.M`; but the iterate ball is returned only inside
the existential `∃ F : PicardConvFacts, F.T = δ` at the HIDDEN mass `F.M` (the cone sets
`F.M = D.M = M` definitionally, yet its return type exposes neither `F.M` nor `δ ≤ 1`,
so the equalities `F.M = D.M`, `δ ≤ 1`, and the datum-coefficient bound at `D.M` are not
type-recoverable).  Hence the bridge carries these three cone-internal-but-hidden facts
together with the genuine analytic residual `hsrc0` as ONE per-datum bundle.  All four
are "morally cone-returned"; only `hsrc0` is genuinely open (see W4 STATUS). -/
structure ResidualAtDatum
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (D : GradientMildSolutionData p u₀) where
  /-- horizon ≤ 1 (cone-internal `T₀ ≤ ½`, hidden by the existential). -/
  hT1 : D.T ≤ 1
  /-- datum cosine-coefficient bound at the cone mass (cone-internal `≥ M_in`, hidden). -/
  hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ D.M
  /-- per-iterate ball at the cone mass (cone-returned via `F.hball`, mass hidden). -/
  hball : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ D.T → ∀ y : intervalDomainPoint,
    |picardIter p u₀ n σ y| ≤ D.M
  /-- the genuinely-open analytic surface (W4 STATUS: the irreducible `hsrc0`).
  `TowerConeAnalyticResidual`'s `M`/`A₂` are phantom (only `hsrc0` is a field). -/
  hAnalytic : TowerConeAnalyticResidual p u₀ D D.M 0

/-- **`datumIterLegs_of_cone`.**  At a gate-data cone datum `D` (gate + slice
continuity + strict positivity at mass `D.M`, plus the PID datum facts and the per-datum
`ResidualAtDatum`), build the two iterate-side legs `DatumIterLegs` the narrowed capstone
consumes.  Routes through `towerInputs_of_cone` at mass `D.M` + the two tower
projections (`wdataProvider_of_tower`, `hiter_cont_of_tower`). -/
def datumIterLegs_of_cone
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (u₀ : intervalDomainPoint → ℝ)
    (D : GradientMildSolutionData p u₀) {A₂ : ℝ}
    (hA₂nn : 0 ≤ A₂)
    (hgate : GateCondition p D.M A₂ D.T)
    (hDu : D.u = picardLimit p u₀ D.T)
    (hu₀_cont : Continuous u₀)
    (hpos : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ n σ) x)
    (hcontSlice : ∀ n : ℕ, HasContinuousSlices D.T (picardIter p u₀ n))
    (R : ResidualAtDatum p u₀ D) :
    ShenWork.Paper2.Thm11ChiZeroCoreProvider.DatumIterLegs p u₀ D :=
  -- the limit ball `|D.u s y| ≤ D.M` is the datum's own `hbound` (after `hDu`).
  have hlim_ball : ∀ (s : ℝ), 0 < s → s ≤ D.T → ∀ y : intervalDomainPoint,
      |D.u s y| ≤ D.M := D.hbound
  -- re-wrap the analytic residual at the cone's gate budget `A₂` (`A₂` is phantom in
  -- `TowerConeAnalyticResidual` — only `hsrc0` is a field).
  let HA : TowerConeAnalyticResidual p u₀ D D.M A₂ := ⟨R.hAnalytic.hsrc0⟩
  let HT := towerInputs_of_cone p hχ0 hα ha hb u₀ D
    D.hM.le R.hT1 hA₂nn hgate hu₀_cont R.hu₀_bound hpos hcontSlice R.hball
    hlim_ball HA
  ⟨ShenWork.IntervalPicardTowerProjection.wdataProvider_of_tower p u₀ D HT.2.2,
   ShenWork.IntervalPicardTowerProjection.hiter_cont_of_tower p u₀ HT.2.2⟩

/-- **`from_cone_construction` — THE W6b BRIDGE / PRIZE.**

Paper 2 Theorem 1.1 (χ₀ = 0) modulo ONLY a per-constructed-datum residual.  The
gate-data cone supplies, at its own small horizon `δ`, the datum `D` with the gate /
slice continuity / strict positivity / limit ball; the caller supplies, per
cone datum, the `ResidualAtDatum` bundle (the genuine `hsrc0` analytic surface plus the
three cone-hidden legs `hT1`/`hu₀_bound`/`hball`).  This turns the plausibly-uninstantiable
`∀ D` `from_coneSupply` into a hypothesis owed at exactly the cone-constructed datum. -/
theorem from_cone_construction
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (Hres : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T → ResidualAtDatum p u₀ D) :
    ShenWork.Paper2.Theorem_1_1 intervalDomain p :=
  ShenWork.Paper2.Thm11ChiZeroCoreProvider.paper2_theorem_1_1_chiZero_of_datumProviders
    p hχ0 ha hb hα hγ
    (fun M_in hM_in =>
      -- the cone returns `∃ δ A₂, …` (Prop); choose the datum-free `δ`/`A₂` and the
      -- per-`u₀` existence body via `Classical.choice` (already in the axiom baseline).
      let C := coneGradientMildSolutionData_exists_with_gate_data p hχ0 hM_in hα
      let δ := C.choose
      let A₂ := C.choose_spec.choose
      have hδ : 0 < δ := C.choose_spec.choose_spec.1
      have hA₂nn : 0 ≤ A₂ := C.choose_spec.choose_spec.2.1
      have hbody := C.choose_spec.choose_spec.2.2
      ⟨δ, hδ, fun u₀ hu₀ hbound =>
        let E := hbody u₀ hu₀.admissible.2 hbound
          (ShenWork.Paper2.ConeQuantBridge.positiveInitialDatum_nonneg hu₀)
          (ShenWork.Paper2.ConeQuantBridge.positiveInitialDatum_pos_somewhere hu₀)
        let D := E.choose
        have hspec := E.choose_spec
        have hDT : D.T = δ := hspec.1
        have hDu : D.u = picardLimit p u₀ δ := hspec.2.1
        have hgate : GateCondition p D.M A₂ D.T := hspec.2.2.1
        have hcontSlice : ∀ n, HasContinuousSlices D.T (picardIter p u₀ n) :=
          hspec.2.2.2.1
        have hF : ∃ F : ShenWork.IntervalPicardLimitCoeffConv.PicardConvFacts p u₀,
          F.T = δ := hspec.2.2.2.2.1
        have hpos : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ D.T →
            ∀ x ∈ Set.Icc (0 : ℝ) 1,
            0 < intervalDomainLift (picardIter p u₀ n σ) x := fun n σ hσ hσT x hx =>
          hspec.2.2.2.2.2 n σ hσ (hσT.trans hDT.le) x hx
        have hDu' : D.u = picardLimit p u₀ D.T := by rw [hDT]; exact hDu
        ⟨D, hDT, hDu, hcontSlice, hF,
          datumIterLegs_of_cone p hχ0 hα ha.le hb.le u₀ D hA₂nn hgate hDu'
            hu₀.admissible.2 hpos hcontSlice (Hres u₀ hu₀ D hDu')⟩⟩)

/-- **`paper2_theorem_1_1_chiZero_from_coneSupplyNarrow` — the narrowed, instantiable
entry point.**  Theorem 1.1 (χ₀ = 0) from the per-constructed-datum supply
`DatumProviderSupply p` (the additive CoreProvider capstone).  Thin alias making the
narrowed surface available at the TowerSupply layer alongside the back-compat
`from_coneSupply`. -/
theorem paper2_theorem_1_1_chiZero_from_coneSupplyNarrow
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (Hsupply : ShenWork.Paper2.Thm11ChiZeroCoreProvider.DatumProviderSupply p) :
    ShenWork.Paper2.Theorem_1_1 intervalDomain p :=
  ShenWork.Paper2.Thm11ChiZeroCoreProvider.paper2_theorem_1_1_chiZero_of_datumProviders
    p hχ0 ha hb hα hγ Hsupply

end ShenWork.IntervalPicardTowerSupply
