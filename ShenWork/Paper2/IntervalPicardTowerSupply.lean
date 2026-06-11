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

  ## (b) In-tower source production.
    The endpoint-inclusive source-bounded package and the positive-window
    `TimeC1On` source package are produced level-by-level inside the tower from L0,
    REC, representation, ball, and K2 facts.  The cone supply therefore carries no
    separate analytic residual field.

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

/-! ## §1 — `towerInputs_of_cone` — assembling `TowerInputs` at the cone datum.

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
    (hu₀_nonneg : ∀ y : intervalDomainPoint, 0 ≤ u₀ y)
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
      |D.u s y| ≤ M) :
    -- the tower's source packages are produced in-tower from L0 + REC:
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
    hu₀_nonneg := hu₀_nonneg
    hu₀_abs_bound := by
      have hu₀_lift_abs :=
        ShenWork.IntervalPicardG1All.u₀_lift_abs_le p hMpos.le hu₀_cont D hlim_ball
      intro y
      simpa [intervalDomainLift, y.2] using hu₀_lift_abs y.1
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

/-! ## §2 — The capstone `HWdata` from a per-datum cone supply.

`HWdata_of_coneSupply` packages the cone-returned gate/positivity/mass facts into the
capstone's `HWdata` leg via `towerInputs_of_cone` + `HWdata_of_tower`. -/

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
            |D.u s y| ≤ M)) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        D.u = picardLimit p u₀ D.T →
        Σ' M A₂ : ℝ, TowerInputs p u₀ M A₂ D.T :=
  fun u₀ hu₀ D hDu =>
    let S := HCone u₀ D hDu
    towerInputs_of_cone p hχ0 hα ha hb u₀ D
      S.2.2.1 S.2.2.2.1 S.2.2.2.2.1 S.2.2.2.2.2.1
      S.2.2.2.2.2.2.1 (ShenWork.Paper2.ConeQuantBridge.positiveInitialDatum_nonneg hu₀)
      S.2.2.2.2.2.2.2.1 S.2.2.2.2.2.2.2.2.1
      S.2.2.2.2.2.2.2.2.2.1 S.2.2.2.2.2.2.2.2.2.2.1
      S.2.2.2.2.2.2.2.2.2.2.2

/-- **`iterCoeffTimeCont_of_coneSupply` — the capstone `Hiter` from the cone supply.**

The per-datum cosine-coefficient TIME continuity (`IterCoeffTimeContProvider`) is
discharged from the same per-datum `TowerInputs` bundle the `WdataProvider` uses, via
`IntervalPicardTowerProjection.hiter_cont_of_tower`. -/
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
            |D.u s y| ≤ M)) :
    ShenWork.Paper2.Thm11ChiZeroCoreProvider.IterCoeffTimeContProvider p :=
  fun u₀ hu₀ D hDu =>
    ShenWork.IntervalPicardTowerProjection.hiter_cont_of_tower p u₀
      (coneTowerSupply p hχ0 hα ha hb HCone u₀ hu₀ D hDu).2.2

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
            |D.u s y| ≤ M)) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        D.u = picardLimit p u₀ D.T → WdataProvider p u₀ D :=
  ShenWork.IntervalPicardTowerProjection.HWdata_of_tower p
    (coneTowerSupply p hχ0 hα ha hb HCone)

/-! ## §3 — FINAL WIRING — Paper 2 Theorem 1.1 (χ₀ = 0) from the cone supply.

Feeds `HWdata_of_coneSupply` into the capstone
`paper2_theorem_1_1_chiZero_unconditional`.  The cone-supply package `HCone` contains
only the cone-returned gate/positivity/mass facts; source regularity is produced inside
the tower. -/

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
            |D.u s y| ≤ M)) :
    ShenWork.Paper2.Theorem_1_1 intervalDomain p :=
  ShenWork.Paper2.Thm11ChiZeroCoreProvider.paper2_theorem_1_1_chiZero_unconditional
    p hχ0 ha hb hα hγ
    (iterCoeffTimeCont_of_coneSupply p hχ0 hα ha.le hb.le HCone)
    (HWdata_of_coneSupply p hχ0 hα ha.le hb.le HCone)

/-! ## §5 — Narrow cone bridge.

The strengthened cone construction exposes every bookkeeping fact needed by
`towerInputs_of_cone`.  The source regularity leg is now produced in-tower from the
level-zero source package plus the recursive source step, so the bridge below has no
analytic residual hypothesis. -/

/-- Cone-returned bookkeeping facts at the constructed datum. -/
structure ResidualAtDatum
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (D : GradientMildSolutionData p u₀) where
  hT1 : D.T ≤ 1
  hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ D.M
  hball : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ D.T → ∀ y : intervalDomainPoint,
    |picardIter p u₀ n σ y| ≤ D.M

/-- **`datumIterLegs_of_cone`.**  At a gate-data cone datum `D` (gate + slice
continuity + strict positivity at mass `D.M`), build the two iterate-side legs
`DatumIterLegs` the narrowed capstone consumes. -/
def datumIterLegs_of_cone
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (u₀ : intervalDomainPoint → ℝ)
    (hu₀_pos : PositiveInitialDatum intervalDomain u₀)
    (D : GradientMildSolutionData p u₀) {A₂ : ℝ}
    (hA₂nn : 0 ≤ A₂)
    (hgate : GateCondition p D.M A₂ D.T)
    (hu₀_cont : Continuous u₀)
    (hpos : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ n σ) x)
    (hcontSlice : ∀ n : ℕ, HasContinuousSlices D.T (picardIter p u₀ n))
    (R : ResidualAtDatum p u₀ D) :
    ShenWork.Paper2.Thm11ChiZeroCoreProvider.DatumIterLegs p u₀ D :=
  -- the limit ball `|D.u s y| ≤ D.M` is the datum's own `hbound` (after `hDu`).
  have hlim_ball : ∀ (s : ℝ), 0 < s → s ≤ D.T → ∀ y : intervalDomainPoint,
      |D.u s y| ≤ D.M := D.hbound
  let HT := towerInputs_of_cone p hχ0 hα ha hb u₀ D
    D.hM.le R.hT1 hA₂nn hgate hu₀_cont
    (ShenWork.Paper2.ConeQuantBridge.positiveInitialDatum_nonneg hu₀_pos)
    R.hu₀_bound hpos hcontSlice R.hball hlim_ball
  ⟨ShenWork.IntervalPicardTowerProjection.wdataProvider_of_tower p u₀ D HT.2.2,
   ShenWork.IntervalPicardTowerProjection.hiter_cont_of_tower p u₀ HT.2.2⟩

/-- **`from_cone_construction` — unconditional bridge from the strengthened cone.** -/
theorem from_cone_construction
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    ShenWork.Paper2.Theorem_1_1 intervalDomain p :=
  ShenWork.Paper2.Thm11ChiZeroCoreProvider.paper2_theorem_1_1_chiZero_of_datumProviders
    p hχ0 ha hb hα hγ
    (fun _M_in hM_in =>
      let C :=
        ShenWork.IntervalMildPicardConeData.coneGradientMildSolutionData_exists_with_gate_data'
          p hχ0 hM_in hα
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
          hspec.2.2.2.2.2.1 n σ hσ (hσT.trans hDT.le) x hx
        have hT1 : D.T ≤ 1 := hspec.2.2.2.2.2.2.1
        have hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ D.M :=
          hspec.2.2.2.2.2.2.2.1
        have hball : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ D.T → ∀ y : intervalDomainPoint,
          |picardIter p u₀ n σ y| ≤ D.M := hspec.2.2.2.2.2.2.2.2
        let R : ResidualAtDatum p u₀ D :=
          { hT1 := hT1, hu₀_bound := hu₀_bound, hball := hball }
        ⟨D, hDT, hDu, hcontSlice, hF,
          datumIterLegs_of_cone p hχ0 hα ha.le hb.le u₀ hu₀ D hA₂nn hgate
            hu₀.admissible.2 hpos hcontSlice R⟩⟩)

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

/-- Back-compatible theorem name for the strengthened-cone bridge. -/
theorem from_cone_construction'
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    ShenWork.Paper2.Theorem_1_1 intervalDomain p :=
  from_cone_construction p hχ0 ha hb hα hγ

end ShenWork.IntervalPicardTowerSupply
