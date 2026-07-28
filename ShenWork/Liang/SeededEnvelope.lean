/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import ShenWork.Liang.GlobalDynamicsTools
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Homogeneous weak-competition envelopes started from arbitrary floors

Spatial persistence generally supplies small positive lower bounds, not the
particular half-nullcline bounds used by the canonical envelope.  This file
therefore starts the homogeneous competitive iteration from arbitrary
positive floors `ℓu, ℓv` and upper endpoints one.

The explicit hypotheses

`ℓu + α₁ ≤ 1` and `ℓv + α₂ ≤ 1`

are exactly what makes the first lower endpoints increase.  Under weak
competition, all four nested endpoints converge to the coexistence
equilibrium.  The file does not import the spatial coexistence module, so it
can be used as an acyclic input to its corridor comparison proof.
-/

open Filter Set Topology

namespace ShenWork.Liang

noncomputable section

/-- A homogeneous competitive rectangle with lower and upper endpoints. -/
structure SeededEnvelope where
  uLower : ℝ
  uUpper : ℝ
  vLower : ℝ
  vUpper : ℝ

/-- A positive subrectangle of the invariant unit square. -/
def SeededEnvelope.Valid (e : SeededEnvelope) : Prop :=
  0 < e.uLower ∧ e.uLower ≤ e.uUpper ∧ e.uUpper ≤ 1 ∧
    0 < e.vLower ∧ e.vLower ≤ e.vUpper ∧ e.vUpper ≤ 1

/-- Rectangle refinement raises lower endpoints and lowers upper endpoints. -/
def SeededEnvelopeRefines (e f : SeededEnvelope) : Prop :=
  e.uLower ≤ f.uLower ∧ f.uUpper ≤ e.uUpper ∧
    e.vLower ≤ f.vLower ∧ f.vUpper ≤ e.vUpper

/-- One homogeneous competitive-envelope step. -/
def seededEnvelopeStep
    (ρ₁ ρ₂ α₁ α₂ : ℝ) (e : SeededEnvelope) :
    SeededEnvelope where
  uLower := correctedResponse ρ₁ α₁ e.uLower e.vUpper
  uUpper := correctedResponse ρ₁ α₁ e.uUpper e.vLower
  vLower := correctedResponse ρ₂ α₂ e.vLower e.uUpper
  vUpper := correctedResponse ρ₂ α₂ e.vUpper e.uLower

/-- Initial rectangle supplied by arbitrary positive spatial floors. -/
def seededInitialEnvelope (ℓu ℓv : ℝ) : SeededEnvelope where
  uLower := ℓu
  uUpper := 1
  vLower := ℓv
  vUpper := 1

/-- A canonical admissible seed chosen below an available persistence floor
and below the corresponding weak-competition nullcline intercept. -/
def admissibleSeedFloor (α persistenceFloor : ℝ) : ℝ :=
  min (persistenceFloor / 2) ((1 - α) / 2)

/-- Every positive persistence floor under weak competition contains a
positive seed satisfying the initial-refinement inequality. -/
theorem exists_admissible_seed_floor
    {α persistenceFloor : ℝ}
    (hα : α < 1) (hfloor : 0 < persistenceFloor) :
    ∃ ℓ : ℝ,
      0 < ℓ ∧ ℓ ≤ persistenceFloor ∧ ℓ + α ≤ 1 := by
  refine ⟨admissibleSeedFloor α persistenceFloor, ?_, ?_, ?_⟩
  · unfold admissibleSeedFloor
    exact lt_min (by positivity) (by linarith)
  · unfold admissibleSeedFloor
    have hhalf :
        persistenceFloor / 2 ≤ persistenceFloor := by
      linarith
    exact (min_le_left _ _).trans hhalf
  · unfold admissibleSeedFloor
    have hseed :
        min (persistenceFloor / 2) ((1 - α) / 2) ≤
          (1 - α) / 2 :=
      min_le_right _ _
    linarith

theorem seededInitialEnvelope_valid
    {ℓu ℓv : ℝ}
    (hℓu : 0 < ℓu) (hℓu1 : ℓu ≤ 1)
    (hℓv : 0 < ℓv) (hℓv1 : ℓv ≤ 1) :
    (seededInitialEnvelope ℓu ℓv).Valid := by
  exact ⟨hℓu, hℓu1, le_rfl, hℓv, hℓv1, le_rfl⟩

/-- A valid rectangle remains valid after one favorable homogeneous step. -/
theorem seededEnvelopeStep_valid
    {ρ₁ ρ₂ α₁ α₂ : ℝ} {e : SeededEnvelope}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂)
    (he : e.Valid) :
    (seededEnvelopeStep ρ₁ ρ₂ α₁ α₂ e).Valid := by
  rcases he with ⟨hlu, hluu, huu, hlv, hlvu, huv⟩
  have hlu0 : 0 ≤ e.uLower := hlu.le
  have huu0 : 0 ≤ e.uUpper := hlu0.trans hluu
  have hlv0 : 0 ≤ e.vLower := hlv.le
  have huv0 : 0 ≤ e.vUpper := hlv0.trans hlvu
  unfold SeededEnvelope.Valid seededEnvelopeStep
  constructor
  · unfold correctedResponse
    exact div_pos (mul_pos (by linarith) hlu)
      (correctedResponse_denominator_pos hα₁ hlu0 huv0)
  constructor
  · calc
      correctedResponse ρ₁ α₁ e.uLower e.vUpper ≤
          correctedResponse ρ₁ α₁ e.uLower e.vLower :=
        correctedResponse_antitone_competitor
          (by linarith) hα₁ hlu0 hlv0 hlvu
      _ ≤ correctedResponse ρ₁ α₁ e.uUpper e.vLower :=
        correctedResponse_monotone_focal
          (by linarith) hα₁ hlu0 hluu hlv0
  constructor
  · exact correctedResponse_le_one
      (by linarith) hα₁ huu0 huu hlv0
  constructor
  · unfold correctedResponse
    exact div_pos (mul_pos (by linarith) hlv)
      (correctedResponse_denominator_pos hα₂ hlv0 huu0)
  constructor
  · calc
      correctedResponse ρ₂ α₂ e.vLower e.uUpper ≤
          correctedResponse ρ₂ α₂ e.vLower e.uLower :=
        correctedResponse_antitone_competitor
          (by linarith) hα₂ hlv0 hlu0 hluu
      _ ≤ correctedResponse ρ₂ α₂ e.vUpper e.uLower :=
        correctedResponse_monotone_focal
          (by linarith) hα₂ hlv0 hlvu hlu0
  · exact correctedResponse_le_one
      (by linarith) hα₂ huv0 huv hlu0

/-- The envelope map preserves rectangle refinement. -/
theorem seededEnvelopeStep_refines_mono
    {ρ₁ ρ₂ α₁ α₂ : ℝ} {e f : SeededEnvelope}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂)
    (he : e.Valid) (hf : f.Valid)
    (hef : SeededEnvelopeRefines e f) :
    SeededEnvelopeRefines
      (seededEnvelopeStep ρ₁ ρ₂ α₁ α₂ e)
      (seededEnvelopeStep ρ₁ ρ₂ α₁ α₂ f) := by
  rcases he with ⟨helu, heluu, _, helv, helvu, _⟩
  rcases hf with ⟨hflu, hfluu, _, hflv, hflvu, _⟩
  rcases hef with ⟨hlu, huu, hlv, huv⟩
  have helu0 := helu.le
  have helv0 := helv.le
  have hflu0 := hflu.le
  have hflv0 := hflv.le
  have heuu0 : 0 ≤ e.uUpper := helu0.trans heluu
  have hevu0 : 0 ≤ e.vUpper := helv0.trans helvu
  have hfuu0 : 0 ≤ f.uUpper := hflu0.trans hfluu
  have hfvu0 : 0 ≤ f.vUpper := hflv0.trans hflvu
  unfold SeededEnvelopeRefines seededEnvelopeStep
  constructor
  · calc
      correctedResponse ρ₁ α₁ e.uLower e.vUpper ≤
          correctedResponse ρ₁ α₁ e.uLower f.vUpper :=
        correctedResponse_antitone_competitor
          (by linarith) hα₁ helu0 hfvu0 huv
      _ ≤ correctedResponse ρ₁ α₁ f.uLower f.vUpper :=
        correctedResponse_monotone_focal
          (by linarith) hα₁ helu0 hlu hfvu0
  constructor
  · calc
      correctedResponse ρ₁ α₁ f.uUpper f.vLower ≤
          correctedResponse ρ₁ α₁ f.uUpper e.vLower :=
        correctedResponse_antitone_competitor
          (by linarith) hα₁ hfuu0 helv0 hlv
      _ ≤ correctedResponse ρ₁ α₁ e.uUpper e.vLower :=
        correctedResponse_monotone_focal
          (by linarith) hα₁ hfuu0 huu helv0
  constructor
  · calc
      correctedResponse ρ₂ α₂ e.vLower e.uUpper ≤
          correctedResponse ρ₂ α₂ e.vLower f.uUpper :=
        correctedResponse_antitone_competitor
          (by linarith) hα₂ helv0 hfuu0 huu
      _ ≤ correctedResponse ρ₂ α₂ f.vLower f.uUpper :=
        correctedResponse_monotone_focal
          (by linarith) hα₂ helv0 hlv hfuu0
  · calc
      correctedResponse ρ₂ α₂ f.vUpper f.uLower ≤
          correctedResponse ρ₂ α₂ f.vUpper e.uLower :=
        correctedResponse_antitone_competitor
          (by linarith) hα₂ hfvu0 helu0 hlu
      _ ≤ correctedResponse ρ₂ α₂ e.vUpper e.uLower :=
        correctedResponse_monotone_focal
          (by linarith) hα₂ hfvu0 huv helu0

/-- The explicit floor conditions are exactly sufficient for the first step
to refine the floor-to-one initial rectangle. -/
theorem seededInitialEnvelope_step_refines
    {ρ₁ ρ₂ α₁ α₂ ℓu ℓv : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂)
    (hℓu : 0 < ℓu) (hℓv : 0 < ℓv)
    (huFloor : ℓu + α₁ ≤ 1)
    (hvFloor : ℓv + α₂ ≤ 1) :
    SeededEnvelopeRefines
      (seededInitialEnvelope ℓu ℓv)
      (seededEnvelopeStep ρ₁ ρ₂ α₁ α₂
        (seededInitialEnvelope ℓu ℓv)) := by
  unfold SeededEnvelopeRefines seededEnvelopeStep seededInitialEnvelope
  constructor
  · exact
      (self_le_correctedResponse_iff
        hρ₁ hα₁ hℓu (by norm_num)).2
        (by simpa using huFloor)
  constructor
  · exact correctedResponse_le_one
      (by linarith) hα₁ (by norm_num) le_rfl hℓv.le
  constructor
  · exact
      (self_le_correctedResponse_iff
        hρ₂ hα₂ hℓv (by norm_num)).2
        (by simpa using hvFloor)
  · exact correctedResponse_le_one
      (by linarith) hα₂ (by norm_num) le_rfl hℓu.le

/-- Iteration of the seeded homogeneous envelope. -/
def seededEnvelopeOrbit
    (ρ₁ ρ₂ α₁ α₂ ℓu ℓv : ℝ) : ℕ → SeededEnvelope
  | 0 => seededInitialEnvelope ℓu ℓv
  | n + 1 =>
      seededEnvelopeStep ρ₁ ρ₂ α₁ α₂
        (seededEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ ℓu ℓv n)

@[simp]
theorem seededEnvelopeOrbit_zero
    (ρ₁ ρ₂ α₁ α₂ ℓu ℓv : ℝ) :
    seededEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ ℓu ℓv 0 =
      seededInitialEnvelope ℓu ℓv :=
  rfl

@[simp]
theorem seededEnvelopeOrbit_succ
    (ρ₁ ρ₂ α₁ α₂ ℓu ℓv : ℝ) (n : ℕ) :
    seededEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ ℓu ℓv (n + 1) =
      seededEnvelopeStep ρ₁ ρ₂ α₁ α₂
        (seededEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ ℓu ℓv n) :=
  rfl

theorem seededEnvelopeOrbit_valid
    {ρ₁ ρ₂ α₁ α₂ ℓu ℓv : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂)
    (hℓu : 0 < ℓu) (hℓv : 0 < ℓv)
    (huFloor : ℓu + α₁ ≤ 1)
    (hvFloor : ℓv + α₂ ≤ 1) :
    ∀ n, (seededEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ ℓu ℓv n).Valid := by
  have hℓu1 : ℓu ≤ 1 := by linarith
  have hℓv1 : ℓv ≤ 1 := by linarith
  intro n
  induction n with
  | zero =>
      exact seededInitialEnvelope_valid hℓu hℓu1 hℓv hℓv1
  | succ n ih =>
      exact seededEnvelopeStep_valid hρ₁ hρ₂ hα₁ hα₂ ih

theorem seededEnvelopeOrbit_refines_succ
    {ρ₁ ρ₂ α₁ α₂ ℓu ℓv : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂)
    (hℓu : 0 < ℓu) (hℓv : 0 < ℓv)
    (huFloor : ℓu + α₁ ≤ 1)
    (hvFloor : ℓv + α₂ ≤ 1) :
    ∀ n,
      SeededEnvelopeRefines
        (seededEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ ℓu ℓv n)
        (seededEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ ℓu ℓv (n + 1)) := by
  intro n
  induction n with
  | zero =>
      exact seededInitialEnvelope_step_refines
        hρ₁ hρ₂ hα₁ hα₂ hℓu hℓv huFloor hvFloor
  | succ n ih =>
      exact seededEnvelopeStep_refines_mono
        hρ₁ hρ₂ hα₁ hα₂
        (seededEnvelopeOrbit_valid
          hρ₁ hρ₂ hα₁ hα₂ hℓu hℓv huFloor hvFloor n)
        (seededEnvelopeOrbit_valid
          hρ₁ hρ₂ hα₁ hα₂ hℓu hℓv huFloor hvFloor (n + 1))
        ih

theorem seededEnvelopeOrbit_uLower_monotone
    {ρ₁ ρ₂ α₁ α₂ ℓu ℓv : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂)
    (hℓu : 0 < ℓu) (hℓv : 0 < ℓv)
    (huFloor : ℓu + α₁ ≤ 1)
    (hvFloor : ℓv + α₂ ≤ 1) :
    Monotone
      (fun n =>
        (seededEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ ℓu ℓv n).uLower) :=
  monotone_nat_of_le_succ fun n =>
    (seededEnvelopeOrbit_refines_succ
      hρ₁ hρ₂ hα₁ hα₂ hℓu hℓv huFloor hvFloor n).1

theorem seededEnvelopeOrbit_uUpper_antitone
    {ρ₁ ρ₂ α₁ α₂ ℓu ℓv : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂)
    (hℓu : 0 < ℓu) (hℓv : 0 < ℓv)
    (huFloor : ℓu + α₁ ≤ 1)
    (hvFloor : ℓv + α₂ ≤ 1) :
    Antitone
      (fun n =>
        (seededEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ ℓu ℓv n).uUpper) :=
  antitone_nat_of_succ_le fun n =>
    (seededEnvelopeOrbit_refines_succ
      hρ₁ hρ₂ hα₁ hα₂ hℓu hℓv huFloor hvFloor n).2.1

theorem seededEnvelopeOrbit_vLower_monotone
    {ρ₁ ρ₂ α₁ α₂ ℓu ℓv : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂)
    (hℓu : 0 < ℓu) (hℓv : 0 < ℓv)
    (huFloor : ℓu + α₁ ≤ 1)
    (hvFloor : ℓv + α₂ ≤ 1) :
    Monotone
      (fun n =>
        (seededEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ ℓu ℓv n).vLower) :=
  monotone_nat_of_le_succ fun n =>
    (seededEnvelopeOrbit_refines_succ
      hρ₁ hρ₂ hα₁ hα₂ hℓu hℓv huFloor hvFloor n).2.2.1

theorem seededEnvelopeOrbit_vUpper_antitone
    {ρ₁ ρ₂ α₁ α₂ ℓu ℓv : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂)
    (hℓu : 0 < ℓu) (hℓv : 0 < ℓv)
    (huFloor : ℓu + α₁ ≤ 1)
    (hvFloor : ℓv + α₂ ≤ 1) :
    Antitone
      (fun n =>
        (seededEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ ℓu ℓv n).vUpper) :=
  antitone_nat_of_succ_le fun n =>
    (seededEnvelopeOrbit_refines_succ
      hρ₁ hρ₂ hα₁ hα₂ hℓu hℓv huFloor hvFloor n).2.2.2

theorem seededContinuousAt_correctedResponse_pair
    {ρ α u v : ℝ} (hα : 0 ≤ α) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ContinuousAt
      (fun p : ℝ × ℝ => correctedResponse ρ α p.1 p.2) (u, v) := by
  unfold correctedResponse
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · exact ne_of_gt (correctedResponse_denominator_pos hα hu hv)

/-- Every seeded weak-competition envelope converges at all four endpoints to
the unique positive coexistence equilibrium. -/
theorem seededEnvelopeOrbit_tendsto_coexistence
    {ρ₁ ρ₂ α₁ α₂ ℓu ℓv : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hα₁0 : 0 < α₁) (hα₁1 : α₁ < 1)
    (hα₂0 : 0 < α₂) (hα₂1 : α₂ < 1)
    (hℓu : 0 < ℓu) (hℓv : 0 < ℓv)
    (huFloor : ℓu + α₁ ≤ 1)
    (hvFloor : ℓv + α₂ ≤ 1) :
    Tendsto
        (fun n =>
          (seededEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ ℓu ℓv n).uLower)
        atTop (𝓝 (coexistenceU α₁ α₂)) ∧
      Tendsto
        (fun n =>
          (seededEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ ℓu ℓv n).uUpper)
        atTop (𝓝 (coexistenceU α₁ α₂)) ∧
      Tendsto
        (fun n =>
          (seededEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ ℓu ℓv n).vLower)
        atTop (𝓝 (coexistenceV α₁ α₂)) ∧
      Tendsto
        (fun n =>
          (seededEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ ℓu ℓv n).vUpper)
        atTop (𝓝 (coexistenceV α₁ α₂)) := by
  let orbit :=
    seededEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ ℓu ℓv
  let uLowerLimit : ℝ := ⨆ n, (orbit n).uLower
  let uUpperLimit : ℝ := ⨅ n, (orbit n).uUpper
  let vLowerLimit : ℝ := ⨆ n, (orbit n).vLower
  let vUpperLimit : ℝ := ⨅ n, (orbit n).vUpper
  have hvalid : ∀ n, (orbit n).Valid := by
    exact seededEnvelopeOrbit_valid
      hρ₁ hρ₂ hα₁0.le hα₂0.le hℓu hℓv huFloor hvFloor
  have huLowerBdd :
      BddAbove (range fun n => (orbit n).uLower) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (hvalid n).2.1.trans (hvalid n).2.2.1
  have huUpperBdd :
      BddBelow (range fun n => (orbit n).uUpper) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (hvalid n).1.le.trans (hvalid n).2.1
  have hvLowerBdd :
      BddAbove (range fun n => (orbit n).vLower) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (hvalid n).2.2.2.2.1.trans
      (hvalid n).2.2.2.2.2
  have hvUpperBdd :
      BddBelow (range fun n => (orbit n).vUpper) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (hvalid n).2.2.2.1.le.trans
      (hvalid n).2.2.2.2.1
  have huLowerMono :
      Monotone (fun n => (orbit n).uLower) := by
    exact seededEnvelopeOrbit_uLower_monotone
      hρ₁ hρ₂ hα₁0.le hα₂0.le
      hℓu hℓv huFloor hvFloor
  have huUpperAnti :
      Antitone (fun n => (orbit n).uUpper) := by
    exact seededEnvelopeOrbit_uUpper_antitone
      hρ₁ hρ₂ hα₁0.le hα₂0.le
      hℓu hℓv huFloor hvFloor
  have hvLowerMono :
      Monotone (fun n => (orbit n).vLower) := by
    exact seededEnvelopeOrbit_vLower_monotone
      hρ₁ hρ₂ hα₁0.le hα₂0.le
      hℓu hℓv huFloor hvFloor
  have hvUpperAnti :
      Antitone (fun n => (orbit n).vUpper) := by
    exact seededEnvelopeOrbit_vUpper_antitone
      hρ₁ hρ₂ hα₁0.le hα₂0.le
      hℓu hℓv huFloor hvFloor
  have huLowerTendsto :
      Tendsto (fun n => (orbit n).uLower)
        atTop (𝓝 uLowerLimit) :=
    tendsto_atTop_ciSup huLowerMono huLowerBdd
  have huUpperTendsto :
      Tendsto (fun n => (orbit n).uUpper)
        atTop (𝓝 uUpperLimit) :=
    tendsto_atTop_ciInf huUpperAnti huUpperBdd
  have hvLowerTendsto :
      Tendsto (fun n => (orbit n).vLower)
        atTop (𝓝 vLowerLimit) :=
    tendsto_atTop_ciSup hvLowerMono hvLowerBdd
  have hvUpperTendsto :
      Tendsto (fun n => (orbit n).vUpper)
        atTop (𝓝 vUpperLimit) :=
    tendsto_atTop_ciInf hvUpperAnti hvUpperBdd
  have huLowerPos : 0 < uLowerLimit := by
    have hinit : 0 < (orbit 0).uLower :=
      (hvalid 0).1
    have hle : (orbit 0).uLower ≤ uLowerLimit :=
      ge_of_tendsto' huLowerTendsto fun n =>
        huLowerMono (Nat.zero_le n)
    exact hinit.trans_le hle
  have hvLowerPos : 0 < vLowerLimit := by
    have hinit : 0 < (orbit 0).vLower :=
      (hvalid 0).2.2.2.1
    have hle : (orbit 0).vLower ≤ vLowerLimit :=
      ge_of_tendsto' hvLowerTendsto fun n =>
        hvLowerMono (Nat.zero_le n)
    exact hinit.trans_le hle
  have huUpperNonneg : 0 ≤ uUpperLimit :=
    ge_of_tendsto' huUpperTendsto fun n =>
      (hvalid n).1.le.trans (hvalid n).2.1
  have hvUpperNonneg : 0 ≤ vUpperLimit :=
    ge_of_tendsto' hvUpperTendsto fun n =>
      (hvalid n).2.2.2.1.le.trans
        (hvalid n).2.2.2.2.1
  have huOrder : uLowerLimit ≤ uUpperLimit :=
    le_of_tendsto_of_tendsto huLowerTendsto huUpperTendsto
      (Eventually.of_forall fun n => (hvalid n).2.1)
  have hvOrder : vLowerLimit ≤ vUpperLimit :=
    le_of_tendsto_of_tendsto hvLowerTendsto hvUpperTendsto
      (Eventually.of_forall fun n => (hvalid n).2.2.2.2.1)
  have huUpperPos : 0 < uUpperLimit :=
    huLowerPos.trans_le huOrder
  have hvUpperPos : 0 < vUpperLimit :=
    hvLowerPos.trans_le hvOrder
  have huLowerPair :
      Tendsto
        (fun n => ((orbit n).uLower, (orbit n).vUpper))
        atTop (𝓝 (uLowerLimit, vUpperLimit)) := by
    rw [nhds_prod_eq]
    exact huLowerTendsto.prodMk hvUpperTendsto
  have huUpperPair :
      Tendsto
        (fun n => ((orbit n).uUpper, (orbit n).vLower))
        atTop (𝓝 (uUpperLimit, vLowerLimit)) := by
    rw [nhds_prod_eq]
    exact huUpperTendsto.prodMk hvLowerTendsto
  have hvLowerPair :
      Tendsto
        (fun n => ((orbit n).vLower, (orbit n).uUpper))
        atTop (𝓝 (vLowerLimit, uUpperLimit)) := by
    rw [nhds_prod_eq]
    exact hvLowerTendsto.prodMk huUpperTendsto
  have hvUpperPair :
      Tendsto
        (fun n => ((orbit n).vUpper, (orbit n).uLower))
        atTop (𝓝 (vUpperLimit, uLowerLimit)) := by
    rw [nhds_prod_eq]
    exact hvUpperTendsto.prodMk huLowerTendsto
  have huLowerResponse :
      Tendsto
        (fun n =>
          correctedResponse ρ₁ α₁
            (orbit n).uLower (orbit n).vUpper)
        atTop
        (𝓝
          (correctedResponse
            ρ₁ α₁ uLowerLimit vUpperLimit)) :=
    (seededContinuousAt_correctedResponse_pair
      hα₁0.le huLowerPos.le hvUpperNonneg).tendsto.comp
        huLowerPair
  have huUpperResponse :
      Tendsto
        (fun n =>
          correctedResponse ρ₁ α₁
            (orbit n).uUpper (orbit n).vLower)
        atTop
        (𝓝
          (correctedResponse
            ρ₁ α₁ uUpperLimit vLowerLimit)) :=
    (seededContinuousAt_correctedResponse_pair
      hα₁0.le huUpperNonneg hvLowerPos.le).tendsto.comp
        huUpperPair
  have hvLowerResponse :
      Tendsto
        (fun n =>
          correctedResponse ρ₂ α₂
            (orbit n).vLower (orbit n).uUpper)
        atTop
        (𝓝
          (correctedResponse
            ρ₂ α₂ vLowerLimit uUpperLimit)) :=
    (seededContinuousAt_correctedResponse_pair
      hα₂0.le hvLowerPos.le huUpperNonneg).tendsto.comp
        hvLowerPair
  have hvUpperResponse :
      Tendsto
        (fun n =>
          correctedResponse ρ₂ α₂
            (orbit n).vUpper (orbit n).uLower)
        atTop
        (𝓝
          (correctedResponse
            ρ₂ α₂ vUpperLimit uLowerLimit)) :=
    (seededContinuousAt_correctedResponse_pair
      hα₂0.le hvUpperNonneg huLowerPos.le).tendsto.comp
        hvUpperPair
  have huLowerFixed :
      uLowerLimit =
        correctedResponse ρ₁ α₁ uLowerLimit vUpperLimit := by
    apply tendsto_nhds_unique
      (huLowerTendsto.comp (tendsto_add_atTop_nat 1))
    simpa [orbit, seededEnvelopeOrbit_succ,
      seededEnvelopeStep] using huLowerResponse
  have huUpperFixed :
      uUpperLimit =
        correctedResponse ρ₁ α₁ uUpperLimit vLowerLimit := by
    apply tendsto_nhds_unique
      (huUpperTendsto.comp (tendsto_add_atTop_nat 1))
    simpa [orbit, seededEnvelopeOrbit_succ,
      seededEnvelopeStep] using huUpperResponse
  have hvLowerFixed :
      vLowerLimit =
        correctedResponse ρ₂ α₂ vLowerLimit uUpperLimit := by
    apply tendsto_nhds_unique
      (hvLowerTendsto.comp (tendsto_add_atTop_nat 1))
    simpa [orbit, seededEnvelopeOrbit_succ,
      seededEnvelopeStep] using hvLowerResponse
  have hvUpperFixed :
      vUpperLimit =
        correctedResponse ρ₂ α₂ vUpperLimit uLowerLimit := by
    apply tendsto_nhds_unique
      (hvUpperTendsto.comp (tendsto_add_atTop_nat 1))
    simpa [orbit, seededEnvelopeOrbit_succ,
      seededEnvelopeStep] using hvUpperResponse
  have huUpperNull :
      uUpperLimit + α₁ * vLowerLimit ≤ 1 :=
    (self_le_correctedResponse_iff
      hρ₁ hα₁0.le huUpperPos hvLowerPos.le).1
      huUpperFixed.le
  have huLowerNull :
      1 ≤ uLowerLimit + α₁ * vUpperLimit :=
    (correctedResponse_le_self_iff
      hρ₁ hα₁0.le huLowerPos hvUpperNonneg).1
      huLowerFixed.ge
  have hvUpperNull :
      vUpperLimit + α₂ * uLowerLimit ≤ 1 :=
    (self_le_correctedResponse_iff
      hρ₂ hα₂0.le hvUpperPos huLowerPos.le).1
      hvUpperFixed.le
  have hvLowerNull :
      1 ≤ vLowerLimit + α₂ * uUpperLimit :=
    (correctedResponse_le_self_iff
      hρ₂ hα₂0.le hvLowerPos huUpperNonneg).1
      hvLowerFixed.ge
  obtain ⟨huLowerEq, huUpperEq, hvLowerEq, hvUpperEq⟩ :=
    weakCompetition_rectangle_squeeze
      hα₁0 hα₁1 hα₂0 hα₂1
      huOrder hvOrder
      huUpperNull huLowerNull hvUpperNull hvLowerNull
  constructor
  · simpa [orbit, huLowerEq] using huLowerTendsto
  constructor
  · simpa [orbit, huUpperEq] using huUpperTendsto
  constructor
  · simpa [orbit, hvLowerEq] using hvLowerTendsto
  · simpa [orbit, hvUpperEq] using hvUpperTendsto

section AxiomAudit

#print axioms seededInitialEnvelope_step_refines
#print axioms seededEnvelopeOrbit_refines_succ
#print axioms seededEnvelopeOrbit_tendsto_coexistence

end AxiomAudit

end

end ShenWork.Liang
