/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import ShenWork.Liang.MultistepPersistence
import ShenWork.Liang.FiniteBlockSpreading
import ShenWork.Liang.MovingCorridor
import ShenWork.Liang.StateSpace

/-!
# Intermediate-speed exclusion

This file closes the nonlinear part of the corrected intermediate-speed
theorem under two explicit, checkable kernel hypotheses.

1. A quantitative minorization of the kernel supplies a positive floor on an
   expanding interval; this was proved in `ScalarPersistence`.
2. Compact support supplies a finite domain of dependence.  Starting from
   that positive floor, repeated lower comparison with a Beverton--Holt orbit
   forces the fast component to its carrying level.  If the slow component is
   uniformly small, the lower carrying level is `1 - αδ`, which tends to one
   with the competitor bound `δ`.

The compact-support condition is stronger than the moment assumptions in the
proposal.  It is used here because it yields a complete proof without hiding a
scalar spreading theorem inside an assumption.
-/

open Filter MeasureTheory Set Topology
open scoped BoundedContinuousFunction

namespace ShenWork.Liang

noncomputable section

/-! ## Full-mass lower comparison for a compactly supported kernel -/

/-- The interval left after eroding `[L,R]` by `j` kernel radii at each end. -/
def erodedInterval (L R radius : ℝ) (j : ℕ) : Set ℝ :=
  Set.Icc
    (L + (j : ℝ) * radius)
    (R - (j : ℝ) * radius)

@[simp]
theorem erodedInterval_zero (L R radius : ℝ) :
    erodedInterval L R radius 0 = Set.Icc L R := by
  simp [erodedInterval]

/-- One full probability-kernel step dominates the constant perturbed
Beverton--Holt response whenever all points in its finite domain of dependence
have the required floor. -/
theorem heterogeneousCorrectedStep_ge_compactSupport_floor
    {K ρ focal competitor : ℝ → ℝ}
    {α c x radius ρ₀ δ z : ℝ} {n : ℕ}
    (hKint : Integrable K) (hKcont : Continuous K)
    (hKnonneg : ∀ s, 0 ≤ K s) (hKmass : ∫ s, K s = 1)
    (hKsupport : ∀ s, radius < |s| → K s = 0)
    (hρcont : Continuous ρ) (hρlow : ∀ s, -1 < ρ s)
    (hα : 0 ≤ α)
    (hfocal_cont : Continuous focal)
    (hfocal_nonneg : ∀ y, 0 ≤ focal y)
    (hfocal_le_one : ∀ y, focal y ≤ 1)
    (hcompetitor_cont : Continuous competitor)
    (hcompetitor_nonneg : ∀ y, 0 ≤ competitor y)
    (hρ₀ : 0 ≤ ρ₀) (hz : 0 ≤ z) (hδ : 0 ≤ δ)
    (hsubunit : z + α * δ ≤ 1)
    (hlocal : ∀ y, |x - y| ≤ radius →
      z ≤ focal y ∧ competitor y ≤ δ ∧
        ρ₀ ≤ ρ (y - c * (n : ℝ))) :
    correctedResponse ρ₀ α z δ ≤
      heterogeneousCorrectedStep K ρ α c n focal competitor x := by
  let A : ℝ := correctedResponse ρ₀ α z δ
  let f : ℝ → ℝ := fun y =>
    K (x - y) *
      correctedResponse (ρ (y - c * (n : ℝ))) α
        (focal y) (competitor y)
  have hA : 0 ≤ A :=
    correctedResponse_nonneg (by linarith) hα hz hδ
  have hleft : Integrable (fun y => K (x - y) * A) :=
    (hKint.comp_sub_left x).mul_const A
  have hright : Integrable f :=
    heterogeneousCorrectedIntegrable
      hKint hKcont hρcont hρlow hα
      hfocal_cont hfocal_nonneg hfocal_le_one
      hcompetitor_cont hcompetitor_nonneg
  have hpoint :
      ∀ y, K (x - y) * A ≤ f y := by
    intro y
    by_cases hxy : |x - y| ≤ radius
    · have hs := hlocal y hxy
      exact mul_le_mul_of_nonneg_left
        (correctedResponse_ge_perturbed_floor
          hρ₀ hs.2.2 hα hz hs.1
          (hcompetitor_nonneg y) hs.2.1 hsubunit)
        (hKnonneg _)
    · have hout : radius < |x - y| := lt_of_not_ge hxy
      dsimp [f]
      rw [hKsupport _ hout, zero_mul, zero_mul]
  unfold heterogeneousCorrectedStep ShenWork.Analysis.dispersal
  calc
    correctedResponse ρ₀ α z δ =
        A * ∫ y, K (x - y) := by
      rw [integral_sub_left_eq_self K (volume : Measure ℝ) x, hKmass, mul_one]
    _ = ∫ y, K (x - y) * A := by
      rw [integral_mul_const]
      ring
    _ ≤ ∫ y, f y := integral_mono hleft hright hpoint

/-- Eroding by one more radius guarantees that every kernel predecessor lies
in the preceding eroded interval. -/
theorem predecessor_mem_erodedInterval
    {L R radius x y : ℝ} {j : ℕ}
    (hx : x ∈ erodedInterval L R radius (j + 1))
    (hxy : |x - y| ≤ radius) :
    y ∈ erodedInterval L R radius j := by
  have hdist := (abs_le.mp hxy)
  constructor
  · dsimp [erodedInterval] at hx ⊢
    push_cast at hx
    nlinarith [hx.1, hdist.1]
  · dsimp [erodedInterval] at hx ⊢
    push_cast at hx
    nlinarith [hx.2, hdist.2]

/-! ## Finite-horizon Beverton--Holt lower iteration -/

theorem one_lt_perturbedMultiplier
    {ρ α δ : ℝ} (hρ : 0 < ρ) (hα : 0 ≤ α)
    (hδ : 0 ≤ δ) (hsmall : α * δ < 1) :
    1 < perturbedMultiplier ρ α δ := by
  have hden : 0 < 1 + ρ * α * δ := by positivity
  unfold perturbedMultiplier
  apply (lt_div_iff₀ hden).2
  nlinarith [mul_pos hρ (sub_pos.mpr hsmall)]

/-- The exact finite-horizon lower sandwich.  Its hypotheses concern only the
IDE recurrence, finite kernel support, and pointwise environmental/competitor
bounds on the eroded intervals. -/
theorem bhOrbit_le_on_erodedInterval
    {focal competitor : ℕ → ℝ → ℝ}
    {Kfun ρfun : ℝ → ℝ}
    {α c radius ρ₀ δ seed L R : ℝ} {N horizon : ℕ}
    (horbit :
      ∀ j x,
        focal (N + j + 1) x =
          heterogeneousCorrectedStep Kfun ρfun α c (N + j)
            (focal (N + j)) (competitor (N + j)) x)
    (hKint : Integrable Kfun) (hKcont : Continuous Kfun)
    (hKnonneg : ∀ s, 0 ≤ Kfun s) (hKmass : ∫ s, Kfun s = 1)
    (hKsupport : ∀ s, radius < |s| → Kfun s = 0)
    (hρcont : Continuous ρfun) (hρlow : ∀ s, -1 < ρfun s)
    (hα : 0 ≤ α)
    (hfocal_cont : ∀ n, Continuous (focal n))
    (hfocal_nonneg : ∀ n y, 0 ≤ focal n y)
    (hfocal_le_one : ∀ n y, focal n y ≤ 1)
    (hcompetitor_cont : ∀ n, Continuous (competitor n))
    (hcompetitor_nonneg : ∀ n y, 0 ≤ competitor n y)
    (hρ₀ : 0 < ρ₀) (hδ : 0 ≤ δ) (hsmall : α * δ < 1)
    (hseed_pos : 0 < seed)
    (hseed_carrying : seed ≤ perturbedCarrying α δ)
    (hseed : ∀ y ∈ Set.Icc L R, seed ≤ focal N y)
    (hcompetitor :
      ∀ (j : ℕ) (y : ℝ),
        j ≤ horizon →
        y ∈ erodedInterval L R radius j →
          competitor (N + j) y ≤ δ)
    (henvironment :
      ∀ (j : ℕ) (y : ℝ),
        j ≤ horizon →
        y ∈ erodedInterval L R radius j →
          ρ₀ ≤ ρfun (y - c * ((N + j : ℕ) : ℝ))) :
    ∀ (j : ℕ) (x : ℝ),
      j ≤ horizon →
      x ∈ erodedInterval L R radius j →
        bhOrbit (perturbedMultiplier ρ₀ α δ)
            (perturbedCarrying α δ) seed j ≤
          focal (N + j) x := by
  have hq : 0 < perturbedCarrying α δ := by
    unfold perturbedCarrying
    linarith
  have hr : 1 < perturbedMultiplier ρ₀ α δ :=
    one_lt_perturbedMultiplier hρ₀ hα hδ hsmall
  intro j
  induction j with
  | zero =>
      intro x _hjhorizon hx
      rw [erodedInterval_zero] at hx
      simpa using hseed x hx
  | succ j ih =>
      intro x hjhorizon hx
      have hjhorizon : j ≤ horizon := by omega
      rw [show N + (j + 1) = N + j + 1 by omega, horbit j x]
      rw [bhOrbit_succ]
      have hzj : 0 ≤
          bhOrbit (perturbedMultiplier ρ₀ α δ)
            (perturbedCarrying α δ) seed j :=
        (bhOrbit_pos hr hq hseed_pos j).le
      have hzjq :
          bhOrbit (perturbedMultiplier ρ₀ α δ)
              (perturbedCarrying α δ) seed j ≤
            perturbedCarrying α δ :=
        bhOrbit_le_carrying hr hq hseed_pos.le hseed_carrying j
      have hden : 1 + ρ₀ * α * δ ≠ 0 := by positivity
      have hcarry : perturbedCarrying α δ ≠ 0 := hq.ne'
      have horig :
          1 + ρ₀ *
            (bhOrbit (perturbedMultiplier ρ₀ α δ)
                (perturbedCarrying α δ) seed j + α * δ) ≠ 0 := by
        positivity
      rw [← correctedResponse_eq_bhMap hρ₀.le hden hcarry horig]
      apply heterogeneousCorrectedStep_ge_compactSupport_floor
        hKint hKcont hKnonneg hKmass hKsupport
        hρcont hρlow hα
        (hfocal_cont _) (hfocal_nonneg _) (hfocal_le_one _)
        (hcompetitor_cont _) (hcompetitor_nonneg _)
        hρ₀.le hzj hδ
      · unfold perturbedCarrying at hzjq
        change
          bhOrbit (perturbedMultiplier ρ₀ α δ)
              (1 - α * δ) seed j + α * δ ≤ 1
        linarith
      · intro y hxy
        have hy : y ∈ erodedInterval L R radius j :=
          predecessor_mem_erodedInterval hx hxy
        exact
          ⟨ih y hjhorizon hy,
            hcompetitor j y hjhorizon hy,
            henvironment j y hjhorizon hy⟩

/-! ## Recovery behind an attenuated front -/

/-- An attenuated floor propagated for `k` generations can be recovered by
`P * k` subsequent full-mass steps.  This is the spatial counterpart of
`bhOrbit_recovers_pow_seed`.

The theorem is deliberately stated on the exact eroded interval.  Corridor
geometry is handled separately, so the analytic block condition
`A * r ^ P > 1` is not mixed with affine endpoint arithmetic. -/
theorem bhOrbit_pow_seed_le_after_attenuated_front
    {focal competitor : ℕ → ℝ → ℝ}
    {Kfun ρfun : ℝ → ℝ}
    {α c radius ρtransport δtransport ρrecover δrecover seed A
      L R a b θ : ℝ}
    {N P k : ℕ}
    (hstep :
      ∀ n x,
        focal (n + 1) x =
          heterogeneousCorrectedStep Kfun ρfun α c n
            (focal n) (competitor n) x)
    (hKint : Integrable Kfun) (hKcont : Continuous Kfun)
    (hKnonneg : ∀ s, 0 ≤ Kfun s) (hKmass : ∫ s, Kfun s = 1)
    (hKsupport : ∀ s, radius < |s| → Kfun s = 0)
    (hρcont : Continuous ρfun) (hρlow : ∀ s, -1 < ρfun s)
    (hα : 0 ≤ α)
    (hfocal_cont : ∀ n, Continuous (focal n))
    (hfocal_nonneg : ∀ n y, 0 ≤ focal n y)
    (hfocal_le_one : ∀ n y, focal n y ≤ 1)
    (hcompetitor_cont : ∀ n, Continuous (competitor n))
    (hcompetitor_nonneg : ∀ n y, 0 ≤ competitor n y)
    (hA0 : 0 < A) (hA1 : A ≤ 1)
    (hρtransport : 0 < ρtransport)
    (hδtransport : 0 ≤ δtransport)
    (hsmall_transport : α * δtransport < 1)
    (hseed : 0 < seed)
    (hseed_transport :
      seed ≤ perturbedCarrying α δtransport)
    (hfront :
      ∀ (j : ℕ) (y : ℝ),
        y ∈ expandingSeedInterval L R a b θ j →
          attenuatedFloor A ρtransport α δtransport seed j ≤
            focal (N + j) y)
    (hρrecover : 0 < ρrecover)
    (hδrecover : 0 ≤ δrecover)
    (hδorder : δrecover ≤ δtransport)
    (hcompetitor :
      ∀ (j : ℕ) (y : ℝ),
        j ≤ P * k →
        y ∈ erodedInterval
          (L + (a + θ) * (k : ℝ))
          (R + (b - θ) * (k : ℝ))
          radius j →
        competitor (N + k + j) y ≤ δrecover)
    (henvironment :
      ∀ (j : ℕ) (y : ℝ),
        j ≤ P * k →
        y ∈ erodedInterval
          (L + (a + θ) * (k : ℝ))
          (R + (b - θ) * (k : ℝ))
          radius j →
        ρrecover ≤ ρfun (y - c * ((N + k + j : ℕ) : ℝ))) :
    ∀ x ∈ erodedInterval
        (L + (a + θ) * (k : ℝ))
        (R + (b - θ) * (k : ℝ))
        radius (P * k),
      bhOrbit (perturbedMultiplier ρrecover α δrecover)
          (perturbedCarrying α δrecover) (A ^ k * seed) (P * k) ≤
        focal (N + k + P * k) x := by
  have hsmall_recover : α * δrecover < 1 := by
    have hmul :
        α * δrecover ≤ α * δtransport :=
      mul_le_mul_of_nonneg_left hδorder hα
    exact hmul.trans_lt hsmall_transport
  have hqrecover : 0 < perturbedCarrying α δrecover := by
    unfold perturbedCarrying
    linarith
  have hpowseed_pos : 0 < A ^ k * seed :=
    mul_pos (pow_pos hA0 k) hseed
  have hpowA_le : A ^ k ≤ 1 :=
    pow_le_one₀ hA0.le hA1
  have hseed_recover :
      A ^ k * seed ≤ perturbedCarrying α δrecover := by
    have hcarry_order :
        perturbedCarrying α δtransport ≤
          perturbedCarrying α δrecover := by
      unfold perturbedCarrying
      have := mul_le_mul_of_nonneg_left hδorder hα
      linarith
    calc
      A ^ k * seed ≤ 1 * seed :=
        mul_le_mul_of_nonneg_right hpowA_le hseed.le
      _ ≤ perturbedCarrying α δtransport := by
        simpa using hseed_transport
      _ ≤ perturbedCarrying α δrecover := hcarry_order
  have htransport_floor :
      A ^ k * seed ≤
        attenuatedFloor A ρtransport α δtransport seed k :=
    pow_mul_seed_le_attenuatedFloor
      hA0.le hA1 hρtransport hα hδtransport
      hsmall_transport hseed.le hseed_transport k
  intro x hx
  apply bhOrbit_le_on_erodedInterval
    (N := N + k) (horizon := P * k)
    (L := L + (a + θ) * (k : ℝ))
    (R := R + (b - θ) * (k : ℝ))
    (Kfun := Kfun) (ρfun := ρfun)
    (α := α) (c := c) (radius := radius)
    (ρ₀ := ρrecover) (δ := δrecover)
    (seed := A ^ k * seed)
  · intro j y
    simpa [Nat.add_assoc] using hstep (N + k + j) y
  · exact hKint
  · exact hKcont
  · exact hKnonneg
  · exact hKmass
  · exact hKsupport
  · exact hρcont
  · exact hρlow
  · exact hα
  · exact hfocal_cont
  · exact hfocal_nonneg
  · exact hfocal_le_one
  · exact hcompetitor_cont
  · exact hcompetitor_nonneg
  · exact hρrecover
  · exact hδrecover
  · exact hsmall_recover
  · exact hpowseed_pos
  · exact hseed_recover
  · intro y hy
    apply htransport_floor.trans
    apply hfront k y
    simpa [expandingSeedInterval] using hy
  · exact hcompetitor
  · exact henvironment
  · exact le_rfl
  · exact hx

/-- Under the block-growth condition, the lower bound furnished by the
previous theorem approaches the recovery carrying level uniformly over its
whole eroded interval. -/
theorem eventually_carrying_minus_lt_after_attenuated_front
    {focal competitor : ℕ → ℝ → ℝ}
    {Kfun ρfun : ℝ → ℝ}
    {α c radius ρtransport δtransport ρrecover δrecover seed A
      L R a b θ η : ℝ}
    {N P Kpre : ℕ}
    (hstep :
      ∀ n x,
        focal (n + 1) x =
          heterogeneousCorrectedStep Kfun ρfun α c n
            (focal n) (competitor n) x)
    (hKint : Integrable Kfun) (hKcont : Continuous Kfun)
    (hKnonneg : ∀ s, 0 ≤ Kfun s) (hKmass : ∫ s, Kfun s = 1)
    (hKsupport : ∀ s, radius < |s| → Kfun s = 0)
    (hρcont : Continuous ρfun) (hρlow : ∀ s, -1 < ρfun s)
    (hα : 0 ≤ α)
    (hfocal_cont : ∀ n, Continuous (focal n))
    (hfocal_nonneg : ∀ n y, 0 ≤ focal n y)
    (hfocal_le_one : ∀ n y, focal n y ≤ 1)
    (hcompetitor_cont : ∀ n, Continuous (competitor n))
    (hcompetitor_nonneg : ∀ n y, 0 ≤ competitor n y)
    (hA0 : 0 < A) (hA1 : A ≤ 1)
    (hρtransport : 0 < ρtransport)
    (hδtransport : 0 ≤ δtransport)
    (hsmall_transport : α * δtransport < 1)
    (hseed : 0 < seed)
    (hseed_transport :
      seed ≤ perturbedCarrying α δtransport)
    (hfront :
      ∀ (j : ℕ) (y : ℝ),
        y ∈ expandingSeedInterval L R a b θ j →
          attenuatedFloor A ρtransport α δtransport seed j ≤
            focal (N + j) y)
    (hρrecover : 0 < ρrecover)
    (hδrecover : 0 ≤ δrecover)
    (hδorder : δrecover ≤ δtransport)
    (hcompetitor :
      ∀ (k j : ℕ) (y : ℝ),
        Kpre ≤ k →
        j ≤ P * k →
        y ∈ erodedInterval
          (L + (a + θ) * (k : ℝ))
          (R + (b - θ) * (k : ℝ))
          radius j →
        competitor (N + k + j) y ≤ δrecover)
    (henvironment :
      ∀ (k j : ℕ) (y : ℝ),
        Kpre ≤ k →
        j ≤ P * k →
        y ∈ erodedInterval
          (L + (a + θ) * (k : ℝ))
          (R + (b - θ) * (k : ℝ))
          radius j →
        ρrecover ≤ ρfun (y - c * ((N + k + j : ℕ) : ℝ)))
    (hgrowth :
      1 < A * perturbedMultiplier ρrecover α δrecover ^ P)
    (hη : 0 < η) :
    ∃ K, ∀ (k : ℕ), K ≤ k →
      ∀ x ∈ erodedInterval
          (L + (a + θ) * (k : ℝ))
          (R + (b - θ) * (k : ℝ))
          radius (P * k),
        perturbedCarrying α δrecover - η <
          focal (N + k + P * k) x := by
  have hsmall_recover : α * δrecover < 1 := by
    have hmul :
        α * δrecover ≤ α * δtransport :=
      mul_le_mul_of_nonneg_left hδorder hα
    exact hmul.trans_lt hsmall_transport
  have hqrecover : 0 < perturbedCarrying α δrecover := by
    unfold perturbedCarrying
    linarith
  have hrrecover :
      1 < perturbedMultiplier ρrecover α δrecover :=
    one_lt_perturbedMultiplier
      hρrecover hα hδrecover hsmall_recover
  have hlimit :=
    bhOrbit_recovers_pow_seed
      hA0 hA1 hrrecover hqrecover hseed
      (hseed_transport.trans <| by
        unfold perturbedCarrying
        have := mul_le_mul_of_nonneg_left hδorder hα
        linarith)
      hgrowth
  have hevent :
      ∀ᶠ k : ℕ in atTop,
        perturbedCarrying α δrecover - η <
          bhOrbit (perturbedMultiplier ρrecover α δrecover)
            (perturbedCarrying α δrecover) (A ^ k * seed) (P * k) :=
    (tendsto_order.1 hlimit).1
      (perturbedCarrying α δrecover - η) (by linarith)
  rcases eventually_atTop.1 hevent with ⟨K, hK⟩
  refine ⟨max K Kpre, ?_⟩
  intro k hk x hx
  have hKk : K ≤ k := le_trans (le_max_left _ _) hk
  have hprek : Kpre ≤ k := le_trans (le_max_right _ _) hk
  exact (hK k hKk).trans_le <|
    bhOrbit_pow_seed_le_after_attenuated_front
      hstep hKint hKcont hKnonneg hKmass hKsupport
      hρcont hρlow hα
      hfocal_cont hfocal_nonneg hfocal_le_one
      hcompetitor_cont hcompetitor_nonneg
      hA0 hA1 hρtransport hδtransport hsmall_transport
      hseed hseed_transport hfront
      hρrecover hδrecover hδorder
      (fun j y hj hy => hcompetitor k j y hprek hj hy)
      (fun j y hj hy => henvironment k j y hprek hj hy)
      x hx

/-! ## Corridor geometry for a fixed finite iteration horizon -/

/-- A target corridor with a strictly larger margin is eventually contained
in the `k`-fold erosion of the wider corridor at the earlier generation. -/
theorem eventually_targetCorridor_subset_eroded
    {c front εwide εtarget radius : ℝ} {k : ℕ}
    (hgap : εwide < εtarget) :
    ∀ᶠ n : ℕ in atTop,
      favorableCorridor c front εtarget (n + k) ⊆
        erodedInterval
          ((c + εwide) * (n : ℝ))
          ((front - εwide) * (n : ℝ))
          radius k := by
  have hgappos : 0 < εtarget - εwide := sub_pos.mpr hgap
  have htend :
      Tendsto (fun n : ℕ => (εtarget - εwide) * (n : ℝ))
        atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hgappos).2
      tendsto_natCast_atTop_atTop
  have hleft :
      ∀ᶠ n : ℕ in atTop,
        (k : ℝ) * radius - (c + εtarget) * (k : ℝ) ≤
          (εtarget - εwide) * (n : ℝ) :=
    htend.eventually (eventually_ge_atTop _)
  have hright :
      ∀ᶠ n : ℕ in atTop,
        (front - εtarget) * (k : ℝ) + (k : ℝ) * radius ≤
          (εtarget - εwide) * (n : ℝ) :=
    htend.eventually (eventually_ge_atTop _)
  filter_upwards [hleft, hright] with n hnleft hnright
  intro x hx
  constructor
  · dsimp [favorableCorridor, erodedInterval] at hx ⊢
    push_cast at hx
    nlinarith [hx.1]
  · dsimp [favorableCorridor, erodedInterval] at hx ⊢
    push_cast at hx
    nlinarith [hx.2]

/-- Uniform finite-horizon version of
`eventually_targetCorridor_subset_eroded`. -/
theorem eventually_targetCorridor_subset_eroded_upTo
    {c front εwide εtarget radius : ℝ} {P : ℕ}
    (hgap : εwide < εtarget) (hradius : 0 ≤ radius) :
    ∀ᶠ n : ℕ in atTop,
      ∀ j ≤ P,
        favorableCorridor c front εtarget (n + j) ⊆
          erodedInterval
            ((c + εwide) * (n : ℝ))
            ((front - εwide) * (n : ℝ))
            radius j := by
  have hgappos : 0 < εtarget - εwide := sub_pos.mpr hgap
  let Cleft : ℝ :=
    (P : ℝ) * (radius + |c + εtarget|)
  let Cright : ℝ :=
    (P : ℝ) * (radius + |front - εtarget|)
  have htend :
      Tendsto (fun n : ℕ => (εtarget - εwide) * (n : ℝ))
        atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hgappos).2
      tendsto_natCast_atTop_atTop
  have hleft :
      ∀ᶠ n : ℕ in atTop,
        Cleft ≤ (εtarget - εwide) * (n : ℝ) :=
    htend.eventually (eventually_ge_atTop _)
  have hright :
      ∀ᶠ n : ℕ in atTop,
        Cright ≤ (εtarget - εwide) * (n : ℝ) :=
    htend.eventually (eventually_ge_atTop _)
  filter_upwards [hleft, hright] with n hnleft hnright
  intro j hj x hx
  have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hjP : (j : ℝ) ≤ (P : ℝ) := by exact_mod_cast hj
  have habsleft_neg : -(c + εtarget) ≤ |c + εtarget| :=
    neg_le_abs _
  have habsright : front - εtarget ≤ |front - εtarget| :=
    le_abs_self _
  have hleftCost :
      (j : ℝ) * radius - (c + εtarget) * (j : ℝ) ≤ Cleft := by
    dsimp [Cleft]
    have hfactor :
        radius - (c + εtarget) ≤ radius + |c + εtarget| := by
      linarith
    have hnonneg : 0 ≤ radius + |c + εtarget| := by positivity
    calc
      (j : ℝ) * radius - (c + εtarget) * (j : ℝ) =
          (j : ℝ) * (radius - (c + εtarget)) := by ring
      _ ≤ (j : ℝ) * (radius + |c + εtarget|) :=
        mul_le_mul_of_nonneg_left hfactor hj0
      _ ≤ (P : ℝ) * (radius + |c + εtarget|) :=
        mul_le_mul_of_nonneg_right hjP hnonneg
  have hrightCost :
      (front - εtarget) * (j : ℝ) +
          (j : ℝ) * radius ≤ Cright := by
    dsimp [Cright]
    have hfactor :
        front - εtarget + radius ≤
          radius + |front - εtarget| := by
      linarith
    have hnonneg : 0 ≤ radius + |front - εtarget| := by positivity
    calc
      (front - εtarget) * (j : ℝ) +
          (j : ℝ) * radius =
          (j : ℝ) * (front - εtarget + radius) := by ring
      _ ≤ (j : ℝ) * (radius + |front - εtarget|) :=
        mul_le_mul_of_nonneg_left hfactor hj0
      _ ≤ (P : ℝ) * (radius + |front - εtarget|) :=
        mul_le_mul_of_nonneg_right hjP hnonneg
  constructor
  · dsimp [favorableCorridor, erodedInterval] at hx ⊢
    push_cast at hx
    nlinarith [hx.1, hleftCost]
  · dsimp [favorableCorridor, erodedInterval] at hx ⊢
    push_cast at hx
    nlinarith [hx.2, hrightCost]

/-- Geometry for the transport--recovery block construction.  After `k`
transport steps and `P * k` recovery steps, the target corridor is contained
in the corresponding erosion of the transported interval whenever both
strict asymptotic slope inequalities hold. -/
theorem eventually_blockCorridor_subset_erodedExpanding
    {L R a b θ c front ε radius : ℝ} {N P : ℕ}
    (hleft :
      a + θ + (P : ℝ) * radius <
        (c + ε) * (1 + (P : ℝ)))
    (hright :
      (front - ε) * (1 + (P : ℝ)) <
        b - θ - (P : ℝ) * radius) :
    ∀ᶠ k : ℕ in atTop,
      favorableCorridor c front ε (N + k + P * k) ⊆
        erodedInterval
          (L + (a + θ) * (k : ℝ))
          (R + (b - θ) * (k : ℝ))
          radius (P * k) := by
  let leftGap : ℝ :=
    (c + ε) * (1 + (P : ℝ)) -
      (a + θ + (P : ℝ) * radius)
  let rightGap : ℝ :=
    (b - θ - (P : ℝ) * radius) -
      (front - ε) * (1 + (P : ℝ))
  have hleftGap : 0 < leftGap := by
    dsimp [leftGap]
    linarith
  have hrightGap : 0 < rightGap := by
    dsimp [rightGap]
    linarith
  have hleftTend :
      Tendsto (fun k : ℕ => leftGap * (k : ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hleftGap).2
      tendsto_natCast_atTop_atTop
  have hrightTend :
      Tendsto (fun k : ℕ => rightGap * (k : ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hrightGap).2
      tendsto_natCast_atTop_atTop
  have hleftEventually :
      ∀ᶠ k : ℕ in atTop,
        L - (c + ε) * (N : ℝ) ≤ leftGap * (k : ℝ) :=
    hleftTend.eventually (eventually_ge_atTop _)
  have hrightEventually :
      ∀ᶠ k : ℕ in atTop,
        (front - ε) * (N : ℝ) - R ≤ rightGap * (k : ℝ) :=
    hrightTend.eventually (eventually_ge_atTop _)
  filter_upwards [hleftEventually, hrightEventually] with
    k hkleft hkright
  intro x hx
  constructor
  · dsimp [favorableCorridor, erodedInterval] at hx ⊢
    dsimp [leftGap] at hkleft
    push_cast at hx ⊢
    nlinarith [hx.1]
  · dsimp [favorableCorridor, erodedInterval] at hx ⊢
    dsimp [rightGap] at hkright
    push_cast at hx ⊢
    nlinarith [hx.2]

/-- Any eventual lower bound on the eroded transport--recovery intervals
therefore becomes an eventual lower bound on the block-time moving
corridors. -/
theorem eventually_blockCorridor_lower_of_eroded_lower
    {focal : ℕ → ℝ → ℝ}
    {L R a b θ c front ε radius lower : ℝ} {N P : ℕ}
    (hleft :
      a + θ + (P : ℝ) * radius <
        (c + ε) * (1 + (P : ℝ)))
    (hright :
      (front - ε) * (1 + (P : ℝ)) <
        b - θ - (P : ℝ) * radius)
    (heroded :
      ∃ K, ∀ (k : ℕ), K ≤ k →
        ∀ x ∈ erodedInterval
            (L + (a + θ) * (k : ℝ))
            (R + (b - θ) * (k : ℝ))
            radius (P * k),
          lower < focal (N + k + P * k) x) :
    ∃ K, ∀ (k : ℕ), K ≤ k →
      ∀ x ∈ favorableCorridor c front ε (N + k + P * k),
        lower < focal (N + k + P * k) x := by
  have hgeom :=
    eventually_blockCorridor_subset_erodedExpanding
      (L := L) (R := R) (a := a) (b := b) (θ := θ)
      (c := c) (front := front) (ε := ε) (radius := radius)
      (N := N) (P := P) hleft hright
  rcases eventually_atTop.1 hgeom with ⟨Kgeom, hKgeom⟩
  rcases heroded with ⟨Klower, hKlower⟩
  refine ⟨max Kgeom Klower, ?_⟩
  intro k hk x hx
  exact hKlower k (le_trans (le_max_right _ _) hk) x <|
    hKgeom k (le_trans (le_max_left _ _) hk) hx

/-- The interval produced by the explicit kernel-minorization induction
eventually contains every corridor whose two boundary speeds lie strictly
inside its expansion speeds. -/
theorem eventually_favorableCorridor_subset_expandingSeedInterval
    {L R a b θ c front ε : ℝ} {N : ℕ}
    (hleft : a + θ < c + ε)
    (hright : front - ε < b - θ) :
    ∀ᶠ k : ℕ in atTop,
      favorableCorridor c front ε (N + k) ⊆
        expandingSeedInterval L R a b θ k := by
  have hleftgap : 0 < (c + ε) - (a + θ) := sub_pos.mpr hleft
  have hrightgap : 0 < (b - θ) - (front - ε) := sub_pos.mpr hright
  have hleft_tend :
      Tendsto (fun k : ℕ => ((c + ε) - (a + θ)) * (k : ℝ))
        atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hleftgap).2
      tendsto_natCast_atTop_atTop
  have hright_tend :
      Tendsto (fun k : ℕ => ((b - θ) - (front - ε)) * (k : ℝ))
        atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hrightgap).2
      tendsto_natCast_atTop_atTop
  have hleft_event :
      ∀ᶠ k : ℕ in atTop,
        L - (c + ε) * (N : ℝ) ≤
          ((c + ε) - (a + θ)) * (k : ℝ) :=
    hleft_tend.eventually (eventually_ge_atTop _)
  have hright_event :
      ∀ᶠ k : ℕ in atTop,
        (front - ε) * (N : ℝ) - R ≤
          ((b - θ) - (front - ε)) * (k : ℝ) :=
    hright_tend.eventually (eventually_ge_atTop _)
  filter_upwards [hleft_event, hright_event] with k hkleft hkright
  intro x hx
  constructor
  · dsimp [favorableCorridor, expandingSeedInterval] at hx ⊢
    push_cast at hx
    nlinarith [hx.1]
  · dsimp [favorableCorridor, expandingSeedInterval] at hx ⊢
    push_cast at hx
    nlinarith [hx.2]

/-- Direct discharge of the positive-floor hypothesis from the quantitative
kernel minorization.  The two strict speed inequalities state exactly which
corridors are certified by the chosen kernel window. -/
theorem favorableCorridor_positive_floor_of_minorization
    {competitor orbit : ℕ → ℝ → ℝ}
    {Kfun ρfun : ℝ → ℝ}
    {α c front ε ρ₀ δ z κ L R a b θ : ℝ} {N : ℕ}
    (horbit :
      ∀ k x,
        orbit (N + k + 1) x =
          heterogeneousCorrectedStep Kfun ρfun α c (N + k)
            (orbit (N + k)) (competitor (N + k)) x)
    (hKint : Integrable Kfun) (hKcont : Continuous Kfun)
    (hK : ∀ s, 0 ≤ Kfun s)
    (hKminor : ∀ s ∈ Set.Icc a b, κ ≤ Kfun s)
    (hρcont : Continuous ρfun) (hρlow : ∀ s, -1 < ρfun s)
    (hα : 0 ≤ α)
    (horbit_cont : ∀ n, Continuous (orbit n))
    (horbit_nonneg : ∀ n y, 0 ≤ orbit n y)
    (horbit_le_one : ∀ n y, orbit n y ≤ 1)
    (hcomp_cont : ∀ n, Continuous (competitor n))
    (hcomp_nonneg : ∀ n y, 0 ≤ competitor n y)
    (hκ : 0 ≤ κ) (hθ : 0 ≤ θ)
    (hwidth : b - a ≤ R - L)
    (hexpand : 2 * θ ≤ b - a)
    (hρ₀ : 0 ≤ ρ₀) (hz : 0 ≤ z) (hδ : 0 ≤ δ)
    (hsubunit : z + α * δ ≤ 1)
    (hfixed : z ≤ κ * θ * correctedResponse ρ₀ α z δ)
    (hseed : ∀ y ∈ Set.Icc L R, z ≤ orbit N y)
    (hcompetitor :
      ∀ (k : ℕ) (y : ℝ),
        y ∈ expandingSeedInterval L R a b θ k →
          competitor (N + k) y ≤ δ)
    (henvironment :
      ∀ (k : ℕ) (y : ℝ),
        y ∈ expandingSeedInterval L R a b θ k →
          ρ₀ ≤ ρfun (y - c * ((N + k : ℕ) : ℝ)))
    (hleft : a + θ < c + ε)
    (hright : front - ε < b - θ) :
    ∃ Nfloor, ∀ n, Nfloor ≤ n →
      ∀ y ∈ favorableCorridor c front ε n,
        z ≤ orbit n y := by
  have hpositive :=
    expanding_interval_positive_floor
      horbit hKint hKcont hK hKminor hρcont hρlow hα
      horbit_cont horbit_nonneg horbit_le_one
      hcomp_cont hcomp_nonneg hκ hθ hwidth hexpand
      hρ₀ hz hδ hsubunit hfixed hseed hcompetitor henvironment
  have hinclude :=
    eventually_favorableCorridor_subset_expandingSeedInterval
      (L := L) (R := R) (a := a) (b := b) (θ := θ)
      (c := c) (front := front) (ε := ε) (N := N)
      hleft hright
  rcases eventually_atTop.1 hinclude with ⟨k₀, hk₀⟩
  refine ⟨N + k₀, ?_⟩
  intro n hn y hy
  let k := n - N
  have hNn : N ≤ n := by omega
  have hNk : N + k = n := by
    dsimp [k]
    omega
  have hk₀k : k₀ ≤ k := by
    dsimp [k]
    omega
  have hyexpand :
      y ∈ expandingSeedInterval L R a b θ k := by
    apply hk₀ k hk₀k
    simpa [hNk] using hy
  have hp := hpositive k y hyexpand
  simpa [hNk] using hp

/-- At a fixed finite iteration horizon, every eroded predecessor corridor is
eventually far enough ahead of the habitat to sample any prescribed favorable
tail. -/
theorem eventually_erodedCorridor_ahead_of
    {c εwide radius S : ℝ} {k : ℕ}
    (hc : 0 ≤ c) (hε : 0 < εwide) (hradius : 0 ≤ radius) :
    ∀ᶠ n : ℕ in atTop,
      ∀ j ≤ k, ∀ y,
        y ∈ erodedInterval
          ((c + εwide) * (n : ℝ))
          (S + (c + εwide + radius + 1) * (n : ℝ))
          radius j →
        S ≤ y - c * ((n + j : ℕ) : ℝ) := by
  have htend :
      Tendsto (fun n : ℕ => εwide * (n : ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hε).2
      tendsto_natCast_atTop_atTop
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        S + c * (k : ℝ) ≤ εwide * (n : ℝ) :=
    htend.eventually (eventually_ge_atTop _)
  filter_upwards [hevent] with n hn
  intro j hj y hy
  have hjcast : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hj
  dsimp [erodedInterval] at hy
  push_cast
  nlinarith [hy.1]

/-- The preceding tail lemma specialized to an actual favorable corridor. -/
theorem eventually_erodedFavorableCorridor_ahead_of
    {c front εwide radius S : ℝ} {k : ℕ}
    (hc : 0 ≤ c) (hε : 0 < εwide) (hradius : 0 ≤ radius) :
    ∀ᶠ n : ℕ in atTop,
      ∀ j ≤ k, ∀ y,
        y ∈ erodedInterval
          ((c + εwide) * (n : ℝ))
          ((front - εwide) * (n : ℝ))
          radius j →
        S ≤ y - c * ((n + j : ℕ) : ℝ) := by
  have htend :
      Tendsto (fun n : ℕ => εwide * (n : ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hε).2
      tendsto_natCast_atTop_atTop
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        S + c * (k : ℝ) ≤ εwide * (n : ℝ) :=
    htend.eventually (eventually_ge_atTop _)
  filter_upwards [hevent] with n hn
  intro j hj y hy
  have hjcast : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hj
  have hcj : c * (j : ℝ) ≤ c * (k : ℝ) :=
    mul_le_mul_of_nonneg_left hjcast hc
  have hjr : 0 ≤ (j : ℝ) * radius :=
    mul_nonneg (Nat.cast_nonneg j) hradius
  dsimp [erodedInterval] at hy
  push_cast
  nlinarith [hy.1, hcj, hjr]

/-! ## Uniform convergence in the corrected one-sided corridor -/

/-- Once a quantitative positive floor is available in a slightly wider
corridor, uniform extinction of the competitor forces the focal species to
converge uniformly to one in every strictly smaller corridor.

The positive-floor hypothesis is not circular: `expanding_interval_positive_floor`
proves it from a compact interval seed and a quantitative kernel
minorization.  Keeping it explicit here separates the propagation mechanism
from the subsequent Beverton--Holt relaxation argument. -/
theorem corridor_converges_to_one_of_positive_floor
    {focal competitor : ℕ → ℝ → ℝ}
    {Kfun ρfun : ℝ → ℝ}
    {α c front εwide εtarget radius ρ₀ floor : ℝ}
    (hstep :
      ∀ n x,
        focal (n + 1) x =
          heterogeneousCorrectedStep Kfun ρfun α c n
            (focal n) (competitor n) x)
    (hKint : Integrable Kfun) (hKcont : Continuous Kfun)
    (hKnonneg : ∀ s, 0 ≤ Kfun s) (hKmass : ∫ s, Kfun s = 1)
    (hradius : 0 ≤ radius)
    (hKsupport : ∀ s, radius < |s| → Kfun s = 0)
    (hρcont : Continuous ρfun) (hρlow : ∀ s, -1 < ρfun s)
    (hα : 0 ≤ α)
    (hfocal_cont : ∀ n, Continuous (focal n))
    (hfocal_nonneg : ∀ n y, 0 ≤ focal n y)
    (hfocal_le_one : ∀ n y, focal n y ≤ 1)
    (hcompetitor_cont : ∀ n, Continuous (competitor n))
    (hcompetitor_nonneg : ∀ n y, 0 ≤ competitor n y)
    (hc : 0 ≤ c) (hρ₀ : 0 < ρ₀)
    (henvironment_tail : ∃ S, ∀ s, S ≤ s → ρ₀ ≤ ρfun s)
    (hεwide : 0 < εwide) (hεgap : εwide < εtarget)
    (hcorridor : c + 2 * εtarget ≤ front)
    (hfloor_pos : 0 < floor)
    (hfloor :
      ∃ Nfloor, ∀ n, Nfloor ≤ n →
        ∀ x ∈ favorableCorridor c front εwide n,
          floor ≤ focal n x)
    (hcompetitor_vanishes :
      ∀ δ, 0 < δ →
        ∃ Nδ, ∀ n, Nδ ≤ n → ∀ x, competitor n x ≤ δ) :
    ∀ η, 0 < η →
      ∃ N, ∀ n, N ≤ n →
        ∀ x ∈ favorableCorridor c front εtarget n,
          |focal n x - 1| < η := by
  have _hcorridor_nonempty :
      (favorableCorridor c front εtarget 1).Nonempty :=
    favorableCorridor_nonempty hcorridor 1
  intro η hη
  let e : ℝ := min η (1 / 2 : ℝ)
  have he : 0 < e := lt_min hη (by norm_num)
  have heη : e ≤ η := min_le_left _ _
  have hehalf : e ≤ 1 / 2 := min_le_right _ _
  let δ : ℝ := e / (4 * (α + 1))
  have hαone : 0 < α + 1 := by linarith
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hαδ_nonneg : 0 ≤ α * δ := mul_nonneg hα hδ.le
  have hαδ_lt_equarter : α * δ < e / 4 := by
    dsimp [δ]
    have hratio : α / (α + 1) < 1 := by
      apply (div_lt_one hαone).2
      linarith
    have he4 : 0 < e / 4 := by positivity
    calc
      α * (e / (4 * (α + 1))) =
          (e / 4) * (α / (α + 1)) := by field_simp
      _ < (e / 4) * 1 :=
        mul_lt_mul_of_pos_left hratio he4
      _ = e / 4 := mul_one _
  have hsmall : α * δ < 1 := by
    have : e / 4 ≤ 1 / 8 := by linarith
    linarith
  have hq : 0 < perturbedCarrying α δ := by
    unfold perturbedCarrying
    linarith
  let seed : ℝ := min floor (perturbedCarrying α δ / 2)
  have hseed_pos : 0 < seed :=
    lt_min hfloor_pos (by positivity)
  have hseed_floor : seed ≤ floor := min_le_left _ _
  have hseed_carrying : seed ≤ perturbedCarrying α δ := by
    calc
      seed ≤ perturbedCarrying α δ / 2 := min_le_right _ _
      _ ≤ perturbedCarrying α δ := by linarith
  have hr : 1 < perturbedMultiplier ρ₀ α δ :=
    one_lt_perturbedMultiplier hρ₀ hα hδ.le hsmall
  have hBHlim :
      Tendsto
        (bhOrbit (perturbedMultiplier ρ₀ α δ)
          (perturbedCarrying α δ) seed)
        atTop (𝓝 (perturbedCarrying α δ)) :=
    bhOrbit_tendsto_carrying hr hq hseed_pos hseed_carrying
  have hBHlarge :
      ∀ᶠ k : ℕ in atTop,
        perturbedCarrying α δ - e / 4 <
          bhOrbit (perturbedMultiplier ρ₀ α δ)
            (perturbedCarrying α δ) seed k :=
    (tendsto_order.1 hBHlim).1 _ (by linarith)
  rcases hBHlarge.exists with ⟨k, hk⟩
  rcases hfloor with ⟨Nfloor, hfloor⟩
  rcases hcompetitor_vanishes δ hδ with ⟨Nδ, hNδ⟩
  rcases henvironment_tail with ⟨S, hS⟩
  have hgeom :=
    eventually_targetCorridor_subset_eroded
      (c := c) (front := front) (radius := radius) (k := k)
      hεgap
  have hahead :=
    eventually_erodedFavorableCorridor_ahead_of
      (c := c) (front := front) (radius := radius) (S := S) (k := k)
      hc hεwide hradius
  have hbase :
      ∀ᶠ n : ℕ in atTop, Nfloor ≤ n ∧ Nδ ≤ n :=
    (eventually_ge_atTop Nfloor).and (eventually_ge_atTop Nδ)
  have hshifted :
      ∀ᶠ n : ℕ in atTop,
        ∀ x ∈ favorableCorridor c front εtarget (n + k),
          |focal (n + k) x - 1| < η := by
    filter_upwards [hgeom, hahead, hbase] with n hngeom hnahead hnbase
    intro x hx
    let L : ℝ := (c + εwide) * (n : ℝ)
    let R : ℝ := (front - εwide) * (n : ℝ)
    have hx_eroded : x ∈ erodedInterval L R radius k := by
      exact hngeom hx
    have hlower :
        bhOrbit (perturbedMultiplier ρ₀ α δ)
            (perturbedCarrying α δ) seed k ≤
          focal (n + k) x := by
      apply bhOrbit_le_on_erodedInterval
        (N := n) (horizon := k) (L := L) (R := R)
        (Kfun := Kfun) (ρfun := ρfun)
        (α := α) (c := c) (radius := radius)
        (ρ₀ := ρ₀) (δ := δ) (seed := seed)
      · intro j y
        simpa [Nat.add_assoc] using hstep (n + j) y
      · exact hKint
      · exact hKcont
      · exact hKnonneg
      · exact hKmass
      · exact hKsupport
      · exact hρcont
      · exact hρlow
      · exact hα
      · exact hfocal_cont
      · exact hfocal_nonneg
      · exact hfocal_le_one
      · exact hcompetitor_cont
      · exact hcompetitor_nonneg
      · exact hρ₀
      · exact hδ.le
      · exact hsmall
      · exact hseed_pos
      · exact hseed_carrying
      · intro y hy
        apply hseed_floor.trans
        apply hfloor n hnbase.1 y
        simpa [favorableCorridor, L, R] using hy
      · intro j y _hj hy
        exact hNδ (n + j) (by omega) y
      · intro j y hj hy
        apply hS
        exact hnahead j hj y <| by
          simpa [L, R] using hy
      · exact le_rfl
      · exact hx_eroded
    have hv1 := hfocal_le_one (n + k) x
    have hv_lower :
        1 - e / 2 < focal (n + k) x := by
      have hBH :
          1 - e / 2 <
            bhOrbit (perturbedMultiplier ρ₀ α δ)
              (perturbedCarrying α δ) seed k := by
        have hthreshold :
            1 - e / 2 <
              perturbedCarrying α δ - e / 4 := by
          unfold perturbedCarrying
          linarith
        exact hthreshold.trans hk
      exact hBH.trans_le hlower
    rw [abs_of_nonpos (sub_nonpos.mpr hv1)]
    linarith
  rcases eventually_atTop.1 hshifted with ⟨Nbase, hNbase⟩
  refine ⟨Nbase + k, ?_⟩
  intro t ht x hx
  let n := t - k
  have hkt : k ≤ t := by omega
  have hn : Nbase ≤ n := by
    dsimp [n]
    omega
  have hnk : n + k = t := by
    dsimp [n]
    omega
  simpa [hnk] using hNbase n hn x (by simpa [hnk] using hx)

/-! ## Corrected intermediate-speed assembly -/

/-- Uniform extinction, written without choosing a particular normed profile
space. -/
def UniformlyExtinct (u : ℕ → ℝ → ℝ) : Prop :=
  ∀ η, 0 < η →
    ∃ N, ∀ n, N ≤ n → ∀ x, u n x < η

/-- Norm convergence of nonnegative bounded-continuous profiles mechanically
supplies the pointwise formulation used by the assembled theorem. -/
theorem uniformlyExtinct_of_bcf_norm_tendsto_zero
    (w : ℕ → ℝ →ᵇ ℝ)
    (hw : ∀ n x, 0 ≤ w n x)
    (hlim : Tendsto (fun n => ‖w n‖) atTop (𝓝 0)) :
    UniformlyExtinct (fun n x => w n x) := by
  intro η hη
  have hevent : ∀ᶠ n : ℕ in atTop, ‖w n‖ < η :=
    (tendsto_order.1 hlim).2 η hη
  rcases eventually_atTop.1 hevent with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn x
  have hpoint :
      |w n x| ≤ ‖w n‖ := by
    simpa [Real.norm_eq_abs] using (w n).norm_coe_le_norm x
  rw [abs_of_nonneg (hw n x)] at hpoint
  exact hpoint.trans_lt (hN n hn)

/-- Uniform convergence to one on the corrected one-sided corridor. -/
def UniformlyConvergesToOneInCorridor
    (u : ℕ → ℝ → ℝ) (c front ε : ℝ) : Prop :=
  ∀ η, 0 < η →
    ∃ N, ∀ n, N ≤ n →
      ∀ x ∈ favorableCorridor c front ε n, |u n x - 1| < η

/-- Uniform convergence on the block times used by the attenuated-front
construction: `N + k + P*k`. -/
def UniformlyConvergesToOneInBlockCorridor
    (u : ℕ → ℝ → ℝ) (c front ε : ℝ) (N P : ℕ) : Prop :=
  ∀ η, 0 < η →
    ∃ K, ∀ (k : ℕ), K ≤ k →
      ∀ x ∈ favorableCorridor c front ε (N + k + P * k),
        |u (N + k + P * k) x - 1| < η

/-- Convergence on all transport--recovery block times propagates across the
bounded set of intermediate residues.  Thus a wider block corridor gives
ordinary all-time convergence on every strictly narrower corridor. -/
theorem blockCorridor_convergence_implies_all_times
    {focal competitor : ℕ → ℝ → ℝ}
    {Kfun ρfun : ℝ → ℝ}
    {α c front εwide εtarget radius ρ₀ : ℝ}
    {N P : ℕ}
    (hstep :
      ∀ n x,
        focal (n + 1) x =
          heterogeneousCorrectedStep Kfun ρfun α c n
            (focal n) (competitor n) x)
    (hKint : Integrable Kfun) (hKcont : Continuous Kfun)
    (hKnonneg : ∀ s, 0 ≤ Kfun s) (hKmass : ∫ s, Kfun s = 1)
    (hradius : 0 ≤ radius)
    (hKsupport : ∀ s, radius < |s| → Kfun s = 0)
    (hρcont : Continuous ρfun) (hρlow : ∀ s, -1 < ρfun s)
    (hα : 0 ≤ α)
    (hfocal_cont : ∀ n, Continuous (focal n))
    (hfocal_nonneg : ∀ n y, 0 ≤ focal n y)
    (hfocal_le_one : ∀ n y, focal n y ≤ 1)
    (hcompetitor_cont : ∀ n, Continuous (competitor n))
    (hcompetitor_nonneg : ∀ n y, 0 ≤ competitor n y)
    (hcompetitor_extinct : UniformlyExtinct competitor)
    (hc : 0 ≤ c) (hρ₀ : 0 < ρ₀)
    (henvironment_tail : ∃ S, ∀ s, S ≤ s → ρ₀ ≤ ρfun s)
    (hεwide : 0 < εwide) (hεgap : εwide < εtarget)
    (hblock :
      UniformlyConvergesToOneInBlockCorridor
        focal c front εwide N P) :
    UniformlyConvergesToOneInCorridor focal c front εtarget := by
  intro η hη
  let e : ℝ := min (η / 2) (1 / 2)
  have hepos : 0 < e := by
    dsimp [e]
    exact lt_min (by positivity) (by norm_num)
  have heη : e ≤ η / 2 := by
    dsimp [e]
    exact min_le_left _ _
  have hehalf : e ≤ 1 / 2 := by
    dsimp [e]
    exact min_le_right _ _
  let δ : ℝ := e / (2 * (1 + α))
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  have hαδ : α * δ < e := by
    have hratio : α / (1 + α) < 1 := by
      apply (div_lt_one (by linarith)).2
      linarith
    calc
      α * δ = (e / 2) * (α / (1 + α)) := by
        dsimp [δ]
        field_simp
      _ < (e / 2) * 1 :=
        mul_lt_mul_of_pos_left hratio (by positivity)
      _ < e := by linarith
  have hsmall : α * δ < 1 := by
    linarith
  have hseedpos : 0 < 1 - e := by
    linarith
  have hseedq : 1 - e ≤ perturbedCarrying α δ := by
    unfold perturbedCarrying
    linarith
  rcases hcompetitor_extinct δ hδpos with ⟨Nδ, hNδ⟩
  rcases hblock e hepos with ⟨Kblock, hKblock⟩
  have hgeom :=
    eventually_targetCorridor_subset_eroded_upTo
      (c := c) (front := front)
      (εwide := εwide) (εtarget := εtarget)
      (radius := radius) (P := P) hεgap hradius
  rcases eventually_atTop.1 hgeom with ⟨Ngeom, hNgeom⟩
  rcases henvironment_tail with ⟨S, hS⟩
  have hahead :=
    eventually_erodedFavorableCorridor_ahead_of
      (c := c) (front := front) (εwide := εwide)
      (radius := radius) (S := S) (k := P)
      hc hεwide hradius
  rcases eventually_atTop.1 hahead with ⟨Nahead, hNahead⟩
  let Kall : ℕ := max Kblock (max Nδ (max Ngeom Nahead))
  refine ⟨N + (P + 1) * Kall, ?_⟩
  intro t ht x hx
  have hNt : N ≤ t := by omega
  let k : ℕ := (t - N) / (P + 1)
  let j : ℕ := (t - N) % (P + 1)
  have hPpos : 0 < P + 1 := by omega
  have hjlt : j < P + 1 := by
    dsimp [j]
    exact Nat.mod_lt _ hPpos
  have hjP : j ≤ P := by omega
  have hprod : (P + 1) * Kall ≤ t - N := by
    apply Nat.le_sub_of_add_le
    simpa [add_comm] using ht
  have hKallk : Kall ≤ k := by
    dsimp [k]
    apply (Nat.le_div_iff_mul_le hPpos).2
    simpa [mul_comm] using hprod
  have hdecomp : j + (P + 1) * k = t - N := by
    dsimp [j, k]
    exact Nat.mod_add_div _ _
  have ht_eq : N + k + P * k + j = t := by
    calc
      N + k + P * k + j = N + (j + (P + 1) * k) := by ring
      _ = N + (t - N) := by rw [hdecomp]
      _ = t := Nat.add_sub_of_le hNt
  let nbase : ℕ := N + k + P * k
  have hKblockk : Kblock ≤ k :=
    le_trans (le_max_left _ _) hKallk
  have hNδbase : Nδ ≤ nbase := by
    dsimp [Kall, nbase] at hKallk ⊢
    omega
  have hNgeombase : Ngeom ≤ nbase := by
    dsimp [Kall, nbase] at hKallk ⊢
    omega
  have hNaheadbase : Nahead ≤ nbase := by
    dsimp [Kall, nbase] at hKallk ⊢
    omega
  have hx_eroded :
      x ∈ erodedInterval
        ((c + εwide) * (nbase : ℝ))
        ((front - εwide) * (nbase : ℝ))
        radius j := by
    apply hNgeom nbase hNgeombase j hjP
    simpa [nbase, ht_eq] using hx
  have hlower :
      bhOrbit (perturbedMultiplier ρ₀ α δ)
          (perturbedCarrying α δ) (1 - e) j ≤
        focal t x := by
    rw [← ht_eq]
    apply bhOrbit_le_on_erodedInterval
      (N := nbase) (horizon := j)
      (L := (c + εwide) * (nbase : ℝ))
      (R := (front - εwide) * (nbase : ℝ))
      (Kfun := Kfun) (ρfun := ρfun)
      (α := α) (c := c) (radius := radius)
      (ρ₀ := ρ₀) (δ := δ) (seed := 1 - e)
    · intro s y
      simpa [nbase, Nat.add_assoc] using hstep (nbase + s) y
    · exact hKint
    · exact hKcont
    · exact hKnonneg
    · exact hKmass
    · exact hKsupport
    · exact hρcont
    · exact hρlow
    · exact hα
    · exact hfocal_cont
    · exact hfocal_nonneg
    · exact hfocal_le_one
    · exact hcompetitor_cont
    · exact hcompetitor_nonneg
    · exact hρ₀
    · exact hδpos.le
    · exact hsmall
    · exact hseedpos
    · exact hseedq
    · intro y hy
      have hclose :=
        hKblock k hKblockk y <| by
          simpa [nbase, favorableCorridor] using hy
      have hlowerclose := (abs_lt.mp hclose).1
      linarith
    · intro s y _hs _hy
      exact (hNδ (nbase + s) (by omega) y).le
    · intro s y hs hy
      apply hS
      exact hNahead nbase hNaheadbase s (hs.trans hjP) y hy
    · exact le_rfl
    · exact hx_eroded
  have hr :
      1 < perturbedMultiplier ρ₀ α δ :=
    one_lt_perturbedMultiplier hρ₀ hα hδpos.le hsmall
  have hq : 0 < perturbedCarrying α δ := by
    unfold perturbedCarrying
    linarith
  have hBHseed :
      1 - e ≤
        bhOrbit (perturbedMultiplier ρ₀ α δ)
          (perturbedCarrying α δ) (1 - e) j := by
    have hmono :=
      bhOrbit_monotone hr hq hseedpos hseedq
    simpa using hmono (Nat.zero_le j)
  have hfocal_lower : 1 - e ≤ focal t x :=
    hBHseed.trans hlower
  have hfocal_upper := hfocal_le_one t x
  rw [abs_of_nonpos (sub_nonpos.mpr hfocal_upper)]
  nlinarith

/-- A fixed positive floor available on all block times extends across the
finitely many intermediate residue classes. -/
theorem blockCorridor_floor_implies_all_times
    {focal competitor : ℕ → ℝ → ℝ}
    {Kfun ρfun : ℝ → ℝ}
    {α c front εwide εtarget radius ρ₀ δ seed : ℝ}
    {N P : ℕ}
    (hstep :
      ∀ n x,
        focal (n + 1) x =
          heterogeneousCorrectedStep Kfun ρfun α c n
            (focal n) (competitor n) x)
    (hKint : Integrable Kfun) (hKcont : Continuous Kfun)
    (hKnonneg : ∀ s, 0 ≤ Kfun s) (hKmass : ∫ s, Kfun s = 1)
    (hradius : 0 ≤ radius)
    (hKsupport : ∀ s, radius < |s| → Kfun s = 0)
    (hρcont : Continuous ρfun) (hρlow : ∀ s, -1 < ρfun s)
    (hα : 0 ≤ α)
    (hfocal_cont : ∀ n, Continuous (focal n))
    (hfocal_nonneg : ∀ n y, 0 ≤ focal n y)
    (hfocal_le_one : ∀ n y, focal n y ≤ 1)
    (hcompetitor_cont : ∀ n, Continuous (competitor n))
    (hcompetitor_nonneg : ∀ n y, 0 ≤ competitor n y)
    (hcompetitor_eventually :
      ∃ Nδ, ∀ n, Nδ ≤ n → ∀ x, competitor n x ≤ δ)
    (hc : 0 ≤ c) (hρ₀ : 0 < ρ₀)
    (henvironment_tail : ∃ S, ∀ s, S ≤ s → ρ₀ ≤ ρfun s)
    (hεwide : 0 < εwide) (hεgap : εwide < εtarget)
    (hδ : 0 < δ) (hsmall : α * δ < 1)
    (hseed : 0 < seed)
    (hseedq : seed ≤ perturbedCarrying α δ)
    (hblockfloor :
      ∃ K, ∀ (k : ℕ), K ≤ k →
        ∀ x ∈ favorableCorridor c front εwide (N + k + P * k),
          seed ≤ focal (N + k + P * k) x) :
    ∃ Nfloor, ∀ n, Nfloor ≤ n →
      ∀ x ∈ favorableCorridor c front εtarget n,
        seed ≤ focal n x := by
  rcases hcompetitor_eventually with ⟨Nδ, hNδ⟩
  rcases hblockfloor with ⟨Kblock, hKblock⟩
  have hgeom :=
    eventually_targetCorridor_subset_eroded_upTo
      (c := c) (front := front)
      (εwide := εwide) (εtarget := εtarget)
      (radius := radius) (P := P) hεgap hradius
  rcases eventually_atTop.1 hgeom with ⟨Ngeom, hNgeom⟩
  rcases henvironment_tail with ⟨S, hS⟩
  have hahead :=
    eventually_erodedFavorableCorridor_ahead_of
      (c := c) (front := front) (εwide := εwide)
      (radius := radius) (S := S) (k := P)
      hc hεwide hradius
  rcases eventually_atTop.1 hahead with ⟨Nahead, hNahead⟩
  let Kall : ℕ := max Kblock (max Nδ (max Ngeom Nahead))
  refine ⟨N + (P + 1) * Kall, ?_⟩
  intro t ht x hx
  have hNt : N ≤ t := by omega
  let k : ℕ := (t - N) / (P + 1)
  let j : ℕ := (t - N) % (P + 1)
  have hPpos : 0 < P + 1 := by omega
  have hjlt : j < P + 1 := by
    dsimp [j]
    exact Nat.mod_lt _ hPpos
  have hjP : j ≤ P := by omega
  have hprod : (P + 1) * Kall ≤ t - N := by
    apply Nat.le_sub_of_add_le
    simpa [add_comm] using ht
  have hKallk : Kall ≤ k := by
    dsimp [k]
    apply (Nat.le_div_iff_mul_le hPpos).2
    simpa [mul_comm] using hprod
  have hdecomp : j + (P + 1) * k = t - N := by
    dsimp [j, k]
    exact Nat.mod_add_div _ _
  have ht_eq : N + k + P * k + j = t := by
    calc
      N + k + P * k + j = N + (j + (P + 1) * k) := by ring
      _ = N + (t - N) := by rw [hdecomp]
      _ = t := Nat.add_sub_of_le hNt
  let nbase : ℕ := N + k + P * k
  have hKblockk : Kblock ≤ k :=
    le_trans (le_max_left _ _) hKallk
  have hNδbase : Nδ ≤ nbase := by
    dsimp [Kall, nbase] at hKallk ⊢
    omega
  have hNgeombase : Ngeom ≤ nbase := by
    dsimp [Kall, nbase] at hKallk ⊢
    omega
  have hNaheadbase : Nahead ≤ nbase := by
    dsimp [Kall, nbase] at hKallk ⊢
    omega
  have hx_eroded :
      x ∈ erodedInterval
        ((c + εwide) * (nbase : ℝ))
        ((front - εwide) * (nbase : ℝ))
        radius j := by
    apply hNgeom nbase hNgeombase j hjP
    simpa [nbase, ht_eq] using hx
  have hlower :
      bhOrbit (perturbedMultiplier ρ₀ α δ)
          (perturbedCarrying α δ) seed j ≤
        focal t x := by
    rw [← ht_eq]
    apply bhOrbit_le_on_erodedInterval
      (N := nbase) (horizon := j)
      (L := (c + εwide) * (nbase : ℝ))
      (R := (front - εwide) * (nbase : ℝ))
      (Kfun := Kfun) (ρfun := ρfun)
      (α := α) (c := c) (radius := radius)
      (ρ₀ := ρ₀) (δ := δ) (seed := seed)
    · intro s y
      simpa [nbase, Nat.add_assoc] using hstep (nbase + s) y
    · exact hKint
    · exact hKcont
    · exact hKnonneg
    · exact hKmass
    · exact hKsupport
    · exact hρcont
    · exact hρlow
    · exact hα
    · exact hfocal_cont
    · exact hfocal_nonneg
    · exact hfocal_le_one
    · exact hcompetitor_cont
    · exact hcompetitor_nonneg
    · exact hρ₀
    · exact hδ.le
    · exact hsmall
    · exact hseed
    · exact hseedq
    · intro y hy
      exact hKblock k hKblockk y <| by
        simpa [nbase, favorableCorridor] using hy
    · intro s y _hs _hy
      exact hNδ (nbase + s) (by omega) y
    · intro s y hs hy
      apply hS
      exact hNahead nbase hNaheadbase s (hs.trans hjP) y hy
    · exact le_rfl
    · exact hx_eroded
  have hr :
      1 < perturbedMultiplier ρ₀ α δ :=
    one_lt_perturbedMultiplier hρ₀ hα hδ.le hsmall
  have hq : 0 < perturbedCarrying α δ := by
    unfold perturbedCarrying
    linarith
  have hBHseed :
      seed ≤
        bhOrbit (perturbedMultiplier ρ₀ α δ)
          (perturbedCarrying α δ) seed j := by
    have hmono :=
      bhOrbit_monotone hr hq hseed hseedq
    simpa using hmono (Nat.zero_le j)
  exact hBHseed.trans hlower

/-- **Multistep corrected Theorem 2.2 on certified block times.**

This removes the impossible-in-general fixed-floor reproduction condition
from the one-step theorem.  A small seed is first transported for `k`
generations and may attenuate like `(κθ)^k`.  It is then given `P*k`
full-mass recovery generations.  The single analytic requirement is the block
growth inequality

`1 < (κθ) * perturbedMultiplier ρ₀ α δseed ^ P`.

The two strict affine inequalities are exactly the cost of fitting the final
moving corridor inside the finite-range domain available to the recovery
phase. -/
theorem correctedIntermediateSpeedExclusion_of_multistep_minorization
    {slow fast : ℕ → ℝ → ℝ}
    {K ρ : ℝ → ℝ}
    {α c front ε radius ρ₀ Senv : ℝ}
    {Nseed P : ℕ}
    {δseed seed κ L R a b θ : ℝ}
    (hslow_extinction : UniformlyExtinct slow)
    (hfaststep :
      ∀ n x,
        fast (n + 1) x =
          heterogeneousCorrectedStep K ρ α c n (fast n) (slow n) x)
    (hKint : Integrable K) (hKcont : Continuous K)
    (hKnonneg : ∀ s, 0 ≤ K s) (hKmass : ∫ s, K s = 1)
    (hradius : 0 ≤ radius)
    (hKsupport : ∀ s, radius < |s| → K s = 0)
    (hKminor : ∀ s ∈ Set.Icc a b, κ ≤ K s)
    (hρcont : Continuous ρ) (hρlow : ∀ s, -1 < ρ s)
    (hα : 0 ≤ α)
    (hfast_cont : ∀ n, Continuous (fast n))
    (hfast_nonneg : ∀ n y, 0 ≤ fast n y)
    (hfast_le_one : ∀ n y, fast n y ≤ 1)
    (hslow_cont : ∀ n, Continuous (slow n))
    (hslow_nonneg : ∀ n y, 0 ≤ slow n y)
    (hc : 0 ≤ c) (hρ₀ : 0 < ρ₀)
    (henvironment_tail : ∀ s, Senv ≤ s → ρ₀ ≤ ρ s)
    (hκ : 0 ≤ κ) (hθ : 0 ≤ θ)
    (hretained_pos : 0 < κ * θ)
    (hretained_le : κ * θ ≤ 1)
    (hwidth : b - a ≤ R - L)
    (hexpand : 2 * θ ≤ b - a)
    (hδseed : 0 < δseed)
    (hsmall_seed : α * δseed < 1)
    (hseed : 0 < seed)
    (hseed_carrying : seed ≤ perturbedCarrying α δseed)
    (hinitial_seed : ∀ y ∈ Set.Icc L R, seed ≤ fast Nseed y)
    (hslow_small_after_seed :
      ∀ n, Nseed ≤ n → ∀ y, slow n y ≤ δseed)
    (hseed_ahead : Senv ≤ L - c * (Nseed : ℝ))
    (hhabitat_block : c * (1 + (P : ℝ)) < a + θ)
    (hgrowth :
      1 < (κ * θ) * perturbedMultiplier ρ₀ α δseed ^ P)
    (hleft :
      a + θ + (P : ℝ) * radius <
        (c + ε) * (1 + (P : ℝ)))
    (hright :
      (front - ε) * (1 + (P : ℝ)) <
        b - θ - (P : ℝ) * radius) :
    UniformlyExtinct slow ∧
      UniformlyConvergesToOneInBlockCorridor
        fast c front ε Nseed P := by
  have hfront :
      ∀ (k : ℕ) (y : ℝ),
        y ∈ expandingSeedInterval L R a b θ k →
          attenuatedFloor (κ * θ) ρ₀ α δseed seed k ≤
            fast (Nseed + k) y := by
    apply expanding_interval_attenuated_floor
      (Kfun := K) (ρfun := ρ) (α := α) (c := c)
      (ρ₀ := ρ₀) (δ := δseed) (seed := seed)
      (κ := κ) (L := L) (R := R) (a := a) (b := b) (θ := θ)
      (N := Nseed)
    · intro k x
      simpa [Nat.add_assoc] using hfaststep (Nseed + k) x
    · exact hKint
    · exact hKcont
    · exact hKnonneg
    · exact hKminor
    · exact hρcont
    · exact hρlow
    · exact hα
    · exact hfast_cont
    · exact hfast_nonneg
    · exact hfast_le_one
    · exact hslow_cont
    · exact hslow_nonneg
    · exact hκ
    · exact hθ
    · exact hretained_le
    · exact hwidth
    · exact hexpand
    · exact hρ₀
    · exact hδseed.le
    · exact hsmall_seed
    · exact hseed.le
    · exact hseed_carrying
    · exact hinitial_seed
    · intro k y _hy
      exact hslow_small_after_seed (Nseed + k) (by omega) y
    · intro k y hy
      apply henvironment_tail
      have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      have hcblock : c ≤ c * (1 + (P : ℝ)) := by
        have hP0 : 0 ≤ (P : ℝ) := Nat.cast_nonneg P
        nlinarith
      have hadvance : 0 ≤ ((a + θ) - c) * (k : ℝ) := by
        apply mul_nonneg
        · linarith
        · exact hk0
      dsimp [expandingSeedInterval] at hy
      push_cast
      nlinarith [hy.1, hseed_ahead, hadvance]
  refine ⟨hslow_extinction, ?_⟩
  intro η hη
  let δrecover : ℝ :=
    min δseed (η / (4 * (1 + α)))
  have hdenα : 0 < 4 * (1 + α) := by positivity
  have hδrecover_pos : 0 < δrecover := by
    dsimp [δrecover]
    exact lt_min hδseed (div_pos hη hdenα)
  have hδrecover_order : δrecover ≤ δseed := by
    dsimp [δrecover]
    exact min_le_left _ _
  have hδrecover_fraction :
      δrecover ≤ η / (4 * (1 + α)) := by
    dsimp [δrecover]
    exact min_le_right _ _
  have hratio : α / (1 + α) < 1 := by
    apply (div_lt_one (by linarith)).2
    linarith
  have hαδrecover : α * δrecover < η / 4 := by
    calc
      α * δrecover ≤ α * (η / (4 * (1 + α))) :=
        mul_le_mul_of_nonneg_left hδrecover_fraction hα
      _ = (η / 4) * (α / (1 + α)) := by
        field_simp
      _ < (η / 4) * 1 :=
        mul_lt_mul_of_pos_left hratio (by positivity)
      _ = η / 4 := mul_one _
  rcases hslow_extinction δrecover hδrecover_pos with
    ⟨Nδ, hNδ⟩
  have hmultiplier :
      perturbedMultiplier ρ₀ α δseed ≤
        perturbedMultiplier ρ₀ α δrecover :=
    perturbedMultiplier_antitone_delta
      hρ₀.le hα hδrecover_pos.le hδrecover_order
  have hpowMultiplier :
      perturbedMultiplier ρ₀ α δseed ^ P ≤
        perturbedMultiplier ρ₀ α δrecover ^ P :=
    pow_le_pow_left₀
      (by
        unfold perturbedMultiplier
        positivity)
      hmultiplier P
  have hgrowth_recover :
      1 < (κ * θ) *
        perturbedMultiplier ρ₀ α δrecover ^ P :=
    hgrowth.trans_le <|
      mul_le_mul_of_nonneg_left hpowMultiplier hretained_pos.le
  have heroded :
      ∃ Kbase, ∀ (k : ℕ), Kbase ≤ k →
        ∀ x ∈ erodedInterval
            (L + (a + θ) * (k : ℝ))
            (R + (b - θ) * (k : ℝ))
            radius (P * k),
          perturbedCarrying α δrecover - η / 4 <
            fast (Nseed + k + P * k) x := by
    apply eventually_carrying_minus_lt_after_attenuated_front
      (Kpre := Nδ)
      (Kfun := K) (ρfun := ρ)
      (α := α) (c := c) (radius := radius)
      (ρtransport := ρ₀) (δtransport := δseed)
      (ρrecover := ρ₀) (δrecover := δrecover)
      (seed := seed) (A := κ * θ)
      (L := L) (R := R) (a := a) (b := b) (θ := θ)
      (N := Nseed) (P := P) (η := η / 4)
    · exact hfaststep
    · exact hKint
    · exact hKcont
    · exact hKnonneg
    · exact hKmass
    · exact hKsupport
    · exact hρcont
    · exact hρlow
    · exact hα
    · exact hfast_cont
    · exact hfast_nonneg
    · exact hfast_le_one
    · exact hslow_cont
    · exact hslow_nonneg
    · exact hretained_pos
    · exact hretained_le
    · exact hρ₀
    · exact hδseed.le
    · exact hsmall_seed
    · exact hseed
    · exact hseed_carrying
    · exact hfront
    · exact hρ₀
    · exact hδrecover_pos.le
    · exact hδrecover_order
    · intro k j y hk _hj _hy
      exact (hNδ (Nseed + k + j) (by omega) y).le
    · intro k j y _hk hj hy
      apply henvironment_tail
      have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
      have hjradius : 0 ≤ (j : ℝ) * radius :=
        mul_nonneg hj0 hradius
      have hjcast : (j : ℝ) ≤ (P : ℝ) * (k : ℝ) := by
        exact_mod_cast hj
      have hcj :
          c * (j : ℝ) ≤ c * ((P : ℝ) * (k : ℝ)) :=
        mul_le_mul_of_nonneg_left hjcast hc
      have hblockAdvance :
          0 ≤
            ((a + θ) - c * (1 + (P : ℝ))) * (k : ℝ) :=
        mul_nonneg (by linarith) hk0
      dsimp [erodedInterval] at hy
      push_cast
      nlinarith [hy.1, hseed_ahead, hcj, hblockAdvance, hjradius]
    · exact hgrowth_recover
    · positivity
  have hcorridor :
      ∃ Kbase, ∀ (k : ℕ), Kbase ≤ k →
        ∀ x ∈ favorableCorridor c front ε (Nseed + k + P * k),
          perturbedCarrying α δrecover - η / 4 <
            fast (Nseed + k + P * k) x :=
    eventually_blockCorridor_lower_of_eroded_lower
      hleft hright heroded
  rcases hcorridor with ⟨Kbase, hKbase⟩
  refine ⟨Kbase, ?_⟩
  intro k hk x hx
  have hlower := hKbase k hk x hx
  have hupper := hfast_le_one (Nseed + k + P * k) x
  rw [abs_of_nonpos (sub_nonpos.mpr hupper)]
  unfold perturbedCarrying at hlower
  nlinarith

/-- All-time version of the multistep certificate.  The block construction is
run on `εwide`; finite-range propagation across the `P + 1` residue classes
then gives convergence on `εtarget`. -/
theorem correctedIntermediateSpeedExclusion_of_multistep_minorization_all_times
    {slow fast : ℕ → ℝ → ℝ}
    {K ρ : ℝ → ℝ}
    {α c front εwide εtarget radius ρ₀ Senv : ℝ}
    {Nseed P : ℕ}
    {δseed seed κ L R a b θ : ℝ}
    (hslow_extinction : UniformlyExtinct slow)
    (hfaststep :
      ∀ n x,
        fast (n + 1) x =
          heterogeneousCorrectedStep K ρ α c n (fast n) (slow n) x)
    (hKint : Integrable K) (hKcont : Continuous K)
    (hKnonneg : ∀ s, 0 ≤ K s) (hKmass : ∫ s, K s = 1)
    (hradius : 0 ≤ radius)
    (hKsupport : ∀ s, radius < |s| → K s = 0)
    (hKminor : ∀ s ∈ Set.Icc a b, κ ≤ K s)
    (hρcont : Continuous ρ) (hρlow : ∀ s, -1 < ρ s)
    (hα : 0 ≤ α)
    (hfast_cont : ∀ n, Continuous (fast n))
    (hfast_nonneg : ∀ n y, 0 ≤ fast n y)
    (hfast_le_one : ∀ n y, fast n y ≤ 1)
    (hslow_cont : ∀ n, Continuous (slow n))
    (hslow_nonneg : ∀ n y, 0 ≤ slow n y)
    (hc : 0 ≤ c) (hρ₀ : 0 < ρ₀)
    (henvironment_tail : ∀ s, Senv ≤ s → ρ₀ ≤ ρ s)
    (hεwide : 0 < εwide) (hεgap : εwide < εtarget)
    (hκ : 0 ≤ κ) (hθ : 0 ≤ θ)
    (hretained_pos : 0 < κ * θ)
    (hretained_le : κ * θ ≤ 1)
    (hwidth : b - a ≤ R - L)
    (hexpand : 2 * θ ≤ b - a)
    (hδseed : 0 < δseed)
    (hsmall_seed : α * δseed < 1)
    (hseed : 0 < seed)
    (hseed_carrying : seed ≤ perturbedCarrying α δseed)
    (hinitial_seed : ∀ y ∈ Set.Icc L R, seed ≤ fast Nseed y)
    (hslow_small_after_seed :
      ∀ n, Nseed ≤ n → ∀ y, slow n y ≤ δseed)
    (hseed_ahead : Senv ≤ L - c * (Nseed : ℝ))
    (hhabitat_block : c * (1 + (P : ℝ)) < a + θ)
    (hgrowth :
      1 < (κ * θ) * perturbedMultiplier ρ₀ α δseed ^ P)
    (hleft :
      a + θ + (P : ℝ) * radius <
        (c + εwide) * (1 + (P : ℝ)))
    (hright :
      (front - εwide) * (1 + (P : ℝ)) <
        b - θ - (P : ℝ) * radius) :
    UniformlyExtinct slow ∧
      UniformlyConvergesToOneInCorridor
        fast c front εtarget := by
  have hblock :=
    correctedIntermediateSpeedExclusion_of_multistep_minorization
      (slow := slow) (fast := fast) (K := K) (ρ := ρ)
      (α := α) (c := c) (front := front) (ε := εwide)
      (radius := radius) (ρ₀ := ρ₀) (Senv := Senv)
      (Nseed := Nseed) (P := P)
      (δseed := δseed) (seed := seed) (κ := κ)
      (L := L) (R := R) (a := a) (b := b) (θ := θ)
      hslow_extinction hfaststep hKint hKcont hKnonneg hKmass
      hradius hKsupport hKminor hρcont hρlow hα
      hfast_cont hfast_nonneg hfast_le_one
      hslow_cont hslow_nonneg hc hρ₀ henvironment_tail
      hκ hθ hretained_pos hretained_le hwidth hexpand
      hδseed hsmall_seed hseed hseed_carrying hinitial_seed
      hslow_small_after_seed hseed_ahead hhabitat_block
      hgrowth hleft hright
  refine ⟨hblock.1, ?_⟩
  apply blockCorridor_convergence_implies_all_times
    (focal := fast) (competitor := slow)
    (Kfun := K) (ρfun := ρ)
    (α := α) (c := c) (front := front)
    (εwide := εwide) (εtarget := εtarget)
    (radius := radius) (ρ₀ := ρ₀)
    (N := Nseed) (P := P)
    hfaststep hKint hKcont hKnonneg hKmass hradius hKsupport
    hρcont hρlow hα hfast_cont hfast_nonneg hfast_le_one
    hslow_cont hslow_nonneg hslow_extinction hc hρ₀
    ⟨Senv, henvironment_tail⟩ hεwide hεgap hblock.2

/-- The sequential transport--then--recovery certificate above cannot certify
a nonempty positive-width corridor for a compactly supported kernel.  If
`P = 0`, its growth inequality contradicts the retained-mass bound.  If
`P ≥ 1`, the recovery erosion consumes at least the whole rightward kernel
range, contradicting the required right-front inequality.  This is why the
finite-block theorem below uses simultaneous linear growth and dispersal. -/
theorem multistep_minorization_positive_corridor_infeasible
    {K : ℝ → ℝ}
    {radius κ a b θ ρ₀ α δ c front ε : ℝ}
    {P : ℕ}
    (hradius : 0 ≤ radius)
    (hKsupport : ∀ s, radius < |s| → K s = 0)
    (hKminor : ∀ s ∈ Set.Icc a b, κ ≤ K s)
    (hab : a ≤ b)
    (hθ : 0 ≤ θ)
    (hretained_pos : 0 < κ * θ)
    (hretained_le : κ * θ ≤ 1)
    (hgrowth :
      1 < (κ * θ) * perturbedMultiplier ρ₀ α δ ^ P)
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hcorridor : c + 2 * ε ≤ front)
    (hright :
      (front - ε) * (1 + (P : ℝ)) <
        b - θ - (P : ℝ) * radius) :
    False := by
  have hκpos : 0 < κ := by
    nlinarith [hretained_pos]
  have hb : b ≤ radius := by
    by_contra hnot
    have hrb : radius < b := lt_of_not_ge hnot
    have habs : radius < |b| :=
      hrb.trans_le (le_abs_self b)
    have hbzero := hKsupport b habs
    have hminor_b := hKminor b ⟨hab, le_rfl⟩
    rw [hbzero] at hminor_b
    linarith
  have hPne : P ≠ 0 := by
    intro hP
    subst P
    norm_num at hgrowth
    linarith
  have hPone : 1 ≤ P := Nat.one_le_iff_ne_zero.mpr hPne
  have hPcast : (1 : ℝ) ≤ (P : ℝ) := by
    exact_mod_cast hPone
  have hfront : 0 < front - ε := by
    linarith
  have hblock : 0 < 1 + (P : ℝ) := by
    linarith
  have hleft_positive :
      0 < (front - ε) * (1 + (P : ℝ)) :=
    mul_pos hfront hblock
  have hright_nonpositive :
      b - θ - (P : ℝ) * radius ≤ 0 := by
    nlinarith
  linarith

/-- **Corrected Theorem 2.2 under a finite linear block certificate.**

Unlike the one-step minorization theorem below, this statement imposes no
fixed-floor reproduction inequality on one kernel window.  All
multigeneration path counting is isolated in `cert`, a finite statement about
the linear growth-and-dispersal recursion.  Once that certificate is
available, the nonlinear IDE comparison, propagation to all time residues,
and convergence to one are proved here. -/
theorem correctedIntermediateSpeedExclusion_of_finiteBlockCertificate
    {slow fast : ℕ → ℝ → ℝ}
    {K ρ : ℝ → ℝ}
    {α c front εblock εfloor εtarget radius ρ₀ δ η slope seed
      L R leftAdvance rightAdvance minWidth : ℝ}
    {Nseed P : ℕ}
    (cert :
      FiniteBlockCertificate K slope η seed (P + 1)
        leftAdvance rightAdvance minWidth)
    (hadvance : leftAdvance ≤ rightAdvance)
    (hwidth : minWidth ≤ R - L)
    (hslow_extinction : UniformlyExtinct slow)
    (hfaststep :
      ∀ n x,
        fast (n + 1) x =
          heterogeneousCorrectedStep K ρ α c n (fast n) (slow n) x)
    (hKint : Integrable K) (hKcont : Continuous K)
    (hKnonneg : ∀ s, 0 ≤ K s) (hKmass : ∫ s, K s = 1)
    (hradius : 0 ≤ radius)
    (hKsupport : ∀ s, radius < |s| → K s = 0)
    (hρcont : Continuous ρ) (hρlow : ∀ s, -1 < ρ s)
    (hα : 0 ≤ α)
    (hfast_cont : ∀ n, Continuous (fast n))
    (hfast_nonneg : ∀ n y, 0 ≤ fast n y)
    (hfast_le_one : ∀ n y, fast n y ≤ 1)
    (hslow_cont : ∀ n, Continuous (slow n))
    (hslow_nonneg : ∀ n y, 0 ≤ slow n y)
    (hc : 0 ≤ c) (hρ₀ : 0 < ρ₀) (hδ : 0 < δ)
    (hη : 0 ≤ η) (hsmall : η + α * δ ≤ 1)
    (hslope : 0 ≤ slope)
    (hslope_le : slope ≤ favorableLowerSlope ρ₀ α δ η)
    (henvironment_tail : ∃ S, ∀ s, S ≤ s → ρ₀ ≤ ρ s)
    (hinitial : ∀ y ∈ Set.Icc L R, seed ≤ fast Nseed y)
    (hfavorable :
      ∀ (k t : ℕ), t < P + 1 → ∀ y,
        0 < finiteLinearOrbit K slope
          (intervalFloor seed
            (L + leftAdvance * (k : ℝ))
            (R + rightAdvance * (k : ℝ))) t y →
        slow (Nseed + (P + 1) * k + t) y ≤ δ ∧
        ρ₀ ≤ ρ
          (y - c * ((Nseed + (P + 1) * k + t : ℕ) : ℝ)))
    (hεblock : 0 < εblock)
    (hblock_floor_gap : εblock < εfloor)
    (hfloor_target_gap : εfloor < εtarget)
    (hcorridor : c + 2 * εtarget ≤ front)
    (hleft :
      (c + εblock) * ((P + 1 : ℕ) : ℝ) > leftAdvance)
    (hright :
      (front - εblock) * ((P + 1 : ℕ) : ℝ) < rightAdvance) :
    UniformlyExtinct slow ∧
      UniformlyConvergesToOneInCorridor fast c front εtarget := by
  have hblockfloor_raw :=
    finiteBlockCertificate_blockCorridor_floor
      (focal := fast) (competitor := slow)
      (Kfun := K) (ρfun := ρ)
      (α := α) (c := c) (ρ₀ := ρ₀) (δ := δ)
      (η := η) (slope := slope) (seed := seed)
      (L := L) (R := R)
      (leftAdvance := leftAdvance) (rightAdvance := rightAdvance)
      (minWidth := minWidth) (front := front) (ε := εblock)
      (N := Nseed) (block := P + 1)
      cert hadvance hwidth hfaststep hKint hKcont hKnonneg
      hρcont hρlow hα hfast_cont hfast_nonneg hfast_le_one
      hslow_cont hslow_nonneg hρ₀ hδ.le hη hsmall
      hslope hslope_le hinitial hfavorable hleft hright
  have hblockfloor :
      ∃ Kbase, ∀ (k : ℕ), Kbase ≤ k →
        ∀ x ∈ favorableCorridor c front εblock
            (Nseed + k + P * k),
          seed ≤ fast (Nseed + k + P * k) x := by
    rcases hblockfloor_raw with ⟨Kbase, hKbase⟩
    refine ⟨Kbase, ?_⟩
    intro k hk x hx
    have htime :
        Nseed + (P + 1) * k = Nseed + k + P * k := by ring
    rw [← htime] at hx ⊢
    exact hKbase k hk x hx
  have hηpos : 0 < η :=
    cert.seed_pos.trans_le cert.seed_le_eta
  have hsmall_strict : α * δ < 1 := by
    linarith
  have hseedq : seed ≤ perturbedCarrying α δ := by
    unfold perturbedCarrying
    linarith [cert.seed_le_eta]
  have hslow_eventually :
      ∃ Nδ, ∀ n, Nδ ≤ n → ∀ x, slow n x ≤ δ := by
    rcases hslow_extinction δ hδ with ⟨Nδ, hNδ⟩
    exact ⟨Nδ, fun n hn x => (hNδ n hn x).le⟩
  have hfloor_all :
      ∃ Nfloor, ∀ n, Nfloor ≤ n →
        ∀ x ∈ favorableCorridor c front εfloor n,
          seed ≤ fast n x :=
    blockCorridor_floor_implies_all_times
      (focal := fast) (competitor := slow)
      (Kfun := K) (ρfun := ρ)
      (α := α) (c := c) (front := front)
      (εwide := εblock) (εtarget := εfloor)
      (radius := radius) (ρ₀ := ρ₀) (δ := δ) (seed := seed)
      (N := Nseed) (P := P)
      hfaststep hKint hKcont hKnonneg hKmass hradius hKsupport
      hρcont hρlow hα hfast_cont hfast_nonneg hfast_le_one
      hslow_cont hslow_nonneg hslow_eventually hc hρ₀
      henvironment_tail hεblock hblock_floor_gap
      hδ hsmall_strict cert.seed_pos hseedq hblockfloor
  refine ⟨hslow_extinction, ?_⟩
  apply corridor_converges_to_one_of_positive_floor
    (focal := fast) (competitor := slow)
    (Kfun := K) (ρfun := ρ)
    (α := α) (c := c) (front := front)
    (εwide := εfloor) (εtarget := εtarget)
    (radius := radius) (ρ₀ := ρ₀) (floor := seed)
    hfaststep hKint hKcont hKnonneg hKmass
    hradius hKsupport hρcont hρlow hα
    hfast_cont hfast_nonneg hfast_le_one
    hslow_cont hslow_nonneg
    hc hρ₀ henvironment_tail
  · exact lt_trans hεblock hblock_floor_gap
  · exact hfloor_target_gap
  · exact hcorridor
  · exact cert.seed_pos
  · exact hfloor_all
  · intro d hd
    rcases hslow_extinction d hd with ⟨Nd, hNd⟩
    exact ⟨Nd, fun n hn x => (hNd n hn x).le⟩

/-- **Corrected Theorem 2.2 under a quantitative kernel certificate.**

The first conclusion is the independently proved extinction of the slow
component.  For the fast component, a compact interval seed and the kernel
minorization produce a positive floor in the wider corridor.  Compact support
then turns uniform extinction of the slow component into convergence of the
fast component to one in every strictly smaller corridor.

The certified front `front` is any speed satisfying the displayed
minorization inequalities; this theorem does not identify it with the sharp
variational speed `c₂*`. -/
theorem correctedIntermediateSpeedExclusion_of_minorization
    {slow fast : ℕ → ℝ → ℝ}
    {K ρ : ℝ → ℝ}
    {α c front εwide εtarget radius ρ₀ Senv : ℝ}
    {Nseed : ℕ}
    {δseed seed κ L R a b θ : ℝ}
    (hslow_extinction : UniformlyExtinct slow)
    (hfaststep :
      ∀ n x,
        fast (n + 1) x =
          heterogeneousCorrectedStep K ρ α c n (fast n) (slow n) x)
    (hKint : Integrable K) (hKcont : Continuous K)
    (hKnonneg : ∀ s, 0 ≤ K s) (hKmass : ∫ s, K s = 1)
    (hradius : 0 ≤ radius)
    (hKsupport : ∀ s, radius < |s| → K s = 0)
    (hKminor : ∀ s ∈ Set.Icc a b, κ ≤ K s)
    (hρcont : Continuous ρ) (hρlow : ∀ s, -1 < ρ s)
    (hα : 0 ≤ α)
    (hfast_cont : ∀ n, Continuous (fast n))
    (hfast_nonneg : ∀ n y, 0 ≤ fast n y)
    (hfast_le_one : ∀ n y, fast n y ≤ 1)
    (hslow_cont : ∀ n, Continuous (slow n))
    (hslow_nonneg : ∀ n y, 0 ≤ slow n y)
    (hc : 0 ≤ c) (hρ₀ : 0 < ρ₀)
    (henvironment_tail : ∀ s, Senv ≤ s → ρ₀ ≤ ρ s)
    (hεwide : 0 < εwide) (hεgap : εwide < εtarget)
    (hcorridor : c + 2 * εtarget ≤ front)
    (hκ : 0 ≤ κ) (hθ : 0 ≤ θ)
    (hwidth : b - a ≤ R - L)
    (hexpand : 2 * θ ≤ b - a)
    (hδseed : 0 < δseed) (hseed : 0 < seed)
    (hseed_subunit : seed + α * δseed ≤ 1)
    (hseed_fixed :
      seed ≤ κ * θ * correctedResponse ρ₀ α seed δseed)
    (hinitial_seed : ∀ y ∈ Set.Icc L R, seed ≤ fast Nseed y)
    /- The seed time is chosen after the slow species is uniformly below
    the fixed seed-stage perturbation `δseed`. -/
    (hslow_small_after_seed :
      ∀ n, Nseed ≤ n → ∀ y, slow n y ≤ δseed)
    /- At the seed time, the whole seed interval already lies in the
    favorable tail. Together with `c < a+θ`, this discharges the environment
    condition at every later expansion step. -/
    (hseed_ahead : Senv ≤ L - c * (Nseed : ℝ))
    (hleft_speed : c < a + θ ∧ a + θ < c + εwide)
    (hright_speed : front - εwide < b - θ) :
    UniformlyExtinct slow ∧
      UniformlyConvergesToOneInCorridor fast c front εtarget := by
  have hfloor :
      ∃ Nfloor, ∀ n, Nfloor ≤ n →
        ∀ y ∈ favorableCorridor c front εwide n,
          seed ≤ fast n y := by
    have hminor_competitor :
        ∀ (k : ℕ) (y : ℝ),
          y ∈ expandingSeedInterval L R a b θ k →
            slow (Nseed + k) y ≤ δseed := by
      intro k y _hy
      exact hslow_small_after_seed (Nseed + k) (by omega) y
    have hminor_environment :
        ∀ (k : ℕ) (y : ℝ),
          y ∈ expandingSeedInterval L R a b θ k →
            ρ₀ ≤ ρ (y - c * ((Nseed + k : ℕ) : ℝ)) := by
      intro k y hy
      apply henvironment_tail
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      have hadvance :
          0 ≤ ((a + θ) - c) * (k : ℝ) :=
        mul_nonneg (sub_nonneg.mpr hleft_speed.1.le) hk
      dsimp [expandingSeedInterval] at hy
      push_cast
      nlinarith [hy.1, hseed_ahead, hadvance]
    apply favorableCorridor_positive_floor_of_minorization
      (competitor := slow) (orbit := fast)
      (Kfun := K) (ρfun := ρ)
      (α := α) (c := c) (front := front) (ε := εwide)
      (ρ₀ := ρ₀) (δ := δseed) (z := seed)
      (κ := κ) (L := L) (R := R) (a := a) (b := b) (θ := θ)
      (N := Nseed)
    · intro k x
      simpa [Nat.add_assoc] using hfaststep (Nseed + k) x
    · exact hKint
    · exact hKcont
    · exact hKnonneg
    · exact hKminor
    · exact hρcont
    · exact hρlow
    · exact hα
    · exact hfast_cont
    · exact hfast_nonneg
    · exact hfast_le_one
    · exact hslow_cont
    · exact hslow_nonneg
    · exact hκ
    · exact hθ
    · exact hwidth
    · exact hexpand
    · exact hρ₀.le
    · exact hseed.le
    · exact hδseed.le
    · exact hseed_subunit
    · exact hseed_fixed
    · exact hinitial_seed
    · exact hminor_competitor
    · exact hminor_environment
    · exact hleft_speed.2
    · exact hright_speed
  have hslow_vanishes :
      ∀ δ, 0 < δ →
        ∃ Nδ, ∀ n, Nδ ≤ n → ∀ x, slow n x ≤ δ := by
    intro δ hδ
    rcases hslow_extinction δ hδ with ⟨Nδ, hNδ⟩
    exact ⟨Nδ, fun n hn x => (hNδ n hn x).le⟩
  refine ⟨hslow_extinction, ?_⟩
  exact corridor_converges_to_one_of_positive_floor
    hfaststep hKint hKcont hKnonneg hKmass hradius hKsupport
    hρcont hρlow hα hfast_cont hfast_nonneg hfast_le_one
    hslow_cont hslow_nonneg hc hρ₀ ⟨Senv, henvironment_tail⟩
    hεwide hεgap hcorridor hseed hfloor hslow_vanishes

/-- Assembly form of the certified exclusion theorem whose slow-component
input has exactly the bounded-continuous norm-limit shape produced by the
fast-habitat extinction theorem.  The norm-to-pointwise bridge is discharged
inside this theorem, so the first conclusion is no longer merely repeated as
an assumption. -/
theorem correctedIntermediateSpeedExclusion_of_bcf_extinction_and_minorization
    {slow : ℕ → ℝ →ᵇ ℝ} {fast : ℕ → ℝ → ℝ}
    {K ρ : ℝ → ℝ}
    {α c front εwide εtarget radius ρ₀ Senv : ℝ}
    {Nseed : ℕ}
    {δseed seed κ L R a b θ : ℝ}
    (hslow_norm :
      Tendsto (fun n => ‖slow n‖) atTop (𝓝 0))
    (hfaststep :
      ∀ n x,
        fast (n + 1) x =
          heterogeneousCorrectedStep K ρ α c n
            (fast n) (fun y => slow n y) x)
    (hKint : Integrable K) (hKcont : Continuous K)
    (hKnonneg : ∀ s, 0 ≤ K s) (hKmass : ∫ s, K s = 1)
    (hradius : 0 ≤ radius)
    (hKsupport : ∀ s, radius < |s| → K s = 0)
    (hKminor : ∀ s ∈ Set.Icc a b, κ ≤ K s)
    (hρcont : Continuous ρ) (hρlow : ∀ s, -1 < ρ s)
    (hα : 0 ≤ α)
    (hfast_cont : ∀ n, Continuous (fast n))
    (hfast_nonneg : ∀ n y, 0 ≤ fast n y)
    (hfast_le_one : ∀ n y, fast n y ≤ 1)
    (hslow_nonneg : ∀ n y, 0 ≤ slow n y)
    (hc : 0 ≤ c) (hρ₀ : 0 < ρ₀)
    (henvironment_tail : ∀ s, Senv ≤ s → ρ₀ ≤ ρ s)
    (hεwide : 0 < εwide) (hεgap : εwide < εtarget)
    (hcorridor : c + 2 * εtarget ≤ front)
    (hκ : 0 ≤ κ) (hθ : 0 ≤ θ)
    (hwidth : b - a ≤ R - L)
    (hexpand : 2 * θ ≤ b - a)
    (hδseed : 0 < δseed) (hseed : 0 < seed)
    (hseed_subunit : seed + α * δseed ≤ 1)
    (hseed_fixed :
      seed ≤ κ * θ * correctedResponse ρ₀ α seed δseed)
    (hinitial_seed : ∀ y ∈ Set.Icc L R, seed ≤ fast Nseed y)
    (hslow_small_after_seed :
      ∀ n, Nseed ≤ n → ∀ y, slow n y ≤ δseed)
    (hseed_ahead : Senv ≤ L - c * (Nseed : ℝ))
    (hleft_speed : c < a + θ ∧ a + θ < c + εwide)
    (hright_speed : front - εwide < b - θ) :
    Tendsto (fun n => ‖slow n‖) atTop (𝓝 0) ∧
      UniformlyConvergesToOneInCorridor fast c front εtarget := by
  have hslow_extinction :
      UniformlyExtinct (fun n x => slow n x) :=
    uniformlyExtinct_of_bcf_norm_tendsto_zero
      slow hslow_nonneg hslow_norm
  have hcertified :=
    correctedIntermediateSpeedExclusion_of_minorization
      (slow := fun n x => slow n x)
      (fast := fast) (K := K) (ρ := ρ)
      (α := α) (c := c) (front := front)
      (εwide := εwide) (εtarget := εtarget)
      (radius := radius) (ρ₀ := ρ₀) (Senv := Senv)
      (Nseed := Nseed) (δseed := δseed) (seed := seed)
      (κ := κ) (L := L) (R := R) (a := a) (b := b) (θ := θ)
      hslow_extinction hfaststep
      hKint hKcont hKnonneg hKmass hradius hKsupport hKminor
      hρcont hρlow hα
      hfast_cont hfast_nonneg hfast_le_one
      (fun n => (slow n).continuous) hslow_nonneg
      hc hρ₀ henvironment_tail
      hεwide hεgap hcorridor hκ hθ hwidth hexpand
      hδseed hseed hseed_subunit hseed_fixed hinitial_seed
      hslow_small_after_seed hseed_ahead hleft_speed hright_speed
  exact ⟨hslow_norm, hcertified.2⟩


section AxiomAudit

#print axioms heterogeneousCorrectedStep_ge_compactSupport_floor
#print axioms bhOrbit_le_on_erodedInterval
#print axioms eventually_targetCorridor_subset_eroded
#print axioms favorableCorridor_positive_floor_of_minorization
#print axioms corridor_converges_to_one_of_positive_floor
#print axioms uniformlyExtinct_of_bcf_norm_tendsto_zero
#print axioms multistep_minorization_positive_corridor_infeasible
#print axioms correctedIntermediateSpeedExclusion_of_finiteBlockCertificate
#print axioms correctedIntermediateSpeedExclusion_of_minorization
#print axioms correctedIntermediateSpeedExclusion_of_bcf_extinction_and_minorization

end AxiomAudit

end

end ShenWork.Liang
