/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import ShenWork.Liang.ScalarPersistence
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
#print axioms correctedIntermediateSpeedExclusion_of_minorization
#print axioms correctedIntermediateSpeedExclusion_of_bcf_extinction_and_minorization

end AxiomAudit

end

end ShenWork.Liang
