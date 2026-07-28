/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import ShenWork.Liang.IntermediateSpeedExclusion
import ShenWork.Liang.WeakCompetitionCoexistence

/-!
# A finite-range spatial certificate for weak-competition coexistence

This file discharges the fixed-depth comparison hypothesis used in
`WeakCompetitionCoexistence` under strong, directly checkable spatial
assumptions:

* both dispersal kernels are continuous compactly supported probability
  densities, with a common support radius;
* each environment is exactly equal to its favorable value on a right tail;
* both state components remain in the unit square and satisfy the corrected
  two-species IDE recurrence;
* both components have an eventual positive floor on a slightly wider
  favorable corridor.

Finite kernel range makes a fixed number of predecessors stay inside an
eroded corridor.  Exact constancy of the environments there then gives an
exact homogeneous seeded-envelope comparison.  Corridor geometry converts
this finite-horizon statement into uniform fixed-depth comparison on the
smaller corridor, and the abstract squeezing theorem supplies coexistence.
-/

open Filter MeasureTheory Set Topology

namespace ShenWork.Liang

noncomputable section

/-! ## Checkable spatial data -/

/-- A continuous probability density supported in the common interval
`[-radius, radius]`. -/
structure CompactProbabilityKernel (K : ℝ → ℝ) (radius : ℝ) : Prop where
  radius_nonneg : 0 ≤ radius
  integrable : Integrable K
  continuous : Continuous K
  nonneg : ∀ z, 0 ≤ K z
  mass_one : ∫ z, K z = 1
  support : ∀ z, radius < |z| → K z = 0

/-- An environment that is exactly homogeneous on a prescribed right tail. -/
structure ExactFavorableTail
    (ρ : ℝ → ℝ) (ρplus threshold : ℝ) : Prop where
  continuous : Continuous ρ
  lower : ∀ s, -1 < ρ s
  eq_favorable : ∀ s, threshold ≤ s → ρ s = ρplus

/-- A continuous unit-square orbit of the corrected competitive IDE. -/
structure CorrectedTwoSpeciesOrbit
    (K₁ K₂ ρ₁ ρ₂ : ℝ → ℝ) (α₁ α₂ c : ℝ)
    (u v : ℕ → ℝ → ℝ) : Prop where
  u_continuous : ∀ n, Continuous (u n)
  v_continuous : ∀ n, Continuous (v n)
  u_nonneg : ∀ n x, 0 ≤ u n x
  u_le_one : ∀ n x, u n x ≤ 1
  v_nonneg : ∀ n x, 0 ≤ v n x
  v_le_one : ∀ n x, v n x ≤ 1
  u_step : ∀ n x,
    u (n + 1) x =
      heterogeneousCorrectedStep K₁ ρ₁ α₁ c n (u n) (v n) x
  v_step : ∀ n x,
    v (n + 1) x =
      heterogeneousCorrectedStep K₂ ρ₂ α₂ c n (v n) (u n) x

/-! ## One exact favorable convolution step -/

/-- A compactly supported probability convolution maps a local competitive
rectangle into the corresponding homogeneous favorable response rectangle. -/
theorem heterogeneousCorrectedStep_mem_favorable_rectangle
    {K ρ focal competitor : ℝ → ℝ}
    {α c x radius ρplus focalLower focalUpper
      competitorLower competitorUpper : ℝ} {n : ℕ}
    (hK : CompactProbabilityKernel K radius)
    (hρcont : Continuous ρ)
    (hρlow : ∀ s, -1 < ρ s)
    (hρplus : -1 < ρplus)
    (hα : 0 ≤ α)
    (hfocal_cont : Continuous focal)
    (hfocal_nonneg : ∀ y, 0 ≤ focal y)
    (hfocal_le_one : ∀ y, focal y ≤ 1)
    (hcompetitor_cont : Continuous competitor)
    (hcompetitor_nonneg : ∀ y, 0 ≤ competitor y)
    (hfocalLower : 0 ≤ focalLower)
    (hcompetitorLower : 0 ≤ competitorLower)
    (henvironment : ∀ y, |x - y| ≤ radius →
      ρ (y - c * (n : ℝ)) = ρplus)
    (hlocal : ∀ y, |x - y| ≤ radius →
      focalLower ≤ focal y ∧ focal y ≤ focalUpper ∧
        competitorLower ≤ competitor y ∧ competitor y ≤ competitorUpper) :
    correctedResponse ρplus α focalLower competitorUpper ≤
        heterogeneousCorrectedStep K ρ α c n focal competitor x ∧
      heterogeneousCorrectedStep K ρ α c n focal competitor x ≤
        correctedResponse ρplus α focalUpper competitorLower := by
  let lowerResponse : ℝ :=
    correctedResponse ρplus α focalLower competitorUpper
  let upperResponse : ℝ :=
    correctedResponse ρplus α focalUpper competitorLower
  let actualIntegrand : ℝ → ℝ := fun y =>
    K (x - y) *
      correctedResponse (ρ (y - c * (n : ℝ))) α
        (focal y) (competitor y)
  have hlowerIntegrable :
      Integrable (fun y => K (x - y) * lowerResponse) :=
    (hK.integrable.comp_sub_left x).mul_const lowerResponse
  have hupperIntegrable :
      Integrable (fun y => K (x - y) * upperResponse) :=
    (hK.integrable.comp_sub_left x).mul_const upperResponse
  have hactualIntegrable : Integrable actualIntegrand := by
    exact heterogeneousCorrectedIntegrable
      hK.integrable hK.continuous hρcont hρlow hα
      hfocal_cont hfocal_nonneg hfocal_le_one
      hcompetitor_cont hcompetitor_nonneg
  have hlowerPointwise :
      ∀ y, K (x - y) * lowerResponse ≤ actualIntegrand y := by
    intro y
    by_cases hxy : |x - y| ≤ radius
    · have hs := hlocal y hxy
      have henv :
          ρ (y - c * (n : ℝ)) = ρplus :=
        henvironment y hxy
      dsimp [lowerResponse, actualIntegrand]
      rw [henv]
      apply mul_le_mul_of_nonneg_left _ (hK.nonneg _)
      calc
        correctedResponse ρplus α focalLower competitorUpper ≤
            correctedResponse ρplus α focalLower (competitor y) :=
          correctedResponse_antitone_competitor
            hρplus hα hfocalLower
            (hcompetitor_nonneg y) hs.2.2.2
        _ ≤ correctedResponse ρplus α (focal y) (competitor y) :=
          correctedResponse_monotone_focal
            hρplus hα hfocalLower hs.1 (hcompetitor_nonneg y)
    · have hout : radius < |x - y| := lt_of_not_ge hxy
      dsimp [lowerResponse, actualIntegrand]
      rw [hK.support _ hout, zero_mul, zero_mul]
  have hupperPointwise :
      ∀ y, actualIntegrand y ≤ K (x - y) * upperResponse := by
    intro y
    by_cases hxy : |x - y| ≤ radius
    · have hs := hlocal y hxy
      have henv :
          ρ (y - c * (n : ℝ)) = ρplus :=
        henvironment y hxy
      dsimp [upperResponse, actualIntegrand]
      rw [henv]
      apply mul_le_mul_of_nonneg_left _ (hK.nonneg _)
      calc
        correctedResponse ρplus α (focal y) (competitor y) ≤
            correctedResponse ρplus α (focal y) competitorLower :=
          correctedResponse_antitone_competitor
            hρplus hα (hfocal_nonneg y)
            hcompetitorLower hs.2.2.1
        _ ≤ correctedResponse ρplus α focalUpper competitorLower :=
          correctedResponse_monotone_focal
            hρplus hα (hfocal_nonneg y) hs.2.1 hcompetitorLower
    · have hout : radius < |x - y| := lt_of_not_ge hxy
      dsimp [upperResponse, actualIntegrand]
      rw [hK.support _ hout, zero_mul, zero_mul]
  have hlowerIntegral :
      lowerResponse =
        ∫ y, K (x - y) * lowerResponse := by
    rw [integral_mul_const,
      integral_sub_left_eq_self K (volume : Measure ℝ) x,
      hK.mass_one, one_mul]
  have hupperIntegral :
      (∫ y, K (x - y) * upperResponse) =
        upperResponse := by
    rw [integral_mul_const,
      integral_sub_left_eq_self K (volume : Measure ℝ) x,
      hK.mass_one, one_mul]
  constructor
  · change lowerResponse ≤ ∫ y, actualIntegrand y
    rw [hlowerIntegral]
    exact integral_mono hlowerIntegrable hactualIntegrable hlowerPointwise
  · change (∫ y, actualIntegrand y) ≤ upperResponse
    rw [← hupperIntegral]
    exact integral_mono hactualIntegrable hupperIntegrable hupperPointwise

/-! ## Exact finite-depth seeded-envelope comparison -/

/-- Pointwise membership in a competitive homogeneous rectangle. -/
def SeededEnvelope.Contains
    (e : SeededEnvelope) (u v : ℝ) : Prop :=
  e.uLower ≤ u ∧ u ≤ e.uUpper ∧
    e.vLower ≤ v ∧ v ≤ e.vUpper

/-- Starting from positive floors on an interval, the corrected spatial orbit
is trapped exactly by the `j`-th seeded homogeneous envelope on the interval
eroded by `j` common kernel radii.  The environmental hypotheses refer only
to the finite predecessor cone used by the proof. -/
theorem seededEnvelopeOrbit_contains_on_erodedInterval
    {K₁ K₂ ρ₁ ρ₂ : ℝ → ℝ}
    {ρ₁plus ρ₂plus α₁ α₂ c radius ℓu ℓv L R S₁ S₂ : ℝ}
    {u v : ℕ → ℝ → ℝ} {N horizon : ℕ}
    (hK₁ : CompactProbabilityKernel K₁ radius)
    (hK₂ : CompactProbabilityKernel K₂ radius)
    (hρ₁tail : ExactFavorableTail ρ₁ ρ₁plus S₁)
    (hρ₂tail : ExactFavorableTail ρ₂ ρ₂plus S₂)
    (hρ₁plus : 0 < ρ₁plus) (hρ₂plus : 0 < ρ₂plus)
    (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂)
    (hℓu : 0 < ℓu) (hℓv : 0 < ℓv)
    (huFloor : ℓu + α₁ ≤ 1)
    (hvFloor : ℓv + α₂ ≤ 1)
    (horbit :
      CorrectedTwoSpeciesOrbit K₁ K₂ ρ₁ ρ₂ α₁ α₂ c u v)
    (hseed : ∀ y ∈ Set.Icc L R,
      ℓu ≤ u N y ∧ ℓv ≤ v N y)
    (henvironment₁ :
      ∀ (j : ℕ) (y : ℝ),
        j ≤ horizon →
        y ∈ erodedInterval L R radius j →
          ρ₁ (y - c * ((N + j : ℕ) : ℝ)) = ρ₁plus)
    (henvironment₂ :
      ∀ (j : ℕ) (y : ℝ),
        j ≤ horizon →
        y ∈ erodedInterval L R radius j →
          ρ₂ (y - c * ((N + j : ℕ) : ℝ)) = ρ₂plus) :
    ∀ (j : ℕ) (x : ℝ),
      j ≤ horizon →
      x ∈ erodedInterval L R radius j →
        (seededEnvelopeOrbit
          ρ₁plus ρ₂plus α₁ α₂ ℓu ℓv j).Contains
            (u (N + j) x) (v (N + j) x) := by
  intro j
  induction j with
  | zero =>
      intro x _hj hx
      rw [erodedInterval_zero] at hx
      have hs := hseed x hx
      constructor
      · simpa [seededEnvelopeOrbit, seededInitialEnvelope] using hs.1
      constructor
      · simpa [seededEnvelopeOrbit, seededInitialEnvelope] using
          horbit.u_le_one N x
      constructor
      · simpa [seededEnvelopeOrbit, seededInitialEnvelope] using hs.2
      · simpa [seededEnvelopeOrbit, seededInitialEnvelope] using
          horbit.v_le_one N x
  | succ j ih =>
      intro x hjhorizon hx
      have hjhorizon' : j ≤ horizon := by omega
      let e : SeededEnvelope :=
        seededEnvelopeOrbit ρ₁plus ρ₂plus α₁ α₂ ℓu ℓv j
      have heValid : e.Valid := by
        exact seededEnvelopeOrbit_valid
          hρ₁plus hρ₂plus hα₁ hα₂ hℓu hℓv
          huFloor hvFloor j
      have huStep :
          correctedResponse ρ₁plus α₁ e.uLower e.vUpper ≤
              heterogeneousCorrectedStep K₁ ρ₁ α₁ c (N + j)
                (u (N + j)) (v (N + j)) x ∧
            heterogeneousCorrectedStep K₁ ρ₁ α₁ c (N + j)
                (u (N + j)) (v (N + j)) x ≤
              correctedResponse ρ₁plus α₁ e.uUpper e.vLower := by
        apply heterogeneousCorrectedStep_mem_favorable_rectangle
          hK₁ hρ₁tail.continuous hρ₁tail.lower
          (by linarith) hα₁
          (horbit.u_continuous _) (horbit.u_nonneg _)
          (horbit.u_le_one _) (horbit.v_continuous _)
          (horbit.v_nonneg _)
          heValid.1.le heValid.2.2.2.1.le
        · intro y hxy
          have hy : y ∈ erodedInterval L R radius j :=
            predecessor_mem_erodedInterval hx hxy
          exact henvironment₁ j y hjhorizon' hy
        · intro y hxy
          have hy : y ∈ erodedInterval L R radius j :=
            predecessor_mem_erodedInterval hx hxy
          exact ih y hjhorizon' hy
      have hvStep :
          correctedResponse ρ₂plus α₂ e.vLower e.uUpper ≤
              heterogeneousCorrectedStep K₂ ρ₂ α₂ c (N + j)
                (v (N + j)) (u (N + j)) x ∧
            heterogeneousCorrectedStep K₂ ρ₂ α₂ c (N + j)
                (v (N + j)) (u (N + j)) x ≤
              correctedResponse ρ₂plus α₂ e.vUpper e.uLower := by
        apply heterogeneousCorrectedStep_mem_favorable_rectangle
          hK₂ hρ₂tail.continuous hρ₂tail.lower
          (by linarith) hα₂
          (horbit.v_continuous _) (horbit.v_nonneg _)
          (horbit.v_le_one _) (horbit.u_continuous _)
          (horbit.u_nonneg _)
          heValid.2.2.2.1.le heValid.1.le
        · intro y hxy
          have hy : y ∈ erodedInterval L R radius j :=
            predecessor_mem_erodedInterval hx hxy
          exact henvironment₂ j y hjhorizon' hy
        · intro y hxy
          have hy : y ∈ erodedInterval L R radius j :=
            predecessor_mem_erodedInterval hx hxy
          have hs := ih y hjhorizon' hy
          exact ⟨hs.2.2.1, hs.2.2.2, hs.1, hs.2.1⟩
      have huRecurrence :
          u (N + (j + 1)) x =
            heterogeneousCorrectedStep K₁ ρ₁ α₁ c (N + j)
              (u (N + j)) (v (N + j)) x := by
        simpa [Nat.add_assoc] using horbit.u_step (N + j) x
      have hvRecurrence :
          v (N + (j + 1)) x =
            heterogeneousCorrectedStep K₂ ρ₂ α₂ c (N + j)
              (v (N + j)) (u (N + j)) x := by
        simpa [Nat.add_assoc] using horbit.v_step (N + j) x
      rw [seededEnvelopeOrbit_succ]
      change
        correctedResponse ρ₁plus α₁ e.uLower e.vUpper ≤
            u (N + (j + 1)) x ∧
          u (N + (j + 1)) x ≤
            correctedResponse ρ₁plus α₁ e.uUpper e.vLower ∧
          correctedResponse ρ₂plus α₂ e.vLower e.uUpper ≤
            v (N + (j + 1)) x ∧
          v (N + (j + 1)) x ≤
            correctedResponse ρ₂plus α₂ e.vUpper e.uLower
      rw [huRecurrence, hvRecurrence]
      exact ⟨huStep.1, huStep.2, hvStep.1, hvStep.2⟩

/-! ## From finite predecessor cones to a moving corridor -/

/-- For every fixed depth, an eventual positive floor in the wider corridor
gives exact seeded-envelope bounds in the smaller corridor.  The target time
is written as `n + m` to expose the finite predecessor cone based at `n`. -/
theorem eventually_seededEnvelopeOrbit_contains_on_targetCorridor
    {K₁ K₂ ρ₁ ρ₂ : ℝ → ℝ}
    {ρ₁plus ρ₂plus α₁ α₂ c front εwide εtarget radius
      ℓu ℓv persistenceU persistenceV S₁ S₂ : ℝ}
    {u v : ℕ → ℝ → ℝ} {m : ℕ}
    (hK₁ : CompactProbabilityKernel K₁ radius)
    (hK₂ : CompactProbabilityKernel K₂ radius)
    (hρ₁tail : ExactFavorableTail ρ₁ ρ₁plus S₁)
    (hρ₂tail : ExactFavorableTail ρ₂ ρ₂plus S₂)
    (hρ₁plus : 0 < ρ₁plus) (hρ₂plus : 0 < ρ₂plus)
    (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂)
    (hc : 0 ≤ c)
    (hεwide : 0 < εwide) (hεgap : εwide < εtarget)
    (hℓu : 0 < ℓu) (hℓv : 0 < ℓv)
    (hℓuPersistence : ℓu ≤ persistenceU)
    (hℓvPersistence : ℓv ≤ persistenceV)
    (huFloor : ℓu + α₁ ≤ 1)
    (hvFloor : ℓv + α₂ ≤ 1)
    (horbit :
      CorrectedTwoSpeciesOrbit K₁ K₂ ρ₁ ρ₂ α₁ α₂ c u v)
    (hpersistence :
      ∀ᶠ n : ℕ in atTop,
        ∀ x ∈ favorableCorridor c front εwide n,
          persistenceU ≤ u n x ∧ persistenceV ≤ v n x) :
    ∀ᶠ n : ℕ in atTop,
      ∀ x ∈ favorableCorridor c front εtarget (n + m),
        (seededEnvelopeOrbit
          ρ₁plus ρ₂plus α₁ α₂ ℓu ℓv m).Contains
            (u (n + m) x) (v (n + m) x) := by
  have htarget :=
    eventually_targetCorridor_subset_eroded
      (c := c) (front := front)
      (εwide := εwide) (εtarget := εtarget)
      (radius := radius) (k := m) hεgap
  have hahead₁ :=
    eventually_erodedFavorableCorridor_ahead_of
      (c := c) (front := front) (εwide := εwide)
      (radius := radius) (S := S₁) (k := m)
      hc hεwide hK₁.radius_nonneg
  have hahead₂ :=
    eventually_erodedFavorableCorridor_ahead_of
      (c := c) (front := front) (εwide := εwide)
      (radius := radius) (S := S₂) (k := m)
      hc hεwide hK₂.radius_nonneg
  filter_upwards
    [hpersistence, htarget, hahead₁, hahead₂] with
      n hnPersistence hnTarget hnAhead₁ hnAhead₂
  intro x hx
  let L : ℝ := (c + εwide) * (n : ℝ)
  let R : ℝ := (front - εwide) * (n : ℝ)
  have hxEroded : x ∈ erodedInterval L R radius m := by
    apply hnTarget
    exact hx
  apply seededEnvelopeOrbit_contains_on_erodedInterval
      (K₁ := K₁) (K₂ := K₂) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
      (ρ₁plus := ρ₁plus) (ρ₂plus := ρ₂plus)
      (α₁ := α₁) (α₂ := α₂) (c := c)
      (radius := radius) (ℓu := ℓu) (ℓv := ℓv)
      (L := L) (R := R) (S₁ := S₁) (S₂ := S₂)
      (u := u) (v := v) (N := n) (horizon := m)
      hK₁ hK₂ hρ₁tail hρ₂tail
      hρ₁plus hρ₂plus hα₁ hα₂
      hℓu hℓv huFloor hvFloor horbit
  · intro y hy
    have hyCorridor :
        y ∈ favorableCorridor c front εwide n := by
      simpa [favorableCorridor, L, R] using hy
    have hp := hnPersistence y hyCorridor
    exact
      ⟨hℓuPersistence.trans hp.1,
        hℓvPersistence.trans hp.2⟩
  · intro j y hj hy
    apply hρ₁tail.eq_favorable
    apply hnAhead₁ j hj y
    simpa [L, R] using hy
  · intro j y hj hy
    apply hρ₂tail.eq_favorable
    apply hnAhead₂ j hj y
    simpa [L, R] using hy
  · exact le_rfl
  · exact hxEroded

/-- Compact support, an exact favorable tail, and eventual positive floors
discharge the abstract uniform fixed-depth comparison interface. -/
theorem eventuallyUniformlyTrappedByEverySeededEnvelope_of_compactSupport
    {K₁ K₂ ρ₁ ρ₂ : ℝ → ℝ}
    {ρ₁plus ρ₂plus α₁ α₂ c front εwide εtarget radius
      ℓu ℓv persistenceU persistenceV S₁ S₂ : ℝ}
    {u v : ℕ → ℝ → ℝ}
    (hK₁ : CompactProbabilityKernel K₁ radius)
    (hK₂ : CompactProbabilityKernel K₂ radius)
    (hρ₁tail : ExactFavorableTail ρ₁ ρ₁plus S₁)
    (hρ₂tail : ExactFavorableTail ρ₂ ρ₂plus S₂)
    (hρ₁plus : 0 < ρ₁plus) (hρ₂plus : 0 < ρ₂plus)
    (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂)
    (hc : 0 ≤ c)
    (hεwide : 0 < εwide) (hεgap : εwide < εtarget)
    (hℓu : 0 < ℓu) (hℓv : 0 < ℓv)
    (hℓuPersistence : ℓu ≤ persistenceU)
    (hℓvPersistence : ℓv ≤ persistenceV)
    (huFloor : ℓu + α₁ ≤ 1)
    (hvFloor : ℓv + α₂ ≤ 1)
    (horbit :
      CorrectedTwoSpeciesOrbit K₁ K₂ ρ₁ ρ₂ α₁ α₂ c u v)
    (hpersistence :
      ∀ᶠ n : ℕ in atTop,
        ∀ x ∈ favorableCorridor c front εwide n,
          persistenceU ≤ u n x ∧ persistenceV ≤ v n x) :
    EventuallyUniformlyTrappedByEverySeededEnvelope
      ρ₁plus ρ₂plus α₁ α₂ ℓu ℓv u v
      (favorableCorridor c front εtarget) := by
  intro m ε hε
  have hshifted :=
    eventually_seededEnvelopeOrbit_contains_on_targetCorridor
      (m := m)
      hK₁ hK₂ hρ₁tail hρ₂tail hρ₁plus hρ₂plus
      hα₁ hα₂ hc hεwide hεgap hℓu hℓv
      hℓuPersistence hℓvPersistence huFloor hvFloor
      horbit hpersistence
  rcases eventually_atTop.1 hshifted with ⟨Nbase, hNbase⟩
  refine eventually_atTop.2 ⟨Nbase + m, ?_⟩
  intro t ht x hx
  let n : ℕ := t - m
  have hmt : m ≤ t := by omega
  have hnbase : Nbase ≤ n := by
    dsimp [n]
    omega
  have hnm : n + m = t := by
    dsimp [n]
    omega
  have hs :
      (seededEnvelopeOrbit
        ρ₁plus ρ₂plus α₁ α₂ ℓu ℓv m).Contains
          (u t x) (v t x) := by
    simpa [hnm] using
      hNbase n hnbase x (by simpa [hnm] using hx)
  exact
    ⟨by linarith [hs.1],
      by linarith [hs.2.1],
      by linarith [hs.2.2.1],
      by linarith [hs.2.2.2]⟩

/-! ## Certified spatial coexistence -/

/-- A complete weak-competition coexistence theorem under finite-range,
exact-tail, and positive-corridor-floor certificates.  Unlike the abstract
interface theorem, every spatial hypothesis here is stated directly in terms
of the kernels, environments, state bounds, recurrence, and persistence. -/
theorem certified_weak_competition_spatial_coexistence
    {K₁ K₂ ρ₁ ρ₂ : ℝ → ℝ}
    {ρ₁plus ρ₂plus α₁ α₂ c front εwide εtarget radius
      persistenceU persistenceV S₁ S₂ : ℝ}
    {u v : ℕ → ℝ → ℝ}
    (hK₁ : CompactProbabilityKernel K₁ radius)
    (hK₂ : CompactProbabilityKernel K₂ radius)
    (hρ₁tail : ExactFavorableTail ρ₁ ρ₁plus S₁)
    (hρ₂tail : ExactFavorableTail ρ₂ ρ₂plus S₂)
    (hρ₁plus : 0 < ρ₁plus) (hρ₂plus : 0 < ρ₂plus)
    (hα₁0 : 0 < α₁) (hα₁1 : α₁ < 1)
    (hα₂0 : 0 < α₂) (hα₂1 : α₂ < 1)
    (hc : 0 ≤ c)
    (hεwide : 0 < εwide) (hεgap : εwide < εtarget)
    (hcorridor : c + 2 * εtarget ≤ front)
    (hpersistenceU : 0 < persistenceU)
    (hpersistenceV : 0 < persistenceV)
    (horbit :
      CorrectedTwoSpeciesOrbit K₁ K₂ ρ₁ ρ₂ α₁ α₂ c u v)
    (hpersistence :
      ∀ᶠ n : ℕ in atTop,
        ∀ x ∈ favorableCorridor c front εwide n,
          persistenceU ≤ u n x ∧ persistenceV ≤ v n x) :
    (∀ n, (favorableCorridor c front εtarget n).Nonempty) ∧
      UniformlyTendstoOnMovingSets u
        (favorableCorridor c front εtarget)
        (coexistenceU α₁ α₂) ∧
      UniformlyTendstoOnMovingSets v
        (favorableCorridor c front εtarget)
        (coexistenceV α₁ α₂) := by
  obtain ⟨ℓu, hℓu, hℓuPersistence, huFloor⟩ :=
    exists_admissible_seed_floor hα₁1 hpersistenceU
  obtain ⟨ℓv, hℓv, hℓvPersistence, hvFloor⟩ :=
    exists_admissible_seed_floor hα₂1 hpersistenceV
  have htrap :
      EventuallyUniformlyTrappedByEverySeededEnvelope
        ρ₁plus ρ₂plus α₁ α₂ ℓu ℓv u v
        (favorableCorridor c front εtarget) :=
    eventuallyUniformlyTrappedByEverySeededEnvelope_of_compactSupport
      hK₁ hK₂ hρ₁tail hρ₂tail
      hρ₁plus hρ₂plus hα₁0.le hα₂0.le
      hc hεwide hεgap hℓu hℓv
      hℓuPersistence hℓvPersistence huFloor hvFloor
      horbit hpersistence
  have hconvergence :=
    uniformly_tendsto_coexistence_of_fixed_depth_comparison
      hρ₁plus hρ₂plus
      hα₁0 hα₁1 hα₂0 hα₂1
      hℓu hℓv huFloor hvFloor htrap
  exact
    ⟨fun n => favorableCorridor_nonempty hcorridor n,
      hconvergence.1, hconvergence.2⟩

/-! ## Producing both persistence floors from kernel minorization -/

/-- Per-species quantitative data for producing a positive floor on a moving
corridor.  The compact seed and kernel-window minorization feed
`favorableCorridor_positive_floor_of_minorization`; `expanding_ahead` is the
explicit geometric certificate that every point used in that induction lies
in the exact favorable tail. -/
structure CorridorFloorCertificate
    (K : ℝ → ℝ) (ρplus α c front ε S : ℝ)
    (orbit : ℕ → ℝ → ℝ) where
  startTime : ℕ
  floor : ℝ
  kappa : ℝ
  seedLeft : ℝ
  seedRight : ℝ
  displacementLeft : ℝ
  displacementRight : ℝ
  windowLength : ℝ
  floor_pos : 0 < floor
  kappa_nonneg : 0 ≤ kappa
  windowLength_nonneg : 0 ≤ windowLength
  kernel_minorization :
    ∀ z ∈ Set.Icc displacementLeft displacementRight, kappa ≤ K z
  displacement_window_fits_seed :
    displacementRight - displacementLeft ≤ seedRight - seedLeft
  expanding_width :
    2 * windowLength ≤ displacementRight - displacementLeft
  floor_subunit : floor + α * 1 ≤ 1
  floor_reproduces :
    floor ≤
      kappa * windowLength *
        correctedResponse ρplus α floor 1
  initial_seed :
    ∀ y ∈ Set.Icc seedLeft seedRight,
      floor ≤ orbit startTime y
  expanding_ahead :
    ∀ (k : ℕ) (y : ℝ),
      y ∈ expandingSeedInterval
        seedLeft seedRight displacementLeft displacementRight
        windowLength k →
      S ≤ y - c * ((startTime + k : ℕ) : ℝ)
  left_speed :
    displacementLeft + windowLength < c + ε
  right_speed :
    front - ε < displacementRight - windowLength

/-- The one-step certificate is deliberately stronger than weak competition.
For a probability kernel it forces both `α < 1 / 2` and favorable growth
strictly larger than one.  Thus the certificate below is an optional
quantitative sufficient condition, not a general persistence theorem for all
`0 < α < 1`. -/
theorem corridorFloorCertificate_forces_growth_restriction
    {K : ℝ → ℝ} {ρplus α c front ε radius S : ℝ}
    {orbit : ℕ → ℝ → ℝ}
    (hK : CompactProbabilityKernel K radius)
    (hρplus : 0 < ρplus) (hα : 0 ≤ α)
    (certificate :
      CorridorFloorCertificate
        K ρplus α c front ε S orbit) :
    1 ≤
        ρplus *
          (1 - 2 * certificate.floor - 2 * α) ∧
      α < (1 : ℝ) / 2 ∧
      1 < ρplus := by
  have hmargin :=
    minorization_reproduction_forces_growth_margin
      hK.integrable hK.nonneg hK.mass_one
      certificate.kernel_minorization
      certificate.kappa_nonneg certificate.windowLength_nonneg
      certificate.expanding_width hρplus hα
      certificate.floor_pos (by norm_num : 0 ≤ (1 : ℝ))
      certificate.floor_reproduces
  have hfactor :
      0 <
        1 - 2 * certificate.floor - 2 * α := by
    by_contra hnot
    have hfactor_nonpos :
        1 - 2 * certificate.floor - 2 * α ≤ 0 :=
      le_of_not_gt hnot
    have hproduct_nonpos :
        ρplus *
            (1 - 2 * certificate.floor - 2 * α) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hρplus.le hfactor_nonpos
    linarith
  have hαhalf : α < (1 : ℝ) / 2 := by
    linarith [certificate.floor_pos]
  have hfactor_lt_one :
      1 - 2 * certificate.floor - 2 * α < 1 := by
    linarith [certificate.floor_pos]
  have hρlarge : 1 < ρplus := by
    by_contra hnot
    have hρle : ρplus ≤ 1 := le_of_not_gt hnot
    have hproduct_lt :
        ρplus *
            (1 - 2 * certificate.floor - 2 * α) < 1 := by
      calc
        ρplus *
              (1 - 2 * certificate.floor - 2 * α) <
            ρplus * 1 :=
          mul_lt_mul_of_pos_left hfactor_lt_one hρplus
        _ = ρplus := mul_one ρplus
        _ ≤ 1 := hρle
    linarith
  exact ⟨by simpa using hmargin, hαhalf, hρlarge⟩

/-! ## Finite-block persistence certificates -/

/-- A finite linear block certificate supplies the eventual positive corridor
floor needed by the weak-competition coexistence theorem.  The resident
species is bounded only by one; no extinction assumption is used. -/
theorem favorableCorridor_positive_floor_of_finiteBlockCertificate
    {K ρ : ℝ → ℝ}
    {ρplus α c front εblock εwide radius S
      slope η seed L R leftAdvance rightAdvance minWidth : ℝ}
    {focal competitor : ℕ → ℝ → ℝ}
    {N P : ℕ}
    (hK : CompactProbabilityKernel K radius)
    (hρtail : ExactFavorableTail ρ ρplus S)
    (hρplus : 0 < ρplus)
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hstep : ∀ n x,
      focal (n + 1) x =
        heterogeneousCorrectedStep K ρ α c n
          (focal n) (competitor n) x)
    (hfocal_continuous : ∀ n, Continuous (focal n))
    (hfocal_nonneg : ∀ n x, 0 ≤ focal n x)
    (hfocal_le_one : ∀ n x, focal n x ≤ 1)
    (hcompetitor_continuous : ∀ n, Continuous (competitor n))
    (hcompetitor_nonneg : ∀ n x, 0 ≤ competitor n x)
    (hcompetitor_le_one : ∀ n x, competitor n x ≤ 1)
    (cert :
      FiniteBlockCertificate K slope η seed (P + 1)
        leftAdvance rightAdvance minWidth)
    (hadvance : leftAdvance ≤ rightAdvance)
    (hwidth : minWidth ≤ R - L)
    (hη : 0 ≤ η) (hsmall : η + α ≤ 1)
    (hslope : 0 ≤ slope)
    (hslope_le :
      slope ≤ favorableLowerSlope ρplus α 1 η)
    (hinitial : ∀ y ∈ Set.Icc L R, seed ≤ focal N y)
    (hsupport_ahead :
      ∀ (k t : ℕ), t < P + 1 → ∀ y,
        0 < finiteLinearOrbit K slope
          (intervalFloor seed
            (L + leftAdvance * (k : ℝ))
            (R + rightAdvance * (k : ℝ))) t y →
        S ≤ y - c * ((N + (P + 1) * k + t : ℕ) : ℝ))
    (hc : 0 ≤ c)
    (hεblock : 0 < εblock) (hεgap : εblock < εwide)
    (hleft :
      (c + εblock) * ((P + 1 : ℕ) : ℝ) > leftAdvance)
    (hright :
      (front - εblock) * ((P + 1 : ℕ) : ℝ) < rightAdvance) :
    ∃ Nfloor, ∀ n, Nfloor ≤ n →
      ∀ y ∈ favorableCorridor c front εwide n,
        seed ≤ focal n y := by
  have hfavorable :
      ∀ (k t : ℕ), t < P + 1 → ∀ y,
        0 < finiteLinearOrbit K slope
          (intervalFloor seed
            (L + leftAdvance * (k : ℝ))
            (R + rightAdvance * (k : ℝ))) t y →
        competitor (N + (P + 1) * k + t) y ≤ 1 ∧
        ρplus ≤ ρ
          (y - c * ((N + (P + 1) * k + t : ℕ) : ℝ)) := by
    intro k t ht y hy
    constructor
    · exact hcompetitor_le_one _ y
    · rw [hρtail.eq_favorable _ (hsupport_ahead k t ht y hy)]
  have hblockfloor_raw :=
    finiteBlockCertificate_blockCorridor_floor
      (focal := focal) (competitor := competitor)
      (Kfun := K) (ρfun := ρ)
      (α := α) (c := c) (ρ₀ := ρplus) (δ := 1)
      (η := η) (slope := slope) (seed := seed)
      (L := L) (R := R)
      (leftAdvance := leftAdvance) (rightAdvance := rightAdvance)
      (minWidth := minWidth) (front := front) (ε := εblock)
      (N := N) (block := P + 1)
      cert hadvance hwidth hstep hK.integrable hK.continuous hK.nonneg
      hρtail.continuous hρtail.lower hα0
      hfocal_continuous hfocal_nonneg hfocal_le_one
      hcompetitor_continuous hcompetitor_nonneg
      hρplus (by norm_num) hη (by simpa using hsmall)
      hslope hslope_le hinitial hfavorable hleft hright
  have hblockfloor :
      ∃ Kbase, ∀ (k : ℕ), Kbase ≤ k →
        ∀ x ∈ favorableCorridor c front εblock
            (N + k + P * k),
          seed ≤ focal (N + k + P * k) x := by
    rcases hblockfloor_raw with ⟨Kbase, hKbase⟩
    refine ⟨Kbase, ?_⟩
    intro k hk x hx
    have htime :
        N + (P + 1) * k = N + k + P * k := by ring
    rw [← htime] at hx ⊢
    exact hKbase k hk x hx
  have hηpos : 0 < η :=
    cert.seed_pos.trans_le cert.seed_le_eta
  have hseedq : seed ≤ perturbedCarrying α 1 := by
    unfold perturbedCarrying
    linarith [cert.seed_le_eta]
  apply blockCorridor_floor_implies_all_times
    (focal := focal) (competitor := competitor)
    (Kfun := K) (ρfun := ρ)
    (α := α) (c := c) (front := front)
    (εwide := εblock) (εtarget := εwide)
    (radius := radius) (ρ₀ := ρplus) (δ := 1) (seed := seed)
    (N := N) (P := P)
    hstep hK.integrable hK.continuous hK.nonneg hK.mass_one
    hK.radius_nonneg hK.support
    hρtail.continuous hρtail.lower hα0
    hfocal_continuous hfocal_nonneg hfocal_le_one
    hcompetitor_continuous hcompetitor_nonneg
  · exact ⟨0, fun n _hn x => hcompetitor_le_one n x⟩
  · exact hc
  · exact hρplus
  · exact ⟨S, fun s hs => by
      rw [hρtail.eq_favorable s hs]⟩
  · exact hεblock
  · exact hεgap
  · norm_num
  · simpa using hα1
  · exact cert.seed_pos
  · exact hseedq
  · exact hblockfloor

/-- All finite-dimensional data needed to generate a positive moving-corridor
floor for one species.  Kernel regularity, the exact favorable tail, and the
two-species recurrence remain outside this structure because they are shared
by the final coexistence theorem. -/
structure FiniteBlockCorridorCertificate
    (K : ℝ → ℝ) (ρplus α c front εwide S : ℝ)
    (focal : ℕ → ℝ → ℝ) where
  blockEpsilon : ℝ
  slope : ℝ
  eta : ℝ
  seed : ℝ
  seedLeft : ℝ
  seedRight : ℝ
  leftAdvance : ℝ
  rightAdvance : ℝ
  minWidth : ℝ
  startTime : ℕ
  blockMinusOne : ℕ
  finite_block :
    FiniteBlockCertificate K slope eta seed (blockMinusOne + 1)
      leftAdvance rightAdvance minWidth
  advance_order : leftAdvance ≤ rightAdvance
  initial_width : minWidth ≤ seedRight - seedLeft
  eta_nonneg : 0 ≤ eta
  low_density : eta + α ≤ 1
  slope_nonneg : 0 ≤ slope
  slope_below_response :
    slope ≤ favorableLowerSlope ρplus α 1 eta
  initial_seed :
    ∀ y ∈ Set.Icc seedLeft seedRight, seed ≤ focal startTime y
  favorable_support :
    ∀ (k t : ℕ), t < blockMinusOne + 1 → ∀ y,
      0 < finiteLinearOrbit K slope
        (intervalFloor seed
          (seedLeft + leftAdvance * (k : ℝ))
          (seedRight + rightAdvance * (k : ℝ))) t y →
      S ≤
        y - c *
          ((startTime + (blockMinusOne + 1) * k + t : ℕ) : ℝ)
  blockEpsilon_pos : 0 < blockEpsilon
  blockEpsilon_lt_wide : blockEpsilon < εwide
  left_speed :
    (c + blockEpsilon) * ((blockMinusOne + 1 : ℕ) : ℝ) >
      leftAdvance
  right_speed :
    (front - blockEpsilon) * ((blockMinusOne + 1 : ℕ) : ℝ) <
      rightAdvance

/-- Bundled form of
`favorableCorridor_positive_floor_of_finiteBlockCertificate`. -/
theorem favorableCorridor_positive_floor_of_finiteBlockCorridorCertificate
    {K ρ : ℝ → ℝ}
    {ρplus α c front εwide radius S : ℝ}
    {focal competitor : ℕ → ℝ → ℝ}
    (hK : CompactProbabilityKernel K radius)
    (hρtail : ExactFavorableTail ρ ρplus S)
    (hρplus : 0 < ρplus)
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hstep : ∀ n x,
      focal (n + 1) x =
        heterogeneousCorrectedStep K ρ α c n
          (focal n) (competitor n) x)
    (hfocal_continuous : ∀ n, Continuous (focal n))
    (hfocal_nonneg : ∀ n x, 0 ≤ focal n x)
    (hfocal_le_one : ∀ n x, focal n x ≤ 1)
    (hcompetitor_continuous : ∀ n, Continuous (competitor n))
    (hcompetitor_nonneg : ∀ n x, 0 ≤ competitor n x)
    (hcompetitor_le_one : ∀ n x, competitor n x ≤ 1)
    (hc : 0 ≤ c)
    (data :
      FiniteBlockCorridorCertificate
        K ρplus α c front εwide S focal) :
    ∃ Nfloor, ∀ n, Nfloor ≤ n →
      ∀ y ∈ favorableCorridor c front εwide n,
        data.seed ≤ focal n y := by
  exact
    favorableCorridor_positive_floor_of_finiteBlockCertificate
      hK hρtail hρplus hα0 hα1 hstep
      hfocal_continuous hfocal_nonneg hfocal_le_one
      hcompetitor_continuous hcompetitor_nonneg hcompetitor_le_one
      data.finite_block data.advance_order data.initial_width
      data.eta_nonneg data.low_density
      data.slope_nonneg data.slope_below_response
      data.initial_seed data.favorable_support
      hc data.blockEpsilon_pos data.blockEpsilon_lt_wide
      data.left_speed data.right_speed

/-- **Corrected Theorem 2.3 from two finite linear block certificates.**

Each species supplies a finite certificate for simultaneous growth and
dispersal while the other species is bounded by one.  The certificates first
produce positive floors on the common moving corridor; the finite-depth
rectangle comparison then gives uniform convergence to the coexistence
equilibrium on every strictly narrower corridor. -/
theorem certified_weak_competition_spatial_coexistence_of_finiteBlockCertificates
    {K₁ K₂ ρ₁ ρ₂ : ℝ → ℝ}
    {ρ₁plus ρ₂plus α₁ α₂ c front εwide εtarget radius S₁ S₂ : ℝ}
    {u v : ℕ → ℝ → ℝ}
    (hK₁ : CompactProbabilityKernel K₁ radius)
    (hK₂ : CompactProbabilityKernel K₂ radius)
    (hρ₁tail : ExactFavorableTail ρ₁ ρ₁plus S₁)
    (hρ₂tail : ExactFavorableTail ρ₂ ρ₂plus S₂)
    (hρ₁plus : 0 < ρ₁plus) (hρ₂plus : 0 < ρ₂plus)
    (hα₁0 : 0 < α₁) (hα₁1 : α₁ < 1)
    (hα₂0 : 0 < α₂) (hα₂1 : α₂ < 1)
    (hc : 0 ≤ c)
    (hεwide : 0 < εwide) (hεgap : εwide < εtarget)
    (hcorridor : c + 2 * εtarget ≤ front)
    (horbit :
      CorrectedTwoSpeciesOrbit K₁ K₂ ρ₁ ρ₂ α₁ α₂ c u v)
    (huCertificate :
      FiniteBlockCorridorCertificate
        K₁ ρ₁plus α₁ c front εwide S₁ u)
    (hvCertificate :
      FiniteBlockCorridorCertificate
        K₂ ρ₂plus α₂ c front εwide S₂ v) :
    (∀ n, (favorableCorridor c front εtarget n).Nonempty) ∧
      UniformlyTendstoOnMovingSets u
        (favorableCorridor c front εtarget)
        (coexistenceU α₁ α₂) ∧
      UniformlyTendstoOnMovingSets v
        (favorableCorridor c front εtarget)
        (coexistenceV α₁ α₂) := by
  obtain ⟨Nu, hNu⟩ :=
    favorableCorridor_positive_floor_of_finiteBlockCorridorCertificate
      hK₁ hρ₁tail hρ₁plus hα₁0.le hα₁1
      horbit.u_step horbit.u_continuous horbit.u_nonneg
      horbit.u_le_one horbit.v_continuous horbit.v_nonneg
      horbit.v_le_one hc huCertificate
  obtain ⟨Nv, hNv⟩ :=
    favorableCorridor_positive_floor_of_finiteBlockCorridorCertificate
      hK₂ hρ₂tail hρ₂plus hα₂0.le hα₂1
      horbit.v_step horbit.v_continuous horbit.v_nonneg
      horbit.v_le_one horbit.u_continuous horbit.u_nonneg
      horbit.u_le_one hc hvCertificate
  have huEventually :
      ∀ᶠ n : ℕ in atTop,
        ∀ x ∈ favorableCorridor c front εwide n,
          huCertificate.seed ≤ u n x :=
    eventually_atTop.2 ⟨Nu, hNu⟩
  have hvEventually :
      ∀ᶠ n : ℕ in atTop,
        ∀ x ∈ favorableCorridor c front εwide n,
          hvCertificate.seed ≤ v n x :=
    eventually_atTop.2 ⟨Nv, hNv⟩
  have hpersistence :
      ∀ᶠ n : ℕ in atTop,
        ∀ x ∈ favorableCorridor c front εwide n,
          huCertificate.seed ≤ u n x ∧
            hvCertificate.seed ≤ v n x := by
    filter_upwards [huEventually, hvEventually] with n huFloor hvFloor
    exact fun x hx => ⟨huFloor x hx, hvFloor x hx⟩
  exact certified_weak_competition_spatial_coexistence
    hK₁ hK₂ hρ₁tail hρ₂tail hρ₁plus hρ₂plus
    hα₁0 hα₁1 hα₂0 hα₂1 hc hεwide hεgap hcorridor
    huCertificate.finite_block.seed_pos
    hvCertificate.finite_block.seed_pos
    horbit hpersistence

/-- A per-species minorization certificate produces the eventual corridor
floor needed by the finite-depth coexistence argument.  The competitor bound
is fixed to one and comes directly from the invariant unit square. -/
theorem favorableCorridor_positive_floor_of_certificate
    {K ρ : ℝ → ℝ} {ρplus α c front ε radius S : ℝ}
    {focal competitor : ℕ → ℝ → ℝ}
    (hK : CompactProbabilityKernel K radius)
    (hρtail : ExactFavorableTail ρ ρplus S)
    (hρplus : 0 ≤ ρplus) (hα : 0 ≤ α)
    (hstep : ∀ n x,
      focal (n + 1) x =
        heterogeneousCorrectedStep K ρ α c n
          (focal n) (competitor n) x)
    (hfocal_continuous : ∀ n, Continuous (focal n))
    (hfocal_nonneg : ∀ n x, 0 ≤ focal n x)
    (hfocal_le_one : ∀ n x, focal n x ≤ 1)
    (hcompetitor_continuous : ∀ n, Continuous (competitor n))
    (hcompetitor_nonneg : ∀ n x, 0 ≤ competitor n x)
    (hcompetitor_le_one : ∀ n x, competitor n x ≤ 1)
    (certificate :
      CorridorFloorCertificate
        K ρplus α c front ε S focal) :
    ∃ Nfloor, ∀ n, Nfloor ≤ n →
      ∀ y ∈ favorableCorridor c front ε n,
        certificate.floor ≤ focal n y := by
  apply favorableCorridor_positive_floor_of_minorization
      (competitor := competitor) (orbit := focal)
      (Kfun := K) (ρfun := ρ)
      (α := α) (c := c) (front := front) (ε := ε)
      (ρ₀ := ρplus) (δ := 1)
      (z := certificate.floor) (κ := certificate.kappa)
      (L := certificate.seedLeft) (R := certificate.seedRight)
      (a := certificate.displacementLeft)
      (b := certificate.displacementRight)
      (θ := certificate.windowLength)
      (N := certificate.startTime)
  · intro k x
    simpa [Nat.add_assoc] using
      hstep (certificate.startTime + k) x
  · exact hK.integrable
  · exact hK.continuous
  · exact hK.nonneg
  · exact certificate.kernel_minorization
  · exact hρtail.continuous
  · exact hρtail.lower
  · exact hα
  · exact hfocal_continuous
  · exact hfocal_nonneg
  · exact hfocal_le_one
  · exact hcompetitor_continuous
  · exact hcompetitor_nonneg
  · exact certificate.kappa_nonneg
  · exact certificate.windowLength_nonneg
  · exact certificate.displacement_window_fits_seed
  · exact certificate.expanding_width
  · exact hρplus
  · exact certificate.floor_pos.le
  · norm_num
  · simpa using certificate.floor_subunit
  · exact certificate.floor_reproduces
  · exact certificate.initial_seed
  · intro k y _hy
    exact hcompetitor_le_one (certificate.startTime + k) y
  · intro k y hy
    rw [hρtail.eq_favorable _ (certificate.expanding_ahead k y hy)]
  · exact certificate.left_speed
  · exact certificate.right_speed

/-- Optional one-step-minorization corollary with no external corridor-floor
premise.  Each floor is derived from a compact seed and a numerical
certificate, and the two eventual conclusions are intersected before invoking
the finite-range spatial theorem.  The preceding obstruction theorem shows
that these certificates are substantially stronger than weak competition
alone. -/
theorem certified_weak_competition_spatial_coexistence_of_minorization
    {K₁ K₂ ρ₁ ρ₂ : ℝ → ℝ}
    {ρ₁plus ρ₂plus α₁ α₂ c front εwide εtarget radius S₁ S₂ : ℝ}
    {u v : ℕ → ℝ → ℝ}
    (hK₁ : CompactProbabilityKernel K₁ radius)
    (hK₂ : CompactProbabilityKernel K₂ radius)
    (hρ₁tail : ExactFavorableTail ρ₁ ρ₁plus S₁)
    (hρ₂tail : ExactFavorableTail ρ₂ ρ₂plus S₂)
    (hρ₁plus : 0 < ρ₁plus) (hρ₂plus : 0 < ρ₂plus)
    (hα₁0 : 0 < α₁) (hα₁1 : α₁ < 1)
    (hα₂0 : 0 < α₂) (hα₂1 : α₂ < 1)
    (hc : 0 ≤ c)
    (hεwide : 0 < εwide) (hεgap : εwide < εtarget)
    (hcorridor : c + 2 * εtarget ≤ front)
    (horbit :
      CorrectedTwoSpeciesOrbit K₁ K₂ ρ₁ ρ₂ α₁ α₂ c u v)
    (huCertificate :
      CorridorFloorCertificate
        K₁ ρ₁plus α₁ c front εwide S₁ u)
    (hvCertificate :
      CorridorFloorCertificate
        K₂ ρ₂plus α₂ c front εwide S₂ v) :
    (∀ n, (favorableCorridor c front εtarget n).Nonempty) ∧
      UniformlyTendstoOnMovingSets u
        (favorableCorridor c front εtarget)
        (coexistenceU α₁ α₂) ∧
      UniformlyTendstoOnMovingSets v
        (favorableCorridor c front εtarget)
        (coexistenceV α₁ α₂) := by
  obtain ⟨Nu, hNu⟩ :=
    favorableCorridor_positive_floor_of_certificate
      hK₁ hρ₁tail hρ₁plus.le hα₁0.le
      horbit.u_step horbit.u_continuous horbit.u_nonneg
      horbit.u_le_one horbit.v_continuous horbit.v_nonneg
      horbit.v_le_one huCertificate
  obtain ⟨Nv, hNv⟩ :=
    favorableCorridor_positive_floor_of_certificate
      hK₂ hρ₂tail hρ₂plus.le hα₂0.le
      horbit.v_step horbit.v_continuous horbit.v_nonneg
      horbit.v_le_one horbit.u_continuous horbit.u_nonneg
      horbit.u_le_one hvCertificate
  have huEventually :
      ∀ᶠ n : ℕ in atTop,
        ∀ x ∈ favorableCorridor c front εwide n,
          huCertificate.floor ≤ u n x :=
    eventually_atTop.2 ⟨Nu, hNu⟩
  have hvEventually :
      ∀ᶠ n : ℕ in atTop,
        ∀ x ∈ favorableCorridor c front εwide n,
          hvCertificate.floor ≤ v n x :=
    eventually_atTop.2 ⟨Nv, hNv⟩
  have hpersistence :
      ∀ᶠ n : ℕ in atTop,
        ∀ x ∈ favorableCorridor c front εwide n,
          huCertificate.floor ≤ u n x ∧
            hvCertificate.floor ≤ v n x := by
    filter_upwards [huEventually, hvEventually] with n huFloor hvFloor
    exact fun x hx => ⟨huFloor x hx, hvFloor x hx⟩
  exact certified_weak_competition_spatial_coexistence
    hK₁ hK₂ hρ₁tail hρ₂tail hρ₁plus hρ₂plus
    hα₁0 hα₁1 hα₂0 hα₂1 hc hεwide hεgap hcorridor
    huCertificate.floor_pos hvCertificate.floor_pos
    horbit hpersistence

section AxiomAudit

#print axioms heterogeneousCorrectedStep_mem_favorable_rectangle
#print axioms seededEnvelopeOrbit_contains_on_erodedInterval
#print axioms eventuallyUniformlyTrappedByEverySeededEnvelope_of_compactSupport
#print axioms certified_weak_competition_spatial_coexistence
#print axioms corridorFloorCertificate_forces_growth_restriction
#print axioms favorableCorridor_positive_floor_of_finiteBlockCertificate
#print axioms favorableCorridor_positive_floor_of_finiteBlockCorridorCertificate
#print axioms certified_weak_competition_spatial_coexistence_of_finiteBlockCertificates
#print axioms favorableCorridor_positive_floor_of_certificate
#print axioms certified_weak_competition_spatial_coexistence_of_minorization

end AxiomAudit

end

end ShenWork.Liang
