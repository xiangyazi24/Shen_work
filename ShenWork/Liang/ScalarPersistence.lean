/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import ShenWork.Liang.IDEComparison
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Scalar persistence tools for the corrected shifting-habitat IDE

This file proves the genuinely nonlinear ingredients needed for the
intermediate-speed result.  They are deliberately quantitative.

* A nonzero continuous focal profile remains nonzero after one convolution
  step when the kernel is positive at one displacement.
* Positivity at one point gives a uniform positive seed on an interval.
* A kernel minorization on an interval propagates a positive floor on an
  explicitly expanding interval.
* The favorable Beverton--Holt map, including a bounded competitor, is reduced
  to a standard two-parameter map whose positive orbit converges to its
  carrying level.

No spreading or persistence conclusion is included as a hypothesis.
-/

open Filter MeasureTheory Set Topology

namespace ShenWork.Liang

noncomputable section

/-! ## Favorable local maps -/

/-- Beverton--Holt map with low-density multiplier `r` and carrying level
`q`.  The normalization makes `q` a fixed point. -/
def bhMap (r q z : ℝ) : ℝ :=
  r * q * z / (q + (r - 1) * z)

/-- The orbit of the normalized Beverton--Holt map. -/
def bhOrbit (r q z : ℝ) : ℕ → ℝ
  | 0 => z
  | n + 1 => bhMap r q (bhOrbit r q z n)

@[simp]
theorem bhOrbit_zero (r q z : ℝ) :
    bhOrbit r q z 0 = z :=
  rfl

@[simp]
theorem bhOrbit_succ (r q z : ℝ) (n : ℕ) :
    bhOrbit r q z (n + 1) = bhMap r q (bhOrbit r q z n) :=
  rfl

theorem bhMap_denominator_pos
    {r q z : ℝ} (hr : 1 < r) (hq : 0 < q) (hz : 0 ≤ z) :
    0 < q + (r - 1) * z := by
  positivity

theorem bhMap_pos
    {r q z : ℝ} (hr : 1 < r) (hq : 0 < q) (hz : 0 < z) :
    0 < bhMap r q z := by
  unfold bhMap
  positivity

theorem bhMap_nonneg
    {r q z : ℝ} (hr : 1 < r) (hq : 0 < q) (hz : 0 ≤ z) :
    0 ≤ bhMap r q z := by
  rcases hz.eq_or_lt with rfl | hzpos
  · simp [bhMap]
  · exact (bhMap_pos hr hq hzpos).le

/-- The interval from a positive seed to the carrying level is invariant. -/
theorem bhMap_le_carrying
    {r q z : ℝ} (hr : 1 < r) (hq : 0 < q)
    (hz : 0 ≤ z) (hzq : z ≤ q) :
    bhMap r q z ≤ q := by
  have hden := bhMap_denominator_pos hr hq hz
  unfold bhMap
  apply (div_le_iff₀ hden).2
  have hq0 : 0 ≤ q := hq.le
  nlinarith [mul_nonneg (sub_nonneg.mpr hr.le) (sub_nonneg.mpr hzq)]

/-- Below the carrying level, one Beverton--Holt step does not decrease the
population. -/
theorem le_bhMap_of_le_carrying
    {r q z : ℝ} (hr : 1 < r) (hq : 0 < q)
    (hz : 0 ≤ z) (hzq : z ≤ q) :
    z ≤ bhMap r q z := by
  have hden := bhMap_denominator_pos hr hq hz
  unfold bhMap
  apply (le_div_iff₀ hden).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hr.le) (sub_nonneg.mpr hzq)]

/-- The Beverton--Holt map is increasing on the positive cone. -/
theorem bhMap_mono
    {r q z₁ z₂ : ℝ} (hr : 1 < r) (hq : 0 < q)
    (hz₁ : 0 ≤ z₁) (hz₁₂ : z₁ ≤ z₂) :
    bhMap r q z₁ ≤ bhMap r q z₂ := by
  have hz₂ : 0 ≤ z₂ := hz₁.trans hz₁₂
  have hden₁ := bhMap_denominator_pos hr hq hz₁
  have hden₂ := bhMap_denominator_pos hr hq hz₂
  unfold bhMap
  apply (div_le_div_iff₀ hden₁ hden₂).2
  have hr0 : 0 ≤ r := le_trans (by norm_num) hr.le
  have hq0 : 0 ≤ q := hq.le
  have hmain :
      0 ≤ r * q ^ 2 * (z₂ - z₁) := by positivity
  have hid :
      r * q * z₂ * (q + (r - 1) * z₁) -
          r * q * z₁ * (q + (r - 1) * z₂) =
        r * q ^ 2 * (z₂ - z₁) := by ring
  nlinarith

theorem bhOrbit_pos
    {r q z : ℝ} (hr : 1 < r) (hq : 0 < q) (hz : 0 < z) :
    ∀ n, 0 < bhOrbit r q z n := by
  intro n
  induction n with
  | zero => exact hz
  | succ n ih =>
      exact bhMap_pos hr hq ih

theorem bhOrbit_nonneg
    {r q z : ℝ} (hr : 1 < r) (hq : 0 < q) (hz : 0 ≤ z) :
    ∀ n, 0 ≤ bhOrbit r q z n := by
  intro n
  induction n with
  | zero => exact hz
  | succ n ih =>
      exact bhMap_nonneg hr hq ih

theorem bhOrbit_le_carrying
    {r q z : ℝ} (hr : 1 < r) (hq : 0 < q)
    (hz : 0 ≤ z) (hzq : z ≤ q) :
    ∀ n, bhOrbit r q z n ≤ q := by
  intro n
  induction n with
  | zero => exact hzq
  | succ n ih =>
      exact bhMap_le_carrying hr hq
        (bhOrbit_nonneg hr hq hz n) ih

theorem bhOrbit_monotone
    {r q z : ℝ} (hr : 1 < r) (hq : 0 < q)
    (hz : 0 < z) (hzq : z ≤ q) :
    Monotone (bhOrbit r q z) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [bhOrbit_succ]
  exact le_bhMap_of_le_carrying hr hq
    (bhOrbit_pos hr hq hz n).le
    (bhOrbit_le_carrying hr hq hz.le hzq n)

/-- Every positive Beverton--Holt orbit started below its carrying level
converges to that level. -/
theorem bhOrbit_tendsto_carrying
    {r q z : ℝ} (hr : 1 < r) (hq : 0 < q)
    (hz : 0 < z) (hzq : z ≤ q) :
    Tendsto (bhOrbit r q z) atTop (𝓝 q) := by
  let w : ℕ → ℝ := bhOrbit r q z
  have hwmono : Monotone w := bhOrbit_monotone hr hq hz hzq
  have hwupper : ∀ n, w n ≤ q :=
    bhOrbit_le_carrying hr hq hz.le hzq
  have hbdd : BddAbove (Set.range w) :=
    ⟨q, fun _ ⟨n, hn⟩ => hn ▸ hwupper n⟩
  let ell : ℝ := ⨆ n, w n
  have hell : Tendsto w atTop (𝓝 ell) :=
    tendsto_atTop_ciSup hwmono hbdd
  have hell_succ : Tendsto (fun n => w (n + 1)) atTop (𝓝 ell) :=
    hell.comp (tendsto_add_atTop_nat 1)
  have hcont : ContinuousAt (bhMap r q) ell := by
    have hell0 : 0 ≤ ell := by
      exact le_ciSup_of_le hbdd 0 (by simpa [w] using hz.le)
    unfold bhMap
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact ne_of_gt (bhMap_denominator_pos hr hq hell0)
  have hmaplim :
      Tendsto (fun n => bhMap r q (w n)) atTop (𝓝 (bhMap r q ell)) :=
    hcont.tendsto.comp hell
  have hfix : bhMap r q ell = ell := by
    apply tendsto_nhds_unique hmaplim
    simpa [w, bhOrbit_succ] using hell_succ
  have hell_pos : 0 < ell := by
    exact lt_of_lt_of_le hz
      (le_ciSup_of_le hbdd 0 (by simp [w]))
  have hden := bhMap_denominator_pos hr hq hell_pos.le
  have hell_eq : ell = q := by
    unfold bhMap at hfix
    have hcross :
        r * q * ell = ell * (q + (r - 1) * ell) :=
      (div_eq_iff hden.ne').mp hfix
    have hfactor :
        (r - 1) * ell * (q - ell) = 0 := by
      have hid :
          r * q * ell - ell * (q + (r - 1) * ell) =
            (r - 1) * ell * (q - ell) := by ring
      rw [← hid, hcross, sub_self]
    rcases mul_eq_zero.mp hfactor with hzero | hzero
    · rcases mul_eq_zero.mp hzero with hrzero | hellzero
      · exfalso
        exact (sub_pos.mpr hr).ne' hrzero
      · exact (hell_pos.ne' hellzero).elim
    · linarith
  simpa [hell_eq] using hell

/-- Effective multiplier of a species whose competitor is held at density
`δ` in a favorable environment. -/
def perturbedMultiplier (ρ α δ : ℝ) : ℝ :=
  (1 + ρ) / (1 + ρ * α * δ)

/-- Carrying level under a constant competitor of density `δ`. -/
def perturbedCarrying (α δ : ℝ) : ℝ :=
  1 - α * δ

/-- The corrected local response with a constant competitor is exactly a
normalized Beverton--Holt map. -/
theorem correctedResponse_eq_bhMap
    {ρ α δ z : ℝ} (hρ : 0 ≤ ρ)
    (hden : 1 + ρ * α * δ ≠ 0)
    (hcarry : perturbedCarrying α δ ≠ 0)
    (horig : 1 + ρ * (z + α * δ) ≠ 0) :
    correctedResponse ρ α z δ =
      bhMap (perturbedMultiplier ρ α δ)
        (perturbedCarrying α δ) z := by
  rw [correctedResponse_eq_localResponse_of_nonneg hρ]
  let D : ℝ :=
    perturbedCarrying α δ +
      (perturbedMultiplier ρ α δ - 1) * z
  have hden' : 1 + α * δ * ρ ≠ 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hden
  have hDidentity :
      D * (1 + ρ * α * δ) =
        perturbedCarrying α δ * (1 + ρ * (z + α * δ)) := by
    dsimp [D, perturbedCarrying, perturbedMultiplier]
    field_simp [hden, hden']
    ring
  have hD : D ≠ 0 := by
    intro hzero
    have hzero' :
        perturbedCarrying α δ * (1 + ρ * (z + α * δ)) = 0 := by
      rw [← hDidentity, hzero, zero_mul]
    exact (mul_ne_zero hcarry horig) hzero'
  unfold localResponse bhMap
  change
    (1 + ρ) * z / (1 + ρ * (z + α * δ)) =
      (perturbedMultiplier ρ α δ * perturbedCarrying α δ * z) / D
  apply (div_eq_div_iff horig hD).2
  dsimp [D, perturbedCarrying, perturbedMultiplier]
  field_simp [hden, hden']
  ring

/-- On states below one, increasing a favorable environmental increment can
only increase the corrected response. -/
theorem correctedResponse_mono_environment
    {ρ₁ ρ₂ α u v : ℝ}
    (hρ₁ : 0 ≤ ρ₁) (hρ₁₂ : ρ₁ ≤ ρ₂)
    (hα : 0 ≤ α) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hsubunit : u + α * v ≤ 1) :
    correctedResponse ρ₁ α u v ≤ correctedResponse ρ₂ α u v := by
  have hρ₂ : 0 ≤ ρ₂ := hρ₁.trans hρ₁₂
  rw [correctedResponse_eq_localResponse_of_nonneg hρ₁,
    correctedResponse_eq_localResponse_of_nonneg hρ₂]
  have hq : 0 ≤ u + α * v := by positivity
  have hden₁ : 0 < 1 + ρ₁ * (u + α * v) := by positivity
  have hden₂ : 0 < 1 + ρ₂ * (u + α * v) := by positivity
  unfold localResponse
  apply (div_le_div_iff₀ hden₁ hden₂).2
  have hgap : 0 ≤ (ρ₂ - ρ₁) * u * (1 - (u + α * v)) := by
    positivity
  nlinarith

/-- Lower sandwich used after the slower species has become uniformly small:
reduce the focal species to `z`, raise its competitor to `δ`, and reduce the
favorable environment to `ρ₀`. -/
theorem correctedResponse_ge_perturbed_floor
    {ρ ρ₀ α u v δ z : ℝ}
    (hρ₀ : 0 ≤ ρ₀) (hρ : ρ₀ ≤ ρ)
    (hα : 0 ≤ α) (hz : 0 ≤ z) (hzu : z ≤ u)
    (hv : 0 ≤ v) (hvδ : v ≤ δ)
    (hsubunit : z + α * δ ≤ 1) :
    correctedResponse ρ₀ α z δ ≤ correctedResponse ρ α u v := by
  have hδ : 0 ≤ δ := hv.trans hvδ
  have hρgt : -1 < ρ := lt_of_lt_of_le (by linarith) hρ
  have hρ₀gt : -1 < ρ₀ := by linarith
  calc
    correctedResponse ρ₀ α z δ ≤ correctedResponse ρ α z δ :=
      correctedResponse_mono_environment hρ₀ hρ hα hz hδ hsubunit
    _ ≤ correctedResponse ρ α u δ :=
      correctedResponse_monotone_focal hρgt hα hz hzu hδ
    _ ≤ correctedResponse ρ α u v :=
      correctedResponse_antitone_competitor hρgt hα
        (hz.trans hzu) hv hvδ

/-! ## Strong positivity and interval seeds -/

/-- Positivity at one source point produces positivity after convolution at
the corresponding displaced point. -/
theorem heterogeneousCorrectedStep_pos_of_point_seed
    {K ρ u v : ℝ → ℝ} {α c y₀ z₀ : ℝ} {n : ℕ}
    (hKint : Integrable K) (hKcont : Continuous K)
    (hK : ∀ z, 0 ≤ K z) (hKz : 0 < K z₀)
    (hρcont : Continuous ρ) (hρlow : ∀ s, -1 < ρ s)
    (hα : 0 ≤ α)
    (hucont : Continuous u) (hu : ∀ y, 0 ≤ u y) (hu1 : ∀ y, u y ≤ 1)
    (hvcont : Continuous v) (hv : ∀ y, 0 ≤ v y)
    (huy₀ : 0 < u y₀) :
    0 < heterogeneousCorrectedStep K ρ α c n u v (y₀ + z₀) := by
  let f : ℝ → ℝ := fun y =>
    K ((y₀ + z₀) - y) *
      correctedResponse (ρ (y - c * (n : ℝ))) α (u y) (v y)
  have hfcont : Continuous f := by
    apply (hKcont.comp (continuous_const.sub continuous_id)).mul
    exact correctedResponse_comp_continuous
      (hρcont.comp (continuous_id.sub continuous_const))
      hucont hvcont hα hu hv
  have hfint : Integrable f := by
    exact heterogeneousCorrectedIntegrable
      hKint hKcont hρcont hρlow hα hucont hu hu1 hvcont hv
  have hfnonneg : 0 ≤ f := fun y =>
    mul_nonneg (hK _) (correctedResponse_nonneg (hρlow _) hα (hu y) (hv y))
  have hresp : 0 <
      correctedResponse (ρ (y₀ - c * (n : ℝ))) α (u y₀) (v y₀) := by
    unfold correctedResponse
    exact div_pos (mul_pos (by linarith [hρlow (y₀ - c * (n : ℝ))]) huy₀)
      (correctedResponse_denominator_pos hα (hu y₀) (hv y₀))
  have hfy₀ : f y₀ ≠ 0 := by
    dsimp [f]
    have : (y₀ + z₀) - y₀ = z₀ := by ring
    rw [this]
    positivity
  unfold heterogeneousCorrectedStep ShenWork.Analysis.dispersal
  exact integral_pos_of_integrable_nonneg_nonzero
    hfcont hfint hfnonneg hfy₀

/-- A nonzero focal species remains nonzero at every generation.  More
precisely, positivity can be followed along repeated copies of any displacement
where the kernel is strictly positive. -/
theorem correctedOrbit_pos_along_displacement
    {orbit competitor : ℕ → ℝ → ℝ}
    {K ρ : ℝ → ℝ} {α c x₀ z₀ : ℝ}
    (hstep :
      ∀ n x,
        orbit (n + 1) x =
          heterogeneousCorrectedStep K ρ α c n
            (orbit n) (competitor n) x)
    (hKint : Integrable K) (hKcont : Continuous K)
    (hK : ∀ z, 0 ≤ K z) (hKz : 0 < K z₀)
    (hρcont : Continuous ρ) (hρlow : ∀ s, -1 < ρ s)
    (hα : 0 ≤ α)
    (horbit_cont : ∀ n, Continuous (orbit n))
    (horbit_nonneg : ∀ n y, 0 ≤ orbit n y)
    (horbit_le_one : ∀ n y, orbit n y ≤ 1)
    (hcompetitor_cont : ∀ n, Continuous (competitor n))
    (hcompetitor_nonneg : ∀ n y, 0 ≤ competitor n y)
    (hseed : 0 < orbit 0 x₀) :
    ∀ n, 0 < orbit n (x₀ + (n : ℝ) * z₀) := by
  intro n
  induction n with
  | zero =>
      simpa using hseed
  | succ n ih =>
      have hpos :=
        heterogeneousCorrectedStep_pos_of_point_seed
          (c := c) (n := n)
          (y₀ := x₀ + (n : ℝ) * z₀) (z₀ := z₀)
          hKint hKcont hK hKz hρcont hρlow hα
          (horbit_cont n) (horbit_nonneg n) (horbit_le_one n)
          (hcompetitor_cont n) (hcompetitor_nonneg n) ih
      have hx :
          x₀ + ((n + 1 : ℕ) : ℝ) * z₀ =
            (x₀ + (n : ℝ) * z₀) + z₀ := by
        push_cast
        ring
      rw [hstep n, hx]
      exact hpos

/-- A positive value of a continuous profile contains a quantitative compact
interval seed. -/
theorem exists_interval_floor_of_continuous_pos
    {u : ℝ → ℝ} {x₀ : ℝ} (hu : Continuous u) (hx₀ : 0 < u x₀) :
    ∃ radius floor : ℝ,
      0 < radius ∧ 0 < floor ∧
      ∀ x ∈ Set.Icc (x₀ - radius) (x₀ + radius), floor ≤ u x := by
  have heps : 0 < u x₀ / 2 := by positivity
  rcases (Metric.continuousAt_iff.1 hu.continuousAt) (u x₀ / 2) heps with
    ⟨δ, hδ, hclose⟩
  refine ⟨δ / 2, u x₀ / 2, by positivity, heps, ?_⟩
  intro x hx
  have hdistx : dist x x₀ < δ := by
    rw [Real.dist_eq]
    have habs : |x - x₀| ≤ δ / 2 := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2]
    linarith
  have hdistu := hclose hdistx
  rw [Real.dist_eq] at hdistu
  have hlower := (abs_lt.mp hdistu).1
  linarith

/-! ## Quantitative interval propagation -/

/-- A nonnegative integrable function which is at least `A` on `[p,q]`
has whole-line integral at least `A(q-p)`. -/
theorem const_mul_intervalLength_le_integral
    {f : ℝ → ℝ} {A p q : ℝ}
    (hfint : Integrable f) (hf : ∀ y, 0 ≤ f y)
    (hpq : p ≤ q)
    (hfloor : ∀ y ∈ Set.Icc p q, A ≤ f y) :
    A * (q - p) ≤ ∫ y, f y := by
  let ν : Measure ℝ := volume.restrict (Set.Icc p q)
  have hν : ν ≤ volume := Measure.restrict_le_self
  have hfrestrict : Integrable f ν := hfint.mono_measure hν
  have hconst : Integrable (fun _ : ℝ => A) ν := by
    simp [ν]
  have hlocal :
      (∫ _y : ℝ, A ∂ν) ≤ ∫ y, f y ∂ν := by
    apply integral_mono_ae hconst hfrestrict
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact hfloor y hy
  have hrestrict :
      (∫ y, f y ∂ν) ≤ ∫ y, f y :=
    integral_mono_measure hν (Eventually.of_forall hf) hfint
  calc
    A * (q - p) = ∫ _y : ℝ, A ∂ν := by
      simp [ν, hpq, mul_comm]
    _ ≤ ∫ y, f y ∂ν := hlocal
    _ ≤ ∫ y, f y := hrestrict

/-- A one-step interval-minorization floor certificate necessarily requires
strong favorable growth.  The factor `2` is forced by propagating both
endpoints of an expanding interval: a probability kernel and
`2 * θ ≤ b - a` imply `κ * θ ≤ 1 / 2`.  Consequently, the reproduction
inequality can hold only if the displayed quantitative growth margin is at
least one. -/
theorem minorization_reproduction_forces_growth_margin
    {K : ℝ → ℝ}
    {ρ₀ α z δ κ a b θ : ℝ}
    (hKint : Integrable K)
    (hKnonneg : ∀ s, 0 ≤ K s)
    (hKmass : ∫ s, K s = 1)
    (hKminor : ∀ s ∈ Set.Icc a b, κ ≤ K s)
    (hκ : 0 ≤ κ) (hθ : 0 ≤ θ)
    (hexpand : 2 * θ ≤ b - a)
    (hρ₀ : 0 < ρ₀) (hα : 0 ≤ α)
    (hz : 0 < z) (hδ : 0 ≤ δ)
    (hfixed :
      z ≤ κ * θ * correctedResponse ρ₀ α z δ) :
    1 ≤ ρ₀ * (1 - 2 * z - 2 * α * δ) := by
  have hab : a ≤ b := by linarith
  have hwindowMass : κ * (b - a) ≤ 1 := by
    have hbound :=
      const_mul_intervalLength_le_integral
        hKint hKnonneg hab hKminor
    simpa [hKmass] using hbound
  have hhalf : 2 * (κ * θ) ≤ 1 := by
    have hscaled :
        κ * (2 * θ) ≤ κ * (b - a) :=
      mul_le_mul_of_nonneg_left hexpand hκ
    nlinarith
  have hden :
      0 < 1 + ρ₀ * (z + α * δ) := by
    positivity
  have hfixed' :
      z * (1 + ρ₀ * (z + α * δ)) ≤
        (κ * θ * (1 + ρ₀)) * z := by
    rw [correctedResponse_eq_localResponse_of_nonneg hρ₀.le,
      localResponse, ← mul_div_assoc] at hfixed
    have hcross :=
      (le_div_iff₀ hden).mp hfixed
    nlinarith
  have hratio :
      1 + ρ₀ * (z + α * δ) ≤
        κ * θ * (1 + ρ₀) := by
    apply le_of_mul_le_mul_left (a := z) ?_ hz
    nlinarith
  have hmultiplier :
      2 * (κ * θ * (1 + ρ₀)) ≤ 1 + ρ₀ := by
    have :=
      mul_le_mul_of_nonneg_right hhalf (by linarith : 0 ≤ 1 + ρ₀)
    nlinarith
  nlinarith

/-- A kernel lower bound on one displacement window turns a profile floor on
the corresponding source window into a quantitative next-generation floor. -/
theorem heterogeneousCorrectedStep_ge_window
    {K ρ u v : ℝ → ℝ}
    {α c x ρ₀ δ z κ a b p q : ℝ} {n : ℕ}
    (hKint : Integrable K) (hKcont : Continuous K)
    (hK : ∀ s, 0 ≤ K s)
    (hKminor : ∀ s ∈ Set.Icc a b, κ ≤ K s)
    (hρcont : Continuous ρ) (hρlow : ∀ s, -1 < ρ s)
    (hα : 0 ≤ α)
    (hucont : Continuous u) (hu : ∀ y, 0 ≤ u y) (hu1 : ∀ y, u y ≤ 1)
    (hvcont : Continuous v) (hv : ∀ y, 0 ≤ v y)
    (hκ : 0 ≤ κ) (hpq : p ≤ q)
    (hwindow : ∀ y ∈ Set.Icc p q, x - y ∈ Set.Icc a b)
    (hρ₀ : 0 ≤ ρ₀)
    (hsource : ∀ y ∈ Set.Icc p q,
      z ≤ u y ∧ v y ≤ δ ∧
        ρ₀ ≤ ρ (y - c * (n : ℝ)))
    (hz : 0 ≤ z) (hδ : 0 ≤ δ)
    (hsubunit : z + α * δ ≤ 1) :
    κ * (q - p) * correctedResponse ρ₀ α z δ ≤
      heterogeneousCorrectedStep K ρ α c n u v x := by
  let f : ℝ → ℝ := fun y =>
    K (x - y) *
      correctedResponse (ρ (y - c * (n : ℝ))) α (u y) (v y)
  have hfint : Integrable f :=
    heterogeneousCorrectedIntegrable
      hKint hKcont hρcont hρlow hα hucont hu hu1 hvcont hv
  have hf : ∀ y, 0 ≤ f y := fun y =>
    mul_nonneg (hK _) (correctedResponse_nonneg (hρlow _) hα (hu y) (hv y))
  have hresp0 : 0 ≤ correctedResponse ρ₀ α z δ :=
    correctedResponse_nonneg (by linarith) hα hz hδ
  have hA : 0 ≤ κ * correctedResponse ρ₀ α z δ :=
    mul_nonneg hκ hresp0
  have hlocal :
      ∀ y ∈ Set.Icc p q,
        κ * correctedResponse ρ₀ α z δ ≤ f y := by
    intro y hy
    have hs := hsource y hy
    have hresp :
        correctedResponse ρ₀ α z δ ≤
          correctedResponse (ρ (y - c * (n : ℝ))) α (u y) (v y) :=
      correctedResponse_ge_perturbed_floor
        hρ₀ hs.2.2 hα hz hs.1 (hv y) hs.2.1 hsubunit
    exact mul_le_mul (hKminor _ (hwindow y hy)) hresp hresp0 (hK _)
  have hint :=
    const_mul_intervalLength_le_integral
      hfint hf hpq hlocal
  unfold heterogeneousCorrectedStep ShenWork.Analysis.dispersal
  nlinarith

/-- Explicit expanding interval generated by a minorized displacement window. -/
def expandingSeedInterval
    (L R a b θ : ℝ) (k : ℕ) : Set ℝ :=
  Set.Icc
    (L + (a + θ) * (k : ℝ))
    (R + (b - θ) * (k : ℝ))

theorem expandingSeedInterval_zero
    (L R a b θ : ℝ) :
    expandingSeedInterval L R a b θ 0 = Set.Icc L R := by
  simp [expandingSeedInterval]

/-- One interval-minorization step.  The proof uses the left part of the
kernel window near the left edge and the right part near the right edge. -/
theorem expanding_interval_floor_step
    {K ρ u v : ℝ → ℝ}
    {α c ρ₀ δ z κ L R a b θ : ℝ} {n : ℕ}
    (hKint : Integrable K) (hKcont : Continuous K)
    (hK : ∀ s, 0 ≤ K s)
    (hKminor : ∀ s ∈ Set.Icc a b, κ ≤ K s)
    (hρcont : Continuous ρ) (hρlow : ∀ s, -1 < ρ s)
    (hα : 0 ≤ α)
    (hucont : Continuous u) (hu : ∀ y, 0 ≤ u y) (hu1 : ∀ y, u y ≤ 1)
    (hvcont : Continuous v) (hv : ∀ y, 0 ≤ v y)
    (hκ : 0 ≤ κ) (hθ : 0 ≤ θ)
    (hθwidth : θ ≤ b - a)
    (hwidth : b - a ≤ R - L)
    (hρ₀ : 0 ≤ ρ₀) (hz : 0 ≤ z) (hδ : 0 ≤ δ)
    (hsubunit : z + α * δ ≤ 1)
    (hfloor :
      ∀ y ∈ Set.Icc L R,
        z ≤ u y ∧ v y ≤ δ ∧ ρ₀ ≤ ρ (y - c * (n : ℝ)))
    (hfixed :
      z ≤ κ * θ * correctedResponse ρ₀ α z δ) :
    ∀ x ∈ Set.Icc (L + a + θ) (R + b - θ),
      z ≤ heterogeneousCorrectedStep K ρ α c n u v x := by
  intro x hx
  by_cases hxl : x ≤ L + b
  · let p := x - (a + θ)
    let q := x - a
    have hpq : p ≤ q := by dsimp [p, q]; linarith
    have hsourceWindow : Set.Icc p q ⊆ Set.Icc L R := by
      intro y hy
      constructor
      · dsimp [p] at hy
        linarith [hy.1, hx.1]
      · dsimp [q] at hy
        linarith [hy.2, hxl, hwidth]
    have hdisp : ∀ y ∈ Set.Icc p q, x - y ∈ Set.Icc a b := by
      intro y hy
      dsimp [p, q] at hy
      constructor
      · linarith [hy.2]
      · linarith [hy.1, hθwidth]
    have hstep := heterogeneousCorrectedStep_ge_window
      hKint hKcont hK hKminor hρcont hρlow hα
      hucont hu hu1 hvcont hv hκ hpq hdisp hρ₀
      (fun y hy => hfloor y (hsourceWindow hy))
      hz hδ hsubunit
    have hlen : q - p = θ := by dsimp [p, q]; ring
    rw [hlen] at hstep
    exact hfixed.trans hstep
  · have hxl' : L + b ≤ x := le_of_not_ge hxl
    let p := x - b
    let q := x - (b - θ)
    have hpq : p ≤ q := by dsimp [p, q]; linarith
    have hsourceWindow : Set.Icc p q ⊆ Set.Icc L R := by
      intro y hy
      constructor
      · dsimp [p] at hy
        linarith [hy.1, hxl']
      · dsimp [q] at hy
        linarith [hy.2, hx.2]
    have hdisp : ∀ y ∈ Set.Icc p q, x - y ∈ Set.Icc a b := by
      intro y hy
      dsimp [p, q] at hy
      constructor
      · linarith [hy.2, hθwidth]
      · linarith [hy.1]
    have hstep := heterogeneousCorrectedStep_ge_window
      hKint hKcont hK hKminor hρcont hρlow hα
      hucont hu hu1 hvcont hv hκ hpq hdisp hρ₀
      (fun y hy => hfloor y (hsourceWindow hy))
      hz hδ hsubunit
    have hlen : q - p = θ := by dsimp [p, q]; ring
    rw [hlen] at hstep
    exact hfixed.trans hstep

/-- Quantitative persistence on the whole explicitly expanding interval.
This is an induction from a compact interval seed, not a reformulation of the
conclusion as an assumption. -/
theorem expanding_interval_positive_floor
    {competitor orbit : ℕ → ℝ → ℝ}
    {Kfun ρfun : ℝ → ℝ}
    {α c ρ₀ δ z κ L R a b θ : ℝ} {N : ℕ}
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
          ρ₀ ≤ ρfun (y - c * ((N + k : ℕ) : ℝ))) :
    ∀ (k : ℕ) (y : ℝ),
      y ∈ expandingSeedInterval L R a b θ k →
        z ≤ orbit (N + k) y := by
  intro k
  induction k with
  | zero =>
      intro y hy
      rw [expandingSeedInterval_zero] at hy
      exact hseed y hy
  | succ k ih =>
      intro x hx
      let Lk := L + (a + θ) * (k : ℝ)
      let Rk := R + (b - θ) * (k : ℝ)
      have hwidthk : b - a ≤ Rk - Lk := by
        dsimp [Lk, Rk]
        have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
        have hgrow : 0 ≤ ((b - a) - 2 * θ) * (k : ℝ) :=
          mul_nonneg (sub_nonneg.mpr hexpand) hk
        nlinarith
      have hx' : x ∈ Set.Icc (Lk + a + θ) (Rk + b - θ) := by
        constructor
        · dsimp [expandingSeedInterval, Lk] at hx ⊢
          push_cast at hx
          nlinarith [hx.1]
        · dsimp [expandingSeedInterval, Rk] at hx ⊢
          push_cast at hx
          nlinarith [hx.2]
      rw [show N + (k + 1) = N + k + 1 by omega, horbit k x]
      apply expanding_interval_floor_step
        hKint hKcont hK hKminor hρcont hρlow hα
        (horbit_cont _) (horbit_nonneg _) (horbit_le_one _)
        (hcomp_cont _) (hcomp_nonneg _)
        hκ hθ (by linarith) hwidthk hρ₀ hz hδ hsubunit
      · intro y hy
        have hy' : y ∈ expandingSeedInterval L R a b θ k := by
          simpa [expandingSeedInterval, Lk, Rk] using hy
        exact ⟨ih y hy', hcompetitor k y hy', henvironment k y hy'⟩
      · exact hfixed
      · exact hx'

section AxiomAudit

#print axioms bhOrbit_tendsto_carrying
#print axioms correctedResponse_ge_perturbed_floor
#print axioms heterogeneousCorrectedStep_pos_of_point_seed
#print axioms correctedOrbit_pos_along_displacement
#print axioms exists_interval_floor_of_continuous_pos
#print axioms minorization_reproduction_forces_growth_margin
#print axioms expanding_interval_positive_floor

end AxiomAudit

end

end ShenWork.Liang
