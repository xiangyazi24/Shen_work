/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import ShenWork.Liang.ScalarPersistence

/-!
# Attenuated front propagation

The one-step fixed-floor construction in `ScalarPersistence` is intentionally
strong: the same positive number must reproduce itself at both moving
endpoints.  This file separates two different effects.

* A small floor is transported through the leading edge and is allowed to
  attenuate.
* Subsequent generations in the interior can amplify that floor through the
  full Beverton--Holt dynamics.

The first part is proved here.  In particular, no inequality of the form
`z ≤ κ * θ * correctedResponse ... z ...` is assumed.
-/

open Filter MeasureTheory Set Topology

namespace ShenWork.Liang

noncomputable section

/-! ## The attenuated scalar floor -/

/-- The floor transported by a kernel window of retained mass `A`. -/
def attenuatedFloor
    (A ρ α δ seed : ℝ) : ℕ → ℝ
  | 0 => seed
  | n + 1 =>
      A * correctedResponse ρ α (attenuatedFloor A ρ α δ seed n) δ

@[simp]
theorem attenuatedFloor_zero
    (A ρ α δ seed : ℝ) :
    attenuatedFloor A ρ α δ seed 0 = seed :=
  rfl

@[simp]
theorem attenuatedFloor_succ
    (A ρ α δ seed : ℝ) (n : ℕ) :
    attenuatedFloor A ρ α δ seed (n + 1) =
      A * correctedResponse ρ α
        (attenuatedFloor A ρ α δ seed n) δ :=
  rfl

/-- In a favorable environment with a bounded competitor, the corrected
response does not decrease a focal density below the perturbed carrying
level. -/
theorem le_correctedResponse_of_le_perturbedCarrying
    {ρ α δ z : ℝ}
    (hρ : 0 < ρ) (hα : 0 ≤ α) (hδ : 0 ≤ δ)
    (hsmall : α * δ < 1)
    (hz : 0 ≤ z) (hzq : z ≤ perturbedCarrying α δ) :
    z ≤ correctedResponse ρ α z δ := by
  have hq : 0 < perturbedCarrying α δ := by
    unfold perturbedCarrying
    linarith
  have hdenpos : 0 < 1 + ρ * α * δ := by positivity
  have hr : 1 < perturbedMultiplier ρ α δ := by
    unfold perturbedMultiplier
    apply (lt_div_iff₀ hdenpos).2
    nlinarith [mul_pos hρ (sub_pos.mpr hsmall)]
  have hden : 1 + ρ * α * δ ≠ 0 := by positivity
  have hcarry : perturbedCarrying α δ ≠ 0 := hq.ne'
  have horig : 1 + ρ * (z + α * δ) ≠ 0 := by positivity
  rw [correctedResponse_eq_bhMap hρ.le hden hcarry horig]
  exact le_bhMap_of_le_carrying hr hq hz hzq

/-- The perturbed carrying interval is invariant under the corrected
response. -/
theorem correctedResponse_le_perturbedCarrying
    {ρ α δ z : ℝ}
    (hρ : 0 < ρ) (hα : 0 ≤ α) (hδ : 0 ≤ δ)
    (hsmall : α * δ < 1)
    (hz : 0 ≤ z) (hzq : z ≤ perturbedCarrying α δ) :
    correctedResponse ρ α z δ ≤ perturbedCarrying α δ := by
  have hq : 0 < perturbedCarrying α δ := by
    unfold perturbedCarrying
    linarith
  have hdenpos : 0 < 1 + ρ * α * δ := by positivity
  have hr : 1 < perturbedMultiplier ρ α δ := by
    unfold perturbedMultiplier
    apply (lt_div_iff₀ hdenpos).2
    nlinarith [mul_pos hρ (sub_pos.mpr hsmall)]
  have hden : 1 + ρ * α * δ ≠ 0 := by positivity
  have hcarry : perturbedCarrying α δ ≠ 0 := hq.ne'
  have horig : 1 + ρ * (z + α * δ) ≠ 0 := by positivity
  rw [correctedResponse_eq_bhMap hρ.le hden hcarry horig]
  exact bhMap_le_carrying hr hq hz hzq

/-- A larger competitor bound gives a smaller effective low-density
multiplier. -/
theorem perturbedMultiplier_antitone_delta
    {ρ α δ₁ δ₂ : ℝ}
    (hρ : 0 ≤ ρ) (hα : 0 ≤ α)
    (hδ₁ : 0 ≤ δ₁) (hδ₁₂ : δ₁ ≤ δ₂) :
    perturbedMultiplier ρ α δ₂ ≤ perturbedMultiplier ρ α δ₁ := by
  have hnum : 0 ≤ 1 + ρ := by positivity
  have hden₁ : 0 < 1 + ρ * α * δ₁ := by positivity
  have hdenorder :
      1 + ρ * α * δ₁ ≤ 1 + ρ * α * δ₂ := by
    gcongr
  unfold perturbedMultiplier
  exact div_le_div_of_nonneg_left hnum hden₁ hdenorder

theorem attenuatedFloor_pos
    {A ρ α δ seed : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ)
    (hα : 0 ≤ α) (hδ : 0 ≤ δ) (hseed : 0 < seed) :
    ∀ n, 0 < attenuatedFloor A ρ α δ seed n := by
  intro n
  induction n with
  | zero => simpa using hseed
  | succ n ih =>
      rw [attenuatedFloor_succ]
      apply mul_pos hA
      unfold correctedResponse
      exact div_pos (mul_pos (by linarith) ih)
        (correctedResponse_denominator_pos hα ih.le hδ)

theorem attenuatedFloor_nonneg
    {A ρ α δ seed : ℝ}
    (hA : 0 ≤ A) (hρ : -1 < ρ)
    (hα : 0 ≤ α) (hδ : 0 ≤ δ) (hseed : 0 ≤ seed) :
    ∀ n, 0 ≤ attenuatedFloor A ρ α δ seed n := by
  intro n
  induction n with
  | zero => simpa using hseed
  | succ n ih =>
      rw [attenuatedFloor_succ]
      exact mul_nonneg hA (correctedResponse_nonneg hρ hα ih hδ)

/-- If at most all kernel mass is retained, the attenuated floor remains
below the perturbed carrying level. -/
theorem attenuatedFloor_le_perturbedCarrying
    {A ρ α δ seed : ℝ}
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hρ : 0 < ρ) (hα : 0 ≤ α) (hδ : 0 ≤ δ)
    (hsmall : α * δ < 1)
    (hseed0 : 0 ≤ seed)
    (hseedq : seed ≤ perturbedCarrying α δ) :
    ∀ n, attenuatedFloor A ρ α δ seed n ≤
      perturbedCarrying α δ := by
  intro n
  induction n with
  | zero => simpa using hseedq
  | succ n ih =>
      have hnonneg : 0 ≤ attenuatedFloor A ρ α δ seed n :=
        attenuatedFloor_nonneg hA0 (by linarith) hα hδ hseed0 n
      have hresp :=
        correctedResponse_le_perturbedCarrying
          hρ hα hδ hsmall hnonneg ih
      have hq0 : 0 ≤ perturbedCarrying α δ := by
        unfold perturbedCarrying
        linarith
      rw [attenuatedFloor_succ]
      calc
        A * correctedResponse ρ α
              (attenuatedFloor A ρ α δ seed n) δ ≤
            1 * correctedResponse ρ α
              (attenuatedFloor A ρ α δ seed n) δ :=
          mul_le_mul_of_nonneg_right hA1 <|
            correctedResponse_nonneg (by linarith) hα hnonneg hδ
        _ ≤ perturbedCarrying α δ := by simpa using hresp

/-- The leading-edge floor loses at most the retained kernel fraction at each
generation.  This deliberately ignores favorable low-density growth; it is a
robust lower bound used by the later multistep recovery argument. -/
theorem pow_mul_seed_le_attenuatedFloor
    {A ρ α δ seed : ℝ}
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hρ : 0 < ρ) (hα : 0 ≤ α) (hδ : 0 ≤ δ)
    (hsmall : α * δ < 1)
    (hseed0 : 0 ≤ seed)
    (hseedq : seed ≤ perturbedCarrying α δ) :
    ∀ n, A ^ n * seed ≤ attenuatedFloor A ρ α δ seed n := by
  have hupper :=
    attenuatedFloor_le_perturbedCarrying
      hA0 hA1 hρ hα hδ hsmall hseed0 hseedq
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hfloor0 : 0 ≤ attenuatedFloor A ρ α δ seed n := by
        have hpow0 : 0 ≤ A ^ n * seed :=
          mul_nonneg (pow_nonneg hA0 n) hseed0
        exact hpow0.trans ih
      have hresponse :
          attenuatedFloor A ρ α δ seed n ≤
            correctedResponse ρ α
              (attenuatedFloor A ρ α δ seed n) δ :=
        le_correctedResponse_of_le_perturbedCarrying
          hρ hα hδ hsmall hfloor0 (hupper n)
      rw [attenuatedFloor_succ, pow_succ]
      calc
        A ^ n * A * seed = A * (A ^ n * seed) := by ring
        _ ≤ A * attenuatedFloor A ρ α δ seed n :=
          mul_le_mul_of_nonneg_left ih hA0
        _ ≤ A * correctedResponse ρ α
              (attenuatedFloor A ρ α δ seed n) δ :=
          mul_le_mul_of_nonneg_left hresponse hA0

/-! ## Recovery from an exponentially attenuated seed -/

/-- Closed form of the normalized Beverton--Holt orbit. -/
theorem bhOrbit_eq_closedForm
    {r q z : ℝ} (hr : 1 < r) (hq : 0 < q) (hz : 0 < z) :
    ∀ n,
      bhOrbit r q z n =
        q * r ^ n * z / (q - z + r ^ n * z) := by
  intro n
  induction n with
  | zero =>
      rw [bhOrbit_zero, pow_zero]
      rw [show q - z + 1 * z = q by ring]
      exact (eq_div_iff hq.ne').2 (by ring)
  | succ n ih =>
      have hr0 : 0 < r := by linarith
      have hrpow : 1 ≤ r ^ n := one_le_pow₀ (by linarith)
      have hDn : 0 < q - z + r ^ n * z := by
        rw [show q - z + r ^ n * z =
          q + (r ^ n - 1) * z by ring]
        positivity
      have hfrac :
          0 < q * r ^ n * z / (q - z + r ^ n * z) := by
        positivity
      have hinner :
          0 < q + (r - 1) *
            (q * r ^ n * z / (q - z + r ^ n * z)) := by
        positivity
      rw [bhOrbit_succ, ih]
      unfold bhMap
      rw [pow_succ]
      have hrnext : 1 ≤ r ^ n * r := by
        have h := mul_lt_mul_of_pos_left hr (pow_pos hr0 n)
        nlinarith
      have hDnext : 0 < q - z + r ^ n * r * z := by
        rw [show q - z + r ^ n * r * z =
          q + (r ^ n * r - 1) * z by ring]
        positivity
      field_simp [hDn.ne', hinner.ne', hDnext.ne']
      ring

/-- Quantitative error estimate for a Beverton--Holt orbit. -/
theorem bhOrbit_carrying_sub_le
    {r q z : ℝ}
    (hr : 1 < r) (hq : 0 < q) (hz : 0 < z) (hzq : z ≤ q) :
    ∀ n,
      0 ≤ q - bhOrbit r q z n ∧
      q - bhOrbit r q z n ≤ q ^ 2 / (r ^ n * z) := by
  intro n
  have hr0 : 0 < r := by linarith
  have hrpow : 0 < r ^ n := pow_pos hr0 n
  have hden0 : 0 < r ^ n * z := mul_pos hrpow hz
  have hrpow1 : 1 ≤ r ^ n := one_le_pow₀ (by linarith)
  have hD : 0 < q - z + r ^ n * z := by nlinarith
  have horbitle : bhOrbit r q z n ≤ q :=
    bhOrbit_le_carrying hr hq hz.le hzq n
  constructor
  · linarith
  · rw [bhOrbit_eq_closedForm hr hq hz n]
    have hid :
        q - q * r ^ n * z / (q - z + r ^ n * z) =
          (q * (q - z)) / (q - z + r ^ n * z) := by
      apply (eq_div_iff hD.ne').2
      field_simp [hD.ne']
      ring
    rw [hid]
    apply div_le_div₀
    · positivity
    · nlinarith
    · exact hden0
    · nlinarith

/-- A fixed number of full-mass recovery steps per transport step overcomes
an attenuated leading-edge seed exactly when the displayed block multiplier
is larger than one. -/
theorem bhOrbit_recovers_pow_seed
    {A r q seed : ℝ} {P : ℕ}
    (hA0 : 0 < A) (hA1 : A ≤ 1)
    (hr : 1 < r) (hq : 0 < q)
    (hseed : 0 < seed) (hseedq : seed ≤ q)
    (hgrowth : 1 < A * r ^ P) :
    Tendsto
      (fun k : ℕ =>
        bhOrbit r q (A ^ k * seed) (P * k))
      Filter.atTop (𝓝 q) := by
  let G : ℝ := A * r ^ P
  have hG : 1 < G := hgrowth
  have hGpos : 0 < G := lt_trans (by norm_num) hG
  have hGinv0 : 0 ≤ G⁻¹ := inv_nonneg.mpr hGpos.le
  have hGinv1 : G⁻¹ < 1 := inv_lt_one_of_one_lt₀ hG
  have hgeom :
      Tendsto (fun k : ℕ => (G⁻¹) ^ k) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hGinv0 hGinv1
  have hupperlim :
      Tendsto
        (fun k : ℕ => (q ^ 2 / seed) * (G⁻¹) ^ k)
        Filter.atTop (𝓝 0) := by
    simpa using hgeom.const_mul (q ^ 2 / seed)
  have herror :
      Tendsto
        (fun k : ℕ =>
          q - bhOrbit r q (A ^ k * seed) (P * k))
        Filter.atTop (𝓝 0) := by
    apply squeeze_zero
    · intro k
      have hAkpos : 0 < A ^ k * seed :=
        mul_pos (pow_pos hA0 k) hseed
      have hAk_le_one : A ^ k ≤ 1 :=
        pow_le_one₀ hA0.le hA1
      have hAkseedq : A ^ k * seed ≤ q := by
        calc
          A ^ k * seed ≤ 1 * seed :=
            mul_le_mul_of_nonneg_right hAk_le_one hseed.le
          _ ≤ q := by simpa using hseedq
      exact
        (bhOrbit_carrying_sub_le
          hr hq hAkpos hAkseedq (P * k)).1
    · intro k
      have hAkpos : 0 < A ^ k * seed :=
        mul_pos (pow_pos hA0 k) hseed
      have hAk_le_one : A ^ k ≤ 1 :=
        pow_le_one₀ hA0.le hA1
      have hAkseedq : A ^ k * seed ≤ q := by
        calc
          A ^ k * seed ≤ 1 * seed :=
            mul_le_mul_of_nonneg_right hAk_le_one hseed.le
          _ ≤ q := by simpa using hseedq
      have hbound :=
        (bhOrbit_carrying_sub_le
          hr hq hAkpos hAkseedq (P * k)).2
      calc
        q - bhOrbit r q (A ^ k * seed) (P * k) ≤
            q ^ 2 / (r ^ (P * k) * (A ^ k * seed)) :=
          hbound
        _ = (q ^ 2 / seed) * (G⁻¹) ^ k := by
          dsimp [G]
          rw [pow_mul, inv_pow]
          field_simp [hA0.ne', (pow_pos (by linarith : 0 < r) P).ne',
            hseed.ne']
          ring
    · exact hupperlim
  have hrecover := herror.const_sub q
  simpa using hrecover

/-! ## Spatial propagation with a varying floor -/

/-- One interval-minorization step with different input and output floors.
Unlike `expanding_interval_floor_step`, this theorem does not require the
input floor to reproduce itself. -/
theorem expanding_interval_floor_step_to
    {K ρ u v : ℝ → ℝ}
    {α c ρ₀ δ z znext κ L R a b θ : ℝ} {n : ℕ}
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
    (hnext :
      znext ≤ κ * θ * correctedResponse ρ₀ α z δ) :
    ∀ x ∈ Set.Icc (L + a + θ) (R + b - θ),
      znext ≤ heterogeneousCorrectedStep K ρ α c n u v x := by
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
    exact hnext.trans hstep
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
    exact hnext.trans hstep

/-- A generic varying floor propagates on the same expanding intervals as the
fixed-floor construction. -/
theorem expanding_interval_variable_floor
    {competitor orbit : ℕ → ℝ → ℝ}
    {Kfun ρfun : ℝ → ℝ}
    {floor : ℕ → ℝ}
    {α c ρ₀ δ κ L R a b θ : ℝ} {N : ℕ}
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
    (hρ₀ : 0 ≤ ρ₀) (hδ : 0 ≤ δ)
    (hfloor_nonneg : ∀ k, 0 ≤ floor k)
    (hfloor_subunit : ∀ k, floor k + α * δ ≤ 1)
    (hreproduce :
      ∀ k, floor (k + 1) ≤
        κ * θ * correctedResponse ρ₀ α (floor k) δ)
    (hseed : ∀ y ∈ Set.Icc L R, floor 0 ≤ orbit N y)
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
        floor k ≤ orbit (N + k) y := by
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
      apply expanding_interval_floor_step_to
        hKint hKcont hK hKminor hρcont hρlow hα
        (horbit_cont _) (horbit_nonneg _) (horbit_le_one _)
        (hcomp_cont _) (hcomp_nonneg _)
        hκ hθ (by linarith) hwidthk hρ₀
        (hfloor_nonneg k) hδ (hfloor_subunit k)
      · intro y hy
        have hy' : y ∈ expandingSeedInterval L R a b θ k := by
          simpa [expandingSeedInterval, Lk, Rk] using hy
        exact ⟨ih y hy', hcompetitor k y hy', henvironment k y hy'⟩
      · exact hreproduce k
      · exact hx'

/-- The concrete attenuated floor therefore propagates without a fixed-point
reproduction inequality. -/
theorem expanding_interval_attenuated_floor
    {competitor orbit : ℕ → ℝ → ℝ}
    {Kfun ρfun : ℝ → ℝ}
    {α c ρ₀ δ seed κ L R a b θ : ℝ} {N : ℕ}
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
    (hretained : κ * θ ≤ 1)
    (hwidth : b - a ≤ R - L)
    (hexpand : 2 * θ ≤ b - a)
    (hρ₀ : 0 < ρ₀) (hδ : 0 ≤ δ)
    (hsmall : α * δ < 1)
    (hseed : 0 ≤ seed)
    (hseedq : seed ≤ perturbedCarrying α δ)
    (hinitial : ∀ y ∈ Set.Icc L R, seed ≤ orbit N y)
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
        attenuatedFloor (κ * θ) ρ₀ α δ seed k ≤
          orbit (N + k) y := by
  have hA0 : 0 ≤ κ * θ := mul_nonneg hκ hθ
  have hfloor_nonneg :
      ∀ k, 0 ≤ attenuatedFloor (κ * θ) ρ₀ α δ seed k := by
    intro k
    induction k with
    | zero => simpa using hseed
    | succ k ih =>
        rw [attenuatedFloor_succ]
        exact mul_nonneg hA0 <|
          correctedResponse_nonneg (by linarith) hα ih hδ
  apply expanding_interval_variable_floor
    horbit hKint hKcont hK hKminor hρcont hρlow hα
    horbit_cont horbit_nonneg horbit_le_one
    hcomp_cont hcomp_nonneg hκ hθ hwidth hexpand
    hρ₀.le hδ hfloor_nonneg
  · intro k
    have hupper :
        attenuatedFloor (κ * θ) ρ₀ α δ seed k ≤
          perturbedCarrying α δ := by
      exact attenuatedFloor_le_perturbedCarrying
        hA0 hretained hρ₀ hα hδ hsmall hseed hseedq k
    unfold perturbedCarrying at hupper
    linarith
  · intro k
    rfl
  · simpa using hinitial
  · exact hcompetitor
  · exact henvironment

section AxiomAudit

#print axioms pow_mul_seed_le_attenuatedFloor
#print axioms perturbedMultiplier_antitone_delta
#print axioms bhOrbit_recovers_pow_seed
#print axioms expanding_interval_variable_floor

end AxiomAudit

end

end ShenWork.Liang
