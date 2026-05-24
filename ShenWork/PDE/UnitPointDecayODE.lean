/-
  ShenWork/PDE/UnitPointDecayODE.lean

  Pure decay ODE u'(t) = -b u(t)^(α+1) on the unit-point domain.
  Used to close Paper 2 Theorem 1.2 and Paper 3 Proposition 1.4 in the
  (a = 0, b > 0) case where the logistic source vanishes.
-/
import ShenWork.Paper2.Statements
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section

namespace ShenWork.Paper2

open Filter Set
open scoped Topology

/-- Denominator `1 + α b u₀^α t` of the Bernoulli decay formula. -/
def bernoulliDecayDenominator (p : CM2Params) (u₀ t : ℝ) : ℝ :=
  1 + p.α * p.b * u₀ ^ p.α * t

/-- Forward-time Bernoulli formula for the pure-decay ODE
`u' = -b u^(α+1)`. -/
def bernoulliDecayForward (p : CM2Params) (u₀ t : ℝ) : ℝ :=
  u₀ * (bernoulliDecayDenominator p u₀ t) ^ (-1 / p.α)

/-- Globally differentiable extension of the Bernoulli decay formula.
Forward arc uses the exact Bernoulli formula; backward arc uses the
exponential matched in value and derivative at `t = 0`. -/
def bernoulliDecaySolution (p : CM2Params) (u₀ t : ℝ) : ℝ :=
  if 0 ≤ t then
    bernoulliDecayForward p u₀ t
  else
    u₀ * Real.exp ((-(p.b * u₀ ^ p.α)) * t)

/-- Derivative of the Bernoulli decay solution at a point. -/
def bernoulliDecaySolutionDerivative (p : CM2Params) (u₀ t : ℝ) : ℝ :=
  if 0 ≤ t then
    bernoulliDecayForward p u₀ t *
      (-(p.b * (bernoulliDecayForward p u₀ t) ^ p.α))
  else
    u₀ * Real.exp ((-(p.b * u₀ ^ p.α)) * t) *
      (-(p.b * u₀ ^ p.α))

@[simp] lemma bernoulliDecayDenominator_zero
    (p : CM2Params) (u₀ : ℝ) :
    bernoulliDecayDenominator p u₀ 0 = 1 := by
  simp [bernoulliDecayDenominator]

@[simp] lemma bernoulliDecaySolution_of_nonneg
    (p : CM2Params) (u₀ t : ℝ) (ht : 0 ≤ t) :
    bernoulliDecaySolution p u₀ t = bernoulliDecayForward p u₀ t := by
  simp [bernoulliDecaySolution, ht]

@[simp] lemma bernoulliDecaySolution_of_neg
    (p : CM2Params) (u₀ t : ℝ) (ht : t < 0) :
    bernoulliDecaySolution p u₀ t =
      u₀ * Real.exp ((-(p.b * u₀ ^ p.α)) * t) := by
  simp [bernoulliDecaySolution, not_le.mpr ht]

lemma bernoulliDecayDenominator_pos_of_nonneg_time
    (p : CM2Params) {u₀ t : ℝ} (hb : 0 < p.b)
    (hu₀ : 0 < u₀) (ht : 0 ≤ t) :
    0 < bernoulliDecayDenominator p u₀ t := by
  have hα_pos : 0 < p.α := p.hα
  have hu_pow_pos : 0 < u₀ ^ p.α := Real.rpow_pos_of_pos hu₀ _
  have hcoef : 0 ≤ p.α * p.b * u₀ ^ p.α :=
    mul_nonneg (mul_nonneg hα_pos.le hb.le) hu_pow_pos.le
  have hmul : 0 ≤ p.α * p.b * u₀ ^ p.α * t :=
    mul_nonneg hcoef ht
  unfold bernoulliDecayDenominator
  linarith

@[simp] lemma bernoulliDecayForward_zero
    (p : CM2Params) {u₀ : ℝ} (hu₀ : 0 < u₀) :
    bernoulliDecayForward p u₀ 0 = u₀ := by
  have hα_ne : p.α ≠ 0 := ne_of_gt p.hα
  simp [bernoulliDecayForward, bernoulliDecayDenominator]

lemma bernoulliDecayForward_pos
    (p : CM2Params) {u₀ t : ℝ} (hb : 0 < p.b)
    (hu₀ : 0 < u₀) (ht : 0 ≤ t) :
    0 < bernoulliDecayForward p u₀ t := by
  unfold bernoulliDecayForward
  exact mul_pos hu₀ (Real.rpow_pos_of_pos
    (bernoulliDecayDenominator_pos_of_nonneg_time p hb hu₀ ht) _)

lemma bernoulliDecaySolution_pos
    (p : CM2Params) {u₀ t : ℝ} (hb : 0 < p.b)
    (hu₀ : 0 < u₀) :
    0 < bernoulliDecaySolution p u₀ t := by
  by_cases ht : 0 ≤ t
  · rw [bernoulliDecaySolution_of_nonneg p u₀ t ht]
    exact bernoulliDecayForward_pos p hb hu₀ ht
  · have ht_neg : t < 0 := not_le.mp ht
    rw [bernoulliDecaySolution_of_neg p u₀ t ht_neg]
    exact mul_pos hu₀ (Real.exp_pos _)

lemma bernoulliDecayDenominator_hasDerivAt
    (p : CM2Params) (u₀ t : ℝ) :
    HasDerivAt (fun s : ℝ => bernoulliDecayDenominator p u₀ s)
      (p.α * p.b * u₀ ^ p.α) t := by
  have h := (hasDerivAt_id t).const_mul (p.α * p.b * u₀ ^ p.α)
  have h2 := h.const_add (1 : ℝ)
  simpa [bernoulliDecayDenominator] using h2

lemma bernoulliDecayForward_hasDerivAt_raw
    (p : CM2Params) {u₀ t : ℝ} (hb : 0 < p.b)
    (hu₀ : 0 < u₀) (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => bernoulliDecayForward p u₀ s)
      (u₀ * ((p.α * p.b * u₀ ^ p.α) * (-1 / p.α) *
        (bernoulliDecayDenominator p u₀ t) ^ (-1 / p.α - 1))) t := by
  have hden_pos : 0 < bernoulliDecayDenominator p u₀ t :=
    bernoulliDecayDenominator_pos_of_nonneg_time p hb hu₀ ht
  have hden_ne : bernoulliDecayDenominator p u₀ t ≠ 0 := ne_of_gt hden_pos
  have hden := bernoulliDecayDenominator_hasDerivAt p u₀ t
  have hpow := hden.rpow_const (Or.inl hden_ne) (p := -1 / p.α)
  have hmul := hpow.const_mul u₀
  simpa [bernoulliDecayForward, mul_comm, mul_left_comm, mul_assoc] using hmul

lemma bernoulliDecayForward_raw_derivative_eq_vectorField
    (p : CM2Params) {u₀ t : ℝ} (hb : 0 < p.b)
    (hu₀ : 0 < u₀) (ht : 0 ≤ t) :
    u₀ * ((p.α * p.b * u₀ ^ p.α) * (-1 / p.α) *
        (bernoulliDecayDenominator p u₀ t) ^ (-1 / p.α - 1)) =
      bernoulliDecayForward p u₀ t *
        (-(p.b * (bernoulliDecayForward p u₀ t) ^ p.α)) := by
  set D := bernoulliDecayDenominator p u₀ t
  have hD_pos : 0 < D :=
    bernoulliDecayDenominator_pos_of_nonneg_time p hb hu₀ ht
  have hD_ne : D ≠ 0 := ne_of_gt hD_pos
  have hα_ne : p.α ≠ 0 := ne_of_gt p.hα
  have hu_pos : 0 < u₀ := hu₀
  have hu_ne : u₀ ≠ 0 := ne_of_gt hu_pos
  have hu_pow_pos : 0 < u₀ ^ p.α := Real.rpow_pos_of_pos hu₀ _
  have hu_pow_ne : (u₀ ^ p.α) ≠ 0 := ne_of_gt hu_pow_pos
  have hpow_add :
      D ^ (-1 / p.α - 1) = D ^ (-1 / p.α) * D⁻¹ := by
    rw [show -1 / p.α - 1 = -1 / p.α + (-1 : ℝ) by ring]
    rw [Real.rpow_add hD_pos, Real.rpow_neg_one]
  have hfwd_eq :
      bernoulliDecayForward p u₀ t = u₀ * D ^ (-1 / p.α) := by
    rfl
  have hfwd_pow :
      (bernoulliDecayForward p u₀ t) ^ p.α = u₀ ^ p.α * D⁻¹ := by
    rw [hfwd_eq, Real.mul_rpow hu_pos.le (Real.rpow_nonneg hD_pos.le _)]
    congr 1
    rw [← Real.rpow_mul hD_pos.le]
    have hmul : (-1 / p.α) * p.α = -1 := by field_simp [hα_ne]
    rw [hmul, Real.rpow_neg_one]
  calc
    u₀ * ((p.α * p.b * u₀ ^ p.α) * (-1 / p.α) *
        D ^ (-1 / p.α - 1))
        = u₀ * ((p.α * p.b * u₀ ^ p.α) * (-1 / p.α) *
            (D ^ (-1 / p.α) * D⁻¹)) := by rw [hpow_add]
    _ = (u₀ * D ^ (-1 / p.α)) *
            (-(p.b * (u₀ ^ p.α * D⁻¹))) := by
          field_simp [hα_ne]
    _ = bernoulliDecayForward p u₀ t *
            (-(p.b * (bernoulliDecayForward p u₀ t) ^ p.α)) := by
          rw [← hfwd_eq, ← hfwd_pow]

lemma bernoulliDecayForward_hasDerivAt
    (p : CM2Params) {u₀ t : ℝ} (hb : 0 < p.b)
    (hu₀ : 0 < u₀) (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => bernoulliDecayForward p u₀ s)
      (bernoulliDecayForward p u₀ t *
        (-(p.b * (bernoulliDecayForward p u₀ t) ^ p.α))) t :=
  (bernoulliDecayForward_hasDerivAt_raw p hb hu₀ ht).congr_deriv
    (bernoulliDecayForward_raw_derivative_eq_vectorField p hb hu₀ ht)

lemma bernoulliDecaySolution_hasDerivAt_of_pos_time
    (p : CM2Params) {u₀ t : ℝ} (hb : 0 < p.b)
    (hu₀ : 0 < u₀) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => bernoulliDecaySolution p u₀ s)
      (bernoulliDecaySolution p u₀ t *
        (-(p.b * (bernoulliDecaySolution p u₀ t) ^ p.α))) t := by
  have hbranch :
      (fun s : ℝ => bernoulliDecaySolution p u₀ s) =ᶠ[𝓝 t]
        (fun s : ℝ => bernoulliDecayForward p u₀ s) := by
    filter_upwards [eventually_ge_nhds ht] with s hs
    exact bernoulliDecaySolution_of_nonneg p u₀ s hs
  have hsol_t :
      bernoulliDecaySolution p u₀ t =
        bernoulliDecayForward p u₀ t :=
    bernoulliDecaySolution_of_nonneg p u₀ t ht.le
  simpa [hsol_t] using
    (bernoulliDecayForward_hasDerivAt p hb hu₀ ht.le).congr_of_eventuallyEq hbranch

lemma bernoulliDecaySolution_hasDerivAt_of_neg_time
    (p : CM2Params) {u₀ t : ℝ} (ht : t < 0) :
    HasDerivAt (fun s : ℝ => bernoulliDecaySolution p u₀ s)
      (bernoulliDecaySolutionDerivative p u₀ t) t := by
  let c : ℝ := -(p.b * u₀ ^ p.α)
  have hbranch :
      (fun s : ℝ => bernoulliDecaySolution p u₀ s) =ᶠ[𝓝 t]
        (fun s : ℝ => u₀ * Real.exp (c * s)) := by
    filter_upwards [eventually_lt_nhds ht] with s hs
    simp [bernoulliDecaySolution_of_neg p u₀ s hs, c]
  have hneg :
      HasDerivAt (fun s : ℝ => u₀ * Real.exp (c * s))
        (u₀ * Real.exp (c * t) * c) t := by
    have h := (((hasDerivAt_id t).const_mul c).exp).const_mul u₀
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  simpa [bernoulliDecaySolutionDerivative, not_le.mpr ht, c, mul_comm,
    mul_left_comm, mul_assoc] using hneg.congr_of_eventuallyEq hbranch

lemma bernoulliDecaySolution_hasDerivAt_zero
    (p : CM2Params) {u₀ : ℝ} (hb : 0 < p.b)
    (hu₀ : 0 < u₀) :
    HasDerivAt (fun s : ℝ => bernoulliDecaySolution p u₀ s)
      (bernoulliDecaySolutionDerivative p u₀ 0) 0 := by
  let d : ℝ := u₀ * (-(p.b * u₀ ^ p.α))
  let c : ℝ := -(p.b * u₀ ^ p.α)
  have hforward0 : bernoulliDecayForward p u₀ 0 = u₀ :=
    bernoulliDecayForward_zero p hu₀
  have hderiv_def : bernoulliDecaySolutionDerivative p u₀ 0 = d := by
    simp [bernoulliDecaySolutionDerivative, hforward0, d, c]
  have hforward_deriv :
      HasDerivAt (fun s : ℝ => bernoulliDecayForward p u₀ s) d 0 := by
    have h := bernoulliDecayForward_hasDerivAt p hb hu₀ (le_rfl : 0 ≤ (0 : ℝ))
    simpa [hforward0, d, c] using h
  have hright :
      HasDerivWithinAt (fun s : ℝ => bernoulliDecaySolution p u₀ s) d
        (Ici (0 : ℝ)) 0 := by
    refine hforward_deriv.hasDerivWithinAt.congr ?_ ?_
    · intro s hs
      exact bernoulliDecaySolution_of_nonneg p u₀ s hs
    · exact bernoulliDecaySolution_of_nonneg p u₀ 0 le_rfl
  have hnegative_deriv :
      HasDerivAt (fun s : ℝ => u₀ * Real.exp (c * s)) d 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).const_mul c).exp).const_mul u₀
    simpa [c, d, mul_comm, mul_left_comm, mul_assoc] using h
  have hleft :
      HasDerivWithinAt (fun s : ℝ => bernoulliDecaySolution p u₀ s) d
        (Iic (0 : ℝ)) 0 := by
    refine hnegative_deriv.hasDerivWithinAt.congr ?_ ?_
    · intro s hs
      by_cases hs0 : s = 0
      · subst s
        simp [bernoulliDecaySolution, hforward0, c]
      · have hsneg : s < 0 := lt_of_le_of_ne hs hs0
        simp [bernoulliDecaySolution_of_neg p u₀ s hsneg, c]
    · simp [bernoulliDecaySolution, hforward0, c]
  have hunion : Iic (0 : ℝ) ∪ Ici (0 : ℝ) = univ := by
    ext x
    constructor
    · intro _; trivial
    · intro _
      by_cases hx : x ≤ 0
      · exact Or.inl hx
      · exact Or.inr (le_of_lt (not_le.mp hx))
  have hboth :
      HasDerivWithinAt (fun s : ℝ => bernoulliDecaySolution p u₀ s) d
        (Iic (0 : ℝ) ∪ Ici (0 : ℝ)) 0 :=
    hleft.union hright
  have hAt :
      HasDerivAt (fun s : ℝ => bernoulliDecaySolution p u₀ s) d 0 := by
    rw [← hasDerivWithinAt_univ]
    simpa [hunion] using hboth
  simpa [hderiv_def] using hAt

lemma bernoulliDecaySolution_hasDerivAt
    (p : CM2Params) {u₀ t : ℝ} (hb : 0 < p.b)
    (hu₀ : 0 < u₀) :
    HasDerivAt (fun s : ℝ => bernoulliDecaySolution p u₀ s)
      (bernoulliDecaySolutionDerivative p u₀ t) t := by
  by_cases ht_pos : 0 < t
  · have hsol_t :
        bernoulliDecaySolution p u₀ t =
          bernoulliDecayForward p u₀ t :=
      bernoulliDecaySolution_of_nonneg p u₀ t ht_pos.le
    simpa [bernoulliDecaySolutionDerivative, ht_pos.le, hsol_t] using
      bernoulliDecaySolution_hasDerivAt_of_pos_time p hb hu₀ ht_pos
  · have ht_le : t ≤ 0 := le_of_not_gt ht_pos
    by_cases ht_zero : t = 0
    · subst t
      exact bernoulliDecaySolution_hasDerivAt_zero p hb hu₀
    · have ht_neg : t < 0 := lt_of_le_of_ne ht_le ht_zero
      exact bernoulliDecaySolution_hasDerivAt_of_neg_time p ht_neg

lemma bernoulliDecaySolution_differentiable
    (p : CM2Params) {u₀ : ℝ} (hb : 0 < p.b)
    (hu₀ : 0 < u₀) :
    Differentiable ℝ (fun t : ℝ => bernoulliDecaySolution p u₀ t) :=
  fun t => (bernoulliDecaySolution_hasDerivAt p hb hu₀ (t := t)).differentiableAt

/-- For nonneg time the forward Bernoulli decay solution is bounded by `u₀`. -/
lemma bernoulliDecayForward_le
    (p : CM2Params) {u₀ t : ℝ} (hb : 0 < p.b)
    (hu₀ : 0 < u₀) (ht : 0 ≤ t) :
    bernoulliDecayForward p u₀ t ≤ u₀ := by
  set D : ℝ := bernoulliDecayDenominator p u₀ t with hD_def
  have hD_pos : 0 < D :=
    bernoulliDecayDenominator_pos_of_nonneg_time p hb hu₀ ht
  have hD_ge_one : 1 ≤ D := by
    have hα_pos : 0 < p.α := p.hα
    have hu_pow_pos : 0 < u₀ ^ p.α := Real.rpow_pos_of_pos hu₀ _
    have hcoef : 0 ≤ p.α * p.b * u₀ ^ p.α :=
      mul_nonneg (mul_nonneg hα_pos.le hb.le) hu_pow_pos.le
    have hmul : 0 ≤ p.α * p.b * u₀ ^ p.α * t :=
      mul_nonneg hcoef ht
    show (1 : ℝ) ≤ 1 + p.α * p.b * u₀ ^ p.α * t
    linarith
  have hexp_neg : -1 / p.α ≤ 0 := by
    have hpos : 0 < 1 / p.α := div_pos one_pos p.hα
    rw [show (-1 : ℝ) / p.α = -(1 / p.α) by ring]
    linarith
  have hpow_le_one : D ^ (-1 / p.α) ≤ 1 := by
    have h := Real.rpow_le_one_of_one_le_of_nonpos hD_ge_one hexp_neg
    simpa using h
  have hpow_pos : 0 < D ^ (-1 / p.α) := Real.rpow_pos_of_pos hD_pos _
  unfold bernoulliDecayForward
  have := mul_le_mul_of_nonneg_left hpow_le_one hu₀.le
  simpa [mul_one] using this

lemma bernoulliDecaySolution_le_of_nonneg_time
    (p : CM2Params) {u₀ t : ℝ} (hb : 0 < p.b)
    (hu₀ : 0 < u₀) (ht : 0 ≤ t) :
    bernoulliDecaySolution p u₀ t ≤ u₀ := by
  rw [bernoulliDecaySolution_of_nonneg p u₀ t ht]
  exact bernoulliDecayForward_le p hb hu₀ ht

/-- The unit-point classical Paper 2 solution for the (a = 0, b > 0) branch. -/
lemma unitPointDecay_classicalSolution
    (p : CM2Params) {u₀ : unitPointDomain.Point → ℝ}
    (ha : p.a = 0) (hb : 0 < p.b)
    (hu₀ : PositiveInitialDatum unitPointDomain u₀)
    {T : ℝ} (hT : 0 < T) :
    IsPaper2ClassicalSolution unitPointDomain p T
      (fun t _ => bernoulliDecaySolution p (u₀ ()) t)
      (fun t _ => (p.ν / p.μ) *
        (bernoulliDecaySolution p (u₀ ()) t) ^ p.γ) := by
  have hu₀_pos : 0 < u₀ () := hu₀.pos trivial
  have hsol_diff :
      Differentiable ℝ (fun t : ℝ => bernoulliDecaySolution p (u₀ ()) t) :=
    bernoulliDecaySolution_differentiable p hb hu₀_pos
  have hsol_pos_all :
      ∀ t : ℝ, 0 < bernoulliDecaySolution p (u₀ ()) t := fun t =>
    bernoulliDecaySolution_pos p hb hu₀_pos
  have hv_cont :
      Continuous (fun t : ℝ => (p.ν / p.μ) *
        (bernoulliDecaySolution p (u₀ ()) t) ^ p.γ) := by
    exact continuous_const.mul
      (hsol_diff.continuous.rpow_const fun t =>
        Or.inl (ne_of_gt (hsol_pos_all t)))
  refine ⟨hT, ⟨hsol_diff, hv_cont⟩, ?_, ?_, ?_, ?_⟩
  · intro t x _ht_pos _ht_lt _hx
    cases x
    exact hsol_pos_all t
  · intro t x ht_pos _ht_lt _hx
    cases x
    have hderiv :=
      (bernoulliDecaySolution_hasDerivAt_of_pos_time p hb hu₀_pos ht_pos).deriv
    -- ODE PDE form: u' = -b u^(α+1) = u * (a - b u^α) since a = 0.
    have hrewrite :
        bernoulliDecaySolution p (u₀ ()) t *
          (-(p.b * (bernoulliDecaySolution p (u₀ ()) t) ^ p.α)) =
          bernoulliDecaySolution p (u₀ ()) t *
            (p.a - p.b * (bernoulliDecaySolution p (u₀ ()) t) ^ p.α) := by
      rw [ha]
      ring
    rw [hrewrite] at hderiv
    simpa [unitPointDomain] using hderiv
  · intro t x _ht_pos _ht_lt _hx
    cases x
    show (0 : ℝ) =
      0 - p.μ * ((p.ν / p.μ) *
        (bernoulliDecaySolution p (u₀ ()) t) ^ p.γ) +
        p.ν * (bernoulliDecaySolution p (u₀ ()) t) ^ p.γ
    field_simp [ne_of_gt p.hμ]
    ring
  · intro t x _ht_pos _ht_lt hx
    exact absurd hx (by intro h; exact h)

lemma unitPointDecay_initialTrace
    (p : CM2Params) {u₀ : unitPointDomain.Point → ℝ}
    (_ha : p.a = 0) (hb : 0 < p.b)
    (hu₀ : PositiveInitialDatum unitPointDomain u₀) :
    InitialTrace unitPointDomain u₀
      (fun t _ => bernoulliDecaySolution p (u₀ ()) t) := by
  have hu₀_pos : 0 < u₀ () := hu₀.pos trivial
  have hzero :
      bernoulliDecaySolution p (u₀ ()) 0 = u₀ () := by
    rw [bernoulliDecaySolution_of_nonneg p (u₀ ()) 0 le_rfl]
    exact bernoulliDecayForward_zero p hu₀_pos
  have hcont :
      ContinuousAt (fun t : ℝ => bernoulliDecaySolution p (u₀ ()) t) 0 :=
    (bernoulliDecaySolution_hasDerivAt_zero p hb hu₀_pos).continuousAt
  intro ε hε
  rcases (Metric.continuousAt_iff.mp hcont ε hε) with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro t ht_pos htδ
  have htdist : dist t 0 < δ := by
    rw [Real.dist_eq]
    simpa [abs_of_pos ht_pos] using htδ
  have hclose := hδ htdist
  rw [hzero] at hclose
  show unitPointDomain.supNorm
      (fun x => bernoulliDecaySolution p (u₀ ()) t - u₀ x) < ε
  have hfun :
      (fun x : unitPointDomain.Point =>
        bernoulliDecaySolution p (u₀ ()) t - u₀ x) =
        fun _ => bernoulliDecaySolution p (u₀ ()) t - u₀ () := by
    funext x
    cases x
    rfl
  rw [hfun]
  simpa [unitPointDomain, Real.dist_eq] using hclose

theorem unitPointDecay_globalClassicalSolution
    (p : CM2Params) {u₀ : unitPointDomain.Point → ℝ}
    (ha : p.a = 0) (hb : 0 < p.b)
    (hu₀ : PositiveInitialDatum unitPointDomain u₀) :
    IsPaper2GlobalClassicalSolution unitPointDomain p
      (fun t _ => bernoulliDecaySolution p (u₀ ()) t)
      (fun t _ => (p.ν / p.μ) *
        (bernoulliDecaySolution p (u₀ ()) t) ^ p.γ) := by
  intro T hT
  exact unitPointDecay_classicalSolution p ha hb hu₀ hT

/-- For the (a = 0, b > 0) branch on the unit-point domain we get a global
classical solution, the prescribed initial trace, and a uniform a-priori
bound `‖u(t)‖∞ ≤ ‖u₀‖∞`. -/
theorem unitPointDecay_globalExistence_with_bound
    (p : CM2Params) (ha : p.a = 0) (hb : 0 < p.b)
    (u₀ : unitPointDomain.Point → ℝ)
    (hu₀ : PositiveInitialDatum unitPointDomain u₀) :
    ∃ u v : ℝ → unitPointDomain.Point → ℝ,
      IsPaper2GlobalClassicalSolution unitPointDomain p u v ∧
      InitialTrace unitPointDomain u₀ u ∧
      (∀ t, 0 ≤ t →
        unitPointDomain.supNorm (u t) ≤ unitPointDomain.supNorm u₀) := by
  let u : ℝ → unitPointDomain.Point → ℝ :=
    fun t _ => bernoulliDecaySolution p (u₀ ()) t
  let v : ℝ → unitPointDomain.Point → ℝ :=
    fun t _ => (p.ν / p.μ) *
      (bernoulliDecaySolution p (u₀ ()) t) ^ p.γ
  have hu₀_pos : 0 < u₀ () := hu₀.pos trivial
  refine ⟨u, v, ?_, ?_, ?_⟩
  · simpa [u, v] using unitPointDecay_globalClassicalSolution p ha hb hu₀
  · simpa [u] using unitPointDecay_initialTrace p ha hb hu₀
  · intro t ht
    have hsol_pos :
        0 < bernoulliDecaySolution p (u₀ ()) t :=
      bernoulliDecaySolution_pos p hb hu₀_pos
    have hbound :
        bernoulliDecaySolution p (u₀ ()) t ≤ u₀ () :=
      bernoulliDecaySolution_le_of_nonneg_time p hb hu₀_pos ht
    show unitPointDomain.supNorm (fun _ => bernoulliDecaySolution p (u₀ ()) t) ≤
      unitPointDomain.supNorm u₀
    -- unitPointDomain.supNorm f = |f ()|
    show |bernoulliDecaySolution p (u₀ ()) t| ≤ |u₀ ()|
    rw [abs_of_pos hsol_pos, abs_of_pos hu₀_pos]
    exact hbound

end ShenWork.Paper2

end
