import ShenWork.Paper2.Statements
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section

namespace ShenWork.Paper2

open Filter Set
open scoped Topology

/-- Exponential weight in the Bernoulli reduction for `u' = u(a - b u^α)`. -/
def bernoulliLogisticWeight (p : CM2Params) (t : ℝ) : ℝ :=
  Real.exp (-(p.α * p.a) * t)

/-- Denominator for the forward-time Bernoulli formula. -/
def bernoulliLogisticDenominator (p : CM2Params) (u₀ t : ℝ) : ℝ :=
  p.b / p.a + (u₀ ^ (-p.α) - p.b / p.a) * bernoulliLogisticWeight p t

/-- Forward-time Bernoulli formula for the scalar logistic ODE. -/
def bernoulliLogisticForward (p : CM2Params) (u₀ t : ℝ) : ℝ :=
  (bernoulliLogisticDenominator p u₀ t) ^ (-1 / p.α)

/-- The derivative prescribed by the logistic vector field at the initial value. -/
def bernoulliLogisticInitialDerivative (p : CM2Params) (u₀ : ℝ) : ℝ :=
  u₀ * (p.a - p.b * u₀ ^ p.α)

/-- A globally differentiable extension of the Bernoulli formula.

For `0 ≤ t` this is the exact Bernoulli solution.  For `t < 0` it uses the
positive exponential arc with the same value and first derivative at `t = 0`;
the Paper 2 unit-point construction only uses the forward-time ODE identity. -/
def bernoulliLogisticSolution (p : CM2Params) (u₀ t : ℝ) : ℝ :=
  if 0 ≤ t then
    bernoulliLogisticForward p u₀ t
  else
    u₀ * Real.exp ((p.a - p.b * u₀ ^ p.α) * t)

/-- Derivative of the globally extended Bernoulli-logistic solution. -/
def bernoulliLogisticSolutionDerivative (p : CM2Params) (u₀ t : ℝ) : ℝ :=
  if 0 ≤ t then
    bernoulliLogisticForward p u₀ t *
      (p.a - p.b * (bernoulliLogisticForward p u₀ t) ^ p.α)
  else
    u₀ * Real.exp ((p.a - p.b * u₀ ^ p.α) * t) *
      (p.a - p.b * u₀ ^ p.α)

@[simp] lemma bernoulliLogisticWeight_zero (p : CM2Params) :
    bernoulliLogisticWeight p 0 = 1 := by
  simp [bernoulliLogisticWeight]

@[simp] lemma bernoulliLogisticDenominator_zero
    (p : CM2Params) (u₀ : ℝ) :
    bernoulliLogisticDenominator p u₀ 0 = u₀ ^ (-p.α) := by
  simp [bernoulliLogisticDenominator, bernoulliLogisticWeight]

@[simp] lemma bernoulliLogisticSolution_of_nonneg
    (p : CM2Params) (u₀ t : ℝ) (ht : 0 ≤ t) :
    bernoulliLogisticSolution p u₀ t = bernoulliLogisticForward p u₀ t := by
  simp [bernoulliLogisticSolution, ht]

@[simp] lemma bernoulliLogisticSolution_of_neg
    (p : CM2Params) (u₀ t : ℝ) (ht : t < 0) :
    bernoulliLogisticSolution p u₀ t =
      u₀ * Real.exp ((p.a - p.b * u₀ ^ p.α) * t) := by
  simp [bernoulliLogisticSolution, not_le.mpr ht]

lemma bernoulliLogisticDenominator_pos_of_nonneg_time
    (p : CM2Params) {u₀ t : ℝ} (ha : 0 < p.a) (hb : 0 < p.b)
    (hu₀ : 0 < u₀) (ht : 0 ≤ t) :
    0 < bernoulliLogisticDenominator p u₀ t := by
  set w := bernoulliLogisticWeight p t
  have hw_pos : 0 < w := by
    simpa [w, bernoulliLogisticWeight, mul_assoc] using
      (Real.exp_pos (-(p.α * p.a) * t))
  have harg_nonpos : -(p.α * p.a) * t ≤ 0 := by
    have hprod : 0 ≤ (p.α * p.a) * t :=
      mul_nonneg (mul_nonneg p.hα.le ha.le) ht
    linarith
  have hw_le_one : w ≤ 1 := by
    simpa [w, bernoulliLogisticWeight] using Real.exp_le_one_iff.mpr harg_nonpos
  have hc_pos : 0 < u₀ ^ (-p.α) := Real.rpow_pos_of_pos hu₀ _
  have hq_pos : 0 < p.b / p.a := div_pos hb ha
  have hden_eq :
      bernoulliLogisticDenominator p u₀ t =
        u₀ ^ (-p.α) * w + (p.b / p.a) * (1 - w) := by
    simp [bernoulliLogisticDenominator, w]
    ring
  rw [hden_eq]
  exact add_pos_of_pos_of_nonneg (mul_pos hc_pos hw_pos)
    (mul_nonneg hq_pos.le (sub_nonneg.mpr hw_le_one))

lemma bernoulliLogisticSolution_pos
    (p : CM2Params) {u₀ t : ℝ} (ha : 0 < p.a) (hb : 0 < p.b)
    (hu₀ : 0 < u₀) :
    0 < bernoulliLogisticSolution p u₀ t := by
  by_cases ht : 0 ≤ t
  · rw [bernoulliLogisticSolution_of_nonneg p u₀ t ht]
    exact Real.rpow_pos_of_pos
      (bernoulliLogisticDenominator_pos_of_nonneg_time p ha hb hu₀ ht) _
  · have ht_neg : t < 0 := not_le.mp ht
    rw [bernoulliLogisticSolution_of_neg p u₀ t ht_neg]
    exact mul_pos hu₀ (Real.exp_pos _)

lemma bernoulliLogisticWeight_hasDerivAt (p : CM2Params) (t : ℝ) :
    HasDerivAt (fun s : ℝ => bernoulliLogisticWeight p s)
      (-(p.α * p.a) * bernoulliLogisticWeight p t) t := by
  have h :=
    (((hasDerivAt_id t).const_mul (-(p.α * p.a))).exp)
  simpa [bernoulliLogisticWeight, mul_comm, mul_left_comm, mul_assoc] using h

lemma bernoulliLogisticDenominator_hasDerivAt
    (p : CM2Params) (u₀ t : ℝ) :
    HasDerivAt (fun s : ℝ => bernoulliLogisticDenominator p u₀ s)
      ((u₀ ^ (-p.α) - p.b / p.a) *
        (-(p.α * p.a) * bernoulliLogisticWeight p t)) t := by
  have hweight := bernoulliLogisticWeight_hasDerivAt p t
  have hmul :=
    hweight.const_mul (u₀ ^ (-p.α) - p.b / p.a)
  simpa [bernoulliLogisticDenominator, mul_comm, mul_left_comm, mul_assoc] using
    hmul.const_add (p.b / p.a)

lemma bernoulliLogisticForward_hasDerivAt_raw
    (p : CM2Params) {u₀ t : ℝ} (ha : 0 < p.a) (hb : 0 < p.b)
    (hu₀ : 0 < u₀) (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => bernoulliLogisticForward p u₀ s)
      (((u₀ ^ (-p.α) - p.b / p.a) *
          (-(p.α * p.a) * bernoulliLogisticWeight p t)) *
        (-1 / p.α) *
        (bernoulliLogisticDenominator p u₀ t) ^ (-1 / p.α - 1)) t := by
  have hden_pos :
      0 < bernoulliLogisticDenominator p u₀ t :=
    bernoulliLogisticDenominator_pos_of_nonneg_time p ha hb hu₀ ht
  have hden_ne : bernoulliLogisticDenominator p u₀ t ≠ 0 :=
    ne_of_gt hden_pos
  have hden := bernoulliLogisticDenominator_hasDerivAt p u₀ t
  simpa [bernoulliLogisticForward] using
    (hden.rpow_const (Or.inl hden_ne) (p := -1 / p.α))

lemma bernoulliLogisticForward_raw_derivative_eq_vectorField
    (p : CM2Params) {u₀ t : ℝ} (ha : 0 < p.a) (hb : 0 < p.b)
    (hu₀ : 0 < u₀) (ht : 0 ≤ t) :
    (((u₀ ^ (-p.α) - p.b / p.a) *
          (-(p.α * p.a) * bernoulliLogisticWeight p t)) *
        (-1 / p.α) *
        (bernoulliLogisticDenominator p u₀ t) ^ (-1 / p.α - 1)) =
      bernoulliLogisticForward p u₀ t *
        (p.a - p.b * (bernoulliLogisticForward p u₀ t) ^ p.α) := by
  set D := bernoulliLogisticDenominator p u₀ t
  have hD_pos : 0 < D := by
    simpa [D] using
      bernoulliLogisticDenominator_pos_of_nonneg_time p ha hb hu₀ ht
  have hD_ne : D ≠ 0 := ne_of_gt hD_pos
  have hα_ne : p.α ≠ 0 := ne_of_gt p.hα
  have ha_ne : p.a ≠ 0 := ne_of_gt ha
  have hD_sub :
      D - p.b / p.a =
        (u₀ ^ (-p.α) - p.b / p.a) * bernoulliLogisticWeight p t := by
    simp [D, bernoulliLogisticDenominator]
  have hfactor :
      (u₀ ^ (-p.α) - p.b / p.a) *
          (-(p.α * p.a) * bernoulliLogisticWeight p t) =
        -(p.α * p.a) * (D - p.b / p.a) := by
    rw [hD_sub]
    ring
  have hpow_add :
      D ^ (-1 / p.α - 1) = D ^ (-1 / p.α) * D⁻¹ := by
    rw [show -1 / p.α - 1 = -1 / p.α + (-1 : ℝ) by ring]
    rw [Real.rpow_add hD_pos]
    rw [Real.rpow_neg_one]
  have hpow_alpha :
      (D ^ (-1 / p.α)) ^ p.α = D⁻¹ := by
    rw [← Real.rpow_mul hD_pos.le]
    have hmul : (-1 / p.α) * p.α = -1 := by
      field_simp [hα_ne]
    rw [hmul, Real.rpow_neg_one]
  calc
    (((u₀ ^ (-p.α) - p.b / p.a) *
          (-(p.α * p.a) * bernoulliLogisticWeight p t)) *
        (-1 / p.α) * D ^ (-1 / p.α - 1))
        = (-(p.α * p.a) * (D - p.b / p.a)) *
            (-1 / p.α) * D ^ (-1 / p.α - 1) := by rw [hfactor]
    _ = p.a * (D - p.b / p.a) * (D ^ (-1 / p.α) * D⁻¹) := by
      rw [hpow_add]
      field_simp [hα_ne]
    _ = D ^ (-1 / p.α) * (p.a - p.b * D⁻¹) := by
      field_simp [hD_ne, ha_ne]
    _ = bernoulliLogisticForward p u₀ t *
        (p.a - p.b * (bernoulliLogisticForward p u₀ t) ^ p.α) := by
      rw [show bernoulliLogisticForward p u₀ t = D ^ (-1 / p.α) by
        simp [bernoulliLogisticForward, D]]
      rw [hpow_alpha]

lemma bernoulliLogisticForward_hasDerivAt
    (p : CM2Params) {u₀ t : ℝ} (ha : 0 < p.a) (hb : 0 < p.b)
    (hu₀ : 0 < u₀) (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => bernoulliLogisticForward p u₀ s)
      (bernoulliLogisticForward p u₀ t *
        (p.a - p.b * (bernoulliLogisticForward p u₀ t) ^ p.α)) t :=
  (bernoulliLogisticForward_hasDerivAt_raw p ha hb hu₀ ht).congr_deriv
    (bernoulliLogisticForward_raw_derivative_eq_vectorField p ha hb hu₀ ht)

@[simp] lemma bernoulliLogisticForward_zero
    (p : CM2Params) {u₀ : ℝ} (hu₀ : 0 < u₀) :
    bernoulliLogisticForward p u₀ 0 = u₀ := by
  have hα_ne : p.α ≠ 0 := ne_of_gt p.hα
  rw [bernoulliLogisticForward, bernoulliLogisticDenominator_zero]
  rw [← Real.rpow_mul hu₀.le]
  have hmul : (-p.α) * (-1 / p.α) = 1 := by
    field_simp [hα_ne]
  rw [hmul, Real.rpow_one]

lemma bernoulliLogisticSolution_hasDerivAt_of_pos_time
    (p : CM2Params) {u₀ t : ℝ} (ha : 0 < p.a) (hb : 0 < p.b)
    (hu₀ : 0 < u₀) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => bernoulliLogisticSolution p u₀ s)
      (bernoulliLogisticSolution p u₀ t *
        (p.a - p.b * (bernoulliLogisticSolution p u₀ t) ^ p.α)) t := by
  have hbranch :
      (fun s : ℝ => bernoulliLogisticSolution p u₀ s) =ᶠ[𝓝 t]
        (fun s : ℝ => bernoulliLogisticForward p u₀ s) := by
    filter_upwards [eventually_ge_nhds ht] with s hs
    exact bernoulliLogisticSolution_of_nonneg p u₀ s hs
  have hsol_t :
      bernoulliLogisticSolution p u₀ t =
        bernoulliLogisticForward p u₀ t :=
    bernoulliLogisticSolution_of_nonneg p u₀ t ht.le
  simpa [hsol_t] using
    (bernoulliLogisticForward_hasDerivAt p ha hb hu₀ ht.le).congr_of_eventuallyEq hbranch

lemma bernoulliLogisticSolution_hasDerivAt_of_neg_time
    (p : CM2Params) {u₀ t : ℝ} (ht : t < 0) :
    HasDerivAt (fun s : ℝ => bernoulliLogisticSolution p u₀ s)
      (bernoulliLogisticSolutionDerivative p u₀ t) t := by
  let c : ℝ := p.a - p.b * u₀ ^ p.α
  have hbranch :
      (fun s : ℝ => bernoulliLogisticSolution p u₀ s) =ᶠ[𝓝 t]
        (fun s : ℝ => u₀ * Real.exp (c * s)) := by
    filter_upwards [eventually_lt_nhds ht] with s hs
    simp [bernoulliLogisticSolution_of_neg p u₀ s hs, c]
  have hneg :
      HasDerivAt (fun s : ℝ => u₀ * Real.exp (c * s))
        (u₀ * Real.exp (c * t) * c) t := by
    have h := (((hasDerivAt_id t).const_mul c).exp).const_mul u₀
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  simpa [bernoulliLogisticSolutionDerivative, not_le.mpr ht, c, mul_comm, mul_left_comm,
    mul_assoc] using hneg.congr_of_eventuallyEq hbranch

lemma bernoulliLogisticSolution_hasDerivAt_zero
    (p : CM2Params) {u₀ : ℝ} (ha : 0 < p.a) (hb : 0 < p.b)
    (hu₀ : 0 < u₀) :
    HasDerivAt (fun s : ℝ => bernoulliLogisticSolution p u₀ s)
      (bernoulliLogisticSolutionDerivative p u₀ 0) 0 := by
  let d : ℝ := bernoulliLogisticInitialDerivative p u₀
  let c : ℝ := p.a - p.b * u₀ ^ p.α
  have hforward0 : bernoulliLogisticForward p u₀ 0 = u₀ :=
    bernoulliLogisticForward_zero p hu₀
  have hderiv_def : bernoulliLogisticSolutionDerivative p u₀ 0 = d := by
    simp [bernoulliLogisticSolutionDerivative, bernoulliLogisticInitialDerivative,
      hforward0, d]
  have hforward_deriv :
      HasDerivAt (fun s : ℝ => bernoulliLogisticForward p u₀ s) d 0 := by
    simpa [bernoulliLogisticInitialDerivative, hforward0, d] using
      (bernoulliLogisticForward_hasDerivAt p ha hb hu₀ (le_rfl : 0 ≤ (0 : ℝ)))
  have hright :
      HasDerivWithinAt (fun s : ℝ => bernoulliLogisticSolution p u₀ s) d
        (Ici (0 : ℝ)) 0 := by
    refine hforward_deriv.hasDerivWithinAt.congr ?_ ?_
    · intro s hs
      exact bernoulliLogisticSolution_of_nonneg p u₀ s hs
    · exact bernoulliLogisticSolution_of_nonneg p u₀ 0 le_rfl
  have hnegative_deriv :
      HasDerivAt (fun s : ℝ => u₀ * Real.exp (c * s)) d 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).const_mul c).exp).const_mul u₀
    simpa [bernoulliLogisticInitialDerivative, c, d, mul_comm, mul_left_comm, mul_assoc] using h
  have hleft :
      HasDerivWithinAt (fun s : ℝ => bernoulliLogisticSolution p u₀ s) d
        (Iic (0 : ℝ)) 0 := by
    refine hnegative_deriv.hasDerivWithinAt.congr ?_ ?_
    · intro s hs
      by_cases hs0 : s = 0
      · subst s
        simp [bernoulliLogisticSolution, hforward0, c]
      · have hsneg : s < 0 := lt_of_le_of_ne hs hs0
        simp [bernoulliLogisticSolution_of_neg p u₀ s hsneg, c]
    · simp [bernoulliLogisticSolution, hforward0, c]
  have hunion : Iic (0 : ℝ) ∪ Ici (0 : ℝ) = univ := by
    ext x
    constructor
    · intro _; trivial
    · intro _
      by_cases hx : x ≤ 0
      · exact Or.inl hx
      · exact Or.inr (le_of_lt (not_le.mp hx))
  have hboth :
      HasDerivWithinAt (fun s : ℝ => bernoulliLogisticSolution p u₀ s) d
        (Iic (0 : ℝ) ∪ Ici (0 : ℝ)) 0 :=
    hleft.union hright
  have hAt :
      HasDerivAt (fun s : ℝ => bernoulliLogisticSolution p u₀ s) d 0 := by
    rw [← hasDerivWithinAt_univ]
    simpa [hunion] using hboth
  simpa [hderiv_def] using hAt

lemma bernoulliLogisticSolution_hasDerivAt
    (p : CM2Params) {u₀ t : ℝ} (ha : 0 < p.a) (hb : 0 < p.b)
    (hu₀ : 0 < u₀) :
    HasDerivAt (fun s : ℝ => bernoulliLogisticSolution p u₀ s)
      (bernoulliLogisticSolutionDerivative p u₀ t) t := by
  by_cases ht_pos : 0 < t
  · have hsol_t :
        bernoulliLogisticSolution p u₀ t =
          bernoulliLogisticForward p u₀ t :=
      bernoulliLogisticSolution_of_nonneg p u₀ t ht_pos.le
    simpa [bernoulliLogisticSolutionDerivative, ht_pos.le, hsol_t] using
      bernoulliLogisticSolution_hasDerivAt_of_pos_time p ha hb hu₀ ht_pos
  · have ht_le : t ≤ 0 := le_of_not_gt ht_pos
    by_cases ht_zero : t = 0
    · subst t
      exact bernoulliLogisticSolution_hasDerivAt_zero p ha hb hu₀
    · have ht_neg : t < 0 := lt_of_le_of_ne ht_le ht_zero
      exact bernoulliLogisticSolution_hasDerivAt_of_neg_time p ht_neg

lemma bernoulliLogisticSolution_differentiable
    (p : CM2Params) {u₀ : ℝ} (ha : 0 < p.a) (hb : 0 < p.b)
    (hu₀ : 0 < u₀) :
    Differentiable ℝ (fun t : ℝ => bernoulliLogisticSolution p u₀ t) :=
  fun t => (bernoulliLogisticSolution_hasDerivAt p ha hb hu₀ (t := t)).differentiableAt

lemma bernoulliLogisticSolution_le_max_of_nonneg_time
    (p : CM2Params) {u₀ t : ℝ} (ha : 0 < p.a) (hb : 0 < p.b)
    (hu₀ : 0 < u₀) (ht : 0 ≤ t) :
    bernoulliLogisticSolution p u₀ t ≤
      max u₀ ((p.a / p.b) ^ (1 / p.α)) := by
  set K : ℝ := (p.a / p.b) ^ (1 / p.α)
  set D : ℝ := bernoulliLogisticDenominator p u₀ t
  set c : ℝ := u₀ ^ (-p.α)
  set q : ℝ := p.b / p.a
  set w : ℝ := bernoulliLogisticWeight p t
  have hα_ne : p.α ≠ 0 := ne_of_gt p.hα
  have hD_pos : 0 < D := by
    simpa [D] using
      bernoulliLogisticDenominator_pos_of_nonneg_time p ha hb hu₀ ht
  have hc_pos : 0 < c := by
    simpa [c] using Real.rpow_pos_of_pos hu₀ (-p.α)
  have hq_pos : 0 < q := by
    simpa [q] using div_pos hb ha
  have hK_pos : 0 < K := by
    simpa [K] using Real.rpow_pos_of_pos (div_pos ha hb) (1 / p.α)
  have hw_pos : 0 < w := by
    simpa [w, bernoulliLogisticWeight, mul_assoc] using
      (Real.exp_pos (-(p.α * p.a) * t))
  have harg_nonpos : -(p.α * p.a) * t ≤ 0 := by
    have hprod : 0 ≤ (p.α * p.a) * t :=
      mul_nonneg (mul_nonneg p.hα.le ha.le) ht
    linarith
  have hw_le_one : w ≤ 1 := by
    simpa [w, bernoulliLogisticWeight] using Real.exp_le_one_iff.mpr harg_nonpos
  have hD_eq : D = c * w + q * (1 - w) := by
    simp [D, c, q, w, bernoulliLogisticDenominator]
    ring
  have hK_pow_neg :
      K ^ (-p.α) = q := by
    change ((p.a / p.b) ^ (1 / p.α)) ^ (-p.α) = q
    rw [← Real.rpow_mul (div_pos ha hb).le]
    have hmul : (1 / p.α) * (-p.α) = -1 := by
      field_simp [hα_ne]
    rw [hmul, Real.rpow_neg_one]
    change (p.a / p.b)⁻¹ = p.b / p.a
    field_simp [ne_of_gt ha, ne_of_gt hb]
  have hq_back :
      q ^ (-1 / p.α) = K := by
    rw [← hK_pow_neg]
    rw [← Real.rpow_mul hK_pos.le]
    have hmul : (-p.α) * (-1 / p.α) = 1 := by
      field_simp [hα_ne]
    rw [hmul, Real.rpow_one]
  have hc_back :
      c ^ (-1 / p.α) = u₀ := by
    change (u₀ ^ (-p.α)) ^ (-1 / p.α) = u₀
    rw [← Real.rpow_mul hu₀.le]
    have hmul : (-p.α) * (-1 / p.α) = 1 := by
      field_simp [hα_ne]
    rw [hmul, Real.rpow_one]
  have hneg_alpha : -p.α ≤ 0 := by linarith [p.hα]
  have hneg_inv_alpha : -1 / p.α ≤ 0 := by
    have hnonneg : 0 ≤ 1 / p.α := (div_pos zero_lt_one p.hα).le
    rw [show -1 / p.α = -(1 / p.α) by ring]
    exact neg_nonpos.mpr hnonneg
  have hsolution_eq :
      bernoulliLogisticSolution p u₀ t = D ^ (-1 / p.α) := by
    rw [bernoulliLogisticSolution_of_nonneg p u₀ t ht]
    simp [bernoulliLogisticForward, D]
  by_cases huK : u₀ ≤ K
  · have hq_le_c : q ≤ c := by
      have hpow := Real.rpow_le_rpow_of_nonpos hu₀ huK hneg_alpha
      simpa [hK_pow_neg, c] using hpow
    have hD_ge_q : q ≤ D := by
      rw [hD_eq]
      calc
        q = q * w + q * (1 - w) := by ring
        _ ≤ c * w + q * (1 - w) := by
          exact add_le_add (mul_le_mul_of_nonneg_right hq_le_c hw_pos.le) (le_refl _)
    have hmain : D ^ (-1 / p.α) ≤ q ^ (-1 / p.α) :=
      Real.rpow_le_rpow_of_nonpos hq_pos hD_ge_q hneg_inv_alpha
    calc
      bernoulliLogisticSolution p u₀ t = D ^ (-1 / p.α) := hsolution_eq
      _ ≤ q ^ (-1 / p.α) := hmain
      _ = K := hq_back
      _ ≤ max u₀ K := le_max_right _ _
  · have hK_le_u : K ≤ u₀ := le_of_not_ge huK
    have hc_le_q : c ≤ q := by
      have hpow := Real.rpow_le_rpow_of_nonpos hK_pos hK_le_u hneg_alpha
      simpa [hK_pow_neg, c] using hpow
    have hD_ge_c : c ≤ D := by
      rw [hD_eq]
      calc
        c = c * w + c * (1 - w) := by ring
        _ ≤ c * w + q * (1 - w) := by
          exact add_le_add (le_refl _)
            (mul_le_mul_of_nonneg_right hc_le_q (sub_nonneg.mpr hw_le_one))
    have hmain : D ^ (-1 / p.α) ≤ c ^ (-1 / p.α) :=
      Real.rpow_le_rpow_of_nonpos hc_pos hD_ge_c hneg_inv_alpha
    calc
      bernoulliLogisticSolution p u₀ t = D ^ (-1 / p.α) := hsolution_eq
      _ ≤ c ^ (-1 / p.α) := hmain
      _ = u₀ := hc_back
      _ ≤ max u₀ K := le_max_left _ _

lemma unitPointLogistic_classicalSolution
    (p : CM2Params) {u₀ : unitPointDomain.Point → ℝ}
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hu₀ : PositiveInitialDatum unitPointDomain u₀)
    {T : ℝ} (hT : 0 < T) :
    IsPaper2ClassicalSolution unitPointDomain p T
      (fun t _ => bernoulliLogisticSolution p (u₀ ()) t)
      (fun t _ => (p.ν / p.μ) *
        (bernoulliLogisticSolution p (u₀ ()) t) ^ p.γ) := by
  have hu₀_pos : 0 < u₀ () := hu₀.pos trivial
  have hsol_diff :
      Differentiable ℝ (fun t : ℝ => bernoulliLogisticSolution p (u₀ ()) t) :=
    bernoulliLogisticSolution_differentiable p ha hb hu₀_pos
  have hsol_pos_all :
      ∀ t : ℝ, 0 < bernoulliLogisticSolution p (u₀ ()) t := fun t =>
    bernoulliLogisticSolution_pos p ha hb hu₀_pos
  have hv_cont :
      Continuous (fun t : ℝ => (p.ν / p.μ) *
        (bernoulliLogisticSolution p (u₀ ()) t) ^ p.γ) := by
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
      (bernoulliLogisticSolution_hasDerivAt_of_pos_time p ha hb hu₀_pos ht_pos).deriv
    simpa [unitPointDomain] using hderiv
  · intro t x _ht_pos _ht_lt _hx
    cases x
    show (0 : ℝ) =
      0 - p.μ * ((p.ν / p.μ) *
        (bernoulliLogisticSolution p (u₀ ()) t) ^ p.γ) +
        p.ν * (bernoulliLogisticSolution p (u₀ ()) t) ^ p.γ
    field_simp [ne_of_gt p.hμ]
    ring
  · intro t x _ht_pos _ht_lt hx
    exact absurd hx (by intro h; exact h)

lemma unitPointLogistic_initialTrace
    (p : CM2Params) {u₀ : unitPointDomain.Point → ℝ}
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hu₀ : PositiveInitialDatum unitPointDomain u₀) :
    InitialTrace unitPointDomain u₀
      (fun t _ => bernoulliLogisticSolution p (u₀ ()) t) := by
  have hu₀_pos : 0 < u₀ () := hu₀.pos trivial
  have hzero :
      bernoulliLogisticSolution p (u₀ ()) 0 = u₀ () := by
    rw [bernoulliLogisticSolution_of_nonneg p (u₀ ()) 0 le_rfl]
    exact bernoulliLogisticForward_zero p hu₀_pos
  have hcont :
      ContinuousAt (fun t : ℝ => bernoulliLogisticSolution p (u₀ ()) t) 0 :=
    (bernoulliLogisticSolution_hasDerivAt_zero p ha hb hu₀_pos).continuousAt
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
      (fun x => bernoulliLogisticSolution p (u₀ ()) t - u₀ x) < ε
  have hfun :
      (fun x : unitPointDomain.Point =>
        bernoulliLogisticSolution p (u₀ ()) t - u₀ x) =
        fun _ => bernoulliLogisticSolution p (u₀ ()) t - u₀ () := by
    funext x
    cases x
    rfl
  rw [hfun]
  simpa [unitPointDomain, Real.dist_eq] using hclose

end ShenWork.Paper2
