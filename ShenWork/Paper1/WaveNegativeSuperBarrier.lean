/-
  Paper-faithful negative-sensitivity upper barrier at M = 1.

  The paper operator contains the favorable cross-frozen reaction term, so
  its scalar dominance condition has right-hand side `1 + |χ|`, not the
  stronger frozen-operator bound with right-hand side `1`.
-/
import ShenWork.Paper1.WavePaperRotheProducer

noncomputable section

namespace ShenWork.Paper1

private def negativeBarrierSpeedCoefficient (p : CMParams) : ℝ :=
  p.m * p.γ * |p.χ| + p.γ ^ 2 * |p.χ| + p.γ ^ 2

/-- The second branch in `cStarLower` is exactly the speed condition needed
by the relaxed paper upper-barrier estimate. -/
theorem negativeBarrierSpeedCoefficient_mul_kappa_sq_lt_one
    (p : CMParams) {c : ℝ} (hc : cStarLower p < c) :
    negativeBarrierSpeedCoefficient p * (kappa c) ^ 2 < 1 := by
  let A := negativeBarrierSpeedCoefficient p
  have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hγ0 : 0 ≤ p.γ := le_trans zero_le_one p.hγ
  have hχ0 : 0 ≤ |p.χ| := abs_nonneg p.χ
  have hterm1 : 0 ≤ p.m * p.γ * |p.χ| :=
    mul_nonneg (mul_nonneg hm0 hγ0) hχ0
  have hterm2 : 0 ≤ p.γ ^ 2 * |p.χ| :=
    mul_nonneg (sq_nonneg p.γ) hχ0
  have hγsq_one : 1 ≤ p.γ ^ 2 := by nlinarith [p.hγ]
  have hA1 : 1 ≤ A := by
    dsimp [A, negativeBarrierSpeedCoefficient]
    nlinarith
  have hA0 : 0 ≤ A := le_trans zero_le_one hA1
  have hsqrt_sq : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA0
  have hsqrt1 : 1 ≤ Real.sqrt A := by
    nlinarith [Real.sqrt_nonneg A]
  have hc2 : 2 < c := two_lt_of_cStarLower_lt hc
  have hsqrt_speed : Real.sqrt A + (Real.sqrt A)⁻¹ < c := by
    have hbranch : 1 / Real.sqrt A + Real.sqrt A < c := by
      exact lt_of_le_of_lt (le_max_right _ _) (by simpa [cStarLower, A] using hc)
    simpa [one_div, add_comm] using hbranch
  have hsqrtκ : Real.sqrt A * kappa c < 1 :=
    gamma_mul_kappa_lt_one_of_gamma_add_inv_lt_speed
      hc2 hsqrt1 hsqrt_speed
  have hsqrtκ0 : 0 < Real.sqrt A * kappa c :=
    mul_pos (lt_of_lt_of_le zero_lt_one hsqrt1)
      (kappa_pos_of_cStarLower_lt hc)
  have hsquare : (Real.sqrt A * kappa c) ^ 2 < 1 := by
    nlinarith
  calc
    negativeBarrierSpeedCoefficient p * (kappa c) ^ 2 =
        A * (kappa c) ^ 2 := rfl
    _ = (Real.sqrt A) ^ 2 * (kappa c) ^ 2 := by
      exact congrArg (fun t : ℝ => t * (kappa c) ^ 2) hsqrt_sq.symm
    _ = (Real.sqrt A * kappa c) ^ 2 := by ring
    _ < 1 := hsquare

/-- `cStarLower p < c` automatically supplies the relaxed scalar bundle used
by the whole-line paper Green step at amplitude one. -/
theorem paperUpperBarrierSuperScalarConditions_one_of_cStarLower_lt
    (p : CMParams) {c : ℝ}
    (hχ : p.χ ≤ 0) (hα : p.α ≤ p.m + p.γ - 1)
    (hc : cStarLower p < c) :
    PaperUpperBarrierSuperScalarConditions p c (kappa c) 1 := by
  have hκ : 0 < kappa c := kappa_pos_of_cStarLower_lt hc
  have hκ1 : kappa c < 1 := kappa_lt_one_of_cStarLower_lt hc
  have hc2 : 2 < c := two_lt_of_cStarLower_lt hc
  have hm_speed : p.m + p.m⁻¹ < c := by
    have hbranch : 1 / p.m + p.m < c :=
      lt_of_le_of_lt (le_max_left _ _ ) (by simpa [cStarLower] using hc)
    simpa [one_div, add_comm] using hbranch
  have hmκ_lt : p.m * kappa c < 1 :=
    gamma_mul_kappa_lt_one_of_gamma_add_inv_lt_speed
      hc2 p.hm hm_speed
  have hmκ : kappa c * p.m ≤ 1 := by
    rw [mul_comm]
    exact hmκ_lt.le
  have hspeed := negativeBarrierSpeedCoefficient_mul_kappa_sq_lt_one p hc
  have hγ0 : 0 ≤ p.γ := le_trans zero_le_one p.hγ
  have hχ0 : 0 ≤ |p.χ| := abs_nonneg p.χ
  have hterm1 : 0 ≤ p.m * p.γ * |p.χ| :=
    mul_nonneg (mul_nonneg (le_trans zero_le_one p.hm) hγ0) hχ0
  have hterm2 : 0 ≤ p.γ ^ 2 * |p.χ| :=
    mul_nonneg (sq_nonneg p.γ) hχ0
  have hγsq_le : p.γ ^ 2 ≤ negativeBarrierSpeedCoefficient p := by
    dsimp [negativeBarrierSpeedCoefficient]
    nlinarith
  have hk2 : 0 ≤ (kappa c) ^ 2 := sq_nonneg (kappa c)
  have hγsqκsq : p.γ ^ 2 * (kappa c) ^ 2 < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hγsq_le hk2) hspeed
  have hγκ0 : 0 < p.γ * kappa c :=
    mul_pos (lt_of_lt_of_le zero_lt_one p.hγ) hκ
  have hγκ : p.γ * kappa c < 1 := by
    have hsquare : (p.γ * kappa c) ^ 2 < 1 := by
      nlinarith
    rw [sq_lt_one_iff_abs_lt_one] at hsquare
    rwa [abs_of_pos hγκ0] at hsquare
  have hden : 0 < 1 - p.γ ^ 2 * (kappa c) ^ 2 := by linarith
  have hMbound :
      |p.χ| * (1 + p.m * p.γ * (kappa c) ^ 2) /
          (1 - p.γ ^ 2 * (kappa c) ^ 2) *
          (1 : ℝ) ^ (p.m + p.γ - p.α - 1) ≤
        1 + |p.χ| * (1 : ℝ) ^ (p.m + p.γ - p.α - 1) := by
    simp only [Real.one_rpow, mul_one]
    rw [div_le_iff₀ hden]
    dsimp [negativeBarrierSpeedCoefficient] at hspeed
    nlinarith [le_of_lt hspeed]
  exact
    { hχ := hχ
      hα := hα
      hκ1 := hκ1
      hγκ := hγκ
      hmκ := hmκ
      hM := le_rfl
      hMbound := hMbound
      hc := (kappa_add_inv_eq_of_cStarLower_lt hc).symm }

/-- Full whole-line paper upper-barrier wrapper for the negative branch.  This
is the form consumed by the cross-frozen Green producer. -/
theorem paperUpperBarrier_super_one_of_cStarLower_lt
    (p : CMParams) {c : ℝ}
    (hχ : p.χ ≤ 0) (hα : p.α ≤ p.m + p.γ - 1)
    (hc : cStarLower p < c)
    {u : ℝ → ℝ} (hu : InMonotoneWaveTrapSet (kappa c) 1 u) :
    ∀ x, paperWaveOperator p c u (upperBarrier (kappa c) 1) x ≤ 0 :=
  paperUpperBarrier_super_of_scalar
    (kappa_pos_of_cStarLower_lt hc)
    (paperUpperBarrierSuperScalarConditions_one_of_cStarLower_lt
      p hχ hα hc)
    hu

section AxiomAudit

#print axioms negativeBarrierSpeedCoefficient_mul_kappa_sq_lt_one
#print axioms paperUpperBarrierSuperScalarConditions_one_of_cStarLower_lt
#print axioms paperUpperBarrier_super_one_of_cStarLower_lt

end AxiomAudit

end ShenWork.Paper1
