import ShenWork.Paper1.WholeLineWeightedRegularityForcingL2Trajectory

open Filter MeasureTheory Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Quantitative exact-weight forcing continuity

This file upgrades the qualitative product and four-summand closures used
for the weighted generator forcing to explicit, common-modulus estimates.
All assumptions live at the exact exponential weight.  No stronger weight,
second spatial derivative, generator-domain hypothesis, or differentiated
flux is used.
-/

/-- Quantitative bounded-coefficient product estimate with a common scalar
modulus.  The field difference and the coefficient difference are measured
at the same nonnegative scale `rho`. -/
theorem integral_mul_sub_mul_sq_data_of_modulus
    {a b u v : ℝ → ℝ}
    {B D E H rho : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hE : 0 ≤ E) (hH : 0 ≤ H)
    (hrho : 0 ≤ rho)
    (ha : ∀ x, |a x| ≤ B)
    (hab : ∀ x, |a x - b x| ≤ D * rho)
    (hout_meas : AEStronglyMeasurable
      (fun x => a x * u x - b x * v x) volume)
    (huv : Integrable (fun x => (u x - v x) ^ 2) volume)
    (hv : Integrable (fun x => v x ^ 2) volume)
    (huv_bound : (∫ x : ℝ, (u x - v x) ^ 2) ≤ H ^ 2 * rho ^ 2)
    (hv_bound : (∫ x : ℝ, v x ^ 2) ≤ E ^ 2) :
    Integrable (fun x => (a x * u x - b x * v x) ^ 2) volume ∧
      (∫ x : ℝ, (a x * u x - b x * v x) ^ 2) ≤
        2 * (B ^ 2 * H ^ 2 + D ^ 2 * E ^ 2) * rho ^ 2 := by
  have hDrho : 0 ≤ D * rho := mul_nonneg hD hrho
  have hraw := integral_mul_sub_mul_sq_data hB hDrho ha hab
    hout_meas huv hv
  refine ⟨hraw.1, hraw.2.trans ?_⟩
  have hBsq : 0 ≤ 2 * B ^ 2 := mul_nonneg (by norm_num) (sq_nonneg B)
  have hDsq : 0 ≤ 2 * (D * rho) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg (D * rho))
  calc
    2 * B ^ 2 * (∫ x : ℝ, (u x - v x) ^ 2) +
        2 * (D * rho) ^ 2 * (∫ x : ℝ, v x ^ 2) ≤
      2 * B ^ 2 * (H ^ 2 * rho ^ 2) +
        2 * (D * rho) ^ 2 * E ^ 2 := by
          gcongr
    _ = 2 * (B ^ 2 * H ^ 2 + D ^ 2 * E ^ 2) * rho ^ 2 := by
      ring

/-- Four quantitative product estimates at one common modulus may be
assembled without a pointwise spatial dominator. -/
theorem integral_four_product_sum_sub_sq_data_of_modulus
    {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : ℝ → ℝ}
    {u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ : ℝ → ℝ}
    {B₁ B₂ B₃ B₄ D₁ D₂ D₃ D₄ : ℝ}
    {E₁ E₂ E₃ E₄ H₁ H₂ H₃ H₄ rho : ℝ}
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hB₃ : 0 ≤ B₃) (hB₄ : 0 ≤ B₄)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hD₃ : 0 ≤ D₃) (hD₄ : 0 ≤ D₄)
    (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (hE₃ : 0 ≤ E₃) (hE₄ : 0 ≤ E₄)
    (hH₁ : 0 ≤ H₁) (hH₂ : 0 ≤ H₂)
    (hH₃ : 0 ≤ H₃) (hH₄ : 0 ≤ H₄)
    (hrho : 0 ≤ rho)
    (ha₁ : ∀ x, |a₁ x| ≤ B₁) (ha₂ : ∀ x, |a₂ x| ≤ B₂)
    (ha₃ : ∀ x, |a₃ x| ≤ B₃) (ha₄ : ∀ x, |a₄ x| ≤ B₄)
    (hab₁ : ∀ x, |a₁ x - b₁ x| ≤ D₁ * rho)
    (hab₂ : ∀ x, |a₂ x - b₂ x| ≤ D₂ * rho)
    (hab₃ : ∀ x, |a₃ x - b₃ x| ≤ D₃ * rho)
    (hab₄ : ∀ x, |a₄ x - b₄ x| ≤ D₄ * rho)
    (hout_meas : AEStronglyMeasurable (fun x =>
      (a₁ x * u₁ x + a₂ x * u₂ x + a₃ x * u₃ x + a₄ x * u₄ x) -
        (b₁ x * v₁ x + b₂ x * v₂ x + b₃ x * v₃ x + b₄ x * v₄ x)) volume)
    (h₁meas : AEStronglyMeasurable (fun x => a₁ x * u₁ x - b₁ x * v₁ x) volume)
    (h₂meas : AEStronglyMeasurable (fun x => a₂ x * u₂ x - b₂ x * v₂ x) volume)
    (h₃meas : AEStronglyMeasurable (fun x => a₃ x * u₃ x - b₃ x * v₃ x) volume)
    (h₄meas : AEStronglyMeasurable (fun x => a₄ x * u₄ x - b₄ x * v₄ x) volume)
    (h₁diff : Integrable (fun x => (u₁ x - v₁ x) ^ 2) volume)
    (h₂diff : Integrable (fun x => (u₂ x - v₂ x) ^ 2) volume)
    (h₃diff : Integrable (fun x => (u₃ x - v₃ x) ^ 2) volume)
    (h₄diff : Integrable (fun x => (u₄ x - v₄ x) ^ 2) volume)
    (hv₁ : Integrable (fun x => v₁ x ^ 2) volume)
    (hv₂ : Integrable (fun x => v₂ x ^ 2) volume)
    (hv₃ : Integrable (fun x => v₃ x ^ 2) volume)
    (hv₄ : Integrable (fun x => v₄ x ^ 2) volume)
    (h₁diff_bound : (∫ x : ℝ, (u₁ x - v₁ x) ^ 2) ≤ H₁ ^ 2 * rho ^ 2)
    (h₂diff_bound : (∫ x : ℝ, (u₂ x - v₂ x) ^ 2) ≤ H₂ ^ 2 * rho ^ 2)
    (h₃diff_bound : (∫ x : ℝ, (u₃ x - v₃ x) ^ 2) ≤ H₃ ^ 2 * rho ^ 2)
    (h₄diff_bound : (∫ x : ℝ, (u₄ x - v₄ x) ^ 2) ≤ H₄ ^ 2 * rho ^ 2)
    (hv₁_bound : (∫ x : ℝ, v₁ x ^ 2) ≤ E₁ ^ 2)
    (hv₂_bound : (∫ x : ℝ, v₂ x ^ 2) ≤ E₂ ^ 2)
    (hv₃_bound : (∫ x : ℝ, v₃ x ^ 2) ≤ E₃ ^ 2)
    (hv₄_bound : (∫ x : ℝ, v₄ x ^ 2) ≤ E₄ ^ 2) :
    Integrable (fun x =>
      ((a₁ x * u₁ x + a₂ x * u₂ x + a₃ x * u₃ x + a₄ x * u₄ x) -
        (b₁ x * v₁ x + b₂ x * v₂ x + b₃ x * v₃ x + b₄ x * v₄ x)) ^ 2) volume ∧
      (∫ x : ℝ,
        ((a₁ x * u₁ x + a₂ x * u₂ x + a₃ x * u₃ x + a₄ x * u₄ x) -
          (b₁ x * v₁ x + b₂ x * v₂ x + b₃ x * v₃ x + b₄ x * v₄ x)) ^ 2) ≤
        8 * ((B₁ ^ 2 * H₁ ^ 2 + D₁ ^ 2 * E₁ ^ 2) +
          (B₂ ^ 2 * H₂ ^ 2 + D₂ ^ 2 * E₂ ^ 2) +
          (B₃ ^ 2 * H₃ ^ 2 + D₃ ^ 2 * E₃ ^ 2) +
          (B₄ ^ 2 * H₄ ^ 2 + D₄ ^ 2 * E₄ ^ 2)) * rho ^ 2 := by
  have h₁ := integral_mul_sub_mul_sq_data_of_modulus
    hB₁ hD₁ hE₁ hH₁ hrho ha₁ hab₁ h₁meas h₁diff hv₁
      h₁diff_bound hv₁_bound
  have h₂ := integral_mul_sub_mul_sq_data_of_modulus
    hB₂ hD₂ hE₂ hH₂ hrho ha₂ hab₂ h₂meas h₂diff hv₂
      h₂diff_bound hv₂_bound
  have h₃ := integral_mul_sub_mul_sq_data_of_modulus
    hB₃ hD₃ hE₃ hH₃ hrho ha₃ hab₃ h₃meas h₃diff hv₃
      h₃diff_bound hv₃_bound
  have h₄ := integral_mul_sub_mul_sq_data_of_modulus
    hB₄ hD₄ hE₄ hH₄ hrho ha₄ hab₄ h₄meas h₄diff hv₄
      h₄diff_bound hv₄_bound
  have hsum := integral_four_sum_sub_sq_data hout_meas h₁.1 h₂.1 h₃.1 h₄.1
  refine ⟨hsum.1, hsum.2.trans ?_⟩
  calc
    4 * ((∫ x : ℝ, (a₁ x * u₁ x - b₁ x * v₁ x) ^ 2) +
          (∫ x : ℝ, (a₂ x * u₂ x - b₂ x * v₂ x) ^ 2) +
          (∫ x : ℝ, (a₃ x * u₃ x - b₃ x * v₃ x) ^ 2) +
          (∫ x : ℝ, (a₄ x * u₄ x - b₄ x * v₄ x) ^ 2)) ≤
        4 * (2 * (B₁ ^ 2 * H₁ ^ 2 + D₁ ^ 2 * E₁ ^ 2) * rho ^ 2 +
          2 * (B₂ ^ 2 * H₂ ^ 2 + D₂ ^ 2 * E₂ ^ 2) * rho ^ 2 +
          2 * (B₃ ^ 2 * H₃ ^ 2 + D₃ ^ 2 * E₃ ^ 2) * rho ^ 2 +
          2 * (B₄ ^ 2 * H₄ ^ 2 + D₄ ^ 2 * E₄ ^ 2) * rho ^ 2) := by
            nlinarith [h₁.2, h₂.2, h₃.2, h₄.2]
    _ = 8 * ((B₁ ^ 2 * H₁ ^ 2 + D₁ ^ 2 * E₁ ^ 2) +
          (B₂ ^ 2 * H₂ ^ 2 + D₂ ^ 2 * E₂ ^ 2) +
          (B₃ ^ 2 * H₃ ^ 2 + D₃ ^ 2 * E₃ ^ 2) +
          (B₄ ^ 2 * H₄ ^ 2 + D₄ ^ 2 * E₄ ^ 2)) * rho ^ 2 := by
      ring

/-! ## Expanded forcing at one common modulus -/

/-- Quantitative exact-weight estimate for the four-product expanded
chemotactic flux derivative. -/
theorem paper5WeightedFluxDerivativeExpandedTrajectory_sub_sq_data_of_modulus
    (p : CMParams) (eta : ℝ)
    {u v : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {W Wx Z Zx : ℝ → ℝ → ℝ} {s t : ℝ}
    {K₁ K₂ K₃ K₄ D₁ D₂ : ℝ}
    {EW EWx EZ EZx HW HWx HZ HZx rho : ℝ}
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hK₃ : 0 ≤ K₃) (hK₄ : 0 ≤ K₄)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hEW : 0 ≤ EW) (hEWx : 0 ≤ EWx)
    (hEZ : 0 ≤ EZ) (hEZx : 0 ≤ EZx)
    (hHW : 0 ≤ HW) (hHWx : 0 ≤ HWx)
    (hHZ : 0 ≤ HZ) (hHZx : 0 ≤ HZx)
    (hrho : 0 ≤ rho)
    (hB₁_bound : ∀ x, |paper5B1 p u v s x| ≤ K₁)
    (hB₁_diff : ∀ x,
      |paper5B1 p u v s x - paper5B1 p u v t x| ≤ D₁ * rho)
    (hB₂_bound : ∀ x,
      |paper5WeightedFluxPopulationCoefficient p eta u v U s x| ≤ K₂)
    (hB₂_diff : ∀ x,
      |paper5WeightedFluxPopulationCoefficient p eta u v U s x -
        paper5WeightedFluxPopulationCoefficient p eta u v U t x| ≤
          D₂ * rho)
    (hB₃_bound : ∀ x, |paper5B3 p U x| ≤ K₃)
    (hB₄_bound : ∀ x,
      |paper5WeightedFluxSignalCoefficient p eta U x| ≤ K₄)
    (hB₁_meas : ∀ q,
      AEStronglyMeasurable (paper5B1 p u v q) volume)
    (hB₂_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedFluxPopulationCoefficient p eta u v U q) volume)
    (hB₃_meas : AEStronglyMeasurable (paper5B3 p U) volume)
    (hB₄_meas : AEStronglyMeasurable
      (paper5WeightedFluxSignalCoefficient p eta U) volume)
    (hW_meas : ∀ q, AEStronglyMeasurable (W q) volume)
    (hWx_meas : ∀ q, AEStronglyMeasurable (Wx q) volume)
    (hZ_meas : ∀ q, AEStronglyMeasurable (Z q) volume)
    (hZx_meas : ∀ q, AEStronglyMeasurable (Zx q) volume)
    (hW_diff : Integrable (fun x => (W s x - W t x) ^ 2) volume)
    (hWx_diff : Integrable (fun x => (Wx s x - Wx t x) ^ 2) volume)
    (hZ_diff : Integrable (fun x => (Z s x - Z t x) ^ 2) volume)
    (hZx_diff : Integrable (fun x => (Zx s x - Zx t x) ^ 2) volume)
    (hW_t : Integrable (fun x => W t x ^ 2) volume)
    (hWx_t : Integrable (fun x => Wx t x ^ 2) volume)
    (hZ_t : Integrable (fun x => Z t x ^ 2) volume)
    (hZx_t : Integrable (fun x => Zx t x ^ 2) volume)
    (hW_diff_bound : (∫ x : ℝ, (W s x - W t x) ^ 2) ≤ HW ^ 2 * rho ^ 2)
    (hWx_diff_bound : (∫ x : ℝ, (Wx s x - Wx t x) ^ 2) ≤ HWx ^ 2 * rho ^ 2)
    (hZ_diff_bound : (∫ x : ℝ, (Z s x - Z t x) ^ 2) ≤ HZ ^ 2 * rho ^ 2)
    (hZx_diff_bound : (∫ x : ℝ, (Zx s x - Zx t x) ^ 2) ≤ HZx ^ 2 * rho ^ 2)
    (hW_t_bound : (∫ x : ℝ, W t x ^ 2) ≤ EW ^ 2)
    (hWx_t_bound : (∫ x : ℝ, Wx t x ^ 2) ≤ EWx ^ 2)
    (hZ_t_bound : (∫ x : ℝ, Z t x ^ 2) ≤ EZ ^ 2)
    (hZx_t_bound : (∫ x : ℝ, Zx t x ^ 2) ≤ EZx ^ 2) :
    Integrable (fun x =>
      (paper5WeightedFluxDerivativeExpandedTrajectory
          p eta u v U W Wx Z Zx s x -
        paper5WeightedFluxDerivativeExpandedTrajectory
          p eta u v U W Wx Z Zx t x) ^ 2) volume ∧
      (∫ x : ℝ,
        (paper5WeightedFluxDerivativeExpandedTrajectory
            p eta u v U W Wx Z Zx s x -
          paper5WeightedFluxDerivativeExpandedTrajectory
            p eta u v U W Wx Z Zx t x) ^ 2) ≤
        8 * ((K₁ ^ 2 * HWx ^ 2 + D₁ ^ 2 * EWx ^ 2) +
          (K₂ ^ 2 * HW ^ 2 + D₂ ^ 2 * EW ^ 2) +
          K₃ ^ 2 * HZx ^ 2 + K₄ ^ 2 * HZ ^ 2) * rho ^ 2 := by
  let a₁ : ℝ → ℝ := paper5B1 p u v s
  let b₁ : ℝ → ℝ := paper5B1 p u v t
  let a₂ : ℝ → ℝ := paper5WeightedFluxPopulationCoefficient p eta u v U s
  let b₂ : ℝ → ℝ := paper5WeightedFluxPopulationCoefficient p eta u v U t
  let a₃ : ℝ → ℝ := paper5B3 p U
  let a₄ : ℝ → ℝ := paper5WeightedFluxSignalCoefficient p eta U
  have h₁meas : AEStronglyMeasurable
      (fun x => a₁ x * Wx s x - b₁ x * Wx t x) volume :=
    ((hB₁_meas s).mul (hWx_meas s)).sub ((hB₁_meas t).mul (hWx_meas t))
  have h₂meas : AEStronglyMeasurable
      (fun x => a₂ x * W s x - b₂ x * W t x) volume :=
    ((hB₂_meas s).mul (hW_meas s)).sub ((hB₂_meas t).mul (hW_meas t))
  have h₃meas : AEStronglyMeasurable
      (fun x => a₃ x * Zx s x - a₃ x * Zx t x) volume :=
    (hB₃_meas.mul (hZx_meas s)).sub (hB₃_meas.mul (hZx_meas t))
  have h₄meas : AEStronglyMeasurable
      (fun x => a₄ x * Z s x - a₄ x * Z t x) volume :=
    (hB₄_meas.mul (hZ_meas s)).sub (hB₄_meas.mul (hZ_meas t))
  have hsum_s : AEStronglyMeasurable (fun x =>
      a₁ x * Wx s x + a₂ x * W s x + a₃ x * Zx s x + a₄ x * Z s x)
      volume :=
    ((((hB₁_meas s).mul (hWx_meas s)).add
      ((hB₂_meas s).mul (hW_meas s))).add
      (hB₃_meas.mul (hZx_meas s))).add
      (hB₄_meas.mul (hZ_meas s))
  have hsum_t : AEStronglyMeasurable (fun x =>
      b₁ x * Wx t x + b₂ x * W t x + a₃ x * Zx t x + a₄ x * Z t x)
      volume :=
    ((((hB₁_meas t).mul (hWx_meas t)).add
      ((hB₂_meas t).mul (hW_meas t))).add
      (hB₃_meas.mul (hZx_meas t))).add
      (hB₄_meas.mul (hZ_meas t))
  have hout_meas : AEStronglyMeasurable (fun x =>
      (a₁ x * Wx s x + a₂ x * W s x + a₃ x * Zx s x + a₄ x * Z s x) -
        (b₁ x * Wx t x + b₂ x * W t x + a₃ x * Zx t x + a₄ x * Z t x)) volume :=
    hsum_s.sub hsum_t
  have hraw := integral_four_product_sum_sub_sq_data_of_modulus
    hK₁ hK₂ hK₃ hK₄ hD₁ hD₂ (show 0 ≤ (0 : ℝ) by norm_num)
      (show 0 ≤ (0 : ℝ) by norm_num)
      hEWx hEW hEZx hEZ hHWx hHW hHZx hHZ hrho
      hB₁_bound hB₂_bound hB₃_bound hB₄_bound
      hB₁_diff hB₂_diff (fun x => by simp [a₃]) (fun x => by simp [a₄])
      hout_meas h₁meas h₂meas h₃meas h₄meas
      hWx_diff hW_diff hZx_diff hZ_diff hWx_t hW_t hZx_t hZ_t
      hWx_diff_bound hW_diff_bound hZx_diff_bound hZ_diff_bound
      hWx_t_bound hW_t_bound hZx_t_bound hZ_t_bound
  simpa [paper5WeightedFluxDerivativeExpandedTrajectory,
    paper5WeightedFluxDerivativeExpanded,
    paper5WeightedFluxPopulationCoefficient,
    paper5WeightedFluxSignalCoefficient, a₁, b₁, a₂, b₂, a₃, a₄] using hraw

/-- Quantitative exact-weight estimate for the reaction mean-coefficient
product. -/
theorem paper5WeightedReactionExpandedTrajectory_sub_sq_data_of_modulus
    (p : CMParams)
    {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {W : ℝ → ℝ → ℝ} {s t : ℝ}
    {K D EW HW rho : ℝ}
    (hK : 0 ≤ K) (hD : 0 ≤ D) (hEW : 0 ≤ EW) (hHW : 0 ≤ HW)
    (hrho : 0 ≤ rho)
    (hcoef_bound : ∀ x,
      |1 - paper5A (1 + p.α) u U s x| ≤ K)
    (hcoef_diff : ∀ x,
      |(1 - paper5A (1 + p.α) u U s x) -
        (1 - paper5A (1 + p.α) u U t x)| ≤ D * rho)
    (hcoef_meas : ∀ q, AEStronglyMeasurable
      (fun x => 1 - paper5A (1 + p.α) u U q x) volume)
    (hW_meas : ∀ q, AEStronglyMeasurable (W q) volume)
    (hW_diff : Integrable (fun x => (W s x - W t x) ^ 2) volume)
    (hW_t : Integrable (fun x => W t x ^ 2) volume)
    (hW_diff_bound : (∫ x : ℝ, (W s x - W t x) ^ 2) ≤ HW ^ 2 * rho ^ 2)
    (hW_t_bound : (∫ x : ℝ, W t x ^ 2) ≤ EW ^ 2) :
    Integrable (fun x =>
      (paper5WeightedReactionExpandedTrajectory p u U W s x -
        paper5WeightedReactionExpandedTrajectory p u U W t x) ^ 2) volume ∧
      (∫ x : ℝ,
        (paper5WeightedReactionExpandedTrajectory p u U W s x -
          paper5WeightedReactionExpandedTrajectory p u U W t x) ^ 2) ≤
        2 * (K ^ 2 * HW ^ 2 + D ^ 2 * EW ^ 2) * rho ^ 2 := by
  let as : ℝ → ℝ := fun x => 1 - paper5A (1 + p.α) u U s x
  let bt : ℝ → ℝ := fun x => 1 - paper5A (1 + p.α) u U t x
  have hout_meas : AEStronglyMeasurable
      (fun x => as x * W s x - bt x * W t x) volume :=
    ((hcoef_meas s).mul (hW_meas s)).sub ((hcoef_meas t).mul (hW_meas t))
  simpa [paper5WeightedReactionExpandedTrajectory, as, bt] using
    (integral_mul_sub_mul_sq_data_of_modulus
      hK hD hEW hHW hrho hcoef_bound hcoef_diff hout_meas
        hW_diff hW_t hW_diff_bound hW_t_bound)

/-- A fixed scalar multiple of one varying field plus a second varying field
retains an explicit common square modulus.  `CF` and `CR` are squared
modulus constants, so no square-root algebra is needed in scalar forcing
assemblies. -/
theorem integral_const_mul_add_sub_sq_data_of_modulus
    {Fₛ Fₜ Rₛ Rₜ : ℝ → ℝ} {q CF CR rho : ℝ}
    (hCF : 0 ≤ CF) (hCR : 0 ≤ CR) (hrho : 0 ≤ rho)
    (hout_meas : AEStronglyMeasurable (fun x =>
      (q * Fₛ x + Rₛ x) - (q * Fₜ x + Rₜ x)) volume)
    (hF : Integrable (fun x => (Fₛ x - Fₜ x) ^ 2) volume)
    (hR : Integrable (fun x => (Rₛ x - Rₜ x) ^ 2) volume)
    (hF_bound : (∫ x : ℝ, (Fₛ x - Fₜ x) ^ 2) ≤ CF * rho ^ 2)
    (hR_bound : (∫ x : ℝ, (Rₛ x - Rₜ x) ^ 2) ≤ CR * rho ^ 2) :
    Integrable (fun x =>
      ((q * Fₛ x + Rₛ x) - (q * Fₜ x + Rₜ x)) ^ 2) volume ∧
      (∫ x : ℝ,
        ((q * Fₛ x + Rₛ x) - (q * Fₜ x + Rₜ x)) ^ 2) ≤
        2 * (q ^ 2 * CF + CR) * rho ^ 2 := by
  let major : ℝ → ℝ := fun x =>
    2 * q ^ 2 * (Fₛ x - Fₜ x) ^ 2 + 2 * (Rₛ x - Rₜ x) ^ 2
  have hmajor : Integrable major volume :=
    (hF.const_mul (2 * q ^ 2)).add (hR.const_mul 2)
  have hpoint : ∀ x,
      ((q * Fₛ x + Rₛ x) - (q * Fₜ x + Rₜ x)) ^ 2 ≤ major x := by
    intro x
    dsimp only [major]
    have hsquare :
        (q * (Fₛ x - Fₜ x) + (Rₛ x - Rₜ x)) ^ 2 ≤
          2 * (q * (Fₛ x - Fₜ x)) ^ 2 +
            2 * (Rₛ x - Rₜ x) ^ 2 := by
      nlinarith [sq_nonneg
        (q * (Fₛ x - Fₜ x) - (Rₛ x - Rₜ x))]
    convert hsquare using 1 <;> ring
  have hout : Integrable (fun x =>
      ((q * Fₛ x + Rₛ x) - (q * Fₜ x + Rₜ x)) ^ 2) volume := by
    refine hmajor.mono' (hout_meas.pow 2) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint x
  refine ⟨hout, ?_⟩
  calc
    (∫ x : ℝ,
        ((q * Fₛ x + Rₛ x) - (q * Fₜ x + Rₜ x)) ^ 2) ≤
        ∫ x : ℝ, major x := integral_mono hout hmajor hpoint
    _ = 2 * q ^ 2 * (∫ x : ℝ, (Fₛ x - Fₜ x) ^ 2) +
          2 * (∫ x : ℝ, (Rₛ x - Rₜ x) ^ 2) := by
      dsimp only [major]
      rw [integral_add, integral_const_mul, integral_const_mul]
      · exact hF.const_mul _
      · exact hR.const_mul _
    _ ≤ 2 * q ^ 2 * (CF * rho ^ 2) + 2 * (CR * rho ^ 2) := by
      gcongr
    _ = 2 * (q ^ 2 * CF + CR) * rho ^ 2 := by ring

/-- Quantitative expanded generator-forcing closure from independently
estimated flux and reaction differences. -/
theorem paper5WeightedGeneratorForcingExpandedTrajectory_sub_sq_data_of_flux_reaction_modulus
    (p : CMParams) (eta : ℝ)
    {u v : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {W Wx Z Zx : ℝ → ℝ → ℝ} {s t CF CR rho : ℝ}
    (hCF : 0 ≤ CF) (hCR : 0 ≤ CR) (hrho : 0 ≤ rho)
    (hflux_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedFluxDerivativeExpandedTrajectory
        p eta u v U W Wx Z Zx q) volume)
    (hreact_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedReactionExpandedTrajectory p u U W q) volume)
    (hflux : Integrable (fun x =>
      (paper5WeightedFluxDerivativeExpandedTrajectory
          p eta u v U W Wx Z Zx s x -
        paper5WeightedFluxDerivativeExpandedTrajectory
          p eta u v U W Wx Z Zx t x) ^ 2) volume)
    (hreact : Integrable (fun x =>
      (paper5WeightedReactionExpandedTrajectory p u U W s x -
        paper5WeightedReactionExpandedTrajectory p u U W t x) ^ 2) volume)
    (hflux_bound : (∫ x : ℝ,
      (paper5WeightedFluxDerivativeExpandedTrajectory
          p eta u v U W Wx Z Zx s x -
        paper5WeightedFluxDerivativeExpandedTrajectory
          p eta u v U W Wx Z Zx t x) ^ 2) ≤ CF * rho ^ 2)
    (hreact_bound : (∫ x : ℝ,
      (paper5WeightedReactionExpandedTrajectory p u U W s x -
        paper5WeightedReactionExpandedTrajectory p u U W t x) ^ 2) ≤
          CR * rho ^ 2) :
    Integrable (fun x =>
      (paper5WeightedGeneratorForcingExpandedTrajectory
          p eta u v U W Wx Z Zx s x -
        paper5WeightedGeneratorForcingExpandedTrajectory
          p eta u v U W Wx Z Zx t x) ^ 2) volume ∧
      (∫ x : ℝ,
        (paper5WeightedGeneratorForcingExpandedTrajectory
            p eta u v U W Wx Z Zx s x -
          paper5WeightedGeneratorForcingExpandedTrajectory
            p eta u v U W Wx Z Zx t x) ^ 2) ≤
        2 * (p.χ ^ 2 * CF + CR) * rho ^ 2 := by
  have hout_meas : AEStronglyMeasurable (fun x =>
      (-p.χ * paper5WeightedFluxDerivativeExpandedTrajectory
          p eta u v U W Wx Z Zx s x +
        paper5WeightedReactionExpandedTrajectory p u U W s x) -
      (-p.χ * paper5WeightedFluxDerivativeExpandedTrajectory
          p eta u v U W Wx Z Zx t x +
        paper5WeightedReactionExpandedTrajectory p u U W t x)) volume :=
    (((hflux_meas s).const_mul (-p.χ)).add (hreact_meas s)).sub
      (((hflux_meas t).const_mul (-p.χ)).add (hreact_meas t))
  simpa [paper5WeightedGeneratorForcingExpandedTrajectory] using
    (integral_const_mul_add_sub_sq_data_of_modulus
      hCF hCR hrho hout_meas hflux hreact hflux_bound hreact_bound)

/-! ## Canonical `L²` norm form -/

/-- A concrete square-integral modulus is an unsquared modulus for the
canonical `L²` section. -/
theorem wholeLineRealL2Section_norm_sub_le_of_integral_sub_sq_le_modulus
    {g : ℝ → ℝ → ℝ}
    (hg_meas : ∀ q, AEStronglyMeasurable (g q) volume)
    (hg_sq : ∀ q, Integrable (fun x => g q x ^ 2) volume)
    {s t C rho : ℝ} (hC : 0 ≤ C) (hrho : 0 ≤ rho)
    (hbound : (∫ x : ℝ, (g s x - g t x) ^ 2) ≤ C * rho ^ 2) :
    ‖wholeLineRealL2Section g hg_meas hg_sq s -
        wholeLineRealL2Section g hg_meas hg_sq t‖ ≤ Real.sqrt C * rho := by
  have hnorm := wholeLineRealL2Section_norm_sub_sq g hg_meas hg_sq s t
  have hsqrt : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt hC
  have hright : 0 ≤ Real.sqrt C * rho :=
    mul_nonneg (Real.sqrt_nonneg C) hrho
  apply (sq_le_sq₀ (norm_nonneg _) hright).mp
  rw [hnorm]
  calc
    (∫ x : ℝ, (g s x - g t x) ^ 2) ≤ C * rho ^ 2 := hbound
    _ = (Real.sqrt C * rho) ^ 2 := by rw [mul_pow, hsqrt]

/-- Unsquared Hilbert norm form for the canonical expanded generator
forcing trajectory. -/
theorem paper5WeightedGeneratorForcingExpandedL2Trajectory_norm_sub_le_of_modulus
    (p : CMParams) (eta : ℝ)
    (u v : ℝ → ℝ → ℝ) (U : ℝ → ℝ)
    (W Wx Z Zx : ℝ → ℝ → ℝ)
    (hF_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedGeneratorForcingExpandedTrajectory
        p eta u v U W Wx Z Zx q) volume)
    (hF_sq : ∀ q, Integrable (fun x =>
      paper5WeightedGeneratorForcingExpandedTrajectory
        p eta u v U W Wx Z Zx q x ^ 2) volume)
    {s t C rho : ℝ} (hC : 0 ≤ C) (hrho : 0 ≤ rho)
    (hbound : (∫ x : ℝ,
      (paper5WeightedGeneratorForcingExpandedTrajectory
          p eta u v U W Wx Z Zx s x -
        paper5WeightedGeneratorForcingExpandedTrajectory
          p eta u v U W Wx Z Zx t x) ^ 2) ≤ C * rho ^ 2) :
    ‖paper5WeightedGeneratorForcingExpandedL2Trajectory
          p eta u v U W Wx Z Zx hF_meas hF_sq s -
        paper5WeightedGeneratorForcingExpandedL2Trajectory
          p eta u v U W Wx Z Zx hF_meas hF_sq t‖ ≤
      Real.sqrt C * rho := by
  exact wholeLineRealL2Section_norm_sub_le_of_integral_sub_sq_le_modulus
    hF_meas hF_sq hC hrho hbound

/-! ## Quantitative resolver transfer -/

set_option maxHeartbeats 4000000 in
/-- The frozen resolver transfers a common exact-weight population modulus
to both the weighted signal and its first weighted derivative.  The
reference profiles cancel from the two time differences. -/
theorem paper5WeightedSignal_sub_sq_data_of_population_modulus
    (p : CMParams) {M eta s t HW rho : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hM : 1 ≤ M) (heta : 0 < eta) (heta1 : eta < 1)
    (huC : ∀ q, IsCUnifBdd (u q))
    (huM : ∀ q x, u q x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : ∀ q, v q = frozenElliptic p (u q))
    (hvDiff : ∀ q, Differentiable ℝ (v q))
    (hHW : 0 ≤ HW) (hrho : 0 ≤ rho)
    (hW_diff : Integrable (fun x =>
      (paper5WeightedPopulation eta u U s x -
        paper5WeightedPopulation eta u U t x) ^ 2) volume)
    (hW_diff_bound : (∫ x : ℝ,
      (paper5WeightedPopulation eta u U s x -
        paper5WeightedPopulation eta u U t x) ^ 2) ≤ HW ^ 2 * rho ^ 2) :
    Integrable (fun x =>
      (paper5WeightedSignal eta v V s x -
        paper5WeightedSignal eta v V t x) ^ 2) volume ∧
      Integrable (fun x =>
        (paper5WeightedSignalX eta v V s x -
          paper5WeightedSignalX eta v V t x) ^ 2) volume ∧
      (∫ x : ℝ,
        (paper5WeightedSignal eta v V s x -
          paper5WeightedSignal eta v V t x) ^ 2) ≤
        paper5WeightedResolverVFactor p M eta * HW ^ 2 * rho ^ 2 ∧
      (∫ x : ℝ,
        (paper5WeightedSignalX eta v V s x -
          paper5WeightedSignalX eta v V t x) ^ 2) ≤
        paper5WeightedResolverVxFactor p M eta * HW ^ 2 * rho ^ 2 := by
  have hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) * |u s x - u t x| ^ 2) volume := by
    refine hW_diff.congr (Eventually.of_forall fun x => ?_)
    unfold paper5WeightedPopulation
    change
      (Real.exp (eta * x) * (u s x - U x) -
          Real.exp (eta * x) * (u t x - U x)) ^ 2 =
        Real.exp (2 * eta * x) * |u s x - u t x| ^ 2
    rw [show
        (Real.exp (eta * x) * (u s x - U x) -
            Real.exp (eta * x) * (u t x - U x)) =
          Real.exp (eta * x) * (u s x - u t x) by ring,
      mul_pow, sq_abs]
    congr 1
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hcoU : coMovingPath 0 u s = u s := by
    funext x
    simp [coMovingPath]
  have hcoV : coMovingPath 0 v s = v s := by
    funext x
    simp [coMovingPath]
  have hclose_co : Integrable (fun x =>
      Real.exp (2 * eta * x) * |coMovingPath 0 u s x - u t x| ^ 2) volume := by
    simpa only [hcoU] using hclose
  have hraw := paper5WeightedSignal_resolver_data
    p (c := 0) (t := s) (u := u) (v := v) (U := u t) (V := v t)
      hM heta heta1
      (by simpa only [hcoU] using huC s) (huC t)
      (by simpa only [hcoU] using huM s) (huM t)
      (by simpa only [hcoU, hcoV] using hvEq s) (hvEq t)
      (by simpa only [hcoV] using hvDiff s) (hvDiff t) hclose_co
  have hWfun :
      paper5WeightedPopulation eta (coMovingPath 0 u) (u t) s =
        fun x => paper5WeightedPopulation eta u U s x -
          paper5WeightedPopulation eta u U t x := by
    funext x
    simp only [paper5WeightedPopulation, coMovingPath, zero_mul, add_zero]
    ring
  have hZfun :
      paper5WeightedSignal eta (coMovingPath 0 v) (v t) s =
        fun x => paper5WeightedSignal eta v V s x -
          paper5WeightedSignal eta v V t x := by
    funext x
    simp only [paper5WeightedSignal, coMovingPath, zero_mul, add_zero]
    ring
  have hZxfun :
      paper5WeightedSignalX eta (coMovingPath 0 v) (v t) s =
        fun x => paper5WeightedSignalX eta v V s x -
          paper5WeightedSignalX eta v V t x := by
    funext x
    simp only [paper5WeightedSignalX, paper5WeightedSignal,
      coMovingPath, zero_mul, add_zero]
    rw [congrArg (fun f : ℝ → ℝ => deriv f x) hcoV]
    ring
  rw [hWfun, hZfun, hZxfun] at hraw
  have hRV : 0 ≤ paper5WeightedResolverVFactor p M eta := by
    unfold paper5WeightedResolverVFactor
    exact div_nonneg
      (mul_nonneg (sq_nonneg p.γ)
        (Real.rpow_nonneg (zero_le_one.trans hM) _))
      (sq_nonneg (1 - eta))
  have hetaSq : eta ^ 2 < 1 := by
    have hprod : 0 < (1 - eta) * (1 + eta) :=
      mul_pos (sub_pos.mpr heta1) (by linarith)
    nlinarith
  have hRVx : 0 ≤ paper5WeightedResolverVxFactor p M eta := by
    unfold paper5WeightedResolverVxFactor
    exact div_nonneg
      (mul_nonneg (sq_nonneg p.γ)
        (Real.rpow_nonneg (zero_le_one.trans hM) _))
      (sub_nonneg.mpr hetaSq.le)
  have hZint : Integrable (fun x =>
      (paper5WeightedSignal eta v V s x -
        paper5WeightedSignal eta v V t x) ^ 2) volume := by
    exact hraw.1
  have hZxint : Integrable (fun x =>
      (paper5WeightedSignalX eta v V s x -
        paper5WeightedSignalX eta v V t x) ^ 2) volume := by
    exact hraw.2.1
  have hZbound : (∫ x : ℝ,
      (paper5WeightedSignal eta v V s x -
        paper5WeightedSignal eta v V t x) ^ 2) ≤
      paper5WeightedResolverVFactor p M eta * HW ^ 2 * rho ^ 2 := by
    calc
      (∫ x : ℝ,
          (paper5WeightedSignal eta v V s x -
            paper5WeightedSignal eta v V t x) ^ 2) ≤
        paper5WeightedResolverVFactor p M eta *
          (∫ x : ℝ,
            (paper5WeightedPopulation eta u U s x -
              paper5WeightedPopulation eta u U t x) ^ 2) := hraw.2.2.1
      _ ≤ paper5WeightedResolverVFactor p M eta *
          (HW ^ 2 * rho ^ 2) :=
        mul_le_mul_of_nonneg_left hW_diff_bound hRV
      _ = paper5WeightedResolverVFactor p M eta * HW ^ 2 * rho ^ 2 := by ring
  have hZxbound : (∫ x : ℝ,
      (paper5WeightedSignalX eta v V s x -
        paper5WeightedSignalX eta v V t x) ^ 2) ≤
      paper5WeightedResolverVxFactor p M eta * HW ^ 2 * rho ^ 2 := by
    calc
      (∫ x : ℝ,
          (paper5WeightedSignalX eta v V s x -
            paper5WeightedSignalX eta v V t x) ^ 2) ≤
        paper5WeightedResolverVxFactor p M eta *
          (∫ x : ℝ,
            (paper5WeightedPopulation eta u U s x -
              paper5WeightedPopulation eta u U t x) ^ 2) := hraw.2.2.2
      _ ≤ paper5WeightedResolverVxFactor p M eta *
          (HW ^ 2 * rho ^ 2) :=
        mul_le_mul_of_nonneg_left hW_diff_bound hRVx
      _ = paper5WeightedResolverVxFactor p M eta * HW ^ 2 * rho ^ 2 := by ring
  exact ⟨hZint, hZxint, hZbound, hZxbound⟩

/-! ## Population-`H¹` capstone -/

/-- Squared modulus constant for the four expanded flux products. -/
def paper5WeightedFluxHolderSquareConst
    (K₁ K₂ K₃ K₄ D₁ D₂ EWx EW HWx HW HZx HZ : ℝ) : ℝ :=
  8 * ((K₁ ^ 2 * HWx ^ 2 + D₁ ^ 2 * EWx ^ 2) +
    (K₂ ^ 2 * HW ^ 2 + D₂ ^ 2 * EW ^ 2) +
    K₃ ^ 2 * HZx ^ 2 + K₄ ^ 2 * HZ ^ 2)

/-- Squared modulus constant for the reaction product. -/
def paper5WeightedReactionHolderSquareConst
    (KR DR EW HW : ℝ) : ℝ :=
  2 * (KR ^ 2 * HW ^ 2 + DR ^ 2 * EW ^ 2)

/-- Squared modulus constant for the full expanded generator forcing. -/
def paper5WeightedGeneratorForcingHolderSquareConst
    (p : CMParams)
    (K₁ K₂ K₃ K₄ KR D₁ D₂ DR EWx EW HWx HW HZx HZ : ℝ) : ℝ :=
  2 * (p.χ ^ 2 * paper5WeightedFluxHolderSquareConst
      K₁ K₂ K₃ K₄ D₁ D₂ EWx EW HWx HW HZx HZ +
    paper5WeightedReactionHolderSquareConst KR DR EW HW)

set_option maxHeartbeats 3000000 in
/-- Exact-weight quantitative forcing capstone.  A common `L²` modulus for
the weighted population and its first spatial derivative, coefficient
sup-moduli, and the frozen-resolver transfer give a genuine unsquared
Hilbert-space modulus for the canonical expanded forcing trajectory. -/
theorem paper5WeightedGeneratorForcingExpandedL2Trajectory_norm_sub_le_of_population_H1_modulus
    (p : CMParams) {M eta s t rho : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    {K₁ K₂ K₃ K₄ KR D₁ D₂ DR : ℝ}
    {EW EWx EZ EZx HW HWx : ℝ}
    (hM : 1 ≤ M) (heta : 0 < eta) (heta1 : eta < 1)
    (huC : ∀ q, IsCUnifBdd (u q))
    (huM : ∀ q x, u q x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : ∀ q, v q = frozenElliptic p (u q))
    (hvDiff : ∀ q, Differentiable ℝ (v q))
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hK₃ : 0 ≤ K₃) (hK₄ : 0 ≤ K₄) (hKR : 0 ≤ KR)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hDR : 0 ≤ DR)
    (hEW : 0 ≤ EW) (hEWx : 0 ≤ EWx)
    (hEZ : 0 ≤ EZ) (hEZx : 0 ≤ EZx)
    (hHW : 0 ≤ HW) (hHWx : 0 ≤ HWx) (hrho : 0 ≤ rho)
    (hB₁_bound : ∀ x, |paper5B1 p u v s x| ≤ K₁)
    (hB₁_diff : ∀ x,
      |paper5B1 p u v s x - paper5B1 p u v t x| ≤ D₁ * rho)
    (hB₂_bound : ∀ x,
      |paper5WeightedFluxPopulationCoefficient p eta u v U s x| ≤ K₂)
    (hB₂_diff : ∀ x,
      |paper5WeightedFluxPopulationCoefficient p eta u v U s x -
        paper5WeightedFluxPopulationCoefficient p eta u v U t x| ≤ D₂ * rho)
    (hB₃_bound : ∀ x, |paper5B3 p U x| ≤ K₃)
    (hB₄_bound : ∀ x,
      |paper5WeightedFluxSignalCoefficient p eta U x| ≤ K₄)
    (hR_bound : ∀ x, |1 - paper5A (1 + p.α) u U s x| ≤ KR)
    (hR_diff : ∀ x,
      |(1 - paper5A (1 + p.α) u U s x) -
        (1 - paper5A (1 + p.α) u U t x)| ≤ DR * rho)
    (hB₁_meas : ∀ q, AEStronglyMeasurable (paper5B1 p u v q) volume)
    (hB₂_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedFluxPopulationCoefficient p eta u v U q) volume)
    (hB₃_meas : AEStronglyMeasurable (paper5B3 p U) volume)
    (hB₄_meas : AEStronglyMeasurable
      (paper5WeightedFluxSignalCoefficient p eta U) volume)
    (hR_meas : ∀ q, AEStronglyMeasurable
      (fun x => 1 - paper5A (1 + p.α) u U q x) volume)
    (hW_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedPopulation eta u U q) volume)
    (hWx_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedPopulationX eta u U q) volume)
    (hZ_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedSignal eta v V q) volume)
    (hZx_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedSignalX eta v V q) volume)
    (hF_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedGeneratorForcingExpandedTrajectory p eta u v U
        (paper5WeightedPopulation eta u U)
        (paper5WeightedPopulationX eta u U)
        (paper5WeightedSignal eta v V)
        (paper5WeightedSignalX eta v V) q) volume)
    (hF_sq : ∀ q, Integrable (fun x =>
      paper5WeightedGeneratorForcingExpandedTrajectory p eta u v U
        (paper5WeightedPopulation eta u U)
        (paper5WeightedPopulationX eta u U)
        (paper5WeightedSignal eta v V)
        (paper5WeightedSignalX eta v V) q x ^ 2) volume)
    (hW_diff : Integrable (fun x =>
      (paper5WeightedPopulation eta u U s x -
        paper5WeightedPopulation eta u U t x) ^ 2) volume)
    (hWx_diff : Integrable (fun x =>
      (paper5WeightedPopulationX eta u U s x -
        paper5WeightedPopulationX eta u U t x) ^ 2) volume)
    (hW_t : Integrable (fun x => paper5WeightedPopulation eta u U t x ^ 2) volume)
    (hWx_t : Integrable (fun x => paper5WeightedPopulationX eta u U t x ^ 2) volume)
    (hZ_t : Integrable (fun x => paper5WeightedSignal eta v V t x ^ 2) volume)
    (hZx_t : Integrable (fun x => paper5WeightedSignalX eta v V t x ^ 2) volume)
    (hW_diff_bound : (∫ x : ℝ,
      (paper5WeightedPopulation eta u U s x -
        paper5WeightedPopulation eta u U t x) ^ 2) ≤ HW ^ 2 * rho ^ 2)
    (hWx_diff_bound : (∫ x : ℝ,
      (paper5WeightedPopulationX eta u U s x -
        paper5WeightedPopulationX eta u U t x) ^ 2) ≤ HWx ^ 2 * rho ^ 2)
    (hW_t_bound : (∫ x : ℝ,
      paper5WeightedPopulation eta u U t x ^ 2) ≤ EW ^ 2)
    (hWx_t_bound : (∫ x : ℝ,
      paper5WeightedPopulationX eta u U t x ^ 2) ≤ EWx ^ 2)
    (hZ_t_bound : (∫ x : ℝ,
      paper5WeightedSignal eta v V t x ^ 2) ≤ EZ ^ 2)
    (hZx_t_bound : (∫ x : ℝ,
      paper5WeightedSignalX eta v V t x ^ 2) ≤ EZx ^ 2) :
    let HZ := Real.sqrt (paper5WeightedResolverVFactor p M eta) * HW
    let HZx := Real.sqrt (paper5WeightedResolverVxFactor p M eta) * HW
    ‖paper5WeightedGeneratorForcingExpandedL2Trajectory p eta u v U
          (paper5WeightedPopulation eta u U)
          (paper5WeightedPopulationX eta u U)
          (paper5WeightedSignal eta v V)
          (paper5WeightedSignalX eta v V) hF_meas hF_sq s -
        paper5WeightedGeneratorForcingExpandedL2Trajectory p eta u v U
          (paper5WeightedPopulation eta u U)
          (paper5WeightedPopulationX eta u U)
          (paper5WeightedSignal eta v V)
          (paper5WeightedSignalX eta v V) hF_meas hF_sq t‖ ≤
      Real.sqrt (paper5WeightedGeneratorForcingHolderSquareConst p
        K₁ K₂ K₃ K₄ KR D₁ D₂ DR EWx EW HWx HW HZx HZ) * rho := by
  dsimp only
  let RV := paper5WeightedResolverVFactor p M eta
  let RVx := paper5WeightedResolverVxFactor p M eta
  let HZ := Real.sqrt RV * HW
  let HZx := Real.sqrt RVx * HW
  have hRV : 0 ≤ RV := by
    dsimp only [RV, paper5WeightedResolverVFactor]
    exact div_nonneg
      (mul_nonneg (sq_nonneg p.γ) (Real.rpow_nonneg (zero_le_one.trans hM) _))
      (sq_nonneg (1 - eta))
  have hetaSq : eta ^ 2 < 1 := by
    have hprod : 0 < (1 - eta) * (1 + eta) :=
      mul_pos (sub_pos.mpr heta1) (by linarith)
    nlinarith
  have hRVx : 0 ≤ RVx := by
    dsimp only [RVx, paper5WeightedResolverVxFactor]
    exact div_nonneg
      (mul_nonneg (sq_nonneg p.γ) (Real.rpow_nonneg (zero_le_one.trans hM) _))
      (sub_nonneg.mpr hetaSq.le)
  have hHZ : 0 ≤ HZ := mul_nonneg (Real.sqrt_nonneg _) hHW
  have hHZx : 0 ≤ HZx := mul_nonneg (Real.sqrt_nonneg _) hHW
  have hresolver := paper5WeightedSignal_sub_sq_data_of_population_modulus
    p (U := U) (V := V) hM heta heta1 huC huM hvEq hvDiff
      hHW hrho hW_diff hW_diff_bound
  have hZ_diff_bound : (∫ x : ℝ,
      (paper5WeightedSignal eta v V s x -
        paper5WeightedSignal eta v V t x) ^ 2) ≤ HZ ^ 2 * rho ^ 2 := by
    calc
      _ ≤ RV * HW ^ 2 * rho ^ 2 := by simpa only [RV] using hresolver.2.2.1
      _ = HZ ^ 2 * rho ^ 2 := by
        dsimp only [HZ]
        rw [mul_pow, Real.sq_sqrt hRV]
  have hZx_diff_bound : (∫ x : ℝ,
      (paper5WeightedSignalX eta v V s x -
        paper5WeightedSignalX eta v V t x) ^ 2) ≤ HZx ^ 2 * rho ^ 2 := by
    calc
      _ ≤ RVx * HW ^ 2 * rho ^ 2 := by simpa only [RVx] using hresolver.2.2.2
      _ = HZx ^ 2 * rho ^ 2 := by
        dsimp only [HZx]
        rw [mul_pow, Real.sq_sqrt hRVx]
  have hflux :=
    paper5WeightedFluxDerivativeExpandedTrajectory_sub_sq_data_of_modulus
      p eta hK₁ hK₂ hK₃ hK₄ hD₁ hD₂ hEW hEWx hEZ hEZx
        hHW hHWx hHZ hHZx hrho hB₁_bound hB₁_diff hB₂_bound hB₂_diff
        hB₃_bound hB₄_bound hB₁_meas hB₂_meas hB₃_meas hB₄_meas
        hW_meas hWx_meas hZ_meas hZx_meas hW_diff hWx_diff
        hresolver.1 hresolver.2.1 hW_t hWx_t hZ_t hZx_t
        hW_diff_bound hWx_diff_bound hZ_diff_bound hZx_diff_bound
        hW_t_bound hWx_t_bound hZ_t_bound hZx_t_bound
  have hreact :=
    paper5WeightedReactionExpandedTrajectory_sub_sq_data_of_modulus
      p hKR hDR hEW hHW hrho hR_bound hR_diff hR_meas hW_meas
        hW_diff hW_t hW_diff_bound hW_t_bound
  have hflux_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedFluxDerivativeExpandedTrajectory p eta u v U
        (paper5WeightedPopulation eta u U)
        (paper5WeightedPopulationX eta u U)
        (paper5WeightedSignal eta v V)
        (paper5WeightedSignalX eta v V) q) volume := by
    intro q
    exact paper5WeightedFluxDerivativeExpandedTrajectory_aestronglyMeasurable
      p eta q (hB₁_meas q) (hB₂_meas q) hB₃_meas hB₄_meas
        (hW_meas q) (hWx_meas q) (hZ_meas q) (hZx_meas q)
  have hreact_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedReactionExpandedTrajectory p u U
        (paper5WeightedPopulation eta u U) q) volume := by
    intro q
    exact paper5WeightedReactionExpandedTrajectory_aestronglyMeasurable
      p q (hR_meas q) (hW_meas q)
  let CF := paper5WeightedFluxHolderSquareConst
    K₁ K₂ K₃ K₄ D₁ D₂ EWx EW HWx HW HZx HZ
  let CR := paper5WeightedReactionHolderSquareConst KR DR EW HW
  let C := paper5WeightedGeneratorForcingHolderSquareConst p
    K₁ K₂ K₃ K₄ KR D₁ D₂ DR EWx EW HWx HW HZx HZ
  have hCF : 0 ≤ CF := by
    dsimp only [CF, paper5WeightedFluxHolderSquareConst]
    positivity
  have hCR : 0 ≤ CR := by
    dsimp only [CR, paper5WeightedReactionHolderSquareConst]
    positivity
  have hC : 0 ≤ C := by
    dsimp only [C, paper5WeightedGeneratorForcingHolderSquareConst]
    exact mul_nonneg (by norm_num)
      (add_nonneg (mul_nonneg (sq_nonneg p.χ) hCF) hCR)
  have hforcing :=
    paper5WeightedGeneratorForcingExpandedTrajectory_sub_sq_data_of_flux_reaction_modulus
      p eta hCF hCR hrho hflux_meas hreact_meas hflux.1 hreact.1
        (by simpa only [CF, paper5WeightedFluxHolderSquareConst] using hflux.2)
        (by simpa only [CR, paper5WeightedReactionHolderSquareConst] using hreact.2)
  apply paper5WeightedGeneratorForcingExpandedL2Trajectory_norm_sub_le_of_modulus
    p eta u v U (paper5WeightedPopulation eta u U)
      (paper5WeightedPopulationX eta u U)
      (paper5WeightedSignal eta v V) (paper5WeightedSignalX eta v V)
      hF_meas hF_sq hC hrho
  simpa only [C, paper5WeightedGeneratorForcingHolderSquareConst] using hforcing.2

section AxiomAudit

#print axioms integral_mul_sub_mul_sq_data_of_modulus
#print axioms integral_four_product_sum_sub_sq_data_of_modulus
#print axioms
  paper5WeightedFluxDerivativeExpandedTrajectory_sub_sq_data_of_modulus
#print axioms paper5WeightedReactionExpandedTrajectory_sub_sq_data_of_modulus
#print axioms integral_const_mul_add_sub_sq_data_of_modulus
#print axioms
  paper5WeightedGeneratorForcingExpandedTrajectory_sub_sq_data_of_flux_reaction_modulus
#print axioms
  wholeLineRealL2Section_norm_sub_le_of_integral_sub_sq_le_modulus
#print axioms
  paper5WeightedGeneratorForcingExpandedL2Trajectory_norm_sub_le_of_modulus
#print axioms paper5WeightedSignal_sub_sq_data_of_population_modulus
#print axioms
  paper5WeightedGeneratorForcingExpandedL2Trajectory_norm_sub_le_of_population_H1_modulus

end AxiomAudit

end ShenWork.Paper1
