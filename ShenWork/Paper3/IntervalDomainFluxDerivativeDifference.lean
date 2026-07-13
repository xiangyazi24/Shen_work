/- Polarized algebra for the exact route-(a) seven-term flux derivative. -/
import ShenWork.Paper3.IntervalDomainFluxRemainderDerivative

namespace ShenWork.Paper3

open Real

noncomputable section

private theorem abs_mul_three_sub_mul_three_le
    (a₁ b₁ c₁ a₂ b₂ c₂ : ℝ) :
    |a₁ * b₁ * c₁ - a₂ * b₂ * c₂| ≤
      |a₁ - a₂| * |b₁| * |c₁| +
        |a₂| * |b₁ - b₂| * |c₁| +
          |a₂| * |b₂| * |c₁ - c₂| := by
  rw [show a₁ * b₁ * c₁ - a₂ * b₂ * c₂ =
      (a₁ - a₂) * b₁ * c₁ + a₂ * (b₁ - b₂) * c₁ +
        a₂ * b₂ * (c₁ - c₂) by ring]
  calc
    _ ≤ |(a₁ - a₂) * b₁ * c₁ + a₂ * (b₁ - b₂) * c₁| +
        |a₂ * b₂ * (c₁ - c₂)| := abs_add_le _ _
    _ ≤ (|(a₁ - a₂) * b₁ * c₁| +
        |a₂ * (b₁ - b₂) * c₁|) +
          |a₂ * b₂ * (c₁ - c₂)| := by
      gcongr
      exact abs_add_le _ _
    _ = _ := by simp only [abs_mul]

private theorem abs_seven_difference_le
    (a₁ b₁ c₁ d₁ e₁ f₁ g₁ a₂ b₂ c₂ d₂ e₂ f₂ g₂ : ℝ) :
    |(a₁ + b₁ + c₁ + d₁ + e₁ + f₁ + g₁) -
        (a₂ + b₂ + c₂ + d₂ + e₂ + f₂ + g₂)| ≤
      |a₁ - a₂| + |b₁ - b₂| + |c₁ - c₂| + |d₁ - d₂| +
        |e₁ - e₂| + |f₁ - f₂| + |g₁ - g₂| := by
  rw [show
    (a₁ + b₁ + c₁ + d₁ + e₁ + f₁ + g₁) -
        (a₂ + b₂ + c₂ + d₂ + e₂ + f₂ + g₂) =
      (a₁ - a₂) + (b₁ - b₂) + (c₁ - c₂) + (d₁ - d₂) +
        (e₁ - e₂) + (f₁ - f₂) + (g₁ - g₂) by ring]
  calc
    _ ≤ |(a₁ - a₂) + (b₁ - b₂) + (c₁ - c₂) + (d₁ - d₂) +
          (e₁ - e₂) + (f₁ - f₂)| + |g₁ - g₂| := abs_add_le _ _
    _ ≤ (|(a₁ - a₂) + (b₁ - b₂) + (c₁ - c₂) + (d₁ - d₂) +
          (e₁ - e₂)| + |f₁ - f₂|) + |g₁ - g₂| := by gcongr; exact abs_add_le _ _
    _ ≤ ((|(a₁ - a₂) + (b₁ - b₂) + (c₁ - c₂) + (d₁ - d₂)| +
          |e₁ - e₂|) + |f₁ - f₂|) + |g₁ - g₂| := by gcongr; exact abs_add_le _ _
    _ ≤ (((|(a₁ - a₂) + (b₁ - b₂) + (c₁ - c₂)| + |d₁ - d₂|) +
          |e₁ - e₂|) + |f₁ - f₂|) + |g₁ - g₂| := by gcongr; exact abs_add_le _ _
    _ ≤ ((((|(a₁ - a₂) + (b₁ - b₂)| + |c₁ - c₂|) + |d₁ - d₂|) +
          |e₁ - e₂|) + |f₁ - f₂|) + |g₁ - g₂| := by gcongr; exact abs_add_le _ _
    _ ≤ _ := by
      have h := abs_add_le (a₁ - a₂) (b₁ - b₂)
      linarith

/-- Pointwise local data for two eliminated flux derivatives.  The linear
variables have size `C*Mi`; the quadratic elliptic variables have size
`C*Mi^2`; every difference is polarized by `D`. -/
structure EliminatedFluxDerivativePolarizedPointData where
  uStar : ℝ
  qStar : ℝ
  M₁ : ℝ
  M₂ : ℝ
  D : ℝ
  U : ℝ
  C : ℝ
  w₁ : ℝ
  wx₁ : ℝ
  z1x₁ : ℝ
  z1xx₁ : ℝ
  z2x₁ : ℝ
  z2xx₁ : ℝ
  qDiff₁ : ℝ
  qx₁ : ℝ
  zx₁ : ℝ
  zxx₁ : ℝ
  w₂ : ℝ
  wx₂ : ℝ
  z1x₂ : ℝ
  z1xx₂ : ℝ
  z2x₂ : ℝ
  z2xx₂ : ℝ
  qDiff₂ : ℝ
  qx₂ : ℝ
  zx₂ : ℝ
  zxx₂ : ℝ
  M₁_nonneg : 0 ≤ M₁
  M₂_nonneg : 0 ≤ M₂
  M₁_le_one : M₁ ≤ 1
  M₂_le_one : M₂ ≤ 1
  D_nonneg : 0 ≤ D
  U_nonneg : 0 ≤ U
  C_nonneg : 0 ≤ C
  w₁_bound : |w₁| ≤ M₁
  wx₁_bound : |wx₁| ≤ M₁
  u₁_bound : |uStar + w₁| ≤ U
  w₂_bound : |w₂| ≤ M₂
  wx₂_bound : |wx₂| ≤ M₂
  u₂_bound : |uStar + w₂| ≤ U
  linear₁_bounds : |z1x₁| ≤ C * M₁ ∧ |z1xx₁| ≤ C * M₁ ∧
    |qDiff₁| ≤ C * M₁ ∧ |qx₁| ≤ C * M₁ ∧
    |zx₁| ≤ C * M₁ ∧ |zxx₁| ≤ C * M₁
  linear₂_bounds : |z1x₂| ≤ C * M₂ ∧ |z1xx₂| ≤ C * M₂ ∧
    |qDiff₂| ≤ C * M₂ ∧ |qx₂| ≤ C * M₂ ∧
    |zx₂| ≤ C * M₂ ∧ |zxx₂| ≤ C * M₂
  quadratic₁_bounds : |z2x₁| ≤ C * M₁ ^ 2 ∧ |z2xx₁| ≤ C * M₁ ^ 2
  quadratic₂_bounds : |z2x₂| ≤ C * M₂ ^ 2 ∧ |z2xx₂| ≤ C * M₂ ^ 2
  w_diff : |w₁ - w₂| ≤ D
  wx_diff : |wx₁ - wx₂| ≤ D
  linear_diff_bounds : |z1x₁ - z1x₂| ≤ C * D ∧
    |z1xx₁ - z1xx₂| ≤ C * D ∧ |qDiff₁ - qDiff₂| ≤ C * D ∧
    |qx₁ - qx₂| ≤ C * D ∧ |zx₁ - zx₂| ≤ C * D ∧
    |zxx₁ - zxx₂| ≤ C * D
  quadratic_diff_bounds : |z2x₁ - z2x₂| ≤ C * (M₁ + M₂) * D ∧
    |z2xx₁ - z2xx₂| ≤ C * (M₁ + M₂) * D

namespace EliminatedFluxDerivativePolarizedPointData

def eliminatedFluxDerivativePolarizedConstant (qStar C U : ℝ) : ℝ :=
  |qStar| * C * (5 + U) + C ^ 2 * (5 + 4 * U)

def lipschitzConstant (H : EliminatedFluxDerivativePolarizedPointData) : ℝ :=
  eliminatedFluxDerivativePolarizedConstant H.qStar H.C H.U

theorem lipschitzConstant_nonneg (H : EliminatedFluxDerivativePolarizedPointData) :
    0 ≤ H.lipschitzConstant := by
  unfold lipschitzConstant eliminatedFluxDerivativePolarizedConstant
  have h5U : 0 ≤ 5 + H.U := by linarith [H.U_nonneg]
  have h54U : 0 ≤ 5 + 4 * H.U := by linarith [H.U_nonneg]
  exact add_nonneg
    (mul_nonneg (mul_nonneg (abs_nonneg _) H.C_nonneg) h5U)
    (mul_nonneg (sq_nonneg H.C) h54U)

set_option maxHeartbeats 1000000 in
/-- The seven-term derivative is genuinely polarized; the bound vanishes
with the strong difference `D`. -/
theorem difference_le (H : EliminatedFluxDerivativePolarizedPointData) :
    |paper3EliminatedFluxRemainderDerivativeValue
        H.uStar H.qStar H.w₁ H.wx₁ H.z1x₁ H.z1xx₁ H.z2x₁ H.z2xx₁
          H.qDiff₁ H.qx₁ H.zx₁ H.zxx₁ -
      paper3EliminatedFluxRemainderDerivativeValue
        H.uStar H.qStar H.w₂ H.wx₂ H.z1x₂ H.z1xx₂ H.z2x₂ H.z2xx₂
          H.qDiff₂ H.qx₂ H.zx₂ H.zxx₂| ≤
      H.lipschitzConstant * (H.M₁ + H.M₂) * H.D := by
  let S := H.M₁ + H.M₂
  have hS : 0 ≤ S := add_nonneg H.M₁_nonneg H.M₂_nonneg
  have hM₁0 := H.M₁_nonneg
  have hM₂0 := H.M₂_nonneg
  have hM₁1 := H.M₁_le_one
  have hM₂1 := H.M₂_le_one
  have hD0 := H.D_nonneg
  have hU0 := H.U_nonneg
  have hC0 := H.C_nonneg
  have hw₁ := H.w₁_bound
  have hwx₁ := H.wx₁_bound
  have hu₁ := H.u₁_bound
  have hw₂ := H.w₂_bound
  have hwx₂ := H.wx₂_bound
  have hu₂ := H.u₂_bound
  have hwD := H.w_diff
  have hwxD := H.wx_diff
  have hM₁S : H.M₁ ≤ S := by dsimp [S]; linarith [H.M₂_nonneg]
  have hM₂S : H.M₂ ≤ S := by dsimp [S]; linarith [H.M₁_nonneg]
  have hM₁sq : H.M₁ ^ 2 ≤ H.M₁ := by nlinarith [H.M₁_nonneg, H.M₁_le_one]
  have hM₂sq : H.M₂ ^ 2 ≤ H.M₂ := by nlinarith [H.M₂_nonneg, H.M₂_le_one]
  have hM₁sqS : H.M₁ ^ 2 ≤ S := hM₁sq.trans hM₁S
  have hM₂sqS : H.M₂ ^ 2 ≤ S := hM₂sq.trans hM₂S
  rcases H.linear₁_bounds with ⟨hz1x₁, hz1xx₁, hqD₁, hqx₁, hzx₁, hzxx₁⟩
  rcases H.linear₂_bounds with ⟨hz1x₂, hz1xx₂, hqD₂, hqx₂, hzx₂, hzxx₂⟩
  rcases H.quadratic₁_bounds with ⟨hz2x₁, hz2xx₁⟩
  rcases H.quadratic₂_bounds with ⟨hz2x₂, hz2xx₂⟩
  rcases H.linear_diff_bounds with
    ⟨hz1xD, hz1xxD, hqDD, hqxD, hzxD, hzxxD⟩
  rcases H.quadratic_diff_bounds with ⟨hz2xD, hz2xxD⟩
  have hq0 : 0 ≤ |H.qStar| := abs_nonneg _
  have hCD : 0 ≤ H.C * H.D := mul_nonneg H.C_nonneg H.D_nonneg
  have hCS : 0 ≤ H.C * S := mul_nonneg H.C_nonneg hS
  have hCSD : 0 ≤ H.C * S * H.D := mul_nonneg hCS H.D_nonneg
  have t1 : |H.wx₁ * H.qStar * H.z1x₁ -
      H.wx₂ * H.qStar * H.z1x₂| ≤ |H.qStar| * H.C * S * H.D := by
    have h := abs_mul_three_sub_mul_three_le
      H.wx₁ H.qStar H.z1x₁ H.wx₂ H.qStar H.z1x₂
    calc
      _ ≤ |H.wx₁ - H.wx₂| * |H.qStar| * |H.z1x₁| +
          |H.wx₂| * |H.qStar - H.qStar| * |H.z1x₁| +
            |H.wx₂| * |H.qStar| * |H.z1x₁ - H.z1x₂| := h
      _ ≤ H.D * |H.qStar| * (H.C * H.M₁) +
          H.M₂ * 0 * (H.C * H.M₁) +
            H.M₂ * |H.qStar| * (H.C * H.D) := by
        gcongr
        all_goals (first | assumption | simp)
      _ = |H.qStar| * H.C * S * H.D := by dsimp [S]; ring
  have t2 : |H.w₁ * H.qStar * H.z1xx₁ -
      H.w₂ * H.qStar * H.z1xx₂| ≤ |H.qStar| * H.C * S * H.D := by
    have h := abs_mul_three_sub_mul_three_le
      H.w₁ H.qStar H.z1xx₁ H.w₂ H.qStar H.z1xx₂
    calc
      _ ≤ |H.w₁ - H.w₂| * |H.qStar| * |H.z1xx₁| +
          |H.w₂| * |H.qStar - H.qStar| * |H.z1xx₁| +
            |H.w₂| * |H.qStar| * |H.z1xx₁ - H.z1xx₂| := h
      _ ≤ H.D * |H.qStar| * (H.C * H.M₁) +
          H.M₂ * 0 * (H.C * H.M₁) +
            H.M₂ * |H.qStar| * (H.C * H.D) := by
        gcongr
        all_goals (first | assumption | simp)
      _ = |H.qStar| * H.C * S * H.D := by dsimp [S]; ring
  have t3 : |H.wx₁ * H.qStar * H.z2x₁ -
      H.wx₂ * H.qStar * H.z2x₂| ≤ 2 * |H.qStar| * H.C * S * H.D := by
    have h := abs_mul_three_sub_mul_three_le
      H.wx₁ H.qStar H.z2x₁ H.wx₂ H.qStar H.z2x₂
    have ha : H.D * |H.qStar| * (H.C * H.M₁ ^ 2) ≤
        |H.qStar| * H.C * S * H.D := by
      calc
        _ ≤ H.D * |H.qStar| * (H.C * S) := by
          gcongr
        _ = _ := by ring
    have hb : H.M₂ * |H.qStar| * (H.C * S * H.D) ≤
        |H.qStar| * H.C * S * H.D := by
      calc
        _ ≤ 1 * |H.qStar| * (H.C * S * H.D) := by
          gcongr
        _ = _ := by ring
    calc
      _ ≤ |H.wx₁ - H.wx₂| * |H.qStar| * |H.z2x₁| +
          |H.wx₂| * |H.qStar - H.qStar| * |H.z2x₁| +
            |H.wx₂| * |H.qStar| * |H.z2x₁ - H.z2x₂| := h
      _ ≤ H.D * |H.qStar| * (H.C * H.M₁ ^ 2) +
          H.M₂ * 0 * (H.C * H.M₁ ^ 2) +
            H.M₂ * |H.qStar| * (H.C * S * H.D) := by
        dsimp [S] at hz2xD ⊢
        gcongr
        all_goals (first | assumption | simp)
      _ ≤ _ := by linarith
  have t4 : |(H.uStar + H.w₁) * H.qStar * H.z2xx₁ -
      (H.uStar + H.w₂) * H.qStar * H.z2xx₂| ≤
        |H.qStar| * H.C * (1 + H.U) * S * H.D := by
    have h := abs_mul_three_sub_mul_three_le
      (H.uStar + H.w₁) H.qStar H.z2xx₁
      (H.uStar + H.w₂) H.qStar H.z2xx₂
    have ha : |(H.uStar + H.w₁) - (H.uStar + H.w₂)| ≤ H.D := by
      rw [show (H.uStar + H.w₁) - (H.uStar + H.w₂) = H.w₁ - H.w₂ by ring]
      exact hwD
    have hfirst : H.D * |H.qStar| * (H.C * H.M₁ ^ 2) ≤
        |H.qStar| * H.C * S * H.D := by
      calc
        _ ≤ H.D * |H.qStar| * (H.C * S) := by
          gcongr
        _ = _ := by ring
    calc
      _ ≤ |(H.uStar + H.w₁) - (H.uStar + H.w₂)| * |H.qStar| * |H.z2xx₁| +
          |H.uStar + H.w₂| * |H.qStar - H.qStar| * |H.z2xx₁| +
            |H.uStar + H.w₂| * |H.qStar| * |H.z2xx₁ - H.z2xx₂| := h
      _ ≤ H.D * |H.qStar| * (H.C * H.M₁ ^ 2) +
          H.U * 0 * (H.C * H.M₁ ^ 2) +
            H.U * |H.qStar| * (H.C * S * H.D) := by
        dsimp [S] at hz2xxD ⊢
        gcongr
        all_goals (first | assumption | simp)
      _ ≤ |H.qStar| * H.C * S * H.D +
          H.U * (|H.qStar| * H.C * S * H.D) := by
        linarith
      _ = _ := by ring
  have cubic_bound
      {a₁ b₁ c₁ a₂ b₂ c₂ : ℝ}
      (ha₁ : |a₁| ≤ H.M₁) (ha₂ : |a₂| ≤ H.M₂)
      (hb₁ : |b₁| ≤ H.C * H.M₁) (hb₂ : |b₂| ≤ H.C * H.M₂)
      (hc₁ : |c₁| ≤ H.C * H.M₁) (hc₂ : |c₂| ≤ H.C * H.M₂)
      (haD : |a₁ - a₂| ≤ H.D) (hbD : |b₁ - b₂| ≤ H.C * H.D)
      (hcD : |c₁ - c₂| ≤ H.C * H.D) :
      |a₁ * b₁ * c₁ - a₂ * b₂ * c₂| ≤ 3 * H.C ^ 2 * S * H.D := by
    have h := abs_mul_three_sub_mul_three_le a₁ b₁ c₁ a₂ b₂ c₂
    have hterm1 : H.D * (H.C * H.M₁) * (H.C * H.M₁) ≤
        H.C ^ 2 * S * H.D := by
      have hsquare : H.M₁ * H.M₁ ≤ S := by
        simpa [pow_two] using hM₁sq.trans hM₁S
      calc
        _ = H.C ^ 2 * (H.M₁ * H.M₁) * H.D := by ring
        _ ≤ H.C ^ 2 * S * H.D := by
          gcongr
    have hterm2 : H.M₂ * (H.C * H.D) * (H.C * H.M₁) ≤
        H.C ^ 2 * S * H.D := by
      have hp : H.M₂ * H.M₁ ≤ S := by
        calc
          H.M₂ * H.M₁ ≤ 1 * H.M₁ := by
            exact mul_le_mul_of_nonneg_right H.M₂_le_one hM₁0
          _ ≤ S := by simpa using hM₁S
      calc
        _ = H.C ^ 2 * (H.M₂ * H.M₁) * H.D := by ring
        _ ≤ H.C ^ 2 * S * H.D := by
          gcongr
    have hterm3 : H.M₂ * (H.C * H.M₂) * (H.C * H.D) ≤
        H.C ^ 2 * S * H.D := by
      calc
        _ = H.C ^ 2 * H.M₂ ^ 2 * H.D := by ring
        _ ≤ H.C ^ 2 * S * H.D := by
          gcongr
    calc
      _ ≤ |a₁ - a₂| * |b₁| * |c₁| + |a₂| * |b₁ - b₂| * |c₁| +
          |a₂| * |b₂| * |c₁ - c₂| := h
      _ ≤ H.D * (H.C * H.M₁) * (H.C * H.M₁) +
          H.M₂ * (H.C * H.D) * (H.C * H.M₁) +
            H.M₂ * (H.C * H.M₂) * (H.C * H.D) := by
        gcongr
      _ ≤ _ := by linarith
  have t5 : |H.wx₁ * H.qDiff₁ * H.zx₁ - H.wx₂ * H.qDiff₂ * H.zx₂| ≤
      3 * H.C ^ 2 * S * H.D :=
    cubic_bound H.wx₁_bound H.wx₂_bound hqD₁ hqD₂ hzx₁ hzx₂
      H.wx_diff hqDD hzxD
  have u_cubic_bound
      {b₁ c₁ b₂ c₂ : ℝ}
      (hb₁ : |b₁| ≤ H.C * H.M₁) (hb₂ : |b₂| ≤ H.C * H.M₂)
      (hc₁ : |c₁| ≤ H.C * H.M₁) (hc₂ : |c₂| ≤ H.C * H.M₂)
      (hbD : |b₁ - b₂| ≤ H.C * H.D) (hcD : |c₁ - c₂| ≤ H.C * H.D) :
      |(H.uStar + H.w₁) * b₁ * c₁ - (H.uStar + H.w₂) * b₂ * c₂| ≤
        H.C ^ 2 * (1 + 2 * H.U) * S * H.D := by
    have h := abs_mul_three_sub_mul_three_le
      (H.uStar + H.w₁) b₁ c₁ (H.uStar + H.w₂) b₂ c₂
    have huD : |(H.uStar + H.w₁) - (H.uStar + H.w₂)| ≤ H.D := by
      rw [show (H.uStar + H.w₁) - (H.uStar + H.w₂) = H.w₁ - H.w₂ by ring]
      exact hwD
    have hterm1 : H.D * (H.C * H.M₁) * (H.C * H.M₁) ≤
        H.C ^ 2 * S * H.D := by
      calc
        _ = H.C ^ 2 * H.M₁ ^ 2 * H.D := by ring
        _ ≤ H.C ^ 2 * S * H.D := by
          gcongr
    have hterm2 : H.U * (H.C * H.D) * (H.C * H.M₁) ≤
        H.U * (H.C ^ 2 * S * H.D) := by
      calc
        _ ≤ H.U * (H.C * H.D) * (H.C * S) := by
          gcongr
        _ = _ := by ring
    have hterm3 : H.U * (H.C * H.M₂) * (H.C * H.D) ≤
        H.U * (H.C ^ 2 * S * H.D) := by
      calc
        _ ≤ H.U * (H.C * S) * (H.C * H.D) := by
          gcongr
        _ = _ := by ring
    calc
      _ ≤ |(H.uStar + H.w₁) - (H.uStar + H.w₂)| * |b₁| * |c₁| +
          |H.uStar + H.w₂| * |b₁ - b₂| * |c₁| +
            |H.uStar + H.w₂| * |b₂| * |c₁ - c₂| := h
      _ ≤ H.D * (H.C * H.M₁) * (H.C * H.M₁) +
          H.U * (H.C * H.D) * (H.C * H.M₁) +
            H.U * (H.C * H.M₂) * (H.C * H.D) := by
        gcongr
      _ ≤ H.C ^ 2 * S * H.D + 2 * H.U * (H.C ^ 2 * S * H.D) := by
        linarith
      _ = _ := by ring
  have t6 : |(H.uStar + H.w₁) * H.qx₁ * H.zx₁ -
      (H.uStar + H.w₂) * H.qx₂ * H.zx₂| ≤
        H.C ^ 2 * (1 + 2 * H.U) * S * H.D :=
    u_cubic_bound hqx₁ hqx₂ hzx₁ hzx₂ hqxD hzxD
  have t7 : |(H.uStar + H.w₁) * H.qDiff₁ * H.zxx₁ -
      (H.uStar + H.w₂) * H.qDiff₂ * H.zxx₂| ≤
        H.C ^ 2 * (1 + 2 * H.U) * S * H.D :=
    u_cubic_bound hqD₁ hqD₂ hzxx₁ hzxx₂ hqDD hzxxD
  unfold paper3EliminatedFluxRemainderDerivativeValue
  have hsum := abs_seven_difference_le
    (H.wx₁ * H.qStar * H.z1x₁) (H.w₁ * H.qStar * H.z1xx₁)
    (H.wx₁ * H.qStar * H.z2x₁) ((H.uStar + H.w₁) * H.qStar * H.z2xx₁)
    (H.wx₁ * H.qDiff₁ * H.zx₁) ((H.uStar + H.w₁) * H.qx₁ * H.zx₁)
    ((H.uStar + H.w₁) * H.qDiff₁ * H.zxx₁)
    (H.wx₂ * H.qStar * H.z1x₂) (H.w₂ * H.qStar * H.z1xx₂)
    (H.wx₂ * H.qStar * H.z2x₂) ((H.uStar + H.w₂) * H.qStar * H.z2xx₂)
    (H.wx₂ * H.qDiff₂ * H.zx₂) ((H.uStar + H.w₂) * H.qx₂ * H.zx₂)
    ((H.uStar + H.w₂) * H.qDiff₂ * H.zxx₂)
  calc
    _ ≤ |H.wx₁ * H.qStar * H.z1x₁ - H.wx₂ * H.qStar * H.z1x₂| +
        |H.w₁ * H.qStar * H.z1xx₁ - H.w₂ * H.qStar * H.z1xx₂| +
        |H.wx₁ * H.qStar * H.z2x₁ - H.wx₂ * H.qStar * H.z2x₂| +
        |(H.uStar + H.w₁) * H.qStar * H.z2xx₁ -
          (H.uStar + H.w₂) * H.qStar * H.z2xx₂| +
        |H.wx₁ * H.qDiff₁ * H.zx₁ - H.wx₂ * H.qDiff₂ * H.zx₂| +
        |(H.uStar + H.w₁) * H.qx₁ * H.zx₁ -
          (H.uStar + H.w₂) * H.qx₂ * H.zx₂| +
        |(H.uStar + H.w₁) * H.qDiff₁ * H.zxx₁ -
          (H.uStar + H.w₂) * H.qDiff₂ * H.zxx₂| := hsum
    _ ≤ |H.qStar| * H.C * S * H.D + |H.qStar| * H.C * S * H.D +
        2 * |H.qStar| * H.C * S * H.D +
        |H.qStar| * H.C * (1 + H.U) * S * H.D +
        3 * H.C ^ 2 * S * H.D +
        H.C ^ 2 * (1 + 2 * H.U) * S * H.D +
        H.C ^ 2 * (1 + 2 * H.U) * S * H.D := by linarith
    _ = H.lipschitzConstant * (H.M₁ + H.M₂) * H.D := by
      unfold lipschitzConstant eliminatedFluxDerivativePolarizedConstant
      dsimp [S]
      ring

#print axioms EliminatedFluxDerivativePolarizedPointData.difference_le

end EliminatedFluxDerivativePolarizedPointData

end

end ShenWork.Paper3
