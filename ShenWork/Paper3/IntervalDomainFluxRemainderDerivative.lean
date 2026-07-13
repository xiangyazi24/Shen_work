/- Exact seven-term derivative estimate for the eliminated flux remainder. -/
import ShenWork.Paper3.IntervalDomainEliminatedNonlinearity

namespace ShenWork.Paper3

open Real

noncomputable section

/-- Derivative of the three-term eliminated flux remainder when `m = 1`.
The arguments represent `w, w_x, z1_x, z1_xx, z2_x, z2_xx,
q-qStar, q_x, z_x, z_xx`. -/
def paper3EliminatedFluxRemainderDerivativeValue
    (uStar qStar w wx z1x z1xx z2x z2xx qDiff qx zx zxx : ℝ) : ℝ :=
  wx * qStar * z1x + w * qStar * z1xx +
    wx * qStar * z2x + (uStar + w) * qStar * z2xx +
      wx * qDiff * zx + (uStar + w) * qx * zx +
        (uStar + w) * qDiff * zxx

/-- Three-term physical flux remainder written as functions of space. -/
def paper3EliminatedFluxRemainderThreeTermProfile
    (uStar qStar : ℝ)
    (w z1x z2x q zx : ℝ → ℝ) (x : ℝ) : ℝ :=
  w x * qStar * z1x x +
    (uStar + w x) * qStar * z2x x +
      (uStar + w x) * (q x - qStar) * zx x

/-- Exact product-rule derivative of the three-term eliminated remainder. -/
theorem paper3EliminatedFluxRemainderThreeTermProfile_hasDerivAt
    {uStar qStar x w0 wx0 z1x0 z1xx0 z2x0 z2xx0 q0 qx0 zx0 zxx0 : ℝ}
    {w z1x z2x q zx : ℝ → ℝ}
    (hw : HasDerivAt w wx0 x)
    (hz1 : HasDerivAt z1x z1xx0 x)
    (hz2 : HasDerivAt z2x z2xx0 x)
    (hq : HasDerivAt q qx0 x)
    (hz : HasDerivAt zx zxx0 x)
    (hw0 : w x = w0) (hz1x0 : z1x x = z1x0)
    (hz2x0 : z2x x = z2x0) (hq0 : q x = q0) (hzx0 : zx x = zx0) :
    HasDerivAt
      (paper3EliminatedFluxRemainderThreeTermProfile
        uStar qStar w z1x z2x q zx)
      (paper3EliminatedFluxRemainderDerivativeValue
        uStar qStar w0 wx0 z1x0 z1xx0 z2x0 z2xx0
          (q0 - qStar) qx0 zx0 zxx0) x := by
  unfold paper3EliminatedFluxRemainderThreeTermProfile
    paper3EliminatedFluxRemainderDerivativeValue
  convert
    ((hw.mul_const qStar).mul hz1).add
      ((((hasDerivAt_const x uStar).add hw).mul_const qStar).mul hz2) |>.add
        ((((hasDerivAt_const x uStar).add hw).mul
          (hq.sub_const qStar)).mul hz) using 1 <;>
    simp only [Pi.add_apply, Pi.mul_apply] <;>
    rw [hw0, hz1x0, hz2x0, hq0, hzx0] <;> ring

/-- Pointwise `deriv` form of the exact product-rule identity. -/
theorem paper3EliminatedFluxRemainderThreeTermProfile_deriv_eq
    {uStar qStar x w0 wx0 z1x0 z1xx0 z2x0 z2xx0 q0 qx0 zx0 zxx0 : ℝ}
    {w z1x z2x q zx : ℝ → ℝ}
    (hw : HasDerivAt w wx0 x)
    (hz1 : HasDerivAt z1x z1xx0 x)
    (hz2 : HasDerivAt z2x z2xx0 x)
    (hq : HasDerivAt q qx0 x)
    (hz : HasDerivAt zx zxx0 x)
    (hw0 : w x = w0) (hz1x0 : z1x x = z1x0)
    (hz2x0 : z2x x = z2x0) (hq0 : q x = q0) (hzx0 : zx x = zx0) :
    deriv
      (paper3EliminatedFluxRemainderThreeTermProfile
        uStar qStar w z1x z2x q zx) x =
      paper3EliminatedFluxRemainderDerivativeValue
        uStar qStar w0 wx0 z1x0 z1xx0 z2x0 z2xx0
          (q0 - qStar) qx0 zx0 zxx0 :=
  (paper3EliminatedFluxRemainderThreeTermProfile_hasDerivAt
    hw hz1 hz2 hq hz hw0 hz1x0 hz2x0 hq0 hzx0).deriv

/-- Constants in the strong-times-weak derivative estimate. -/
structure EliminatedFluxDerivativeQuadraticBounds where
  M : ℝ
  L : ℝ
  U : ℝ
  Cz1x : ℝ
  Cz1xx : ℝ
  Cz2x : ℝ
  Cz2xx : ℝ
  Cq : ℝ
  Cqx : ℝ
  Czx : ℝ
  Czxx : ℝ
  M_nonneg : 0 ≤ M
  M_le_one : M ≤ 1
  L_nonneg : 0 ≤ L
  L_le_M : L ≤ M
  U_nonneg : 0 ≤ U
  Cz1x_nonneg : 0 ≤ Cz1x
  Cz1xx_nonneg : 0 ≤ Cz1xx
  Cz2x_nonneg : 0 ≤ Cz2x
  Cz2xx_nonneg : 0 ≤ Cz2xx
  Cq_nonneg : 0 ≤ Cq
  Cqx_nonneg : 0 ≤ Cqx
  Czx_nonneg : 0 ≤ Czx
  Czxx_nonneg : 0 ≤ Czxx

/-- Explicit coefficient in the seven-term derivative estimate. -/
def eliminatedFluxDerivativeQuadraticConstant
    (H : EliminatedFluxDerivativeQuadraticBounds) (qStar : ℝ) : ℝ :=
  |qStar| * H.Cz1x + |qStar| * H.Cz1xx +
    |qStar| * H.Cz2x + H.U * |qStar| * H.Cz2xx +
      H.Cq * H.Czx + H.U * H.Cqx * H.Czx +
        H.U * H.Cq * H.Czxx

theorem eliminatedFluxDerivativeQuadraticConstant_nonneg
    (H : EliminatedFluxDerivativeQuadraticBounds) (qStar : ℝ) :
    0 ≤ eliminatedFluxDerivativeQuadraticConstant H qStar := by
  unfold eliminatedFluxDerivativeQuadraticConstant
  have hU := H.U_nonneg
  have h1 := H.Cz1x_nonneg
  have h2 := H.Cz1xx_nonneg
  have h3 := H.Cz2x_nonneg
  have h4 := H.Cz2xx_nonneg
  have h5 := H.Cq_nonneg
  have h6 := H.Cqx_nonneg
  have h7 := H.Czx_nonneg
  have h8 := H.Czxx_nonneg
  positivity

/-- The derivative of the nonlinear eliminated flux is `O(M L)` on a unit
local ball.  Terms that are formally cubic are absorbed with `L ≤ M ≤ 1`. -/
theorem paper3EliminatedFluxRemainderDerivativeValue_quadratic
    (H : EliminatedFluxDerivativeQuadraticBounds)
    {uStar qStar w wx z1x z1xx z2x z2xx qDiff qx zx zxx : ℝ}
    (hw : |w| ≤ H.M) (hwx : |wx| ≤ H.M)
    (hu : |uStar + w| ≤ H.U)
    (hz1x : |z1x| ≤ H.Cz1x * H.L)
    (hz1xx : |z1xx| ≤ H.Cz1xx * H.L)
    (hz2x : |z2x| ≤ H.Cz2x * H.M * H.L)
    (hz2xx : |z2xx| ≤ H.Cz2xx * H.M * H.L)
    (hqDiff : |qDiff| ≤ H.Cq * H.L)
    (hqx : |qx| ≤ H.Cqx * H.L)
    (hzx : |zx| ≤ H.Czx * H.L)
    (hzxx : |zxx| ≤ H.Czxx * H.L) :
    |paper3EliminatedFluxRemainderDerivativeValue
        uStar qStar w wx z1x z1xx z2x z2xx qDiff qx zx zxx| ≤
      eliminatedFluxDerivativeQuadraticConstant H qStar * H.M * H.L := by
  have hM0 := H.M_nonneg
  have hL0 := H.L_nonneg
  have hU0 := H.U_nonneg
  have hCz1x0 := H.Cz1x_nonneg
  have hCz1xx0 := H.Cz1xx_nonneg
  have hCz2x0 := H.Cz2x_nonneg
  have hCz2xx0 := H.Cz2xx_nonneg
  have hCq0 := H.Cq_nonneg
  have hCqx0 := H.Cqx_nonneg
  have hCzx0 := H.Czx_nonneg
  have hCzxx0 := H.Czxx_nonneg
  have hL1 : H.L ≤ 1 := H.L_le_M.trans H.M_le_one
  have hMM : H.M * H.M ≤ H.M := by
    calc
      H.M * H.M ≤ H.M * 1 :=
        mul_le_mul_of_nonneg_left H.M_le_one H.M_nonneg
      _ = H.M := mul_one _
  have hLL : H.L * H.L ≤ H.M * H.L :=
    mul_le_mul_of_nonneg_right H.L_le_M H.L_nonneg
  have hMML : H.M * H.M * H.L ≤ H.M * H.L := by
    exact mul_le_mul_of_nonneg_right hMM H.L_nonneg
  have hMLL : H.M * H.L * H.L ≤ H.M * H.L := by
    have hML0 : 0 ≤ H.M * H.L := mul_nonneg H.M_nonneg H.L_nonneg
    nlinarith
  have h1 : |wx * qStar * z1x| ≤
      (|qStar| * H.Cz1x) * H.M * H.L := by
    rw [abs_mul, abs_mul]
    calc
      |wx| * |qStar| * |z1x| ≤
          H.M * |qStar| * (H.Cz1x * H.L) := by gcongr
      _ = (|qStar| * H.Cz1x) * H.M * H.L := by ring
  have h2 : |w * qStar * z1xx| ≤
      (|qStar| * H.Cz1xx) * H.M * H.L := by
    rw [abs_mul, abs_mul]
    calc
      |w| * |qStar| * |z1xx| ≤
          H.M * |qStar| * (H.Cz1xx * H.L) := by gcongr
      _ = (|qStar| * H.Cz1xx) * H.M * H.L := by ring
  have h3 : |wx * qStar * z2x| ≤
      (|qStar| * H.Cz2x) * H.M * H.L := by
    rw [abs_mul, abs_mul]
    calc
      |wx| * |qStar| * |z2x| ≤
          H.M * |qStar| * (H.Cz2x * H.M * H.L) := by gcongr
      _ = (|qStar| * H.Cz2x) * (H.M * H.M * H.L) := by ring
      _ ≤ (|qStar| * H.Cz2x) * (H.M * H.L) :=
        mul_le_mul_of_nonneg_left hMML
          (mul_nonneg (abs_nonneg _) H.Cz2x_nonneg)
      _ = (|qStar| * H.Cz2x) * H.M * H.L := by ring
  have h4 : |(uStar + w) * qStar * z2xx| ≤
      (H.U * |qStar| * H.Cz2xx) * H.M * H.L := by
    rw [abs_mul, abs_mul]
    calc
      |uStar + w| * |qStar| * |z2xx| ≤
          H.U * |qStar| * (H.Cz2xx * H.M * H.L) := by gcongr
      _ = (H.U * |qStar| * H.Cz2xx) * H.M * H.L := by ring
  have h5 : |wx * qDiff * zx| ≤
      (H.Cq * H.Czx) * H.M * H.L := by
    rw [abs_mul, abs_mul]
    calc
      |wx| * |qDiff| * |zx| ≤
          H.M * (H.Cq * H.L) * (H.Czx * H.L) := by gcongr
      _ = (H.Cq * H.Czx) * (H.M * H.L * H.L) := by ring
      _ ≤ (H.Cq * H.Czx) * (H.M * H.L) :=
        mul_le_mul_of_nonneg_left hMLL
          (mul_nonneg H.Cq_nonneg H.Czx_nonneg)
      _ = (H.Cq * H.Czx) * H.M * H.L := by ring
  have h6 : |(uStar + w) * qx * zx| ≤
      (H.U * H.Cqx * H.Czx) * H.M * H.L := by
    rw [abs_mul, abs_mul]
    calc
      |uStar + w| * |qx| * |zx| ≤
          H.U * (H.Cqx * H.L) * (H.Czx * H.L) := by gcongr
      _ = (H.U * H.Cqx * H.Czx) * (H.L * H.L) := by ring
      _ ≤ (H.U * H.Cqx * H.Czx) * (H.M * H.L) :=
        mul_le_mul_of_nonneg_left hLL
          (mul_nonneg (mul_nonneg H.U_nonneg H.Cqx_nonneg) H.Czx_nonneg)
      _ = (H.U * H.Cqx * H.Czx) * H.M * H.L := by ring
  have h7 : |(uStar + w) * qDiff * zxx| ≤
      (H.U * H.Cq * H.Czxx) * H.M * H.L := by
    rw [abs_mul, abs_mul]
    calc
      |uStar + w| * |qDiff| * |zxx| ≤
          H.U * (H.Cq * H.L) * (H.Czxx * H.L) := by gcongr
      _ = (H.U * H.Cq * H.Czxx) * (H.L * H.L) := by ring
      _ ≤ (H.U * H.Cq * H.Czxx) * (H.M * H.L) :=
        mul_le_mul_of_nonneg_left hLL
          (mul_nonneg (mul_nonneg H.U_nonneg H.Cq_nonneg) H.Czxx_nonneg)
      _ = (H.U * H.Cq * H.Czxx) * H.M * H.L := by ring
  unfold paper3EliminatedFluxRemainderDerivativeValue
  have hsum :
      |wx * qStar * z1x + w * qStar * z1xx +
          wx * qStar * z2x + (uStar + w) * qStar * z2xx +
            wx * qDiff * zx + (uStar + w) * qx * zx +
              (uStar + w) * qDiff * zxx| ≤
        |wx * qStar * z1x| + |w * qStar * z1xx| +
          |wx * qStar * z2x| + |(uStar + w) * qStar * z2xx| +
            |wx * qDiff * zx| + |(uStar + w) * qx * zx| +
              |(uStar + w) * qDiff * zxx| := by
    calc
      |wx * qStar * z1x + w * qStar * z1xx +
          wx * qStar * z2x + (uStar + w) * qStar * z2xx +
            wx * qDiff * zx + (uStar + w) * qx * zx +
              (uStar + w) * qDiff * zxx| ≤
        |wx * qStar * z1x + w * qStar * z1xx +
          wx * qStar * z2x + (uStar + w) * qStar * z2xx +
            wx * qDiff * zx + (uStar + w) * qx * zx| +
              |(uStar + w) * qDiff * zxx| := abs_add_le _ _
      _ ≤ (|wx * qStar * z1x + w * qStar * z1xx +
          wx * qStar * z2x + (uStar + w) * qStar * z2xx +
            wx * qDiff * zx| + |(uStar + w) * qx * zx|) +
              |(uStar + w) * qDiff * zxx| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ ((|wx * qStar * z1x + w * qStar * z1xx +
          wx * qStar * z2x + (uStar + w) * qStar * z2xx| +
            |wx * qDiff * zx|) + |(uStar + w) * qx * zx|) +
              |(uStar + w) * qDiff * zxx| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ (((|wx * qStar * z1x + w * qStar * z1xx +
          wx * qStar * z2x| + |(uStar + w) * qStar * z2xx|) +
            |wx * qDiff * zx|) + |(uStar + w) * qx * zx|) +
              |(uStar + w) * qDiff * zxx| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ ((((|wx * qStar * z1x + w * qStar * z1xx| +
          |wx * qStar * z2x|) + |(uStar + w) * qStar * z2xx|) +
            |wx * qDiff * zx|) + |(uStar + w) * qx * zx|) +
              |(uStar + w) * qDiff * zxx| :=
        by
          gcongr
          exact abs_add_le _ _
      _ ≤ |wx * qStar * z1x| + |w * qStar * z1xx| +
          |wx * qStar * z2x| + |(uStar + w) * qStar * z2xx| +
            |wx * qDiff * zx| + |(uStar + w) * qx * zx| +
              |(uStar + w) * qDiff * zxx| := by
        have h := abs_add_le (wx * qStar * z1x) (w * qStar * z1xx)
        linarith
  calc
    |wx * qStar * z1x + w * qStar * z1xx +
          wx * qStar * z2x + (uStar + w) * qStar * z2xx +
            wx * qDiff * zx + (uStar + w) * qx * zx +
              (uStar + w) * qDiff * zxx| ≤
        |wx * qStar * z1x| + |w * qStar * z1xx| +
          |wx * qStar * z2x| + |(uStar + w) * qStar * z2xx| +
            |wx * qDiff * zx| + |(uStar + w) * qx * zx| +
              |(uStar + w) * qDiff * zxx| := hsum
    _ ≤ (|qStar| * H.Cz1x) * H.M * H.L +
          (|qStar| * H.Cz1xx) * H.M * H.L +
          (|qStar| * H.Cz2x) * H.M * H.L +
          (H.U * |qStar| * H.Cz2xx) * H.M * H.L +
          (H.Cq * H.Czx) * H.M * H.L +
          (H.U * H.Cqx * H.Czx) * H.M * H.L +
          (H.U * H.Cq * H.Czxx) * H.M * H.L := by gcongr
    _ = eliminatedFluxDerivativeQuadraticConstant H qStar * H.M * H.L := by
      unfold eliminatedFluxDerivativeQuadraticConstant
      ring

#print axioms paper3EliminatedFluxRemainderDerivativeValue_quadratic
#print axioms paper3EliminatedFluxRemainderThreeTermProfile_deriv_eq

end

end ShenWork.Paper3
