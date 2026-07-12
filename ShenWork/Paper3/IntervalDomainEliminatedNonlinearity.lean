/-
  Exact eliminated chemotaxis flux remainder and its quadratic product bound.

  This file is independent of the spectral realization of the elliptic
  resolver.  The resolver coefficient estimates supply the named pointwise
  bounds below; the algebraic decomposition then exposes one strong/sup factor
  and one weak/L2 factor in every nonlinear term.
-/
import ShenWork.Paper3.IntervalDomainEllipticRemainderCoeffs

namespace ShenWork.Paper3

open Real

noncomputable section

/-- Full eliminated flux at one spatial point.  The `uPow` argument is `u^m`,
`q=(1+v)^(-beta)`, and `zGrad` is the gradient of `v-vStar`. -/
def paper3EliminatedFluxValue
    (uPow q zGrad : ℝ) : ℝ :=
  uPow * q * zGrad

/-- Linearized eliminated flux at the same point. -/
def paper3EliminatedLinearFluxValue
    (uStarPow qStar z1Grad : ℝ) : ℝ :=
  uStarPow * qStar * z1Grad

/-- Nonlinear chemotaxis flux remainder before the outer divergence. -/
def paper3EliminatedFluxRemainder
    (uPow uStarPow q qStar zGrad z1Grad : ℝ) : ℝ :=
  paper3EliminatedFluxValue uPow q zGrad -
    paper3EliminatedLinearFluxValue uStarPow qStar z1Grad

/-- Exact three-term expansion of the eliminated flux remainder. -/
theorem paper3EliminatedFluxRemainder_eq
    (uPow uStarPow q qStar zGrad z1Grad z2Grad : ℝ)
    (hz : zGrad = z1Grad + z2Grad) :
    paper3EliminatedFluxRemainder
        uPow uStarPow q qStar zGrad z1Grad =
      (uPow - uStarPow) * qStar * z1Grad +
        uPow * qStar * z2Grad +
          uPow * (q - qStar) * zGrad := by
  simp only [paper3EliminatedFluxRemainder,
    paper3EliminatedFluxValue, paper3EliminatedLinearFluxValue]
  rw [hz]
  ring

/-- Quantitative pointwise inputs furnished by the local Nemytskii and elliptic
resolver estimates.  `M` is a strong/sup perturbation size and `L` a weak/L2
size. -/
structure EliminatedFluxQuadraticBounds where
  M : ℝ
  L : ℝ
  Cu : ℝ
  U : ℝ
  Cq : ℝ
  Cz : ℝ
  CzGrad : ℝ
  Cz1Grad : ℝ
  Cz2Grad : ℝ
  M_nonneg : 0 ≤ M
  L_nonneg : 0 ≤ L
  L_le_M : L ≤ M
  Cu_nonneg : 0 ≤ Cu
  U_nonneg : 0 ≤ U
  Cq_nonneg : 0 ≤ Cq
  Cz_nonneg : 0 ≤ Cz
  CzGrad_nonneg : 0 ≤ CzGrad
  Cz1Grad_nonneg : 0 ≤ Cz1Grad
  Cz2Grad_nonneg : 0 ≤ Cz2Grad

/-- Explicit constant in the quadratic flux estimate. -/
def eliminatedFluxQuadraticConstant
    (H : EliminatedFluxQuadraticBounds) (qStar : ℝ) : ℝ :=
  H.Cu * |qStar| * H.Cz1Grad +
    H.U * |qStar| * H.Cz2Grad +
      H.U * H.Cq * H.Cz * H.CzGrad

theorem eliminatedFluxQuadraticConstant_nonneg
    (H : EliminatedFluxQuadraticBounds) (qStar : ℝ) :
    0 ≤ eliminatedFluxQuadraticConstant H qStar := by
  unfold eliminatedFluxQuadraticConstant
  exact add_nonneg
    (add_nonneg
      (mul_nonneg
        (mul_nonneg H.Cu_nonneg (abs_nonneg qStar)) H.Cz1Grad_nonneg)
      (mul_nonneg
        (mul_nonneg H.U_nonneg (abs_nonneg qStar)) H.Cz2Grad_nonneg))
    (mul_nonneg
      (mul_nonneg (mul_nonneg H.U_nonneg H.Cq_nonneg) H.Cz_nonneg)
      H.CzGrad_nonneg)

/-- L3 product estimate for the eliminated chemotaxis flux.  The assumptions
match the three exact terms:

* `u^m-uStar^m = O(M)`, `grad Z1 = O(L)`;
* `grad Z2 = O(M*L)`;
* `q-qStar = O(Z)`, while `Z` and `grad Z` are `O(L)` and `L<=M`.
-/
theorem paper3EliminatedFluxRemainder_quadratic
    (H : EliminatedFluxQuadraticBounds)
    {uPow uStarPow q qStar zGrad z1Grad z2Grad : ℝ}
    (hz : zGrad = z1Grad + z2Grad)
    (huDiff : |uPow - uStarPow| ≤ H.Cu * H.M)
    (hu : |uPow| ≤ H.U)
    (hqDiff : |q - qStar| ≤ H.Cq * (H.Cz * H.L))
    (hzGrad : |zGrad| ≤ H.CzGrad * H.L)
    (hz1Grad : |z1Grad| ≤ H.Cz1Grad * H.L)
    (hz2Grad : |z2Grad| ≤ H.Cz2Grad * H.M * H.L) :
    |paper3EliminatedFluxRemainder
        uPow uStarPow q qStar zGrad z1Grad| ≤
      eliminatedFluxQuadraticConstant H qStar * H.M * H.L := by
  have hCuM : 0 ≤ H.Cu * H.M := mul_nonneg H.Cu_nonneg H.M_nonneg
  have hUL : 0 ≤ H.U := H.U_nonneg
  have hCqCzL : 0 ≤ H.Cq * (H.Cz * H.L) :=
    mul_nonneg H.Cq_nonneg (mul_nonneg H.Cz_nonneg H.L_nonneg)
  have hCz1L : 0 ≤ H.Cz1Grad * H.L :=
    mul_nonneg H.Cz1Grad_nonneg H.L_nonneg
  have hCz2ML : 0 ≤ H.Cz2Grad * H.M * H.L :=
    mul_nonneg (mul_nonneg H.Cz2Grad_nonneg H.M_nonneg) H.L_nonneg
  have hCzGradL : 0 ≤ H.CzGrad * H.L :=
    mul_nonneg H.CzGrad_nonneg H.L_nonneg
  rw [paper3EliminatedFluxRemainder_eq _ _ _ _ _ _ _ hz]
  have hterm1 :
      |(uPow - uStarPow) * qStar * z1Grad| ≤
        (H.Cu * |qStar| * H.Cz1Grad) * H.M * H.L := by
    rw [abs_mul, abs_mul]
    calc
      |uPow - uStarPow| * |qStar| * |z1Grad| ≤
          (H.Cu * H.M) * |qStar| * (H.Cz1Grad * H.L) := by
        gcongr
      _ = (H.Cu * |qStar| * H.Cz1Grad) * H.M * H.L := by ring
  have hterm2 :
      |uPow * qStar * z2Grad| ≤
        (H.U * |qStar| * H.Cz2Grad) * H.M * H.L := by
    rw [abs_mul, abs_mul]
    calc
      |uPow| * |qStar| * |z2Grad| ≤
          H.U * |qStar| * (H.Cz2Grad * H.M * H.L) := by
        gcongr
      _ = (H.U * |qStar| * H.Cz2Grad) * H.M * H.L := by ring
  have hLsq : H.L * H.L ≤ H.M * H.L :=
    mul_le_mul_of_nonneg_right H.L_le_M H.L_nonneg
  have hterm3 :
      |uPow * (q - qStar) * zGrad| ≤
        (H.U * H.Cq * H.Cz * H.CzGrad) * H.M * H.L := by
    rw [abs_mul, abs_mul]
    calc
      |uPow| * |q - qStar| * |zGrad| ≤
          H.U * (H.Cq * (H.Cz * H.L)) *
            (H.CzGrad * H.L) := by
        gcongr
      _ = (H.U * H.Cq * H.Cz * H.CzGrad) * (H.L * H.L) := by ring
      _ ≤ (H.U * H.Cq * H.Cz * H.CzGrad) * (H.M * H.L) := by
        exact mul_le_mul_of_nonneg_left hLsq
          (mul_nonneg
            (mul_nonneg (mul_nonneg H.U_nonneg H.Cq_nonneg) H.Cz_nonneg)
            H.CzGrad_nonneg)
      _ = (H.U * H.Cq * H.Cz * H.CzGrad) * H.M * H.L := by ring
  calc
    |(uPow - uStarPow) * qStar * z1Grad +
        uPow * qStar * z2Grad + uPow * (q - qStar) * zGrad| ≤
      |(uPow - uStarPow) * qStar * z1Grad| +
        |uPow * qStar * z2Grad| +
          |uPow * (q - qStar) * zGrad| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ (H.Cu * |qStar| * H.Cz1Grad) * H.M * H.L +
        (H.U * |qStar| * H.Cz2Grad) * H.M * H.L +
          (H.U * H.Cq * H.Cz * H.CzGrad) * H.M * H.L :=
      add_le_add (add_le_add hterm1 hterm2) hterm3
    _ = eliminatedFluxQuadraticConstant H qStar * H.M * H.L := by
      unfold eliminatedFluxQuadraticConstant
      ring

#print axioms paper3EliminatedFluxRemainder_eq
#print axioms paper3EliminatedFluxRemainder_quadratic

end

end ShenWork.Paper3
