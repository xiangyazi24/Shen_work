import ShenWork.Defs

/-!
# Crude scalar dissipation closure on a plateau

The estimate here is deliberately limited in scope.  Its threshold
`4 * √α * a ^ (α / 2) / b ^ α` tends to `4 * √α` as the plateau
`[a,b]` shrinks to `{1}`.  Although `4 * √α ≤ (1 + √α) ^ 2`, equality holds
only at `α = 1`; consequently this crude Cauchy--Schwarz closure is not sharp
for `α > 1`.  The sharp constant `(1 + √α) ^ 2` requires the
sum-of-squares/resolver-moment argument recorded in the dispersion brick.

Everything below is scalar and static.  In particular, the time-derivative
identity and invariance of a plateau along a PDE trajectory are hypotheses to
be established by PDE-coupled arguments, not consequences of this file.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- A Cauchy--Schwarz cross-term bound and the plateau reaction coefficient
close the abstract dissipation inequality.  This theorem assumes the identity
`Edot = -D + T + R`; it does not establish a time derivative or plateau
invariance for any PDE solution.  Its limiting threshold is `4 * √α`, which is
strictly below the sharp `(1 + √α) ^ 2` for `α > 1` (equality occurs only at
`α = 1`).  Reaching the sharp threshold needs the separate
sum-of-squares/resolver-moment dispersion argument. -/
theorem plateau_dissipation_closure
    (D M χ γ α a b T R Edot : ℝ)
    (hD : 0 ≤ D) (hM : 0 < M) (ha : 0 < a) (hb : 0 < b)
    (hα : 1 ≤ α)
    (hT : |T| ≤
      (χ * γ / 2) * b ^ α * Real.sqrt D * Real.sqrt M)
    (hR : R ≤ -α * a ^ α * M)
    (hEdot : Edot = -D + T + R)
    (hχ : χ * γ ≤
      4 * Real.sqrt α * a ^ (α / 2) / b ^ α) :
    Edot ≤ 0 := by
  have hαnonneg : 0 ≤ α := le_trans zero_le_one hα
  have hbpow_pos : 0 < b ^ α := Real.rpow_pos_of_pos hb _
  have hχmul :
      (χ * γ) * b ^ α ≤ 4 * Real.sqrt α * a ^ (α / 2) :=
    (le_div_iff₀ hbpow_pos).mp hχ
  have hcoefficient :
      (χ * γ / 2) * b ^ α ≤
        2 * Real.sqrt α * a ^ (α / 2) := by
    nlinarith
  have hsqrt_product : 0 ≤ Real.sqrt D * Real.sqrt M :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hTupper :
      T ≤ 2 * Real.sqrt α * a ^ (α / 2) *
        Real.sqrt D * Real.sqrt M := by
    calc
      T ≤ |T| := le_abs_self T
      _ ≤ (χ * γ / 2) * b ^ α * Real.sqrt D * Real.sqrt M := hT
      _ ≤ 2 * Real.sqrt α * a ^ (α / 2) *
          Real.sqrt D * Real.sqrt M := by
        simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_right hcoefficient hsqrt_product)
  have hapow_sq : (a ^ (α / 2)) ^ 2 = a ^ α := by
    rw [← Real.rpow_natCast (a ^ (α / 2)) 2,
      ← Real.rpow_mul ha.le]
    congr 1
    ring
  have hweighted_sq :
      (Real.sqrt α * a ^ (α / 2) * Real.sqrt M) ^ 2 =
        α * a ^ α * M := by
    calc
      (Real.sqrt α * a ^ (α / 2) * Real.sqrt M) ^ 2 =
          (Real.sqrt α) ^ 2 * (a ^ (α / 2)) ^ 2 *
            (Real.sqrt M) ^ 2 := by ring
      _ = α * a ^ α * M := by
        rw [Real.sq_sqrt hαnonneg, hapow_sq, Real.sq_sqrt hM.le]
  have hyoung :
      2 * Real.sqrt α * a ^ (α / 2) * Real.sqrt D * Real.sqrt M ≤
        D + α * a ^ α * M := by
    have hbasic :
        2 * Real.sqrt D *
            (Real.sqrt α * a ^ (α / 2) * Real.sqrt M) ≤
          (Real.sqrt D) ^ 2 +
            (Real.sqrt α * a ^ (α / 2) * Real.sqrt M) ^ 2 := by
      nlinarith [sq_nonneg
        (Real.sqrt D - Real.sqrt α * a ^ (α / 2) * Real.sqrt M)]
    rw [Real.sq_sqrt hD, hweighted_sq] at hbasic
    nlinarith
  rw [hEdot]
  nlinarith

section AxiomAudit

#print axioms plateau_dissipation_closure

end AxiomAudit

end ShenWork.Paper1
