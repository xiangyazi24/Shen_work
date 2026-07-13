/- Exact differentiated sensitivity factor and its positive-signal bound. -/
import ShenWork.Paper3.IntervalDomainLocalNemytskiiBounds
import ShenWork.PDE.IntervalChemFluxLipschitz

namespace ShenWork.Paper3

open Real

noncomputable section

def paper3SensitivityDerivativeValue (beta v vx : ℝ) : ℝ :=
  -beta * (1 + v) ^ (-beta - 1) * vx

theorem paper3SensitivityFactor_comp_hasDerivAt
    {beta x v vx : ℝ} {V : ℝ → ℝ}
    (hV : HasDerivAt V vx x) (hbase : 0 < 1 + v) (hv : V x = v) :
    HasDerivAt (fun y => paper3SensitivityFactor beta (V y))
      (paper3SensitivityDerivativeValue beta v vx) x := by
  have hbase' : 0 < 1 + V x := by simpa [hv] using hbase
  have hpow := Real.hasDerivAt_rpow_const
    (x := 1 + V x) (p := -beta) (Or.inl hbase'.ne')
  have hinner : HasDerivAt (fun y => 1 + V y) vx x := by
    convert (hasDerivAt_const x (1 : ℝ)).add hV using 1 <;> simp
  have hcomp := hpow.comp x hinner
  simpa [paper3SensitivityFactor, paper3SensitivityDerivativeValue, hv,
    Function.comp_def] using hcomp

theorem paper3SensitivityDerivativeValue_abs_le
    {beta v vx : ℝ} (hbeta : 0 ≤ beta) (hv : 0 ≤ v) :
    |paper3SensitivityDerivativeValue beta v vx| ≤ beta * |vx| := by
  have hbase : (1 : ℝ) ≤ 1 + v := by linarith
  have hexp : -beta - 1 ≤ 0 := by linarith
  have hpowle : (1 + v) ^ (-beta - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hbase hexp
  have hpow0 : 0 ≤ (1 + v) ^ (-beta - 1) :=
    Real.rpow_nonneg (by linarith) _
  unfold paper3SensitivityDerivativeValue
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hbeta, abs_of_nonneg hpow0]
  have hbetaPow : beta * (1 + v) ^ (-beta - 1) ≤ beta := by
    simpa using mul_le_mul_of_nonneg_left hpowle hbeta
  exact mul_le_mul_of_nonneg_right hbetaPow (abs_nonneg _)

theorem paper3SensitivityFactor_sub_abs_le
    {beta v₁ v₂ : ℝ} (hbeta : 0 ≤ beta)
    (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) :
    |paper3SensitivityFactor beta v₁ - paper3SensitivityFactor beta v₂| ≤
      beta * |v₁ - v₂| := by
  simpa [paper3SensitivityFactor] using
    ShenWork.IntervalChemFluxLipschitz.oneAddRpow_neg_lipschitz
      hbeta hv₁ hv₂

#print axioms paper3SensitivityFactor_comp_hasDerivAt
#print axioms paper3SensitivityDerivativeValue_abs_le
#print axioms paper3SensitivityFactor_sub_abs_le

end

end ShenWork.Paper3
