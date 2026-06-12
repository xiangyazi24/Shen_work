import ShenWork.PDE.IntervalChemDivLocalChainRule

open ShenWork.IntervalDomain
open Set Filter Topology

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

/-- Lifted chemotactic flux before the outer spatial derivative. -/
def coupledChemDivFluxLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s y : ℝ) : ℝ :=
  let v : ℝ → ℝ := intervalDomainLift (coupledChemicalConcentration p u s)
  intervalDomainLift (u s) y * deriv v y / (1 + v y) ^ p.β

/-- Time derivative of the lifted chemotactic flux before the outer derivative. -/
def coupledChemDivFluxTimeDerivativeLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s y : ℝ) : ℝ :=
  let v : ℝ → ℝ := intervalDomainLift (coupledChemicalConcentration p u s)
  let vt : ℝ → ℝ := coupledChemicalTimeDerivativeLift p u s
  ShenWork.Paper2.PicardLimitK1.slopeSlice u s y * deriv v y /
      (1 + v y) ^ p.β +
    intervalDomainLift (u s) y * deriv vt y / (1 + v y) ^ p.β -
    p.β * intervalDomainLift (u s) y * deriv v y * vt y /
      (1 + v y) ^ (p.β + 1)

private theorem chemDiv_flux_deriv_algebra
    {β U G Ut Gt Vt B : ℝ} (hB : 0 < B) :
    (((Ut * G + U * Gt) * B ^ β - U * G * (Vt * β * B ^ (β - 1))) /
        (B ^ β) ^ 2) =
      Ut * G / B ^ β + U * Gt / B ^ β - β * U * G * Vt / B ^ (β + 1) := by
  have hBβne : B ^ β ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hB β)
  have hBβ1ne : B ^ (β + 1) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hB (β + 1))
  have hpow1 : (B ^ β) ^ 2 = B ^ (2 * β) := by
    rw [← Real.rpow_natCast (B ^ β) 2, ← Real.rpow_mul hB.le]
    norm_num
    ring_nf
  have hcombine : B ^ (β - 1) / B ^ (2 * β) = 1 / B ^ (β + 1) := by
    rw [← Real.rpow_sub hB]
    have : β - 1 - 2 * β = -(β + 1) := by ring
    rw [this, Real.rpow_neg hB.le (β + 1), one_div]
  rw [hpow1]
  have hsplit :
      ((Ut * G + U * Gt) * B ^ β - U * G * (Vt * β * B ^ (β - 1))) /
          B ^ (2 * β) =
        (Ut * G + U * Gt) / B ^ β -
          U * G * (Vt * β) * (B ^ (β - 1) / B ^ (2 * β)) := by
    field_simp [hBβne]
    ring_nf
    rw [hpow1, show β * 2 = 2 * β by ring]
    ring
  rw [hsplit, hcombine]
  field_simp [hBβne, hBβ1ne]

/-- Pointwise product/quotient/rpow time chain rule for the inner flux. -/
theorem coupledChemDivFlux_hasDerivAt_time
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s y : ℝ}
    (hu : HasDerivAt (fun r => intervalDomainLift (u r) y)
      (ShenWork.Paper2.PicardLimitK1.slopeSlice u s y) s)
    (hgv : HasDerivAt
      (fun r => deriv (intervalDomainLift (coupledChemicalConcentration p u r)) y)
      (deriv (coupledChemicalTimeDerivativeLift p u s) y) s)
    (hv : HasDerivAt
      (fun r => intervalDomainLift (coupledChemicalConcentration p u r) y)
      (coupledChemicalTimeDerivativeLift p u s y) s)
    (hbase : 0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) y) :
    HasDerivAt (fun r => coupledChemDivFluxLift p u r y)
      (coupledChemDivFluxTimeDerivativeLift p u s y) s := by
  let v : ℝ → ℝ := intervalDomainLift (coupledChemicalConcentration p u s)
  let U := intervalDomainLift (u s) y
  let G := deriv v y
  let Ut := ShenWork.Paper2.PicardLimitK1.slopeSlice u s y
  let Gt := deriv (coupledChemicalTimeDerivativeLift p u s) y
  let Vt := coupledChemicalTimeDerivativeLift p u s y
  let B := 1 + v y
  have hden : B ^ p.β ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hbase p.β)
  have hnum := hu.mul hgv
  have hone : HasDerivAt
      (fun r => 1 + intervalDomainLift (coupledChemicalConcentration p u r) y)
      Vt s := by
    change HasDerivAt (((fun _ : ℝ => (1 : ℝ)) +
      fun r => intervalDomainLift (coupledChemicalConcentration p u r) y)) Vt s
    simpa [Vt] using (hasDerivAt_const s (1 : ℝ)).add hv
  have hpow : HasDerivAt
      (fun r => (1 + intervalDomainLift (coupledChemicalConcentration p u r) y) ^
        p.β) (Vt * p.β * B ^ (p.β - 1)) s := by
    simpa [B, v, Vt] using hone.rpow_const (Or.inl (ne_of_gt hbase))
  have hquot := hnum.div hpow hden
  have hvalue :
      (((Ut * G + U * Gt) * B ^ p.β - U * G * (Vt * p.β * B ^ (p.β - 1))) /
          (B ^ p.β) ^ 2) = coupledChemDivFluxTimeDerivativeLift p u s y := by
    rw [chemDiv_flux_deriv_algebra hbase]
    simp [coupledChemDivFluxTimeDerivativeLift, v, U, G, Ut, Gt, Vt]
  rw [← hvalue]
  simpa [coupledChemDivFluxLift, v, U, G, Ut, Gt, Vt, B] using hquot

end ShenWork.IntervalCoupledRegularityBootstrap
