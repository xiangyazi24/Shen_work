import ShenWork.Paper1.WholeLineChiPosRectangleSeed

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-!
# A crude positive floor through the ceiling burn-in interval

Before the positive-sensitivity ceiling has relaxed close to `MChi`, the
resolver is controlled only by a possibly large global bound `G ^ γ`.  A
decaying exponential preserves a strictly positive uniform floor across this
finite interval.  The rectangle floor can then be restarted under the sharper
eventual ceiling.
-/

/-- Exponentially decaying scalar floor. -/
def chiPosDecayFloor (C lam t : ℝ) : ℝ :=
  C * Real.exp (-lam * t)

/-- A deliberately generous decay rate valid under the resolver ceiling
`G ^ γ`. -/
def chiPosDecayFloorRate (p : CMParams) (G : ℝ) : ℝ :=
  p.χ * G ^ (p.m - 1) * G ^ p.γ + G ^ p.α + 1

@[simp] theorem chiPosDecayFloor_zero (C lam : ℝ) :
    chiPosDecayFloor C lam 0 = C := by
  simp [chiPosDecayFloor]

theorem chiPosDecayFloor_hasDerivAt (C lam t : ℝ) :
    HasDerivAt (chiPosDecayFloor C lam)
      (-lam * chiPosDecayFloor C lam t) t := by
  have hlin : HasDerivAt (fun s : ℝ => -lam * s) (-lam) t := by
    simpa using (hasDerivAt_id t).const_mul (-lam)
  have hexp := hlin.exp
  convert hexp.const_mul C using 1 <;> simp [chiPosDecayFloor] <;> ring

theorem chiPosDecayFloorRate_pos
    {p : CMParams} {G : ℝ} (hchi : 0 ≤ p.χ) (hG : 0 ≤ G) :
    0 < chiPosDecayFloorRate p G := by
  unfold chiPosDecayFloorRate
  have hm0 : 0 ≤ G ^ (p.m - 1) := Real.rpow_nonneg hG _
  have hgamma0 : 0 ≤ G ^ p.γ := Real.rpow_nonneg hG _
  have halpha0 : 0 ≤ G ^ p.α := Real.rpow_nonneg hG _
  nlinarith [mul_nonneg (mul_nonneg hchi hm0) hgamma0]

theorem chiPosDecayFloor_pos
    {C lam t : ℝ} (hC : 0 < C) :
    0 < chiPosDecayFloor C lam t :=
  mul_pos hC (Real.exp_pos _)

theorem chiPosDecayFloor_le_start
    {C lam t : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    chiPosDecayFloor C lam t ≤ C := by
  have hexp : Real.exp (-lam * t) ≤ 1 := by
    simpa using Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg hlam ht))
  unfold chiPosDecayFloor
  simpa using mul_le_mul_of_nonneg_left hexp hC

/-- The crude decay floor satisfies the weighted resolver budget for every
nonnegative solution bounded by `G`. -/
theorem chiPosDecayFloor_weighted_subsolution
    {p : CMParams} {G C t : ℝ}
    (hchi : 0 ≤ p.χ) (hG : 0 ≤ G)
    (hC : 0 < C) (hCG : C ≤ G) (ht : 0 ≤ t) :
    deriv (chiPosDecayFloor C (chiPosDecayFloorRate p G)) t +
        p.χ * (chiPosDecayFloor C (chiPosDecayFloorRate p G) t) ^ p.m *
          G ^ p.γ ≤
      reactionFun p.α
        (chiPosDecayFloor C (chiPosDecayFloorRate p G) t) := by
  let lam : ℝ := chiPosDecayFloorRate p G
  let B : ℝ := chiPosDecayFloor C lam t
  have hlam : 0 < lam := chiPosDecayFloorRate_pos hchi hG
  have hBpos : 0 < B := chiPosDecayFloor_pos hC
  have hBC : B ≤ C := chiPosDecayFloor_le_start hC.le hlam.le ht
  have hBG : B ≤ G := hBC.trans hCG
  have hm0 : 0 ≤ p.m - 1 := sub_nonneg.mpr p.hm
  have hBm : B ^ (p.m - 1) ≤ G ^ (p.m - 1) :=
    Real.rpow_le_rpow hBpos.le hBG hm0
  have hBalpha : B ^ p.α ≤ G ^ p.α :=
    Real.rpow_le_rpow hBpos.le hBG (zero_le_one.trans p.hα)
  have hGgamma : 0 ≤ G ^ p.γ := Real.rpow_nonneg hG _
  have hchiPow :
      p.χ * B ^ (p.m - 1) * G ^ p.γ ≤
        p.χ * G ^ (p.m - 1) * G ^ p.γ := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hBm hchi) hGgamma
  have hcoef :
      -lam + p.χ * B ^ (p.m - 1) * G ^ p.γ ≤ 1 - B ^ p.α := by
    dsimp [lam, chiPosDecayFloorRate]
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hcoef hBpos.le
  have hm : B * B ^ (p.m - 1) = B ^ p.m :=
    mul_rpow_sub_one p.m p.hm hBpos.le
  have hderiv : deriv (chiPosDecayFloor C lam) t = -lam * B := by
    simpa [B] using (chiPosDecayFloor_hasDerivAt C lam t).deriv
  change deriv (chiPosDecayFloor C lam) t + p.χ * B ^ p.m * G ^ p.γ ≤
    reactionFun p.α B
  rw [hderiv]
  unfold reactionFun
  rw [← hm]
  nlinarith

section AxiomAudit

#print axioms chiPosDecayFloor_hasDerivAt
#print axioms chiPosDecayFloorRate_pos
#print axioms chiPosDecayFloor_weighted_subsolution

end AxiomAudit

end ShenWork.Paper1
