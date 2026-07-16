import ShenWork.Paper1.WaveRotheStep

open Filter Topology Real

noncomputable section

namespace ShenWork.Paper1

/-!
# A target-capped scalar KPP floor

At a fixed moving coordinate the canonical orbit converges only to the wave
value there, which is strictly below one.  Thus the old floor converging all
the way to one cannot serve as a lateral-boundary subsolution on a fixed
half-line.  The floor below converges to an arbitrary target `L < 1` and
never crosses `L`.
-/

/-- Exponentially relaxing floor from `C` toward the prescribed target `L`. -/
def chiZeroKPPFloor (C L lam t : ℝ) : ℝ :=
  L - (L - C) * Real.exp (-lam * t)

@[simp] theorem chiZeroKPPFloor_zero (C L lam : ℝ) :
    chiZeroKPPFloor C L lam 0 = C := by
  simp [chiZeroKPPFloor]

theorem chiZeroKPPFloor_hasDerivAt (C L lam t : ℝ) :
    HasDerivAt (chiZeroKPPFloor C L lam)
      (lam * (L - chiZeroKPPFloor C L lam t)) t := by
  have hlin : HasDerivAt (fun s : ℝ => -lam * s) (-lam) t := by
    simpa using (hasDerivAt_id t).const_mul (-lam)
  have hexp := hlin.exp
  convert (hexp.const_mul (L - C)).const_sub L using 1 <;>
    simp [chiZeroKPPFloor] <;> ring

theorem chiZeroKPPFloor_le_target
    {C L lam t : ℝ} (hCL : C ≤ L) :
    chiZeroKPPFloor C L lam t ≤ L := by
  unfold chiZeroKPPFloor
  exact sub_le_self _ (mul_nonneg (sub_nonneg.mpr hCL) (Real.exp_nonneg _))

theorem chiZeroKPPFloor_ge_start
    {C L lam t : ℝ} (hCL : C ≤ L) (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    C ≤ chiZeroKPPFloor C L lam t := by
  have hexp : Real.exp (-lam * t) ≤ 1 := by
    simpa using Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg hlam ht))
  unfold chiZeroKPPFloor
  have hgap : 0 ≤ L - C := sub_nonneg.mpr hCL
  nlinarith [mul_le_mul_of_nonneg_left hexp hgap]

theorem chiZeroKPPFloor_tendsto_target
    {C L lam : ℝ} (hlam : 0 < lam) :
    Tendsto (chiZeroKPPFloor C L lam) atTop (nhds L) := by
  have hlin : Tendsto (fun t : ℝ => -lam * t) atTop atBot := by
    have hmul : Tendsto (fun t : ℝ => lam * t) atTop atTop :=
      tendsto_id.const_mul_atTop hlam
    simpa only [neg_mul] using tendsto_neg_atTop_atBot.comp hmul
  have hexp : Tendsto (fun t : ℝ => Real.exp (-lam * t)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hlin
  have hconstL : Tendsto (fun _t : ℝ => L) atTop (nhds L) :=
    tendsto_const_nhds
  have hconstGap : Tendsto (fun _t : ℝ => L - C) atTop (nhds (L - C)) :=
    tendsto_const_nhds
  change Tendsto
    (fun t : ℝ => L - (L - C) * Real.exp (-lam * t)) atTop (nhds L)
  simpa using hconstL.sub (hconstGap.mul hexp)

/-- Sufficient scalar condition for the target-capped floor to be a
subsolution of `b' = reactionFun alpha b`. -/
theorem chiZeroKPPFloor_deriv_le_reaction
    {alpha C L lam t : ℝ}
    (halpha : 1 ≤ alpha) (hC : 0 < C) (hCL : C ≤ L) (hL1 : L < 1)
    (hlam : 0 ≤ lam) (ht : 0 ≤ t)
    (hrate : lam * (L - C) ≤ C * (1 - L ^ alpha)) :
    deriv (chiZeroKPPFloor C L lam) t ≤
      reactionFun alpha (chiZeroKPPFloor C L lam t) := by
  let B := chiZeroKPPFloor C L lam t
  have hBderiv : deriv (chiZeroKPPFloor C L lam) t = lam * (L - B) := by
    simpa [B] using (chiZeroKPPFloor_hasDerivAt C L lam t).deriv
  have hBge : C ≤ B := chiZeroKPPFloor_ge_start hCL hlam ht
  have hBle : B ≤ L := chiZeroKPPFloor_le_target hCL
  have hB0 : 0 ≤ B := hC.le.trans hBge
  have hL0 : 0 ≤ L := hB0.trans hBle
  have halpha0 : 0 ≤ alpha := zero_le_one.trans halpha
  have hpow : B ^ alpha ≤ L ^ alpha :=
    Real.rpow_le_rpow hB0 hBle halpha0
  have hLpow1 : L ^ alpha < 1 := by
    have halphaPos : 0 < alpha := lt_of_lt_of_le zero_lt_one halpha
    simpa only [Real.one_rpow] using
      Real.rpow_lt_rpow hL0 hL1 halphaPos
  have hgapL : 0 ≤ 1 - L ^ alpha := by linarith
  have hgapB : 0 ≤ 1 - B ^ alpha := by linarith
  have htimeBound : lam * (L - B) ≤ lam * (L - C) := by
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left hBge L) hlam
  have hreactionBound : C * (1 - L ^ alpha) ≤ B * (1 - B ^ alpha) := by
    calc
      C * (1 - L ^ alpha) ≤ B * (1 - L ^ alpha) :=
        mul_le_mul_of_nonneg_right hBge hgapL
      _ ≤ B * (1 - B ^ alpha) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_left hpow 1) hB0
  rw [hBderiv]
  unfold reactionFun
  exact htimeBound.trans (hrate.trans hreactionBound)

/-- A concrete positive rate satisfying the preceding subsolution condition. -/
def chiZeroKPPFloorRate (alpha C L : ℝ) : ℝ :=
  C * (1 - L ^ alpha) / (L - C + 1)

theorem chiZeroKPPFloorRate_pos
    {alpha C L : ℝ}
    (halpha : 1 ≤ alpha) (hC : 0 < C) (hCL : C < L) (hL1 : L < 1) :
    0 < chiZeroKPPFloorRate alpha C L := by
  have hL0 : 0 ≤ L := hC.le.trans hCL.le
  have halphaPos : 0 < alpha := lt_of_lt_of_le zero_lt_one halpha
  have hLpow1 : L ^ alpha < 1 := by
    simpa only [Real.one_rpow] using
      Real.rpow_lt_rpow hL0 hL1 halphaPos
  have hnum : 0 < C * (1 - L ^ alpha) :=
    mul_pos hC (sub_pos.mpr hLpow1)
  have hden : 0 < L - C + 1 := by linarith
  unfold chiZeroKPPFloorRate
  exact div_pos hnum hden

theorem chiZeroKPPFloorRate_mul_gap_le
    {alpha C L : ℝ}
    (halpha : 1 ≤ alpha) (hC : 0 < C) (hCL : C < L) (hL1 : L < 1) :
    chiZeroKPPFloorRate alpha C L * (L - C) ≤
      C * (1 - L ^ alpha) := by
  have hL0 : 0 ≤ L := hC.le.trans hCL.le
  have halphaPos : 0 < alpha := lt_of_lt_of_le zero_lt_one halpha
  have hLpow1 : L ^ alpha < 1 := by
    simpa only [Real.one_rpow] using
      Real.rpow_lt_rpow hL0 hL1 halphaPos
  have hgap : 0 < L - C := sub_pos.mpr hCL
  have hden : 0 < L - C + 1 := by linarith
  have hfrac : (L - C) / (L - C + 1) ≤ 1 := by
    exact (div_le_one hden).2 (by linarith)
  unfold chiZeroKPPFloorRate
  calc
    (C * (1 - L ^ alpha) / (L - C + 1)) * (L - C) =
        (C * (1 - L ^ alpha)) * ((L - C) / (L - C + 1)) := by ring
    _ ≤ (C * (1 - L ^ alpha)) * 1 :=
      mul_le_mul_of_nonneg_left hfrac (mul_nonneg hC.le (by linarith))
    _ = C * (1 - L ^ alpha) := mul_one _

section AxiomAudit

#print axioms chiZeroKPPFloor_hasDerivAt
#print axioms chiZeroKPPFloor_le_target
#print axioms chiZeroKPPFloor_ge_start
#print axioms chiZeroKPPFloor_tendsto_target
#print axioms chiZeroKPPFloor_deriv_le_reaction
#print axioms chiZeroKPPFloorRate_pos
#print axioms chiZeroKPPFloorRate_mul_gap_le

end AxiomAudit

end ShenWork.Paper1
