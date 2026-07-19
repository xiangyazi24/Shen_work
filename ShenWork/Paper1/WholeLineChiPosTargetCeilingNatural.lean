import ShenWork.Paper1.WholeLineWeightedRegularityChiZeroKPPFloorNatural

open Filter Topology Real

noncomputable section

namespace ShenWork.Paper1

/-!
# A target-capped scalar KPP ceiling

The ceiling relaxes exponentially from an initial height `D` toward a target
`Ahat > 1`.  Its rate can reserve a fixed positive-sensitivity defect while
remaining a supersolution of the scalar logistic reaction.
-/

/-- Exponentially relaxing ceiling from `D` toward the prescribed target
`Ahat`. -/
def chiPosTargetCeiling (Ahat D lam t : ℝ) : ℝ :=
  Ahat + (D - Ahat) * Real.exp (-lam * t)

@[simp] theorem chiPosTargetCeiling_zero (Ahat D lam : ℝ) :
    chiPosTargetCeiling Ahat D lam 0 = D := by
  simp [chiPosTargetCeiling]

theorem chiPosTargetCeiling_hasDerivAt (Ahat D lam t : ℝ) :
    HasDerivAt (chiPosTargetCeiling Ahat D lam)
      (-lam * (chiPosTargetCeiling Ahat D lam t - Ahat)) t := by
  have hlin : HasDerivAt (fun s : ℝ => -lam * s) (-lam) t := by
    simpa using (hasDerivAt_id t).const_mul (-lam)
  have hexp := hlin.exp
  convert (hasDerivAt_const t Ahat).add (hexp.const_mul (D - Ahat)) using 1 <;>
    simp [chiPosTargetCeiling] <;> ring

theorem chiPosTargetCeiling_ge_target
    {Ahat D lam t : ℝ} (hAD : Ahat ≤ D) :
    Ahat ≤ chiPosTargetCeiling Ahat D lam t := by
  unfold chiPosTargetCeiling
  exact le_add_of_nonneg_right
    (mul_nonneg (sub_nonneg.mpr hAD) (Real.exp_nonneg _))

theorem chiPosTargetCeiling_le_start
    {Ahat D lam t : ℝ} (hAD : Ahat ≤ D)
    (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    chiPosTargetCeiling Ahat D lam t ≤ D := by
  have hexp : Real.exp (-lam * t) ≤ 1 := by
    simpa using Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg hlam ht))
  unfold chiPosTargetCeiling
  have hgap : 0 ≤ D - Ahat := sub_nonneg.mpr hAD
  nlinarith [mul_le_mul_of_nonneg_left hexp hgap]

/-- The target ceiling stays in the interval from its target to its start. -/
theorem chiPosTargetCeiling_mem_Icc
    {Ahat D lam t : ℝ} (hAD : Ahat ≤ D)
    (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    chiPosTargetCeiling Ahat D lam t ∈ Set.Icc Ahat D := by
  exact ⟨chiPosTargetCeiling_ge_target hAD,
    chiPosTargetCeiling_le_start hAD hlam ht⟩

theorem chiPosTargetCeiling_tendsto_target
    {Ahat D lam : ℝ} (hlam : 0 < lam) :
    Tendsto (chiPosTargetCeiling Ahat D lam) atTop (nhds Ahat) := by
  have hlin : Tendsto (fun t : ℝ => -lam * t) atTop atBot := by
    have hmul : Tendsto (fun t : ℝ => lam * t) atTop atTop :=
      tendsto_id.const_mul_atTop hlam
    simpa only [neg_mul] using tendsto_neg_atTop_atBot.comp hmul
  have hexp : Tendsto (fun t : ℝ => Real.exp (-lam * t)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hlin
  have hconstA : Tendsto (fun _t : ℝ => Ahat) atTop (nhds Ahat) :=
    tendsto_const_nhds
  have hconstGap : Tendsto (fun _t : ℝ => D - Ahat) atTop (nhds (D - Ahat)) :=
    tendsto_const_nhds
  change Tendsto
    (fun t : ℝ => Ahat + (D - Ahat) * Real.exp (-lam * t)) atTop (nhds Ahat)
  simpa using hconstA.add (hconstGap.mul hexp)

/-- Restarting a target ceiling preserves the same exponential orbit, provided
the relaxation rate is kept fixed. -/
theorem chiPosTargetCeiling_restart (Ahat D lam a s : ℝ) :
    chiPosTargetCeiling Ahat (chiPosTargetCeiling Ahat D lam a) lam s =
      chiPosTargetCeiling Ahat D lam (a + s) := by
  simp only [chiPosTargetCeiling]
  have hexp : Real.exp (-lam * a) * Real.exp (-lam * s) =
      Real.exp (-lam * (a + s)) := by
    rw [← Real.exp_add]
    ring_nf
  have hscaled :
      (D - Ahat) * Real.exp (-lam * a) * Real.exp (-lam * s) =
        (D - Ahat) * Real.exp (-lam * (a + s)) := by
    rw [mul_assoc, hexp]
  linarith

/-- Positive relaxation rate after reserving a fixed upper-contact defect
`H`. -/
def chiPosTargetCeilingRate (alpha Ahat D H : ℝ) : ℝ :=
  (Ahat * (Ahat ^ alpha - 1) - H) / (D - Ahat + 1)

theorem chiPosTargetCeilingRate_pos
    {alpha Ahat D H : ℝ} (hAD : Ahat ≤ D)
    (hH : H < Ahat * (Ahat ^ alpha - 1)) :
    0 < chiPosTargetCeilingRate alpha Ahat D H := by
  have hden : 0 < D - Ahat + 1 := by linarith
  unfold chiPosTargetCeilingRate
  exact div_pos (sub_pos.mpr hH) hden

theorem chiPosTargetCeilingRate_mul_gap_add_defect_le
    {alpha Ahat D H : ℝ} (hAD : Ahat ≤ D)
    (hH : H < Ahat * (Ahat ^ alpha - 1)) :
    chiPosTargetCeilingRate alpha Ahat D H * (D - Ahat) + H ≤
      Ahat * (Ahat ^ alpha - 1) := by
  let A : ℝ := Ahat * (Ahat ^ alpha - 1)
  have hden : 0 < D - Ahat + 1 := by linarith
  have hAH : 0 < A - H := sub_pos.mpr hH
  have hfrac : (D - Ahat) / (D - Ahat + 1) ≤ 1 :=
    (div_le_one hden).2 (by linarith)
  have hscaled :
      (A - H) * ((D - Ahat) / (D - Ahat + 1)) ≤ A - H := by
    simpa using mul_le_mul_of_nonneg_left hfrac hAH.le
  unfold chiPosTargetCeilingRate
  dsimp [A] at hscaled
  calc
    ((Ahat * (Ahat ^ alpha - 1) - H) / (D - Ahat + 1)) *
          (D - Ahat) + H =
        (Ahat * (Ahat ^ alpha - 1) - H) *
          ((D - Ahat) / (D - Ahat + 1)) + H := by ring
    _ ≤ (Ahat * (Ahat ^ alpha - 1) - H) + H := by
      linarith [hscaled]
    _ = Ahat * (Ahat ^ alpha - 1) := by ring

/-- With the defect-reserving rate, the target ceiling is a supersolution of
the scalar logistic reaction plus the fixed defect `H`. -/
theorem chiPosTargetCeiling_deriv_ge_reaction_add_defect
    {alpha Ahat D H t : ℝ}
    (halpha : 1 ≤ alpha) (hA1 : 1 < Ahat) (hAD : Ahat ≤ D)
    (hH : H < Ahat * (Ahat ^ alpha - 1)) (ht : 0 ≤ t) :
    deriv (chiPosTargetCeiling Ahat D
      (chiPosTargetCeilingRate alpha Ahat D H)) t ≥
      reactionFun alpha (chiPosTargetCeiling Ahat D
        (chiPosTargetCeilingRate alpha Ahat D H) t) + H := by
  let lam : ℝ := chiPosTargetCeilingRate alpha Ahat D H
  let B : ℝ := chiPosTargetCeiling Ahat D lam t
  have hlam : 0 < lam := chiPosTargetCeilingRate_pos hAD hH
  have hBderiv : deriv (chiPosTargetCeiling Ahat D lam) t =
      -lam * (B - Ahat) := by
    simpa [B] using (chiPosTargetCeiling_hasDerivAt Ahat D lam t).deriv
  have hAge : Ahat ≤ B := chiPosTargetCeiling_ge_target hAD
  have hBle : B ≤ D := chiPosTargetCeiling_le_start hAD hlam.le ht
  have hA0 : 0 ≤ Ahat := zero_le_one.trans hA1.le
  have hB0 : 0 ≤ B := hA0.trans hAge
  have halpha0 : 0 ≤ alpha := zero_le_one.trans halpha
  have hpow : Ahat ^ alpha ≤ B ^ alpha :=
    Real.rpow_le_rpow hA0 hAge halpha0
  have hApow1 : 1 < Ahat ^ alpha := by
    have halphaPos : 0 < alpha := lt_of_lt_of_le zero_lt_one halpha
    simpa only [Real.one_rpow] using
      Real.rpow_lt_rpow zero_le_one hA1 halphaPos
  have hgapA : 0 ≤ Ahat ^ alpha - 1 := by linarith
  have htimeBound : lam * (B - Ahat) ≤ lam * (D - Ahat) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right hBle Ahat) hlam.le
  have hbudget : lam * (D - Ahat) + H ≤ Ahat * (Ahat ^ alpha - 1) := by
    simpa [lam] using
      chiPosTargetCeilingRate_mul_gap_add_defect_le hAD hH
  have hreactionBound :
      Ahat * (Ahat ^ alpha - 1) ≤ B * (B ^ alpha - 1) := by
    calc
      Ahat * (Ahat ^ alpha - 1) ≤ B * (Ahat ^ alpha - 1) :=
        mul_le_mul_of_nonneg_right hAge hgapA
      _ ≤ B * (B ^ alpha - 1) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_right hpow 1) hB0
  have htotal : lam * (B - Ahat) + H ≤ B * (B ^ alpha - 1) :=
    (show lam * (B - Ahat) + H ≤ lam * (D - Ahat) + H by
      linarith [htimeBound]).trans (hbudget.trans hreactionBound)
  rw [hBderiv]
  unfold reactionFun
  nlinarith [htotal]

section AxiomAudit

#print axioms chiPosTargetCeiling_zero
#print axioms chiPosTargetCeiling_hasDerivAt
#print axioms chiPosTargetCeiling_ge_target
#print axioms chiPosTargetCeiling_le_start
#print axioms chiPosTargetCeiling_mem_Icc
#print axioms chiPosTargetCeiling_tendsto_target
#print axioms chiPosTargetCeiling_restart
#print axioms chiPosTargetCeilingRate_pos
#print axioms chiPosTargetCeilingRate_mul_gap_add_defect_le
#print axioms chiPosTargetCeiling_deriv_ge_reaction_add_defect

end AxiomAudit

end ShenWork.Paper1
