import ShenWork.Paper1.WholeLineWeightedRegularityChiZeroKPPFloorNatural

open Filter Topology Real

noncomputable section

namespace ShenWork.Paper1

/-!
# Target-capped KPP floors with a fixed negative-sensitivity defect

On a buffered left half-line the elliptic resolver misses only an
exponentially small fraction of the constant-source mass.  The resulting
chemotactic loss is a fixed nonnegative scalar `H`.  The rate below leaves
exactly that amount of room in the logistic reaction and still converges to
the prescribed target `L < 1`.
-/

/-- Positive relaxation rate after reserving a fixed defect `H` from the
logistic reaction budget. -/
def chiNegKPPFloorRate (alpha C L H : ℝ) : ℝ :=
  (C * (1 - L ^ alpha) - H) / (L - C + 1)

theorem chiNegKPPFloorRate_pos
    {alpha C L H : ℝ}
    (hCL : C < L)
    (hH : H < C * (1 - L ^ alpha)) :
    0 < chiNegKPPFloorRate alpha C L H := by
  have hden : 0 < L - C + 1 := by linarith
  unfold chiNegKPPFloorRate
  exact div_pos (sub_pos.mpr hH) hden

theorem chiNegKPPFloorRate_mul_gap_add_defect_le
    {alpha C L H : ℝ}
    (hCL : C < L)
    (hH : H < C * (1 - L ^ alpha)) :
    chiNegKPPFloorRate alpha C L H * (L - C) + H ≤
      C * (1 - L ^ alpha) := by
  let A : ℝ := C * (1 - L ^ alpha)
  have hgap : 0 < L - C := sub_pos.mpr hCL
  have hden : 0 < L - C + 1 := by linarith
  have hAH : 0 < A - H := sub_pos.mpr hH
  have hfrac : (L - C) / (L - C + 1) ≤ 1 := by
    exact (div_le_one hden).2 (by linarith)
  have hscaled : (A - H) * ((L - C) / (L - C + 1)) ≤ A - H := by
    simpa using mul_le_mul_of_nonneg_left hfrac hAH.le
  unfold chiNegKPPFloorRate
  dsimp [A] at hscaled
  calc
    ((C * (1 - L ^ alpha) - H) / (L - C + 1)) * (L - C) + H =
        (C * (1 - L ^ alpha) - H) *
            ((L - C) / (L - C + 1)) + H := by ring
    _ ≤ (C * (1 - L ^ alpha) - H) + H :=
      by linarith [hscaled]
    _ = C * (1 - L ^ alpha) := by ring

/-- The target-capped floor remains a reaction subsolution after adding the
fixed nonnegative defect `H` to its time derivative. -/
theorem chiNegKPPFloor_deriv_add_defect_le_reaction
    {alpha C L H t : ℝ}
    (halpha : 1 ≤ alpha) (hC : 0 < C) (hCL : C < L) (hL1 : L < 1)
    (hH : H < C * (1 - L ^ alpha)) (ht : 0 ≤ t) :
    deriv (chiZeroKPPFloor C L (chiNegKPPFloorRate alpha C L H)) t + H ≤
      reactionFun alpha
        (chiZeroKPPFloor C L (chiNegKPPFloorRate alpha C L H) t) := by
  let lam : ℝ := chiNegKPPFloorRate alpha C L H
  let B : ℝ := chiZeroKPPFloor C L lam t
  have hlam : 0 < lam :=
    chiNegKPPFloorRate_pos hCL hH
  have hBderiv : deriv (chiZeroKPPFloor C L lam) t = lam * (L - B) := by
    simpa [B] using (chiZeroKPPFloor_hasDerivAt C L lam t).deriv
  have hBge : C ≤ B := chiZeroKPPFloor_ge_start hCL.le hlam.le ht
  have hBle : B ≤ L := chiZeroKPPFloor_le_target hCL.le
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
  have htimeBound : lam * (L - B) ≤ lam * (L - C) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_left hBge L) hlam.le
  have hbudget : lam * (L - C) + H ≤ C * (1 - L ^ alpha) := by
    simpa [lam] using
      chiNegKPPFloorRate_mul_gap_add_defect_le
        hCL hH
  have hreactionBound : C * (1 - L ^ alpha) ≤
      B * (1 - B ^ alpha) := by
    calc
      C * (1 - L ^ alpha) ≤ B * (1 - L ^ alpha) :=
        mul_le_mul_of_nonneg_right hBge hgapL
      _ ≤ B * (1 - B ^ alpha) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_left hpow 1) hB0
  rw [hBderiv]
  unfold reactionFun
  have htimeDefect : lam * (L - B) + H ≤ lam * (L - C) + H := by
    linarith [htimeBound]
  exact htimeDefect.trans (hbudget.trans hreactionBound)

/-- Any fixed coefficient times the missing right-kernel mass can be made
smaller than a prescribed positive reaction budget by taking a sufficiently
wide buffer. -/
theorem exists_nonneg_buffer_exp_defect_lt
    {K budget : ℝ} (hbudget : 0 < budget) :
    ∃ R : ℝ, 0 ≤ R ∧ K * (Real.exp (-R) / 2) < budget := by
  have hneg : Tendsto (fun R : ℝ => -R) atTop atBot :=
    tendsto_neg_atTop_atBot
  have hexp : Tendsto (fun R : ℝ => Real.exp (-R)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hscaled : Tendsto
      (fun R : ℝ => (K / 2) * Real.exp (-R)) atTop (𝓝 0) := by
    simpa using hexp.const_mul (K / 2)
  have hsmall : ∀ᶠ R : ℝ in atTop,
      (K / 2) * Real.exp (-R) < budget :=
    hscaled (Iio_mem_nhds hbudget)
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 hsmall
  let R : ℝ := max R₀ 0
  refine ⟨R, le_max_right _ _, ?_⟩
  have hraw := hR₀ R (le_max_left _ _)
  calc
    K * (Real.exp (-R) / 2) = (K / 2) * Real.exp (-R) := by ring
    _ < budget := hraw

section AxiomAudit

#print axioms chiNegKPPFloorRate_pos
#print axioms chiNegKPPFloorRate_mul_gap_add_defect_le
#print axioms chiNegKPPFloor_deriv_add_defect_le_reaction
#print axioms exists_nonneg_buffer_exp_defect_lt

end AxiomAudit

end ShenWork.Paper1
