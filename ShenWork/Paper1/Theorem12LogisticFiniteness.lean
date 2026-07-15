import ShenWork.Paper1.Theorem12WeightedResolverEta

open Filter MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Logistic exhaustion weight for the route-B weighted finiteness

`capWeight η R z = e^{2ηz} / (1 + e^{2η(z-R)})` is a smooth, elementary exhaustion of the
exponential weight `e^{2ηz}`: it equals `e^{2ηz}` for `z ≪ R`, levels off to the plateau
`e^{2ηR}` for `z ≫ R`, is bounded, and is *moderate* — `|∂_z capWeight| ≤ 2η · capWeight`
on the whole line.  This moderateness (the derivative of the cap only *decreases* the log
derivative, never blows it up as a compact cutoff would) is what makes the truncated weighted
energy estimate close with an `R`-independent constant.
-/

/-- The (strictly positive) denominator of the logistic weight. -/
theorem capWeight_denom_pos (η R z : ℝ) : 0 < 1 + Real.exp (2 * η * (z - R)) := by
  have := Real.exp_pos (2 * η * (z - R)); linarith

/-- Logistic exhaustion weight `e^{2ηz}/(1+e^{2η(z-R)})`. -/
def capWeight (η R z : ℝ) : ℝ :=
  Real.exp (2 * η * z) / (1 + Real.exp (2 * η * (z - R)))

theorem capWeight_pos (η R z : ℝ) : 0 < capWeight η R z :=
  div_pos (Real.exp_pos _) (capWeight_denom_pos η R z)

theorem capWeight_nonneg (η R z : ℝ) : 0 ≤ capWeight η R z := (capWeight_pos η R z).le

/-- `capWeight ≤ e^{2ηz}` since the denominator is `≥ 1`. -/
theorem capWeight_le_full (η R z : ℝ) : capWeight η R z ≤ Real.exp (2 * η * z) := by
  refine div_le_self (Real.exp_nonneg _) ?_
  have := Real.exp_pos (2 * η * (z - R)); linarith

/-- `capWeight ≤ e^{2ηR}` (the plateau bound). -/
theorem capWeight_le_plateau (η R z : ℝ) : capWeight η R z ≤ Real.exp (2 * η * R) := by
  rw [capWeight, div_le_iff₀ (capWeight_denom_pos η R z)]
  have hmul : Real.exp (2 * η * R) * Real.exp (2 * η * (z - R)) = Real.exp (2 * η * z) := by
    rw [← Real.exp_add]; ring_nf
  nlinarith [Real.exp_pos (2 * η * R), Real.exp_pos (2 * η * (z - R)), hmul]

/-- Chain-rule derivative of `z ↦ e^{2ηz}`. -/
theorem hasDerivAt_exp_lin (a z : ℝ) :
    HasDerivAt (fun z => Real.exp (a * z)) (a * Real.exp (a * z)) z := by
  have h : HasDerivAt (fun z => a * z) a z := by
    simpa using (hasDerivAt_id z).const_mul a
  simpa [mul_comm] using (Real.hasDerivAt_exp (a * z)).comp z h

/-- The exact derivative of the logistic weight:
`∂_z capWeight = 2η · capWeight / (1 + e^{2η(z-R)})`. -/
theorem capWeight_hasDerivAt (η R z : ℝ) :
    HasDerivAt (capWeight η R)
      (2 * η * capWeight η R z / (1 + Real.exp (2 * η * (z - R)))) z := by
  have hf : HasDerivAt (fun z => Real.exp (2 * η * z)) (2 * η * Real.exp (2 * η * z)) z :=
    hasDerivAt_exp_lin (2 * η) z
  have hg' : HasDerivAt (fun z => Real.exp (2 * η * (z - R)))
      (2 * η * Real.exp (2 * η * (z - R))) z := by
    have h : HasDerivAt (fun z => 2 * η * (z - R)) (2 * η) z := by
      simpa using ((hasDerivAt_id z).sub_const R).const_mul (2 * η)
    simpa [mul_comm] using (Real.hasDerivAt_exp (2 * η * (z - R))).comp z h
  have hg : HasDerivAt (fun z => 1 + Real.exp (2 * η * (z - R)))
      (2 * η * Real.exp (2 * η * (z - R))) z := by
    simpa using hg'.const_add (1 : ℝ)
  have hd := hf.div hg (ne_of_gt (capWeight_denom_pos η R z))
  convert hd using 1
  set E := Real.exp (2 * η * z) with hE
  set F := Real.exp (2 * η * (z - R)) with hF
  have hden : (0 : ℝ) < 1 + F := by rw [hF]; exact capWeight_denom_pos η R z
  rw [capWeight]
  field_simp
  ring

theorem capWeight_deriv_eq (η R z : ℝ) :
    deriv (capWeight η R) z
      = 2 * η * capWeight η R z / (1 + Real.exp (2 * η * (z - R))) :=
  (capWeight_hasDerivAt η R z).deriv

/-- The MODERATE bound: `|∂_z capWeight| ≤ 2η · capWeight` on the whole line. -/
theorem capWeight_abs_deriv_le {η : ℝ} (hη : 0 ≤ η) (R z : ℝ) :
    |deriv (capWeight η R) z| ≤ 2 * η * capWeight η R z := by
  rw [capWeight_deriv_eq]
  have hden : (0 : ℝ) < 1 + Real.exp (2 * η * (z - R)) := capWeight_denom_pos η R z
  have hnum : 0 ≤ 2 * η * capWeight η R z :=
    mul_nonneg (by positivity) (capWeight_nonneg η R z)
  rw [abs_of_nonneg (div_nonneg hnum hden.le)]
  refine div_le_self hnum ?_
  have := Real.exp_pos (2 * η * (z - R)); linarith

/-- `capWeight` is monotone increasing in the truncation radius `R` (for `η ≥ 0`). -/
theorem capWeight_mono_R {η : ℝ} (hη : 0 ≤ η) (z : ℝ) :
    Monotone (fun R => capWeight η R z) := by
  intro R₁ R₂ hR
  simp only [capWeight]
  apply div_le_div_of_nonneg_left (Real.exp_nonneg _) (capWeight_denom_pos η R₂ z)
  have h : Real.exp (2 * η * (z - R₂)) ≤ Real.exp (2 * η * (z - R₁)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  linarith

/-- `capWeight η R z → e^{2ηz}` as `R → ∞` (for `η > 0`). -/
theorem capWeight_tendsto_full {η : ℝ} (hη : 0 < η) (z : ℝ) :
    Filter.Tendsto (fun R => capWeight η R z) Filter.atTop
      (nhds (Real.exp (2 * η * z))) := by
  have hRz : Filter.Tendsto (fun R : ℝ => 2 * η * (R - z)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity)
      (Filter.tendsto_atTop_add_const_right _ (-z) Filter.tendsto_id)
  have hinner : Filter.Tendsto (fun R : ℝ => 2 * η * (z - R)) Filter.atTop Filter.atBot := by
    have : (fun R : ℝ => 2 * η * (z - R)) = fun R => -(2 * η * (R - z)) := by
      funext R; ring
    rw [this]; exact tendsto_neg_atTop_atBot.comp hRz
  have hexp : Filter.Tendsto (fun R => Real.exp (2 * η * (z - R))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_comp_nhds_zero.mpr hinner
  have hden : Filter.Tendsto (fun R => 1 + Real.exp (2 * η * (z - R))) Filter.atTop (nhds 1) := by
    simpa using hexp.const_add (1 : ℝ)
  have hquot := (tendsto_const_nhds (x := Real.exp (2 * η * z))
    (f := Filter.atTop)).div hden (by norm_num)
  simpa [capWeight, div_one] using hquot

section Theorem12LogisticFinitenessAxiomAudit

#print axioms capWeight_pos
#print axioms capWeight_le_full
#print axioms capWeight_le_plateau
#print axioms capWeight_hasDerivAt
#print axioms capWeight_abs_deriv_le
#print axioms capWeight_mono_R
#print axioms capWeight_tendsto_full

end Theorem12LogisticFinitenessAxiomAudit

end ShenWork.Paper1
