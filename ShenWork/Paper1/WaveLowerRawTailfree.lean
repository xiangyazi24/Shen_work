import ShenWork.Paper1.WavePaperApproxComparison
import ShenWork.Paper1.WaveLemma42G1Discharge

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-- Positivity of the raw two-exponential lower barrier characterizes the
right side of its zero.  The reverse implication complements the existing
`lowerBarrierRaw_pos_of_xminus_lt`. -/
theorem lowerBarrierXMinus_lt_of_lowerBarrierRaw_pos
    {κ κtilde D x : ℝ}
    (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (hpos : 0 < lowerBarrierRaw κ κtilde D x) :
    lowerBarrierXMinus κ κtilde D < x := by
  by_contra hnot
  have hx : x ≤ lowerBarrierXMinus κ κtilde D := le_of_not_gt hnot
  have hlog_ge : (κtilde - κ) * x ≤ Real.log D := by
    rw [lowerBarrierXMinus] at hx
    have := (le_div_iff₀ hgap).mp hx
    simpa [mul_comm] using this
  have hexp_ge :
      Real.exp 0 ≤
        Real.exp (Real.log D + (-(κtilde - κ) * x)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hDone : 1 ≤ D * Real.exp (-(κtilde - κ) * x) := by
    simpa [Real.exp_add, Real.exp_log hD] using hexp_ge
  rw [lowerBarrierRaw_eq_exp_mul] at hpos
  have hfactor :
      1 - D * Real.exp (-(κtilde - κ) * x) ≤ 0 := by
    linarith
  have hexp0 : 0 < Real.exp (-κ * x) := Real.exp_pos _
  nlinarith

/-- The sole local estimate needed by the tail-free lower comparison.  Unlike
`PaperLowerRawStepAux`, this record contains no endpoint limits and no global
maximum-attainment field. -/
structure PaperLowerRawStepApproxOperatorData
    (p : CMParams) (c lam κ κtilde D : ℝ)
    (u W : ℝ → ℝ) : Type where
  Cmono : ℝ
  E : ℝ
  small : (1 / lam) * Cmono < 1
  E_nonneg : 0 ≤ E
  op_approx : ∀ eta, 0 < eta → ∀ x₀,
    0 < lowerBarrierRaw κ κtilde D x₀ - W x₀ →
    |deriv (fun x => lowerBarrierRaw κ κtilde D x - W x) x₀| < eta →
    deriv (deriv (fun x => lowerBarrierRaw κ κtilde D x - W x)) x₀ < eta →
    paperWaveOperator p c u (lowerBarrierRaw κ κtilde D) x₀ -
        paperWaveOperator p c u W x₀ ≤
      Cmono * (lowerBarrierRaw κ κtilde D x₀ - W x₀) + E * eta

/-- Lemma 4.2 plus the one-sided approximate maximum principle preserves the
raw lower barrier in one paper implicit step.  No orbit tail, family-uniform
tail, or endpoint limit occurs. -/
theorem paperImplicitStep_ge_lowerBarrierRaw_tailfree
    {p : CMParams} {c lam M κ κtilde D : ℝ} {u Z W : ℝ → ℝ}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hu : InLowerPinnedMonotoneTrap κ M
      (lowerBarrierRaw κ κtilde D) u)
    (hprev : ∀ x, lowerBarrierRaw κ κtilde D x ≤ Z x)
    (hlam : 0 < lam)
    (hstep : ∀ x,
      paperImplicitStepOp p c (1 / lam) u W x = Z x)
    (hW2 : ContDiff ℝ 2 W)
    (hWnonneg : ∀ x, 0 ≤ W x)
    (haux : PaperLowerRawStepApproxOperatorData
      p c lam κ κtilde D u W) :
    ∀ x, lowerBarrierRaw κ κtilde D x ≤ W x := by
  have hDpos : 0 < D := D_pos_of_paperDMin_lt hcond hD
  have hgap : 0 < κtilde - κ := sub_pos.mpr hcond.hgap
  have hf2 : ContDiff ℝ 2
      (fun x => lowerBarrierRaw κ κtilde D x - W x) := by
    have hraw : ContDiff ℝ 2 (lowerBarrierRaw κ κtilde D) := by
      unfold lowerBarrierRaw
      fun_prop
    exact hraw.sub hW2
  have hExpM :
      Real.exp (-κ * lowerBarrierXPlus κ κtilde D) ≤ M :=
    lowerBarrierExpXPlus_le_one_of_one_le_D hcond.hκ0 hgap
      hD_ge_one hcond.hM
  have hfbound : ∀ x,
      lowerBarrierRaw κ κtilde D x - W x ≤ M := by
    intro x
    have hraw_plateau :
        lowerBarrierRaw κ κtilde D x ≤
          lowerBarrierPlateau κ κtilde D x :=
      lowerBarrierRaw_le_plateau hcond.hκ0 hgap hDpos x
    have hplat_exp :
        lowerBarrierPlateau κ κtilde D x ≤
          Real.exp (-κ * lowerBarrierXPlus κ κtilde D) :=
      lowerBarrierPlateau_le_exp_xplus hcond.hκ0.le hDpos.le x
    linarith [hWnonneg x]
  have hsub : ∀ x,
      0 < lowerBarrierRaw κ κtilde D x - W x →
      0 ≤ paperWaveOperator p c u (lowerBarrierRaw κ κtilde D) x := by
    intro x hx
    have hrawpos : 0 < lowerBarrierRaw κ κtilde D x := by
      linarith [hWnonneg x]
    have hregion : x ∈ Set.Ioi (lowerBarrierXMinus κ κtilde D) :=
      lowerBarrierXMinus_lt_of_lowerBarrierRaw_pos hgap hDpos hrawpos
    exact PaperLemma_4_2_paperWaveOperator_of_conditions
      hcond hD hD_ge_one u hu.bare.1 x hregion
  exact paperImplicitStep_ge_barrier_of_quasiMonotone_tailfree
    (p := p) (c := c) (lam := lam)
    (Cmono := haux.Cmono) (E := haux.E) (Q := M)
    (u := u) (Z := Z) (W := W)
    (A := lowerBarrierRaw κ κtilde D)
    hlam haux.small haux.E_nonneg hstep hprev hf2 hfbound hsub
    haux.op_approx

section AxiomAudit

#print axioms lowerBarrierXMinus_lt_of_lowerBarrierRaw_pos
#print axioms paperImplicitStep_ge_lowerBarrierRaw_tailfree

end AxiomAudit

end ShenWork.Paper1
