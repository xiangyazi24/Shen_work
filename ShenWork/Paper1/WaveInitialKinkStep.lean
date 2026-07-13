import ShenWork.Paper1.WaveApproxMaximumAway
import ShenWork.Paper1.WavePinnedStepRest
import ShenWork.Paper1.WavePaperTermConvergence

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-- Pointwise `C¹` source regularity.  This is the local counterpart of
`paperStepSource_contDiff_one_of_nonzero`; it allows one nonsmooth point in the
old iterate. -/
theorem paperStepSource_differentiableAt_of_nonzero
    (p : CMParams) (c lam : ℝ) {u Z W : ℝ → ℝ} {x : ℝ}
    (hZ : DifferentiableAt ℝ Z x)
    (hW : ContDiff ℝ 2 W)
    (hWnz : W x ≠ 0)
    (hV : ContDiff ℝ 2 (frozenElliptic p u)) :
    DifferentiableAt ℝ (paperStepSource p c lam u Z W) x := by
  have hW0 : DifferentiableAt ℝ W x :=
    hW.differentiable (by norm_num) x
  have hWd : DifferentiableAt ℝ (deriv W) x :=
    hW.differentiable_deriv_two x
  have hV0 : DifferentiableAt ℝ (frozenElliptic p u) x :=
    hV.differentiable (by norm_num) x
  have hVd : DifferentiableAt ℝ (deriv (frozenElliptic p u)) x :=
    hV.differentiable_deriv_two x
  have hWm1 : DifferentiableAt ℝ (fun y => W y ^ (p.m - 1)) x :=
    hW0.rpow_const (Or.inl hWnz)
  have hWa : DifferentiableAt ℝ (fun y => W y ^ p.α) x :=
    hW0.rpow_const (Or.inl hWnz)
  have hWmg : DifferentiableAt ℝ
      (fun y => W y ^ (p.m + p.γ - 1)) x :=
    hW0.rpow_const (Or.inl hWnz)
  unfold paperStepSource paperStepNonlinearity
  dsimp only
  fun_prop (disch := assumption)

/-- With unit amplitude the only nonsmooth point of the upper barrier is the
origin. -/
theorem upperBarrier_one_contDiffAt_one_of_ne_zero
    {κ x : ℝ} (hκ : 0 < κ) (hx : x ≠ 0) :
    ContDiffAt ℝ 1 (upperBarrier κ 1) x := by
  have hne : Real.exp (-κ * x) ≠ (1 : ℝ) := by
    intro heq
    have hz : -κ * x = 0 := by
      apply Real.exp_injective
      simpa using heq
    apply hx
    nlinarith
  exact (upperBarrier_contDiffAt_two_of_ne_interface hne).of_le (by norm_num)

/-- Local third-order derivative data for the first Green step.  The old
upper barrier is only needed to be smooth at the displayed point. -/
theorem PaperLocalFixedStepData.routeA_deriv_data_of_old_differentiableAt
    {p : CMParams} {c lam M κ Λ B : ℝ} {u Z : ℝ → ℝ} {x : ℝ}
    (hlam : 0 < lam)
    (hu : InMonotoneWaveTrapSet κ M u)
    (d : PaperLocalFixedStepData p c lam M κ Λ B u Z)
    (hZ : DifferentiableAt ℝ Z x)
    (hWpos : ∀ y, 0 < d.fixed.W y) :
    HasDerivAt d.fixed.W (deriv d.fixed.W x) x ∧
      HasDerivAt (deriv d.fixed.W) (deriv (deriv d.fixed.W) x) x ∧
      HasDerivAt (iteratedDeriv 2 d.fixed.W)
        (deriv (deriv (deriv d.fixed.W)) x) x := by
  have hW2 : ContDiff ℝ 2 d.fixed.W := d.contDiff_two hlam
  have hV2 : ContDiff ℝ 2 (frozenElliptic p u) :=
    frozenElliptic_contDiff_two_of_inWaveTrapSet p hu.trap
  have hRdiff : DifferentiableAt ℝ d.fixed.R x := by
    rw [d.fixed.source_eq]
    exact paperStepSource_differentiableAt_of_nonzero
      p c lam hZ hW2 (ne_of_gt (hWpos x)) hV2
  have hW0 : HasDerivAt d.fixed.W (deriv d.fixed.W x) x :=
    (hW2.differentiable (by norm_num) x).hasDerivAt
  have hW1 : HasDerivAt (deriv d.fixed.W)
      (deriv (deriv d.fixed.W) x) x :=
    (hW2.differentiable_deriv_two x).hasDerivAt
  let ha := paperStepAnalytic_of_core
    (c := c) (lam := lam) hlam d.fixed.analyticCore
  have hiterEq : (fun y => iteratedDeriv 2 d.fixed.W y) =
      fun y => -d.fixed.R y - c * deriv d.fixed.W y + lam * d.fixed.W y := by
    funext y
    exact paperStep_iteratedDeriv_two_eq
      (c := c) (lam := lam) hlam ha y
  have hiterDiff : DifferentiableAt ℝ
      (fun y => iteratedDeriv 2 d.fixed.W y) x := by
    rw [hiterEq]
    exact (hRdiff.neg.sub
      ((hW2.differentiable_deriv_two x).const_mul c)).add
        ((hW2.differentiable (by norm_num) x).const_mul lam)
  have hW2has : HasDerivAt (iteratedDeriv 2 d.fixed.W)
      (deriv (deriv (deriv d.fixed.W)) x) x := by
    have hhas := hiterDiff.hasDerivAt
    have heq : (fun y => iteratedDeriv 2 d.fixed.W y) =
        deriv (deriv d.fixed.W) := by
      funext y
      simp [iteratedDeriv_succ, iteratedDeriv_zero]
    simpa [heq] using hhas
  exact ⟨hW0, hW1, hW2has⟩

/-- Tail-free differentiated maximum principle when the step is third-order
regular away from one point. -/
theorem paperStep_deriv_nonpos_of_quasiMonotone_tailfree_away
    {p : CMParams} {c lam Cmono E Q a : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam)
    (hsmall : (1 / lam) * Cmono < 1)
    (hE : 0 ≤ E)
    (hstep_deriv : ∀ x, x ≠ a →
      deriv W x - (1 / lam) *
          deriv (fun y => paperWaveOperator p c u W y) x = deriv Z x)
    (hZderiv : ∀ x, deriv Z x ≤ 0)
    (hq1 : ContDiff ℝ 1 (fun x => deriv W x))
    (hq2away : ∀ x, x ≠ a →
      DifferentiableAt ℝ (deriv (fun y => deriv W y)) x)
    (hqbound : ∀ x, |deriv W x| ≤ Q)
    (hmono_approx : ∀ eta, 0 < eta → ∀ x₀, x₀ ≠ a →
      0 < deriv W x₀ →
      |deriv (deriv W) x₀| < eta →
      deriv (deriv (deriv W)) x₀ < eta →
      deriv (fun x => paperWaveOperator p c u W x) x₀ ≤
        Cmono * deriv W x₀ + E * eta) :
    ∀ x, deriv W x ≤ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₁, hx₁⟩ := hcon
  have hClam : Cmono < lam := by
    have hmul := mul_lt_mul_of_pos_left hsmall hlam
    have hlamne : lam ≠ 0 := ne_of_gt hlam
    field_simp [hlamne] at hmul
    linarith
  let eta : ℝ := (lam - Cmono) * deriv W x₁ / (4 * (E + 1))
  have heta : 0 < eta := by
    dsimp [eta]
    exact div_pos (mul_pos (sub_pos.mpr hClam) hx₁)
      (mul_pos (by norm_num) (by linarith))
  obtain ⟨x₀, hx₀ne, hqvalue, hqSlope, hqSecond⟩ :=
    exists_approx_positive_max_deriv_data_away
      (f := fun x => deriv W x) (A := Q) (eta := eta)
      (x₁ := x₁) (a := a) hq1 hq2away hqbound hx₁ heta
  have hqpos : 0 < deriv W x₀ := by linarith
  have hA := hmono_approx eta heta x₀ hx₀ne hqpos hqSlope hqSecond
  have hstep₀ := hstep_deriv x₀ hx₀ne
  have hA_lower : lam * deriv W x₀ ≤
      deriv (fun x => paperWaveOperator p c u W x) x₀ := by
    have hdiv : deriv W x₀ ≤
        (1 / lam) * deriv (fun x => paperWaveOperator p c u W x) x₀ := by
      linarith [hZderiv x₀]
    have hmul := mul_le_mul_of_nonneg_left hdiv hlam.le
    have hlamne : lam ≠ 0 := ne_of_gt hlam
    calc
      lam * deriv W x₀ ≤ lam * ((1 / lam) *
          deriv (fun x => paperWaveOperator p c u W x) x₀) := hmul
      _ = deriv (fun x => paperWaveOperator p c u W x) x₀ := by
        field_simp [hlamne]
  have hEeta : E * eta < (lam - Cmono) * deriv W x₁ / 4 := by
    dsimp [eta]
    have hE1 : E < E + 1 := by linarith
    have hbase : 0 < (lam - Cmono) * deriv W x₁ :=
      mul_pos (sub_pos.mpr hClam) hx₁
    have hden : 0 < 4 * (E + 1) :=
      mul_pos (by norm_num) (by linarith)
    have hscaled : E * ((lam - Cmono) * deriv W x₁) <
        (E + 1) * ((lam - Cmono) * deriv W x₁) :=
      mul_lt_mul_of_pos_right hE1 hbase
    calc
      E * ((lam - Cmono) * deriv W x₁ / (4 * (E + 1))) =
          (E * ((lam - Cmono) * deriv W x₁)) / (4 * (E + 1)) := by ring
      _ < ((E + 1) * ((lam - Cmono) * deriv W x₁)) /
          (4 * (E + 1)) := (div_lt_div_iff_of_pos_right hden).2 hscaled
      _ = (lam - Cmono) * deriv W x₁ / 4 := by
        field_simp [ne_of_gt (show 0 < E + 1 by linarith)]
  have hqscaled :
      (lam - Cmono) * (deriv W x₁ / 2) <
        (lam - Cmono) * deriv W x₀ :=
    mul_lt_mul_of_pos_left hqvalue (sub_pos.mpr hClam)
  have hgap_le : (lam - Cmono) * deriv W x₀ ≤ E * eta := by
    linarith [hA_lower, hA]
  have hbase : 0 < (lam - Cmono) * deriv W x₁ :=
    mul_pos (sub_pos.mpr hClam) hx₁
  have hquarter :
      (lam - Cmono) * deriv W x₁ / 4 <
        (lam - Cmono) * (deriv W x₁ / 2) := by
    calc
      (lam - Cmono) * deriv W x₁ / 4 <
          (lam - Cmono) * deriv W x₁ / 2 := by linarith
      _ = (lam - Cmono) * (deriv W x₁ / 2) := by ring
  exact (not_lt_of_ge hgap_le)
    (lt_trans (lt_trans hEeta hquarter) hqscaled)

/-- The first local Green step from the unit upper barrier is antitone.  The
proof uses Route A at contacts away from the sole barrier kink `x = 0`. -/
theorem PaperLocalFixedStepData.antitone_of_upperBarrier_one
    {p : CMParams} {c lam κ Λ B Cmono : ℝ} {u : ℝ → ℝ}
    (hlam : 0 < lam) (hκ : 0 < κ)
    (hu : InMonotoneWaveTrapSet κ 1 u)
    (hbox : PaperFrozenEllipticSourceBox p κ 1)
    (hχ : p.χ ≤ 0)
    (hsmall : (1 / lam) * Cmono < 1)
    (hCmono : paperCmono p (-p.χ) 1 (1 ^ p.γ) (2 * 1 ^ p.γ) ≤ Cmono)
    (d : PaperLocalFixedStepData p c lam 1 κ Λ B u (upperBarrier κ 1)) :
    Antitone d.fixed.W := by
  let hs : PaperStepRouteAStructuralData
      p c lam Cmono u (upperBarrier κ 1) d.fixed.W :=
    paperStepRouteAStructuralData_of_frozenSourceBox
      hu hbox hχ hsmall hCmono
  let E : ℝ := 1 + |c| + hs.a * p.m * hs.M ^ (p.m - 1) * hs.BV
  have ha0 : 0 ≤ hs.a := by rw [hs.ha]; linarith [hs.hχ]
  have hBV0 : 0 ≤ hs.BV :=
    le_trans (abs_nonneg (frozenElliptic p u 0)) (hs.V_bound 0)
  have hE : 0 ≤ E := by
    dsimp [E]
    have hm0 : 0 ≤ p.m := by linarith [p.hm]
    have hM0 : 0 ≤ hs.M := by
      change 0 ≤ (1 : ℝ)
      norm_num
    have hpow0 : 0 ≤ hs.M ^ (p.m - 1) := Real.rpow_nonneg hM0 _
    have hterm : 0 ≤ hs.a * p.m * hs.M ^ (p.m - 1) * hs.BV :=
      mul_nonneg (mul_nonneg (mul_nonneg ha0 hm0) hpow0) hBV0
    exact add_nonneg (add_nonneg zero_le_one (abs_nonneg c)) hterm
  have hW2 : ContDiff ℝ 2 d.fixed.W := d.contDiff_two hlam
  have hWpos : ∀ x, 0 < d.fixed.W x :=
    d.strict_pos_of_old_pos hlam (upperBarrier_pos one_pos)
  have hq1 : ContDiff ℝ 1 (fun x => deriv d.fixed.W x) := by
    have hW2' : ContDiff ℝ ((1 : ℕ∞) + 1) d.fixed.W := by
      simpa using hW2
    exact (contDiff_succ_iff_deriv.mp hW2').2.2
  have hq2away : ∀ x, x ≠ 0 →
      DifferentiableAt ℝ (deriv (fun y => deriv d.fixed.W y)) x := by
    intro x hx
    have hZ1 := (upperBarrier_one_contDiffAt_one_of_ne_zero hκ hx).differentiableAt_one
    have hdata := d.routeA_deriv_data_of_old_differentiableAt
      hlam hu hZ1 hWpos
    have heq : (fun y => iteratedDeriv 2 d.fixed.W y) =
        deriv (fun y => deriv d.fixed.W y) := by
      funext y
      simp [iteratedDeriv_succ, iteratedDeriv_zero]
    rw [← heq]
    exact hdata.2.2.differentiableAt
  have hstepDeriv : ∀ x, x ≠ 0 →
      deriv d.fixed.W x - (1 / lam) *
          deriv (fun y => paperWaveOperator p c u d.fixed.W y) x =
        deriv (upperBarrier κ 1) x := by
    intro x hx
    have hZat := upperBarrier_one_contDiffAt_one_of_ne_zero hκ hx
    have hdata := d.routeA_deriv_data_of_old_differentiableAt
      hlam hu hZat.differentiableAt_one hWpos
    have hV0 : HasDerivAt (frozenElliptic p u)
        (deriv (frozenElliptic p u) x) x :=
      (hs.V_reg.differentiable (by norm_num) x).hasDerivAt
    have hV1 : HasDerivAt (deriv (frozenElliptic p u))
        (deriv (deriv (frozenElliptic p u)) x) x :=
      (hs.V_reg.differentiable_deriv_two x).hasDerivAt
    have hwave := paperWaveOperator_hasDerivAt_routeA
      (p := p) (c := c) (a := hs.a) (u := u) (W := d.fixed.W) (x₀ := x)
      hs.ha hdata.1 hdata.2.1 hdata.2.2 hV0 hV1 (hWpos x)
    have hwave' : HasDerivAt
        (fun y => paperWaveOperator p c u d.fixed.W y)
        (deriv (fun y => paperWaveOperator p c u d.fixed.W y) x) x := by
      convert hwave using 1
      exact hwave.deriv
    have hleft : HasDerivAt
        (paperImplicitStepOp p c (1 / lam) u d.fixed.W)
        (deriv d.fixed.W x - (1 / lam) *
          deriv (fun y => paperWaveOperator p c u d.fixed.W y) x) x := by
      simpa [paperImplicitStepOp] using
        hdata.1.sub (hwave'.const_mul (1 / lam))
    calc
      deriv d.fixed.W x - (1 / lam) *
          deriv (fun y => paperWaveOperator p c u d.fixed.W y) x =
          deriv (paperImplicitStepOp p c (1 / lam) u d.fixed.W) x :=
        hleft.deriv.symm
      _ = deriv (upperBarrier κ 1) x := by
        congr 1
        funext y
        exact d.step_op hlam y
  have hmono : ∀ eta, 0 < eta → ∀ x₀, x₀ ≠ 0 →
      0 < deriv d.fixed.W x₀ →
      |deriv (deriv d.fixed.W) x₀| < eta →
      deriv (deriv (deriv d.fixed.W)) x₀ < eta →
      deriv (fun x => paperWaveOperator p c u d.fixed.W x) x₀ ≤
        Cmono * deriv d.fixed.W x₀ + E * eta := by
    intro eta heta x₀ hx₀ hqpos hqSlope hqSecond
    have hZat := upperBarrier_one_contDiffAt_one_of_ne_zero hκ hx₀
    have hdata := d.routeA_deriv_data_of_old_differentiableAt
      hlam hu hZat.differentiableAt_one hWpos
    exact paperWaveOperator_deriv_at_approx_pos_max_le_of_structural
      (p := p) (c := c) (a := hs.a) (M := hs.M) (BV := hs.BV)
      (BV2 := hs.BV2) (BVd := hs.BV) (Cmono := Cmono) (eta := eta)
      (u := u) (W := d.fixed.W) (x₀ := x₀)
      hs.ha hs.hχ hdata.1 hdata.2.1 hdata.2.2 hs.V_reg
      (fun x => ⟨(d.range x).1,
        (d.range x).2.trans (upperBarrier_le_M κ 1 x)⟩)
      hs.V_deriv_nonpos hs.V_deriv_bound hs.V_bound hs.V2_bound
      hBV0 heta hqpos hqSlope hqSecond hs.Cmono_bound
  have hqnonpos := paperStep_deriv_nonpos_of_quasiMonotone_tailfree_away
    (p := p) (c := c) (lam := lam) (Cmono := Cmono) (E := E)
    (Q := Λ) (a := 0) (u := u) (Z := upperBarrier κ 1)
    (W := d.fixed.W) hlam hsmall hE hstepDeriv
    (fun x => (upperBarrier_antitone hκ.le).deriv_nonpos)
    hq1 hq2away (d.deriv_le hlam) hmono
  exact antitone_of_deriv_nonpos
    (hW2.differentiable (by norm_num)) hqnonpos

section AxiomAudit

#print axioms paperStepSource_differentiableAt_of_nonzero
#print axioms upperBarrier_one_contDiffAt_one_of_ne_zero
#print axioms PaperLocalFixedStepData.routeA_deriv_data_of_old_differentiableAt
#print axioms paperStep_deriv_nonpos_of_quasiMonotone_tailfree_away
#print axioms PaperLocalFixedStepData.antitone_of_upperBarrier_one

end AxiomAudit

end ShenWork.Paper1
