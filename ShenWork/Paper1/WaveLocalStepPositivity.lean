import ShenWork.Paper1.WaveLocalStepConstruction
import ShenWork.Paper1.NoSmallLeftPocket
import ShenWork.Paper1.WaveLemma42Paper

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-- A nonnegative genuine local paper step is strictly positive whenever its
old iterate is.  This is the pointwise strong-minimum argument needed before
bootstrapping through noninteger powers. -/
theorem PaperLocalFixedStepData.strict_pos_of_old_pos
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam)
    (d : PaperLocalFixedStepData p c lam M κ Λ u Z)
    (hZpos : ∀ x, 0 < Z x) :
    ∀ x, 0 < d.fixed.W x := by
  intro x
  have hWnonneg : ∀ y, 0 ≤ d.fixed.W y := fun y => (d.range y).1
  by_contra hnot
  have hWx : d.fixed.W x = 0 :=
    le_antisymm (le_of_not_gt hnot) (hWnonneg x)
  have hminOn : IsMinOn d.fixed.W Set.univ x := by
    intro y _hy
    rw [hWx]
    exact hWnonneg y
  have hmin : IsLocalMin d.fixed.W x :=
    hminOn.isLocalMin Filter.univ_mem
  have hderiv : deriv d.fixed.W x = 0 := hmin.deriv_eq_zero
  have hW2 : ContDiff ℝ 2 d.fixed.W := d.contDiff_two hlam
  have hsecond : 0 ≤ deriv (deriv d.fixed.W) x :=
    deriv_deriv_nonneg_of_isLocalMin
      hW2.continuous.continuousAt hmin hderiv
  have hi2 : iteratedDeriv 2 d.fixed.W x =
      deriv (deriv d.fixed.W) x := by
    simp [iteratedDeriv_succ, iteratedDeriv_zero]
  have hF : paperWaveOperator p c u d.fixed.W x =
      iteratedDeriv 2 d.fixed.W x := by
    unfold paperWaveOperator
    rw [hWx, hderiv]
    ring
  have hstep := d.step_op hlam
  have hrel := paperWaveOperator_eq_of_implicitStep
    p c lam hlam hstep x
  rw [hF, hi2, hWx] at hrel
  nlinarith [hZpos x]

/-- Positive `C²` Green steps bootstrap to `C³` once the old iterate is `C¹`.
The frozen elliptic `C²` input is automatic from trap membership. -/
theorem PaperLocalFixedStepData.contDiff_three_of_old_pos
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam)
    (hu : InMonotoneWaveTrapSet κ M u)
    (d : PaperLocalFixedStepData p c lam M κ Λ u Z)
    (hZ1 : ContDiff ℝ 1 Z)
    (hZpos : ∀ x, 0 < Z x) :
    ContDiff ℝ 3 d.fixed.W := by
  exact paperStep_contDiff_three_of_core_smooth_nonzero
    hlam d.fixed.analyticCore hZ1
      (frozenElliptic_contDiff_two_of_inWaveTrapSet p hu.trap)
      (fun x => ne_of_gt (d.strict_pos_of_old_pos hlam hZpos x))

/-- The paper operator of a positive `C³` profile with a `C²` frozen elliptic
coefficient is differentiable. -/
theorem paperWaveOperator_differentiable_of_pos
    {p : CMParams} {c : ℝ} {u W : ℝ → ℝ}
    (hW3 : ContDiff ℝ 3 W)
    (hV2 : ContDiff ℝ 2 (frozenElliptic p u))
    (hWpos : ∀ x, 0 < W x) :
    Differentiable ℝ (fun x => paperWaveOperator p c u W x) := by
  intro x
  have hW0 : DifferentiableAt ℝ W x :=
    (hW3.differentiable (by norm_num)) x
  have hW1 : DifferentiableAt ℝ (deriv W) x := by
    simpa [iteratedDeriv_one] using
      (hW3.differentiable_iteratedDeriv 1 (by norm_num) x)
  have hW2 : DifferentiableAt ℝ (iteratedDeriv 2 W) x :=
    hW3.differentiable_iteratedDeriv 2 (by norm_num) x
  have hV0 : DifferentiableAt ℝ (frozenElliptic p u) x :=
    (hV2.differentiable (by norm_num)) x
  have hV1 : DifferentiableAt ℝ (deriv (frozenElliptic p u)) x := by
    simpa [iteratedDeriv_one] using
      (hV2.differentiable_iteratedDeriv 1 (by norm_num) x)
  have hpow_m1 : DifferentiableAt ℝ (fun y => (W y) ^ (p.m - 1)) x :=
    hW0.rpow_const (Or.inl (ne_of_gt (hWpos x)))
  have hpow_a : DifferentiableAt ℝ (fun y => (W y) ^ p.α) x :=
    hW0.rpow_const (Or.inl (ne_of_gt (hWpos x)))
  have hpow_mg1 :
      DifferentiableAt ℝ (fun y => (W y) ^ (p.m + p.γ - 1)) x :=
    hW0.rpow_const (Or.inl (ne_of_gt (hWpos x)))
  unfold paperWaveOperator
  dsimp only
  fun_prop

/-- Route A closes antitonicity for every genuine local step whose old iterate
is positive and `C¹`.  In particular, every successor after the kinked initial
upper barrier is internal; only the initial kink case remains separate. -/
theorem PaperLocalFixedStepData.antitone_of_old_pos_contDiff_one
    {p : CMParams} {c lam M κ Λ Cmono : ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hbox : PaperFrozenEllipticSourceBox p κ M)
    (hχ : p.χ ≤ 0)
    (hsmall : (1 / lam) * Cmono < 1)
    (hCmono :
      paperCmono p (-p.χ) M (M ^ p.γ) (2 * M ^ p.γ) ≤ Cmono)
    (d : PaperLocalFixedStepData p c lam M κ Λ u Z)
    (hZ1 : ContDiff ℝ 1 Z)
    (hZpos : ∀ x, 0 < Z x)
    (hZanti : Antitone Z) :
    Antitone d.fixed.W := by
  have hW3 : ContDiff ℝ 3 d.fixed.W :=
    d.contDiff_three_of_old_pos hlam hu hZ1 hZpos
  have hWpos : ∀ x, 0 < d.fixed.W x :=
    d.strict_pos_of_old_pos hlam hZpos
  have hV2 : ContDiff ℝ 2 (frozenElliptic p u) :=
    frozenElliptic_contDiff_two_of_inWaveTrapSet p hu.trap
  have hwave : Differentiable ℝ
      (fun x => paperWaveOperator p c u d.fixed.W x) :=
    paperWaveOperator_differentiable_of_pos hW3 hV2 hWpos
  have hWrange : ∀ x, d.fixed.W x ∈ Set.Icc (0 : ℝ) M := by
    intro x
    exact ⟨(d.range x).1,
      (d.range x).2.trans (upperBarrier_le_M κ M x)⟩
  let hs : PaperStepRouteAStructuralData
      p c lam Cmono u Z d.fixed.W :=
    paperStepRouteAStructuralData_of_frozenSourceBox
      hu hbox hχ hsmall hCmono
  exact paperStep_antitone_by_routeA_of_structuralData_tailfree
    (p := p) (c := c) (lam := lam) (Cmono := Cmono) (Q := Λ)
    (u := u) (Z := Z) (W := d.fixed.W)
    hlam hs hW3 hwave hWrange (d.step_op hlam)
      (fun x => hZanti.deriv_nonpos) (d.deriv_le hlam)

section AxiomAudit

#print axioms PaperLocalFixedStepData.strict_pos_of_old_pos
#print axioms PaperLocalFixedStepData.contDiff_three_of_old_pos
#print axioms paperWaveOperator_differentiable_of_pos
#print axioms PaperLocalFixedStepData.antitone_of_old_pos_contDiff_one

end AxiomAudit

end ShenWork.Paper1
