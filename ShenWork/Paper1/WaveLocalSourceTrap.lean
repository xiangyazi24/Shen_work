/-
  Tail-free trap comparison for the compact-open whole-line Green step.

  The source Schauder set has no shared left-tail modulus.  Consequently clamp
  inactivity must be proved without first manufacturing endpoint limits.  The
  quadratic-penalty maximum principle gives exactly the small derivative errors
  needed by the truncated operator.
-/
import ShenWork.Paper1.WaveApproxMaximum
import ShenWork.Paper1.WaveLocalSourceSchauder

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-- Tail-free lower comparison for the spatially truncated paper step.  The
only coefficient retained explicitly is the drift multiplying `W'`; its
absolute bound makes the endpoint case `m = 1` harmless. -/
theorem paperImplicitStep_truncated_ge_zero_tailfree
    {p : CMParams} {c lam M κ A C : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hstep :
      ∀ x, paperImplicitStepOp_truncated p c (1 / lam) M κ u W x = Z x)
    (hW2 : ContDiff ℝ 2 W)
    (hWbound : ∀ x, |W x| ≤ A)
    (hZnonneg : ∀ x, 0 ≤ Z x)
    (hcoeff : ∀ x,
      |(-p.χ * p.m) * (paperWeightedClamp κ M W x) ^ (p.m - 1) *
          deriv (frozenElliptic p u) x| ≤ C) :
    ∀ x, 0 ≤ W x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₁, hx₁⟩ := hcon
  have hfpos : 0 < -W x₁ := by linarith
  let K : ℝ := 1 + |c| + C
  have hK : 0 < K := by
    dsimp [K]
    positivity
  let eta : ℝ := lam * (-W x₁) / (4 * K)
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  have hf2 : ContDiff ℝ 2 (fun x => -W x) := hW2.neg
  have hfbound : ∀ x, |(fun y => -W y) x| ≤ A := by
    intro x
    simpa only [abs_neg] using hWbound x
  obtain ⟨x₀, hvalue, hfirst, hsecond⟩ :=
    exists_approx_positive_max_deriv_data
      (f := fun x => -W x) (A := A) (eta := eta) (x₁ := x₁)
      hf2 hfbound hfpos heta
  have hW₀neg : W x₀ < 0 := by
    have : -W x₁ / 2 < -W x₀ := hvalue
    nlinarith
  have hW₀strong : W x₀ < W x₁ / 2 := by
    have : -W x₁ / 2 < -W x₀ := hvalue
    linarith
  have hWdiff : Differentiable ℝ W := hW2.differentiable (by norm_num)
  have hfirst_eq :
      deriv (fun x => -W x) x₀ = -deriv W x₀ := by
    exact (hWdiff x₀).hasDerivAt.neg.deriv
  have hWfirst : |deriv W x₀| < eta := by
    rw [hfirst_eq, abs_neg] at hfirst
    exact hfirst
  have hsecond_eq :
      deriv (deriv (fun x => -W x)) x₀ =
        -iteratedDeriv 2 W x₀ := by
    calc
      deriv (deriv (fun x => -W x)) x₀ =
          iteratedDeriv 2 (fun x => -W x) x₀ := by
            simp [iteratedDeriv_succ, iteratedDeriv_zero]
      _ = -iteratedDeriv 2 W x₀ := iteratedDeriv_fun_neg 2 W x₀
  have hWsecond : -eta < iteratedDeriv 2 W x₀ := by
    rw [hsecond_eq] at hsecond
    linarith
  have hclamp : paperWeightedClamp κ M W x₀ = 0 :=
    paperWeightedClamp_eq_zero_of_nonpos
      (κ := κ) (M := M) (W := W) hM hW₀neg.le
  let a₀ : ℝ :=
    (-p.χ * p.m) * (paperWeightedClamp κ M W x₀) ^ (p.m - 1) *
      deriv (frozenElliptic p u) x₀
  have ha₀ : |a₀| ≤ C := hcoeff x₀
  have hNL :
      paperStepTruncatedNonlinearity p c M κ u W x₀ =
        a₀ * deriv W x₀ := by
    unfold paperStepTruncatedNonlinearity
    dsimp only
    dsimp [a₀]
    rw [hclamp]
    ring
  have hNLlower : -C * eta ≤
      paperStepTruncatedNonlinearity p c M κ u W x₀ := by
    rw [hNL]
    have habs : |a₀ * deriv W x₀| ≤ C * eta := by
      rw [abs_mul]
      exact mul_le_mul ha₀ hWfirst.le (abs_nonneg _) hC
    simpa only [neg_mul] using neg_le_of_abs_le habs
  have hcWlower : -|c| * eta ≤ c * deriv W x₀ := by
    have habs : |c * deriv W x₀| ≤ |c| * eta := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hWfirst.le (abs_nonneg c)
    simpa only [neg_mul] using neg_le_of_abs_le habs
  have hAlower :
      -(K * eta) < paperWaveOperator_truncated p c M κ u W x₀ := by
    unfold paperWaveOperator_truncated
    dsimp [K]
    nlinarith
  have hAupper :
      paperWaveOperator_truncated p c M κ u W x₀ ≤ lam * W x₀ := by
    have hraw := hstep x₀
    rw [paperImplicitStepOp_truncated_apply] at hraw
    have hdiv :
        (1 / lam) * paperWaveOperator_truncated p c M κ u W x₀ ≤ W x₀ := by
      linarith [hZnonneg x₀]
    have hmul := mul_le_mul_of_nonneg_left hdiv hlam.le
    have hlamne : lam ≠ 0 := ne_of_gt hlam
    calc
      paperWaveOperator_truncated p c M κ u W x₀ =
          lam * ((1 / lam) *
            paperWaveOperator_truncated p c M κ u W x₀) := by
              field_simp [hlamne]
      _ ≤ lam * W x₀ := hmul
  have hKeta : K * eta = lam * (-W x₁) / 4 := by
    dsimp [K, eta]
    field_simp [ne_of_gt hK]
  rw [hKeta] at hAlower
  nlinarith [mul_pos hlam hfpos]

/-- A fixed point supplied by the compact-open source Schauder theorem is
nonnegative.  This is the concrete tail-free replacement for the lower half of
`paperFixedSource_truncation_inactive_direct_of_trap`. -/
theorem paperFixedSource_truncated_ge_zero_local_of_trap
    {p : CMParams} {c lam M κ β B H : ℝ} {u Z R : ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 < M) (hB : 0 ≤ B)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hR : PaperLocalHolderSourceBox κ M β B H R)
    (hRfix : paperFixedSourceMap p c lam M κ u Z R = R)
    (hZnonneg : ∀ x, 0 ≤ Z x) :
    ∀ x, 0 ≤ greenConv c lam R x := by
  have hR_const : ∀ y, |R y| ≤ B * M := by
    intro y
    calc
      |R y| ≤ B * upperBarrier κ M y := hR.bound y
      _ ≤ B * M :=
        mul_le_mul_of_nonneg_left (upperBarrier_le_M κ M y) hB
  have hHi : ∀ t,
      IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi t) :=
    fun t => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) hR.cont hR_const t
  have hLo : ∀ t,
      IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic t) :=
    fun t => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) hR.cont hR_const t
  have hstep : ∀ x,
      paperImplicitStepOp_truncated p c (1 / lam) M κ u
          (greenConv c lam R) x = Z x :=
    paperImplicitStepOp_truncated_of_green_fixed_source
      (c := c) (lam := lam) (p := p) (M := M) (κ := κ)
      (u := u) (Z := Z) (R := R) hlam hRfix.symm hR.cont hHi hLo
  have hW2 : ContDiff ℝ 2 (greenConv c lam R) :=
    greenConv_contDiff_two hR.cont hHi hLo
  have hWbound : ∀ x, |greenConv c lam R x| ≤ lam⁻¹ * (B * M) :=
    greenConv_abs_le_of_bound (c := c) (lam := lam)
      hlam hR.cont hR_const
  let C : ℝ := |(-p.χ * p.m)| * M ^ (p.m - 1) * M ^ p.γ
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hcoeff : ∀ x,
      |(-p.χ * p.m) *
          (paperWeightedClamp κ M (greenConv c lam R) x) ^ (p.m - 1) *
            deriv (frozenElliptic p u) x| ≤ C := by
    intro x
    have hpow :
        |(paperWeightedClamp κ M (greenConv c lam R) x) ^ (p.m - 1)| ≤
          M ^ (p.m - 1) :=
      paperWeightedClamp_rpow_abs_le_M hM.le (sub_nonneg.mpr p.hm) x
    have hVd : |deriv (frozenElliptic p u) x| ≤ M ^ p.γ :=
      (frozenElliptic_deriv_abs_le p hu.trap.cunif_bdd hu.nonneg x).trans
        (frozenElliptic_le_rpow_of_inWaveTrapSet p hM hu.trap x)
    dsimp [C]
    rw [abs_mul, abs_mul]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hpow (abs_nonneg (-p.χ * p.m)))
      hVd (abs_nonneg _) (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hM.le _))
  exact paperImplicitStep_truncated_ge_zero_tailfree
    (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
    (A := lam⁻¹ * (B * M)) (C := C) (u := u) (Z := Z)
    (W := greenConv c lam R)
    hlam hM.le hC hstep hW2 hWbound hZnonneg hcoeff

section AxiomAudit

#print axioms paperImplicitStep_truncated_ge_zero_tailfree
#print axioms paperFixedSource_truncated_ge_zero_local_of_trap

end AxiomAudit

end ShenWork.Paper1
