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

/-- Tail-free upper comparison against the kinked exponential barrier.  The
quadratic-penalized contact cannot occur at the kink: `W - eps*x²` is
differentiable, so the same one-sided corner argument used for exact contacts
applies. -/
theorem paperImplicitStep_truncated_le_upperBarrier_tailfree
    {p : CMParams} {c lam M κ A C : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam) (hκ : 0 < κ) (hM : 0 < M)
    (hC : 0 ≤ C)
    (hstep :
      ∀ x, paperImplicitStepOp_truncated p c (1 / lam) M κ u W x = Z x)
    (hW2 : ContDiff ℝ 2 W)
    (hWbound : ∀ x, |W x| ≤ A)
    (hZupper : ∀ x, Z x ≤ upperBarrier κ M x)
    (hsuper : ∀ x,
      paperWaveOperator p c u (upperBarrier κ M) x ≤ 0)
    (hcoeff : ∀ x,
      |(-p.χ * p.m) * (upperBarrier κ M x) ^ (p.m - 1) *
          deriv (frozenElliptic p u) x| ≤ C) :
    ∀ x, W x ≤ upperBarrier κ M x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₁, hx₁⟩ := hcon
  let φ : ℝ → ℝ := fun x => W x - upperBarrier κ M x
  have hφpos : 0 < φ x₁ := by
    dsimp [φ]
    linarith
  have hφcont : Continuous φ := by
    dsimp [φ]
    exact hW2.continuous.sub (upperBarrier_continuous κ M)
  have hφbound : ∀ x, |φ x| ≤ A + M := by
    intro x
    have hbar0 : 0 ≤ upperBarrier κ M x := upperBarrier_nonneg hM.le x
    have hbarM : upperBarrier κ M x ≤ M := upperBarrier_le_M κ M x
    dsimp [φ]
    calc
      |W x - upperBarrier κ M x| ≤ |W x| + |upperBarrier κ M x| :=
        abs_sub _ _
      _ ≤ A + M := by
        rw [abs_of_nonneg hbar0]
        exact add_le_add (hWbound x) hbarM
  let K : ℝ := 1 + |c| + C
  have hK : 0 < K := by
    dsimp [K]
    positivity
  let eta : ℝ := lam * φ x₁ / (4 * K)
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  obtain ⟨eps, x₀, heps, hmax, hvalue, hpenalty, hpenalty2⟩ :=
    exists_penalized_max_small_quadratic_errors
      (f := φ) (A := A + M) (eta := eta) (x₁ := x₁)
      hφcont hφbound hφpos heta
  let Wε : ℝ → ℝ := fun x => W x - eps * x ^ 2
  have hmax' :
      IsMaxOn (fun x => Wε x - upperBarrier κ M x) Set.univ x₀ := by
    convert hmax using 1
    funext x
    dsimp [φ, Wε]
    ring
  have hloc : IsLocalMax (fun x => Wε x - upperBarrier κ M x) x₀ :=
    hmax'.isLocalMax Filter.univ_mem
  have hpen2 : ContDiff ℝ 2 (fun x : ℝ => eps * x ^ 2) := by fun_prop
  have hWε2 : ContDiff ℝ 2 Wε := by
    dsimp [Wε]
    exact hW2.sub hpen2
  have hWεdiff : Differentiable ℝ Wε := hWε2.differentiable (by norm_num)
  have hne : Real.exp (-κ * x₀) ≠ M :=
    maxSub_upperBarrier_ne_interface hκ hM (hWεdiff x₀) hloc
  have hB2 : ContDiffAt ℝ 2 (upperBarrier κ M) x₀ :=
    upperBarrier_contDiffAt_two_of_ne_interface hne
  have hderiv2raw :
      iteratedDeriv 2 Wε x₀ ≤
        iteratedDeriv 2 (upperBarrier κ M) x₀ :=
    iteratedDeriv2_le_of_isLocalMax_sub hWε2.contDiffAt hB2 hloc
  have hpen2eq :
      iteratedDeriv 2 (fun x : ℝ => eps * x ^ 2) x₀ = 2 * eps := by
    simp [iteratedDeriv_succ, iteratedDeriv_zero]
    ring
  have hWε2eq :
      iteratedDeriv 2 Wε x₀ = iteratedDeriv 2 W x₀ - 2 * eps := by
    dsimp [Wε]
    rw [iteratedDeriv_fun_sub hW2.contDiffAt hpen2.contDiffAt, hpen2eq]
  have hderiv2 :
      iteratedDeriv 2 W x₀ <
        iteratedDeriv 2 (upperBarrier κ M) x₀ + eta := by
    rw [hWε2eq] at hderiv2raw
    linarith
  have hWdiff : Differentiable ℝ W := hW2.differentiable (by norm_num)
  have hBdiff : DifferentiableAt ℝ (upperBarrier κ M) x₀ :=
    hB2.differentiableAt (by norm_num)
  have hWεhas :
      HasDerivAt Wε (deriv W x₀ - 2 * eps * x₀) x₀ := by
    dsimp [Wε]
    have hsq : HasDerivAt (fun x : ℝ => eps * x ^ 2) (2 * eps * x₀) x₀ := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        ((hasDerivAt_id x₀).pow 2).const_mul eps
    exact (hWdiff x₀).hasDerivAt.sub hsq
  have hBhas :
      HasDerivAt (upperBarrier κ M) (deriv (upperBarrier κ M) x₀) x₀ :=
    hBdiff.hasDerivAt
  have hzero : deriv (fun x => Wε x - upperBarrier κ M x) x₀ = 0 :=
    hloc.deriv_eq_zero
  have hsubderiv :
      deriv (fun x => Wε x - upperBarrier κ M x) x₀ =
        (deriv W x₀ - 2 * eps * x₀) - deriv (upperBarrier κ M) x₀ :=
    (hWεhas.sub hBhas).deriv
  have hderiv1eq :
      deriv W x₀ - deriv (upperBarrier κ M) x₀ = 2 * eps * x₀ := by
    rw [hsubderiv] at hzero
    linarith
  have hderiv1 :
      |deriv W x₀ - deriv (upperBarrier κ M) x₀| < eta := by
    rw [hderiv1eq]
    exact hpenalty
  have hcontact : upperBarrier κ M x₀ < W x₀ := by
    have : φ x₁ / 2 < φ x₀ := hvalue
    dsimp [φ] at this
    linarith [hφpos]
  have hclamp :
      paperWeightedClamp κ M W x₀ = upperBarrier κ M x₀ :=
    paperWeightedClamp_eq_upperBarrier_of_upper_le
      (κ := κ) (M := M) (W := W) hM.le hcontact.le
  let a₀ : ℝ :=
    (-p.χ * p.m) * (upperBarrier κ M x₀) ^ (p.m - 1) *
      deriv (frozenElliptic p u) x₀
  have ha₀ : |a₀| ≤ C := hcoeff x₀
  have hNLdiff :
      paperStepTruncatedNonlinearity p c M κ u W x₀ -
          paperStepNonlinearity p u (upperBarrier κ M) x₀ =
        a₀ * (deriv W x₀ - deriv (upperBarrier κ M) x₀) := by
    unfold paperStepTruncatedNonlinearity paperStepNonlinearity
    dsimp only
    dsimp [a₀]
    rw [hclamp]
    ring
  have hNLerr :
      paperStepTruncatedNonlinearity p c M κ u W x₀ -
          paperStepNonlinearity p u (upperBarrier κ M) x₀ ≤ C * eta := by
    rw [hNLdiff]
    calc
      a₀ * (deriv W x₀ - deriv (upperBarrier κ M) x₀)
          ≤ |a₀ * (deriv W x₀ - deriv (upperBarrier κ M) x₀)| :=
        le_abs_self _
      _ ≤ C * eta := by
        rw [abs_mul]
        exact mul_le_mul ha₀ hderiv1.le (abs_nonneg _) hC
  have hcerr :
      c * deriv W x₀ - c * deriv (upperBarrier κ M) x₀ ≤ |c| * eta := by
    calc
      c * deriv W x₀ - c * deriv (upperBarrier κ M) x₀ =
          c * (deriv W x₀ - deriv (upperBarrier κ M) x₀) := by ring
      _ ≤ |c * (deriv W x₀ - deriv (upperBarrier κ M) x₀)| := le_abs_self _
      _ ≤ |c| * eta := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hderiv1.le (abs_nonneg c)
  have hop_le :
      paperWaveOperator_truncated p c M κ u W x₀ ≤ K * eta := by
    have hsuper₀ := hsuper x₀
    rw [paperWaveOperator_eq_linear_add_paperStepNonlinearity] at hsuper₀
    unfold paperWaveOperator_truncated
    dsimp [K]
    nlinarith
  have hop_ge : lam * φ x₀ ≤
      paperWaveOperator_truncated p c M κ u W x₀ := by
    have hraw := hstep x₀
    rw [paperImplicitStepOp_truncated_apply] at hraw
    have hdiv :
        W x₀ - upperBarrier κ M x₀ ≤
          (1 / lam) * paperWaveOperator_truncated p c M κ u W x₀ := by
      linarith [hZupper x₀]
    have hmul := mul_le_mul_of_nonneg_left hdiv hlam.le
    have hlamne : lam ≠ 0 := ne_of_gt hlam
    dsimp [φ]
    calc
      lam * (W x₀ - upperBarrier κ M x₀) ≤
          lam * ((1 / lam) *
            paperWaveOperator_truncated p c M κ u W x₀) := hmul
      _ = paperWaveOperator_truncated p c M κ u W x₀ := by
        field_simp [hlamne]
  have hKeta : K * eta = lam * φ x₁ / 4 := by
    dsimp [K, eta]
    field_simp [ne_of_gt hK]
  nlinarith [mul_pos hlam hφpos]

/-- Concrete local-source upper comparison. -/
theorem paperFixedSource_truncated_le_upperBarrier_local_of_trap
    {p : CMParams} {c lam M κ β B H : ℝ} {u Z R : ℝ → ℝ}
    (hlam : 0 < lam) (hκ : 0 < κ) (hM : 0 < M) (hB : 0 ≤ B)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hR : PaperLocalHolderSourceBox κ M β B H R)
    (hRfix : paperFixedSourceMap p c lam M κ u Z R = R)
    (hZupper : ∀ x, Z x ≤ upperBarrier κ M x)
    (hsuper : ∀ x,
      paperWaveOperator p c u (upperBarrier κ M) x ≤ 0) :
    ∀ x, greenConv c lam R x ≤ upperBarrier κ M x := by
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
      |(-p.χ * p.m) * (upperBarrier κ M x) ^ (p.m - 1) *
          deriv (frozenElliptic p u) x| ≤ C := by
    intro x
    have hbar0 : 0 ≤ upperBarrier κ M x := upperBarrier_nonneg hM.le x
    have hbarM : upperBarrier κ M x ≤ M := upperBarrier_le_M κ M x
    have hpownn : 0 ≤ (upperBarrier κ M x) ^ (p.m - 1) :=
      Real.rpow_nonneg hbar0 _
    have hpow : |(upperBarrier κ M x) ^ (p.m - 1)| ≤ M ^ (p.m - 1) := by
      rw [abs_of_nonneg hpownn]
      exact Real.rpow_le_rpow hbar0 hbarM (sub_nonneg.mpr p.hm)
    have hVd : |deriv (frozenElliptic p u) x| ≤ M ^ p.γ :=
      (frozenElliptic_deriv_abs_le p hu.trap.cunif_bdd hu.nonneg x).trans
        (frozenElliptic_le_rpow_of_inWaveTrapSet p hM hu.trap x)
    dsimp [C]
    rw [abs_mul, abs_mul]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hpow (abs_nonneg (-p.χ * p.m)))
      hVd (abs_nonneg _) (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hM.le _))
  exact paperImplicitStep_truncated_le_upperBarrier_tailfree
    (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
    (A := lam⁻¹ * (B * M)) (C := C) (u := u) (Z := Z)
    (W := greenConv c lam R)
    hlam hκ hM hC hstep hW2 hWbound hZupper hsuper hcoeff

/-- Both clamps are inactive for the no-tail source fixed point once the
paper-faithful scalar super-barrier conditions are supplied. -/
theorem paperFixedSource_truncation_inactive_local_of_oldData
    {p : CMParams} {c lam M κ β B H : ℝ} {u Z R : ℝ → ℝ}
    (hlam : 0 < lam) (hκ : 0 < κ) (hM : 0 < M) (hB : 0 ≤ B)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hZ : PaperFixedSourceOldData κ M Z)
    (hscalar : PaperUpperBarrierSuperScalarConditions p c κ M)
    (hR : PaperLocalHolderSourceBox κ M β B H R)
    (hRfix : paperFixedSourceMap p c lam M κ u Z R = R) :
    ∀ x, greenConv c lam R x ∈
      Set.Icc (0 : ℝ) (upperBarrier κ M x) := by
  have hnonneg := paperFixedSource_truncated_ge_zero_local_of_trap
    (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
    (u := u) (Z := Z) (R := R)
    hlam hM hB hu hR hRfix hZ.nonneg
  have hsuper : ∀ x,
      paperWaveOperator p c u (upperBarrier κ M) x ≤ 0 :=
    paperUpperBarrier_super_of_scalar hκ hscalar hu
  have hupper := paperFixedSource_truncated_le_upperBarrier_local_of_trap
    (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
    (u := u) (Z := Z) (R := R)
    hlam hκ hM hB hu hR hRfix hZ.le_barrier hsuper
  exact fun x => ⟨hnonneg x, hupper x⟩

/-- Backwards-compatible clamp-inactivity wrapper for a full Rothe old
iterate. -/
theorem paperFixedSource_truncation_inactive_local_of_scalar
    {p : CMParams} {c lam M κ β B H : ℝ} {u Z R : ℝ → ℝ}
    (hlam : 0 < lam) (hκ : 0 < κ) (hM : 0 < M) (hB : 0 ≤ B)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hZ : PaperIterateBase p c κ M u Z)
    (hscalar : PaperUpperBarrierSuperScalarConditions p c κ M)
    (hR : PaperLocalHolderSourceBox κ M β B H R)
    (hRfix : paperFixedSourceMap p c lam M κ u Z R = R) :
    ∀ x, greenConv c lam R x ∈
      Set.Icc (0 : ℝ) (upperBarrier κ M x) :=
  paperFixedSource_truncation_inactive_local_of_oldData
    hlam hκ hM hB hu (hZ.toFixedSourceOldData hκ.le hM.le)
      hscalar hR hRfix

section AxiomAudit

#print axioms paperImplicitStep_truncated_ge_zero_tailfree
#print axioms paperFixedSource_truncated_ge_zero_local_of_trap
#print axioms paperImplicitStep_truncated_le_upperBarrier_tailfree
#print axioms paperFixedSource_truncated_le_upperBarrier_local_of_trap
#print axioms paperFixedSource_truncation_inactive_local_of_oldData
#print axioms paperFixedSource_truncation_inactive_local_of_scalar

end AxiomAudit

end ShenWork.Paper1
