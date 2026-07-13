/-
  Tail-free lower comparison for the positive-attraction Green step.

  The negative construction can exploit the sign of `-chi`.  Here `chi` is
  positive, so both cross-frozen terms are estimated with their absolute
  Lipschitz constants.  The logarithmic slope supplied by the positive
  plateau removes the `1 < m < 2` power cusp.
-/
import ShenWork.Paper1.WavePositivePlateauComparison
import ShenWork.Paper1.WavePinnedStepComparison
import ShenWork.Paper1.WavePinnedStepParameterAsymptotics

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-- Cross-frozen gradient increment with no sign assumption on the
coefficient.  The cost is the absolute coefficient. -/
theorem paperCrossGradient_diff_le_of_lower_log_slope_abs
    {p : CMParams} {a M BVd K eta : ℝ}
    {u A B : ℝ → ℝ} {x₀ : ℝ}
    (hM : 0 < M) (hBVd : 0 ≤ BVd) (hK : 0 ≤ K)
    (hB0 : 0 ≤ B x₀) (hBA : B x₀ ≤ A x₀) (hAM : A x₀ ≤ M)
    (hVpabs : |deriv (frozenElliptic p u) x₀| ≤ BVd)
    (hBderiv : |deriv B x₀| ≤ K * B x₀)
    (hslope : |deriv A x₀ - deriv B x₀| ≤ eta) :
    a * p.m * (A x₀) ^ (p.m - 1) *
          deriv (frozenElliptic p u) x₀ * deriv A x₀
      - a * p.m * (B x₀) ^ (p.m - 1) *
          deriv (frozenElliptic p u) x₀ * deriv B x₀ ≤
      (|a| * p.m * BVd * K * (p.m - 1) * M ^ (p.m - 1)) *
          (A x₀ - B x₀)
        + (|a| * p.m * BVd * M ^ (p.m - 1)) * eta := by
  let r : ℝ := p.m - 1
  let ds : ℝ := deriv A x₀ - deriv B x₀
  have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hr0 : 0 ≤ r := by dsimp [r]; linarith [p.hm]
  have hA0 : 0 ≤ A x₀ := le_trans hB0 hBA
  have hgap : 0 ≤ A x₀ - B x₀ := sub_nonneg.mpr hBA
  have hAr0 : 0 ≤ (A x₀) ^ r := Real.rpow_nonneg hA0 r
  have hpowmono : (B x₀) ^ r ≤ (A x₀) ^ r :=
    Real.rpow_le_rpow hB0 hBA hr0
  have hpowdiff0 : 0 ≤ (A x₀) ^ r - (B x₀) ^ r :=
    sub_nonneg.mpr hpowmono
  have hArM : (A x₀) ^ r ≤ M ^ r :=
    Real.rpow_le_rpow hA0 hAM hr0
  have hweighted :
      B x₀ * ((A x₀) ^ r - (B x₀) ^ r) ≤
        r * M ^ r * (A x₀ - B x₀) :=
    lower_weighted_rpow_increment_le hr0 hM hB0 hBA hAM
  have hds : |ds| ≤ eta := by simpa [ds] using hslope
  have hKabs :
      |a * p.m * deriv (frozenElliptic p u) x₀| ≤
        |a| * p.m * BVd := by
    rw [abs_mul, abs_mul, abs_of_nonneg hm0]
    exact mul_le_mul_of_nonneg_left hVpabs
      (mul_nonneg (abs_nonneg a) hm0)
  have hsplit :
      (A x₀) ^ r * deriv A x₀ - (B x₀) ^ r * deriv B x₀ =
        ((A x₀) ^ r - (B x₀) ^ r) * deriv B x₀ +
          (A x₀) ^ r * ds := by
    dsimp [ds]
    ring
  have hterm1 :
      |((A x₀) ^ r - (B x₀) ^ r) * deriv B x₀| ≤
        K * r * M ^ r * (A x₀ - B x₀) := by
    rw [abs_mul, abs_of_nonneg hpowdiff0]
    calc
      ((A x₀) ^ r - (B x₀) ^ r) * |deriv B x₀| ≤
          ((A x₀) ^ r - (B x₀) ^ r) * (K * B x₀) :=
        mul_le_mul_of_nonneg_left hBderiv hpowdiff0
      _ = K * (B x₀ * ((A x₀) ^ r - (B x₀) ^ r)) := by ring
      _ ≤ K * (r * M ^ r * (A x₀ - B x₀)) :=
        mul_le_mul_of_nonneg_left hweighted hK
      _ = K * r * M ^ r * (A x₀ - B x₀) := by ring
  have hterm2 : |(A x₀) ^ r * ds| ≤ M ^ r * eta := by
    rw [abs_mul, abs_of_nonneg hAr0]
    exact mul_le_mul hArM hds (abs_nonneg ds)
      (Real.rpow_nonneg hM.le r)
  have hbracket :
      |(A x₀) ^ r * deriv A x₀ - (B x₀) ^ r * deriv B x₀| ≤
        K * r * M ^ r * (A x₀ - B x₀) + M ^ r * eta := by
    rw [hsplit]
    exact (abs_add_le _ _).trans (add_le_add hterm1 hterm2)
  calc
    a * p.m * (A x₀) ^ r * deriv (frozenElliptic p u) x₀ * deriv A x₀
        - a * p.m * (B x₀) ^ r * deriv (frozenElliptic p u) x₀ * deriv B x₀ =
      (a * p.m * deriv (frozenElliptic p u) x₀) *
        ((A x₀) ^ r * deriv A x₀ - (B x₀) ^ r * deriv B x₀) := by
          ring
    _ ≤ |(a * p.m * deriv (frozenElliptic p u) x₀) *
        ((A x₀) ^ r * deriv A x₀ - (B x₀) ^ r * deriv B x₀)| :=
      le_abs_self _
    _ = |a * p.m * deriv (frozenElliptic p u) x₀| *
        |(A x₀) ^ r * deriv A x₀ - (B x₀) ^ r * deriv B x₀| :=
      abs_mul _ _
    _ ≤ (|a| * p.m * BVd) *
        (K * r * M ^ r * (A x₀ - B x₀) + M ^ r * eta) :=
      mul_le_mul hKabs hbracket (abs_nonneg _)
        (mul_nonneg (mul_nonneg (abs_nonneg a) hm0) hBVd)
    _ = (|a| * p.m * BVd * K * (p.m - 1) * M ^ (p.m - 1)) *
          (A x₀ - B x₀)
        + (|a| * p.m * BVd * M ^ (p.m - 1)) * eta := by
      dsimp [r]
      ring

/-- Cross-gradient estimate using a derivative bound proportional to the
upper contact profile.  This is the non-circular estimate used while proving
that a freshly selected Green step is above the plateau. -/
theorem paperCrossGradient_diff_le_of_upper_log_slope_abs
    {p : CMParams} {a M BVd K eta : ℝ}
    {u A B : ℝ → ℝ} {x₀ : ℝ}
    (hM : 0 < M) (hBVd : 0 ≤ BVd) (hK : 0 ≤ K)
    (hB0 : 0 ≤ B x₀) (hBA : B x₀ ≤ A x₀) (hAM : A x₀ ≤ M)
    (hVpabs : |deriv (frozenElliptic p u) x₀| ≤ BVd)
    (hBderiv : |deriv B x₀| ≤ K * A x₀)
    (hslope : |deriv A x₀ - deriv B x₀| ≤ eta) :
    a * p.m * (A x₀) ^ (p.m - 1) *
          deriv (frozenElliptic p u) x₀ * deriv A x₀
      - a * p.m * (B x₀) ^ (p.m - 1) *
          deriv (frozenElliptic p u) x₀ * deriv B x₀ ≤
      (|a| * p.m * BVd * K * p.m * M ^ (p.m - 1)) *
          (A x₀ - B x₀)
        + (|a| * p.m * BVd * M ^ (p.m - 1)) * eta := by
  let r : ℝ := p.m - 1
  let ds : ℝ := deriv A x₀ - deriv B x₀
  have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hr0 : 0 ≤ r := by dsimp [r]; linarith [p.hm]
  have hA0 : 0 ≤ A x₀ := le_trans hB0 hBA
  have hgap : 0 ≤ A x₀ - B x₀ := sub_nonneg.mpr hBA
  have hAr0 : 0 ≤ (A x₀) ^ r := Real.rpow_nonneg hA0 r
  have hpowdiff0 : 0 ≤ (A x₀) ^ r - (B x₀) ^ r :=
    sub_nonneg.mpr (Real.rpow_le_rpow hB0 hBA hr0)
  have hArM : (A x₀) ^ r ≤ M ^ r :=
    Real.rpow_le_rpow hA0 hAM hr0
  have hweighted :
      A x₀ * ((A x₀) ^ r - (B x₀) ^ r) ≤
        (r + 1) * M ^ r * (A x₀ - B x₀) :=
    upper_weighted_rpow_increment_le hr0 hM hB0 hBA hAM
  have hds : |ds| ≤ eta := by simpa [ds] using hslope
  have hKabs :
      |a * p.m * deriv (frozenElliptic p u) x₀| ≤
        |a| * p.m * BVd := by
    rw [abs_mul, abs_mul, abs_of_nonneg hm0]
    exact mul_le_mul_of_nonneg_left hVpabs
      (mul_nonneg (abs_nonneg a) hm0)
  have hsplit :
      (A x₀) ^ r * deriv A x₀ - (B x₀) ^ r * deriv B x₀ =
        ((A x₀) ^ r - (B x₀) ^ r) * deriv B x₀ +
          (A x₀) ^ r * ds := by
    dsimp [ds]
    ring
  have hterm1 :
      |((A x₀) ^ r - (B x₀) ^ r) * deriv B x₀| ≤
        K * (r + 1) * M ^ r * (A x₀ - B x₀) := by
    rw [abs_mul, abs_of_nonneg hpowdiff0]
    calc
      ((A x₀) ^ r - (B x₀) ^ r) * |deriv B x₀| ≤
          ((A x₀) ^ r - (B x₀) ^ r) * (K * A x₀) :=
        mul_le_mul_of_nonneg_left hBderiv hpowdiff0
      _ = K * (A x₀ * ((A x₀) ^ r - (B x₀) ^ r)) := by ring
      _ ≤ K * ((r + 1) * M ^ r * (A x₀ - B x₀)) :=
        mul_le_mul_of_nonneg_left hweighted hK
      _ = K * (r + 1) * M ^ r * (A x₀ - B x₀) := by ring
  have hterm2 : |(A x₀) ^ r * ds| ≤ M ^ r * eta := by
    rw [abs_mul, abs_of_nonneg hAr0]
    exact mul_le_mul hArM hds (abs_nonneg ds)
      (Real.rpow_nonneg hM.le r)
  have hbracket :
      |(A x₀) ^ r * deriv A x₀ - (B x₀) ^ r * deriv B x₀| ≤
        K * (r + 1) * M ^ r * (A x₀ - B x₀) + M ^ r * eta := by
    rw [hsplit]
    exact (abs_add_le _ _).trans (add_le_add hterm1 hterm2)
  calc
    a * p.m * (A x₀) ^ r * deriv (frozenElliptic p u) x₀ * deriv A x₀
        - a * p.m * (B x₀) ^ r * deriv (frozenElliptic p u) x₀ * deriv B x₀ =
      (a * p.m * deriv (frozenElliptic p u) x₀) *
        ((A x₀) ^ r * deriv A x₀ - (B x₀) ^ r * deriv B x₀) := by
          ring
    _ ≤ |(a * p.m * deriv (frozenElliptic p u) x₀) *
        ((A x₀) ^ r * deriv A x₀ - (B x₀) ^ r * deriv B x₀)| :=
      le_abs_self _
    _ = |a * p.m * deriv (frozenElliptic p u) x₀| *
        |(A x₀) ^ r * deriv A x₀ - (B x₀) ^ r * deriv B x₀| :=
      abs_mul _ _
    _ ≤ (|a| * p.m * BVd) *
        (K * (r + 1) * M ^ r * (A x₀ - B x₀) + M ^ r * eta) :=
      mul_le_mul hKabs hbracket (abs_nonneg _)
        (mul_nonneg (mul_nonneg (abs_nonneg a) hm0) hBVd)
    _ = (|a| * p.m * BVd * K * p.m * M ^ (p.m - 1)) *
          (A x₀ - B x₀)
        + (|a| * p.m * BVd * M ^ (p.m - 1)) * eta := by
      dsimp [r]
      ring

/-- Error-tolerant paper-operator ledger with no sign assumption on `chi`.
Both algebraic cross-frozen terms are bounded by absolute Lipschitz costs. -/
theorem paperWaveOperator_diff_le_abs_of_approx_contact
    {p : CMParams} {c a M BV Ccross Ecross eta : ℝ}
    {u A W : ℝ → ℝ} {x₀ : ℝ}
    (ha : a = -p.χ) (hM : 0 ≤ M)
    (hAmem : A x₀ ∈ Set.Icc (0 : ℝ) M)
    (hWmem : W x₀ ∈ Set.Icc (0 : ℝ) M)
    (hWA : W x₀ ≤ A x₀)
    (hVnonneg : 0 ≤ frozenElliptic p u x₀)
    (hVbound : frozenElliptic p u x₀ ≤ BV)
    (hsecond : iteratedDeriv 2 A x₀ - iteratedDeriv 2 W x₀ ≤ eta)
    (hslope : |deriv A x₀ - deriv W x₀| ≤ eta)
    (hcross :
      a * p.m * (A x₀) ^ (p.m - 1) *
            deriv (frozenElliptic p u) x₀ * deriv A x₀
        - a * p.m * (W x₀) ^ (p.m - 1) *
            deriv (frozenElliptic p u) x₀ * deriv W x₀ ≤
      Ccross * (A x₀ - W x₀) + Ecross * eta) :
    paperWaveOperator p c u A x₀ - paperWaveOperator p c u W x₀ ≤
      (reactionLip p.α M + |a| * BV * rpowLip p.m M +
          |a| * rpowLip (p.m + p.γ) M + Ccross) *
          (A x₀ - W x₀)
        + (1 + |c| + Ecross) * eta := by
  have hgap : 0 ≤ A x₀ - W x₀ := sub_nonneg.mpr hWA
  have hV0 : 0 ≤ BV := le_trans hVnonneg hVbound
  have hVabs : |frozenElliptic p u x₀| ≤ BV := by
    rw [abs_of_nonneg hVnonneg]
    exact hVbound
  have hrxn :
      reactionFun p.α (A x₀) - reactionFun p.α (W x₀) ≤
        reactionLip p.α M * (A x₀ - W x₀) := by
    have habs := reaction_increment_abs_le p.hα hM hWmem hAmem
    have hle := le_abs_self
      (reactionFun p.α (A x₀) - reactionFun p.α (W x₀))
    rw [abs_of_nonneg hgap] at habs
    linarith
  have hpowm :
      (A x₀) ^ p.m - (W x₀) ^ p.m ≤
        rpowLip p.m M * (A x₀ - W x₀) :=
    rpow_increment_le_rpowLip p.hm hM hWmem hAmem hWA
  have hpowm0 : 0 ≤ (A x₀) ^ p.m - (W x₀) ^ p.m :=
    sub_nonneg.mpr
      (Real.rpow_le_rpow hWmem.1 hWA (le_trans zero_le_one p.hm))
  have hVterm :
      a * (A x₀) ^ p.m * frozenElliptic p u x₀ -
          a * (W x₀) ^ p.m * frozenElliptic p u x₀ ≤
        |a| * BV * rpowLip p.m M * (A x₀ - W x₀) := by
    calc
      a * (A x₀) ^ p.m * frozenElliptic p u x₀ -
          a * (W x₀) ^ p.m * frozenElliptic p u x₀ =
        a * ((A x₀) ^ p.m - (W x₀) ^ p.m) *
          frozenElliptic p u x₀ := by ring
      _ ≤ |a * ((A x₀) ^ p.m - (W x₀) ^ p.m) *
          frozenElliptic p u x₀| := le_abs_self _
      _ = |a| * ((A x₀) ^ p.m - (W x₀) ^ p.m) *
          |frozenElliptic p u x₀| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hpowm0]
      _ ≤ |a| * (rpowLip p.m M * (A x₀ - W x₀)) * BV := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hpowm (abs_nonneg a)) hVabs
          (abs_nonneg _) (mul_nonneg (abs_nonneg a)
            (mul_nonneg (rpowLip_nonneg p.hm hM) hgap))
      _ = |a| * BV * rpowLip p.m M * (A x₀ - W x₀) := by ring
  have hmg : 1 ≤ p.m + p.γ := by linarith [p.hm, p.hγ]
  have hpowmg :
      (A x₀) ^ (p.m + p.γ) - (W x₀) ^ (p.m + p.γ) ≤
        rpowLip (p.m + p.γ) M * (A x₀ - W x₀) :=
    rpow_increment_le_rpowLip hmg hM hWmem hAmem hWA
  have hpowmg0 : 0 ≤
      (A x₀) ^ (p.m + p.γ) - (W x₀) ^ (p.m + p.γ) :=
    sub_nonneg.mpr
      (Real.rpow_le_rpow hWmem.1 hWA (le_trans zero_le_one hmg))
  have hdiag :
      -a * (A x₀) ^ (p.m + p.γ) -
          (-a * (W x₀) ^ (p.m + p.γ)) ≤
        |a| * rpowLip (p.m + p.γ) M * (A x₀ - W x₀) := by
    calc
      -a * (A x₀) ^ (p.m + p.γ) -
          (-a * (W x₀) ^ (p.m + p.γ)) =
        -a * ((A x₀) ^ (p.m + p.γ) -
          (W x₀) ^ (p.m + p.γ)) := by ring
      _ ≤ |-a * ((A x₀) ^ (p.m + p.γ) -
          (W x₀) ^ (p.m + p.γ))| := le_abs_self _
      _ = |a| * ((A x₀) ^ (p.m + p.γ) -
          (W x₀) ^ (p.m + p.γ)) := by
        rw [abs_mul, abs_neg, abs_of_nonneg hpowmg0]
      _ ≤ |a| * (rpowLip (p.m + p.γ) M * (A x₀ - W x₀)) :=
        mul_le_mul_of_nonneg_left hpowmg (abs_nonneg a)
      _ = |a| * rpowLip (p.m + p.γ) M * (A x₀ - W x₀) := by ring
  have hcSlope :
      c * deriv A x₀ - c * deriv W x₀ ≤ |c| * eta := by
    calc
      c * deriv A x₀ - c * deriv W x₀ =
          c * (deriv A x₀ - deriv W x₀) := by ring
      _ ≤ |c * (deriv A x₀ - deriv W x₀)| := le_abs_self _
      _ = |c| * |deriv A x₀ - deriv W x₀| := abs_mul _ _
      _ ≤ |c| * eta :=
        mul_le_mul_of_nonneg_left hslope (abs_nonneg c)
  rw [paperWaveOperator_eq_routeA_pieces p ha hAmem.1,
    paperWaveOperator_eq_routeA_pieces p ha hWmem.1]
  nlinarith [hrxn, hVterm, hdiag, hcSlope, hsecond, hcross]

/-- Tail-free comparison when the lower barrier is only `C²` away from one
`C¹` splice.  The two-center penalty lemma ensures that the approximate
contact is a smooth point. -/
theorem paperImplicitStep_ge_barrier_piecewise_tailfree
    {p : CMParams} {c lam Cmono E Q X : ℝ} {u Z W A : ℝ → ℝ}
    (hlam : 0 < lam)
    (hsmall : (1 / lam) * Cmono < 1)
    (hE : 0 ≤ E)
    (hstep : ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x)
    (hAZ : ∀ x, A x ≤ Z x)
    (hfcont : Continuous (fun x => A x - W x))
    (hfbound : ∀ x, |A x - W x| ≤ Q)
    (hfX : DifferentiableAt ℝ (fun x => A x - W x) X)
    (hfaway : ∀ x, x ≠ X → ContDiffAt ℝ 2 (fun y => A y - W y) x)
    (hAsub : ∀ x, x ≠ X → 0 < A x - W x →
      0 ≤ paperWaveOperator p c u A x)
    (hop_approx : ∀ eta, 0 < eta → ∀ x₀, x₀ ≠ X →
      0 < A x₀ - W x₀ →
      |deriv (fun x => A x - W x) x₀| < eta →
      deriv (deriv (fun x => A x - W x)) x₀ < eta →
      paperWaveOperator p c u A x₀ - paperWaveOperator p c u W x₀ ≤
        Cmono * (A x₀ - W x₀) + E * eta) :
    ∀ x, A x ≤ W x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₁, hx₁⟩ := hcon
  have hfpos : 0 < A x₁ - W x₁ := sub_pos.mpr hx₁
  have hClam : Cmono < lam := by
    have hmul := mul_lt_mul_of_pos_left hsmall hlam
    have hlamne : lam ≠ 0 := ne_of_gt hlam
    field_simp [hlamne] at hmul
    linarith
  let eta : ℝ :=
    (lam - Cmono) * (A x₁ - W x₁) / (4 * (E + 1))
  have heta : 0 < eta := by
    dsimp [eta]
    exact div_pos (mul_pos (sub_pos.mpr hClam) hfpos)
      (mul_pos (by norm_num) (by linarith))
  obtain ⟨x₀, hx₀X, hfvalue, hfSlope, hfSecond⟩ :=
    exists_approx_positive_max_deriv_data_away_C1splice
      (f := fun x => A x - W x) (A := Q) (eta := eta)
      (x₁ := x₁) (X := X)
      hfcont hfbound hfpos heta hfX hfaway
  have hfpos₀ : 0 < A x₀ - W x₀ := by linarith
  have hA := hop_approx eta heta x₀ hx₀X hfpos₀ hfSlope hfSecond
  have hstep₀ := hstep x₀
  have hdiv : A x₀ - W x₀ ≤
      -(1 / lam) * paperWaveOperator p c u W x₀ := by
    simp only [paperImplicitStepOp_apply] at hstep₀
    linarith [hAZ x₀]
  have hA_lower : lam * (A x₀ - W x₀) ≤
      paperWaveOperator p c u A x₀ - paperWaveOperator p c u W x₀ := by
    have hmul := mul_le_mul_of_nonneg_left hdiv hlam.le
    have hlamne : lam ≠ 0 := ne_of_gt hlam
    have hmain : lam * (A x₀ - W x₀) ≤
        -paperWaveOperator p c u W x₀ := by
      calc
        lam * (A x₀ - W x₀) ≤
            lam * (-(1 / lam) * paperWaveOperator p c u W x₀) := hmul
        _ = -paperWaveOperator p c u W x₀ := by field_simp [hlamne]
    linarith [hAsub x₀ hx₀X hfpos₀]
  have hEeta :
      E * eta < (lam - Cmono) * (A x₁ - W x₁) / 4 := by
    dsimp [eta]
    have hE1 : E < E + 1 := by linarith
    have hbase : 0 < (lam - Cmono) * (A x₁ - W x₁) :=
      mul_pos (sub_pos.mpr hClam) hfpos
    have hden : 0 < 4 * (E + 1) :=
      mul_pos (by norm_num) (by linarith)
    have hscaled :
        E * ((lam - Cmono) * (A x₁ - W x₁)) <
          (E + 1) * ((lam - Cmono) * (A x₁ - W x₁)) :=
      mul_lt_mul_of_pos_right hE1 hbase
    calc
      E * ((lam - Cmono) * (A x₁ - W x₁) / (4 * (E + 1))) =
          (E * ((lam - Cmono) * (A x₁ - W x₁))) /
            (4 * (E + 1)) := by ring
      _ < ((E + 1) * ((lam - Cmono) * (A x₁ - W x₁))) /
          (4 * (E + 1)) := (div_lt_div_iff_of_pos_right hden).2 hscaled
      _ = (lam - Cmono) * (A x₁ - W x₁) / 4 := by
        field_simp [ne_of_gt (show 0 < E + 1 by linarith)]
  have hfscaled :
      (lam - Cmono) * ((A x₁ - W x₁) / 2) <
        (lam - Cmono) * (A x₀ - W x₀) :=
    mul_lt_mul_of_pos_left hfvalue (sub_pos.mpr hClam)
  have hgap_le :
      (lam - Cmono) * (A x₀ - W x₀) ≤ E * eta := by
    linarith [hA_lower, hA]
  have hbase : 0 < (lam - Cmono) * (A x₁ - W x₁) :=
    mul_pos (sub_pos.mpr hClam) hfpos
  have hquarter :
      (lam - Cmono) * (A x₁ - W x₁) / 4 <
        (lam - Cmono) * ((A x₁ - W x₁) / 2) := by
    calc
      (lam - Cmono) * (A x₁ - W x₁) / 4 <
          (lam - Cmono) * (A x₁ - W x₁) / 2 := by linarith
      _ = (lam - Cmono) * ((A x₁ - W x₁) / 2) := by ring
  exact (not_lt_of_ge hgap_le)
    (lt_trans (lt_trans hEeta hquarter) hfscaled)

/-- Zeroth- and first-order comparison cost for a positive lower-pinned
paper step. -/
def paperPositivePinnedStepCmono
    (p : CMParams) (M K : ℝ) : ℝ :=
  reactionLip p.α M
    + |p.χ| * (M ^ p.γ) * rpowLip p.m M
    + |p.χ| * rpowLip (p.m + p.γ) M
    + |p.χ| * p.m * (M ^ p.γ) * K *
        (p.m - 1) * M ^ (p.m - 1)

/-- Comparison cost before the lower pin is known.  The Green derivative is
controlled by the upper barrier, producing the factor `m` in place of
`m - 1`. -/
def paperPositivePlateauStepCmono
    (p : CMParams) (M K : ℝ) : ℝ :=
  reactionLip p.α M
    + |p.χ| * (M ^ p.γ) * rpowLip p.m M
    + |p.χ| * rpowLip (p.m + p.γ) M
    + |p.χ| * p.m * (M ^ p.γ) * K *
        p.m * M ^ (p.m - 1)

def paperPositivePinnedStepE
    (p : CMParams) (c M : ℝ) : ℝ :=
  1 + |c| + |p.χ| * p.m * (M ^ p.γ) * M ^ (p.m - 1)

/-- With the canonical affine source radius, the positive comparison cost is
little-o of the implicit resolvent parameter. -/
theorem paperPositivePinnedStepCmono_large_source_tendsto_zero
    (p : CMParams) (c M κ κtilde D C : ℝ) :
    Tendsto
      (fun lam : ℝ =>
        (1 / lam) * paperPositivePinnedStepCmono p M
          (paperLowerPinnedStepLogSlopeCoeff c lam κ κtilde D M
            (2 * (C + lam))))
      atTop (nhds 0) := by
  let A : ℝ :=
    reactionLip p.α M
      + |p.χ| * M ^ p.γ * rpowLip p.m M
      + |p.χ| * rpowLip (p.m + p.γ) M
  let Q : ℝ :=
    |p.χ| * p.m * M ^ p.γ * (p.m - 1) * M ^ (p.m - 1)
  let R : ℝ := lowerPinnedBarrierRatio κ κtilde D M
  have hCdiv : Tendsto (fun lam : ℝ => C / lam) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hBdiv : Tendsto
      (fun lam : ℝ => (2 * (C + lam)) / lam) atTop (nhds 2) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have h := (hCdiv.add hone).const_mul 2
    have h' : Tendsto (fun lam : ℝ => 2 * (C / lam + 1))
        atTop (nhds 2) := by simpa using h
    refine h'.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with lam hlam
    field_simp [ne_of_gt hlam]
  have hmassB : Tendsto
      (fun lam : ℝ =>
        greenWeightedMass1 c lam κ * ((2 * (C + lam)) / lam))
      atTop (nhds 0) := by
    simpa using (greenWeightedMass1_tendsto_zero c κ).mul hBdiv
  have hKdiv : Tendsto
      (fun lam : ℝ =>
        (1 / lam) *
          paperLowerPinnedStepLogSlopeCoeff c lam κ κtilde D M
            (2 * (C + lam)))
      atTop (nhds 0) := by
    have h := hmassB.const_mul R
    have h' : Tendsto
        (fun lam : ℝ =>
          R * (greenWeightedMass1 c lam κ *
            ((2 * (C + lam)) / lam))) atTop (nhds 0) := by
      simpa using h
    refine h'.congr' (Filter.Eventually.of_forall ?_)
    intro lam
    dsimp [R]
    rw [paperLowerPinnedStepLogSlopeCoeff,
      paperStepWeightedDerivCoeff_eq_mass_mul]
    ring
  have hAdiv : Tendsto (fun lam : ℝ => A / lam) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have htotal := hAdiv.add (hKdiv.const_mul Q)
  have htotal' : Tendsto
      (fun lam : ℝ => A / lam + Q * ((1 / lam) *
        paperLowerPinnedStepLogSlopeCoeff c lam κ κtilde D M
          (2 * (C + lam)))) atTop (nhds 0) := by
    simpa using htotal
  refine htotal'.congr' (Filter.Eventually.of_forall ?_)
  intro lam
  dsimp [A, Q]
  unfold paperPositivePinnedStepCmono
  ring

theorem paperPositivePlateauStepCmono_large_source_tendsto_zero
    (p : CMParams) (c M κ κtilde D C : ℝ) :
    Tendsto
      (fun lam : ℝ =>
        (1 / lam) * paperPositivePlateauStepCmono p M
          (paperLowerPinnedStepLogSlopeCoeff c lam κ κtilde D M
            (2 * (C + lam))))
      atTop (nhds 0) := by
  let A : ℝ :=
    reactionLip p.α M
      + |p.χ| * M ^ p.γ * rpowLip p.m M
      + |p.χ| * rpowLip (p.m + p.γ) M
  let Q : ℝ := |p.χ| * p.m * M ^ p.γ * p.m * M ^ (p.m - 1)
  let R : ℝ := lowerPinnedBarrierRatio κ κtilde D M
  have hCdiv : Tendsto (fun lam : ℝ => C / lam) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hBdiv : Tendsto
      (fun lam : ℝ => (2 * (C + lam)) / lam) atTop (nhds 2) := by
    have h := (hCdiv.add
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1))).const_mul 2
    have h' : Tendsto (fun lam : ℝ => 2 * (C / lam + 1))
        atTop (nhds 2) := by simpa using h
    refine h'.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with lam hlam
    field_simp [ne_of_gt hlam]
  have hmassB : Tendsto
      (fun lam : ℝ => greenWeightedMass1 c lam κ *
        ((2 * (C + lam)) / lam)) atTop (nhds 0) := by
    simpa using (greenWeightedMass1_tendsto_zero c κ).mul hBdiv
  have hKdiv : Tendsto
      (fun lam : ℝ => (1 / lam) *
        paperLowerPinnedStepLogSlopeCoeff c lam κ κtilde D M
          (2 * (C + lam))) atTop (nhds 0) := by
    have h := hmassB.const_mul R
    refine (show Tendsto
      (fun lam : ℝ => R * (greenWeightedMass1 c lam κ *
        ((2 * (C + lam)) / lam))) atTop (nhds 0) by simpa using h).congr'
      (Filter.Eventually.of_forall ?_)
    intro lam
    dsimp [R]
    rw [paperLowerPinnedStepLogSlopeCoeff,
      paperStepWeightedDerivCoeff_eq_mass_mul]
    ring
  have hAdiv : Tendsto (fun lam : ℝ => A / lam) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have htotal := hAdiv.add (hKdiv.const_mul Q)
  refine (show Tendsto
    (fun lam : ℝ => A / lam + Q * ((1 / lam) *
      paperLowerPinnedStepLogSlopeCoeff c lam κ κtilde D M
        (2 * (C + lam)))) atTop (nhds 0) by simpa using htotal).congr'
      (Filter.Eventually.of_forall ?_)
  intro lam
  dsimp [A, Q]
  unfold paperPositivePlateauStepCmono
  ring

/-- The positive paper Green step preserves the actual plateau lower
barrier.  This is the sign-correct replacement for the negative Route-A
comparison: no `chi <= 0` hypothesis occurs. -/
theorem paperImplicitStep_ge_lowerBarrierPlateau_positive_tailfree
    (p : CMParams) {c lam κ κtilde D K : ℝ} {u Z W : ℝ → ℝ}
    (hcond : PositivePaperLemma42ExactConditions
      p c κ κtilde (MChi p))
    (hD : paperDMin p.χ (MChi p) κ κtilde p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (hχhalf : p.χ < (1 / 2 : ℝ))
    (hplateau : ∀ x, lowerBarrierPlateau κ κtilde D x ≤
      paper1PositivePlateauFloor p)
    (hlam : 0 < lam)
    (hu : InWaveTrapSet κ (MChi p) u)
    (hprev : ∀ x, lowerBarrierPlateau κ κtilde D x ≤ Z x)
    (hstep : ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x)
    (hW2 : ContDiff ℝ 2 W)
    (hWrange : ∀ x, W x ∈ Set.Icc (0 : ℝ) (MChi p))
    (hK : 0 ≤ K)
    (hWlog : ∀ x,
      |deriv W x| ≤ K * lowerBarrierPlateau κ κtilde D x)
    (hsmall : (1 / lam) *
      paperPositivePlateauStepCmono p (MChi p) K < 1) :
    ∀ x, lowerBarrierPlateau κ κtilde D x ≤ W x := by
  let A : ℝ → ℝ := lowerBarrierPlateau κ κtilde D
  let M : ℝ := MChi p
  let Ccross : ℝ :=
    |p.χ| * p.m * M ^ p.γ * K *
      p.m * M ^ (p.m - 1)
  let Ecross : ℝ :=
    |p.χ| * p.m * M ^ p.γ * M ^ (p.m - 1)
  let Cmono : ℝ := paperPositivePlateauStepCmono p M K
  let E : ℝ := paperPositivePinnedStepE p c M
  let X : ℝ := lowerBarrierXPlus κ κtilde D
  have hχ1 : p.χ < 1 := by linarith
  have hM1 : 1 ≤ M := by
    dsimp [M]
    exact one_le_MChi_of_chi_nonneg_lt_one p hcond.hχ_nonneg hχ1
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hgap : 0 < κtilde - κ := sub_pos.mpr hcond.hgap
  have hE0 : 0 ≤ E := by
    dsimp [E, paperPositivePinnedStepE, Ecross, M]
    have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
    have hMγ : 0 ≤ (MChi p) ^ p.γ := Real.rpow_nonneg hMpos.le _
    have hMm : 0 ≤ (MChi p) ^ (p.m - 1) := Real.rpow_nonneg hMpos.le _
    positivity
  have hsmall' : (1 / lam) * Cmono < 1 := by
    simpa [Cmono, M] using hsmall
  have hArange : ∀ x, A x ∈ Set.Icc (0 : ℝ) M := by
    intro x
    refine ⟨(lowerBarrierPlateau_pos hcond.hκ0 hgap hDpos x).le, ?_⟩
    exact (hplateau x).trans ((min_le_left _ _).trans hM1)
  have hfcont : Continuous (fun x => A x - W x) := by
    exact (lowerBarrierPlateau_continuous κ κtilde D).sub hW2.continuous
  have hfbound : ∀ x, |A x - W x| ≤ M := by
    intro x
    rw [abs_le]
    constructor <;> linarith [(hArange x).1, (hArange x).2,
      (hWrange x).1, (hWrange x).2]
  have hfX : DifferentiableAt ℝ (fun x => A x - W x) X := by
    exact (lowerBarrierPlateau_differentiableAt_xplus hcond.hκ0 hgap hDpos).sub
      (hW2.differentiable (by norm_num) X)
  have hfaway : ∀ x, x ≠ X → ContDiffAt ℝ 2 (fun y => A y - W y) x := by
    intro x hx
    exact (lowerBarrierPlateau_contDiffAt_two_of_ne_xplus hx).sub hW2.contDiffAt
  have hsub : ∀ x, x ≠ X → 0 < A x - W x →
      0 ≤ paperWaveOperator p c u A x := by
    intro x hx _
    exact paperWaveOperator_lowerBarrierPlateau_nonneg_pos_away
      p hcond hD hD1 hχhalf hplateau hu hx
  have hop : ∀ eta, 0 < eta → ∀ x₀, x₀ ≠ X →
      0 < A x₀ - W x₀ →
      |deriv (fun x => A x - W x) x₀| < eta →
      deriv (deriv (fun x => A x - W x)) x₀ < eta →
      paperWaveOperator p c u A x₀ - paperWaveOperator p c u W x₀ ≤
        Cmono * (A x₀ - W x₀) + E * eta := by
    intro eta heta x₀ hx₀ _hcontact hfSlope hfSecond
    have hA2 : ContDiffAt ℝ 2 A x₀ :=
      lowerBarrierPlateau_contDiffAt_two_of_ne_xplus hx₀
    have hWA : W x₀ ≤ A x₀ := by linarith
    have hslope : |deriv A x₀ - deriv W x₀| ≤ eta := by
      have heq : deriv (fun x => A x - W x) x₀ =
          deriv A x₀ - deriv W x₀ :=
        deriv_sub (hA2.differentiableAt (by norm_num))
          (hW2.differentiable (by norm_num) x₀)
      rw [heq] at hfSlope
      exact hfSlope.le
    have hsecond : iteratedDeriv 2 A x₀ - iteratedDeriv 2 W x₀ ≤ eta := by
      have heq : deriv (deriv (fun x => A x - W x)) x₀ =
          iteratedDeriv 2 A x₀ - iteratedDeriv 2 W x₀ := by
        calc
          deriv (deriv (fun x => A x - W x)) x₀ =
              iteratedDeriv 2 (fun x => A x - W x) x₀ := by
            simp [iteratedDeriv_succ, iteratedDeriv_zero]
          _ = iteratedDeriv 2 A x₀ - iteratedDeriv 2 W x₀ :=
            iteratedDeriv_fun_sub hA2 hW2.contDiffAt
      rw [heq] at hfSecond
      exact hfSecond.le
    have hVd : |deriv (frozenElliptic p u) x₀| ≤ M ^ p.γ := by
      exact (frozenElliptic_deriv_abs_le p hu.cunif_bdd hu.nonneg x₀).trans
        (frozenElliptic_le_rpow_of_inWaveTrapSet p hMpos hu x₀)
    have hcross :
        (-p.χ) * p.m * (A x₀) ^ (p.m - 1) *
              deriv (frozenElliptic p u) x₀ * deriv A x₀
          - (-p.χ) * p.m * (W x₀) ^ (p.m - 1) *
              deriv (frozenElliptic p u) x₀ * deriv W x₀ ≤
        Ccross * (A x₀ - W x₀) + Ecross * eta := by
      simpa [Ccross, Ecross, abs_neg] using
        paperCrossGradient_diff_le_of_upper_log_slope_abs
          (p := p) (a := -p.χ) (M := M) (BVd := M ^ p.γ)
          (K := K) (eta := eta) (u := u) (A := A) (B := W) (x₀ := x₀)
          hMpos (Real.rpow_nonneg hMpos.le _) hK
          (hWrange x₀).1 hWA (hArange x₀).2 hVd (hWlog x₀) hslope
    have hop0 := paperWaveOperator_diff_le_abs_of_approx_contact
      (p := p) (c := c) (a := -p.χ) (M := M) (BV := M ^ p.γ)
      (Ccross := Ccross) (Ecross := Ecross) (eta := eta)
      (u := u) (A := A) (W := W) (x₀ := x₀)
      rfl hMpos.le (hArange x₀) (hWrange x₀) hWA
      (frozenElliptic_nonneg_of_inWaveTrapSet p hu x₀)
      (frozenElliptic_le_rpow_of_inWaveTrapSet p hMpos hu x₀)
      hsecond hslope hcross
    dsimp [Cmono, paperPositivePlateauStepCmono, Ccross, Ecross, E,
      paperPositivePinnedStepE] at hop0 ⊢
    simpa [abs_neg] using hop0
  exact paperImplicitStep_ge_barrier_piecewise_tailfree
    (p := p) (c := c) (lam := lam) (Cmono := Cmono) (E := E)
    (Q := M) (X := X) (u := u) (Z := Z) (W := W) (A := A)
    hlam hsmall' hE0 hstep hprev hfcont hfbound hfX hfaway hsub hop

section AxiomAudit

#print axioms paperCrossGradient_diff_le_of_lower_log_slope_abs
#print axioms paperWaveOperator_diff_le_abs_of_approx_contact
#print axioms paperImplicitStep_ge_barrier_piecewise_tailfree
#print axioms paperImplicitStep_ge_lowerBarrierPlateau_positive_tailfree
#print axioms paperPositivePinnedStepCmono_large_source_tendsto_zero
#print axioms paperPositivePlateauStepCmono_large_source_tendsto_zero

end AxiomAudit

end ShenWork.Paper1
