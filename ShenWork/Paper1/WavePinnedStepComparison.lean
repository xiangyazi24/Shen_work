import ShenWork.Paper1.WaveLowerRawApproxOperator
import ShenWork.Paper1.WaveLowerPinnedLogSlope

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-- The exact scalar coefficient in comparison with a smooth lower-pinned old
iterate.  Unlike the earlier generic Route-A coefficient, this includes the
weighted log-slope term needed when `1 < m < 2`. -/
def paperPinnedStepCmono
    (p : CMParams) (c lam M κ κtilde D B : ℝ) : ℝ :=
  reactionLip p.α M
    + (-p.χ) * (M ^ p.γ) * rpowLip p.m M
    + ((-p.χ) * p.m * (M ^ p.γ) *
        paperLowerPinnedStepLogSlopeCoeff c lam κ κtilde D M B *
        (p.m - 1) * M ^ (p.m - 1))

/-- Multiplication by the lower endpoint removes the power cusp with the sharp
factor `r`. -/
theorem lower_weighted_rpow_increment_le
    {r M b A : ℝ} (hr : 0 ≤ r) (hM : 0 < M)
    (hb : 0 ≤ b) (hbA : b ≤ A) (hAM : A ≤ M) :
    b * (A ^ r - b ^ r) ≤ r * M ^ r * (A - b) := by
  have hA0 : 0 ≤ A := le_trans hb hbA
  have hgap : 0 ≤ A - b := sub_nonneg.mpr hbA
  rcases eq_or_lt_of_le hr with hr0 | hrpos
  · subst r
    simp
  by_cases hr1 : r < 1
  · have h := weighted_rpow_increment_le
      hrpos hr1 hM hb hgap (by linarith : b + (A - b) ≤ M)
    simpa [show b + (A - b) = A by ring] using h
  · have hrone : 1 ≤ r := le_of_not_gt hr1
    have hbmem : b ∈ Set.Icc (0 : ℝ) M := ⟨hb, le_trans hbA hAM⟩
    have hAmem : A ∈ Set.Icc (0 : ℝ) M := ⟨hA0, hAM⟩
    have hinc := rpow_increment_le_rpowLip hrone hM.le hbmem hAmem hbA
    have hfirst :
        b * (A ^ r - b ^ r) ≤
          b * (rpowLip r M * (A - b)) :=
      mul_le_mul_of_nonneg_left hinc hb
    have hbM : b * (rpowLip r M * (A - b)) ≤
        M * (rpowLip r M * (A - b)) :=
      mul_le_mul_of_nonneg_right (le_trans hbA hAM)
        (mul_nonneg (rpowLip_nonneg hrone hM.le) hgap)
    have hMr : M * M ^ (r - 1) = M ^ r :=
      mul_rpow_sub_one r hrone hM.le
    calc
      b * (A ^ r - b ^ r) ≤
          b * (rpowLip r M * (A - b)) := hfirst
      _ ≤ M * (rpowLip r M * (A - b)) := hbM
      _ = r * M ^ r * (A - b) := by
        unfold rpowLip
        rw [← hMr]
        ring

/-- Cross-frozen gradient increment at an approximate positive contact with a
lower profile having `|B'| ≤ K B`.  This is uniform through the cusp regime
`1 < m < 2`. -/
theorem paperCrossGradient_diff_le_of_lower_log_slope
    {p : CMParams} {a M BVd K eta : ℝ}
    {u A B : ℝ → ℝ} {x₀ : ℝ}
    (ha : a = -p.χ) (hχ : p.χ ≤ 0)
    (hM : 0 < M) (hBVd : 0 ≤ BVd) (hK : 0 ≤ K)
    (hB0 : 0 ≤ B x₀) (hBA : B x₀ ≤ A x₀) (hAM : A x₀ ≤ M)
    (hVpabs : |deriv (frozenElliptic p u) x₀| ≤ BVd)
    (hBderiv : |deriv B x₀| ≤ K * B x₀)
    (hslope : |deriv A x₀ - deriv B x₀| ≤ eta) :
    a * p.m * (A x₀) ^ (p.m - 1) *
          deriv (frozenElliptic p u) x₀ * deriv A x₀
      - a * p.m * (B x₀) ^ (p.m - 1) *
          deriv (frozenElliptic p u) x₀ * deriv B x₀ ≤
      (a * p.m * BVd * K * (p.m - 1) * M ^ (p.m - 1)) *
          (A x₀ - B x₀)
        + (a * p.m * BVd * M ^ (p.m - 1)) * eta := by
  let r : ℝ := p.m - 1
  let ds : ℝ := deriv A x₀ - deriv B x₀
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hr0 : 0 ≤ r := by dsimp [r]; linarith [p.hm]
  have hA0 : 0 ≤ A x₀ := le_trans hB0 hBA
  have hgap : 0 ≤ A x₀ - B x₀ := sub_nonneg.mpr hBA
  have hAr0 : 0 ≤ (A x₀) ^ r := Real.rpow_nonneg hA0 r
  have hBr0 : 0 ≤ (B x₀) ^ r := Real.rpow_nonneg hB0 r
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
      |a * p.m * deriv (frozenElliptic p u) x₀| ≤ a * p.m * BVd := by
    rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hm0]
    exact mul_le_mul_of_nonneg_left hVpabs (mul_nonneg ha0 hm0)
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
        ((A x₀) ^ r * deriv A x₀ - (B x₀) ^ r * deriv B x₀) := by ring
    _ ≤ |(a * p.m * deriv (frozenElliptic p u) x₀) *
        ((A x₀) ^ r * deriv A x₀ - (B x₀) ^ r * deriv B x₀)| := le_abs_self _
    _ = |a * p.m * deriv (frozenElliptic p u) x₀| *
        |(A x₀) ^ r * deriv A x₀ - (B x₀) ^ r * deriv B x₀| := abs_mul _ _
    _ ≤ (a * p.m * BVd) *
        (K * r * M ^ r * (A x₀ - B x₀) + M ^ r * eta) :=
      mul_le_mul hKabs hbracket (abs_nonneg _)
        (mul_nonneg (mul_nonneg ha0 hm0) hBVd)
    _ = (a * p.m * BVd * K * (p.m - 1) * M ^ (p.m - 1)) *
          (A x₀ - B x₀)
        + (a * p.m * BVd * M ^ (p.m - 1)) * eta := by
      dsimp [r]
      ring

/-- Tail-free comparison of a smooth implicit step with a lower-pinned smooth
old supersolution carrying a logarithmic slope bound. -/
theorem paperImplicitStep_le_of_pinned_smooth_old
    {p : CMParams} {c lam M κ Cmono K : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 < M)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hbox : PaperFrozenEllipticSourceBox p κ M)
    (hχ : p.χ ≤ 0)
    (hsmall : (1 / lam) * Cmono < 1)
    (hCmono :
      reactionLip p.α M
          + (-p.χ) * (M ^ p.γ) * rpowLip p.m M
          + ((-p.χ) * p.m * (M ^ p.γ) * K *
              (p.m - 1) * M ^ (p.m - 1)) ≤ Cmono)
    (hK : 0 ≤ K)
    (hstep : ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x)
    (hW2 : ContDiff ℝ 2 W) (hZ2 : ContDiff ℝ 2 Z)
    (hWrange : ∀ x, W x ∈ Set.Icc (0 : ℝ) M)
    (hZrange : ∀ x, Z x ∈ Set.Icc (0 : ℝ) M)
    (hZsuper : ∀ x, paperWaveOperator p c u Z x ≤ 0)
    (hZlog : ∀ x, |deriv Z x| ≤ K * Z x) :
    ∀ x, W x ≤ Z x := by
  let Ccross : ℝ :=
    (-p.χ) * p.m * (M ^ p.γ) * K *
      (p.m - 1) * M ^ (p.m - 1)
  let Ecross : ℝ :=
    (-p.χ) * p.m * (M ^ p.γ) * M ^ (p.m - 1)
  let E : ℝ := 1 + |c| + Ecross
  have hnegχ : 0 ≤ -p.χ := by linarith
  have hE0 : 0 ≤ E := by
    dsimp [E, Ecross]
    have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
    have hpγ : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM.le _
    have hpm : 0 ≤ M ^ (p.m - 1) := Real.rpow_nonneg hM.le _
    have ht : 0 ≤ (-p.χ) * p.m * M ^ p.γ * M ^ (p.m - 1) := by
      positivity
    linarith [abs_nonneg c]
  have hf2 : ContDiff ℝ 2 (fun x => W x - Z x) := hW2.sub hZ2
  have hfbound : ∀ x, W x - Z x ≤ M := by
    intro x
    linarith [(hWrange x).2, (hZrange x).1]
  have hop : ∀ eta, 0 < eta → ∀ x₀,
      0 < W x₀ - Z x₀ →
      |deriv (fun x => W x - Z x) x₀| < eta →
      deriv (deriv (fun x => W x - Z x)) x₀ < eta →
      paperWaveOperator p c u W x₀ - paperWaveOperator p c u Z x₀ ≤
        Cmono * (W x₀ - Z x₀) + E * eta := by
    intro eta heta x₀ hcontact hfSlope hfSecond
    have hZW : Z x₀ ≤ W x₀ := by linarith
    have hslope : |deriv W x₀ - deriv Z x₀| ≤ eta := by
      have heq : deriv (fun x => W x - Z x) x₀ =
          deriv W x₀ - deriv Z x₀ :=
        deriv_sub (hW2.differentiable (by norm_num) x₀)
          (hZ2.differentiable (by norm_num) x₀)
      rw [heq] at hfSlope
      exact hfSlope.le
    have hsecond : iteratedDeriv 2 W x₀ - iteratedDeriv 2 Z x₀ ≤ eta := by
      have heq : deriv (deriv (fun x => W x - Z x)) x₀ =
          iteratedDeriv 2 W x₀ - iteratedDeriv 2 Z x₀ := by
        calc
          deriv (deriv (fun x => W x - Z x)) x₀ =
              iteratedDeriv 2 (fun x => W x - Z x) x₀ := by
            simp [iteratedDeriv_succ, iteratedDeriv_zero]
          _ = iteratedDeriv 2 W x₀ - iteratedDeriv 2 Z x₀ :=
            iteratedDeriv_fun_sub hW2.contDiffAt hZ2.contDiffAt
      rw [heq] at hfSecond
      exact hfSecond.le
    have hcross :
        (-p.χ) * p.m * (W x₀) ^ (p.m - 1) *
              deriv (frozenElliptic p u) x₀ * deriv W x₀
          - (-p.χ) * p.m * (Z x₀) ^ (p.m - 1) *
              deriv (frozenElliptic p u) x₀ * deriv Z x₀ ≤
        Ccross * (W x₀ - Z x₀) + Ecross * eta := by
      simpa [Ccross, Ecross] using
        paperCrossGradient_diff_le_of_lower_log_slope
          (p := p) (a := -p.χ) (M := M) (BVd := M ^ p.γ)
          (K := K) (eta := eta) (u := u) (A := W) (B := Z) (x₀ := x₀)
          rfl hχ hM (Real.rpow_nonneg hM.le _) hK
          (hZrange x₀).1 hZW (hWrange x₀).2
          (hbox.deriv_abs_le u hu x₀) (hZlog x₀) hslope
    have hop0 := paperWaveOperator_diff_le_of_approx_contact
      (p := p) (c := c) (a := -p.χ) (M := M) (BV := M ^ p.γ)
      (Ccross := Ccross) (Ecross := Ecross) (eta := eta)
      (u := u) (A := W) (W := Z) (x₀ := x₀)
      rfl hχ hM.le (hWrange x₀) (hZrange x₀) hZW
      (hbox.value_nonneg u hu x₀) (hbox.value_le u hu x₀)
      hsecond hslope hcross
    dsimp [Ccross, Ecross, E] at hop0 ⊢
    nlinarith [hop0, hCmono]
  exact paperImplicitStep_le_barrier_of_quasiMonotone_tailfree
    (p := p) (c := c) (lam := lam) (Cmono := Cmono)
    (E := E) (Q := M) (u := u) (Z := Z) (W := W) (B := Z)
    hlam hsmall hE0 hstep (fun _ => le_rfl) hf2 hfbound hZsuper hop

/-- Tail-free lower comparison with a smooth stationary subsolution.  Here the
logarithmic-slope input is carried by the newly produced (lower) profile.  This
is the dual comparison needed to show that the upper-start Rothe orbit stays
above every lower-pinned stationary profile for the same frozen parameter. -/
theorem paperImplicitStep_ge_of_pinned_smooth_new
    {p : CMParams} {c lam M κ Cmono K : ℝ} {u Z W A : ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 < M)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hbox : PaperFrozenEllipticSourceBox p κ M)
    (hχ : p.χ ≤ 0)
    (hsmall : (1 / lam) * Cmono < 1)
    (hCmono :
      reactionLip p.α M
          + (-p.χ) * (M ^ p.γ) * rpowLip p.m M
          + ((-p.χ) * p.m * (M ^ p.γ) * K *
              (p.m - 1) * M ^ (p.m - 1)) ≤ Cmono)
    (hK : 0 ≤ K)
    (hstep : ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x)
    (hA2 : ContDiff ℝ 2 A) (hW2 : ContDiff ℝ 2 W)
    (hArange : ∀ x, A x ∈ Set.Icc (0 : ℝ) M)
    (hWrange : ∀ x, W x ∈ Set.Icc (0 : ℝ) M)
    (hAsub : ∀ x, 0 ≤ paperWaveOperator p c u A x)
    (hWlog : ∀ x, |deriv W x| ≤ K * W x)
    (hAZ : ∀ x, A x ≤ Z x) :
    ∀ x, A x ≤ W x := by
  let Ccross : ℝ :=
    (-p.χ) * p.m * (M ^ p.γ) * K *
      (p.m - 1) * M ^ (p.m - 1)
  let Ecross : ℝ :=
    (-p.χ) * p.m * (M ^ p.γ) * M ^ (p.m - 1)
  let E : ℝ := 1 + |c| + Ecross
  have hnegχ : 0 ≤ -p.χ := by linarith
  have hE0 : 0 ≤ E := by
    dsimp [E, Ecross]
    have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
    have hpγ : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM.le _
    have hpm : 0 ≤ M ^ (p.m - 1) := Real.rpow_nonneg hM.le _
    have ht : 0 ≤ (-p.χ) * p.m * M ^ p.γ * M ^ (p.m - 1) := by
      positivity
    linarith [abs_nonneg c]
  have hf2 : ContDiff ℝ 2 (fun x => A x - W x) := hA2.sub hW2
  have hfbound : ∀ x, A x - W x ≤ M := by
    intro x
    linarith [(hArange x).2, (hWrange x).1]
  have hop : ∀ eta, 0 < eta → ∀ x₀,
      0 < A x₀ - W x₀ →
      |deriv (fun x => A x - W x) x₀| < eta →
      deriv (deriv (fun x => A x - W x)) x₀ < eta →
      paperWaveOperator p c u A x₀ - paperWaveOperator p c u W x₀ ≤
        Cmono * (A x₀ - W x₀) + E * eta := by
    intro eta heta x₀ hcontact hfSlope hfSecond
    have hWA : W x₀ ≤ A x₀ := by linarith
    have hslope : |deriv A x₀ - deriv W x₀| ≤ eta := by
      have heq : deriv (fun x => A x - W x) x₀ =
          deriv A x₀ - deriv W x₀ :=
        deriv_sub (hA2.differentiable (by norm_num) x₀)
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
            iteratedDeriv_fun_sub hA2.contDiffAt hW2.contDiffAt
      rw [heq] at hfSecond
      exact hfSecond.le
    have hcross :
        (-p.χ) * p.m * (A x₀) ^ (p.m - 1) *
              deriv (frozenElliptic p u) x₀ * deriv A x₀
          - (-p.χ) * p.m * (W x₀) ^ (p.m - 1) *
              deriv (frozenElliptic p u) x₀ * deriv W x₀ ≤
        Ccross * (A x₀ - W x₀) + Ecross * eta := by
      simpa [Ccross, Ecross] using
        paperCrossGradient_diff_le_of_lower_log_slope
          (p := p) (a := -p.χ) (M := M) (BVd := M ^ p.γ)
          (K := K) (eta := eta) (u := u) (A := A) (B := W) (x₀ := x₀)
          rfl hχ hM (Real.rpow_nonneg hM.le _) hK
          (hWrange x₀).1 hWA (hArange x₀).2
          (hbox.deriv_abs_le u hu x₀) (hWlog x₀) hslope
    have hop0 := paperWaveOperator_diff_le_of_approx_contact
      (p := p) (c := c) (a := -p.χ) (M := M) (BV := M ^ p.γ)
      (Ccross := Ccross) (Ecross := Ecross) (eta := eta)
      (u := u) (A := A) (W := W) (x₀ := x₀)
      rfl hχ hM.le (hArange x₀) (hWrange x₀) hWA
      (hbox.value_nonneg u hu x₀) (hbox.value_le u hu x₀)
      hsecond hslope hcross
    dsimp [Ccross, Ecross, E] at hop0 ⊢
    nlinarith [hop0, hCmono]
  exact paperImplicitStep_ge_barrier_of_quasiMonotone_tailfree
    (p := p) (c := c) (lam := lam) (Cmono := Cmono)
    (E := E) (Q := M) (u := u) (Z := Z) (W := W) (A := A)
    hlam hsmall hE0 hstep hAZ hf2 hfbound
    (fun x _ => hAsub x) hop

/-- Successor comparison in the genuine local Green construction.  Once the
old step is lower-pinned, all smoothness, range and logarithmic-slope inputs
are internal; only the single explicit scalar gap remains. -/
theorem PaperLocalFixedStepData.le_old_of_lowerPinned_old
    {p : CMParams} {c lam M κ κtilde D Λ B : ℝ}
    {u Z₀ : ℝ → ℝ}
    (hlam : 0 < lam)
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD : 0 < D) (hM : 0 < M) (hB : 0 ≤ B)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hbox : PaperFrozenEllipticSourceBox p κ M)
    (hχ : p.χ ≤ 0)
    (hsmall :
      (1 / lam) * paperPinnedStepCmono p c lam M κ κtilde D B < 1)
    (dOld : PaperLocalFixedStepData p c lam M κ Λ B u Z₀)
    (hOldLower : ∀ x,
      lowerBarrierPlateau κ κtilde D x ≤ dOld.fixed.W x)
    (hOldSuper : ∀ x, paperWaveOperator p c u dOld.fixed.W x ≤ 0)
    (dNew : PaperLocalFixedStepData p c lam M κ Λ B u dOld.fixed.W) :
    ∀ x, dNew.fixed.W x ≤ dOld.fixed.W x := by
  let K := paperLowerPinnedStepLogSlopeCoeff c lam κ κtilde D M B
  have hK : 0 ≤ K :=
    paperLowerPinnedStepLogSlopeCoeff_nonneg
      hlam hrpκ hrmκ hκ hgap hD hM.le hB
  have hWrange : ∀ x, dNew.fixed.W x ∈ Set.Icc (0 : ℝ) M := by
    intro x
    exact ⟨(dNew.range x).1,
      (dNew.range x).2.trans (upperBarrier_le_M κ M x)⟩
  have hZrange : ∀ x, dOld.fixed.W x ∈ Set.Icc (0 : ℝ) M := by
    intro x
    exact ⟨(dOld.range x).1,
      (dOld.range x).2.trans (upperBarrier_le_M κ M x)⟩
  apply paperImplicitStep_le_of_pinned_smooth_old
    (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
    (Cmono := paperPinnedStepCmono p c lam M κ κtilde D B)
    (K := K) (u := u) (Z := dOld.fixed.W) (W := dNew.fixed.W)
    hlam hM hu hbox hχ hsmall
  · exact le_rfl
  · exact hK
  · exact dNew.step_op hlam
  · exact dNew.contDiff_two hlam
  · exact dOld.contDiff_two hlam
  · exact hWrange
  · exact hZrange
  · exact hOldSuper
  · exact dOld.deriv_abs_le_mul_self_of_lowerBound
      hlam hrpκ hrmκ hκ hgap hD hM.le hB hOldLower

/-- The raw lower-barrier comparison is automatic for a genuine local Green
step whenever the old iterate already carries the lower pin. -/
theorem PaperLocalFixedStepData.lowerRaw_of_old_lowerRaw
    {p : CMParams} {c lam M κ κtilde D Λ B : ℝ}
    {u Z : ℝ → ℝ}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hu : InLowerPinnedMonotoneTrap κ M
      (lowerBarrierRaw κ κtilde D) u)
    (hprev : ∀ x, lowerBarrierRaw κ κtilde D x ≤ Z x)
    (hlam : 0 < lam)
    (hsmall :
      (1 / lam) * paperLowerRawApproxCmono p M κtilde < 1)
    (d : PaperLocalFixedStepData p c lam M κ Λ B u Z) :
    ∀ x, lowerBarrierRaw κ κtilde D x ≤ d.fixed.W x := by
  have haux : PaperLowerRawStepApproxOperatorData
      p c lam κ κtilde D u d.fixed.W :=
    paperLowerRawStepApproxOperatorData_of_conditions
      hcond hD hD_ge_one hu.bare (d.contDiff_two hlam)
      (fun x => (d.range x).1) (fun x => (d.range x).2) hsmall
  exact paperImplicitStep_ge_lowerBarrierRaw_tailfree
    hcond hD hD_ge_one hu hprev hlam (d.step_op hlam)
      (d.contDiff_two hlam) (fun x => (d.range x).1) haux

section AxiomAudit

#print axioms lower_weighted_rpow_increment_le
#print axioms paperCrossGradient_diff_le_of_lower_log_slope
#print axioms paperImplicitStep_le_of_pinned_smooth_old
#print axioms paperImplicitStep_ge_of_pinned_smooth_new
#print axioms PaperLocalFixedStepData.le_old_of_lowerPinned_old
#print axioms PaperLocalFixedStepData.lowerRaw_of_old_lowerRaw

end AxiomAudit

end ShenWork.Paper1
