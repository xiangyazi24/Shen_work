import ShenWork.Paper1.WavePositiveStepComparison
import ShenWork.Paper1.WholeLineCauchyLocalExistence

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-!
# Approximate-contact operator bounds for the dynamic lower plateau

The comparison argument for a Cauchy restart has no monotonicity information
on the current population slice.  In particular, no sign of the frozen
resolver gradient is available.  The estimates below use only a global
nonnegative value strip for that slice.  The cusp at `1 < m < 2` is removed by
placing the logarithmic-slope bound on the upper contact barrier and using the
upper-weighted power increment.
-/

/-- Cross-frozen gradient increment controlled by the logarithmic slope of
the upper contact profile.  No sign of the frozen resolver gradient is used.

The power difference is split around `deriv A`; this is the form needed when
`A` is the stationary lower plateau and `W` is an arbitrary Cauchy slice. -/
theorem paperCrossGradient_diff_le_of_upper_barrier_log_slope_abs
    {p : CMParams} {a M BVd K eta : ℝ}
    {u A W : ℝ → ℝ} {x₀ : ℝ}
    (hM : 0 < M) (hBVd : 0 ≤ BVd) (hK : 0 ≤ K)
    (hW0 : 0 ≤ W x₀) (hWA : W x₀ ≤ A x₀) (hAM : A x₀ ≤ M)
    (hVpabs : |deriv (frozenElliptic p u) x₀| ≤ BVd)
    (hAderiv : |deriv A x₀| ≤ K * A x₀)
    (hslope : |deriv A x₀ - deriv W x₀| ≤ eta) :
    a * p.m * (A x₀) ^ (p.m - 1) *
          deriv (frozenElliptic p u) x₀ * deriv A x₀
      - a * p.m * (W x₀) ^ (p.m - 1) *
          deriv (frozenElliptic p u) x₀ * deriv W x₀ ≤
      (|a| * p.m * BVd * K * p.m * M ^ (p.m - 1)) *
          (A x₀ - W x₀)
        + (|a| * p.m * BVd * M ^ (p.m - 1)) * eta := by
  let r : ℝ := p.m - 1
  let ds : ℝ := deriv A x₀ - deriv W x₀
  have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hr0 : 0 ≤ r := by
    dsimp [r]
    linarith [p.hm]
  have hA0 : 0 ≤ A x₀ := le_trans hW0 hWA
  have hgap : 0 ≤ A x₀ - W x₀ := sub_nonneg.mpr hWA
  have hWr0 : 0 ≤ (W x₀) ^ r := Real.rpow_nonneg hW0 r
  have hpowdiff0 : 0 ≤ (A x₀) ^ r - (W x₀) ^ r :=
    sub_nonneg.mpr (Real.rpow_le_rpow hW0 hWA hr0)
  have hArM : (A x₀) ^ r ≤ M ^ r :=
    Real.rpow_le_rpow hA0 hAM hr0
  have hWrM : (W x₀) ^ r ≤ M ^ r :=
    (Real.rpow_le_rpow hW0 hWA hr0).trans hArM
  have hweighted :
      A x₀ * ((A x₀) ^ r - (W x₀) ^ r) ≤
        (r + 1) * M ^ r * (A x₀ - W x₀) :=
    upper_weighted_rpow_increment_le hr0 hM hW0 hWA hAM
  have hds : |ds| ≤ eta := by
    simpa [ds] using hslope
  have hKabs :
      |a * p.m * deriv (frozenElliptic p u) x₀| ≤
        |a| * p.m * BVd := by
    rw [abs_mul, abs_mul, abs_of_nonneg hm0]
    exact mul_le_mul_of_nonneg_left hVpabs
      (mul_nonneg (abs_nonneg a) hm0)
  have hsplit :
      (A x₀) ^ r * deriv A x₀ - (W x₀) ^ r * deriv W x₀ =
        ((A x₀) ^ r - (W x₀) ^ r) * deriv A x₀ +
          (W x₀) ^ r * ds := by
    dsimp [ds]
    ring
  have hterm1 :
      |((A x₀) ^ r - (W x₀) ^ r) * deriv A x₀| ≤
        K * (r + 1) * M ^ r * (A x₀ - W x₀) := by
    rw [abs_mul, abs_of_nonneg hpowdiff0]
    calc
      ((A x₀) ^ r - (W x₀) ^ r) * |deriv A x₀| ≤
          ((A x₀) ^ r - (W x₀) ^ r) * (K * A x₀) :=
        mul_le_mul_of_nonneg_left hAderiv hpowdiff0
      _ = K * (A x₀ * ((A x₀) ^ r - (W x₀) ^ r)) := by ring
      _ ≤ K * ((r + 1) * M ^ r * (A x₀ - W x₀)) :=
        mul_le_mul_of_nonneg_left hweighted hK
      _ = K * (r + 1) * M ^ r * (A x₀ - W x₀) := by ring
  have hterm2 : |(W x₀) ^ r * ds| ≤ M ^ r * eta := by
    rw [abs_mul, abs_of_nonneg hWr0]
    exact mul_le_mul hWrM hds (abs_nonneg ds)
      (Real.rpow_nonneg hM.le r)
  have hbracket :
      |(A x₀) ^ r * deriv A x₀ - (W x₀) ^ r * deriv W x₀| ≤
        K * (r + 1) * M ^ r * (A x₀ - W x₀) + M ^ r * eta := by
    rw [hsplit]
    exact (abs_add_le _ _).trans (add_le_add hterm1 hterm2)
  calc
    a * p.m * (A x₀) ^ r * deriv (frozenElliptic p u) x₀ * deriv A x₀
        - a * p.m * (W x₀) ^ r * deriv (frozenElliptic p u) x₀ * deriv W x₀ =
      (a * p.m * deriv (frozenElliptic p u) x₀) *
        ((A x₀) ^ r * deriv A x₀ - (W x₀) ^ r * deriv W x₀) := by
          ring
    _ ≤ |(a * p.m * deriv (frozenElliptic p u) x₀) *
        ((A x₀) ^ r * deriv A x₀ - (W x₀) ^ r * deriv W x₀)| :=
      le_abs_self _
    _ = |a * p.m * deriv (frozenElliptic p u) x₀| *
        |(A x₀) ^ r * deriv A x₀ - (W x₀) ^ r * deriv W x₀| :=
      abs_mul _ _
    _ ≤ (|a| * p.m * BVd) *
        (K * (r + 1) * M ^ r * (A x₀ - W x₀) + M ^ r * eta) :=
      mul_le_mul hKabs hbracket (abs_nonneg _)
        (mul_nonneg (mul_nonneg (abs_nonneg a) hm0) hBVd)
    _ = (|a| * p.m * BVd * K * p.m * M ^ (p.m - 1)) *
          (A x₀ - W x₀)
        + (|a| * p.m * BVd * M ^ (p.m - 1)) * eta := by
      dsimp [r]
      ring

/-- The complete paper-operator estimate at an approximate upper contact.
The frozen resolver value and gradient bounds are generated internally from
the global strip `0 ≤ q ≤ Q`; no monotonicity or wave-trap property of `q` is
assumed. -/
theorem paperWaveOperator_diff_le_of_upper_barrier_contact_abs
    (p : CMParams) {c Q M K eta : ℝ}
    {q A W : ℝ → ℝ} {x₀ : ℝ}
    (hQ : 0 ≤ Q) (hM : 0 < M) (hK : 0 ≤ K)
    (hq : IsCUnifBdd q) (hqQ : ∀ x, q x ∈ Set.Icc (0 : ℝ) Q)
    (hAmem : A x₀ ∈ Set.Icc (0 : ℝ) M)
    (hWmem : W x₀ ∈ Set.Icc (0 : ℝ) M)
    (hWA : W x₀ ≤ A x₀)
    (hAderiv : |deriv A x₀| ≤ K * A x₀)
    (hsecond : iteratedDeriv 2 A x₀ - iteratedDeriv 2 W x₀ ≤ eta)
    (hslope : |deriv A x₀ - deriv W x₀| ≤ eta) :
    paperWaveOperator p c q A x₀ - paperWaveOperator p c q W x₀ ≤
      (reactionLip p.α M + |p.χ| * (Q ^ p.γ) * rpowLip p.m M +
          |p.χ| * rpowLip (p.m + p.γ) M +
          |p.χ| * p.m * (Q ^ p.γ) * K * p.m * M ^ (p.m - 1)) *
          (A x₀ - W x₀)
        + (1 + |c| +
          |p.χ| * p.m * (Q ^ p.γ) * M ^ (p.m - 1)) * eta := by
  let Ccross : ℝ :=
    |p.χ| * p.m * (Q ^ p.γ) * K * p.m * M ^ (p.m - 1)
  let Ecross : ℝ :=
    |p.χ| * p.m * (Q ^ p.γ) * M ^ (p.m - 1)
  have hVnonneg : 0 ≤ frozenElliptic p q x₀ :=
    frozenElliptic_nonneg p (fun y => (hqQ y).1) x₀
  have hVbound : frozenElliptic p q x₀ ≤ Q ^ p.γ := by
    apply frozenElliptic_le_of_rpow_le p (Real.rpow_nonneg hQ p.γ)
      hq.1 (fun y => (hqQ y).1)
    intro y
    exact Real.rpow_le_rpow (hqQ y).1 (hqQ y).2
      (zero_le_one.trans p.hγ)
  have hVderiv : |deriv (frozenElliptic p q) x₀| ≤ Q ^ p.γ :=
    frozenElliptic_deriv_abs_le_rpow_of_Icc p hQ hq hqQ x₀
  have hcross :
      (-p.χ) * p.m * (A x₀) ^ (p.m - 1) *
            deriv (frozenElliptic p q) x₀ * deriv A x₀
        - (-p.χ) * p.m * (W x₀) ^ (p.m - 1) *
            deriv (frozenElliptic p q) x₀ * deriv W x₀ ≤
      Ccross * (A x₀ - W x₀) + Ecross * eta := by
    simpa [Ccross, Ecross, abs_neg] using
      paperCrossGradient_diff_le_of_upper_barrier_log_slope_abs
        (p := p) (a := -p.χ) (M := M) (BVd := Q ^ p.γ)
        (K := K) (eta := eta) (u := q) (A := A) (W := W) (x₀ := x₀)
        hM (Real.rpow_nonneg hQ p.γ) hK hWmem.1 hWA hAmem.2
        hVderiv hAderiv hslope
  have hop := paperWaveOperator_diff_le_abs_of_approx_contact
    (p := p) (c := c) (a := -p.χ) (M := M) (BV := Q ^ p.γ)
    (Ccross := Ccross) (Ecross := Ecross) (eta := eta)
    (u := q) (A := A) (W := W) (x₀ := x₀)
    rfl hM.le hAmem hWmem hWA hVnonneg hVbound hsecond hslope hcross
  simpa [Ccross, Ecross, abs_neg] using hop

/-- Away from its unique `C¹` splice, the patched lower barrier has a
uniform logarithmic-slope bound on both branches.  The constant branch is
trivial; the decreasing branch uses the raw two-exponential estimate. -/
theorem lowerBarrierPlateau_deriv_abs_le_mul_away
    {kappa kappaTilde D x : ℝ}
    (hkappa : 0 < kappa) (hgap : 0 < kappaTilde - kappa)
    (hD : 0 < D) (hx : x ≠ lowerBarrierXPlus kappa kappaTilde D) :
    |deriv (lowerBarrierPlateau kappa kappaTilde D) x| ≤
      kappaTilde * lowerBarrierPlateau kappa kappaTilde D x := by
  rcases lt_or_gt_of_ne hx with hxlt | hxgt
  · have heq := lowerBarrierPlateau_eventuallyEq_const_of_lt hxlt
    rw [heq.deriv_eq]
    simp only [deriv_const, abs_zero]
    exact mul_nonneg (by linarith)
      (lowerBarrierPlateau_pos hkappa hgap hD x).le
  · have heq := lowerBarrierPlateau_eventuallyEq_raw_of_gt hxgt
    rw [heq.deriv_eq, lowerBarrierPlateau_eq_raw_of_xplus_lt hxgt]
    exact lowerBarrierRaw_deriv_abs_le_mul_of_xplus_le
      hkappa hgap hD hxgt.le

/-- Approximate-contact operator bound for the patched plateau away from its
splice.  The current slice needs only the global strip `0 ≤ q ≤ Q`; in
particular it need not lie in a wave trap. -/
theorem paperWaveOperator_lowerBarrierPlateau_diff_le_of_approx_contact_abs
    (p : CMParams) {c Q M kappa kappaTilde D eta x : ℝ}
    {q : ℝ → ℝ}
    (hQ : 0 ≤ Q) (hM : 0 < M)
    (hq : IsCUnifBdd q) (hqQ : ∀ y, q y ∈ Set.Icc (0 : ℝ) Q)
    (hkappa : 0 < kappa) (hgap : 0 < kappaTilde - kappa)
    (hD : 0 < D)
    (hx : x ≠ lowerBarrierXPlus kappa kappaTilde D)
    (hAM : lowerBarrierPlateau kappa kappaTilde D x ≤ M)
    (hcontact : q x ≤ lowerBarrierPlateau kappa kappaTilde D x)
    (hsecond :
      iteratedDeriv 2 (lowerBarrierPlateau kappa kappaTilde D) x -
        iteratedDeriv 2 q x ≤ eta)
    (hslope :
      |deriv (lowerBarrierPlateau kappa kappaTilde D) x - deriv q x| ≤ eta) :
    paperWaveOperator p c q (lowerBarrierPlateau kappa kappaTilde D) x -
        paperWaveOperator p c q q x ≤
      (reactionLip p.α M + |p.χ| * (Q ^ p.γ) * rpowLip p.m M +
          |p.χ| * rpowLip (p.m + p.γ) M +
          |p.χ| * p.m * (Q ^ p.γ) * kappaTilde * p.m *
            M ^ (p.m - 1)) *
          (lowerBarrierPlateau kappa kappaTilde D x - q x)
        + (1 + |c| +
          |p.χ| * p.m * (Q ^ p.γ) * M ^ (p.m - 1)) * eta := by
  have hA0 : 0 ≤ lowerBarrierPlateau kappa kappaTilde D x :=
    (lowerBarrierPlateau_pos hkappa hgap hD x).le
  have hqM : q x ∈ Set.Icc (0 : ℝ) M :=
    ⟨(hqQ x).1, hcontact.trans hAM⟩
  exact paperWaveOperator_diff_le_of_upper_barrier_contact_abs
    p hQ hM (by linarith : 0 ≤ kappaTilde) hq hqQ
    ⟨hA0, hAM⟩ hqM hcontact
    (lowerBarrierPlateau_deriv_abs_le_mul_away hkappa hgap hD hx)
    hsecond hslope

/-- Splice-side version using the constant profile with the plateau value.
Both first derivatives vanish at contact, so the cross-gradient gap cost is
zero and only its universal `eta` cost remains. -/
theorem paperWaveOperator_const_diff_le_of_approx_contact_abs
    (p : CMParams) {c Q M d eta x : ℝ}
    {q : ℝ → ℝ}
    (hQ : 0 ≤ Q) (hM : 0 < M) (heta : 0 ≤ eta)
    (hq : IsCUnifBdd q) (hqQ : ∀ y, q y ∈ Set.Icc (0 : ℝ) Q)
    (hd : d ∈ Set.Icc (0 : ℝ) M) (hcontact : q x ≤ d)
    (hqx : deriv q x = 0)
    (hsecond : -iteratedDeriv 2 q x ≤ eta) :
    paperWaveOperator p c q (fun _ : ℝ => d) x -
        paperWaveOperator p c q q x ≤
      (reactionLip p.α M + |p.χ| * (Q ^ p.γ) * rpowLip p.m M +
          |p.χ| * rpowLip (p.m + p.γ) M) * (d - q x)
        + (1 + |c| +
          |p.χ| * p.m * (Q ^ p.γ) * M ^ (p.m - 1)) * eta := by
  have hqM : q x ∈ Set.Icc (0 : ℝ) M :=
    ⟨(hqQ x).1, hcontact.trans hd.2⟩
  have hAderiv : |deriv (fun _ : ℝ => d) x| ≤ 0 * d := by simp
  have hslope : |deriv (fun _ : ℝ => d) x - deriv q x| ≤ eta := by
    simp [hqx, heta]
  have hsecond' :
      iteratedDeriv 2 (fun _ : ℝ => d) x - iteratedDeriv 2 q x ≤ eta := by
    simpa only [iteratedDeriv_const, show (2 : ℕ) ≠ 0 by norm_num,
      ite_false, zero_sub] using hsecond
  have hop := paperWaveOperator_diff_le_of_upper_barrier_contact_abs
    p (c := c) (Q := Q) (M := M) (K := 0) (eta := eta)
    (q := q) (A := fun _ : ℝ => d) (W := q) (x₀ := x)
    hQ hM (show 0 ≤ (0 : ℝ) by norm_num) hq hqQ hd hqM
    hcontact hAderiv hsecond' hslope
  simpa using hop

section AxiomAudit

#print axioms paperCrossGradient_diff_le_of_upper_barrier_log_slope_abs
#print axioms paperWaveOperator_diff_le_of_upper_barrier_contact_abs
#print axioms lowerBarrierPlateau_deriv_abs_le_mul_away
#print axioms paperWaveOperator_lowerBarrierPlateau_diff_le_of_approx_contact_abs
#print axioms paperWaveOperator_const_diff_le_of_approx_contact_abs

end AxiomAudit

end ShenWork.Paper1
