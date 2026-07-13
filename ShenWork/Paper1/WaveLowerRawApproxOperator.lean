import ShenWork.Paper1.WavePaperApproxOperator
import ShenWork.Paper1.WaveWeightedCuspLemma
import ShenWork.Paper1.WaveLemma42Paper
import ShenWork.Paper1.WaveLowerRawTailfree

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-- Multiplication by the upper endpoint removes the cusp of `s ↦ s^r` for
every `r ≥ 0`.  The concave regime uses `weighted_rpow_increment_le`; the
convex regime uses the ordinary explicit Lipschitz constant. -/
theorem upper_weighted_rpow_increment_le
    {r M w A : ℝ} (hr : 0 ≤ r) (hM : 0 < M)
    (hw : 0 ≤ w) (hwa : w ≤ A) (hAM : A ≤ M) :
    A * (A ^ r - w ^ r) ≤
      (r + 1) * M ^ r * (A - w) := by
  have hA0 : 0 ≤ A := le_trans hw hwa
  have hgap : 0 ≤ A - w := sub_nonneg.mpr hwa
  have hpowdiff : 0 ≤ A ^ r - w ^ r :=
    sub_nonneg.mpr (Real.rpow_le_rpow hw hwa hr)
  rcases eq_or_lt_of_le hr with hr0 | hrpos
  · subst r
    simpa using hgap
  by_cases hr1 : r < 1
  · have hweighted := weighted_rpow_increment_le
      hrpos hr1 hM hw hgap (by linarith : w + (A - w) ≤ M)
    have hweighted' :
        w * (A ^ r - w ^ r) ≤ r * M ^ r * (A - w) := by
      simpa [show w + (A - w) = A by ring] using hweighted
    have hApow : A ^ r ≤ M ^ r :=
      Real.rpow_le_rpow hA0 hAM hr
    have hwpow0 : 0 ≤ w ^ r := Real.rpow_nonneg hw r
    have hdiff_le : A ^ r - w ^ r ≤ M ^ r := by linarith
    have hgap_part :
        (A - w) * (A ^ r - w ^ r) ≤ (A - w) * M ^ r :=
      mul_le_mul_of_nonneg_left hdiff_le hgap
    have hsplit :
        A * (A ^ r - w ^ r) =
          w * (A ^ r - w ^ r) +
            (A - w) * (A ^ r - w ^ r) := by ring
    rw [hsplit]
    calc
      w * (A ^ r - w ^ r) +
            (A - w) * (A ^ r - w ^ r) ≤
          r * M ^ r * (A - w) + (A - w) * M ^ r :=
        add_le_add hweighted' hgap_part
      _ = (r + 1) * M ^ r * (A - w) := by ring
  · have hrone : 1 ≤ r := le_of_not_gt hr1
    have hwmem : w ∈ Set.Icc (0 : ℝ) M := ⟨hw, le_trans hwa hAM⟩
    have hAmem : A ∈ Set.Icc (0 : ℝ) M := ⟨hA0, hAM⟩
    have hinc := rpow_increment_le_rpowLip hrone hM.le hwmem hAmem hwa
    have hfirst :
        A * (A ^ r - w ^ r) ≤
          A * (rpowLip r M * (A - w)) :=
      mul_le_mul_of_nonneg_left hinc hA0
    have hsecond :
        A * (rpowLip r M * (A - w)) ≤
          M * (rpowLip r M * (A - w)) := by
      exact mul_le_mul_of_nonneg_right hAM
        (mul_nonneg (rpowLip_nonneg hrone hM.le) hgap)
    have hMr : M * M ^ (r - 1) = M ^ r :=
      mul_rpow_sub_one r hrone hM.le
    have hrewrite :
        M * (rpowLip r M * (A - w)) =
          r * M ^ r * (A - w) := by
      unfold rpowLip
      rw [← hMr]
      ring
    have hcoef :
        r * M ^ r * (A - w) ≤
          (r + 1) * M ^ r * (A - w) := by
      have hpow0 : 0 ≤ M ^ r := Real.rpow_nonneg hM.le r
      nlinarith [mul_nonneg hpow0 hgap]
    exact hfirst.trans (hsecond.trans (by simpa [hrewrite] using hcoef))

/-- On the decreasing side of the two-exponential raw barrier, its logarithmic
slope is bounded by `κtilde`. -/
theorem lowerBarrierRaw_deriv_abs_le_mul_of_xplus_le
    {κ κtilde D x : ℝ}
    (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (hx : lowerBarrierXPlus κ κtilde D ≤ x) :
    |deriv (lowerBarrierRaw κ κtilde D) x| ≤
      κtilde * lowerBarrierRaw κ κtilde D x := by
  have hderiv : deriv (lowerBarrierRaw κ κtilde D) x ≤ 0 :=
    lowerBarrierRaw_deriv_nonpos_of_xplus_le hκ hgap hD hx
  have hκtilde : 0 < κtilde := by linarith
  rw [abs_of_nonpos hderiv, lowerBarrierRaw_deriv]
  unfold lowerBarrierRaw
  have hE : 0 < Real.exp (-κ * x) := Real.exp_pos _
  nlinarith

/-- Approximate-contact bound for the cross-frozen gradient term against the
raw lower barrier.  The increasing side has the favorable sign.  On the
decreasing side, the logarithmic slope and the weighted cusp lemma yield a
uniform coefficient even when `1 < m < 2`. -/
theorem lowerBarrierRaw_crossGradient_diff_le
    {p : CMParams} {a M κ κtilde D BVd eta : ℝ}
    {u W : ℝ → ℝ} {x₀ : ℝ}
    (ha : a = -p.χ) (hχ : p.χ ≤ 0)
    (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (hM : 0 < M) (hBVd : 0 ≤ BVd)
    (hW0 : 0 ≤ W x₀)
    (hWA : W x₀ ≤ lowerBarrierRaw κ κtilde D x₀)
    (hAM : lowerBarrierRaw κ κtilde D x₀ ≤ M)
    (hVp : deriv (frozenElliptic p u) x₀ ≤ 0)
    (hVpabs : |deriv (frozenElliptic p u) x₀| ≤ BVd)
    (hslope :
      |deriv (lowerBarrierRaw κ κtilde D) x₀ - deriv W x₀| ≤ eta) :
    a * p.m * (lowerBarrierRaw κ κtilde D x₀) ^ (p.m - 1) *
          deriv (frozenElliptic p u) x₀ *
          deriv (lowerBarrierRaw κ κtilde D) x₀
      - a * p.m * (W x₀) ^ (p.m - 1) *
          deriv (frozenElliptic p u) x₀ * deriv W x₀ ≤
      (a * p.m * BVd * κtilde * p.m * M ^ (p.m - 1)) *
          (lowerBarrierRaw κ κtilde D x₀ - W x₀)
        + (a * p.m * BVd * M ^ (p.m - 1)) * eta := by
  let A := lowerBarrierRaw κ κtilde D x₀
  let r := p.m - 1
  let vp := deriv (frozenElliptic p u) x₀
  let ds := deriv (lowerBarrierRaw κ κtilde D) x₀ - deriv W x₀
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hr0 : 0 ≤ r := by dsimp [r]; linarith [p.hm]
  have hA0 : 0 ≤ A := le_trans hW0 hWA
  have hgap0 : 0 ≤ A - W x₀ := sub_nonneg.mpr hWA
  have hAr0 : 0 ≤ A ^ r := Real.rpow_nonneg hA0 r
  have hWr0 : 0 ≤ (W x₀) ^ r := Real.rpow_nonneg hW0 r
  have hpowmono : (W x₀) ^ r ≤ A ^ r :=
    Real.rpow_le_rpow hW0 hWA hr0
  have hpowdiff0 : 0 ≤ A ^ r - (W x₀) ^ r := sub_nonneg.mpr hpowmono
  have hArM : A ^ r ≤ M ^ r := Real.rpow_le_rpow hA0 hAM hr0
  have hWrM : (W x₀) ^ r ≤ M ^ r := hpowmono.trans hArM
  have hds : |ds| ≤ eta := by simpa [ds, A] using hslope
  have hKnonpos : a * p.m * vp ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha0 hm0) hVp
  have hKabs : |a * p.m * vp| ≤ a * p.m * BVd := by
    rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hm0]
    exact mul_le_mul_of_nonneg_left hVpabs (mul_nonneg ha0 hm0)
  have hsplit :
      A ^ r * deriv (lowerBarrierRaw κ κtilde D) x₀ -
          (W x₀) ^ r * deriv W x₀ =
        (A ^ r - (W x₀) ^ r) *
            deriv (lowerBarrierRaw κ κtilde D) x₀ +
          (W x₀) ^ r * ds := by
    dsimp [ds]
    ring
  have hleft_eq :
      a * p.m * A ^ r * vp *
            deriv (lowerBarrierRaw κ κtilde D) x₀
        - a * p.m * (W x₀) ^ r * vp * deriv W x₀ =
      (a * p.m * vp) *
        (A ^ r * deriv (lowerBarrierRaw κ κtilde D) x₀ -
          (W x₀) ^ r * deriv W x₀) := by ring
  rw [show lowerBarrierRaw κ κtilde D x₀ = A by rfl, hleft_eq, hsplit]
  by_cases hx : x₀ ≤ lowerBarrierXPlus κ κtilde D
  · have hAderiv :
        0 ≤ deriv (lowerBarrierRaw κ κtilde D) x₀ :=
      lowerBarrierRaw_deriv_nonneg_of_le_xplus hκ hgap hD hx
    have hgood :
        (a * p.m * vp) *
            ((A ^ r - (W x₀) ^ r) *
              deriv (lowerBarrierRaw κ κtilde D) x₀) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hKnonpos
        (mul_nonneg hpowdiff0 hAderiv)
    have herr :
        (a * p.m * vp) * ((W x₀) ^ r * ds) ≤
          (a * p.m * BVd * M ^ r) * eta := by
      calc
        (a * p.m * vp) * ((W x₀) ^ r * ds) ≤
            |(a * p.m * vp) * ((W x₀) ^ r * ds)| := le_abs_self _
        _ = |a * p.m * vp| * ((W x₀) ^ r * |ds|) := by
          simp only [abs_mul, abs_of_nonneg hWr0]
        _ ≤ (a * p.m * BVd) * (M ^ r * eta) :=
          mul_le_mul hKabs
            (mul_le_mul hWrM hds (abs_nonneg ds)
              (Real.rpow_nonneg hM.le r))
            (mul_nonneg hWr0 (abs_nonneg ds))
            (mul_nonneg (mul_nonneg ha0 hm0) hBVd)
        _ = (a * p.m * BVd * M ^ r) * eta := by ring
    have hCnonneg : 0 ≤ a * p.m * BVd * κtilde * p.m * M ^ r := by
      have hκtilde : 0 ≤ κtilde := by linarith
      positivity
    nlinarith [mul_nonneg hCnonneg hgap0]
  · have hx' : lowerBarrierXPlus κ κtilde D ≤ x₀ := le_of_not_ge hx
    have hAderivAbs :
        |deriv (lowerBarrierRaw κ κtilde D) x₀| ≤ κtilde * A := by
      simpa [A] using
        lowerBarrierRaw_deriv_abs_le_mul_of_xplus_le hκ hgap hD hx'
    have hweighted :
        A * (A ^ r - (W x₀) ^ r) ≤
          (r + 1) * M ^ r * (A - W x₀) :=
      upper_weighted_rpow_increment_le hr0 hM hW0 hWA hAM
    have hrm : r + 1 = p.m := by dsimp [r]; ring
    rw [hrm] at hweighted
    have hterm1abs :
        |(A ^ r - (W x₀) ^ r) *
            deriv (lowerBarrierRaw κ κtilde D) x₀| ≤
          κtilde * p.m * M ^ r * (A - W x₀) := by
      rw [abs_mul, abs_of_nonneg hpowdiff0]
      have hκtilde : 0 ≤ κtilde := by linarith
      calc
        (A ^ r - (W x₀) ^ r) *
              |deriv (lowerBarrierRaw κ κtilde D) x₀| ≤
            (A ^ r - (W x₀) ^ r) * (κtilde * A) :=
          mul_le_mul_of_nonneg_left hAderivAbs hpowdiff0
        _ = κtilde * (A * (A ^ r - (W x₀) ^ r)) := by ring
        _ ≤ κtilde * (p.m * M ^ r * (A - W x₀)) :=
          mul_le_mul_of_nonneg_left hweighted hκtilde
        _ = κtilde * p.m * M ^ r * (A - W x₀) := by ring
    have hbracketAbs :
        |(A ^ r - (W x₀) ^ r) *
              deriv (lowerBarrierRaw κ κtilde D) x₀ +
            (W x₀) ^ r * ds| ≤
          κtilde * p.m * M ^ r * (A - W x₀) + M ^ r * eta := by
      have hterm1abs' :
          |A ^ r - (W x₀) ^ r| *
              |deriv (lowerBarrierRaw κ κtilde D) x₀| ≤
            κtilde * p.m * M ^ r * (A - W x₀) := by
        simpa only [abs_mul] using hterm1abs
      calc
        |(A ^ r - (W x₀) ^ r) *
              deriv (lowerBarrierRaw κ κtilde D) x₀ +
            (W x₀) ^ r * ds| ≤
            |(A ^ r - (W x₀) ^ r) *
              deriv (lowerBarrierRaw κ κtilde D) x₀| +
              |(W x₀) ^ r * ds| := abs_add_le _ _
        _ ≤ κtilde * p.m * M ^ r * (A - W x₀) + M ^ r * eta := by
          simp only [abs_mul, abs_of_nonneg hWr0]
          exact add_le_add hterm1abs'
            (mul_le_mul hWrM hds (abs_nonneg ds)
              (Real.rpow_nonneg hM.le r))
    calc
      (a * p.m * vp) *
          ((A ^ r - (W x₀) ^ r) *
              deriv (lowerBarrierRaw κ κtilde D) x₀ +
            (W x₀) ^ r * ds) ≤
          |(a * p.m * vp) *
            ((A ^ r - (W x₀) ^ r) *
                deriv (lowerBarrierRaw κ κtilde D) x₀ +
              (W x₀) ^ r * ds)| := le_abs_self _
      _ = |a * p.m * vp| *
          |(A ^ r - (W x₀) ^ r) *
                deriv (lowerBarrierRaw κ κtilde D) x₀ +
              (W x₀) ^ r * ds| := abs_mul _ _
      _ ≤ (a * p.m * BVd) *
          (κtilde * p.m * M ^ r * (A - W x₀) + M ^ r * eta) :=
        mul_le_mul hKabs hbracketAbs (abs_nonneg _)
          (mul_nonneg (mul_nonneg ha0 hm0) hBVd)
      _ = (a * p.m * BVd * κtilde * p.m * M ^ r) *
            (A - W x₀) +
          (a * p.m * BVd * M ^ r) * eta := by ring

/-- Uniform coefficient multiplying the lower-barrier contact gap. -/
def paperLowerRawApproxCcross
    (p : CMParams) (M κtilde : ℝ) : ℝ :=
  (-p.χ) * p.m * M ^ p.γ * κtilde * p.m * M ^ (p.m - 1)

/-- Uniform coefficient multiplying the penalization slope error. -/
def paperLowerRawApproxEcross
    (p : CMParams) (M : ℝ) : ℝ :=
  (-p.χ) * p.m * M ^ p.γ * M ^ (p.m - 1)

/-- Total strict-gap coefficient for the raw lower comparison. -/
def paperLowerRawApproxCmono
    (p : CMParams) (M κtilde : ℝ) : ℝ :=
  reactionLip p.α M
    + (-p.χ) * M ^ p.γ * rpowLip p.m M
    + paperLowerRawApproxCcross p M κtilde

/-- Total coefficient of the approximate maximum errors. -/
def paperLowerRawApproxE
    (p : CMParams) (c M : ℝ) : ℝ :=
  1 + |c| + paperLowerRawApproxEcross p M

/-- The automatic source box, the weighted cusp estimate, and the explicit raw
barrier slope produce all local operator data.  Only the scalar strict gap with
`lam` remains. -/
def paperLowerRawStepApproxOperatorData_of_conditions
    {p : CMParams} {c lam M κ κtilde D : ℝ} {u W : ℝ → ℝ}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hW2 : ContDiff ℝ 2 W)
    (hWnonneg : ∀ x, 0 ≤ W x)
    (hWbar : ∀ x, W x ≤ upperBarrier κ M x)
    (hsmall :
      (1 / lam) * paperLowerRawApproxCmono p M κtilde < 1) :
    PaperLowerRawStepApproxOperatorData p c lam κ κtilde D u W := by
  let a : ℝ := -p.χ
  let BV : ℝ := M ^ p.γ
  let Ccross : ℝ := paperLowerRawApproxCcross p M κtilde
  let Ecross : ℝ := paperLowerRawApproxEcross p M
  let Cmono : ℝ := paperLowerRawApproxCmono p M κtilde
  let E : ℝ := paperLowerRawApproxE p c M
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hcond.hM
  have hDpos : 0 < D := D_pos_of_paperDMin_lt hcond hD
  have hgap : 0 < κtilde - κ := sub_pos.mpr hcond.hgap
  have ha0 : 0 ≤ a := by dsimp [a]; linarith [hcond.hχ]
  have hBV0 : 0 ≤ BV := by
    dsimp [BV]
    exact Real.rpow_nonneg hMpos.le p.γ
  have hbox : ShenWork.Paper1.PaperFrozenEllipticSourceBox p κ M :=
    ShenWork.Paper1.paperFrozenEllipticSourceBox_of_conditions hcond
  have hExpM :
      Real.exp (-κ * lowerBarrierXPlus κ κtilde D) ≤ M :=
    lowerBarrierExpXPlus_le_one_of_one_le_D hcond.hκ0 hgap
      hD_ge_one hcond.hM
  refine
    { Cmono := Cmono
      E := E
      small := by simpa [Cmono] using hsmall
      E_nonneg := ?_
      op_approx := ?_ }
  · dsimp [E, paperLowerRawApproxE, Ecross,
      paperLowerRawApproxEcross]
    have hnegχ : 0 ≤ -p.χ := by linarith [hcond.hχ]
    have hm : 0 ≤ p.m := le_trans zero_le_one p.hm
    have hpowγ : 0 ≤ M ^ p.γ := Real.rpow_nonneg hMpos.le _
    have hpowm : 0 ≤ M ^ (p.m - 1) := Real.rpow_nonneg hMpos.le _
    have hterm :
        0 ≤ (-p.χ) * p.m * M ^ p.γ * M ^ (p.m - 1) := by
      positivity
    linarith [abs_nonneg c]
  · intro eta heta x₀ hcontact hfSlope hfSecond
    let A : ℝ → ℝ := lowerBarrierRaw κ κtilde D
    have hWA : W x₀ ≤ A x₀ := by
      dsimp [A]
      linarith
    have hA0 : 0 ≤ A x₀ := le_trans (hWnonneg x₀) hWA
    have hAraw :
        lowerBarrierRaw κ κtilde D x₀ ≤
          lowerBarrierPlateau κ κtilde D x₀ :=
      lowerBarrierRaw_le_plateau hcond.hκ0 hgap hDpos x₀
    have hAexp :
        lowerBarrierPlateau κ κtilde D x₀ ≤
          Real.exp (-κ * lowerBarrierXPlus κ κtilde D) :=
      lowerBarrierPlateau_le_exp_xplus hcond.hκ0.le hDpos.le x₀
    have hAM : A x₀ ≤ M := by
      dsimp [A]
      exact hAraw.trans (hAexp.trans hExpM)
    have hWmem : W x₀ ∈ Set.Icc (0 : ℝ) M :=
      ⟨hWnonneg x₀,
        (hWbar x₀).trans (upperBarrier_le_M κ M x₀)⟩
    have hAmem : A x₀ ∈ Set.Icc (0 : ℝ) M := ⟨hA0, hAM⟩
    have hraw2 : ContDiff ℝ 2 A := by
      dsimp [A]
      unfold lowerBarrierRaw
      fun_prop
    have hslope : |deriv A x₀ - deriv W x₀| ≤ eta := by
      have heq :
          deriv (fun x => A x - W x) x₀ =
            deriv A x₀ - deriv W x₀ :=
        deriv_sub (hraw2.differentiable (by norm_num) x₀)
          (hW2.differentiable (by norm_num) x₀)
      rw [show (fun x => lowerBarrierRaw κ κtilde D x - W x) =
          (fun x => A x - W x) by rfl, heq] at hfSlope
      exact hfSlope.le
    have hsecond :
        iteratedDeriv 2 A x₀ - iteratedDeriv 2 W x₀ ≤ eta := by
      have heq :
          deriv (deriv (fun x => A x - W x)) x₀ =
            iteratedDeriv 2 A x₀ - iteratedDeriv 2 W x₀ := by
        calc
          deriv (deriv (fun x => A x - W x)) x₀ =
              iteratedDeriv 2 (fun x => A x - W x) x₀ := by
            simp [iteratedDeriv_succ, iteratedDeriv_zero]
          _ = iteratedDeriv 2 A x₀ - iteratedDeriv 2 W x₀ :=
            iteratedDeriv_fun_sub hraw2.contDiffAt hW2.contDiffAt
      rw [show (fun x => lowerBarrierRaw κ κtilde D x - W x) =
          (fun x => A x - W x) by rfl, heq] at hfSecond
      exact hfSecond.le
    have hcross :
        a * p.m * (A x₀) ^ (p.m - 1) *
              deriv (frozenElliptic p u) x₀ * deriv A x₀
          - a * p.m * (W x₀) ^ (p.m - 1) *
              deriv (frozenElliptic p u) x₀ * deriv W x₀ ≤
        Ccross * (A x₀ - W x₀) + Ecross * eta := by
      simpa [a, A, Ccross, Ecross, paperLowerRawApproxCcross,
          paperLowerRawApproxEcross] using
        lowerBarrierRaw_crossGradient_diff_le
          (p := p) (a := a) (M := M) (κ := κ) (κtilde := κtilde)
          (D := D) (BVd := BV) (eta := eta) (u := u) (W := W)
          (x₀ := x₀) rfl hcond.hχ hcond.hκ0 hgap hDpos hMpos hBV0
          (hWnonneg x₀) hWA hAM
          ((hbox.antitone u hu).deriv_nonpos)
          (hbox.deriv_abs_le u hu x₀) hslope
    simpa [A, a, BV, Ccross, Ecross, Cmono, E,
        paperLowerRawApproxCmono, paperLowerRawApproxE,
        paperLowerRawApproxCcross, paperLowerRawApproxEcross] using
      paperWaveOperator_diff_le_of_approx_contact
        (p := p) (c := c) (a := a) (M := M) (BV := BV)
        (Ccross := Ccross) (Ecross := Ecross) (eta := eta)
        (u := u) (A := A) (W := W) (x₀ := x₀)
        rfl hcond.hχ hMpos.le hAmem hWmem hWA
        (hbox.value_nonneg u hu x₀) (hbox.value_le u hu x₀)
        hsecond hslope hcross

section AxiomAudit

#print axioms upper_weighted_rpow_increment_le
#print axioms lowerBarrierRaw_deriv_abs_le_mul_of_xplus_le
#print axioms lowerBarrierRaw_crossGradient_diff_le
#print axioms paperLowerRawStepApproxOperatorData_of_conditions

end AxiomAudit

end ShenWork.Paper1
