import ShenWork.Paper1.Theorem12Section5Budgets
import ShenWork.Paper1.Theorem12LogDerivative
import ShenWork.Paper1.WaveRotheStep

noncomputable section

namespace ShenWork.Paper1

/-!
# The exact mean-value coefficients in Paper 1 (5.18)

The paper writes its coefficient `a_beta` as the integral of the derivative
of `s ↦ s^beta` along the segment joining the Cauchy solution and the wave.
For the energy calculation, the canonical secant form below is equivalent and
has the defining difference identity without an additional integral layer.
-/

/-- Canonical mean-value coefficient for the real power `s ↦ s^beta`.
At coincident endpoints it is filled by the derivative value. -/
def paper5MeanCoefficient (beta s r : ℝ) : ℝ :=
  if s = r then beta * s ^ (beta - 1)
  else (s ^ beta - r ^ beta) / (s - r)

/-- The integral presentation used literally in Paper 1. -/
def paper5IntegralMeanCoefficient (beta s r : ℝ) : ℝ :=
  ∫ tau : ℝ in 0..1,
    beta * (tau * s + (1 - tau) * r) ^ (beta - 1)

theorem paper5MeanCoefficient_mul_sub (beta s r : ℝ) :
    paper5MeanCoefficient beta s r * (s - r) = s ^ beta - r ^ beta := by
  by_cases hsr : s = r
  · simp [paper5MeanCoefficient, hsr]
  · rw [paper5MeanCoefficient, if_neg hsr, div_mul_cancel₀]
    exact sub_ne_zero.mpr hsr

/-- For powers at least one, the canonical coefficient agrees with the
literal segment integral in the paper. -/
theorem paper5IntegralMeanCoefficient_eq
    {beta s r : ℝ} (hbeta : 1 ≤ beta) :
    paper5IntegralMeanCoefficient beta s r =
      paper5MeanCoefficient beta s r := by
  let path : ℝ → ℝ := fun tau => r + tau * (s - r)
  let pathDeriv : ℝ → ℝ := fun tau =>
    (beta * path tau ^ (beta - 1)) * (s - r)
  have hpath : ∀ tau : ℝ, HasDerivAt path (s - r) tau := by
    intro tau
    dsimp [path]
    convert (hasDerivAt_const tau r).add
      ((hasDerivAt_id tau).mul_const (s - r)) using 1 <;> ring
  have hderiv : ∀ tau ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun z => path z ^ beta) (pathDeriv tau) tau := by
    intro tau _htau
    dsimp [pathDeriv]
    convert (hpath tau).rpow_const (Or.inr hbeta) using 1 <;> ring
  have hpath_cont : Continuous path := by
    dsimp [path]
    fun_prop
  have hpow_cont : Continuous (fun tau => path tau ^ (beta - 1)) :=
    hpath_cont.rpow_const (fun _ => Or.inr (by linarith))
  have hint : IntervalIntegrable pathDeriv MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    dsimp [pathDeriv]
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hmul :
      paper5IntegralMeanCoefficient beta s r * (s - r) =
        s ^ beta - r ^ beta := by
    rw [paper5IntegralMeanCoefficient]
    rw [← intervalIntegral.integral_mul_const]
    convert hftc using 1
    · apply intervalIntegral.integral_congr
      intro tau _htau
      dsimp [pathDeriv, path]
      congr 2
      ring
    · dsimp [path]
      ring_nf
  by_cases hsr : s = r
  · subst r
    rw [paper5IntegralMeanCoefficient, paper5MeanCoefficient, if_pos rfl]
    have hfun :
        (fun tau : ℝ =>
          beta * (tau * s + (1 - tau) * s) ^ (beta - 1)) =
          fun _tau : ℝ => beta * s ^ (beta - 1) := by
      funext tau
      congr 2
      ring
    rw [hfun, intervalIntegral.integral_const]
    simp
  · apply mul_right_cancel₀ (sub_ne_zero.mpr hsr)
    rw [hmul, paper5MeanCoefficient_mul_sub]

theorem paper5MeanCoefficient_nonneg
    {beta M s r : ℝ} (hbeta : 1 ≤ beta) (_hM : 0 ≤ M)
    (hs : s ∈ Set.Icc (0 : ℝ) M) (hr : r ∈ Set.Icc (0 : ℝ) M) :
    0 ≤ paper5MeanCoefficient beta s r := by
  by_cases hsr : s = r
  · rw [paper5MeanCoefficient, if_pos hsr]
    exact mul_nonneg (le_trans zero_le_one hbeta)
      (Real.rpow_nonneg hs.1 _)
  · rw [paper5MeanCoefficient, if_neg hsr]
    rcases lt_or_gt_of_ne hsr with hlt | hgt
    · exact div_nonneg_of_nonpos
        (sub_nonpos.mpr (Real.rpow_le_rpow hs.1 hlt.le
          (le_trans zero_le_one hbeta)))
        (sub_nonpos.mpr hlt.le)
    · exact div_nonneg
        (sub_nonneg.mpr (Real.rpow_le_rpow hr.1 hgt.le
          (le_trans zero_le_one hbeta)))
        (sub_nonneg.mpr hgt.le)

theorem paper5MeanCoefficient_abs_le
    {beta M s r : ℝ} (hbeta : 1 ≤ beta) (hM : 0 ≤ M)
    (hs : s ∈ Set.Icc (0 : ℝ) M) (hr : r ∈ Set.Icc (0 : ℝ) M) :
    |paper5MeanCoefficient beta s r| ≤ beta * M ^ (beta - 1) := by
  have hLip := rpow_m_lipschitz_on_Icc hbeta hM
  have hL0 : 0 ≤ rpowLip beta M := rpowLip_nonneg hbeta hM
  have hdist := hLip hs hr
  rw [edist_dist, edist_dist] at hdist
  have hpow : |s ^ beta - r ^ beta| ≤ rpowLip beta M * |s - r| := by
    have hdist' : dist (s ^ beta) (r ^ beta) ≤
        (Real.toNNReal (rpowLip beta M) : ℝ) * dist s r := by
      rw [← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_le_ofReal_iff (by positivity)] at hdist
      exact hdist
    rw [Real.coe_toNNReal _ hL0] at hdist'
    simpa [Real.dist_eq] using hdist'
  by_cases hsr : s = r
  · rw [paper5MeanCoefficient, if_pos hsr, abs_of_nonneg
        (mul_nonneg (le_trans zero_le_one hbeta)
          (Real.rpow_nonneg hs.1 _))]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hs.1 hs.2 (by linarith))
      (le_trans zero_le_one hbeta)
  · rw [paper5MeanCoefficient, if_neg hsr, abs_div]
    apply (div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hsr))).2
    simpa [rpowLip] using hpow

theorem paper5MeanCoefficient_zero (s r : ℝ) :
    paper5MeanCoefficient 0 s r = 0 := by
  by_cases hsr : s = r
  · simp [paper5MeanCoefficient, hsr]
  · simp [paper5MeanCoefficient, hsr]

/-- For a sublinear positive power, the singular secant coefficient becomes
bounded after multiplication by its positive reference point.  This is the
algebraic cancellation used in Paper 1 (5.23). -/
theorem paper5MeanCoefficient_abs_mul_right_le_rpow
    {beta s r : ℝ} (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hs : 0 ≤ s) (hr : 0 < r) :
    |paper5MeanCoefficient beta s r| * r ≤ r ^ beta := by
  have hr0 : 0 ≤ r := hr.le
  have hrpow_pos : 0 < r ^ beta := Real.rpow_pos_of_pos hr _
  by_cases hsr : s = r
  · subst s
    rw [paper5MeanCoefficient, if_pos rfl, abs_of_nonneg
      (mul_nonneg hbeta0.le (Real.rpow_nonneg hr0 _))]
    have hmul : r * r ^ (beta - 1) = r ^ beta := by
      calc
        r * r ^ (beta - 1) = r ^ (1 : ℝ) * r ^ (beta - 1) := by
          rw [Real.rpow_one]
        _ = r ^ ((1 : ℝ) + (beta - 1)) :=
          (Real.rpow_add hr 1 (beta - 1)).symm
        _ = r ^ beta := by ring_nf
    rw [mul_assoc, mul_comm (r ^ (beta - 1)) r, hmul]
    simpa using
      (mul_le_mul_of_nonneg_right hbeta1 (Real.rpow_nonneg hr0 beta))
  · rw [paper5MeanCoefficient, if_neg hsr]
    rcases lt_or_gt_of_ne hsr with hlt | hgt
    · have hpow_le : s ^ beta ≤ r ^ beta :=
        Real.rpow_le_rpow hs hlt.le hbeta0.le
      have hrewrite : (s ^ beta - r ^ beta) / (s - r) =
          (r ^ beta - s ^ beta) / (r - s) := by
        field_simp [sub_ne_zero.mpr hsr, sub_ne_zero.mpr (Ne.symm hsr)]
        ring
      rw [hrewrite]
      rw [abs_of_nonneg (div_nonneg (sub_nonneg.mpr hpow_le)
        (sub_nonneg.mpr hlt.le)), div_mul_eq_mul_div]
      apply (div_le_iff₀ (sub_pos.mpr hlt)).2
      have hq0 : 0 ≤ s / r := div_nonneg hs hr0
      have hq1 : s / r ≤ 1 := (div_le_one hr).2 hlt.le
      have hqpow : s / r ≤ (s / r) ^ beta :=
        Real.self_le_rpow_of_le_one hq0 hq1 hbeta1
      rw [Real.div_rpow hs hr0] at hqpow
      have hcross : s * r ^ beta ≤ s ^ beta * r :=
        (div_le_div_iff₀ hr hrpow_pos).1 hqpow
      nlinarith
    · have hpow_le : r ^ beta ≤ s ^ beta :=
        Real.rpow_le_rpow hr0 hgt.le hbeta0.le
      rw [abs_of_nonneg (div_nonneg (sub_nonneg.mpr hpow_le)
        (sub_nonneg.mpr hgt.le))]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (sub_pos.mpr hgt)).2
      have hq1 : 1 ≤ s / r := by
        apply (le_div_iff₀ hr).2
        simpa using hgt.le
      have hqpow : (s / r) ^ beta ≤ s / r :=
        Real.rpow_le_self_of_one_le hq1 hbeta1
      rw [Real.div_rpow hs hr0] at hqpow
      have hcross : s ^ beta * r ≤ s * r ^ beta :=
        (div_le_div_iff₀ hrpow_pos hr).1 hqpow
      nlinarith

/-- The paper's space-time coefficient `a_beta(t,x)`. -/
def paper5A (beta : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ)
    (t x : ℝ) : ℝ :=
  paper5MeanCoefficient beta (u t x) (U x)

theorem paper5A_mul_sub
    (beta : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ) (t x : ℝ) :
    paper5A beta u U t x * (u t x - U x) =
      (u t x) ^ beta - (U x) ^ beta :=
  paper5MeanCoefficient_mul_sub beta (u t x) (U x)

/-- Coefficients `b_1,...,b_4` in (5.18). -/
def paper5B1 (p : CMParams) (u v : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  p.m * deriv (v t) x * (u t x) ^ (p.m - 1)

def paper5B2 (p : CMParams) (u v : ℝ → ℝ → ℝ) (U : ℝ → ℝ)
    (t x : ℝ) : ℝ :=
  p.m * deriv U x * deriv (v t) x * paper5A (p.m - 1) u U t x

def paper5B3 (p : CMParams) (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  p.m * (U x) ^ (p.m - 1) * deriv U x

def paper5B4 (p : CMParams) (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  (U x) ^ p.m

/-! ## The corrected chemotactic flux difference

There are two sign errors in the displayed equation (5.18) of the paper.
For the elliptic convention `vₓₓ - v + u^γ = 0`, the zero-order part of
`(u^m vₓ)ₓ - (U^m Vₓ)ₓ` contains
`v * a_m - a_{m+γ}`, not `v * a_m + a_{m+γ}`, and it contains
`+ U^m (v - V)`.  Consequently multiplication by `-χ` gives
`-χ * b₄ * (v - V)`, not `+χ * b₄ * (v - V)`.

The following identity is the algebraic core of the corrected (5.18).  It
is stated before invoking any derivative rule: the two arguments on the
left are exactly the product-rule expansions after substituting the two
elliptic equations. -/
theorem paper5ChemFluxDifference_expansion_corrected
    (p : CMParams) (u v : ℝ → ℝ → ℝ) (U V : ℝ → ℝ)
    (t x : ℝ) (hu : 0 ≤ u t x) (hU : 0 ≤ U x) :
    (p.m * (u t x) ^ (p.m - 1) * deriv (u t) x * deriv (v t) x +
          (u t x) ^ p.m * (v t x - (u t x) ^ p.γ)) -
        (p.m * (U x) ^ (p.m - 1) * deriv U x * deriv V x +
          (U x) ^ p.m * (V x - (U x) ^ p.γ)) =
      paper5B1 p u v t x * (deriv (u t) x - deriv U x) +
        (paper5B2 p u v U t x +
            v t x * paper5A p.m u U t x -
              paper5A (p.m + p.γ) u U t x) * (u t x - U x) +
        paper5B3 p U x * (deriv (v t) x - deriv V x) +
        paper5B4 p U x * (v t x - V x) := by
  have hm1 := paper5A_mul_sub (p.m - 1) u U t x
  have hm := paper5A_mul_sub p.m u U t x
  have hmg := paper5A_mul_sub (p.m + p.γ) u U t x
  have hupow : (u t x) ^ p.m * (u t x) ^ p.γ =
      (u t x) ^ (p.m + p.γ) :=
    (Real.rpow_add_of_nonneg hu
      (le_trans zero_le_one p.hm) (le_trans zero_le_one p.hγ)).symm
  have hUpow : (U x) ^ p.m * (U x) ^ p.γ =
      (U x) ^ (p.m + p.γ) :=
    (Real.rpow_add_of_nonneg hU
      (le_trans zero_le_one p.hm) (le_trans zero_le_one p.hγ)).symm
  unfold paper5B1 paper5B2 paper5B3 paper5B4
  linear_combination
    -(p.m * deriv (v t) x * deriv U x) * hm1 -
      v t x * hm + hmg - hupow + hUpow

/-- The corrected zero-order chemotactic coefficient in (5.18), before
multiplication by `-χ`. -/
def paper5CorrectedChemZeroCoefficient
    (p : CMParams) (u v : ℝ → ℝ → ℝ) (U : ℝ → ℝ)
    (t x : ℝ) : ℝ :=
  v t x * paper5A p.m u U t x - paper5A (p.m + p.γ) u U t x

/-- The sign-corrected replacement for the case-dependent estimate used
before (5.28).  Unlike the printed one-sided claim, this absolute estimate
is valid for both signs of `χ`; it has exactly the conservative
`(2m+γ) M^(m+γ-1)` size already retained in the final budget (5.33). -/
theorem paper5CorrectedChemZeroCoefficient_abs_le
    (p : CMParams) {M t x : ℝ}
    {u v : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hM : 0 ≤ M)
    (hu : u t x ∈ Set.Icc (0 : ℝ) M)
    (hU : U x ∈ Set.Icc (0 : ℝ) M)
    (hv : v t x ∈ Set.Icc (0 : ℝ) (M ^ p.γ)) :
    |paper5CorrectedChemZeroCoefficient p u v U t x| ≤
      (2 * p.m + p.γ) * M ^ (p.m + p.γ - 1) := by
  have ham :
      |paper5A p.m u U t x| ≤ p.m * M ^ (p.m - 1) := by
    exact paper5MeanCoefficient_abs_le p.hm hM hu hU
  have hamg :
      |paper5A (p.m + p.γ) u U t x| ≤
        (p.m + p.γ) * M ^ (p.m + p.γ - 1) := by
    exact paper5MeanCoefficient_abs_le (by linarith [p.hm, p.hγ]) hM hu hU
  have hvabs : |v t x| ≤ M ^ p.γ := by
    rw [abs_of_nonneg hv.1]
    exact hv.2
  have hfirst :
      |v t x| * |paper5A p.m u U t x| ≤
        M ^ p.γ * (p.m * M ^ (p.m - 1)) := by
    exact mul_le_mul hvabs ham (abs_nonneg _)
      (Real.rpow_nonneg hM _)
  unfold paper5CorrectedChemZeroCoefficient
  calc
    |v t x * paper5A p.m u U t x -
          paper5A (p.m + p.γ) u U t x|
        ≤ |v t x| * |paper5A p.m u U t x| +
            |paper5A (p.m + p.γ) u U t x| := by
          simpa [abs_mul] using
            (abs_sub (v t x * paper5A p.m u U t x)
              (paper5A (p.m + p.γ) u U t x))
    _ ≤ M ^ p.γ * (p.m * M ^ (p.m - 1)) +
          (p.m + p.γ) * M ^ (p.m + p.γ - 1) :=
      add_le_add hfirst hamg
    _ = (2 * p.m + p.γ) * M ^ (p.m + p.γ - 1) := by
      rw [show p.m + p.γ - 1 = p.γ + (p.m - 1) by ring,
        Real.rpow_add_of_nonneg hM
          (le_trans zero_le_one p.hγ) (by linarith [p.hm])]
      ring

theorem paper5B2_eq_zero_of_m_eq_one
    (p : CMParams) {u v : ℝ → ℝ → ℝ} {U : ℝ → ℝ} {t x : ℝ}
    (hm : p.m = 1) :
    paper5B2 p u v U t x = 0 := by
  simp [paper5B2, paper5A, hm, paper5MeanCoefficient_zero]

theorem paper5B2_abs_le_raw
    (p : CMParams) {Lu Lv La t x : ℝ}
    {u v : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hLu : 0 ≤ Lu) (hLv : 0 ≤ Lv)
    (hUx : |deriv U x| ≤ Lu) (hv : |deriv (v t) x| ≤ Lv)
    (ha : |paper5A (p.m - 1) u U t x| ≤ La) :
    |paper5B2 p u v U t x| ≤ p.m * Lu * Lv * La := by
  unfold paper5B2
  rw [abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (le_trans zero_le_one p.hm)]
  have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
  calc
    p.m * |deriv U x| * |deriv (v t) x| *
        |paper5A (p.m - 1) u U t x|
        ≤ p.m * Lu * |deriv (v t) x| *
            |paper5A (p.m - 1) u U t x| := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hUx hm0) (abs_nonneg _))
            (abs_nonneg _)
    _ ≤ p.m * Lu * Lv * |paper5A (p.m - 1) u U t x| := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hv (mul_nonneg hm0 hLu))
            (abs_nonneg _)
    _ ≤ p.m * Lu * Lv * La :=
      mul_le_mul_of_nonneg_left ha
        (mul_nonneg (mul_nonneg hm0 hLu) hLv)

theorem paper5B2_abs_le_of_two_le_m
    (p : CMParams) {M Lu t x : ℝ}
    {u v : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hm : 2 ≤ p.m) (hM : 0 ≤ M)
    (hu : u t x ∈ Set.Icc (0 : ℝ) M)
    (hU : U x ∈ Set.Icc (0 : ℝ) M)
    (hLu : 0 ≤ Lu) (hUx : |deriv U x| ≤ Lu)
    (hv : |deriv (v t) x| ≤ M ^ p.γ) :
    |paper5B2 p u v U t x| ≤
      p.m * Lu * (M ^ p.γ) * ((p.m - 1) * M ^ (p.m - 2)) := by
  apply paper5B2_abs_le_raw p
    (Lu := Lu) (Lv := M ^ p.γ)
    (La := (p.m - 1) * M ^ (p.m - 2))
    hLu (Real.rpow_nonneg hM _) hUx hv
  have ha :=
    paper5MeanCoefficient_abs_le (beta := p.m - 1)
      (M := M) (s := u t x) (r := U x)
      (hbeta := by linarith [hm]) hM hu hU
  change |paper5MeanCoefficient (p.m - 1) (u t x) (U x)| ≤ _
  convert ha using 1 <;> ring

/-- The `1 < m < 2` branch of Paper 1 (5.23).  The apparently singular
coefficient `a_{m-1}` is paired with `U'`; its singularity cancels against
the positive wave value and leaves only the absolute logarithmic derivative.
-/
theorem paper5B2_abs_le_of_one_lt_m_of_m_lt_two
    (p : CMParams) {M B t x : ℝ}
    {u v : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hm1 : 1 < p.m) (hm2 : p.m < 2)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hu : 0 ≤ u t x) (hUpos : 0 < U x) (hUle : U x ≤ M)
    (hv : |deriv (v t) x| ≤ M ^ p.γ)
    (hlog : |deriv U x / U x| ≤ B) :
    |paper5B2 p u v U t x| ≤
      p.m * M ^ (p.m + p.γ - 1) * B := by
  have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hMg0 : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM _
  have hU0 : 0 ≤ U x := hUpos.le
  have hcoef := paper5MeanCoefficient_abs_mul_right_le_rpow
    (beta := p.m - 1) (s := u t x) (r := U x)
    (by linarith) (by linarith) hu hUpos
  have hderiv_eq : |deriv U x| = |deriv U x / U x| * U x := by
    rw [abs_div, abs_of_pos hUpos]
    field_simp [ne_of_gt hUpos]
  have hpaired :
      |deriv U x| * |paper5A (p.m - 1) u U t x| ≤
        B * (U x) ^ (p.m - 1) := by
    change |deriv U x| *
        |paper5MeanCoefficient (p.m - 1) (u t x) (U x)| ≤ _
    rw [hderiv_eq]
    calc
      (|deriv U x / U x| * U x) *
          |paper5MeanCoefficient (p.m - 1) (u t x) (U x)| =
          |deriv U x / U x| *
            (|paper5MeanCoefficient (p.m - 1) (u t x) (U x)| * U x) := by
              ring
      _ ≤ B * (U x) ^ (p.m - 1) :=
        mul_le_mul hlog hcoef
          (mul_nonneg (abs_nonneg _) hU0) hB
  have hUpow_le : (U x) ^ (p.m - 1) ≤ M ^ (p.m - 1) :=
    Real.rpow_le_rpow hU0 hUle (by linarith)
  unfold paper5B2
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hm0]
  calc
    p.m * |deriv U x| * |deriv (v t) x| *
        |paper5A (p.m - 1) u U t x| =
        p.m * |deriv (v t) x| *
          (|deriv U x| * |paper5A (p.m - 1) u U t x|) := by ring
    _ ≤ p.m * (M ^ p.γ) * (B * (U x) ^ (p.m - 1)) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hv hm0) hpaired
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (mul_nonneg hm0 hMg0)
    _ ≤ p.m * (M ^ p.γ) * (B * M ^ (p.m - 1)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hUpow_le hB)
        (mul_nonneg hm0 hMg0)
    _ = p.m * M ^ (p.m + p.γ - 1) * B := by
      rw [show p.m + p.γ - 1 = p.γ + (p.m - 1) by ring,
        Real.rpow_add_of_nonneg hM (le_trans zero_le_one p.hγ)
          (by linarith)]
      ring

/-- The nonmonotone corrected-wave producer for the singular `b₂` branch.
This is (5.23) with the absolute Lemma 5.2 constant supplied internally. -/
theorem paper5B2_abs_le_of_corrected_wave_one_lt_m_lt_two
    (p : CMParams) {c κ₁ M t x : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hm1 : 1 < p.m) (hm2 : p.m < 2)
    (hspeed :
      c > max (p.γ + p.γ⁻¹)
        (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)))
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hκ₁ : kappa c < κ₁)
    (htail : HasWaveRightTailAsymptotic c κ₁ U)
    (hM : 0 ≤ M) (hu : 0 ≤ u t x) (hUle : U x ≤ M)
    (hv : |deriv (v t) x| ≤ M ^ p.γ) :
    |paper5B2 p u v U t x| ≤
      p.m * M ^ (p.m + p.γ - 1) *
        logDerivativeBoundFormula p c := by
  apply paper5B2_abs_le_of_one_lt_m_of_m_lt_two p hm1 hm2 hM
    (logDerivativeBoundFormula_nonneg_of_speed p
      (le_trans (hbound.pos 0).le (hbound.le_MChi 0)) hspeed)
    hu (hTW.U_pos x) hUle hv
  exact abs_waveLogDerivative_le_logDerivativeBoundFormula
    p hm1 hspeed hTW hreg hbound hκ₁ htail x

theorem paper5B1_abs_le
    (p : CMParams) {M t x : ℝ} {u v : ℝ → ℝ → ℝ}
    (hM : 0 ≤ M) (hu : u t x ∈ Set.Icc (0 : ℝ) M)
    (hv : |deriv (v t) x| ≤ M ^ p.γ) :
    |paper5B1 p u v t x| ≤ paper520B1 p M := by
  unfold paper5B1 paper520B1
  rw [abs_mul, abs_mul, abs_of_nonneg (le_trans zero_le_one p.hm)]
  have hupow : (u t x) ^ (p.m - 1) ≤ M ^ (p.m - 1) :=
    Real.rpow_le_rpow hu.1 hu.2 (by linarith [p.hm])
  have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
  have huPow0 : 0 ≤ (u t x) ^ (p.m - 1) :=
    Real.rpow_nonneg hu.1 _
  have hMg0 : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM _
  rw [abs_of_nonneg (Real.rpow_nonneg hu.1 _)]
  calc
    p.m * |deriv (v t) x| * (u t x) ^ (p.m - 1)
        ≤ p.m * (M ^ p.γ) * (u t x) ^ (p.m - 1) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hv hm0) huPow0
    _ ≤ p.m * (M ^ p.γ) * M ^ (p.m - 1) := by
          exact mul_le_mul_of_nonneg_left hupow (mul_nonneg hm0 hMg0)
    _ = p.m * M ^ (p.m + p.γ - 1) := by
      calc
        p.m * M ^ p.γ * M ^ (p.m - 1)
            = p.m * (M ^ p.γ * M ^ (p.m - 1)) := by ring
        _ = p.m * M ^ (p.γ + (p.m - 1)) := by
          rw [Real.rpow_add_of_nonneg hM
            (le_trans zero_le_one p.hγ) (by linarith [p.hm])]
        _ = p.m * M ^ (p.m + p.γ - 1) := by ring

theorem paper5B3_abs_le_raw
    (p : CMParams) {M L x : ℝ} {U : ℝ → ℝ}
    (hM : 0 ≤ M) (hU : U x ∈ Set.Icc (0 : ℝ) M)
    (hUx : |deriv U x| ≤ L) :
    |paper5B3 p U x| ≤ p.m * M ^ (p.m - 1) * L := by
  unfold paper5B3
  rw [abs_mul, abs_mul, abs_of_nonneg (le_trans zero_le_one p.hm),
    abs_of_nonneg (Real.rpow_nonneg hU.1 _)]
  have hinner :
      (U x) ^ (p.m - 1) * |deriv U x| ≤ M ^ (p.m - 1) * L :=
    mul_le_mul hupow hUx (abs_nonneg _) (Real.rpow_nonneg hM _)
  calc
    p.m * (U x) ^ (p.m - 1) * |deriv U x|
        = p.m * ((U x) ^ (p.m - 1) * |deriv U x|) := by ring
    _ ≤ p.m * (M ^ (p.m - 1) * L) :=
      mul_le_mul_of_nonneg_left hinner (le_trans zero_le_one p.hm)
    _ = p.m * M ^ (p.m - 1) * L := by ring
  where
    hupow : (U x) ^ (p.m - 1) ≤ M ^ (p.m - 1) :=
      Real.rpow_le_rpow hU.1 hU.2 (by linarith [p.hm])

theorem paper5B4_abs_le
    (p : CMParams) {M x : ℝ} {U : ℝ → ℝ}
    (_hM : 0 ≤ M) (hU : U x ∈ Set.Icc (0 : ℝ) M) :
    |paper5B4 p U x| ≤ M ^ p.m := by
  unfold paper5B4
  rw [abs_of_nonneg (Real.rpow_nonneg hU.1 _)]
  exact Real.rpow_le_rpow hU.1 hU.2 (le_trans zero_le_one p.hm)

/-! ## A single coefficient producer for the corrected energy estimate -/

/-- A common, honest bound for `b₂` when both a global wave derivative bound
and an absolute logarithmic derivative bound are available.  The two entries
of the inner maximum are respectively the `m ≥ 2` and `1 < m < 2` branches.
Unlike (5.24), this definition is already a bound for `|b₂|`; it does not hide
an additional power of `|χ|` in the notation. -/
def paper5B2BoundFromDerivativeData
    (p : CMParams) (M Lu Blog : ℝ) : ℝ :=
  max 0 (max
    (p.m * Lu * (M ^ p.γ) * ((p.m - 1) * M ^ (p.m - 2)))
    (p.m * M ^ (p.m + p.γ - 1) * Blog))

theorem paper5B2BoundFromDerivativeData_nonneg
    (p : CMParams) (M Lu Blog : ℝ) :
    0 ≤ paper5B2BoundFromDerivativeData p M Lu Blog :=
  le_max_left _ _

/-- The three-case estimate (5.21)--(5.24), stated with its actual analytic
inputs.  In particular the singular `1 < m < 2` branch explicitly consumes
an *absolute* logarithmic derivative bound. -/
theorem paper5B2_abs_le_of_derivative_data
    (p : CMParams) {M Lu Blog t x : ℝ}
    {u v : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hM : 0 ≤ M) (hLu : 0 ≤ Lu) (hBlog : 0 ≤ Blog)
    (hu : u t x ∈ Set.Icc (0 : ℝ) M)
    (hU : U x ∈ Set.Icc (0 : ℝ) M)
    (hUpos : 0 < U x)
    (hUx : |deriv U x| ≤ Lu)
    (hv : |deriv (v t) x| ≤ M ^ p.γ)
    (hlog : 1 < p.m → p.m < 2 → |deriv U x / U x| ≤ Blog) :
    |paper5B2 p u v U t x| ≤
      paper5B2BoundFromDerivativeData p M Lu Blog := by
  by_cases hm1 : p.m = 1
  · rw [paper5B2_eq_zero_of_m_eq_one p hm1]
    simpa using paper5B2BoundFromDerivativeData_nonneg p M Lu Blog
  · have hm1' : 1 < p.m := lt_of_le_of_ne p.hm (Ne.symm hm1)
    by_cases hm2 : 2 ≤ p.m
    · have hlarge := paper5B2_abs_le_of_two_le_m p hm2 hM hu hU
          hLu hUx hv
      exact hlarge.trans <|
        le_trans (le_max_left _ _) (le_max_right _ _)
    · have hm2' : p.m < 2 := lt_of_not_ge hm2
      have hintermediate := paper5B2_abs_le_of_one_lt_m_of_m_lt_two
        p hm1' hm2' hM hBlog hu.1 hUpos hU.2 hv (hlog hm1' hm2')
      exact hintermediate.trans <|
        le_trans (le_max_right _ _) (le_max_right _ _)

/-- All four coefficient bounds required by the corrected Section 5 energy
estimate.  This theorem is deliberately chi-agnostic; the only nonlinear
profile inputs are the two derivative bounds displayed in its hypotheses. -/
theorem paper5CoefficientBounds_of_derivative_data
    (p : CMParams) {M Lu Blog t x : ℝ}
    {u v : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hM : 0 ≤ M) (hLu : 0 ≤ Lu) (hBlog : 0 ≤ Blog)
    (hu : u t x ∈ Set.Icc (0 : ℝ) M)
    (hU : U x ∈ Set.Icc (0 : ℝ) M)
    (hUpos : 0 < U x)
    (hv : |deriv (v t) x| ≤ M ^ p.γ)
    (hUx : |deriv U x| ≤ Lu)
    (hlog : 1 < p.m → p.m < 2 → |deriv U x / U x| ≤ Blog) :
    |paper5B1 p u v t x| ≤ paper520B1 p M ∧
      |paper5B2 p u v U t x| ≤
        paper5B2BoundFromDerivativeData p M Lu Blog ∧
      |paper5B3 p U x| ≤ p.m * M ^ (p.m - 1) * Lu ∧
      |paper5B4 p U x| ≤ M ^ p.m := by
  exact ⟨paper5B1_abs_le p hM hu hv,
    paper5B2_abs_le_of_derivative_data p hM hLu hBlog hu hU hUpos hUx hv hlog,
    paper5B3_abs_le_raw p hM hU hUx,
    paper5B4_abs_le p hM hU⟩

/-- The coefficient producer specialized to an actual corrected traveling
wave.  Remark 5.1 supplies the global derivative bound, while the corrected
absolute version of Lemma 5.2 is used only in the singular `1 < m < 2`
branch.  The resulting `b₂` budget is allowed to depend on the wave speed;
turning it into a speed-independent threshold is a separate scalar task. -/
theorem paper5CoefficientBounds_of_corrected_wave
    (p : CMParams) {c sigma κ₁ t x : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hsigma : 0 < sigma) (hχ : p.χ ≠ 0)
    (hspeed : remark5SpeedCondition p c sigma)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hκ₁ : kappa c < κ₁)
    (htail : HasWaveRightTailAsymptotic c κ₁ U)
    (hu : u t x ∈ Set.Icc (0 : ℝ) (MChi p))
    (hv : |deriv (v t) x| ≤ (MChi p) ^ p.γ) :
    let Lu := remark51MPrime p / remark5ChiSigma p sigma
    let Blog := logDerivativeBoundFormula p c
    |paper5B1 p u v t x| ≤ paper520B1 p (MChi p) ∧
      |paper5B2 p u v U t x| ≤
        paper5B2BoundFromDerivativeData p (MChi p) Lu Blog ∧
      |paper5B3 p U x| ≤ p.m * (MChi p) ^ (p.m - 1) * Lu ∧
      |paper5B4 p U x| ≤ (MChi p) ^ p.m := by
  let Lu := remark51MPrime p / remark5ChiSigma p sigma
  let Blog := logDerivativeBoundFormula p c
  have hMpos : 0 < MChi p :=
    lt_of_lt_of_le (hbound.pos 0) (hbound.le_MChi 0)
  have hLu : 0 ≤ Lu := by
    dsimp [Lu]
    exact div_nonneg (remark51MPrime_nonneg_of_MChi_pos p hMpos)
      (remark5ChiSigma_nonneg p sigma)
  have hspeedLog :
      c > max (p.γ + p.γ⁻¹)
        (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) :=
    remark5SpeedCondition_implies_Lemma_5_2_speed
      p c sigma hsigma hχ hspeed
  have hBlog : 0 ≤ Blog := by
    dsimp [Blog]
    exact logDerivativeBoundFormula_nonneg_of_speed p hMpos.le hspeedLog
  have hU : U x ∈ Set.Icc (0 : ℝ) (MChi p) :=
    ⟨(hTW.U_pos x).le, hbound.le_MChi x⟩
  have hUx : |deriv U x| ≤ Lu := by
    dsimp [Lu]
    exact remark_5_1_smooth_part1 p c sigma hsigma hχ hspeed U V
      hTW hbound hreg.U_diff hreg.V_deriv_diff hreg.deriv_U_cont
      hreg.deriv_U_diff hreg.deriv_U_tendszero hreg.V_nn hreg.V_bound x
  have hlog : 1 < p.m → p.m < 2 →
      |deriv U x / U x| ≤ Blog := by
    intro hm1 _hm2
    dsimp [Blog]
    exact abs_waveLogDerivative_le_logDerivativeBoundFormula p hm1 hspeedLog
      hTW hreg hbound hκ₁ htail x
  exact paper5CoefficientBounds_of_derivative_data p hMpos.le hLu hBlog
    hu hU (hTW.U_pos x) hv hUx hlog

/-- Speed-independent coefficient producer at the strengthened explicit speed
threshold.  The interval `[-1,1]` is invariant for `U'/U`, so the singular
`b₂` branch uses the fixed budget `Blog = 1` rather than a quantity growing
with `c`.  This applies to both sensitivity signs and needs no monotonicity. -/
theorem paper5CoefficientBounds_of_barrier_speed_corrected_wave
    (p : CMParams) {c sigma t x : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hsigma : 0 < sigma) (hχ : p.χ ≠ 0)
    (hspeed : remark5SpeedCondition p c sigma)
    (hbarrierSpeed : paper52MonotoneBarrierSpeed p < c)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hu : u t x ∈ Set.Icc (0 : ℝ) (MChi p))
    (hv : |deriv (v t) x| ≤ (MChi p) ^ p.γ) :
    let Lu := remark51MPrime p / remark5ChiSigma p sigma
    |paper5B1 p u v t x| ≤ paper520B1 p (MChi p) ∧
      |paper5B2 p u v U t x| ≤
        paper5B2BoundFromDerivativeData p (MChi p) Lu 1 ∧
      |paper5B3 p U x| ≤ p.m * (MChi p) ^ (p.m - 1) * Lu ∧
      |paper5B4 p U x| ≤ (MChi p) ^ p.m := by
  let Lu := remark51MPrime p / remark5ChiSigma p sigma
  have hMpos : 0 < MChi p :=
    lt_of_lt_of_le (hbound.pos 0) (hbound.le_MChi 0)
  have hLu : 0 ≤ Lu := by
    dsimp [Lu]
    exact div_nonneg (remark51MPrime_nonneg_of_MChi_pos p hMpos)
      (remark5ChiSigma_nonneg p sigma)
  have hU : U x ∈ Set.Icc (0 : ℝ) (MChi p) :=
    ⟨(hTW.U_pos x).le, hbound.le_MChi x⟩
  have hUx : |deriv U x| ≤ Lu := by
    dsimp [Lu]
    exact remark_5_1_smooth_part1 p c sigma hsigma hχ hspeed U V
      hTW hbound hreg.U_diff hreg.V_deriv_diff hreg.deriv_U_cont
      hreg.deriv_U_diff hreg.deriv_U_tendszero hreg.V_nn hreg.V_bound x
  have hlog : 1 < p.m → p.m < 2 →
      |deriv U x / U x| ≤ (1 : ℝ) := by
    intro _ _
    exact abs_waveLogDerivative_le_one_of_barrier_speed p hbarrierSpeed
      hTW hreg hbound x
  exact paper5CoefficientBounds_of_derivative_data p hMpos.le hLu
    zero_le_one hu hU (hTW.U_pos x) hv hUx hlog

/-- Compatibility wrapper for the monotone Theorem 1.1(1) branch. -/
theorem paper5CoefficientBounds_of_monotone_corrected_wave
    (p : CMParams) {c sigma t x : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hsigma : 0 < sigma) (hχ : p.χ ≠ 0)
    (hspeed : remark5SpeedCondition p c sigma)
    (hbarrierSpeed : paper52MonotoneBarrierSpeed p < c)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (_hmono : Antitone U)
    (hu : u t x ∈ Set.Icc (0 : ℝ) (MChi p))
    (hv : |deriv (v t) x| ≤ (MChi p) ^ p.γ) :
    let Lu := remark51MPrime p / remark5ChiSigma p sigma
    |paper5B1 p u v t x| ≤ paper520B1 p (MChi p) ∧
      |paper5B2 p u v U t x| ≤
        paper5B2BoundFromDerivativeData p (MChi p) Lu 1 ∧
      |paper5B3 p U x| ≤ p.m * (MChi p) ^ (p.m - 1) * Lu ∧
      |paper5B4 p U x| ≤ (MChi p) ^ p.m :=
  paper5CoefficientBounds_of_barrier_speed_corrected_wave p hsigma hχ
    hspeed hbarrierSpeed hTW hreg hbound hu hv

section Theorem12MeanCoefficientsAxiomAudit
#print axioms paper5MeanCoefficient_mul_sub
#print axioms paper5IntegralMeanCoefficient_eq
#print axioms paper5MeanCoefficient_nonneg
#print axioms paper5MeanCoefficient_abs_le
#print axioms paper5MeanCoefficient_zero
#print axioms paper5MeanCoefficient_abs_mul_right_le_rpow
#print axioms paper5A_mul_sub
#print axioms paper5ChemFluxDifference_expansion_corrected
#print axioms paper5CorrectedChemZeroCoefficient_abs_le
#print axioms paper5B2_eq_zero_of_m_eq_one
#print axioms paper5B2_abs_le_raw
#print axioms paper5B2_abs_le_of_two_le_m
#print axioms paper5B2_abs_le_of_one_lt_m_of_m_lt_two
#print axioms paper5B2_abs_le_of_corrected_wave_one_lt_m_lt_two
#print axioms paper5B1_abs_le
#print axioms paper5B3_abs_le_raw
#print axioms paper5B4_abs_le
#print axioms paper5B2_abs_le_of_derivative_data
#print axioms paper5CoefficientBounds_of_derivative_data
#print axioms paper5CoefficientBounds_of_corrected_wave
#print axioms paper5CoefficientBounds_of_barrier_speed_corrected_wave
#print axioms paper5CoefficientBounds_of_monotone_corrected_wave
end Theorem12MeanCoefficientsAxiomAudit

end ShenWork.Paper1
