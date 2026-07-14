import ShenWork.Paper1.Theorem12Section5Budgets
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

section Theorem12MeanCoefficientsAxiomAudit
#print axioms paper5MeanCoefficient_mul_sub
#print axioms paper5IntegralMeanCoefficient_eq
#print axioms paper5MeanCoefficient_nonneg
#print axioms paper5MeanCoefficient_abs_le
#print axioms paper5MeanCoefficient_zero
#print axioms paper5A_mul_sub
#print axioms paper5B2_eq_zero_of_m_eq_one
#print axioms paper5B2_abs_le_raw
#print axioms paper5B2_abs_le_of_two_le_m
#print axioms paper5B1_abs_le
#print axioms paper5B3_abs_le_raw
#print axioms paper5B4_abs_le
end Theorem12MeanCoefficientsAxiomAudit

end ShenWork.Paper1
