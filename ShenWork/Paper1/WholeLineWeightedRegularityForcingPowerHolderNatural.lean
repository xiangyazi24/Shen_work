import ShenWork.Paper1.WholeLineWeightedRegularityForcingHolderWindowNatural
import ShenWork.Paper1.WholeLineWeightedRegularityFourProfilePower

open Filter MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Natural power modulus for the exact-weight generator forcing

The scalar coefficients in the expanded forcing inherit the canonical
positive-time square-root modulus of the population.  When `1 < m < 2`,
the coefficient multiplying the weighted population is only
`(m - 1) / 2`-Holder in time.  The apparently singular secant in `b₂` is
removed by pairing it with the positive reference wave.
-/

/-- The unit-power secant is identically one. -/
theorem paper5MeanCoefficient_one (s r : ℝ) :
    paper5MeanCoefficient 1 s r = 1 := by
  by_cases hsr : s = r
  · simp [paper5MeanCoefficient, hsr]
  · rw [paper5MeanCoefficient, if_neg hsr]
    simp only [Real.rpow_one]
    exact div_self (sub_ne_zero.mpr hsr)

/-- For `1 < beta < 2`, the fixed-reference secant of `s ↦ s^beta` is
`(beta-1)`-Holder in its moving endpoint, uniformly up to the origin. -/
theorem paper5MeanCoefficient_sub_abs_le_rpow_of_one_lt_of_lt_two
    {beta M s t r : ℝ}
    (hbeta1 : 1 < beta) (hbeta2 : beta < 2) (hM : 0 ≤ M)
    (hs : s ∈ Set.Icc (0 : ℝ) M)
    (ht : t ∈ Set.Icc (0 : ℝ) M)
    (hr : r ∈ Set.Icc (0 : ℝ) M) :
    |paper5MeanCoefficient beta s r -
        paper5MeanCoefficient beta t r| ≤
      beta * |s - t| ^ (beta - 1) := by
  let as : ℝ → ℝ := fun tau => tau * s + (1 - tau) * r
  let bt : ℝ → ℝ := fun tau => tau * t + (1 - tau) * r
  let C : ℝ := beta * |s - t| ^ (beta - 1)
  have hbeta : 1 ≤ beta := hbeta1.le
  have hq0 : 0 ≤ beta - 1 := by linarith
  have hq1 : beta - 1 ≤ 1 := by linarith
  have hbeta0 : 0 ≤ beta := le_trans zero_le_one hbeta
  have hC0 : 0 ≤ C :=
    mul_nonneg hbeta0 (Real.rpow_nonneg (abs_nonneg _) _)
  have hseg (tau : ℝ) (htau : tau ∈ Set.Icc (0 : ℝ) 1) :
      as tau ∈ Set.Icc (0 : ℝ) M ∧ bt tau ∈ Set.Icc (0 : ℝ) M := by
    have has := (convex_Icc (0 : ℝ) M).add_smul_sub_mem hr hs htau
    have hat := (convex_Icc (0 : ℝ) M).add_smul_sub_mem hr ht htau
    constructor
    · have heq : as tau = r + tau * (s - r) := by
        dsimp [as]
        ring
      rw [heq]
      exact has
    · have heq : bt tau = r + tau * (t - r) := by
        dsimp [bt]
        ring
      rw [heq]
      exact hat
  have hpoint (tau : ℝ) (htau : tau ∈ Set.Icc (0 : ℝ) 1) :
      |beta * (as tau ^ (beta - 1) - bt tau ^ (beta - 1))| ≤ C := by
    rcases hseg tau htau with ⟨has, hat⟩
    have hp := abs_nonneg_rpow_sub_rpow_le_abs_sub_rpow
      has.1 hat.1 hq0 hq1
    have htau0 : 0 ≤ tau := htau.1
    have htau1 : tau ≤ 1 := htau.2
    have hdiff : |as tau - bt tau| = tau * |s - t| := by
      rw [show as tau - bt tau = tau * (s - t) by
        dsimp [as, bt]
        ring]
      rw [abs_mul, abs_of_nonneg htau0]
    have htaupow : tau ^ (beta - 1) ≤ 1 := by
      simpa using Real.rpow_le_one htau0 htau1 hq0
    rw [abs_mul, abs_of_nonneg hbeta0]
    calc
      beta * |as tau ^ (beta - 1) - bt tau ^ (beta - 1)| ≤
          beta * |as tau - bt tau| ^ (beta - 1) :=
        mul_le_mul_of_nonneg_left hp hbeta0
      _ = beta * (tau ^ (beta - 1) * |s - t| ^ (beta - 1)) := by
        rw [hdiff, Real.mul_rpow htau0 (abs_nonneg _)]
      _ ≤ beta * (1 * |s - t| ^ (beta - 1)) := by
        gcongr
      _ = C := by simp [C]
  have hintS : IntervalIntegrable
      (fun tau : ℝ => beta * as tau ^ (beta - 1)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.const_mul
    apply Continuous.rpow_const
    · dsimp [as]
      fun_prop
    · intro _
      exact Or.inr hq0
  have hintT : IntervalIntegrable
      (fun tau : ℝ => beta * bt tau ^ (beta - 1)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.const_mul
    apply Continuous.rpow_const
    · dsimp [bt]
      fun_prop
    · intro _
      exact Or.inr hq0
  have hcoef :
      paper5MeanCoefficient beta s r - paper5MeanCoefficient beta t r =
        ∫ tau : ℝ in 0..1,
          beta * (as tau ^ (beta - 1) - bt tau ^ (beta - 1)) := by
    rw [← paper5IntegralMeanCoefficient_eq hbeta,
      ← paper5IntegralMeanCoefficient_eq hbeta]
    unfold paper5IntegralMeanCoefficient
    rw [← intervalIntegral.integral_sub hintS hintT]
    apply intervalIntegral.integral_congr
    intro tau _
    dsimp [as, bt]
    ring
  rw [hcoef]
  simpa [Real.norm_eq_abs, abs_of_nonneg hC0] using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := C)
      (f := fun tau : ℝ =>
        beta * (as tau ^ (beta - 1) - bt tau ^ (beta - 1)))
      (fun tau htau => by
        rw [Real.norm_eq_abs]
        exact hpoint tau (by
          simpa [Set.uIcc_of_le zero_le_one] using
            (Set.uIoc_subset_uIcc htau))))

/-- Pairing the sublinear secant with its positive reference removes the
singularity at zero.  This identity is valid for every `m ≥ 1`. -/
theorem paper5MeanCoefficient_mul_positive_reference
    {m s r : ℝ} (hm : 1 ≤ m) (hs : 0 ≤ s) (hr : 0 < r) :
    r * paper5MeanCoefficient (m - 1) s r =
      paper5MeanCoefficient m s r - s ^ (m - 1) := by
  have hr0 : 0 ≤ r := hr.le
  by_cases hsr : s = r
  · subst s
    rw [paper5MeanCoefficient, if_pos rfl,
      paper5MeanCoefficient, if_pos rfl]
    have hmul : r * r ^ (m - 2) = r ^ (m - 1) := by
      calc
        r * r ^ (m - 2) = r ^ (1 : ℝ) * r ^ (m - 2) := by
          rw [Real.rpow_one]
        _ = r ^ ((1 : ℝ) + (m - 2)) :=
          (Real.rpow_add hr 1 (m - 2)).symm
        _ = r ^ (m - 1) := by ring_nf
    calc
      r * ((m - 1) * r ^ (m - 1 - 1)) =
          (m - 1) * (r * r ^ (m - 2)) := by
        rw [show m - 1 - 1 = m - 2 by ring]
        ring
      _ = (m - 1) * r ^ (m - 1) := by rw [hmul]
      _ = m * r ^ (m - 1) - r ^ (m - 1) := by ring
  · apply mul_right_cancel₀ (sub_ne_zero.mpr hsr)
    rw [mul_assoc, paper5MeanCoefficient_mul_sub, sub_mul,
      paper5MeanCoefficient_mul_sub]
    have hpow : s ^ m = s ^ (m - 1) * s := by
      calc
        s ^ m = s ^ ((m - 1) + 1) := by congr 1 <;> ring
        _ = s ^ (m - 1) * s ^ (1 : ℝ) :=
          Real.rpow_add_of_nonneg hs (by linarith) (by norm_num)
        _ = s ^ (m - 1) * s := by rw [Real.rpow_one]
    have hrpow : r ^ m = r ^ (m - 1) * r := by
      calc
        r ^ m = r ^ ((m - 1) + 1) := by congr 1 <;> ring
        _ = r ^ (m - 1) * r ^ (1 : ℝ) :=
          Real.rpow_add_of_nonneg hr0 (by linarith) (by norm_num)
        _ = r ^ (m - 1) * r := by rw [Real.rpow_one]
    rw [hpow, hrpow]
    ring

/-- Uniform continuous dependence of the resolver value on a bounded
nonnegative profile. -/
theorem frozenElliptic_diff_uniform_abs_le
    (p : CMParams) {M D : ℝ} {u w : ℝ → ℝ}
    (hM : 0 ≤ M)
    (hu : IsCUnifBdd u) (hw : IsCUnifBdd w)
    (huM : ∀ x, u x ∈ Set.Icc (0 : ℝ) M)
    (hwM : ∀ x, w x ∈ Set.Icc (0 : ℝ) M)
    (hD : ∀ x, |u x - w x| ≤ D) (x : ℝ) :
    |frozenElliptic p u x - frozenElliptic p w x| ≤
      rpowLip p.γ M * D := by
  have hL0 : 0 ≤ rpowLip p.γ M := rpowLip_nonneg p.hγ hM
  have hpower : ∀ y,
      |(u y) ^ p.γ - (w y) ^ p.γ| ≤ rpowLip p.γ M * D := by
    intro y
    calc
      |(u y) ^ p.γ - (w y) ^ p.γ| ≤
          rpowLip p.γ M * |u y - w y| := by
        simpa only [rpowLip] using
          abs_rpow_sub_rpow_le_of_mem_Icc p.hγ hM (huM y) (hwM y)
      _ ≤ rpowLip p.γ M * D :=
        mul_le_mul_of_nonneg_left (hD y) hL0
  have hkernel :
      (∫ y, Real.exp (-|x - y|) *
          |(u y) ^ p.γ - (w y) ^ p.γ|) ≤
        ∫ y, Real.exp (-|x - y|) * (rpowLip p.γ M * D) := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun y =>
        mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)
    · exact (exp_neg_abs_sub_integrable x).mul_const _
    · exact Filter.Eventually.of_forall fun y =>
        mul_le_mul_of_nonneg_left (hpower y) (Real.exp_nonneg _)
  have hbase := frozenElliptic_diff_abs_le p hu
    (fun y => (huM y).1) hw (fun y => (hwM y).1) x
  calc
    |frozenElliptic p u x - frozenElliptic p w x| ≤
        1 / 2 * ∫ y, Real.exp (-|x - y|) *
          |(u y) ^ p.γ - (w y) ^ p.γ| := hbase
    _ ≤ 1 / 2 * ∫ y,
        Real.exp (-|x - y|) * (rpowLip p.γ M * D) := by
      exact mul_le_mul_of_nonneg_left hkernel (by norm_num)
    _ = rpowLip p.γ M * D := by
      rw [integral_mul_const, exp_neg_abs_sub_integral_eq]
      ring

/-- Time exponent forced by the least regular sensitivity coefficient. -/
def paper5ForcingTimeExponent (p : CMParams) : ℝ :=
  if p.m = 1 then 1 / 2 else min 1 (p.m - 1) / 2

theorem paper5ForcingTimeExponent_pos (p : CMParams) :
    0 < paper5ForcingTimeExponent p := by
  unfold paper5ForcingTimeExponent
  by_cases hm : p.m = 1
  · rw [if_pos hm]
    norm_num
  · rw [if_neg hm]
    have hm1 : 1 < p.m := lt_of_le_of_ne p.hm (Ne.symm hm)
    have hmin : 0 < min (1 : ℝ) (p.m - 1) :=
      lt_min zero_lt_one (by linarith)
    positivity

theorem paper5ForcingTimeExponent_le_half (p : CMParams) :
    paper5ForcingTimeExponent p ≤ 1 / 2 := by
  unfold paper5ForcingTimeExponent
  by_cases hm : p.m = 1
  · rw [if_pos hm]
  · rw [if_neg hm]
    have hmin : min (1 : ℝ) (p.m - 1) ≤ 1 := min_le_left _ _
    linarith

/-- On a unit time scale, every square-root modulus is also a modulus with
the natural forcing exponent. -/
theorem rpow_half_le_rpow_forcingTimeExponent
    (p : CMParams) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    d ^ (1 / 2 : ℝ) ≤ d ^ paper5ForcingTimeExponent p := by
  exact Real.rpow_le_rpow_of_exponent_ge' hd0 hd1
    (paper5ForcingTimeExponent_pos p).le
    (paper5ForcingTimeExponent_le_half p)

/-- The sensitivity power `u^(m-1)` inherits the natural forcing modulus
from a square-root modulus of `u`. -/
theorem exists_rpow_sensitivity_time_modulus
    (p : CMParams) {M Hu d s t : ℝ} {u : ℝ → ℝ → ℝ}
    (hM : 0 ≤ M) (hHu : 0 ≤ Hu) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (huM : ∀ q x, u q x ∈ Set.Icc (0 : ℝ) M)
    (huHolder : ∀ x,
      |u s x - u t x| ≤ Hu * d ^ (1 / 2 : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |(u s x) ^ (p.m - 1) - (u t x) ^ (p.m - 1)| ≤
        C * d ^ paper5ForcingTimeExponent p := by
  by_cases hm : p.m = 1
  · refine ⟨0, le_rfl, ?_⟩
    intro x
    simp [hm]
  · have hm1 : 1 < p.m := lt_of_le_of_ne p.hm (Ne.symm hm)
    by_cases hm2 : p.m < 2
    · let C : ℝ := Hu ^ (p.m - 1)
      have hC : 0 ≤ C := Real.rpow_nonneg hHu _
      refine ⟨C, hC, ?_⟩
      intro x
      have hp := abs_nonneg_rpow_sub_rpow_le_abs_sub_rpow
        (a := u s x) (b := u t x) (q := p.m - 1)
          (huM s x).1 (huM t x).1 (by linarith) (by linarith)
      have hbase := Real.rpow_le_rpow (abs_nonneg _)
        (huHolder x) (by linarith : 0 ≤ p.m - 1)
      calc
        |(u s x) ^ (p.m - 1) - (u t x) ^ (p.m - 1)| ≤
            |u s x - u t x| ^ (p.m - 1) := hp
        _ ≤ (Hu * d ^ (1 / 2 : ℝ)) ^ (p.m - 1) := hbase
        _ = Hu ^ (p.m - 1) * d ^ ((p.m - 1) / 2) := by
          rw [Real.mul_rpow hHu (Real.rpow_nonneg hd0 _),
            ← Real.rpow_mul hd0]
          congr 1
          ring
        _ = C * d ^ paper5ForcingTimeExponent p := by
          simp only [C, paper5ForcingTimeExponent, hm, if_false]
          rw [min_eq_right (by linarith : p.m - 1 ≤ 1)]
    · have hm2' : 2 ≤ p.m := le_of_not_gt hm2
      let C : ℝ := (p.m - 1) * M ^ (p.m - 2) * Hu
      have hC : 0 ≤ C := by
        dsimp [C]
        exact mul_nonneg (mul_nonneg (by linarith)
          (Real.rpow_nonneg hM _)) hHu
      refine ⟨C, hC, ?_⟩
      intro x
      have hp := abs_rpow_sub_rpow_le_of_mem_Icc
        (gamma := p.m - 1) (M := M) (by linarith) hM
          (huM s x) (huM t x)
      have hhalf := rpow_half_le_rpow_forcingTimeExponent p hd0 hd1
      calc
        |(u s x) ^ (p.m - 1) - (u t x) ^ (p.m - 1)| ≤
            (p.m - 1) * M ^ (p.m - 2) * |u s x - u t x| := by
          convert hp using 1 <;> ring
        _ ≤ (p.m - 1) * M ^ (p.m - 2) *
            (Hu * d ^ (1 / 2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (huHolder x)
            (mul_nonneg (by linarith) (Real.rpow_nonneg hM _))
        _ ≤ C * d ^ paper5ForcingTimeExponent p := by
          dsimp [C]
          have hcoef : 0 ≤ (p.m - 1) * M ^ (p.m - 2) * Hu := by
            positivity
          calc
            (p.m - 1) * M ^ (p.m - 2) *
                (Hu * d ^ (1 / 2 : ℝ)) =
              ((p.m - 1) * M ^ (p.m - 2) * Hu) *
                d ^ (1 / 2 : ℝ) := by ring
            _ ≤ ((p.m - 1) * M ^ (p.m - 2) * Hu) *
                d ^ paper5ForcingTimeExponent p :=
              mul_le_mul_of_nonneg_left hhalf hcoef

/-- The moving endpoint of `a_m(u,U)` has the same natural modulus as
`u^(m-1)`. -/
theorem exists_paper5A_sensitivity_time_modulus
    (p : CMParams) {M Hu d s t : ℝ}
    {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hM : 0 ≤ M) (hHu : 0 ≤ Hu) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (huM : ∀ q x, u q x ∈ Set.Icc (0 : ℝ) M)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (huHolder : ∀ x,
      |u s x - u t x| ≤ Hu * d ^ (1 / 2 : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |paper5A p.m u U s x - paper5A p.m u U t x| ≤
        C * d ^ paper5ForcingTimeExponent p := by
  by_cases hm : p.m = 1
  · refine ⟨0, le_rfl, ?_⟩
    intro x
    simp [paper5A, hm, paper5MeanCoefficient_one]
  · have hm1 : 1 < p.m := lt_of_le_of_ne p.hm (Ne.symm hm)
    by_cases hm2 : p.m < 2
    · let C : ℝ := p.m * Hu ^ (p.m - 1)
      have hC : 0 ≤ C := by dsimp [C]; positivity
      refine ⟨C, hC, ?_⟩
      intro x
      have hsec :=
        paper5MeanCoefficient_sub_abs_le_rpow_of_one_lt_of_lt_two
          hm1 hm2 hM (huM s x) (huM t x) (hUM x)
      have hbase := Real.rpow_le_rpow (abs_nonneg _)
        (huHolder x) (by linarith : 0 ≤ p.m - 1)
      have hpoweq :
          (Hu * d ^ (1 / 2 : ℝ)) ^ (p.m - 1) =
            Hu ^ (p.m - 1) * d ^ ((p.m - 1) / 2) := by
        rw [Real.mul_rpow hHu (Real.rpow_nonneg hd0 _),
          ← Real.rpow_mul hd0]
        congr 1
        ring
      change |paper5MeanCoefficient p.m (u s x) (U x) -
          paper5MeanCoefficient p.m (u t x) (U x)| ≤ _
      calc
        |paper5MeanCoefficient p.m (u s x) (U x) -
            paper5MeanCoefficient p.m (u t x) (U x)| ≤
            p.m * |u s x - u t x| ^ (p.m - 1) := hsec
        _ ≤ p.m * (Hu * d ^ (1 / 2 : ℝ)) ^ (p.m - 1) :=
          mul_le_mul_of_nonneg_left hbase (by linarith [p.hm])
        _ = p.m * (Hu ^ (p.m - 1) * d ^ ((p.m - 1) / 2)) := by
          rw [hpoweq]
        _ = C * d ^ paper5ForcingTimeExponent p := by
          dsimp [C, paper5ForcingTimeExponent]
          rw [if_neg hm, min_eq_right (by linarith : p.m - 1 ≤ 1)]
          ring
    · have hm2' : 2 ≤ p.m := le_of_not_gt hm2
      let C : ℝ := p.m * (p.m - 1) * M ^ (p.m - 2) * Hu
      have hC : 0 ≤ C := by
        dsimp [C]
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (by linarith [p.hm]) (by linarith))
            (Real.rpow_nonneg hM _)) hHu
      refine ⟨C, hC, ?_⟩
      intro x
      have hsec := paper5_four_profile_secant_difference_bound_of_two_le
        (m := p.m) (M := M) (a2 := u s x) (b2 := u t x)
          (a1 := U x) (b1 := U x) hm2' hM
          (huM s x) (huM t x) (hUM x) (hUM x)
      have hhalf := rpow_half_le_rpow_forcingTimeExponent p hd0 hd1
      change |paper5MeanCoefficient p.m (u s x) (U x) -
          paper5MeanCoefficient p.m (u t x) (U x)| ≤ _
      calc
        |paper5MeanCoefficient p.m (u s x) (U x) -
            paper5MeanCoefficient p.m (u t x) (U x)| ≤
            p.m * (p.m - 1) * M ^ (p.m - 2) *
              |u s x - u t x| := by simpa using hsec
        _ ≤ p.m * (p.m - 1) * M ^ (p.m - 2) *
            (Hu * d ^ (1 / 2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (huHolder x)
            (mul_nonneg
              (mul_nonneg (by linarith [p.hm]) (by linarith))
              (Real.rpow_nonneg hM _))
        _ ≤ C * d ^ paper5ForcingTimeExponent p := by
          dsimp [C]
          have hcoef : 0 ≤ p.m * (p.m - 1) * M ^ (p.m - 2) * Hu := by
            positivity
          calc
            p.m * (p.m - 1) * M ^ (p.m - 2) *
                (Hu * d ^ (1 / 2 : ℝ)) =
              (p.m * (p.m - 1) * M ^ (p.m - 2) * Hu) *
                d ^ (1 / 2 : ℝ) := by ring
            _ ≤ (p.m * (p.m - 1) * M ^ (p.m - 2) * Hu) *
                d ^ paper5ForcingTimeExponent p :=
              mul_le_mul_of_nonneg_left hhalf hcoef

/-- Every secant with exponent at least two is Lipschitz in its moving
endpoint, hence has the weaker natural forcing modulus. -/
theorem paper5MeanCoefficient_sub_abs_le_forcingTimeExponent_of_two_le
    (p : CMParams) {beta M Hu d s t r : ℝ}
    (hbeta : 2 ≤ beta) (hM : 0 ≤ M) (hHu : 0 ≤ Hu)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hs : s ∈ Set.Icc (0 : ℝ) M)
    (ht : t ∈ Set.Icc (0 : ℝ) M)
    (hr : r ∈ Set.Icc (0 : ℝ) M)
    (hHolder : |s - t| ≤ Hu * d ^ (1 / 2 : ℝ)) :
    |paper5MeanCoefficient beta s r - paper5MeanCoefficient beta t r| ≤
      (beta * (beta - 1) * M ^ (beta - 2) * Hu) *
        d ^ paper5ForcingTimeExponent p := by
  have hsec := paper5_four_profile_secant_difference_bound_of_two_le
    (m := beta) (M := M) (a2 := s) (b2 := t) (a1 := r) (b1 := r)
      hbeta hM hs ht hr hr
  have hhalf := rpow_half_le_rpow_forcingTimeExponent p hd0 hd1
  calc
    |paper5MeanCoefficient beta s r - paper5MeanCoefficient beta t r| ≤
        beta * (beta - 1) * M ^ (beta - 2) * |s - t| := by
      simpa using hsec
    _ ≤ beta * (beta - 1) * M ^ (beta - 2) *
        (Hu * d ^ (1 / 2 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hHolder
        (mul_nonneg (mul_nonneg (by linarith) (by linarith))
          (Real.rpow_nonneg hM _))
    _ = (beta * (beta - 1) * M ^ (beta - 2) * Hu) *
        d ^ (1 / 2 : ℝ) := by ring
    _ ≤ (beta * (beta - 1) * M ^ (beta - 2) * Hu) *
        d ^ paper5ForcingTimeExponent p := by
      exact mul_le_mul_of_nonneg_left hhalf
        (mul_nonneg
          (mul_nonneg (mul_nonneg (by linarith) (by linarith))
            (Real.rpow_nonneg hM _)) hHu)

/-- The coefficient `b₁` has the natural time modulus.  Its constant is
selected internally from the population square-root modulus. -/
theorem exists_paper5B1_time_modulus
    (p : CMParams) {M Hu d s t : ℝ}
    {u v : ℝ → ℝ → ℝ}
    (hM : 0 ≤ M) (hHu : 0 ≤ Hu) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (huC : ∀ q, IsCUnifBdd (u q))
    (huM : ∀ q x, u q x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : ∀ q, v q = frozenElliptic p (u q))
    (huHolder : ∀ x,
      |u s x - u t x| ≤ Hu * d ^ (1 / 2 : ℝ)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x,
      |paper5B1 p u v s x - paper5B1 p u v t x| ≤
        D * d ^ paper5ForcingTimeExponent p := by
  obtain ⟨Cp, hCp, hp⟩ := exists_rpow_sensitivity_time_modulus
    p hM hHu hd0 hd1 huM huHolder
  let Lγ : ℝ := rpowLip p.γ M
  let D : ℝ := p.m *
    (Lγ * Hu * M ^ (p.m - 1) + M ^ p.γ * Cp)
  have hLγ : 0 ≤ Lγ := rpowLip_nonneg p.hγ hM
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (by linarith [p.hm])
      (add_nonneg
        (mul_nonneg (mul_nonneg hLγ hHu) (Real.rpow_nonneg hM _))
        (mul_nonneg (Real.rpow_nonneg hM _) hCp))
  refine ⟨D, hD, ?_⟩
  intro x
  let rho : ℝ := d ^ paper5ForcingTimeExponent p
  have hrho : 0 ≤ rho := Real.rpow_nonneg hd0 _
  have hhalf := rpow_half_le_rpow_forcingTimeExponent p hd0 hd1
  have hvxDiff0 := frozenElliptic_deriv_diff_uniform_abs_le p hM
    (huC s) (huC t) (huM s) (huM t) huHolder x
  have hvxDiff : |deriv (v s) x - deriv (v t) x| ≤
      Lγ * Hu * rho := by
    rw [hvEq s, hvEq t]
    calc
      |deriv (frozenElliptic p (u s)) x -
          deriv (frozenElliptic p (u t)) x| ≤
          Lγ * (Hu * d ^ (1 / 2 : ℝ)) := by
        simpa only [Lγ] using hvxDiff0
      _ = (Lγ * Hu) * d ^ (1 / 2 : ℝ) := by ring
      _ ≤ (Lγ * Hu) * rho :=
        mul_le_mul_of_nonneg_left hhalf (mul_nonneg hLγ hHu)
      _ = Lγ * Hu * rho := by ring
  have hvxT : |deriv (v t) x| ≤ M ^ p.γ := by
    rw [hvEq t]
    exact frozenElliptic_deriv_abs_le_rpow_of_Icc p hM
      (huC t) (huM t) x
  have huPowS : |(u s x) ^ (p.m - 1)| ≤ M ^ (p.m - 1) := by
    rw [abs_of_nonneg (Real.rpow_nonneg (huM s x).1 _)]
    exact Real.rpow_le_rpow (huM s x).1 (huM s x).2 (by linarith [p.hm])
  have hsplit :
      deriv (v s) x * (u s x) ^ (p.m - 1) -
          deriv (v t) x * (u t x) ^ (p.m - 1) =
        (deriv (v s) x - deriv (v t) x) *
            (u s x) ^ (p.m - 1) +
          deriv (v t) x *
            ((u s x) ^ (p.m - 1) - (u t x) ^ (p.m - 1)) := by
    ring
  unfold paper5B1
  rw [show p.m * deriv (v s) x * (u s x) ^ (p.m - 1) -
      p.m * deriv (v t) x * (u t x) ^ (p.m - 1) =
        p.m * (deriv (v s) x * (u s x) ^ (p.m - 1) -
          deriv (v t) x * (u t x) ^ (p.m - 1)) by ring,
    hsplit, abs_mul, abs_of_nonneg (by linarith [p.hm])]
  calc
    p.m * |(deriv (v s) x - deriv (v t) x) *
          (u s x) ^ (p.m - 1) +
        deriv (v t) x *
          ((u s x) ^ (p.m - 1) - (u t x) ^ (p.m - 1))| ≤
      p.m *
        (|deriv (v s) x - deriv (v t) x| *
            |(u s x) ^ (p.m - 1)| +
          |deriv (v t) x| *
            |(u s x) ^ (p.m - 1) - (u t x) ^ (p.m - 1)|) := by
      exact mul_le_mul_of_nonneg_left
        (by
          simpa only [abs_mul] using
            (abs_add_le
              ((deriv (v s) x - deriv (v t) x) *
                (u s x) ^ (p.m - 1))
              (deriv (v t) x *
                ((u s x) ^ (p.m - 1) - (u t x) ^ (p.m - 1)))))
        (by linarith [p.hm])
    _ ≤ p.m * ((Lγ * Hu * rho) * M ^ (p.m - 1) +
          M ^ p.γ * (Cp * rho)) := by
      have ht1 :
          |deriv (v s) x - deriv (v t) x| *
              |(u s x) ^ (p.m - 1)| ≤
            (Lγ * Hu * rho) * M ^ (p.m - 1) :=
        mul_le_mul hvxDiff huPowS (abs_nonneg _)
          (mul_nonneg (mul_nonneg hLγ hHu) hrho)
      have ht2 :
          |deriv (v t) x| *
              |(u s x) ^ (p.m - 1) - (u t x) ^ (p.m - 1)| ≤
            M ^ p.γ * (Cp * rho) :=
        mul_le_mul hvxT (hp x) (abs_nonneg _)
          (Real.rpow_nonneg hM _)
      exact mul_le_mul_of_nonneg_left (add_le_add ht1 ht2)
        (by linarith [p.hm])
    _ = D * d ^ paper5ForcingTimeExponent p := by
      dsimp [D, rho]
      ring

/-- The reaction secant coefficient has the natural time modulus. -/
theorem exists_paper5ReactionCoefficient_time_modulus
    (p : CMParams) {M Hu d s t : ℝ}
    {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hM : 0 ≤ M) (hHu : 0 ≤ Hu) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (huM : ∀ q x, u q x ∈ Set.Icc (0 : ℝ) M)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (huHolder : ∀ x,
      |u s x - u t x| ≤ Hu * d ^ (1 / 2 : ℝ)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x,
      |(1 - paper5A (1 + p.α) u U s x) -
        (1 - paper5A (1 + p.α) u U t x)| ≤
          D * d ^ paper5ForcingTimeExponent p := by
  let D : ℝ := (1 + p.α) * p.α * M ^ (p.α - 1) * Hu
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by linarith [p.hα])
          (le_trans zero_le_one p.hα))
        (Real.rpow_nonneg hM _)) hHu
  refine ⟨D, hD, ?_⟩
  intro x
  have hsec :=
    paper5MeanCoefficient_sub_abs_le_forcingTimeExponent_of_two_le
      p (beta := 1 + p.α) (M := M) (Hu := Hu) (d := d)
        (s := u s x) (t := u t x) (r := U x)
        (by linarith [p.hα]) hM hHu hd0 hd1
        (huM s x) (huM t x) (hUM x) (huHolder x)
  unfold paper5A
  rw [show
      (1 - paper5MeanCoefficient (1 + p.α) (u s x) (U x)) -
          (1 - paper5MeanCoefficient (1 + p.α) (u t x) (U x)) =
        paper5MeanCoefficient (1 + p.α) (u t x) (U x) -
          paper5MeanCoefficient (1 + p.α) (u s x) (U x) by ring,
    abs_sub_comm]
  convert hsec using 1 <;> dsimp [D] <;> ring

/-- Rewriting `b₂` through the logarithmic derivative removes the
sublinear secant `a_(m-1)` from the formula. -/
theorem paper5B2_eq_logDerivative_mul_regular_difference
    (p : CMParams) {u v : ℝ → ℝ → ℝ} {U : ℝ → ℝ} {q x : ℝ}
    (hu0 : 0 ≤ u q x) (hUpos : 0 < U x) :
    paper5B2 p u v U q x =
      p.m * (deriv U x / U x) * deriv (v q) x *
        (paper5A p.m u U q x - (u q x) ^ (p.m - 1)) := by
  have hid := paper5MeanCoefficient_mul_positive_reference
    p.hm hu0 hUpos
  unfold paper5B2 paper5A
  calc
    p.m * deriv U x * deriv (v q) x *
        paper5MeanCoefficient (p.m - 1) (u q x) (U x) =
      p.m * (deriv U x / U x) * deriv (v q) x *
        (U x * paper5MeanCoefficient (p.m - 1) (u q x) (U x)) := by
      field_simp [ne_of_gt hUpos]
    _ = p.m * (deriv U x / U x) * deriv (v q) x *
        (paper5MeanCoefficient p.m (u q x) (U x) -
          (u q x) ^ (p.m - 1)) := by rw [hid]

/-- The coefficient `b₂` has the natural time modulus for every `m ≥ 1`.
The `1 < m < 2` branch uses the preceding logarithmic cancellation. -/
theorem exists_paper5B2_time_modulus
    (p : CMParams) {M Hu Blog d s t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hM : 0 ≤ M) (hHu : 0 ≤ Hu) (hBlog : 0 ≤ Blog)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (huC : ∀ q, IsCUnifBdd (u q))
    (huM : ∀ q x, u q x ∈ Set.Icc (0 : ℝ) M)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hUpos : ∀ x, 0 < U x)
    (hlog : ∀ x, |deriv U x / U x| ≤ Blog)
    (hvEq : ∀ q, v q = frozenElliptic p (u q))
    (huHolder : ∀ x,
      |u s x - u t x| ≤ Hu * d ^ (1 / 2 : ℝ)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x,
      |paper5B2 p u v U s x - paper5B2 p u v U t x| ≤
        D * d ^ paper5ForcingTimeExponent p := by
  obtain ⟨CA, hCA, hAdiff⟩ := exists_paper5A_sensitivity_time_modulus
    p hM hHu hd0 hd1 huM hUM huHolder
  obtain ⟨Cp, hCp, hpdiff⟩ := exists_rpow_sensitivity_time_modulus
    p hM hHu hd0 hd1 huM huHolder
  let Lγ : ℝ := rpowLip p.γ M
  let Qmax : ℝ := (p.m + 1) * M ^ (p.m - 1)
  let D : ℝ := p.m * Blog *
    (Lγ * Hu * Qmax + M ^ p.γ * (CA + Cp))
  have hLγ : 0 ≤ Lγ := rpowLip_nonneg p.hγ hM
  have hQmax : 0 ≤ Qmax := by
    dsimp [Qmax]
    exact mul_nonneg (by linarith [p.hm]) (Real.rpow_nonneg hM _)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (mul_nonneg (by linarith [p.hm]) hBlog)
      (add_nonneg
        (mul_nonneg (mul_nonneg hLγ hHu) hQmax)
        (mul_nonneg (Real.rpow_nonneg hM _) (add_nonneg hCA hCp)))
  refine ⟨D, hD, ?_⟩
  intro x
  let rho : ℝ := d ^ paper5ForcingTimeExponent p
  let Q : ℝ → ℝ := fun q =>
    paper5A p.m u U q x - (u q x) ^ (p.m - 1)
  have hrho : 0 ≤ rho := Real.rpow_nonneg hd0 _
  have hhalf := rpow_half_le_rpow_forcingTimeExponent p hd0 hd1
  have hvxDiff0 := frozenElliptic_deriv_diff_uniform_abs_le p hM
    (huC s) (huC t) (huM s) (huM t) huHolder x
  have hvxDiff : |deriv (v s) x - deriv (v t) x| ≤
      Lγ * Hu * rho := by
    rw [hvEq s, hvEq t]
    calc
      |deriv (frozenElliptic p (u s)) x -
          deriv (frozenElliptic p (u t)) x| ≤
          Lγ * (Hu * d ^ (1 / 2 : ℝ)) := by
        simpa only [Lγ] using hvxDiff0
      _ = (Lγ * Hu) * d ^ (1 / 2 : ℝ) := by ring
      _ ≤ (Lγ * Hu) * rho :=
        mul_le_mul_of_nonneg_left hhalf (mul_nonneg hLγ hHu)
      _ = Lγ * Hu * rho := by ring
  have hvxT : |deriv (v t) x| ≤ M ^ p.γ := by
    rw [hvEq t]
    exact frozenElliptic_deriv_abs_le_rpow_of_Icc p hM
      (huC t) (huM t) x
  have hAS : |paper5A p.m u U s x| ≤
      p.m * M ^ (p.m - 1) :=
    paper5MeanCoefficient_abs_le p.hm hM (huM s x) (hUM x)
  have hpowS : |(u s x) ^ (p.m - 1)| ≤ M ^ (p.m - 1) := by
    rw [abs_of_nonneg (Real.rpow_nonneg (huM s x).1 _)]
    exact Real.rpow_le_rpow (huM s x).1 (huM s x).2 (by linarith [p.hm])
  have hQS : |Q s| ≤ Qmax := by
    dsimp [Q, Qmax]
    calc
      |paper5A p.m u U s x - (u s x) ^ (p.m - 1)| ≤
          |paper5A p.m u U s x| + |(u s x) ^ (p.m - 1)| := abs_sub _ _
      _ ≤ p.m * M ^ (p.m - 1) + M ^ (p.m - 1) :=
        add_le_add hAS hpowS
      _ = (p.m + 1) * M ^ (p.m - 1) := by ring
  have hQdiff : |Q s - Q t| ≤ (CA + Cp) * rho := by
    dsimp [Q]
    calc
      |(paper5A p.m u U s x - (u s x) ^ (p.m - 1)) -
          (paper5A p.m u U t x - (u t x) ^ (p.m - 1))| ≤
        |paper5A p.m u U s x - paper5A p.m u U t x| +
          |(u s x) ^ (p.m - 1) - (u t x) ^ (p.m - 1)| := by
        convert abs_sub
          (paper5A p.m u U s x - paper5A p.m u U t x)
          ((u s x) ^ (p.m - 1) - (u t x) ^ (p.m - 1)) using 1 <;> ring
      _ ≤ CA * rho + Cp * rho := add_le_add (hAdiff x) (hpdiff x)
      _ = (CA + Cp) * rho := by ring
  have hsRep := paper5B2_eq_logDerivative_mul_regular_difference
    p (u := u) (v := v) (U := U) (q := s) (x := x)
      (huM s x).1 (hUpos x)
  have htRep := paper5B2_eq_logDerivative_mul_regular_difference
    p (u := u) (v := v) (U := U) (q := t) (x := x)
      (huM t x).1 (hUpos x)
  rw [hsRep, htRep]
  have hsplit :
      deriv (v s) x * Q s - deriv (v t) x * Q t =
        (deriv (v s) x - deriv (v t) x) * Q s +
          deriv (v t) x * (Q s - Q t) := by ring
  rw [show
      p.m * (deriv U x / U x) * deriv (v s) x * Q s -
          p.m * (deriv U x / U x) * deriv (v t) x * Q t =
        (p.m * (deriv U x / U x)) *
          (deriv (v s) x * Q s - deriv (v t) x * Q t) by ring,
    hsplit, abs_mul]
  have hpLog : |p.m * (deriv U x / U x)| ≤ p.m * Blog := by
    rw [abs_mul, abs_of_nonneg (by linarith [p.hm])]
    exact mul_le_mul_of_nonneg_left (hlog x) (by linarith [p.hm])
  have hinner :
      |(deriv (v s) x - deriv (v t) x) * Q s +
          deriv (v t) x * (Q s - Q t)| ≤
        (Lγ * Hu * Qmax + M ^ p.γ * (CA + Cp)) * rho := by
    calc
      |(deriv (v s) x - deriv (v t) x) * Q s +
          deriv (v t) x * (Q s - Q t)| ≤
        |deriv (v s) x - deriv (v t) x| * |Q s| +
          |deriv (v t) x| * |Q s - Q t| := by
        simpa only [abs_mul] using abs_add_le
          ((deriv (v s) x - deriv (v t) x) * Q s)
          (deriv (v t) x * (Q s - Q t))
      _ ≤ (Lγ * Hu * rho) * Qmax +
          M ^ p.γ * ((CA + Cp) * rho) := by
        exact add_le_add
          (mul_le_mul hvxDiff hQS (abs_nonneg _)
            (mul_nonneg (mul_nonneg hLγ hHu) hrho))
          (mul_le_mul hvxT hQdiff (abs_nonneg _)
            (Real.rpow_nonneg hM _))
      _ = (Lγ * Hu * Qmax + M ^ p.γ * (CA + Cp)) * rho := by ring
  calc
    |p.m * (deriv U x / U x)| *
        |(deriv (v s) x - deriv (v t) x) * Q s +
          deriv (v t) x * (Q s - Q t)| ≤
      (p.m * Blog) *
        ((Lγ * Hu * Qmax + M ^ p.γ * (CA + Cp)) * rho) :=
      mul_le_mul hpLog hinner (abs_nonneg _)
        (mul_nonneg (by linarith [p.hm]) hBlog)
    _ = D * d ^ paper5ForcingTimeExponent p := by
      dsimp [D, rho]
      ring

/-- The corrected zero-order chemotaxis coefficient has the natural time
modulus.  Both resolver value dependence and power secants are produced
internally. -/
theorem exists_paper5CorrectedChemZeroCoefficient_time_modulus
    (p : CMParams) {M Hu d s t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hM : 0 ≤ M) (hHu : 0 ≤ Hu) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (huC : ∀ q, IsCUnifBdd (u q))
    (huM : ∀ q x, u q x ∈ Set.Icc (0 : ℝ) M)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : ∀ q, v q = frozenElliptic p (u q))
    (huHolder : ∀ x,
      |u s x - u t x| ≤ Hu * d ^ (1 / 2 : ℝ)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x,
      |paper5CorrectedChemZeroCoefficient p u v U s x -
          paper5CorrectedChemZeroCoefficient p u v U t x| ≤
        D * d ^ paper5ForcingTimeExponent p := by
  obtain ⟨CA, hCA, hAdiff⟩ := exists_paper5A_sensitivity_time_modulus
    p hM hHu hd0 hd1 huM hUM huHolder
  let Lγ : ℝ := rpowLip p.γ M
  let Cmg : ℝ := (p.m + p.γ) * (p.m + p.γ - 1) *
    M ^ (p.m + p.γ - 2) * Hu
  let D : ℝ :=
    Lγ * Hu * (p.m * M ^ (p.m - 1)) +
      M ^ p.γ * CA + Cmg
  have hLγ : 0 ≤ Lγ := rpowLip_nonneg p.hγ hM
  have hCmg : 0 ≤ Cmg := by
    dsimp [Cmg]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by linarith [p.hm, p.hγ])
          (by linarith [p.hm, p.hγ]))
        (Real.rpow_nonneg hM _)) hHu
  have hD : 0 ≤ D := by
    dsimp [D]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (mul_nonneg hLγ hHu)
          (mul_nonneg (by linarith [p.hm]) (Real.rpow_nonneg hM _)))
        (mul_nonneg (Real.rpow_nonneg hM _) hCA)) hCmg
  refine ⟨D, hD, ?_⟩
  intro x
  let rho : ℝ := d ^ paper5ForcingTimeExponent p
  have hrho : 0 ≤ rho := Real.rpow_nonneg hd0 _
  have hhalf := rpow_half_le_rpow_forcingTimeExponent p hd0 hd1
  have hvDiff0 := frozenElliptic_diff_uniform_abs_le p hM
    (huC s) (huC t) (huM s) (huM t) huHolder x
  have hvDiff : |v s x - v t x| ≤ Lγ * Hu * rho := by
    rw [hvEq s, hvEq t]
    calc
      |frozenElliptic p (u s) x - frozenElliptic p (u t) x| ≤
          Lγ * (Hu * d ^ (1 / 2 : ℝ)) := by
        simpa only [Lγ] using hvDiff0
      _ = (Lγ * Hu) * d ^ (1 / 2 : ℝ) := by ring
      _ ≤ (Lγ * Hu) * rho :=
        mul_le_mul_of_nonneg_left hhalf (mul_nonneg hLγ hHu)
      _ = Lγ * Hu * rho := by ring
  have hvT0 : 0 ≤ v t x := by
    rw [hvEq t]
    exact frozenElliptic_nonneg p (fun y => (huM t y).1) x
  have hvTle : v t x ≤ M ^ p.γ := by
    rw [hvEq t]
    exact frozenElliptic_le_of_rpow_le p (Real.rpow_nonneg hM _)
      (huC t).1 (fun y => (huM t y).1)
      (fun y => Real.rpow_le_rpow (huM t y).1 (huM t y).2
        (by linarith [p.hγ])) x
  have hvT : |v t x| ≤ M ^ p.γ := by
    rw [abs_of_nonneg hvT0]
    exact hvTle
  have hAS : |paper5A p.m u U s x| ≤
      p.m * M ^ (p.m - 1) :=
    paper5MeanCoefficient_abs_le p.hm hM (huM s x) (hUM x)
  have hAmgDiff :
      |paper5A (p.m + p.γ) u U s x -
          paper5A (p.m + p.γ) u U t x| ≤ Cmg * rho := by
    have hsec :=
      paper5MeanCoefficient_sub_abs_le_forcingTimeExponent_of_two_le
        p (beta := p.m + p.γ) (M := M) (Hu := Hu) (d := d)
          (s := u s x) (t := u t x) (r := U x)
          (by linarith [p.hm, p.hγ]) hM hHu hd0 hd1
          (huM s x) (huM t x) (hUM x) (huHolder x)
    simpa only [paper5A, Cmg] using hsec
  unfold paper5CorrectedChemZeroCoefficient
  have hprodSplit :
      v s x * paper5A p.m u U s x -
          v t x * paper5A p.m u U t x =
        (v s x - v t x) * paper5A p.m u U s x +
          v t x * (paper5A p.m u U s x - paper5A p.m u U t x) := by
    ring
  rw [show
      (v s x * paper5A p.m u U s x - paper5A (p.m + p.γ) u U s x) -
          (v t x * paper5A p.m u U t x - paper5A (p.m + p.γ) u U t x) =
        (v s x * paper5A p.m u U s x -
          v t x * paper5A p.m u U t x) -
          (paper5A (p.m + p.γ) u U s x -
            paper5A (p.m + p.γ) u U t x) by ring,
    hprodSplit]
  calc
    |(v s x - v t x) * paper5A p.m u U s x +
        v t x * (paper5A p.m u U s x - paper5A p.m u U t x) -
        (paper5A (p.m + p.γ) u U s x -
          paper5A (p.m + p.γ) u U t x)| ≤
      |v s x - v t x| * |paper5A p.m u U s x| +
        |v t x| * |paper5A p.m u U s x - paper5A p.m u U t x| +
        |paper5A (p.m + p.γ) u U s x -
          paper5A (p.m + p.γ) u U t x| := by
      calc
        |(v s x - v t x) * paper5A p.m u U s x +
            v t x * (paper5A p.m u U s x - paper5A p.m u U t x) -
            (paper5A (p.m + p.γ) u U s x -
              paper5A (p.m + p.γ) u U t x)| ≤
          |(v s x - v t x) * paper5A p.m u U s x +
            v t x * (paper5A p.m u U s x - paper5A p.m u U t x)| +
            |paper5A (p.m + p.γ) u U s x -
              paper5A (p.m + p.γ) u U t x| := abs_sub _ _
        _ ≤ (|v s x - v t x| * |paper5A p.m u U s x| +
              |v t x| * |paper5A p.m u U s x - paper5A p.m u U t x|) +
            |paper5A (p.m + p.γ) u U s x -
              paper5A (p.m + p.γ) u U t x| := by
          gcongr
          simpa only [abs_mul] using abs_add_le
            ((v s x - v t x) * paper5A p.m u U s x)
            (v t x * (paper5A p.m u U s x - paper5A p.m u U t x))
    _ ≤ (Lγ * Hu * rho) * (p.m * M ^ (p.m - 1)) +
        M ^ p.γ * (CA * rho) + Cmg * rho := by
      exact add_le_add
        (add_le_add
          (mul_le_mul hvDiff hAS (abs_nonneg _)
            (mul_nonneg (mul_nonneg hLγ hHu) hrho))
          (mul_le_mul hvT (hAdiff x) (abs_nonneg _)
            (Real.rpow_nonneg hM _)))
        hAmgDiff
    _ = D * d ^ paper5ForcingTimeExponent p := by
      dsimp [D, rho]
      ring

/-- The complete dynamic coefficient multiplying the weighted population
has the natural time modulus. -/
theorem exists_paper5WeightedFluxPopulationCoefficient_time_modulus
    (p : CMParams) {M eta Hu Blog d s t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hM : 0 ≤ M) (hHu : 0 ≤ Hu) (hBlog : 0 ≤ Blog)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (huC : ∀ q, IsCUnifBdd (u q))
    (huM : ∀ q x, u q x ∈ Set.Icc (0 : ℝ) M)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hUpos : ∀ x, 0 < U x)
    (hlog : ∀ x, |deriv U x / U x| ≤ Blog)
    (hvEq : ∀ q, v q = frozenElliptic p (u q))
    (huHolder : ∀ x,
      |u s x - u t x| ≤ Hu * d ^ (1 / 2 : ℝ)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x,
      |paper5WeightedFluxPopulationCoefficient p eta u v U s x -
          paper5WeightedFluxPopulationCoefficient p eta u v U t x| ≤
        D * d ^ paper5ForcingTimeExponent p := by
  obtain ⟨D1, hD1, hB1⟩ := exists_paper5B1_time_modulus
    p hM hHu hd0 hd1 huC huM hvEq huHolder
  obtain ⟨DB2, hDB2, hB2⟩ := exists_paper5B2_time_modulus
    p hM hHu hBlog hd0 hd1 huC huM hUM hUpos hlog hvEq huHolder
  obtain ⟨DC, hDC, hC⟩ :=
    exists_paper5CorrectedChemZeroCoefficient_time_modulus
      p hM hHu hd0 hd1 huC huM hUM hvEq huHolder
  let D : ℝ := DB2 + DC + |eta| * D1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro x
  let rho : ℝ := d ^ paper5ForcingTimeExponent p
  unfold paper5WeightedFluxPopulationCoefficient
  rw [show
      (paper5B2 p u v U s x +
          paper5CorrectedChemZeroCoefficient p u v U s x -
          eta * paper5B1 p u v s x) -
        (paper5B2 p u v U t x +
          paper5CorrectedChemZeroCoefficient p u v U t x -
          eta * paper5B1 p u v t x) =
      (paper5B2 p u v U s x - paper5B2 p u v U t x) +
        (paper5CorrectedChemZeroCoefficient p u v U s x -
          paper5CorrectedChemZeroCoefficient p u v U t x) -
        eta * (paper5B1 p u v s x - paper5B1 p u v t x) by ring]
  calc
    |(paper5B2 p u v U s x - paper5B2 p u v U t x) +
        (paper5CorrectedChemZeroCoefficient p u v U s x -
          paper5CorrectedChemZeroCoefficient p u v U t x) -
        eta * (paper5B1 p u v s x - paper5B1 p u v t x)| ≤
      |paper5B2 p u v U s x - paper5B2 p u v U t x| +
        |paper5CorrectedChemZeroCoefficient p u v U s x -
          paper5CorrectedChemZeroCoefficient p u v U t x| +
        |eta| * |paper5B1 p u v s x - paper5B1 p u v t x| := by
      calc
        |(paper5B2 p u v U s x - paper5B2 p u v U t x) +
            (paper5CorrectedChemZeroCoefficient p u v U s x -
              paper5CorrectedChemZeroCoefficient p u v U t x) -
            eta * (paper5B1 p u v s x - paper5B1 p u v t x)| ≤
          |(paper5B2 p u v U s x - paper5B2 p u v U t x) +
            (paper5CorrectedChemZeroCoefficient p u v U s x -
              paper5CorrectedChemZeroCoefficient p u v U t x)| +
            |eta * (paper5B1 p u v s x - paper5B1 p u v t x)| :=
          abs_sub _ _
        _ ≤ (|paper5B2 p u v U s x - paper5B2 p u v U t x| +
              |paper5CorrectedChemZeroCoefficient p u v U s x -
                paper5CorrectedChemZeroCoefficient p u v U t x|) +
            |eta| * |paper5B1 p u v s x - paper5B1 p u v t x| := by
          gcongr
          · exact abs_add_le _ _
          · rw [abs_mul]
    _ ≤ DB2 * rho + DC * rho + |eta| * (D1 * rho) := by
      exact add_le_add (add_le_add (hB2 x) (hC x))
        (mul_le_mul_of_nonneg_left (hB1 x) (abs_nonneg eta))
    _ = D * d ^ paper5ForcingTimeExponent p := by
      dsimp [D, rho]
      ring

set_option maxHeartbeats 3000000 in
/-- Natural positive-window Holder estimate for the canonical exact-weight
`L²` forcing trajectory.  All coefficient moduli are selected internally.
The only dynamic weighted premises left explicit are the exact-weight
`W/Wx` square moduli. -/
theorem
    exists_paper5WeightedGeneratorForcingExpandedPositiveWindowL2Trajectory_natural_holder
    (p : CMParams) {M eta a b s t Hu Blog : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    {K₁ K₂ K₃ K₄ KR : ℝ}
    {EW EWx EZ EZx HW HWx : ℝ}
    (hab : a ≤ b) (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    (hM : 1 ≤ M) (heta : 0 < eta) (heta1 : eta < 1)
    (huC : ∀ q, IsCUnifBdd (u q))
    (huM : ∀ q x, u q x ∈ Set.Icc (0 : ℝ) M)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hUpos : ∀ x, 0 < U x)
    (hBlog : 0 ≤ Blog)
    (hlog : ∀ x, |deriv U x / U x| ≤ Blog)
    (hvEq : ∀ q, v q = frozenElliptic p (u q))
    (hvDiff : ∀ q, Differentiable ℝ (v q))
    (hHu : 0 ≤ Hu) (hst : |s - t| ≤ 1)
    (huHolder : ∀ x,
      |u s x - u t x| ≤ Hu * |s - t| ^ (1 / 2 : ℝ))
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hK₃ : 0 ≤ K₃) (hK₄ : 0 ≤ K₄) (hKR : 0 ≤ KR)
    (hEW : 0 ≤ EW) (hEWx : 0 ≤ EWx)
    (hEZ : 0 ≤ EZ) (hEZx : 0 ≤ EZx)
    (hHW : 0 ≤ HW) (hHWx : 0 ≤ HWx)
    (hB₁_bound : ∀ x, |paper5B1 p u v s x| ≤ K₁)
    (hB₂_bound : ∀ x,
      |paper5WeightedFluxPopulationCoefficient p eta u v U s x| ≤ K₂)
    (hB₃_bound : ∀ x, |paper5B3 p U x| ≤ K₃)
    (hB₄_bound : ∀ x,
      |paper5WeightedFluxSignalCoefficient p eta U x| ≤ K₄)
    (hR_bound : ∀ x, |1 - paper5A (1 + p.α) u U s x| ≤ KR)
    (hB₁_meas : ∀ q, AEStronglyMeasurable (paper5B1 p u v q) volume)
    (hB₂_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedFluxPopulationCoefficient p eta u v U q) volume)
    (hB₃_meas : AEStronglyMeasurable (paper5B3 p U) volume)
    (hB₄_meas : AEStronglyMeasurable
      (paper5WeightedFluxSignalCoefficient p eta U) volume)
    (hR_meas : ∀ q, AEStronglyMeasurable
      (fun x => 1 - paper5A (1 + p.α) u U q x) volume)
    (hW_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedPopulation eta u U q) volume)
    (hWx_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedPopulationX eta u U q) volume)
    (hZ_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedSignal eta v V q) volume)
    (hZx_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedSignalX eta v V q) volume)
    (hF_meas : ∀ q ∈ Set.Icc a b, AEStronglyMeasurable
      (paper5WeightedGeneratorForcingExpandedTrajectory p eta u v U
        (paper5WeightedPopulation eta u U)
        (paper5WeightedPopulationX eta u U)
        (paper5WeightedSignal eta v V)
        (paper5WeightedSignalX eta v V) q) volume)
    (hF_sq : ∀ q ∈ Set.Icc a b, Integrable (fun x =>
      paper5WeightedGeneratorForcingExpandedTrajectory p eta u v U
        (paper5WeightedPopulation eta u U)
        (paper5WeightedPopulationX eta u U)
        (paper5WeightedSignal eta v V)
        (paper5WeightedSignalX eta v V) q x ^ 2) volume)
    (hW_diff : Integrable (fun x =>
      (paper5WeightedPopulation eta u U s x -
        paper5WeightedPopulation eta u U t x) ^ 2) volume)
    (hWx_diff : Integrable (fun x =>
      (paper5WeightedPopulationX eta u U s x -
        paper5WeightedPopulationX eta u U t x) ^ 2) volume)
    (hW_t : Integrable (fun x =>
      paper5WeightedPopulation eta u U t x ^ 2) volume)
    (hWx_t : Integrable (fun x =>
      paper5WeightedPopulationX eta u U t x ^ 2) volume)
    (hZ_t : Integrable (fun x =>
      paper5WeightedSignal eta v V t x ^ 2) volume)
    (hZx_t : Integrable (fun x =>
      paper5WeightedSignalX eta v V t x ^ 2) volume)
    (hW_diff_bound : (∫ x : ℝ,
      (paper5WeightedPopulation eta u U s x -
        paper5WeightedPopulation eta u U t x) ^ 2) ≤
      HW ^ 2 * (|s - t| ^ paper5ForcingTimeExponent p) ^ 2)
    (hWx_diff_bound : (∫ x : ℝ,
      (paper5WeightedPopulationX eta u U s x -
        paper5WeightedPopulationX eta u U t x) ^ 2) ≤
      HWx ^ 2 * (|s - t| ^ paper5ForcingTimeExponent p) ^ 2)
    (hW_t_bound : (∫ x : ℝ,
      paper5WeightedPopulation eta u U t x ^ 2) ≤ EW ^ 2)
    (hWx_t_bound : (∫ x : ℝ,
      paper5WeightedPopulationX eta u U t x ^ 2) ≤ EWx ^ 2)
    (hZ_t_bound : (∫ x : ℝ,
      paper5WeightedSignal eta v V t x ^ 2) ≤ EZ ^ 2)
    (hZx_t_bound : (∫ x : ℝ,
      paper5WeightedSignalX eta v V t x ^ 2) ≤ EZx ^ 2) :
    ∃ H : ℝ, 0 ≤ H ∧
      ‖wholeLineRealL2PositiveWindowTrajectory hab
            (paper5WeightedGeneratorForcingExpandedTrajectory p eta u v U
              (paper5WeightedPopulation eta u U)
              (paper5WeightedPopulationX eta u U)
              (paper5WeightedSignal eta v V)
              (paper5WeightedSignalX eta v V)) s -
          wholeLineRealL2PositiveWindowTrajectory hab
            (paper5WeightedGeneratorForcingExpandedTrajectory p eta u v U
              (paper5WeightedPopulation eta u U)
              (paper5WeightedPopulationX eta u U)
              (paper5WeightedSignal eta v V)
              (paper5WeightedSignalX eta v V)) t‖ ≤
        H * |s - t| ^ paper5ForcingTimeExponent p := by
  let d : ℝ := |s - t|
  let rho : ℝ := d ^ paper5ForcingTimeExponent p
  have hd0 : 0 ≤ d := abs_nonneg _
  have hrho : 0 ≤ rho := Real.rpow_nonneg hd0 _
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have huHolder' : ∀ x,
      |u s x - u t x| ≤ Hu * d ^ (1 / 2 : ℝ) := by
    simpa only [d] using huHolder
  obtain ⟨D₁, hD₁, hB₁_diff⟩ := exists_paper5B1_time_modulus
    p hM0 hHu hd0 hst huC huM hvEq huHolder'
  obtain ⟨D₂, hD₂, hB₂_diff⟩ :=
    exists_paper5WeightedFluxPopulationCoefficient_time_modulus
      p hM0 hHu hBlog hd0 hst huC huM hUM hUpos hlog hvEq huHolder'
  obtain ⟨DR, hDR, hR_diff⟩ :=
    exists_paper5ReactionCoefficient_time_modulus
      p hM0 hHu hd0 hst huM hUM huHolder'
  let HZ := Real.sqrt (paper5WeightedResolverVFactor p M eta) * HW
  let HZx := Real.sqrt (paper5WeightedResolverVxFactor p M eta) * HW
  let H := Real.sqrt (paper5WeightedGeneratorForcingHolderSquareConst p
    K₁ K₂ K₃ K₄ KR D₁ D₂ DR EWx EW HWx HW HZx HZ)
  have hmain :=
    paper5WeightedGeneratorForcingExpandedPositiveWindowL2Trajectory_norm_sub_le_of_population_H1_modulus
      p hab hs ht hM heta heta1 huC huM hvEq hvDiff
        hK₁ hK₂ hK₃ hK₄ hKR hD₁ hD₂ hDR
        hEW hEWx hEZ hEZx hHW hHWx hrho
        hB₁_bound (by simpa only [rho] using hB₁_diff)
        hB₂_bound (by simpa only [rho] using hB₂_diff)
        hB₃_bound hB₄_bound hR_bound
        (by simpa only [rho] using hR_diff)
        hB₁_meas hB₂_meas hB₃_meas hB₄_meas hR_meas
        hW_meas hWx_meas hZ_meas hZx_meas hF_meas hF_sq
        hW_diff hWx_diff hW_t hWx_t hZ_t hZx_t
        (by simpa only [rho, d] using hW_diff_bound)
        (by simpa only [rho, d] using hWx_diff_bound)
        hW_t_bound hWx_t_bound hZ_t_bound hZx_t_bound
  refine ⟨H, Real.sqrt_nonneg _, ?_⟩
  simpa only [H, HZ, HZx, rho, d] using hmain

#print axioms paper5MeanCoefficient_one
#print axioms paper5MeanCoefficient_sub_abs_le_rpow_of_one_lt_of_lt_two
#print axioms paper5MeanCoefficient_mul_positive_reference
#print axioms frozenElliptic_diff_uniform_abs_le
#print axioms paper5ForcingTimeExponent_pos
#print axioms rpow_half_le_rpow_forcingTimeExponent
#print axioms exists_rpow_sensitivity_time_modulus
#print axioms exists_paper5A_sensitivity_time_modulus
#print axioms paper5MeanCoefficient_sub_abs_le_forcingTimeExponent_of_two_le
#print axioms exists_paper5B1_time_modulus
#print axioms exists_paper5ReactionCoefficient_time_modulus
#print axioms paper5B2_eq_logDerivative_mul_regular_difference
#print axioms exists_paper5B2_time_modulus
#print axioms exists_paper5CorrectedChemZeroCoefficient_time_modulus
#print axioms exists_paper5WeightedFluxPopulationCoefficient_time_modulus
#print axioms
  exists_paper5WeightedGeneratorForcingExpandedPositiveWindowL2Trajectory_natural_holder

end ShenWork.Paper1
