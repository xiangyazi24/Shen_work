import ShenWork.Paper1.WholeLineLocalMomentEnergy
import ShenWork.Paper1.Lemma25Helpers
import ShenWork.Paper1.WholeLineWeightedRegularityPositiveTimeGronwall
import ShenWork.PDE.IntervalAgmonInterpolation

/-!
# Closing the translation-uniform local moment estimate

This file carries out the second half of the argument on pp. 18--19 of
Paper 1.  A scaled Young inequality and the weighted resolver-gradient
estimate of Lemma 2.5 absorb the last `u^(P+m-1) |v_x|` term in the
critical weighted energy inequality.  A scalar damping argument then gives
a bound uniform in time and in the centre of the translated weight.
-/

open Filter MeasureTheory Real Set Topology
open ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

noncomputable section

namespace ShenWork.Paper1

/-! ## The translated weight as an `ExponentialWeight` -/

theorem contDiff_two_regDist : ContDiff ℝ 2 regDist := by
  unfold regDist
  have hinner : ContDiff ℝ 2 (fun x : ℝ => 1 + x ^ 2) := by fun_prop
  exact hinner.sqrt (fun x => by nlinarith [sq_nonneg x])

theorem contDiff_two_localizingWeight (κ : ℝ) :
    ContDiff ℝ 2 (localizingWeight κ) := by
  unfold localizingWeight
  have hc : ContDiff ℝ 2 (fun _ : ℝ => -κ) := contDiff_const
  exact Real.contDiff_exp.comp (hc.mul contDiff_two_regDist)

theorem contDiff_two_localizingWeightAt (κ x₀ : ℝ) :
    ContDiff ℝ 2 (localizingWeightAt κ x₀) := by
  unfold localizingWeightAt
  exact (contDiff_two_localizingWeight κ).comp
    (contDiff_id.sub contDiff_const)

theorem localizingWeightAt_decay
    {κ : ℝ} (hκ : 0 < κ) (x₀ : ℝ) :
    ∃ k > 0, ∀ x : ℝ,
      localizingWeightAt κ x₀ x ≤ Real.exp (-k * |x|) := by
  refine ⟨κ / (1 + |x₀|), div_pos hκ (by positivity), fun x => ?_⟩
  unfold localizingWeightAt localizingWeight
  rw [Real.exp_le_exp]
  have hreg1 : (1 : ℝ) ≤ regDist (x - x₀) := one_le_regDist _
  have habs_shift : |x - x₀| ≤ regDist (x - x₀) := abs_le_regDist _
  have hx : |x| ≤ (1 + |x₀|) * regDist (x - x₀) := by
    calc
      |x| = |(x - x₀) + x₀| := by ring_nf
      _ ≤ |x - x₀| + |x₀| := abs_add_le _ _
      _ ≤ regDist (x - x₀) + |x₀| * regDist (x - x₀) := by
        exact add_le_add habs_shift (by
          simpa using mul_le_mul_of_nonneg_left hreg1 (abs_nonneg x₀))
      _ = (1 + |x₀|) * regDist (x - x₀) := by ring
  have hden : 0 < 1 + |x₀| := by positivity
  have hscaled : κ / (1 + |x₀|) * |x| ≤ κ * regDist (x - x₀) := by
    calc
      κ / (1 + |x₀|) * |x| ≤
          κ / (1 + |x₀|) * ((1 + |x₀|) * regDist (x - x₀)) :=
        mul_le_mul_of_nonneg_left hx (div_nonneg hκ.le hden.le)
      _ = κ * regDist (x - x₀) := by field_simp
  linarith

/-- The translated weight satisfies the full weight interface used by
Lemma 2.5.  Its decay witness may depend on the centre, while the derivative
envelope used in the estimate is the centre-independent number `κ`. -/
def localizingWeightAtExponentialWeight
    (κ x₀ : ℝ) (hκ : 0 < κ) : ExponentialWeight where
  weight := localizingWeightAt κ x₀
  smooth := contDiff_two_localizingWeightAt κ x₀
  pos := localizingWeightAt_pos κ x₀
  decay := localizingWeightAt_decay hκ x₀
  deriv_abs_le := ⟨κ, hκ, abs_deriv_localizingWeightAt_le hκ.le x₀⟩
  second_deriv_abs_le := by
    refine ⟨κ + κ ^ 2, by nlinarith [sq_pos_of_pos hκ], ?_⟩
    exact abs_iteratedDeriv_two_localizingWeightAt_le hκ.le x₀

/-! ## The scaled Young inequality used on the signal-gradient term -/

/-- Scaled Young inequality with the conjugate power retained explicitly. -/
theorem rpow_mul_scaled_young
    {r s eps U W : ℝ} (hr : 0 < r) (hrs : r < s)
    (heps : 0 < eps) (hU : 0 ≤ U) (hW : 0 ≤ W) :
    let q := s / (s - r)
    let d := (eps * (s / r)) ^ (r / s)
    U ^ r * W ≤ eps * U ^ s + (1 / (d ^ q * q)) * W ^ q := by
  dsimp only
  let q : ℝ := s / (s - r)
  let d : ℝ := (eps * (s / r)) ^ (r / s)
  have hs : 0 < s := lt_trans hr hrs
  have hsr : 0 < s - r := sub_pos.mpr hrs
  have hq : 1 < q := by
    dsimp [q]
    rw [one_lt_div hsr]
    linarith
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hsrdiv : 0 < s / r := div_pos hs hr
  have hd : 0 < d := by
    dsimp [d]
    exact Real.rpow_pos_of_pos (mul_pos heps hsrdiv) _
  have hy := scalar_rpow_young_absorb hr hrs hW heps hU
  have hquot :
      ((W / d) ^ q) / q = (1 / (d ^ q * q)) * W ^ q := by
    rw [Real.div_rpow hW hd.le]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hd q), ne_of_gt hq0]
  change W * U ^ r ≤ eps * U ^ s + ((W / d) ^ q) / q at hy
  rw [hquot] at hy
  calc
    U ^ r * W = W * U ^ r := by ring
    _ ≤ eps * U ^ s + (1 / (d ^ q * q)) * W ^ q := hy
    _ = eps * U ^ s +
        (1 / (((eps * (s / r)) ^ (r / s)) ^ (s / (s - r)) *
          (s / (s - r)))) * W ^ (s / (s - r)) := by
      dsimp [q, d]

/-- In the critical case the Young-conjugate exponent is exactly
`q = (P+α)/γ`. -/
theorem critical_local_signal_scaled_young
    (p : CMParams) {P U W : ℝ}
    (hP : 1 < P)
    (hcritical : p.α = p.m + p.γ - 1)
    (hU : 0 ≤ U) (hW : 0 ≤ W) :
    let q := (P + p.α) / p.γ
    let d := (((1 : ℝ) / 4) * ((P + p.α) / (P + p.m - 1))) ^
      ((P + p.m - 1) / (P + p.α))
    U ^ (P + p.m - 1) * W ≤
      (1 / 4 : ℝ) * U ^ (P + p.α) + (1 / (d ^ q * q)) * W ^ q := by
  dsimp only
  have hr : 0 < P + p.m - 1 := by linarith [p.hm]
  have hrs : P + p.m - 1 < P + p.α := by
    rw [hcritical]
    linarith [p.hγ]
  have hy := rpow_mul_scaled_young
    (r := P + p.m - 1) (s := P + p.α) (eps := (1 : ℝ) / 4)
    (U := U) (W := W) hr hrs (by norm_num) hU hW
  have hgap : P + p.α - (P + p.m - 1) = p.γ := by
    rw [hcritical]
    ring
  rw [hgap] at hy
  exact hy

/-! ## Constants in the resolver-gradient absorption -/

def wholeLineLocalResolverExponent (p : CMParams) (P : ℝ) : ℝ :=
  (P + p.α) / p.γ

def wholeLineLocalYoungScale (p : CMParams) (P : ℝ) : ℝ :=
  (((1 : ℝ) / 4) * ((P + p.α) / (P + p.m - 1))) ^
    ((P + p.m - 1) / (P + p.α))

def wholeLineLocalYoungConstant (p : CMParams) (P : ℝ) : ℝ :=
  1 / ((wholeLineLocalYoungScale p P) ^
    (wholeLineLocalResolverExponent p P) *
      wholeLineLocalResolverExponent p P)

/-- A centre- and `κ`-independent upper bound for the explicit Lemma 2.5
constant, valid when `0 < κ < 1/2`. -/
def wholeLineLocalResolverConstant (p : CMParams) (P : ℝ) : ℝ :=
  (Real.sqrt 1) ^ (wholeLineLocalResolverExponent p P) *
    ((1 / (2 * Real.sqrt 1)) ^ (wholeLineLocalResolverExponent p P) *
      (2 / Real.sqrt 1) ^ (wholeLineLocalResolverExponent p P - 1) * 4)

def wholeLineLocalSignalAbsorptionConstant (p : CMParams) (P : ℝ) : ℝ :=
  (1 / 4 : ℝ) + wholeLineLocalYoungConstant p P *
    wholeLineLocalResolverConstant p P

theorem wholeLineLocalResolverExponent_gt_one
    (p : CMParams) {P : ℝ} (hP : 1 < P)
    (hcritical : p.α = p.m + p.γ - 1) :
    1 < wholeLineLocalResolverExponent p P := by
  unfold wholeLineLocalResolverExponent
  rw [one_lt_div (lt_of_lt_of_le zero_lt_one p.hγ)]
  rw [hcritical]
  linarith [p.hm]

theorem wholeLineLocalYoungScale_pos
    (p : CMParams) {P : ℝ} (hP : 1 < P)
    (hcritical : p.α = p.m + p.γ - 1) :
    0 < wholeLineLocalYoungScale p P := by
  unfold wholeLineLocalYoungScale
  apply Real.rpow_pos_of_pos
  have hden : 0 < P + p.m - 1 := by linarith [p.hm]
  have hnum : 0 < P + p.α := by
    rw [hcritical]
    linarith [p.hm, p.hγ]
  exact mul_pos (by norm_num) (div_pos hnum hden)

theorem wholeLineLocalYoungConstant_pos
    (p : CMParams) {P : ℝ} (hP : 1 < P)
    (hcritical : p.α = p.m + p.γ - 1) :
    0 < wholeLineLocalYoungConstant p P := by
  unfold wholeLineLocalYoungConstant
  have hscale := wholeLineLocalYoungScale_pos p hP hcritical
  have hq := wholeLineLocalResolverExponent_gt_one p hP hcritical
  positivity

theorem wholeLineLocalResolverConstant_pos
    (p : CMParams) {P : ℝ} (hP : 1 < P)
    (hcritical : p.α = p.m + p.γ - 1) :
    0 < wholeLineLocalResolverConstant p P := by
  unfold wholeLineLocalResolverConstant
  have hq := wholeLineLocalResolverExponent_gt_one p hP hcritical
  positivity

theorem wholeLineLocalSignalAbsorptionConstant_pos
    (p : CMParams) {P : ℝ} (hP : 1 < P)
    (hcritical : p.α = p.m + p.γ - 1) :
    0 < wholeLineLocalSignalAbsorptionConstant p P := by
  unfold wholeLineLocalSignalAbsorptionConstant
  have hY := wholeLineLocalYoungConstant_pos p hP hcritical
  have hR := wholeLineLocalResolverConstant_pos p hP hcritical
  positivity

theorem wholeLineLocalExplicitResolverConstant_le
    (p : CMParams) {P κ : ℝ} (hκ : 0 < κ) (hκhalf : κ < 1 / 2) :
    (Real.sqrt 1) ^ (wholeLineLocalResolverExponent p P) *
        ((1 / (2 * Real.sqrt 1)) ^ (wholeLineLocalResolverExponent p P) *
          (2 / Real.sqrt 1) ^ (wholeLineLocalResolverExponent p P - 1) *
          (2 / (Real.sqrt 1 - κ))) ≤
      wholeLineLocalResolverConstant p P := by
  have hden : 0 < 1 - κ := by linarith
  have hlast : 2 / (1 - κ) ≤ (4 : ℝ) := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hfactor : 0 ≤
      (Real.sqrt 1) ^ (wholeLineLocalResolverExponent p P) *
        ((1 / (2 * Real.sqrt 1)) ^ (wholeLineLocalResolverExponent p P) *
          (2 / Real.sqrt 1) ^ (wholeLineLocalResolverExponent p P - 1)) := by
    positivity
  unfold wholeLineLocalResolverConstant
  simp only [Real.sqrt_one, one_div, one_rpow, one_mul]
  exact mul_le_mul_of_nonneg_left hlast (by positivity)

/-! ## Lemma 2.5 for the translated localizing weight -/

theorem WholeLineLocalMomentEnergyData.resolverGradient_estimate
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentEnergyData p P κ T t x₀ u v)
    (hκhalf : κ < 1 / 2)
    (hcritical : p.α = p.m + p.γ - 1)
    (hu : IsCUnifBdd (u t))
    (hu_nonneg : ∀ x, 0 ≤ u t x)
    (hv_resolver : v t = frozenElliptic p (u t)) :
    Integrable (fun x : ℝ =>
        |deriv (v t) x| ^ (wholeLineLocalResolverExponent p P) *
          localizingWeightAt κ x₀ x) ∧
      (∫ x : ℝ,
          |deriv (v t) x| ^ (wholeLineLocalResolverExponent p P) *
            localizingWeightAt κ x₀ x) ≤
        wholeLineLocalResolverConstant p P *
          wholeLineLocalLpMoment (P + p.α) κ u t x₀ := by
  let q : ℝ := wholeLineLocalResolverExponent p P
  let psi : ExponentialWeight :=
    localizingWeightAtExponentialWeight κ x₀ H.hκ
  have hq : 1 ≤ q :=
    (wholeLineLocalResolverExponent_gt_one p H.hP hcritical).le
  have hγq : p.γ * q = P + p.α := by
    dsimp [q, wholeLineLocalResolverExponent]
    field_simp [ne_of_gt (lt_of_lt_of_le zero_lt_one p.hγ)]
  have hint : Integrable (fun x : ℝ =>
      (u t x) ^ (p.γ * q) * psi.weight x) := by
    simpa only [hγq, psi, localizingWeightAtExponentialWeight] using
      H.logistic_integrable
  obtain ⟨hgrad_int, hgrad_le⟩ :=
    Lemma_2_5_with_explicit_k_original_power psi one_pos one_pos hq
      (lt_of_lt_of_le zero_lt_one p.hγ) H.hκ.le
      (by
        rw [Real.sqrt_one]
        linarith)
      (by
        intro z
        exact abs_deriv_localizingWeightAt_le H.hκ.le x₀ z)
      hu hu_nonneg hint
  have hvfun : v t = fun z => Psi (fun y => (u t y) ^ p.γ) 1 1 z := by
    simpa only [frozenElliptic] using hv_resolver
  have hconstant := wholeLineLocalExplicitResolverConstant_le
    (p := p) (P := P) H.hκ hκhalf
  have hhigh_nonneg :
      0 ≤ wholeLineLocalLpMoment (P + p.α) κ u t x₀ :=
    wholeLineLocalLpMoment_nonneg hu_nonneg
  have hrhs_eq :
      (∫ x : ℝ, (u t x) ^ (p.γ * q) * psi.weight x) =
        wholeLineLocalLpMoment (P + p.α) κ u t x₀ := by
    simp only [hγq, psi, localizingWeightAtExponentialWeight]
    rfl
  rw [hrhs_eq] at hgrad_le
  rw [hvfun]
  change Integrable (fun x : ℝ =>
      |deriv (fun z => Psi (fun y => (u t y) ^ p.γ) 1 1 z) x| ^ q *
        psi.weight x) ∧
    (∫ x : ℝ,
      |deriv (fun z => Psi (fun y => (u t y) ^ p.γ) 1 1 z) x| ^ q *
        psi.weight x) ≤
      wholeLineLocalResolverConstant p P *
        wholeLineLocalLpMoment (P + p.α) κ u t x₀
  refine ⟨hgrad_int, hgrad_le.trans ?_⟩
  exact mul_le_mul_of_nonneg_right hconstant hhigh_nonneg

/-- Young's inequality followed by Lemma 2.5 bounds the remaining mixed
signal-gradient moment by the critical high-power moment. -/
theorem WholeLineLocalMomentEnergyData.signalGradientAbs_le_high
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentEnergyData p P κ T t x₀ u v)
    (hκhalf : κ < 1 / 2)
    (hcritical : p.α = p.m + p.γ - 1)
    (hu : IsCUnifBdd (u t))
    (hu_nonneg : ∀ x, 0 ≤ u t x)
    (hv_resolver : v t = frozenElliptic p (u t)) :
    wholeLineLocalLpSignalGradientAbs p P κ u v t x₀ ≤
      wholeLineLocalSignalAbsorptionConstant p P *
        wholeLineLocalLpMoment (P + p.α) κ u t x₀ := by
  let q : ℝ := wholeLineLocalResolverExponent p P
  let CY : ℝ := wholeLineLocalYoungConstant p P
  obtain ⟨hgrad_int, hgrad_le⟩ :=
    H.resolverGradient_estimate hκhalf hcritical hu hu_nonneg hv_resolver
  have hCY : 0 ≤ CY :=
    (wholeLineLocalYoungConstant_pos p H.hP hcritical).le
  have hgrad_le' :
      (∫ x : ℝ, |deriv (v t) x| ^ q * localizingWeightAt κ x₀ x) ≤
        wholeLineLocalResolverConstant p P *
          wholeLineLocalLpMoment (P + p.α) κ u t x₀ := by
    simpa only [q] using hgrad_le
  have hhigh_scaled : Integrable (fun x : ℝ =>
      (1 / 4 : ℝ) *
        ((u t x) ^ (P + p.α) * localizingWeightAt κ x₀ x)) :=
    H.logistic_integrable.const_mul (1 / 4)
  have hgrad_scaled : Integrable (fun x : ℝ =>
      CY * (|deriv (v t) x| ^ q * localizingWeightAt κ x₀ x)) :=
    hgrad_int.const_mul CY
  have hpoint : ∀ x : ℝ,
      (u t x) ^ (P + p.m - 1) * |deriv (v t) x| *
          localizingWeightAt κ x₀ x ≤
        (1 / 4 : ℝ) *
            ((u t x) ^ (P + p.α) * localizingWeightAt κ x₀ x) +
          CY * (|deriv (v t) x| ^ q *
            localizingWeightAt κ x₀ x) := by
    intro x
    have hy := critical_local_signal_scaled_young p H.hP hcritical
      (hu_nonneg x) (abs_nonneg (deriv (v t) x))
    change
      (u t x) ^ (P + p.m - 1) * |deriv (v t) x| ≤
        (1 / 4 : ℝ) * (u t x) ^ (P + p.α) +
          CY * |deriv (v t) x| ^ q at hy
    have hw : 0 ≤ localizingWeightAt κ x₀ x :=
      (localizingWeightAt_pos κ x₀ x).le
    have := mul_le_mul_of_nonneg_right hy hw
    nlinarith
  have hintegral :
      wholeLineLocalLpSignalGradientAbs p P κ u v t x₀ ≤
        (1 / 4 : ℝ) * wholeLineLocalLpMoment (P + p.α) κ u t x₀ +
          CY * (∫ x : ℝ,
            |deriv (v t) x| ^ q * localizingWeightAt κ x₀ x) := by
    unfold wholeLineLocalLpSignalGradientAbs
    calc
      (∫ x : ℝ, (u t x) ^ (P + p.m - 1) * |deriv (v t) x| *
          localizingWeightAt κ x₀ x) ≤
          ∫ x : ℝ,
            (1 / 4 : ℝ) *
                ((u t x) ^ (P + p.α) * localizingWeightAt κ x₀ x) +
              CY * (|deriv (v t) x| ^ q *
                localizingWeightAt κ x₀ x) := by
        exact integral_mono H.signal_gradient_abs_integrable
          (hhigh_scaled.add hgrad_scaled) hpoint
      _ = (1 / 4 : ℝ) *
            wholeLineLocalLpMoment (P + p.α) κ u t x₀ +
          CY * (∫ x : ℝ,
            |deriv (v t) x| ^ q * localizingWeightAt κ x₀ x) := by
        rw [integral_add hhigh_scaled hgrad_scaled,
          integral_const_mul, integral_const_mul]
        rfl
  calc
    wholeLineLocalLpSignalGradientAbs p P κ u v t x₀ ≤
        (1 / 4 : ℝ) * wholeLineLocalLpMoment (P + p.α) κ u t x₀ +
          CY * (∫ x : ℝ,
            |deriv (v t) x| ^ q * localizingWeightAt κ x₀ x) := hintegral
    _ ≤ (1 / 4 : ℝ) * wholeLineLocalLpMoment (P + p.α) κ u t x₀ +
          CY * (wholeLineLocalResolverConstant p P *
            wholeLineLocalLpMoment (P + p.α) κ u t x₀) := by
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left hgrad_le' hCY)
    _ = wholeLineLocalSignalAbsorptionConstant p P *
          wholeLineLocalLpMoment (P + p.α) κ u t x₀ := by
      unfold wholeLineLocalSignalAbsorptionConstant CY
      ring

/-! ## Absorbed critical energy inequality -/

def wholeLineLocalMomentLinearCoefficient (P κ : ℝ) : ℝ :=
  1 + (κ + κ ^ 2) / P

def wholeLineLocalMomentAbsorption
    (p : CMParams) (P κ : ℝ) : ℝ :=
  1 - wholeLineLocalChemotaxisCoefficient p P -
    (p.χ * p.m * κ / (P + p.m - 1)) *
      wholeLineLocalSignalAbsorptionConstant p P

def wholeLineLocalMomentAbsorptionSlope (p : CMParams) (P : ℝ) : ℝ :=
  (p.χ * p.m / (P + p.m - 1)) *
    wholeLineLocalSignalAbsorptionConstant p P

theorem exists_small_kappa_sub_mul_pos
    {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B) :
    ∃ κ : ℝ,
      κ = min (1 / 4 : ℝ) (c / (2 * (B + 1))) ∧
      0 < κ ∧ κ < 1 / 2 ∧ 0 < c - κ * B := by
  let κ : ℝ := min (1 / 4 : ℝ) (c / (2 * (B + 1)))
  have hB1 : 0 < B + 1 := by linarith
  have hden : 0 < 2 * (B + 1) := mul_pos (by norm_num) hB1
  have hκ_pos : 0 < κ := by
    dsimp [κ]
    exact lt_min (by norm_num) (div_pos hc hden)
  have hκ_half : κ < 1 / 2 := by
    have hκ_quarter : κ ≤ (1 / 4 : ℝ) := by
      dsimp [κ]
      exact min_le_left _ _
    norm_num at hκ_quarter ⊢
    linarith
  have hκ_upper : κ ≤ c / (2 * (B + 1)) := by
    dsimp [κ]
    exact min_le_right _ _
  have hscaled : κ * B ≤ (c / (2 * (B + 1))) * B :=
    mul_le_mul_of_nonneg_right hκ_upper hB
  have hratio : (c / (2 * (B + 1))) * B < c := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    have hprod : 0 < c * (B + 2) := mul_pos hc (by linarith)
    nlinarith
  refine ⟨κ, rfl, hκ_pos, hκ_half, ?_⟩
  linarith

/-- Admissibility always leaves room to choose a positive translated-weight
decay rate for which the resolver-gradient term is strictly absorbed. -/
theorem exists_small_localMomentWeight
    (p : CMParams) {P : ℝ} (hP : 1 < P) (hχ : 0 ≤ p.χ)
    (hadm : p.χ * (P - 1) < P + p.m - 1)
    (hcritical : p.α = p.m + p.γ - 1) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 / 2 ∧
      0 < wholeLineLocalMomentAbsorption p P κ := by
  let c : ℝ := 1 - wholeLineLocalChemotaxisCoefficient p P
  let B : ℝ := wholeLineLocalMomentAbsorptionSlope p P
  have hc : 0 < c := by
    dsimp [c]
    exact wholeLineLocalCriticalAbsorptionCoefficient_pos p hP hadm
  have hd : 0 < P + p.m - 1 := by linarith [p.hm]
  have hB : 0 ≤ B := by
    dsimp [B, wholeLineLocalMomentAbsorptionSlope]
    exact mul_nonneg
      (div_nonneg (mul_nonneg hχ (le_trans zero_le_one p.hm)) hd.le)
      (wholeLineLocalSignalAbsorptionConstant_pos p hP hcritical).le
  obtain ⟨κ, -, hκ, hκhalf, habs⟩ :=
    exists_small_kappa_sub_mul_pos hc hB
  refine ⟨κ, hκ, hκhalf, ?_⟩
  have heq : wholeLineLocalMomentAbsorption p P κ = c - κ * B := by
    dsimp [wholeLineLocalMomentAbsorption, c, B,
      wholeLineLocalMomentAbsorptionSlope]
    ring
  rw [heq]
  exact habs

theorem wholeLineLocalMomentLinearCoefficient_pos
    {P κ : ℝ} (hP : 1 < P) (hκ : 0 < κ) :
    0 < wholeLineLocalMomentLinearCoefficient P κ := by
  unfold wholeLineLocalMomentLinearCoefficient
  have hP0 : 0 < P := lt_trans zero_lt_one hP
  have : 0 ≤ κ + κ ^ 2 := by positivity
  positivity

/-- The fixed-time form of (3.8), before the harmless lower-order power is
absorbed. -/
theorem WholeLineLocalMomentEnergyData.critical_energy_absorbed
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentEnergyData p P κ T t x₀ u v)
    (hχ : 0 ≤ p.χ)
    (hκhalf : κ < 1 / 2)
    (hcritical : p.α = p.m + p.γ - 1)
    (hu : IsCUnifBdd (u t))
    (hu_nonneg : ∀ x, 0 ≤ u t x)
    (hv_resolver : v t = frozenElliptic p (u t)) :
    deriv (fun s : ℝ => wholeLineLocalLpEnergy P κ u s x₀) t +
          (4 * (P - 1) / P ^ 2) *
            wholeLineLocalLpHalfPowerGradient P κ u t x₀ +
          wholeLineLocalMomentAbsorption p P κ *
            wholeLineLocalLpMoment (P + p.α) κ u t x₀ ≤
      wholeLineLocalMomentLinearCoefficient P κ *
        wholeLineLocalLpMoment P κ u t x₀ := by
  have hv_nonneg : ∀ x, 0 ≤ v t x := by
    intro x
    rw [hv_resolver]
    exact frozenElliptic_nonneg p hu_nonneg x
  have henergy := H.critical_energy_inequality_drop_signal
    hχ hcritical hv_nonneg
  have hsignal := H.signalGradientAbs_le_high hκhalf hcritical
    hu hu_nonneg hv_resolver
  have hd : 0 < P + p.m - 1 := by linarith [H.hP, p.hm]
  have hmix :
      (p.χ * p.m * κ / (P + p.m - 1)) *
          wholeLineLocalLpSignalGradientAbs p P κ u v t x₀ ≤
        (p.χ * p.m * κ / (P + p.m - 1)) *
          (wholeLineLocalSignalAbsorptionConstant p P *
            wholeLineLocalLpMoment (P + p.α) κ u t x₀) := by
    exact mul_le_mul_of_nonneg_left hsignal
      (div_nonneg (mul_nonneg (mul_nonneg hχ (le_trans zero_le_one p.hm))
        H.hκ.le) hd.le)
  unfold wholeLineLocalMomentAbsorption
  unfold wholeLineLocalMomentLinearCoefficient
  linarith

theorem wholeLineLocalLpHalfPowerGradient_nonneg
    {P κ t x₀ : ℝ} {u : ℝ → ℝ → ℝ} :
    0 ≤ wholeLineLocalLpHalfPowerGradient P κ u t x₀ := by
  unfold wholeLineLocalLpHalfPowerGradient
  exact integral_nonneg fun x =>
    mul_nonneg (sq_nonneg _) (localizingWeightAt_pos κ x₀ x).le

theorem WholeLineLocalMomentEnergyData.critical_energy_absorbed_drop_gradient
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentEnergyData p P κ T t x₀ u v)
    (hχ : 0 ≤ p.χ)
    (hκhalf : κ < 1 / 2)
    (hcritical : p.α = p.m + p.γ - 1)
    (hu : IsCUnifBdd (u t))
    (hu_nonneg : ∀ x, 0 ≤ u t x)
    (hv_resolver : v t = frozenElliptic p (u t)) :
    deriv (fun s : ℝ => wholeLineLocalLpEnergy P κ u s x₀) t +
          wholeLineLocalMomentAbsorption p P κ *
            wholeLineLocalLpMoment (P + p.α) κ u t x₀ ≤
      wholeLineLocalMomentLinearCoefficient P κ *
        wholeLineLocalLpMoment P κ u t x₀ := by
  have hmain := H.critical_energy_absorbed hχ hκhalf hcritical
    hu hu_nonneg hv_resolver
  have hcoef : 0 ≤ 4 * (P - 1) / P ^ 2 := by
    exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr H.hP.le))
      (sq_nonneg P)
  have hgrad := wholeLineLocalLpHalfPowerGradient_nonneg
    (P := P) (κ := κ) (t := t) (x₀ := x₀) (u := u)
  nlinarith

/-! ## Lower-order power absorption and scalar damping -/

def wholeLineLocalMomentYoungCoefficient
    (p : CMParams) (P κ : ℝ) : ℝ :=
  wholeLineLocalMomentLinearCoefficient P κ + 1 / P

def wholeLineLocalMomentYoungRemainder
    (p : CMParams) (P κ : ℝ) : ℝ :=
  ((wholeLineLocalMomentYoungCoefficient p P κ /
      (wholeLineLocalMomentAbsorption p P κ *
        ((P + p.α) / P)) ^ (P / (P + p.α))) ^
      ((P + p.α) / ((P + p.α) - P))) /
    ((P + p.α) / ((P + p.α) - P))

def wholeLineLocalMomentDampingRhs
    (p : CMParams) (P κ : ℝ) : ℝ :=
  wholeLineLocalMomentYoungRemainder p P κ * (2 / κ)

theorem wholeLineLocalMomentYoungCoefficient_pos
    (p : CMParams) {P κ : ℝ} (hP : 1 < P) (hκ : 0 < κ) :
    0 < wholeLineLocalMomentYoungCoefficient p P κ := by
  unfold wholeLineLocalMomentYoungCoefficient
  have hlinear := wholeLineLocalMomentLinearCoefficient_pos hP hκ
  have hP0 : 0 < P := lt_trans zero_lt_one hP
  positivity

theorem wholeLineLocalMomentYoungRemainder_pos
    (p : CMParams) {P κ : ℝ} (hP : 1 < P) (hκ : 0 < κ)
    (habsorb : 0 < wholeLineLocalMomentAbsorption p P κ) :
    0 < wholeLineLocalMomentYoungRemainder p P κ := by
  unfold wholeLineLocalMomentYoungRemainder
  have hA := wholeLineLocalMomentYoungCoefficient_pos p hP hκ
  have hP0 : 0 < P := lt_trans zero_lt_one hP
  have hhigh : 0 < P + p.α := by linarith [p.hα]
  have hratio : 0 < (P + p.α) / P := div_pos hhigh hP0
  have hgap : 0 < (P + p.α) - P := by linarith [p.hα]
  have hconj : 0 < (P + p.α) / ((P + p.α) - P) :=
    div_pos hhigh hgap
  have hscale : 0 <
      (wholeLineLocalMomentAbsorption p P κ * ((P + p.α) / P)) ^
        (P / (P + p.α)) :=
    Real.rpow_pos_of_pos (mul_pos habsorb hratio) _
  positivity

theorem wholeLineLocalMoment_lowerOrder_pointwise
    (p : CMParams) {P κ z : ℝ}
    (hP : 1 < P) (hκ : 0 < κ)
    (habsorb : 0 < wholeLineLocalMomentAbsorption p P κ)
    (hz : 0 ≤ z) :
    wholeLineLocalMomentYoungCoefficient p P κ * z ^ P ≤
      wholeLineLocalMomentAbsorption p P κ * z ^ (P + p.α) +
        wholeLineLocalMomentYoungRemainder p P κ := by
  have hP0 : 0 < P := lt_trans zero_lt_one hP
  have hPs : P < P + p.α := by linarith [p.hα]
  have hA : 0 ≤ wholeLineLocalMomentYoungCoefficient p P κ :=
    (wholeLineLocalMomentYoungCoefficient_pos p hP hκ).le
  have hmain := scalar_rpow_young_absorb hP0 hPs hA habsorb hz
  simpa only [wholeLineLocalMomentYoungRemainder] using hmain

theorem WholeLineLocalMomentEnergyData.lowerOrder_integral_absorption
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentEnergyData p P κ T t x₀ u v)
    (habsorb : 0 < wholeLineLocalMomentAbsorption p P κ)
    (hu_nonneg : ∀ x, 0 ≤ u t x) :
    wholeLineLocalMomentYoungCoefficient p P κ *
        wholeLineLocalLpMoment P κ u t x₀ ≤
      wholeLineLocalMomentAbsorption p P κ *
          wholeLineLocalLpMoment (P + p.α) κ u t x₀ +
        wholeLineLocalMomentYoungRemainder p P κ *
          ∫ x : ℝ, localizingWeightAt κ x₀ x := by
  let A := wholeLineLocalMomentYoungCoefficient p P κ
  let delta := wholeLineLocalMomentAbsorption p P κ
  let B := wholeLineLocalMomentYoungRemainder p P κ
  have hleft : Integrable (fun x : ℝ =>
      A * ((u t x) ^ P * localizingWeightAt κ x₀ x)) :=
    H.moment_integrable.const_mul A
  have hhigh : Integrable (fun x : ℝ =>
      delta * ((u t x) ^ (P + p.α) * localizingWeightAt κ x₀ x)) :=
    H.logistic_integrable.const_mul delta
  have hconst : Integrable (fun x : ℝ =>
      B * localizingWeightAt κ x₀ x) :=
    (localizingWeightAt_integrable H.hκ x₀).const_mul B
  have hpoint : ∀ x : ℝ,
      A * ((u t x) ^ P * localizingWeightAt κ x₀ x) ≤
        delta * ((u t x) ^ (P + p.α) * localizingWeightAt κ x₀ x) +
          B * localizingWeightAt κ x₀ x := by
    intro x
    have hy := wholeLineLocalMoment_lowerOrder_pointwise p H.hP H.hκ
      habsorb (hu_nonneg x)
    have hw := (localizingWeightAt_pos κ x₀ x).le
    have := mul_le_mul_of_nonneg_right hy hw
    dsimp [A, delta, B]
    nlinarith
  calc
    wholeLineLocalMomentYoungCoefficient p P κ *
        wholeLineLocalLpMoment P κ u t x₀ =
      ∫ x : ℝ, A *
        ((u t x) ^ P * localizingWeightAt κ x₀ x) := by
        rw [integral_const_mul]
        rfl
    _ ≤ ∫ x : ℝ,
        delta * ((u t x) ^ (P + p.α) * localizingWeightAt κ x₀ x) +
          B * localizingWeightAt κ x₀ x :=
      integral_mono hleft (hhigh.add hconst) hpoint
    _ = wholeLineLocalMomentAbsorption p P κ *
          wholeLineLocalLpMoment (P + p.α) κ u t x₀ +
        wholeLineLocalMomentYoungRemainder p P κ *
          ∫ x : ℝ, localizingWeightAt κ x₀ x := by
      rw [integral_add hhigh hconst, integral_const_mul,
        integral_const_mul]
      rfl

theorem WholeLineLocalMomentEnergyData.critical_energy_damping
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentEnergyData p P κ T t x₀ u v)
    (hχ : 0 ≤ p.χ)
    (hκhalf : κ < 1 / 2)
    (hcritical : p.α = p.m + p.γ - 1)
    (habsorb : 0 < wholeLineLocalMomentAbsorption p P κ)
    (hu : IsCUnifBdd (u t))
    (hu_nonneg : ∀ x, 0 ≤ u t x)
    (hv_resolver : v t = frozenElliptic p (u t)) :
    deriv (fun s : ℝ => wholeLineLocalLpEnergy P κ u s x₀) t +
        wholeLineLocalLpEnergy P κ u t x₀ ≤
      wholeLineLocalMomentDampingRhs p P κ := by
  have henergy := H.critical_energy_absorbed_drop_gradient
    hχ hκhalf hcritical hu hu_nonneg hv_resolver
  have hyoung := H.lowerOrder_integral_absorption habsorb hu_nonneg
  have hP0 : 0 < P := lt_trans zero_lt_one H.hP
  have hB : 0 ≤ wholeLineLocalMomentYoungRemainder p P κ :=
    (wholeLineLocalMomentYoungRemainder_pos p H.hP H.hκ habsorb).le
  have hweight := integral_localizingWeightAt_le_two_div H.hκ x₀
  have hweight_scaled :
      wholeLineLocalMomentYoungRemainder p P κ *
          (∫ x : ℝ, localizingWeightAt κ x₀ x) ≤
        wholeLineLocalMomentYoungRemainder p P κ * (2 / κ) :=
    mul_le_mul_of_nonneg_left hweight hB
  change deriv (fun s : ℝ => wholeLineLocalLpEnergy P κ u s x₀) t +
      (1 / P) * wholeLineLocalLpMoment P κ u t x₀ ≤
        wholeLineLocalMomentDampingRhs p P κ
  unfold wholeLineLocalMomentYoungCoefficient at hyoung
  unfold wholeLineLocalMomentDampingRhs
  nlinarith

/-- Positive-time damping, with continuity at the initial endpoint, gives a
uniform scalar bound without requiring differentiability at time zero. -/
theorem scalarEnergy_uniform_bound_of_positive_time_damping
    {E : ℝ → ℝ} {T lam K : ℝ}
    (hT : 0 ≤ T) (hlam : 0 < lam)
    (hcont : ContinuousOn E (Icc 0 T))
    (hderiv : ∀ s ∈ Ioo (0 : ℝ) T, HasDerivAt E (deriv E s) s)
    (hdamp : ∀ s ∈ Ioo (0 : ℝ) T,
      deriv E s + lam * E s ≤ K) :
    ∀ t ∈ Icc (0 : ℝ) T, E t ≤ max (E 0) (K / lam) := by
  let R : ℝ := max (E 0) (K / lam)
  let H : ℝ → ℝ := fun t => E t - R
  have hKR : K ≤ lam * R := by
    have h := mul_le_mul_of_nonneg_left
      (le_max_right (E 0) (K / lam)) hlam.le
    dsimp [R]
    field_simp [hlam.ne'] at h
    exact h
  have hHcont : ContinuousOn H (Icc 0 T) :=
    hcont.sub continuousOn_const
  have hHderiv : ∀ s ∈ Ioo (0 : ℝ) T,
      HasDerivWithinAt H (deriv H s) (Ici s) s := by
    intro s hs
    have h0 : HasDerivAt H (deriv E s) s := by
      simpa only [H] using (hderiv s hs).sub_const R
    exact (h0.congr_deriv h0.deriv.symm).hasDerivWithinAt
  have hHgrowth : ∀ s ∈ Ioo (0 : ℝ) T,
      deriv H s ≤ -lam * H s := by
    intro s hs
    have hd := hdamp s hs
    have hdeq : deriv H s = deriv E s :=
      ((hderiv s hs).sub_const R).deriv
    dsimp [H]
    rw [hdeq]
    nlinarith
  intro t ht
  have hbound := scalarEnergy_crude_exponential_bound_of_positive_time_deriv
    (E := H) (C := -lam) (T := T) hT hHcont hHderiv hHgrowth t ht
  have hH0 : H 0 ≤ 0 := by
    dsimp [H, R]
    exact sub_nonpos.mpr (le_max_left _ _)
  have hexp : 0 < Real.exp (-lam * t) := Real.exp_pos _
  have hzero : H 0 * Real.exp (-lam * t) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hH0 hexp.le
  dsimp [H, R] at hbound ⊢
  linarith

/-! ## Uniform closure in time and in the translated centre -/

/-- Analytic data for the time-uniform closure.  The fixed-time fields are
exactly the primitive whole-line regularity/integrability data used in L2.
The resolver identity is recorded explicitly because the elliptic PDE alone
does not rule out unbounded homogeneous solutions. -/
structure WholeLineLocalMomentBoundData
    (p : CMParams) (P κ T U₀ : ℝ) (u v : ℝ → ℝ → ℝ) where
  hT : 0 ≤ T
  hP : max 1 (max p.m p.γ) < P
  hκ : 0 < κ
  hκhalf : κ < 1 / 2
  hχ : 0 ≤ p.χ
  hcritical : p.α = p.m + p.γ - 1
  admissible : p.χ * (P - 1) < P + p.m - 1
  absorption_pos : 0 < wholeLineLocalMomentAbsorption p P κ
  energyData : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x₀ : ℝ,
    WholeLineLocalMomentEnergyData p P κ T t x₀ u v
  u_nonnegative : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : ℝ, 0 ≤ u t x
  u_slice_isCUnifBdd : ∀ t ∈ Ioo (0 : ℝ) T, IsCUnifBdd (u t)
  resolver : ∀ t ∈ Ioo (0 : ℝ) T, v t = frozenElliptic p (u t)
  energy_continuous : ∀ x₀ : ℝ, ContinuousOn
    (fun t : ℝ => wholeLineLocalLpEnergy P κ u t x₀) (Icc 0 T)
  hU₀ : 0 ≤ U₀
  initial_isCUnifBdd : IsCUnifBdd (u 0)
  initial_upper : ∀ x : ℝ, u 0 x ≤ U₀

def wholeLineLocalMomentUniformBound
    (p : CMParams) (P κ U₀ : ℝ) : ℝ :=
  P * max ((U₀ ^ P * (2 / κ)) / P)
    (wholeLineLocalMomentDampingRhs p P κ)

theorem WholeLineLocalMomentBoundData.uniformlyLocalLpBounded
    {p : CMParams} {P κ T U₀ : ℝ} {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentBoundData p P κ T U₀ u v) :
    UniformlyLocalLpBounded P κ u T
      (wholeLineLocalMomentUniformBound p P κ U₀) := by
  have hP : 1 < P :=
    lt_of_le_of_lt (le_max_left 1 (max p.m p.γ)) H.hP
  have hP0 : 0 < P := lt_trans zero_lt_one hP
  intro t ht x₀
  let E : ℝ → ℝ := fun s => wholeLineLocalLpEnergy P κ u s x₀
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) T,
      HasDerivAt E (deriv E s) s := by
    intro s hs
    have hd := (H.energyData s hs x₀).energy_hasDerivAt
    exact hd.congr_deriv hd.deriv.symm
  have hdamp : ∀ s ∈ Ioo (0 : ℝ) T,
      deriv E s + E s ≤ wholeLineLocalMomentDampingRhs p P κ := by
    intro s hs
    exact (H.energyData s hs x₀).critical_energy_damping
      H.hχ H.hκhalf H.hcritical H.absorption_pos
      (H.u_slice_isCUnifBdd s hs)
      (H.u_nonnegative s ⟨hs.1.le, hs.2.le⟩)
      (H.resolver s hs)
  have hdamp_one : ∀ s ∈ Ioo (0 : ℝ) T,
      deriv E s + 1 * E s ≤ wholeLineLocalMomentDampingRhs p P κ := by
    simpa only [one_mul] using hdamp
  have hscalar := scalarEnergy_uniform_bound_of_positive_time_damping
    (E := E) (T := T) (lam := 1)
    (K := wholeLineLocalMomentDampingRhs p P κ)
    H.hT one_pos (H.energy_continuous x₀) hderiv hdamp_one
    t ⟨ht.1, ht.2.le⟩
  have hscalar' : E t ≤
      max (E 0) (wholeLineLocalMomentDampingRhs p P κ) := by
    simpa only [div_one] using hscalar
  have hu0_nonneg : ∀ x : ℝ, 0 ≤ u 0 x :=
    H.u_nonnegative 0 ⟨le_rfl, H.hT⟩
  have hmoment0 :
      wholeLineLocalLpMoment P κ u 0 x₀ ≤ U₀ ^ P * (2 / κ) :=
    wholeLineLocalLpMoment_le_two_mul_div hP0.le H.hκ H.hU₀
      H.initial_isCUnifBdd.1 hu0_nonneg H.initial_upper
  have hE0 : E 0 ≤ (U₀ ^ P * (2 / κ)) / P := by
    change (1 / P) * wholeLineLocalLpMoment P κ u 0 x₀ ≤
      (U₀ ^ P * (2 / κ)) / P
    have := mul_le_mul_of_nonneg_left hmoment0 (one_div_nonneg.mpr hP0.le)
    convert this using 1 <;> field_simp [hP0.ne']
  have hmax :
      max (E 0) (wholeLineLocalMomentDampingRhs p P κ) ≤
        max ((U₀ ^ P * (2 / κ)) / P)
          (wholeLineLocalMomentDampingRhs p P κ) :=
    max_le_max hE0 (le_refl _)
  have hEt : E t ≤
      max ((U₀ ^ P * (2 / κ)) / P)
        (wholeLineLocalMomentDampingRhs p P κ) := by
    exact hscalar'.trans hmax
  have hscaled := mul_le_mul_of_nonneg_left hEt hP0.le
  have hmoment_eq :
      wholeLineLocalLpMoment P κ u t x₀ = P * E t := by
    dsimp [E, wholeLineLocalLpEnergy]
    field_simp [hP0.ne']
  rw [hmoment_eq]
  exact hscaled

theorem WholeLineLocalMomentBoundData.exists_uniformlyLocalLpBounded
    {p : CMParams} {P κ T U₀ : ℝ} {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentBoundData p P κ T U₀ u v) :
    ∃ K : ℝ, UniformlyLocalLpBounded P κ u T K :=
  ⟨wholeLineLocalMomentUniformBound p P κ U₀,
    H.uniformlyLocalLpBounded⟩

section AxiomAudit

#print axioms localizingWeightAtExponentialWeight
#print axioms WholeLineLocalMomentEnergyData.signalGradientAbs_le_high
#print axioms exists_small_localMomentWeight
#print axioms WholeLineLocalMomentBoundData.uniformlyLocalLpBounded

end AxiomAudit

end ShenWork.Paper1
