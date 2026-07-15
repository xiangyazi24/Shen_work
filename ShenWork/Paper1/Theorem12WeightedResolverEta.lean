import ShenWork.Paper1.Theorem12Step4EnergyProducer
import ShenWork.Paper1.WaveRotheClose

open Filter MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

/-!
# The frozen resolver on exponentially weighted `L²`

The Green kernel of `(-∂ₓₓ + 1)⁻¹` is `G(z) = (1 / 2) exp (-|z|)`.
After conjugation by `exp (eta * x)`, its exact `L¹` mass is
`1 / (1 - eta²)`.  The normalized conjugated kernel below is a convex
combination of the already-proved one-sided exponential Markov kernels.
This gives a direct Schur estimate and never assumes weighted integrability
of a solution at positive time.
-/

/-- The exact operator constant for the frozen resolver on `L²_eta`. -/
def weightedResolverEtaConstant (eta : ℝ) : ℝ :=
  1 / (1 - eta ^ 2)

/-- The normalized conjugated Green kernel.  Away from the diagonal it is
`(1 - eta²) / 2 * exp (-|x-y| + eta*(x-y))`. -/
def weightedResolverMarkovKernel (eta : ℝ) (x y : ℝ) : ℝ :=
  ((1 + eta) / 2) * leftExpMarkovKernel (1 - eta) x y +
    ((1 - eta) / 2) * rightExpMarkovKernel (1 + eta) x y

theorem weightedResolverMarkovKernel_measurable (eta : ℝ) :
    Measurable (Function.uncurry (weightedResolverMarkovKernel eta)) := by
  unfold weightedResolverMarkovKernel Function.uncurry
  exact
    ((leftExpMarkovKernel_measurable (1 - eta)).const_mul
      ((1 + eta) / 2)).add
    ((rightExpMarkovKernel_measurable (1 + eta)).const_mul
      ((1 - eta) / 2))

theorem weightedResolverMarkovKernel_nonneg
    {eta : ℝ} (heta_nonneg : 0 ≤ eta) (heta_one : eta < 1)
    (x y : ℝ) :
    0 ≤ weightedResolverMarkovKernel eta x y := by
  unfold weightedResolverMarkovKernel
  have hleft : 0 ≤ (1 + eta) / 2 := by linarith
  have hright : 0 ≤ (1 - eta) / 2 := by linarith
  have hminus : 0 ≤ 1 - eta := by linarith
  have hplus : 0 ≤ 1 + eta := by linarith
  exact add_nonneg
    (mul_nonneg hleft
      (leftExpMarkovKernel_nonneg hminus x y))
    (mul_nonneg hright
      (leftExpMarkovKernel_nonneg hplus y x))

theorem weightedResolverMarkovKernel_row_integrable
    {eta : ℝ} (heta_nonneg : 0 ≤ eta) (heta_one : eta < 1)
    (x : ℝ) :
    Integrable (weightedResolverMarkovKernel eta x) := by
  have hminus : 0 < 1 - eta := by linarith
  have hplus : 0 < 1 + eta := by linarith
  unfold weightedResolverMarkovKernel rightExpMarkovKernel
  exact
    ((leftExpMarkovKernel_row_integrable hminus x).const_mul
      ((1 + eta) / 2)).add
    ((leftExpMarkovKernel_col_integrable hplus x).const_mul
      ((1 - eta) / 2))

theorem weightedResolverMarkovKernel_row_mass
    {eta : ℝ} (heta_nonneg : 0 ≤ eta) (heta_one : eta < 1)
    (x : ℝ) :
    ∫ y : ℝ, weightedResolverMarkovKernel eta x y = 1 := by
  have hminus : 0 < 1 - eta := by linarith
  have hplus : 0 < 1 + eta := by linarith
  have hleft := leftExpMarkovKernel_row_integrable
    hminus x
  have hright := leftExpMarkovKernel_col_integrable hplus x
  unfold weightedResolverMarkovKernel rightExpMarkovKernel
  rw [integral_add (hleft.const_mul ((1 + eta) / 2))
      (hright.const_mul ((1 - eta) / 2)),
    integral_const_mul, integral_const_mul,
    leftExpMarkovKernel_row_mass hminus,
    leftExpMarkovKernel_col_mass hplus]
  ring

theorem weightedResolverMarkovKernel_col_integrable
    {eta : ℝ} (heta_nonneg : 0 ≤ eta) (heta_one : eta < 1)
    (y : ℝ) :
    Integrable (fun x => weightedResolverMarkovKernel eta x y) := by
  have hminus : 0 < 1 - eta := by linarith
  have hplus : 0 < 1 + eta := by linarith
  unfold weightedResolverMarkovKernel rightExpMarkovKernel
  exact
    ((leftExpMarkovKernel_col_integrable hminus y).const_mul
      ((1 + eta) / 2)).add
    ((leftExpMarkovKernel_row_integrable hplus y).const_mul
      ((1 - eta) / 2))

theorem weightedResolverMarkovKernel_col_mass
    {eta : ℝ} (heta_nonneg : 0 ≤ eta) (heta_one : eta < 1)
    (y : ℝ) :
    ∫ x : ℝ, weightedResolverMarkovKernel eta x y = 1 := by
  have hminus : 0 < 1 - eta := by linarith
  have hplus : 0 < 1 + eta := by linarith
  have hleft := leftExpMarkovKernel_col_integrable
    hminus y
  have hright := leftExpMarkovKernel_row_integrable hplus y
  unfold weightedResolverMarkovKernel rightExpMarkovKernel
  rw [integral_add (hleft.const_mul ((1 + eta) / 2))
      (hright.const_mul ((1 - eta) / 2)),
    integral_const_mul, integral_const_mul,
    leftExpMarkovKernel_col_mass hminus,
    leftExpMarkovKernel_row_mass hplus]
  ring

theorem weightedResolverMarkovKernel_l2_contraction
    {eta : ℝ} (heta_nonneg : 0 ≤ eta) (heta_one : eta < 1)
    {q : ℝ → ℝ} (hq_meas : Measurable q)
    (hq_sq : Integrable (fun y => q y ^ 2)) :
    Integrable (fun x =>
        (∫ y : ℝ, weightedResolverMarkovKernel eta x y * |q y|) ^ 2) ∧
      (∫ x : ℝ,
          (∫ y : ℝ,
            weightedResolverMarkovKernel eta x y * |q y|) ^ 2) ≤
        ∫ y : ℝ, q y ^ 2 := by
  exact markovKernel_l2_contraction
    (weightedResolverMarkovKernel eta) q
    (weightedResolverMarkovKernel_measurable eta)
    (weightedResolverMarkovKernel_nonneg heta_nonneg heta_one)
    (weightedResolverMarkovKernel_row_integrable heta_nonneg heta_one)
    (weightedResolverMarkovKernel_row_mass heta_nonneg heta_one)
    (weightedResolverMarkovKernel_col_integrable heta_nonneg heta_one)
    (weightedResolverMarkovKernel_col_mass heta_nonneg heta_one)
    hq_meas hq_sq

private theorem weightedResolverEtaConstant_pos
    {eta : ℝ} (heta_nonneg : 0 ≤ eta) (heta_one : eta < 1) :
    0 < weightedResolverEtaConstant eta := by
  unfold weightedResolverEtaConstant
  have heta_sq : eta ^ 2 < 1 := by nlinarith
  exact one_div_pos.mpr (sub_pos.mpr heta_sq)

private theorem weightedResolver_kernel_ae_identity
    {eta : ℝ} (heta_nonneg : 0 ≤ eta) (heta_one : eta < 1)
    (s : ℝ → ℝ) (x : ℝ) :
    ∀ᵐ y : ℝ ∂volume,
      (1 / 2 : ℝ) * Real.exp (eta * x) *
          (Real.exp (-|x - y|) * |s y|) =
        weightedResolverEtaConstant eta *
          (weightedResolverMarkovKernel eta x y *
            |Real.exp (eta * y) * s y|) := by
  filter_upwards [Measure.ae_ne volume x] with y hy
  have hden : 1 - eta ^ 2 ≠ 0 := by
    have : eta ^ 2 < 1 := by nlinarith
    linarith
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  rcases lt_or_gt_of_ne hy with hyx | hxy
  · have hnot : ¬ x < y := not_lt.mpr hyx.le
    have habs : |x - y| = x - y := abs_of_nonneg (sub_nonneg.mpr hyx.le)
    simp [weightedResolverMarkovKernel, weightedResolverEtaConstant,
      leftExpMarkovKernel, rightExpMarkovKernel, hyx, hnot, habs]
    rw [show (2 : ℝ)⁻¹ * Real.exp (eta * x) *
        (Real.exp (y - x) * |s y|) =
        (2 : ℝ)⁻¹ * (Real.exp (eta * x) * Real.exp (y - x)) *
          |s y| by ring,
      show Real.exp (eta * x) * Real.exp (y - x) =
        Real.exp (-(1 - eta) * (x - y)) * Real.exp (eta * y) by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring]
    field_simp [hden]
    ring
  · have hnot : ¬ y < x := not_lt.mpr hxy.le
    have habs : |x - y| = y - x := by
      rw [abs_of_neg (sub_neg.mpr hxy)]
      ring
    simp [weightedResolverMarkovKernel, weightedResolverEtaConstant,
      leftExpMarkovKernel, rightExpMarkovKernel, hxy, hnot, habs]
    rw [show (2 : ℝ)⁻¹ * Real.exp (eta * x) *
        (Real.exp (x - y) * |s y|) =
        (2 : ℝ)⁻¹ * (Real.exp (eta * x) * Real.exp (x - y)) *
          |s y| by ring,
      show Real.exp (eta * x) * Real.exp (x - y) =
        Real.exp (-(1 + eta) * (y - x)) * Real.exp (eta * y) by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring]
    field_simp [hden]
    ring

private theorem weightedResolver_envelope_l2
    {eta : ℝ} (heta_nonneg : 0 ≤ eta) (heta_one : eta < 1)
    {s : ℝ → ℝ} (hs : IsCUnifBdd s)
    (hq_sq : Integrable (fun y => (Real.exp (eta * y) * s y) ^ 2)) :
    let T := fun x => ∫ y : ℝ,
      weightedResolverMarkovKernel eta x y *
        |Real.exp (eta * y) * s y|
    Integrable (fun x => T x ^ 2) ∧
      (∫ x : ℝ, T x ^ 2) ≤
        ∫ y : ℝ, (Real.exp (eta * y) * s y) ^ 2 := by
  dsimp only
  apply weightedResolverMarkovKernel_l2_contraction
    heta_nonneg heta_one
  exact ((by fun_prop : Continuous fun y : ℝ => Real.exp (eta * y)).mul
    hs.1).measurable
  exact hq_sq

private theorem weightedResolver_value_pointwise_le
    {eta : ℝ} (heta_nonneg : 0 ≤ eta) (heta_one : eta < 1)
    {s : ℝ → ℝ} (hs : IsCUnifBdd s)
    (x : ℝ) :
    |Real.exp (eta * x) * Psi s 1 1 x| ≤
      weightedResolverEtaConstant eta *
        ∫ y : ℝ, weightedResolverMarkovKernel eta x y *
          |Real.exp (eta * y) * s y| := by
  have hsource_int : Integrable
      (fun y : ℝ => Real.exp (-|x - y|) * s y) := by
    simpa [Real.sqrt_one] using
      (Psi_kernel_integrable_of_isCUnifBdd (l := 1) one_pos hs x)
  have habs_integral :
      |∫ y : ℝ, Real.exp (-|x - y|) * s y| ≤
        ∫ y : ℝ, Real.exp (-|x - y|) * |s y| := by
    calc
      |∫ y : ℝ, Real.exp (-|x - y|) * s y| =
          ‖∫ y : ℝ, Real.exp (-|x - y|) * s y‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ∫ y : ℝ, ‖Real.exp (-|x - y|) * s y‖ :=
        norm_integral_le_integral_norm _
      _ = ∫ y : ℝ, Real.exp (-|x - y|) * |s y| := by
        apply integral_congr_ae
        filter_upwards with y
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    |Real.exp (eta * x) * Psi s 1 1 x| =
        (1 / 2 : ℝ) * Real.exp (eta * x) *
          |∫ y : ℝ, Real.exp (-|x - y|) * s y| := by
      unfold Psi
      simp only [Real.sqrt_one, mul_one]
      rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      ring
    _ ≤ (1 / 2 : ℝ) * Real.exp (eta * x) *
          ∫ y : ℝ, Real.exp (-|x - y|) * |s y| := by
      exact mul_le_mul_of_nonneg_left habs_integral
        (mul_nonneg (by norm_num) (Real.exp_nonneg _))
    _ = ∫ y : ℝ, (1 / 2 : ℝ) * Real.exp (eta * x) *
          (Real.exp (-|x - y|) * |s y|) := by
      rw [integral_const_mul]
    _ = ∫ y : ℝ, weightedResolverEtaConstant eta *
          (weightedResolverMarkovKernel eta x y *
            |Real.exp (eta * y) * s y|) := by
      apply integral_congr_ae
      exact weightedResolver_kernel_ae_identity heta_nonneg heta_one s x
    _ = weightedResolverEtaConstant eta *
          ∫ y : ℝ, weightedResolverMarkovKernel eta x y *
            |Real.exp (eta * y) * s y| := by
      rw [integral_const_mul]

/-- STEP 1a, value half.  The frozen Green resolver is bounded on `L²_eta`
with its exact weighted-kernel constant `1 / (1 - eta²)`. -/
theorem weighted_resolver_L2eta_bounded
    {eta : ℝ} (heta_nonneg : 0 ≤ eta) (heta_one : eta < 1)
    {s : ℝ → ℝ} (hs : IsCUnifBdd s)
    (hq_sq : Integrable (fun y => (Real.exp (eta * y) * s y) ^ 2)) :
    Integrable (fun x => (Real.exp (eta * x) * Psi s 1 1 x) ^ 2) ∧
      (∫ x : ℝ, (Real.exp (eta * x) * Psi s 1 1 x) ^ 2) ≤
        weightedResolverEtaConstant eta ^ 2 *
          ∫ y : ℝ, (Real.exp (eta * y) * s y) ^ 2 := by
  let T : ℝ → ℝ := fun x => ∫ y : ℝ,
    weightedResolverMarkovKernel eta x y *
      |Real.exp (eta * y) * s y|
  have hT := weightedResolver_envelope_l2 heta_nonneg heta_one hs hq_sq
  have hc : 0 ≤ weightedResolverEtaConstant eta :=
    (weightedResolverEtaConstant_pos heta_nonneg heta_one).le
  have hVcont : Continuous
      (fun x => Real.exp (eta * x) * Psi s 1 1 x) :=
    (by fun_prop : Continuous fun x : ℝ => Real.exp (eta * x)).mul
      (Psi_continuous one_pos one_pos hs)
  have hdom : Integrable
      (fun x => weightedResolverEtaConstant eta ^ 2 * T x ^ 2) :=
    hT.1.const_mul _
  have hpoint : ∀ x,
      (Real.exp (eta * x) * Psi s 1 1 x) ^ 2 ≤
        weightedResolverEtaConstant eta ^ 2 * T x ^ 2 := by
    intro x
    have hT0 : 0 ≤ T x := by
      dsimp [T]
      exact integral_nonneg fun y => mul_nonneg
        (weightedResolverMarkovKernel_nonneg heta_nonneg heta_one x y)
        (abs_nonneg _)
    have hraw := weightedResolver_value_pointwise_le
      heta_nonneg heta_one hs x
    have hraw' :
        |Real.exp (eta * x) * Psi s 1 1 x| ≤
          weightedResolverEtaConstant eta * T x := by
      simpa only [T] using hraw
    have hsquare := (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg hc hT0)).mpr hraw'
    simpa [sq_abs, mul_pow] using hsquare
  have hVint : Integrable
      (fun x => (Real.exp (eta * x) * Psi s 1 1 x) ^ 2) := by
    refine Integrable.mono' hdom (hVcont.pow 2).aestronglyMeasurable ?_
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint x
  refine ⟨hVint, ?_⟩
  calc
    (∫ x : ℝ, (Real.exp (eta * x) * Psi s 1 1 x) ^ 2) ≤
        ∫ x : ℝ, weightedResolverEtaConstant eta ^ 2 * T x ^ 2 :=
      integral_mono hVint hdom hpoint
    _ = weightedResolverEtaConstant eta ^ 2 * ∫ x : ℝ, T x ^ 2 := by
      rw [integral_const_mul]
    _ ≤ weightedResolverEtaConstant eta ^ 2 *
        ∫ y : ℝ, (Real.exp (eta * y) * s y) ^ 2 :=
      mul_le_mul_of_nonneg_left hT.2 (sq_nonneg _)

/-- Signed derivative-kernel representation for the frozen Green resolver. -/
theorem Psi_deriv_eq_frozenEllipticDerivKernel
    {s : ℝ → ℝ} (hs : IsCUnifBdd s) (x : ℝ) :
    deriv (Psi s 1 1) x =
      1 / 2 * ∫ y, frozenEllipticDerivKernel x y * s y := by
  have hfun :
      Psi s 1 1 = fun z =>
        1 / 2 * ∫ y, Real.exp (-(1 : ℝ) * |z - y|) * s y := by
    funext z
    unfold Psi
    simp only [Real.sqrt_one, mul_one]
  have hLeib := hasDerivAt_integral_exp_neg_mul_abs_sub_general
    (a := 1) one_pos hs x
  have hda := hLeib.const_mul (1 / 2)
  rw [hfun, hda.deriv]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  unfold frozenEllipticDerivKernel
  by_cases hyx : y ≤ x
  · simp only [hyx, if_true]
    ring_nf
  · simp only [hyx, if_false]
    ring_nf

private theorem weightedResolver_gradient_pointwise_le
    {eta : ℝ} (heta_nonneg : 0 ≤ eta) (heta_one : eta < 1)
    {s : ℝ → ℝ} (hs : IsCUnifBdd s)
    (x : ℝ) :
    |Real.exp (eta * x) * deriv (Psi s 1 1) x| ≤
      weightedResolverEtaConstant eta *
        ∫ y : ℝ, weightedResolverMarkovKernel eta x y *
          |Real.exp (eta * y) * s y| := by
  have hsource_int := frozenEllipticDerivKernel_mul_integrable hs x
  have habs_integral :
      |∫ y : ℝ, frozenEllipticDerivKernel x y * s y| ≤
        ∫ y : ℝ, Real.exp (-|x - y|) * |s y| := by
    calc
      |∫ y : ℝ, frozenEllipticDerivKernel x y * s y| =
          ‖∫ y : ℝ, frozenEllipticDerivKernel x y * s y‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ∫ y : ℝ, ‖frozenEllipticDerivKernel x y * s y‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ y : ℝ, Real.exp (-|x - y|) * |s y| := by
        apply integral_mono hsource_int.norm
        · have hdom : Integrable
              (fun y : ℝ => Real.exp (-|x - y|) * |s y|) := by
            have hbase : Integrable
                (fun y : ℝ => Real.exp (-|x - y|) * s y) := by
              simpa [Real.sqrt_one] using
                (Psi_kernel_integrable_of_isCUnifBdd
                  (l := 1) one_pos hs x)
            simpa [Real.norm_eq_abs, abs_mul,
              abs_of_pos (Real.exp_pos _)] using hbase.norm
          exact hdom
        · intro y
          change |frozenEllipticDerivKernel x y * s y| ≤
            Real.exp (-|x - y|) * |s y|
          rw [abs_mul]
          exact mul_le_mul
            (frozenEllipticDerivKernel_abs_le x y) le_rfl
            (abs_nonneg _) (Real.exp_nonneg _)
  calc
    |Real.exp (eta * x) * deriv (Psi s 1 1) x| =
        (1 / 2 : ℝ) * Real.exp (eta * x) *
          |∫ y : ℝ, frozenEllipticDerivKernel x y * s y| := by
      rw [Psi_deriv_eq_frozenEllipticDerivKernel hs x,
        abs_mul, abs_of_pos (Real.exp_pos _), abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      ring
    _ ≤ (1 / 2 : ℝ) * Real.exp (eta * x) *
          ∫ y : ℝ, Real.exp (-|x - y|) * |s y| := by
      exact mul_le_mul_of_nonneg_left habs_integral
        (mul_nonneg (by norm_num) (Real.exp_nonneg _))
    _ = ∫ y : ℝ, (1 / 2 : ℝ) * Real.exp (eta * x) *
          (Real.exp (-|x - y|) * |s y|) := by
      rw [integral_const_mul]
    _ = ∫ y : ℝ, weightedResolverEtaConstant eta *
          (weightedResolverMarkovKernel eta x y *
            |Real.exp (eta * y) * s y|) := by
      apply integral_congr_ae
      exact weightedResolver_kernel_ae_identity heta_nonneg heta_one s x
    _ = weightedResolverEtaConstant eta *
          ∫ y : ℝ, weightedResolverMarkovKernel eta x y *
            |Real.exp (eta * y) * s y| := by
      rw [integral_const_mul]

/-- STEP 1a, gradient half.  The actual spatial derivative `∂ₓ R`, not
the derivative of the conjugated field, has the same `L²_eta` bound. -/
theorem weighted_resolver_gradient_L2eta_bounded
    {eta : ℝ} (heta_nonneg : 0 ≤ eta) (heta_one : eta < 1)
    {s : ℝ → ℝ} (hs : IsCUnifBdd s)
    (hq_sq : Integrable (fun y => (Real.exp (eta * y) * s y) ^ 2)) :
    Integrable
        (fun x => (Real.exp (eta * x) * deriv (Psi s 1 1) x) ^ 2) ∧
      (∫ x : ℝ,
          (Real.exp (eta * x) * deriv (Psi s 1 1) x) ^ 2) ≤
        weightedResolverEtaConstant eta ^ 2 *
          ∫ y : ℝ, (Real.exp (eta * y) * s y) ^ 2 := by
  let T : ℝ → ℝ := fun x => ∫ y : ℝ,
    weightedResolverMarkovKernel eta x y *
      |Real.exp (eta * y) * s y|
  have hT := weightedResolver_envelope_l2 heta_nonneg heta_one hs hq_sq
  have hc : 0 ≤ weightedResolverEtaConstant eta :=
    (weightedResolverEtaConstant_pos heta_nonneg heta_one).le
  have hderivCont : Continuous (deriv (Psi s 1 1)) := by
    have hrep : deriv (Psi s 1 1) = fun x =>
        1 / 2 * ∫ y, frozenEllipticDerivKernelShift (x - y) * s y := by
      funext x
      rw [Psi_deriv_eq_frozenEllipticDerivKernel hs x]
      congr 1
      apply integral_congr_ae
      filter_upwards with y
      rw [frozenEllipticDerivKernel_eq_shift]
    rw [hrep]
    exact continuous_const.mul (deriv_kernel_conv_continuous hs)
  have hVcont : Continuous
      (fun x => Real.exp (eta * x) * deriv (Psi s 1 1) x) :=
    (by fun_prop : Continuous fun x : ℝ => Real.exp (eta * x)).mul hderivCont
  have hdom : Integrable
      (fun x => weightedResolverEtaConstant eta ^ 2 * T x ^ 2) :=
    hT.1.const_mul _
  have hpoint : ∀ x,
      (Real.exp (eta * x) * deriv (Psi s 1 1) x) ^ 2 ≤
        weightedResolverEtaConstant eta ^ 2 * T x ^ 2 := by
    intro x
    have hT0 : 0 ≤ T x := by
      dsimp [T]
      exact integral_nonneg fun y => mul_nonneg
        (weightedResolverMarkovKernel_nonneg heta_nonneg heta_one x y)
        (abs_nonneg _)
    have hraw := weightedResolver_gradient_pointwise_le
      heta_nonneg heta_one hs x
    have hraw' :
        |Real.exp (eta * x) * deriv (Psi s 1 1) x| ≤
          weightedResolverEtaConstant eta * T x := by
      simpa only [T] using hraw
    have hsquare := (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg hc hT0)).mpr hraw'
    simpa [sq_abs, mul_pow] using hsquare
  have hVint : Integrable
      (fun x => (Real.exp (eta * x) * deriv (Psi s 1 1) x) ^ 2) := by
    refine Integrable.mono' hdom (hVcont.pow 2).aestronglyMeasurable ?_
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint x
  refine ⟨hVint, ?_⟩
  calc
    (∫ x : ℝ,
        (Real.exp (eta * x) * deriv (Psi s 1 1) x) ^ 2) ≤
        ∫ x : ℝ, weightedResolverEtaConstant eta ^ 2 * T x ^ 2 :=
      integral_mono hVint hdom hpoint
    _ = weightedResolverEtaConstant eta ^ 2 * ∫ x : ℝ, T x ^ 2 := by
      rw [integral_const_mul]
    _ ≤ weightedResolverEtaConstant eta ^ 2 *
        ∫ y : ℝ, (Real.exp (eta * y) * s y) ^ 2 :=
      mul_le_mul_of_nonneg_left hT.2 (sq_nonneg _)

/-- STEP 1b.  The frozen-resolver gradient difference is bounded directly
from the weighted population difference.  No positive-time output
integrability is assumed. -/
theorem weighted_frozenElliptic_gradient_difference_L2eta_bounded
    (p : CMParams) {M eta : ℝ}
    (hM : 0 ≤ M) (heta_nonneg : 0 ≤ eta) (heta_one : eta < 1)
    {u1 u2 : ℝ → ℝ}
    (hu1 : IsCUnifBdd u1) (hu2 : IsCUnifBdd u2)
    (hu1_mem : ∀ x, u1 x ∈ Set.Icc (0 : ℝ) M)
    (hu2_mem : ∀ x, u2 x ∈ Set.Icc (0 : ℝ) M)
    (hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2)) :
    Integrable (fun x =>
        (Real.exp (eta * x) *
          (deriv (frozenElliptic p u2) x -
            deriv (frozenElliptic p u1) x)) ^ 2) ∧
      (∫ x : ℝ, (Real.exp (eta * x) *
          (deriv (frozenElliptic p u2) x -
            deriv (frozenElliptic p u1) x)) ^ 2) ≤
        (weightedResolverEtaConstant eta *
          (p.γ * M ^ (p.γ - 1))) ^ 2 *
          ∫ x : ℝ,
            Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2 := by
  let s : ℝ → ℝ := fun x => u2 x ^ p.γ - u1 x ^ p.γ
  let L : ℝ := p.γ * M ^ (p.γ - 1)
  have hs : IsCUnifBdd s := by
    dsimp [s]
    exact rpow_difference_isCUnifBdd p.hγ hu1 hu2 hu1_mem hu2_mem
  have hsource := weighted_power_difference_sq_integrable_and_bound
    p.hγ hM hu1 hu2 hu1_mem hu2_mem hclose
  have hsource_int : Integrable
      (fun x => (Real.exp (eta * x) * s x) ^ 2) := by
    simpa [s] using hsource.1
  have hgrad := weighted_resolver_gradient_L2eta_bounded
    heta_nonneg heta_one hs hsource_int
  have hdiff : ∀ x,
      deriv (frozenElliptic p u2) x -
          deriv (frozenElliptic p u1) x =
        deriv (Psi s 1 1) x := by
    intro x
    rw [frozenElliptic_deriv_diff_eq p hu2
      (fun y => (hu2_mem y).1) hu1 (fun y => (hu1_mem y).1) x,
      Psi_deriv_eq_frozenEllipticDerivKernel hs x]
  have houtput_int : Integrable (fun x =>
      (Real.exp (eta * x) *
        (deriv (frozenElliptic p u2) x -
          deriv (frozenElliptic p u1) x)) ^ 2) := by
    refine hgrad.1.congr (Eventually.of_forall fun x => ?_)
    change (Real.exp (eta * x) * deriv (Psi s 1 1) x) ^ 2 =
      (Real.exp (eta * x) *
        (deriv (frozenElliptic p u2) x -
          deriv (frozenElliptic p u1) x)) ^ 2
    rw [hdiff x]
  refine ⟨houtput_int, ?_⟩
  calc
    (∫ x : ℝ, (Real.exp (eta * x) *
        (deriv (frozenElliptic p u2) x -
          deriv (frozenElliptic p u1) x)) ^ 2) =
        ∫ x : ℝ,
          (Real.exp (eta * x) * deriv (Psi s 1 1) x) ^ 2 := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change (Real.exp (eta * x) *
            (deriv (frozenElliptic p u2) x -
              deriv (frozenElliptic p u1) x)) ^ 2 =
          (Real.exp (eta * x) * deriv (Psi s 1 1) x) ^ 2
        rw [hdiff x]
    _ ≤ weightedResolverEtaConstant eta ^ 2 *
          ∫ x : ℝ, (Real.exp (eta * x) * s x) ^ 2 := hgrad.2
    _ ≤ weightedResolverEtaConstant eta ^ 2 *
          (L ^ 2 * ∫ x : ℝ,
            Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [s, L] using hsource.2
      · exact sq_nonneg _
    _ = (weightedResolverEtaConstant eta *
          (p.γ * M ^ (p.γ - 1))) ^ 2 *
          ∫ x : ℝ,
            Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2 := by
      dsimp [L]
      ring

/-! ## Resolver estimate for smooth exponential exhaustions -/

/-- A positive weight whose two-point ratio grows at most like
`exp (k * |x-y|)` conjugates the Green derivative kernel to an `L¹` kernel
of mass `1 / (1-k)`.  This is the uniform estimate used for the smooth,
non-compact exhaustion in STEP 1c. -/
theorem weighted_resolver_gradient_of_ratio_bound
    {a s : ℝ → ℝ} {k : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1)
    (ha : Continuous a) (ha_pos : ∀ x, 0 < a x)
    (hratio : ∀ x y, a x ≤ Real.exp (k * |x - y|) * a y)
    (hs : IsCUnifBdd s)
    (hsource : Integrable (fun y => (a y * s y) ^ 2)) :
    Integrable (fun x => (a x * deriv (Psi s 1 1) x) ^ 2) ∧
      (∫ x : ℝ, (a x * deriv (Psi s 1 1) x) ^ 2) ≤
        (1 / (1 - k)) ^ 2 * ∫ y : ℝ, (a y * s y) ^ 2 := by
  let q : ℝ → ℝ := fun y => a y * s y
  let T : ℝ → ℝ := fun x => ∫ y : ℝ,
    laplaceMarkovKernel (1 - k) x y * |q y|
  have hgap : 0 < 1 - k := by linarith
  have hq_meas : Measurable q := (ha.mul hs.1).measurable
  have hT := laplaceMarkovKernel_l2_contraction hgap hq_meas hsource
  have hc : 0 ≤ 1 / (1 - k) := one_div_nonneg.mpr hgap.le
  have hpointKernel : ∀ x y,
      a x * ((1 / 2 : ℝ) * Real.exp (-|x - y|) * |s y|) ≤
        (1 / (1 - k)) *
          (laplaceMarkovKernel (1 - k) x y * |q y|) := by
    intro x y
    have hfac : 0 ≤
        (1 / 2 : ℝ) * Real.exp (-|x - y|) * |s y| := by positivity
    have hmul := mul_le_mul_of_nonneg_right (hratio x y) hfac
    have hay : |a y| = a y := abs_of_pos (ha_pos y)
    have hqabs : |q y| = a y * |s y| := by
      dsimp [q]
      rw [abs_mul, hay]
    calc
      a x * ((1 / 2 : ℝ) * Real.exp (-|x - y|) * |s y|) ≤
          (Real.exp (k * |x - y|) * a y) *
            ((1 / 2 : ℝ) * Real.exp (-|x - y|) * |s y|) := hmul
      _ = (1 / (1 - k)) *
          (laplaceMarkovKernel (1 - k) x y * |q y|) := by
        rw [hqabs]
        unfold laplaceMarkovKernel
        have hexp :
            Real.exp (k * |x - y|) * Real.exp (-|x - y|) =
              Real.exp (-(1 - k) * |x - y|) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [show Real.exp (k * |x - y|) * a y *
            ((1 / 2 : ℝ) * Real.exp (-|x - y|) * |s y|) =
            (1 / 2 : ℝ) *
              (Real.exp (k * |x - y|) * Real.exp (-|x - y|)) *
                (a y * |s y|) by ring,
          hexp]
        have hne : 1 - k ≠ 0 := ne_of_gt hgap
        field_simp [hne]
  have hpoint : ∀ x,
      |a x * deriv (Psi s 1 1) x| ≤ (1 / (1 - k)) * T x := by
    intro x
    have hsource_int := frozenEllipticDerivKernel_mul_integrable hs x
    have habsIntegral :
        |∫ y : ℝ, frozenEllipticDerivKernel x y * s y| ≤
          ∫ y : ℝ, Real.exp (-|x - y|) * |s y| := by
      calc
        |∫ y : ℝ, frozenEllipticDerivKernel x y * s y| =
            ‖∫ y : ℝ, frozenEllipticDerivKernel x y * s y‖ :=
          (Real.norm_eq_abs _).symm
        _ ≤ ∫ y : ℝ, ‖frozenEllipticDerivKernel x y * s y‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ y : ℝ, Real.exp (-|x - y|) * |s y| := by
          apply integral_mono hsource_int.norm
          · have hbase : Integrable
                (fun y : ℝ => Real.exp (-|x - y|) * s y) := by
              simpa [Real.sqrt_one] using
                (Psi_kernel_integrable_of_isCUnifBdd
                  (l := 1) one_pos hs x)
            simpa [Real.norm_eq_abs, abs_mul,
              abs_of_pos (Real.exp_pos _)] using hbase.norm
          · intro y
            change |frozenEllipticDerivKernel x y * s y| ≤
              Real.exp (-|x - y|) * |s y|
            rw [abs_mul]
            exact mul_le_mul
              (frozenEllipticDerivKernel_abs_le x y) le_rfl
              (abs_nonneg _) (Real.exp_nonneg _)
    calc
      |a x * deriv (Psi s 1 1) x| =
          a x * ((1 / 2 : ℝ) *
            |∫ y : ℝ, frozenEllipticDerivKernel x y * s y|) := by
        rw [Psi_deriv_eq_frozenEllipticDerivKernel hs x,
          abs_mul, abs_of_pos (ha_pos x), abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      _ ≤ a x * ((1 / 2 : ℝ) *
          ∫ y : ℝ, Real.exp (-|x - y|) * |s y|) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left habsIntegral (by norm_num))
          (ha_pos x).le
      _ = (a x * (1 / 2 : ℝ)) *
          ∫ y : ℝ, Real.exp (-|x - y|) * |s y| := by ring
      _ = ∫ y : ℝ,
          (a x * (1 / 2 : ℝ)) *
            (Real.exp (-|x - y|) * |s y|) := by
        rw [integral_const_mul]
      _ = ∫ y : ℝ,
          a x * ((1 / 2 : ℝ) * Real.exp (-|x - y|) * |s y|) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by ring
      _ ≤ ∫ y : ℝ, (1 / (1 - k)) *
          (laplaceMarkovKernel (1 - k) x y * |q y|) := by
        apply integral_mono
        · have hbase : Integrable
              (fun y : ℝ => Real.exp (-|x - y|) * s y) := by
            simpa [Real.sqrt_one] using
              (Psi_kernel_integrable_of_isCUnifBdd
                (l := 1) one_pos hs x)
          have hbaseAbs : Integrable
              (fun y : ℝ => Real.exp (-|x - y|) * |s y|) := by
            simpa [Real.norm_eq_abs, abs_mul,
              abs_of_pos (Real.exp_pos _)] using hbase.norm
          simpa [mul_assoc] using
            (hbaseAbs.const_mul (1 / 2)).const_mul (a x)
        · exact (laplaceMarkovKernel_mul_abs_integrable
            hgap hq_meas hsource x).const_mul (1 / (1 - k))
        · exact hpointKernel x
      _ = (1 / (1 - k)) * T x := by
        dsimp [T]
        rw [integral_const_mul]
  have hderivCont : Continuous (deriv (Psi s 1 1)) := by
    have hrep : deriv (Psi s 1 1) = fun x =>
        1 / 2 * ∫ y, frozenEllipticDerivKernelShift (x - y) * s y := by
      funext x
      rw [Psi_deriv_eq_frozenEllipticDerivKernel hs x]
      congr 1
      apply integral_congr_ae
      filter_upwards with y
      rw [frozenEllipticDerivKernel_eq_shift]
    rw [hrep]
    exact continuous_const.mul (deriv_kernel_conv_continuous hs)
  have hdom : Integrable (fun x => (1 / (1 - k)) ^ 2 * T x ^ 2) :=
    hT.1.const_mul _
  have hpointSq : ∀ x,
      (a x * deriv (Psi s 1 1) x) ^ 2 ≤
        (1 / (1 - k)) ^ 2 * T x ^ 2 := by
    intro x
    have hT0 : 0 ≤ T x := by
      dsimp [T]
      exact integral_nonneg fun y => mul_nonneg
        (laplaceMarkovKernel_nonneg hgap.le x y) (abs_nonneg _)
    have hsquare := (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg hc hT0)).mpr (hpoint x)
    simpa [sq_abs, mul_pow] using hsquare
  have hout : Integrable (fun x => (a x * deriv (Psi s 1 1) x) ^ 2) := by
    refine Integrable.mono' hdom
      ((ha.mul hderivCont).pow 2).aestronglyMeasurable ?_
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpointSq x
  refine ⟨hout, ?_⟩
  calc
    (∫ x : ℝ, (a x * deriv (Psi s 1 1) x) ^ 2) ≤
        ∫ x : ℝ, (1 / (1 - k)) ^ 2 * T x ^ 2 :=
      integral_mono hout hdom hpointSq
    _ = (1 / (1 - k)) ^ 2 * ∫ x : ℝ, T x ^ 2 := by
      rw [integral_const_mul]
    _ ≤ (1 / (1 - k)) ^ 2 * ∫ y : ℝ, (a y * s y) ^ 2 :=
      mul_le_mul_of_nonneg_left hT.2 (sq_nonneg _)

/-- STEP 1b for a positive smooth exhaustion weight with uniformly bounded
logarithmic slope. -/
theorem weighted_frozenElliptic_gradient_difference_of_ratio_bound
    (p : CMParams) {M k : ℝ} {a u1 u2 : ℝ → ℝ}
    (hM : 0 ≤ M) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (ha : Continuous a) (ha_pos : ∀ x, 0 < a x)
    (hratio : ∀ x y, a x ≤ Real.exp (k * |x - y|) * a y)
    (hu1 : IsCUnifBdd u1) (hu2 : IsCUnifBdd u2)
    (hu1_mem : ∀ x, u1 x ∈ Set.Icc (0 : ℝ) M)
    (hu2_mem : ∀ x, u2 x ∈ Set.Icc (0 : ℝ) M)
    (hclose : Integrable (fun x => (a x * (u2 x - u1 x)) ^ 2)) :
    Integrable (fun x =>
        (a x * (deriv (frozenElliptic p u2) x -
          deriv (frozenElliptic p u1) x)) ^ 2) ∧
      (∫ x : ℝ, (a x * (deriv (frozenElliptic p u2) x -
          deriv (frozenElliptic p u1) x)) ^ 2) ≤
        ((1 / (1 - k)) * (p.γ * M ^ (p.γ - 1))) ^ 2 *
          ∫ x : ℝ, (a x * (u2 x - u1 x)) ^ 2 := by
  let s : ℝ → ℝ := fun x => u2 x ^ p.γ - u1 x ^ p.γ
  let L : ℝ := p.γ * M ^ (p.γ - 1)
  have hs : IsCUnifBdd s := by
    dsimp [s]
    exact rpow_difference_isCUnifBdd p.hγ hu1 hu2 hu1_mem hu2_mem
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg (zero_le_one.trans p.hγ)
      (Real.rpow_nonneg hM _)
  have hsourcePoint : ∀ x,
      (a x * s x) ^ 2 ≤ L ^ 2 * (a x * (u2 x - u1 x)) ^ 2 := by
    intro x
    have hp := abs_rpow_sub_rpow_le_of_mem_Icc
      p.hγ hM (hu2_mem x) (hu1_mem x)
    have ha0 : 0 ≤ a x := (ha_pos x).le
    have habs : |a x * s x| ≤ L * |a x * (u2 x - u1 x)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha0]
      dsimp [s, L]
      calc
        a x * |u2 x ^ p.γ - u1 x ^ p.γ| ≤
            a x * (p.γ * M ^ (p.γ - 1) * |u2 x - u1 x|) :=
          mul_le_mul_of_nonneg_left hp ha0
        _ = p.γ * M ^ (p.γ - 1) * (a x * |u2 x - u1 x|) := by
          ring
    have hsq := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hL0 (abs_nonneg _))).2 habs
    simpa [sq_abs, mul_pow] using hsq
  have hsourceDom : Integrable
      (fun x => L ^ 2 * (a x * (u2 x - u1 x)) ^ 2) :=
    hclose.const_mul _
  have hsourceInt : Integrable (fun x => (a x * s x) ^ 2) := by
    refine Integrable.mono' hsourceDom
      ((ha.mul hs.1).pow 2).aestronglyMeasurable ?_
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hsourcePoint x
  have hsourceBound :
      (∫ x : ℝ, (a x * s x) ^ 2) ≤
        L ^ 2 * ∫ x : ℝ, (a x * (u2 x - u1 x)) ^ 2 := by
    calc
      (∫ x : ℝ, (a x * s x) ^ 2) ≤
          ∫ x : ℝ, L ^ 2 * (a x * (u2 x - u1 x)) ^ 2 :=
        integral_mono hsourceInt hsourceDom hsourcePoint
      _ = L ^ 2 * ∫ x : ℝ, (a x * (u2 x - u1 x)) ^ 2 := by
        rw [integral_const_mul]
  have hgrad := weighted_resolver_gradient_of_ratio_bound
    hk0 hk1 ha ha_pos hratio hs hsourceInt
  have hdiff : ∀ x,
      deriv (frozenElliptic p u2) x - deriv (frozenElliptic p u1) x =
        deriv (Psi s 1 1) x := by
    intro x
    rw [frozenElliptic_deriv_diff_eq p hu2
      (fun y => (hu2_mem y).1) hu1 (fun y => (hu1_mem y).1) x,
      Psi_deriv_eq_frozenEllipticDerivKernel hs x]
  have hout : Integrable (fun x =>
      (a x * (deriv (frozenElliptic p u2) x -
        deriv (frozenElliptic p u1) x)) ^ 2) := by
    refine hgrad.1.congr (Eventually.of_forall fun x => ?_)
    change (a x * deriv (Psi s 1 1) x) ^ 2 =
      (a x * (deriv (frozenElliptic p u2) x -
        deriv (frozenElliptic p u1) x)) ^ 2
    rw [hdiff x]
  refine ⟨hout, ?_⟩
  calc
    (∫ x : ℝ, (a x * (deriv (frozenElliptic p u2) x -
        deriv (frozenElliptic p u1) x)) ^ 2) =
        ∫ x : ℝ, (a x * deriv (Psi s 1 1) x) ^ 2 := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change (a x * (deriv (frozenElliptic p u2) x -
          deriv (frozenElliptic p u1) x)) ^ 2 =
            (a x * deriv (Psi s 1 1) x) ^ 2
        rw [hdiff x]
    _ ≤ (1 / (1 - k)) ^ 2 *
        ∫ x : ℝ, (a x * s x) ^ 2 := hgrad.2
    _ ≤ (1 / (1 - k)) ^ 2 *
        (L ^ 2 * ∫ x : ℝ, (a x * (u2 x - u1 x)) ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · exact hsourceBound
      · exact sq_nonneg _
    _ = ((1 / (1 - k)) * (p.γ * M ^ (p.γ - 1))) ^ 2 *
        ∫ x : ℝ, (a x * (u2 x - u1 x)) ^ 2 := by
      dsimp [L]
      ring

section Theorem12WeightedResolverEtaAxiomAudit

#print axioms weighted_resolver_L2eta_bounded
#print axioms weighted_resolver_gradient_L2eta_bounded
#print axioms weighted_frozenElliptic_gradient_difference_L2eta_bounded
#print axioms weighted_resolver_gradient_of_ratio_bound
#print axioms weighted_frozenElliptic_gradient_difference_of_ratio_bound

end Theorem12WeightedResolverEtaAxiomAudit

end ShenWork.Paper1
