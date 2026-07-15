import ShenWork.Paper1.Theorem12TentWeightFiniteness
import ShenWork.Paper1.Theorem12WeightedFiniteness
import ShenWork.Paper1.WholeLineWeightedRegularityConjugation

open Filter MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Uniform cap-weight kernel bounds

The logistic cap `capWeight eta R` is used on the *raw* population
perturbation.  Its square-root ratio is uniformly dominated, independently
of `R`, by the two-sided exponential ratio.  This is the pointwise input for
Schur estimates of the moving heat semigroup and its spatial derivative.
-/

/-- The cap is increasing in its spatial argument when `eta` is nonnegative. -/
theorem capWeight_monotone_space {eta : ℝ} (heta : 0 ≤ eta) (R : ℝ) :
    Monotone (capWeight eta R) := by
  apply monotone_of_deriv_nonneg
  · intro z
    exact (capWeight_hasDerivAt eta R z).differentiableAt
  · intro z
    rw [capWeight_deriv_eq]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) heta)
        (capWeight_pos eta R z).le)
      (by positivity)

/-- Uniform logarithmic-Lipschitz estimate for the logistic cap. -/
theorem capWeight_le_exp_abs_mul
    {eta : ℝ} (heta : 0 ≤ eta) (R x y : ℝ) :
    capWeight eta R x ≤
      Real.exp (2 * eta * |x - y|) * capWeight eta R y := by
  rcases le_total x y with hxy | hyx
  · have hmono : capWeight eta R x ≤ capWeight eta R y :=
      capWeight_monotone_space heta R hxy
    have hexp : 1 ≤ Real.exp (2 * eta * |x - y|) :=
      Real.one_le_exp (mul_nonneg (mul_nonneg (by norm_num) heta) (abs_nonneg _))
    calc
      capWeight eta R x ≤ capWeight eta R y := hmono
      _ ≤ Real.exp (2 * eta * |x - y|) * capWeight eta R y := by
        nlinarith [capWeight_pos eta R y]
  · have hden :
        1 + Real.exp (2 * eta * (y - R)) ≤
          1 + Real.exp (2 * eta * (x - R)) := by
      gcongr
    have hdiv :
        Real.exp (2 * eta * x) /
            (1 + Real.exp (2 * eta * (x - R))) ≤
          Real.exp (2 * eta * x) /
            (1 + Real.exp (2 * eta * (y - R))) :=
      div_le_div_of_nonneg_left (Real.exp_nonneg _)
        (by positivity) hden
    rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    unfold capWeight
    calc
      Real.exp (2 * eta * x) /
          (1 + Real.exp (2 * eta * (x - R))) ≤
        Real.exp (2 * eta * x) /
          (1 + Real.exp (2 * eta * (y - R))) := hdiv
      _ = Real.exp (2 * eta * (x - y)) *
          (Real.exp (2 * eta * y) /
            (1 + Real.exp (2 * eta * (y - R)))) := by
        rw [show Real.exp (2 * eta * x) =
            Real.exp (2 * eta * (x - y)) * Real.exp (2 * eta * y) by
          rw [← Real.exp_add]
          congr 1
          ring]
        ring

/-- Square-root cap ratio, the kernel conjugation factor. -/
def capWeightSqrtRatio (eta R x y : ℝ) : ℝ :=
  Real.sqrt (capWeight eta R x / capWeight eta R y)

/-- Square root of the cap, used to conjugate raw perturbations. -/
def capWeightSqrt (eta R x : ℝ) : ℝ :=
  Real.sqrt (capWeight eta R x)

theorem capWeightSqrt_continuous (eta R : ℝ) :
    Continuous (capWeightSqrt eta R) := by
  unfold capWeightSqrt
  exact (capWeight_continuous eta R).sqrt

theorem capWeightSqrt_pos (eta R x : ℝ) :
    0 < capWeightSqrt eta R x := by
  unfold capWeightSqrt
  exact Real.sqrt_pos.mpr (capWeight_pos eta R x)

theorem capWeightSqrt_sq (eta R x : ℝ) :
    capWeightSqrt eta R x ^ 2 = capWeight eta R x := by
  unfold capWeightSqrt
  exact Real.sq_sqrt (capWeight_pos eta R x).le

theorem capWeightSqrtRatio_nonneg (eta R x y : ℝ) :
    0 ≤ capWeightSqrtRatio eta R x y :=
  Real.sqrt_nonneg _

/-- The square-root cap ratio is bounded by `exp (eta * |x-y|)`, uniformly
in the cap radius `R`. -/
theorem capWeightSqrtRatio_le_exp_abs
    {eta : ℝ} (heta : 0 ≤ eta) (R x y : ℝ) :
    capWeightSqrtRatio eta R x y ≤ Real.exp (eta * |x - y|) := by
  unfold capWeightSqrtRatio
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have hcap := capWeight_le_exp_abs_mul heta R x y
    rw [div_le_iff₀ (capWeight_pos eta R y)]
    calc
      capWeight eta R x ≤
          Real.exp (2 * eta * |x - y|) * capWeight eta R y := hcap
      _ = Real.exp (eta * |x - y|) ^ 2 * capWeight eta R y := by
        rw [pow_two, ← Real.exp_add]
        congr 2
        ring

/-- Multiplicative form of the square-root ratio estimate, matching the
resolver API. -/
theorem capWeightSqrt_le_exp_abs_mul
    {eta : ℝ} (heta : 0 ≤ eta) (R x y : ℝ) :
    capWeightSqrt eta R x ≤
      Real.exp (eta * |x - y|) * capWeightSqrt eta R y := by
  have hratio := capWeightSqrtRatio_le_exp_abs heta R x y
  have hratio_eq : capWeightSqrtRatio eta R x y =
      capWeightSqrt eta R x / capWeightSqrt eta R y := by
    unfold capWeightSqrtRatio capWeightSqrt
    rw [Real.sqrt_div (capWeight_pos eta R x).le]
  rw [hratio_eq] at hratio
  have hy : capWeightSqrt eta R y ≠ 0 :=
    ne_of_gt (capWeightSqrt_pos eta R y)
  calc
    capWeightSqrt eta R x =
        (capWeightSqrt eta R x / capWeightSqrt eta R y) *
          capWeightSqrt eta R y := by field_simp
    _ ≤ Real.exp (eta * |x - y|) * capWeightSqrt eta R y :=
      mul_le_mul_of_nonneg_right hratio (capWeightSqrt_pos eta R y).le

theorem capWeightSqrt_mul_sq_eq
    (eta R x r : ℝ) :
    (capWeightSqrt eta R x * r) ^ 2 =
      capWeight eta R x * |r| ^ 2 := by
  rw [mul_pow, capWeightSqrt_sq, sq_abs]

/-- Cap-weight form of the frozen elliptic gradient estimate.  The cap is
applied to the raw population difference, so no exponential weight is
inserted twice. -/
theorem capWeight_frozenElliptic_gradient_difference_l2_bounded
    (p : CMParams) {M eta R : ℝ}
    (hM : 0 ≤ M) (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    {u1 u2 : ℝ → ℝ}
    (hu1 : IsCUnifBdd u1) (hu2 : IsCUnifBdd u2)
    (hu1_mem : ∀ x, u1 x ∈ Set.Icc (0 : ℝ) M)
    (hu2_mem : ∀ x, u2 x ∈ Set.Icc (0 : ℝ) M)
    (hclose : Integrable (fun x =>
      capWeight eta R x * |u2 x - u1 x| ^ 2)) :
    Integrable (fun x => capWeight eta R x *
        |deriv (frozenElliptic p u2) x -
          deriv (frozenElliptic p u1) x| ^ 2) ∧
      (∫ x : ℝ, capWeight eta R x *
          |deriv (frozenElliptic p u2) x -
            deriv (frozenElliptic p u1) x| ^ 2) ≤
        ((1 / (1 - eta)) * (p.γ * M ^ (p.γ - 1))) ^ 2 *
          ∫ x : ℝ, capWeight eta R x * |u2 x - u1 x| ^ 2 := by
  have hclose' : Integrable (fun x =>
      (capWeightSqrt eta R x * (u2 x - u1 x)) ^ 2) := by
    refine hclose.congr (Eventually.of_forall fun x => ?_)
    change capWeight eta R x * |u2 x - u1 x| ^ 2 =
      (capWeightSqrt eta R x * (u2 x - u1 x)) ^ 2
    exact (capWeightSqrt_mul_sq_eq eta R x (u2 x - u1 x)).symm
  have hgrad := weighted_frozenElliptic_gradient_difference_of_ratio_bound
    p hM heta0 heta1
    (capWeightSqrt_continuous eta R)
    (capWeightSqrt_pos eta R)
    (capWeightSqrt_le_exp_abs_mul heta0 R)
    hu1 hu2 hu1_mem hu2_mem hclose'
  have hout : Integrable (fun x => capWeight eta R x *
      |deriv (frozenElliptic p u2) x -
        deriv (frozenElliptic p u1) x| ^ 2) := by
    refine hgrad.1.congr (Eventually.of_forall fun x => ?_)
    change (capWeightSqrt eta R x *
        (deriv (frozenElliptic p u2) x -
          deriv (frozenElliptic p u1) x)) ^ 2 =
      capWeight eta R x *
        |deriv (frozenElliptic p u2) x -
          deriv (frozenElliptic p u1) x| ^ 2
    exact capWeightSqrt_mul_sq_eq eta R x
      (deriv (frozenElliptic p u2) x -
        deriv (frozenElliptic p u1) x)
  refine ⟨hout, ?_⟩
  calc
    (∫ x : ℝ, capWeight eta R x *
        |deriv (frozenElliptic p u2) x -
          deriv (frozenElliptic p u1) x| ^ 2) =
      ∫ x : ℝ,
        (capWeightSqrt eta R x *
          (deriv (frozenElliptic p u2) x -
            deriv (frozenElliptic p u1) x)) ^ 2 := by
      apply integral_congr_ae
      filter_upwards with x
      rw [capWeightSqrt_mul_sq_eq eta R x
        (deriv (frozenElliptic p u2) x -
          deriv (frozenElliptic p u1) x)]
    _ ≤ ((1 / (1 - eta)) * (p.γ * M ^ (p.γ - 1))) ^ 2 *
        ∫ x : ℝ,
          (capWeightSqrt eta R x * (u2 x - u1 x)) ^ 2 := hgrad.2
    _ = ((1 / (1 - eta)) * (p.γ * M ^ (p.γ - 1))) ^ 2 *
        ∫ x : ℝ, capWeight eta R x * |u2 x - u1 x| ^ 2 := by
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      rw [capWeightSqrt_mul_sq_eq eta R x (u2 x - u1 x)]

/-! ## Constant-mass Schur normalization -/

/-- The constant-mass form of the continuous Schur estimate.  It is a
scaling of `markovKernel_l2_contraction`; keeping it explicit avoids hiding
the cap-radius-independent kernel mass in downstream estimates. -/
theorem constantMassKernel_l2_contraction
    (K : ℝ → ℝ → ℝ) (q : ℝ → ℝ) (C : ℝ)
    (hC : 0 < C)
    (hK_meas : Measurable (Function.uncurry K))
    (hK_nn : ∀ x y, 0 ≤ K x y)
    (hrow_int : ∀ x, Integrable (K x))
    (hrow_mass : ∀ x, ∫ y : ℝ, K x y = C)
    (hcol_int : ∀ y, Integrable (fun x => K x y))
    (hcol_mass : ∀ y, ∫ x : ℝ, K x y = C)
    (hq_meas : Measurable q)
    (hq_sq : Integrable (fun y => q y ^ 2)) :
    Integrable (fun x => (∫ y : ℝ, K x y * |q y|) ^ 2) ∧
      (∫ x : ℝ, (∫ y : ℝ, K x y * |q y|) ^ 2) ≤
        C ^ 2 * ∫ y : ℝ, q y ^ 2 := by
  let K₀ : ℝ → ℝ → ℝ := fun x y => K x y / C
  have hK₀_meas : Measurable (Function.uncurry K₀) := by
    dsimp [K₀, Function.uncurry]
    fun_prop
  have hK₀_nn : ∀ x y, 0 ≤ K₀ x y := fun x y =>
    div_nonneg (hK_nn x y) hC.le
  have hK₀_row_int : ∀ x, Integrable (K₀ x) := by
    intro x
    simpa [K₀, div_eq_mul_inv, mul_comm] using
      (hrow_int x).const_mul C⁻¹
  have hK₀_col_int : ∀ y, Integrable (fun x => K₀ x y) := by
    intro y
    simpa [K₀, div_eq_mul_inv, mul_comm] using
      (hcol_int y).const_mul C⁻¹
  have hK₀_row_mass : ∀ x, ∫ y : ℝ, K₀ x y = 1 := by
    intro x
    change (∫ y : ℝ, K x y / C) = 1
    rw [integral_div, hrow_mass, div_self (ne_of_gt hC)]
  have hK₀_col_mass : ∀ y, ∫ x : ℝ, K₀ x y = 1 := by
    intro y
    change (∫ x : ℝ, K x y / C) = 1
    rw [integral_div, hcol_mass, div_self (ne_of_gt hC)]
  have hnormalized := markovKernel_l2_contraction K₀ q
    hK₀_meas hK₀_nn hK₀_row_int hK₀_row_mass
    hK₀_col_int hK₀_col_mass hq_meas hq_sq
  have hinner : ∀ x,
      (∫ y : ℝ, K x y * |q y|) =
        C * ∫ y : ℝ, K₀ x y * |q y| := by
    intro x
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    dsimp [K₀]
    field_simp
  have hfun :
      (fun x => (∫ y : ℝ, K x y * |q y|) ^ 2) =
        fun x => C ^ 2 * (∫ y : ℝ, K₀ x y * |q y|) ^ 2 := by
    funext x
    rw [hinner]
    ring
  rw [hfun]
  refine ⟨hnormalized.1.const_mul _, ?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hnormalized.2 (sq_nonneg C)

/-- Schur estimate for a nonnegative kernel dominated by a constant-mass
envelope. -/
theorem dominatedKernel_l2_contraction
    (K E : ℝ → ℝ → ℝ) (q : ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hK_meas : Measurable (Function.uncurry K))
    (hK_nn : ∀ x y, 0 ≤ K x y)
    (hKE : ∀ x y, K x y ≤ E x y)
    (hE_meas : Measurable (Function.uncurry E))
    (hE_nn : ∀ x y, 0 ≤ E x y)
    (hErow_int : ∀ x, Integrable (E x))
    (hErow_mass : ∀ x, ∫ y : ℝ, E x y = C)
    (hEcol_int : ∀ y, Integrable (fun x => E x y))
    (hEcol_mass : ∀ y, ∫ x : ℝ, E x y = C)
    (hq_meas : Measurable q)
    (hq_sq : Integrable (fun y => q y ^ 2)) :
    Integrable (fun x => (∫ y : ℝ, K x y * |q y|) ^ 2) ∧
      (∫ x : ℝ, (∫ y : ℝ, K x y * |q y|) ^ 2) ≤
        C ^ 2 * ∫ y : ℝ, q y ^ 2 := by
  let JE : ℝ × ℝ → ℝ := fun z => E z.1 z.2 * q z.2 ^ 2
  have hJE_meas : Measurable JE := by
    dsimp [JE]
    exact hE_meas.mul ((hq_meas.comp measurable_snd).pow_const 2)
  have hJE_int : Integrable JE (volume.prod volume) := by
    refine (integrable_prod_iff' hJE_meas.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · exact Eventually.of_forall fun y => by
        have heq : (fun x => JE (x, y)) = fun x => q y ^ 2 * E x y := by
          funext x
          dsimp [JE]
          ring
        rw [heq]
        exact (hEcol_int y).const_mul (q y ^ 2)
    · have heq : (fun y => ∫ x : ℝ, ‖JE (x, y)‖) =
          fun y => C * q y ^ 2 := by
        funext y
        have hnorm : (fun x => ‖JE (x, y)‖) =
            fun x => q y ^ 2 * E x y := by
          funext x
          rw [Real.norm_eq_abs, abs_of_nonneg]
          · dsimp [JE]
            ring
          · exact mul_nonneg (hE_nn x y) (sq_nonneg _)
        rw [hnorm, integral_const_mul, hEcol_mass]
        ring
      rw [heq]
      exact hq_sq.const_mul C
  let JK : ℝ × ℝ → ℝ := fun z => K z.1 z.2 * q z.2 ^ 2
  have hJK_meas : Measurable JK := by
    dsimp [JK]
    exact hK_meas.mul ((hq_meas.comp measurable_snd).pow_const 2)
  have hJK_int : Integrable JK (volume.prod volume) := by
    refine hJE_int.mono' hJK_meas.aestronglyMeasurable ?_
    filter_upwards with z
    change |K z.1 z.2 * q z.2 ^ 2| ≤ E z.1 z.2 * q z.2 ^ 2
    rw [abs_of_nonneg (mul_nonneg (hK_nn z.1 z.2) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (hKE z.1 z.2) (sq_nonneg _)
  have hKrow_int : ∀ x, Integrable (K x) := by
    intro x
    have hKx : Measurable (K x) :=
      hK_meas.comp (measurable_const.prodMk measurable_id)
    refine (hErow_int x).mono' hKx.aestronglyMeasurable ?_
    filter_upwards with y
    change |K x y| ≤ E x y
    rw [abs_of_nonneg (hK_nn x y)]
    exact hKE x y
  have hKcol_int : ∀ y, Integrable (fun x => K x y) := by
    intro y
    have hKy : Measurable (fun x => K x y) :=
      hK_meas.comp (measurable_id.prodMk measurable_const)
    refine (hEcol_int y).mono' hKy.aestronglyMeasurable ?_
    filter_upwards with x
    change |K x y| ≤ E x y
    rw [abs_of_nonneg (hK_nn x y)]
    exact hKE x y
  have hKrow_mass : ∀ x, (∫ y : ℝ, K x y) ≤ C := by
    intro x
    rw [← hErow_mass x]
    exact integral_mono (hKrow_int x) (hErow_int x) (hKE x)
  have hKcol_mass : ∀ y, (∫ x : ℝ, K x y) ≤ C := by
    intro y
    rw [← hEcol_mass y]
    exact integral_mono (hKcol_int y) (hEcol_int y) (fun x => hKE x y)
  let T : ℝ → ℝ := fun x => ∫ y : ℝ, K x y * |q y|
  let R : ℝ → ℝ := fun x => ∫ y : ℝ, JK (x, y)
  have hT_strong : StronglyMeasurable T := by
    apply StronglyMeasurable.integral_prod_right
    exact (hK_meas.mul ((hq_meas.comp measurable_snd).abs)).stronglyMeasurable
  have hR_int : Integrable R := hJK_int.integral_prod_left
  have hpoint : ∀ᵐ x : ℝ ∂volume, T x ^ 2 ≤ C * R x := by
    filter_upwards [hJK_int.prod_right_ae] with x hx
    let f : ℝ → ℝ := fun y => Real.sqrt (K x y)
    let g : ℝ → ℝ := fun y => Real.sqrt (K x y) * |q y|
    have hf_sq : Integrable (fun y => f y ^ 2) := by
      refine (hKrow_int x).congr (Eventually.of_forall fun y => ?_)
      dsimp [f]
      exact (Real.sq_sqrt (hK_nn x y)).symm
    have hg_sq : Integrable (fun y => g y ^ 2) := by
      refine hx.congr (Eventually.of_forall fun y => ?_)
      dsimp [g, JK]
      rw [mul_pow, Real.sq_sqrt (hK_nn x y), sq_abs]
    have hf_mem : MemLp f 2 volume :=
      (memLp_two_iff_integrable_sq (by fun_prop)).2 hf_sq
    have hg_mem : MemLp g 2 volume :=
      (memLp_two_iff_integrable_sq (by fun_prop)).2 hg_sq
    have hfg : Integrable (fun y => |f y * g y|) := by
      have hmul : Integrable (f * g) := hf_mem.integrable_mul hg_mem
      simpa [Pi.mul_apply, Real.norm_eq_abs] using hmul.norm
    have hcs := sq_integral_abs_mul_le_global hf_sq hg_sq hfg
    have hleft : (∫ y : ℝ, |f y * g y|) = T x := by
      apply integral_congr_ae
      filter_upwards with y
      dsimp [f, g, T]
      rw [← mul_assoc, ← pow_two, Real.sq_sqrt (hK_nn x y)]
      exact abs_of_nonneg (mul_nonneg (hK_nn x y) (abs_nonneg _))
    have hfirst : (∫ y : ℝ, f y ^ 2) = ∫ y : ℝ, K x y := by
      apply integral_congr_ae
      filter_upwards with y
      exact Real.sq_sqrt (hK_nn x y)
    have hsecond : (∫ y : ℝ, g y ^ 2) = R x := by
      apply integral_congr_ae
      filter_upwards with y
      dsimp [g, R, JK]
      rw [mul_pow, Real.sq_sqrt (hK_nn x y), sq_abs]
    rw [hleft, hfirst, hsecond] at hcs
    have hR0 : 0 ≤ R x := integral_nonneg fun y =>
      mul_nonneg (hK_nn x y) (sq_nonneg _)
    have hmass0 : 0 ≤ ∫ y : ℝ, K x y :=
      integral_nonneg (hK_nn x)
    nlinarith [hKrow_mass x]
  have hdom : Integrable (fun x => C * R x) := hR_int.const_mul C
  have hT_sq_int : Integrable (fun x => T x ^ 2) := by
    refine hdom.mono' (hT_strong.pow 2).aestronglyMeasurable ?_
    filter_upwards [hpoint] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hx
  have hmain : (∫ x : ℝ, T x ^ 2) ≤ C * ∫ x : ℝ, R x := by
    calc
      (∫ x : ℝ, T x ^ 2) ≤ ∫ x : ℝ, C * R x :=
        integral_mono_ae hT_sq_int hdom hpoint
      _ = C * ∫ x : ℝ, R x := integral_const_mul C R
  have hR_bound : (∫ x : ℝ, R x) ≤ C * ∫ y : ℝ, q y ^ 2 := by
    dsimp [R]
    rw [integral_integral_swap hJK_int]
    have hsec : Integrable (fun y => ∫ x : ℝ, JK (x, y)) :=
      hJK_int.integral_prod_right
    have hbound_int : Integrable (fun y => C * q y ^ 2) := hq_sq.const_mul C
    calc
      (∫ y : ℝ, ∫ x : ℝ, JK (x, y)) ≤
          ∫ y : ℝ, C * q y ^ 2 := by
        apply integral_mono hsec hbound_int
        intro y
        have heq : (∫ x : ℝ, JK (x, y)) =
            q y ^ 2 * ∫ x : ℝ, K x y := by
          have hfun : (fun x => JK (x, y)) =
              fun x => q y ^ 2 * K x y := by
            funext x
            dsimp [JK]
            ring
          rw [hfun, integral_const_mul]
        change (∫ x : ℝ, JK (x, y)) ≤ C * q y ^ 2
        rw [heq]
        nlinarith [hKcol_mass y, sq_nonneg (q y)]
      _ = C * ∫ y : ℝ, q y ^ 2 := integral_const_mul C _
  have hfinal : (∫ x : ℝ, T x ^ 2) ≤
      C ^ 2 * ∫ y : ℝ, q y ^ 2 := by
    calc
      (∫ x : ℝ, T x ^ 2) ≤ C * ∫ x : ℝ, R x := hmain
      _ ≤ C * (C * ∫ y : ℝ, q y ^ 2) :=
        mul_le_mul_of_nonneg_left hR_bound hC
      _ = C ^ 2 * ∫ y : ℝ, q y ^ 2 := by ring
  exact ⟨by simpa [T] using hT_sq_int, by simpa [T] using hfinal⟩

/-- Signed version of the dominated-kernel Schur estimate. -/
theorem dominatedKernel_signed_l2_contraction
    (K E : ℝ → ℝ → ℝ) (q : ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hK_meas : Measurable (Function.uncurry K))
    (hK_nn : ∀ x y, 0 ≤ K x y)
    (hKE : ∀ x y, K x y ≤ E x y)
    (hE_meas : Measurable (Function.uncurry E))
    (hE_nn : ∀ x y, 0 ≤ E x y)
    (hErow_int : ∀ x, Integrable (E x))
    (hErow_mass : ∀ x, ∫ y : ℝ, E x y = C)
    (hEcol_int : ∀ y, Integrable (fun x => E x y))
    (hEcol_mass : ∀ y, ∫ x : ℝ, E x y = C)
    (hq_meas : Measurable q)
    (hq_sq : Integrable (fun y => q y ^ 2)) :
    Integrable (fun x => (∫ y : ℝ, K x y * q y) ^ 2) ∧
      (∫ x : ℝ, (∫ y : ℝ, K x y * q y) ^ 2) ≤
        C ^ 2 * ∫ y : ℝ, q y ^ 2 := by
  have hpos := dominatedKernel_l2_contraction K E q C hC
    hK_meas hK_nn hKE hE_meas hE_nn hErow_int hErow_mass
    hEcol_int hEcol_mass hq_meas hq_sq
  let T : ℝ → ℝ := fun x => ∫ y : ℝ, K x y * |q y|
  let S : ℝ → ℝ := fun x => ∫ y : ℝ, K x y * q y
  have hSstrong : StronglyMeasurable S := by
    apply StronglyMeasurable.integral_prod_right
    exact (hK_meas.mul (hq_meas.comp measurable_snd)).stronglyMeasurable
  have hpoint : ∀ x, |S x| ≤ T x := by
    intro x
    dsimp [S, T]
    calc
      |∫ y : ℝ, K x y * q y| ≤
          ∫ y : ℝ, ‖K x y * q y‖ := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun y => K x y * q y)
      _ = ∫ y : ℝ, K x y * |q y| := by
        apply integral_congr_ae
        filter_upwards with y
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK_nn x y)]
  have hpointSq : ∀ x, S x ^ 2 ≤ T x ^ 2 := by
    intro x
    have hT0 : 0 ≤ T x := integral_nonneg fun y =>
      mul_nonneg (hK_nn x y) (abs_nonneg _)
    simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg (S x)) hT0).2 (hpoint x)
  have hTint : Integrable (fun x => T x ^ 2) := by
    simpa [T] using hpos.1
  have hSint : Integrable (fun x => S x ^ 2) := by
    refine hTint.mono' (hSstrong.pow 2).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpointSq x
  refine ⟨by simpa [S] using hSint, ?_⟩
  calc
    (∫ x : ℝ, S x ^ 2) ≤ ∫ x : ℝ, T x ^ 2 :=
      integral_mono hSint hTint hpointSq
    _ ≤ C ^ 2 * ∫ y : ℝ, q y ^ 2 := hpos.2

/-- Signed kernel whose absolute value is a dominated nonnegative kernel. -/
theorem absKernel_l2_contraction_of_dominated_envelope
    (L K E : ℝ → ℝ → ℝ) (q : ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hL_meas : Measurable (Function.uncurry L))
    (hK_meas : Measurable (Function.uncurry K))
    (hK_nn : ∀ x y, 0 ≤ K x y)
    (hLabs : ∀ x y, |L x y| = K x y)
    (hKE : ∀ x y, K x y ≤ E x y)
    (hE_meas : Measurable (Function.uncurry E))
    (hE_nn : ∀ x y, 0 ≤ E x y)
    (hErow_int : ∀ x, Integrable (E x))
    (hErow_mass : ∀ x, ∫ y : ℝ, E x y = C)
    (hEcol_int : ∀ y, Integrable (fun x => E x y))
    (hEcol_mass : ∀ y, ∫ x : ℝ, E x y = C)
    (hq_meas : Measurable q)
    (hq_sq : Integrable (fun y => q y ^ 2)) :
    Integrable (fun x => (∫ y : ℝ, L x y * q y) ^ 2) ∧
      (∫ x : ℝ, (∫ y : ℝ, L x y * q y) ^ 2) ≤
        C ^ 2 * ∫ y : ℝ, q y ^ 2 := by
  have hpos := dominatedKernel_l2_contraction K E q C hC
    hK_meas hK_nn hKE hE_meas hE_nn hErow_int hErow_mass
    hEcol_int hEcol_mass hq_meas hq_sq
  let T : ℝ → ℝ := fun x => ∫ y : ℝ, K x y * |q y|
  let S : ℝ → ℝ := fun x => ∫ y : ℝ, L x y * q y
  have hSstrong : StronglyMeasurable S := by
    apply StronglyMeasurable.integral_prod_right
    exact (hL_meas.mul (hq_meas.comp measurable_snd)).stronglyMeasurable
  have hpoint : ∀ x, |S x| ≤ T x := by
    intro x
    dsimp [S, T]
    calc
      |∫ y : ℝ, L x y * q y| ≤
          ∫ y : ℝ, ‖L x y * q y‖ := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun y => L x y * q y)
      _ = ∫ y : ℝ, K x y * |q y| := by
        apply integral_congr_ae
        filter_upwards with y
        rw [Real.norm_eq_abs, abs_mul, hLabs]
  have hpointSq : ∀ x, S x ^ 2 ≤ T x ^ 2 := by
    intro x
    have hT0 : 0 ≤ T x := integral_nonneg fun y =>
      mul_nonneg (hK_nn x y) (abs_nonneg _)
    simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg (S x)) hT0).2 (hpoint x)
  have hTint : Integrable (fun x => T x ^ 2) := by
    simpa [T] using hpos.1
  have hSint : Integrable (fun x => S x ^ 2) := by
    refine hTint.mono' (hSstrong.pow 2).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpointSq x
  refine ⟨by simpa [S] using hSint, ?_⟩
  calc
    (∫ x : ℝ, S x ^ 2) ≤ ∫ x : ℝ, T x ^ 2 :=
      integral_mono hSint hTint hpointSq
    _ ≤ C ^ 2 * ∫ y : ℝ, q y ^ 2 := hpos.2

/-! ## Moving heat kernel envelope -/

/-- Exponential tilting identity for the moving Gaussian kernel. -/
theorem weightedMovingHeat_tilt_kernel_identity
    {t : ℝ} (ht : 0 < t) (theta c x y : ℝ) :
    Real.exp (theta * (x - y)) * heatKernel t (x + c * t - y) =
      weightedMovingHeatGrowth theta c t *
        weightedMovingHeatMarkovKernel theta c t x y := by
  have h := weightedMovingHeat_conjugation_kernel_identity
    ht theta c x y
  have hexp : Real.exp (theta * (x - y)) =
      Real.exp (-theta * y) * Real.exp (theta * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (theta * (x - y)) * heatKernel t (x + c * t - y) =
        Real.exp (-theta * y) *
          (Real.exp (theta * x) * heatKernel t (x + c * t - y)) := by
      rw [hexp]
      ring
    _ = Real.exp (-theta * y) *
        (weightedMovingHeatGrowth theta c t *
          (weightedMovingHeatMarkovKernel theta c t x y *
            Real.exp (theta * y))) := by rw [h]
    _ = weightedMovingHeatGrowth theta c t *
        weightedMovingHeatMarkovKernel theta c t x y := by
      calc
        Real.exp (-theta * y) *
            (weightedMovingHeatGrowth theta c t *
              (weightedMovingHeatMarkovKernel theta c t x y *
                Real.exp (theta * y))) =
            (Real.exp (-theta * y) * Real.exp (theta * y)) *
              (weightedMovingHeatGrowth theta c t *
                weightedMovingHeatMarkovKernel theta c t x y) := by ring
        _ = weightedMovingHeatGrowth theta c t *
            weightedMovingHeatMarkovKernel theta c t x y := by
          rw [show Real.exp (-theta * y) * Real.exp (theta * y) = 1 by
        rw [← Real.exp_add]
        ring_nf
        exact Real.exp_zero]
          ring

theorem exp_mul_abs_le_add_exp
    {eta : ℝ} (_heta : 0 ≤ eta) (r : ℝ) :
    Real.exp (eta * |r|) ≤
      Real.exp (eta * r) + Real.exp (-eta * r) := by
  rcases le_total 0 r with hr | hr
  · rw [abs_of_nonneg hr]
    exact le_add_of_nonneg_right (Real.exp_nonneg _)
  · rw [abs_of_nonpos hr]
    have heq : eta * -r = -eta * r := by ring
    rw [heq]
    exact le_add_of_nonneg_left (Real.exp_nonneg _)

/-- Sum of the two exponentially tilted moving heat kernels. -/
def capHeatSchurEnvelope (eta c t x y : ℝ) : ℝ :=
  weightedMovingHeatGrowth eta c t *
      weightedMovingHeatMarkovKernel eta c t x y +
    weightedMovingHeatGrowth (-eta) c t *
      weightedMovingHeatMarkovKernel (-eta) c t x y

def capHeatSchurMass (eta c t : ℝ) : ℝ :=
  weightedMovingHeatGrowth eta c t +
    weightedMovingHeatGrowth (-eta) c t

theorem capHeatSchurMass_pos (eta c t : ℝ) :
    0 < capHeatSchurMass eta c t := by
  unfold capHeatSchurMass weightedMovingHeatGrowth
  positivity

theorem capHeatSchurEnvelope_measurable (eta c t : ℝ) :
    Measurable (Function.uncurry (capHeatSchurEnvelope eta c t)) := by
  exact
    (measurable_const.mul
      (weightedMovingHeatMarkovKernel_measurable eta c t)).add
    (measurable_const.mul
      (weightedMovingHeatMarkovKernel_measurable (-eta) c t))

theorem capHeatSchurEnvelope_nonneg
    {t : ℝ} (ht : 0 < t) (eta c x y : ℝ) :
    0 ≤ capHeatSchurEnvelope eta c t x y := by
  unfold capHeatSchurEnvelope
  exact add_nonneg
    (mul_nonneg (Real.exp_nonneg _)
      (weightedMovingHeatMarkovKernel_nonneg ht eta c x y))
    (mul_nonneg (Real.exp_nonneg _)
      (weightedMovingHeatMarkovKernel_nonneg ht (-eta) c x y))

theorem capHeatSchurEnvelope_row_integrable
    {t : ℝ} (ht : 0 < t) (eta c x : ℝ) :
    Integrable (capHeatSchurEnvelope eta c t x) := by
  exact
    ((weightedMovingHeatMarkovKernel_row_integrable ht eta c x).const_mul
        (weightedMovingHeatGrowth eta c t)).add
      ((weightedMovingHeatMarkovKernel_row_integrable ht (-eta) c x).const_mul
        (weightedMovingHeatGrowth (-eta) c t))

theorem capHeatSchurEnvelope_col_integrable
    {t : ℝ} (ht : 0 < t) (eta c y : ℝ) :
    Integrable (fun x => capHeatSchurEnvelope eta c t x y) := by
  exact
    ((weightedMovingHeatMarkovKernel_col_integrable ht eta c y).const_mul
        (weightedMovingHeatGrowth eta c t)).add
      ((weightedMovingHeatMarkovKernel_col_integrable ht (-eta) c y).const_mul
        (weightedMovingHeatGrowth (-eta) c t))

theorem capHeatSchurEnvelope_row_mass
    {t : ℝ} (ht : 0 < t) (eta c x : ℝ) :
    ∫ y : ℝ, capHeatSchurEnvelope eta c t x y =
      capHeatSchurMass eta c t := by
  unfold capHeatSchurEnvelope capHeatSchurMass
  rw [integral_add
      ((weightedMovingHeatMarkovKernel_row_integrable ht eta c x).const_mul _)
      ((weightedMovingHeatMarkovKernel_row_integrable ht (-eta) c x).const_mul _),
    integral_const_mul, integral_const_mul,
    weightedMovingHeatMarkovKernel_row_mass ht,
    weightedMovingHeatMarkovKernel_row_mass ht]
  ring

theorem capHeatSchurEnvelope_col_mass
    {t : ℝ} (ht : 0 < t) (eta c y : ℝ) :
    ∫ x : ℝ, capHeatSchurEnvelope eta c t x y =
      capHeatSchurMass eta c t := by
  unfold capHeatSchurEnvelope capHeatSchurMass
  rw [integral_add
      ((weightedMovingHeatMarkovKernel_col_integrable ht eta c y).const_mul _)
      ((weightedMovingHeatMarkovKernel_col_integrable ht (-eta) c y).const_mul _),
    integral_const_mul, integral_const_mul,
    weightedMovingHeatMarkovKernel_col_mass ht,
    weightedMovingHeatMarkovKernel_col_mass ht]
  ring

/-- The cap-conjugated heat kernel is pointwise dominated by a kernel whose
row and column masses are independent of `R`. -/
theorem capWeightSqrtRatio_mul_movingHeat_le_envelope
    {eta t : ℝ} (heta : 0 ≤ eta) (ht : 0 < t)
    (R c x y : ℝ) :
    capWeightSqrtRatio eta R x y * heatKernel t (x + c * t - y) ≤
      capHeatSchurEnvelope eta c t x y := by
  have hheat : 0 ≤ heatKernel t (x + c * t - y) :=
    heatKernel_nonneg ht _
  calc
    capWeightSqrtRatio eta R x y * heatKernel t (x + c * t - y) ≤
        Real.exp (eta * |x - y|) * heatKernel t (x + c * t - y) :=
      mul_le_mul_of_nonneg_right
        (capWeightSqrtRatio_le_exp_abs heta R x y) hheat
    _ ≤ (Real.exp (eta * (x - y)) + Real.exp (-eta * (x - y))) *
        heatKernel t (x + c * t - y) :=
      mul_le_mul_of_nonneg_right (exp_mul_abs_le_add_exp heta (x - y)) hheat
    _ = capHeatSchurEnvelope eta c t x y := by
      rw [add_mul,
        weightedMovingHeat_tilt_kernel_identity ht eta c x y,
        weightedMovingHeat_tilt_kernel_identity ht (-eta) c x y]
      rfl

/-- R-uniform Schur bound for the heat envelope. -/
theorem capHeatSchurEnvelope_l2_bounded
    {t : ℝ} (ht : 0 < t) (eta c : ℝ)
    {q : ℝ → ℝ} (hq_meas : Measurable q)
    (hq_sq : Integrable (fun y => q y ^ 2)) :
    Integrable (fun x =>
        (∫ y : ℝ, capHeatSchurEnvelope eta c t x y * |q y|) ^ 2) ∧
      (∫ x : ℝ,
          (∫ y : ℝ, capHeatSchurEnvelope eta c t x y * |q y|) ^ 2) ≤
        capHeatSchurMass eta c t ^ 2 * ∫ y : ℝ, q y ^ 2 := by
  exact constantMassKernel_l2_contraction
    (capHeatSchurEnvelope eta c t) q (capHeatSchurMass eta c t)
    (capHeatSchurMass_pos eta c t)
    (capHeatSchurEnvelope_measurable eta c t)
    (capHeatSchurEnvelope_nonneg ht eta c)
    (capHeatSchurEnvelope_row_integrable ht eta c)
    (capHeatSchurEnvelope_row_mass ht eta c)
    (capHeatSchurEnvelope_col_integrable ht eta c)
    (capHeatSchurEnvelope_col_mass ht eta c)
    hq_meas hq_sq

/-! ## Moving heat-gradient kernel envelope -/

/-- Differentiating the tilted heat identity introduces the zero-order
conjugation term. -/
theorem weightedMovingHeat_tilt_deriv_kernel_identity
    {t : ℝ} (ht : 0 < t) (theta c x y : ℝ) :
    Real.exp (theta * (x - y)) *
        deriv (fun z : ℝ => heatKernel t z) (x + c * t - y) =
      weightedMovingHeatGrowth theta c t *
        (deriv (fun z : ℝ => heatKernel t z)
            (x + (c - 2 * theta) * t - y) -
          theta * heatKernel t (x + (c - 2 * theta) * t - y)) := by
  have htilt := weightedMovingHeat_tilt_kernel_identity
    ht theta c x y
  rw [deriv_heatKernel ht, deriv_heatKernel ht]
  calc
    Real.exp (theta * (x - y)) *
        (-( (x + c * t - y) / (2 * t)) *
          heatKernel t (x + c * t - y)) =
      (-( (x + c * t - y) / (2 * t))) *
        (Real.exp (theta * (x - y)) *
          heatKernel t (x + c * t - y)) := by ring
    _ = (-( (x + c * t - y) / (2 * t))) *
        (weightedMovingHeatGrowth theta c t *
          weightedMovingHeatMarkovKernel theta c t x y) := by rw [htilt]
    _ = weightedMovingHeatGrowth theta c t *
        (-( (x + (c - 2 * theta) * t - y) / (2 * t)) *
            heatKernel t (x + (c - 2 * theta) * t - y) -
          theta * heatKernel t (x + (c - 2 * theta) * t - y)) := by
      unfold weightedMovingHeatMarkovKernel
      field_simp [ne_of_gt ht]
      ring

/-- Absolute-value consequence of the differentiated tilt identity. -/
theorem weightedMovingHeat_tilt_deriv_abs_le
    {t : ℝ} (ht : 0 < t) (theta c x y : ℝ) :
    Real.exp (theta * (x - y)) *
        |deriv (fun z : ℝ => heatKernel t z) (x + c * t - y)| ≤
      weightedMovingHeatGrowth theta c t *
        (|deriv (fun z : ℝ => heatKernel t z)
            (x + (c - 2 * theta) * t - y)| +
          |theta| * heatKernel t (x + (c - 2 * theta) * t - y)) := by
  have hid := weightedMovingHeat_tilt_deriv_kernel_identity
    ht theta c x y
  have hgrowth : 0 ≤ weightedMovingHeatGrowth theta c t :=
    Real.exp_nonneg _
  have hheat : 0 ≤ heatKernel t
      (x + (c - 2 * theta) * t - y) := heatKernel_nonneg ht _
  calc
    Real.exp (theta * (x - y)) *
        |deriv (fun z : ℝ => heatKernel t z) (x + c * t - y)| =
      |Real.exp (theta * (x - y)) *
        deriv (fun z : ℝ => heatKernel t z) (x + c * t - y)| := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    _ = weightedMovingHeatGrowth theta c t *
        |deriv (fun z : ℝ => heatKernel t z)
            (x + (c - 2 * theta) * t - y) -
          theta * heatKernel t (x + (c - 2 * theta) * t - y)| := by
        rw [hid, abs_mul, abs_of_nonneg hgrowth]
    _ ≤ weightedMovingHeatGrowth theta c t *
        (|deriv (fun z : ℝ => heatKernel t z)
            (x + (c - 2 * theta) * t - y)| +
          |theta| * heatKernel t (x + (c - 2 * theta) * t - y)) := by
      apply mul_le_mul_of_nonneg_left _ hgrowth
      calc
        |deriv (fun z : ℝ => heatKernel t z)
            (x + (c - 2 * theta) * t - y) -
          theta * heatKernel t (x + (c - 2 * theta) * t - y)| ≤
            |deriv (fun z : ℝ => heatKernel t z)
              (x + (c - 2 * theta) * t - y)| +
            |theta * heatKernel t
              (x + (c - 2 * theta) * t - y)| := abs_sub _ _
        _ = |deriv (fun z : ℝ => heatKernel t z)
              (x + (c - 2 * theta) * t - y)| +
            |theta| * heatKernel t
              (x + (c - 2 * theta) * t - y) := by
          rw [abs_mul, abs_of_nonneg hheat]

theorem weightedMovingHeatGradientMarkovKernel_div_sqrt
    {t : ℝ} (ht : 0 < t) (theta c x y : ℝ) :
    weightedMovingHeatGradientMarkovKernel theta c t x y /
        Real.sqrt (Real.pi * t) =
      |deriv (fun z : ℝ => heatKernel t z)
        (x + (c - 2 * theta) * t - y)| := by
  unfold weightedMovingHeatGradientMarkovKernel
  field_simp [ne_of_gt (Real.sqrt_pos.mpr (by positivity : 0 < Real.pi * t))]

/-- One tilted derivative envelope.  The `rho` term records the zero-order
term created by differentiating the exponential conjugation. -/
def tiltedHeatGradientSchurKernel
    (theta rho c t x y : ℝ) : ℝ :=
  weightedMovingHeatGrowth theta c t *
    (weightedMovingHeatGradientMarkovKernel theta c t x y /
        Real.sqrt (Real.pi * t) +
      rho * weightedMovingHeatMarkovKernel theta c t x y)

def tiltedHeatGradientSchurMass
    (theta rho c t : ℝ) : ℝ :=
  weightedMovingHeatGrowth theta c t *
    (1 / Real.sqrt (Real.pi * t) + rho)

theorem tiltedHeatGradientSchurKernel_eq
    {t : ℝ} (ht : 0 < t) (theta rho c x y : ℝ) :
    tiltedHeatGradientSchurKernel theta rho c t x y =
      weightedMovingHeatGrowth theta c t *
        (|deriv (fun z : ℝ => heatKernel t z)
            (x + (c - 2 * theta) * t - y)| +
          rho * heatKernel t (x + (c - 2 * theta) * t - y)) := by
  unfold tiltedHeatGradientSchurKernel weightedMovingHeatMarkovKernel
  rw [weightedMovingHeatGradientMarkovKernel_div_sqrt ht]

theorem tiltedHeatGradientSchurKernel_measurable
    {t : ℝ} (ht : 0 < t) (theta rho c : ℝ) :
    Measurable
      (Function.uncurry (tiltedHeatGradientSchurKernel theta rho c t)) := by
  unfold tiltedHeatGradientSchurKernel Function.uncurry
  have hgrad := weightedMovingHeatGradientMarkovKernel_measurable ht theta c
  have hheat := weightedMovingHeatMarkovKernel_measurable theta c t
  exact measurable_const.mul
    ((hgrad.div_const _).add (measurable_const.mul hheat))

theorem tiltedHeatGradientSchurKernel_nonneg
    {t : ℝ} (ht : 0 < t) {rho : ℝ} (hrho : 0 ≤ rho)
    (theta c x y : ℝ) :
    0 ≤ tiltedHeatGradientSchurKernel theta rho c t x y := by
  unfold tiltedHeatGradientSchurKernel
  exact mul_nonneg (Real.exp_nonneg _)
    (add_nonneg
      (div_nonneg
        (weightedMovingHeatGradientMarkovKernel_nonneg theta c t x y)
        (Real.sqrt_nonneg _))
      (mul_nonneg hrho
        (weightedMovingHeatMarkovKernel_nonneg ht theta c x y)))

theorem tiltedHeatGradientSchurKernel_row_integrable
    {t : ℝ} (ht : 0 < t) (theta rho c x : ℝ) :
    Integrable (tiltedHeatGradientSchurKernel theta rho c t x) := by
  unfold tiltedHeatGradientSchurKernel
  exact
    (((weightedMovingHeatGradientMarkovKernel_row_integrable ht theta c x).div_const _).add
      ((weightedMovingHeatMarkovKernel_row_integrable ht theta c x).const_mul rho)).const_mul _

theorem tiltedHeatGradientSchurKernel_col_integrable
    {t : ℝ} (ht : 0 < t) (theta rho c y : ℝ) :
    Integrable (fun x => tiltedHeatGradientSchurKernel theta rho c t x y) := by
  unfold tiltedHeatGradientSchurKernel
  exact
    (((weightedMovingHeatGradientMarkovKernel_col_integrable ht theta c y).div_const _).add
      ((weightedMovingHeatMarkovKernel_col_integrable ht theta c y).const_mul rho)).const_mul _

theorem tiltedHeatGradientSchurKernel_row_mass
    {t : ℝ} (ht : 0 < t) (theta rho c x : ℝ) :
    ∫ y : ℝ, tiltedHeatGradientSchurKernel theta rho c t x y =
      tiltedHeatGradientSchurMass theta rho c t := by
  have hgrad :=
    (weightedMovingHeatGradientMarkovKernel_row_integrable ht theta c x).div_const
      (Real.sqrt (Real.pi * t))
  have hheat :=
    (weightedMovingHeatMarkovKernel_row_integrable ht theta c x).const_mul rho
  unfold tiltedHeatGradientSchurKernel tiltedHeatGradientSchurMass
  rw [integral_const_mul, integral_add hgrad hheat,
    integral_div, integral_const_mul,
    weightedMovingHeatGradientMarkovKernel_row_mass ht,
    weightedMovingHeatMarkovKernel_row_mass ht]
  ring

theorem tiltedHeatGradientSchurKernel_col_mass
    {t : ℝ} (ht : 0 < t) (theta rho c y : ℝ) :
    ∫ x : ℝ, tiltedHeatGradientSchurKernel theta rho c t x y =
      tiltedHeatGradientSchurMass theta rho c t := by
  have hgrad :=
    (weightedMovingHeatGradientMarkovKernel_col_integrable ht theta c y).div_const
      (Real.sqrt (Real.pi * t))
  have hheat :=
    (weightedMovingHeatMarkovKernel_col_integrable ht theta c y).const_mul rho
  unfold tiltedHeatGradientSchurKernel tiltedHeatGradientSchurMass
  rw [integral_const_mul, integral_add hgrad hheat,
    integral_div, integral_const_mul,
    weightedMovingHeatGradientMarkovKernel_col_mass ht,
    weightedMovingHeatMarkovKernel_col_mass ht]
  ring

theorem tiltedHeatGradientSchurMass_pos
    {t : ℝ} (ht : 0 < t) {rho : ℝ} (hrho : 0 ≤ rho)
    (theta c : ℝ) :
    0 < tiltedHeatGradientSchurMass theta rho c t := by
  unfold tiltedHeatGradientSchurMass weightedMovingHeatGrowth
  have hs : 0 < Real.sqrt (Real.pi * t) := Real.sqrt_pos.mpr (by positivity)
  positivity

/-- The two-tilt envelope for the cap-conjugated moving heat gradient. -/
def capHeatGradientSchurEnvelope (eta c t x y : ℝ) : ℝ :=
  tiltedHeatGradientSchurKernel eta eta c t x y +
    tiltedHeatGradientSchurKernel (-eta) eta c t x y

def capHeatGradientSchurMass (eta c t : ℝ) : ℝ :=
  tiltedHeatGradientSchurMass eta eta c t +
    tiltedHeatGradientSchurMass (-eta) eta c t

theorem capHeatGradientSchurMass_pos
    {t : ℝ} (ht : 0 < t) {eta : ℝ} (heta : 0 ≤ eta) (c : ℝ) :
    0 < capHeatGradientSchurMass eta c t := by
  unfold capHeatGradientSchurMass
  exact add_pos
    (tiltedHeatGradientSchurMass_pos ht heta eta c)
    (tiltedHeatGradientSchurMass_pos ht heta (-eta) c)

theorem capHeatGradientSchurEnvelope_measurable
    {t : ℝ} (ht : 0 < t) (eta c : ℝ) :
    Measurable
      (Function.uncurry (capHeatGradientSchurEnvelope eta c t)) :=
  (tiltedHeatGradientSchurKernel_measurable ht eta eta c).add
    (tiltedHeatGradientSchurKernel_measurable ht (-eta) eta c)

theorem capHeatGradientSchurEnvelope_nonneg
    {t : ℝ} (ht : 0 < t) {eta : ℝ} (heta : 0 ≤ eta)
    (c x y : ℝ) :
    0 ≤ capHeatGradientSchurEnvelope eta c t x y := by
  unfold capHeatGradientSchurEnvelope
  exact add_nonneg
    (tiltedHeatGradientSchurKernel_nonneg ht heta eta c x y)
    (tiltedHeatGradientSchurKernel_nonneg ht heta (-eta) c x y)

theorem capHeatGradientSchurEnvelope_row_integrable
    {t : ℝ} (ht : 0 < t) (eta c x : ℝ) :
    Integrable (capHeatGradientSchurEnvelope eta c t x) :=
  (tiltedHeatGradientSchurKernel_row_integrable ht eta eta c x).add
    (tiltedHeatGradientSchurKernel_row_integrable ht (-eta) eta c x)

theorem capHeatGradientSchurEnvelope_col_integrable
    {t : ℝ} (ht : 0 < t) (eta c y : ℝ) :
    Integrable (fun x => capHeatGradientSchurEnvelope eta c t x y) :=
  (tiltedHeatGradientSchurKernel_col_integrable ht eta eta c y).add
    (tiltedHeatGradientSchurKernel_col_integrable ht (-eta) eta c y)

theorem capHeatGradientSchurEnvelope_row_mass
    {t : ℝ} (ht : 0 < t) (eta c x : ℝ) :
    ∫ y : ℝ, capHeatGradientSchurEnvelope eta c t x y =
      capHeatGradientSchurMass eta c t := by
  unfold capHeatGradientSchurEnvelope capHeatGradientSchurMass
  rw [integral_add
      (tiltedHeatGradientSchurKernel_row_integrable ht eta eta c x)
      (tiltedHeatGradientSchurKernel_row_integrable ht (-eta) eta c x),
    tiltedHeatGradientSchurKernel_row_mass ht,
    tiltedHeatGradientSchurKernel_row_mass ht]

theorem capHeatGradientSchurEnvelope_col_mass
    {t : ℝ} (ht : 0 < t) (eta c y : ℝ) :
    ∫ x : ℝ, capHeatGradientSchurEnvelope eta c t x y =
      capHeatGradientSchurMass eta c t := by
  unfold capHeatGradientSchurEnvelope capHeatGradientSchurMass
  rw [integral_add
      (tiltedHeatGradientSchurKernel_col_integrable ht eta eta c y)
      (tiltedHeatGradientSchurKernel_col_integrable ht (-eta) eta c y),
    tiltedHeatGradientSchurKernel_col_mass ht,
    tiltedHeatGradientSchurKernel_col_mass ht]

/-- R-uniform pointwise envelope for the cap-conjugated moving heat
gradient.  The `eta * heat` terms are essential: they are the zero-order
terms produced by differentiating the exponential tilts. -/
theorem capWeightSqrtRatio_mul_movingHeatGradient_le_envelope
    {eta t : ℝ} (heta : 0 ≤ eta) (ht : 0 < t)
    (R c x y : ℝ) :
    capWeightSqrtRatio eta R x y *
        |deriv (fun z : ℝ => heatKernel t z) (x + c * t - y)| ≤
      capHeatGradientSchurEnvelope eta c t x y := by
  have hderiv : 0 ≤
      |deriv (fun z : ℝ => heatKernel t z) (x + c * t - y)| :=
    abs_nonneg _
  calc
    capWeightSqrtRatio eta R x y *
        |deriv (fun z : ℝ => heatKernel t z) (x + c * t - y)| ≤
      Real.exp (eta * |x - y|) *
        |deriv (fun z : ℝ => heatKernel t z) (x + c * t - y)| :=
      mul_le_mul_of_nonneg_right
        (capWeightSqrtRatio_le_exp_abs heta R x y) hderiv
    _ ≤ (Real.exp (eta * (x - y)) + Real.exp (-eta * (x - y))) *
        |deriv (fun z : ℝ => heatKernel t z) (x + c * t - y)| :=
      mul_le_mul_of_nonneg_right (exp_mul_abs_le_add_exp heta (x - y)) hderiv
    _ = Real.exp (eta * (x - y)) *
          |deriv (fun z : ℝ => heatKernel t z) (x + c * t - y)| +
        Real.exp (-eta * (x - y)) *
          |deriv (fun z : ℝ => heatKernel t z) (x + c * t - y)| := by ring
    _ ≤ tiltedHeatGradientSchurKernel eta eta c t x y +
        tiltedHeatGradientSchurKernel (-eta) eta c t x y := by
      apply add_le_add
      · calc
          Real.exp (eta * (x - y)) *
              |deriv (fun z : ℝ => heatKernel t z) (x + c * t - y)| ≤
            weightedMovingHeatGrowth eta c t *
              (|deriv (fun z : ℝ => heatKernel t z)
                  (x + (c - 2 * eta) * t - y)| +
                |eta| * heatKernel t
                  (x + (c - 2 * eta) * t - y)) :=
            weightedMovingHeat_tilt_deriv_abs_le ht eta c x y
          _ = tiltedHeatGradientSchurKernel eta eta c t x y := by
            rw [tiltedHeatGradientSchurKernel_eq ht, abs_of_nonneg heta]
      · calc
          Real.exp (-eta * (x - y)) *
              |deriv (fun z : ℝ => heatKernel t z) (x + c * t - y)| ≤
            weightedMovingHeatGrowth (-eta) c t *
              (|deriv (fun z : ℝ => heatKernel t z)
                  (x + (c - 2 * (-eta)) * t - y)| +
                |-eta| * heatKernel t
                  (x + (c - 2 * (-eta)) * t - y)) :=
            weightedMovingHeat_tilt_deriv_abs_le ht (-eta) c x y
          _ = tiltedHeatGradientSchurKernel (-eta) eta c t x y := by
            rw [tiltedHeatGradientSchurKernel_eq ht, abs_neg,
              abs_of_nonneg heta]
    _ = capHeatGradientSchurEnvelope eta c t x y := rfl

/-- R-uniform Schur bound for the moving heat-gradient envelope. -/
theorem capHeatGradientSchurEnvelope_l2_bounded
    {eta t : ℝ} (heta : 0 ≤ eta) (ht : 0 < t) (c : ℝ)
    {q : ℝ → ℝ} (hq_meas : Measurable q)
    (hq_sq : Integrable (fun y => q y ^ 2)) :
    Integrable (fun x =>
        (∫ y : ℝ,
          capHeatGradientSchurEnvelope eta c t x y * |q y|) ^ 2) ∧
      (∫ x : ℝ,
          (∫ y : ℝ,
            capHeatGradientSchurEnvelope eta c t x y * |q y|) ^ 2) ≤
        capHeatGradientSchurMass eta c t ^ 2 *
          ∫ y : ℝ, q y ^ 2 := by
  exact constantMassKernel_l2_contraction
    (capHeatGradientSchurEnvelope eta c t) q
    (capHeatGradientSchurMass eta c t)
    (capHeatGradientSchurMass_pos ht heta c)
    (capHeatGradientSchurEnvelope_measurable ht eta c)
    (capHeatGradientSchurEnvelope_nonneg ht heta c)
    (capHeatGradientSchurEnvelope_row_integrable ht eta c)
    (capHeatGradientSchurEnvelope_row_mass ht eta c)
    (capHeatGradientSchurEnvelope_col_integrable ht eta c)
    (capHeatGradientSchurEnvelope_col_mass ht eta c)
    hq_meas hq_sq

/-! ## Actual cap-conjugated moving heat operators -/

def capMovingHeatKernel (eta R c t x y : ℝ) : ℝ :=
  (capWeightSqrt eta R x / capWeightSqrt eta R y) *
    heatKernel t (x + c * t - y)

def capMovingHeatGradientKernel (eta R c t x y : ℝ) : ℝ :=
  (capWeightSqrt eta R x / capWeightSqrt eta R y) *
    deriv (fun z : ℝ => heatKernel t z) (x + c * t - y)

def capMovingHeatGradientAbsKernel (eta R c t x y : ℝ) : ℝ :=
  (capWeightSqrt eta R x / capWeightSqrt eta R y) *
    |deriv (fun z : ℝ => heatKernel t z) (x + c * t - y)|

private theorem capWeightSqrt_div_continuous (eta R : ℝ) :
    Continuous (fun z : ℝ × ℝ =>
      capWeightSqrt eta R z.1 / capWeightSqrt eta R z.2) := by
  apply Continuous.div₀
  · exact (capWeightSqrt_continuous eta R).comp continuous_fst
  · exact (capWeightSqrt_continuous eta R).comp continuous_snd
  · intro z
    exact ne_of_gt (capWeightSqrt_pos eta R z.2)

theorem capMovingHeatKernel_measurable (eta R c t : ℝ) :
    Measurable (Function.uncurry (capMovingHeatKernel eta R c t)) := by
  have hratio := (capWeightSqrt_div_continuous eta R).measurable
  have hheat : Measurable (fun z : ℝ × ℝ =>
      heatKernel t (z.1 + c * t - z.2)) := by
    unfold heatKernel
    fun_prop
  exact hratio.mul hheat

theorem capMovingHeatKernel_nonneg
    {t : ℝ} (ht : 0 < t) (eta R c x y : ℝ) :
    0 ≤ capMovingHeatKernel eta R c t x y := by
  unfold capMovingHeatKernel
  exact mul_nonneg
    (div_nonneg (capWeightSqrt_pos eta R x).le
      (capWeightSqrt_pos eta R y).le)
    (heatKernel_nonneg ht _)

theorem capMovingHeatKernel_le_envelope
    {eta t : ℝ} (heta : 0 ≤ eta) (ht : 0 < t)
    (R c x y : ℝ) :
    capMovingHeatKernel eta R c t x y ≤
      capHeatSchurEnvelope eta c t x y := by
  unfold capMovingHeatKernel
  rw [← show capWeightSqrtRatio eta R x y =
      capWeightSqrt eta R x / capWeightSqrt eta R y by
    unfold capWeightSqrtRatio capWeightSqrt
    rw [Real.sqrt_div (capWeight_pos eta R x).le]]
  exact capWeightSqrtRatio_mul_movingHeat_le_envelope heta ht R c x y

theorem capMovingHeatGradientKernel_measurable
    {t : ℝ} (ht : 0 < t) (eta R c : ℝ) :
    Measurable
      (Function.uncurry (capMovingHeatGradientKernel eta R c t)) := by
  have hratio := (capWeightSqrt_div_continuous eta R).measurable
  have hderiv : Measurable (fun z : ℝ × ℝ =>
      deriv (fun w : ℝ => heatKernel t w) (z.1 + c * t - z.2)) := by
    simp_rw [deriv_heatKernel ht]
    unfold heatKernel
    fun_prop
  exact hratio.mul hderiv

theorem capMovingHeatGradientAbsKernel_measurable
    {t : ℝ} (ht : 0 < t) (eta R c : ℝ) :
    Measurable
      (Function.uncurry (capMovingHeatGradientAbsKernel eta R c t)) := by
  have hratio := (capWeightSqrt_div_continuous eta R).measurable
  have hderiv : Measurable (fun z : ℝ × ℝ =>
      |deriv (fun w : ℝ => heatKernel t w) (z.1 + c * t - z.2)|) := by
    simp_rw [deriv_heatKernel ht]
    unfold heatKernel
    fun_prop
  exact hratio.mul hderiv

theorem capMovingHeatGradientAbsKernel_nonneg
    (eta R c t x y : ℝ) :
    0 ≤ capMovingHeatGradientAbsKernel eta R c t x y := by
  unfold capMovingHeatGradientAbsKernel
  exact mul_nonneg
    (div_nonneg (capWeightSqrt_pos eta R x).le
      (capWeightSqrt_pos eta R y).le)
    (abs_nonneg _)

theorem capMovingHeatGradientKernel_abs
    (eta R c t x y : ℝ) :
    |capMovingHeatGradientKernel eta R c t x y| =
      capMovingHeatGradientAbsKernel eta R c t x y := by
  unfold capMovingHeatGradientKernel capMovingHeatGradientAbsKernel
  rw [abs_mul, abs_of_nonneg (div_nonneg
    (capWeightSqrt_pos eta R x).le (capWeightSqrt_pos eta R y).le)]

theorem capMovingHeatGradientAbsKernel_le_envelope
    {eta t : ℝ} (heta : 0 ≤ eta) (ht : 0 < t)
    (R c x y : ℝ) :
    capMovingHeatGradientAbsKernel eta R c t x y ≤
      capHeatGradientSchurEnvelope eta c t x y := by
  unfold capMovingHeatGradientAbsKernel
  rw [← show capWeightSqrtRatio eta R x y =
      capWeightSqrt eta R x / capWeightSqrt eta R y by
    unfold capWeightSqrtRatio capWeightSqrt
    rw [Real.sqrt_div (capWeight_pos eta R x).le]]
  exact capWeightSqrtRatio_mul_movingHeatGradient_le_envelope
    heta ht R c x y

theorem capWeightSqrt_mul_movingFrameHeatOp_eq
    {t : ℝ} (_ht : 0 < t) (eta R c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    capWeightSqrt eta R x * paper5MovingFrameHeatOp c t f x =
      Real.exp (-t) *
        ∫ y : ℝ, capMovingHeatKernel eta R c t x y *
          (capWeightSqrt eta R y * f y) := by
  unfold paper5MovingFrameHeatOp wholeLineCauchyHeatOp
    modifiedSemigroup heatSemigroup
  rw [show capWeightSqrt eta R x *
      (Real.exp (-t) * ∫ y : ℝ, heatKernel t (x + c * t - y) * f y) =
    Real.exp (-t) * (capWeightSqrt eta R x *
      ∫ y : ℝ, heatKernel t (x + c * t - y) * f y) by ring]
  congr 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  unfold capMovingHeatKernel
  field_simp [ne_of_gt (capWeightSqrt_pos eta R y)]

theorem capWeightSqrt_mul_movingFrameHeatGradOp_eq
    {t : ℝ} (ht : 0 < t) (eta R c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    capWeightSqrt eta R x * paper5MovingFrameHeatGradOp c t f x =
      Real.exp (-t) *
        ∫ y : ℝ, capMovingHeatGradientKernel eta R c t x y *
          (capWeightSqrt eta R y * f y) := by
  unfold paper5MovingFrameHeatGradOp wholeLineCauchyHeatGradOp
  rw [← integral_const_mul]
  calc
    (∫ y : ℝ, capWeightSqrt eta R x *
        (Real.exp (-t) *
          (deriv (fun z : ℝ => heatKernel t (z - y)) (x + c * t) * f y))) =
      ∫ y : ℝ, Real.exp (-t) *
        (capMovingHeatGradientKernel eta R c t x y *
          (capWeightSqrt eta R y * f y)) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [deriv_heatKernel_translated_left ht]
        unfold capMovingHeatGradientKernel
        rw [deriv_heatKernel ht]
        field_simp [ne_of_gt (capWeightSqrt_pos eta R y)]
    _ = Real.exp (-t) *
        ∫ y : ℝ, capMovingHeatGradientKernel eta R c t x y *
          (capWeightSqrt eta R y * f y) := by
      rw [integral_const_mul]

/-- Actual moving heat operator estimate in the cap-weighted raw space. -/
theorem capWeight_movingFrameHeatOp_l2_bounded
    {eta t : ℝ} (heta : 0 ≤ eta) (ht : 0 < t)
    (R c : ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (hcap : Integrable (fun y => capWeight eta R y * |f y| ^ 2)) :
    Integrable (fun x => capWeight eta R x *
        |paper5MovingFrameHeatOp c t f x| ^ 2) ∧
      (∫ x : ℝ, capWeight eta R x *
          |paper5MovingFrameHeatOp c t f x| ^ 2) ≤
        (Real.exp (-t) * capHeatSchurMass eta c t) ^ 2 *
          ∫ y : ℝ, capWeight eta R y * |f y| ^ 2 := by
  let q : ℝ → ℝ := fun y => capWeightSqrt eta R y * f y
  have hq_meas : Measurable q :=
    (capWeightSqrt_continuous eta R).measurable.mul hf
  have hq_sq : Integrable (fun y => q y ^ 2) := by
    refine hcap.congr (Eventually.of_forall fun y => ?_)
    change capWeight eta R y * |f y| ^ 2 =
      (capWeightSqrt eta R y * f y) ^ 2
    exact (capWeightSqrt_mul_sq_eq eta R y (f y)).symm
  have hk := absKernel_l2_contraction_of_dominated_envelope
    (capMovingHeatKernel eta R c t) (capMovingHeatKernel eta R c t)
    (capHeatSchurEnvelope eta c t) q (capHeatSchurMass eta c t)
    (capHeatSchurMass_pos eta c t).le
    (capMovingHeatKernel_measurable eta R c t)
    (capMovingHeatKernel_measurable eta R c t)
    (capMovingHeatKernel_nonneg ht eta R c)
    (fun x y => abs_of_nonneg (capMovingHeatKernel_nonneg ht eta R c x y))
    (capMovingHeatKernel_le_envelope heta ht R c)
    (capHeatSchurEnvelope_measurable eta c t)
    (capHeatSchurEnvelope_nonneg ht eta c)
    (capHeatSchurEnvelope_row_integrable ht eta c)
    (capHeatSchurEnvelope_row_mass ht eta c)
    (capHeatSchurEnvelope_col_integrable ht eta c)
    (capHeatSchurEnvelope_col_mass ht eta c)
    hq_meas hq_sq
  let S : ℝ → ℝ := fun x =>
    ∫ y : ℝ, capMovingHeatKernel eta R c t x y * q y
  have hpoint : ∀ x, capWeight eta R x *
      |paper5MovingFrameHeatOp c t f x| ^ 2 =
        Real.exp (-t) ^ 2 * S x ^ 2 := by
    intro x
    rw [← capWeightSqrt_mul_sq_eq eta R x
      (paper5MovingFrameHeatOp c t f x),
      capWeightSqrt_mul_movingFrameHeatOp_eq ht]
    dsimp [S, q]
    ring
  have hout : Integrable (fun x => capWeight eta R x *
      |paper5MovingFrameHeatOp c t f x| ^ 2) := by
    refine (hk.1.const_mul (Real.exp (-t) ^ 2)).congr
      (Eventually.of_forall fun x => ?_)
    change Real.exp (-t) ^ 2 * S x ^ 2 =
      capWeight eta R x * |paper5MovingFrameHeatOp c t f x| ^ 2
    exact (hpoint x).symm
  refine ⟨hout, ?_⟩
  calc
    (∫ x : ℝ, capWeight eta R x *
        |paper5MovingFrameHeatOp c t f x| ^ 2) =
      Real.exp (-t) ^ 2 * ∫ x : ℝ, S x ^ 2 := by
        simp_rw [hpoint]
        rw [integral_const_mul]
    _ ≤ Real.exp (-t) ^ 2 *
        (capHeatSchurMass eta c t ^ 2 * ∫ y : ℝ, q y ^ 2) :=
      mul_le_mul_of_nonneg_left hk.2 (sq_nonneg _)
    _ = (Real.exp (-t) * capHeatSchurMass eta c t) ^ 2 *
        ∫ y : ℝ, capWeight eta R y * |f y| ^ 2 := by
      have hqeq : (∫ y : ℝ, q y ^ 2) =
          ∫ y : ℝ, capWeight eta R y * |f y| ^ 2 := by
        apply integral_congr_ae
        filter_upwards with y
        exact capWeightSqrt_mul_sq_eq eta R y (f y)
      rw [hqeq]
      ring

/-- Actual moving heat-gradient estimate in the cap-weighted raw space. -/
theorem capWeight_movingFrameHeatGradOp_l2_bounded
    {eta t : ℝ} (heta : 0 ≤ eta) (ht : 0 < t)
    (R c : ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (hcap : Integrable (fun y => capWeight eta R y * |f y| ^ 2)) :
    Integrable (fun x => capWeight eta R x *
        |paper5MovingFrameHeatGradOp c t f x| ^ 2) ∧
      (∫ x : ℝ, capWeight eta R x *
          |paper5MovingFrameHeatGradOp c t f x| ^ 2) ≤
        (Real.exp (-t) * capHeatGradientSchurMass eta c t) ^ 2 *
          ∫ y : ℝ, capWeight eta R y * |f y| ^ 2 := by
  let q : ℝ → ℝ := fun y => capWeightSqrt eta R y * f y
  have hq_meas : Measurable q :=
    (capWeightSqrt_continuous eta R).measurable.mul hf
  have hq_sq : Integrable (fun y => q y ^ 2) := by
    refine hcap.congr (Eventually.of_forall fun y => ?_)
    change capWeight eta R y * |f y| ^ 2 =
      (capWeightSqrt eta R y * f y) ^ 2
    exact (capWeightSqrt_mul_sq_eq eta R y (f y)).symm
  have hk := absKernel_l2_contraction_of_dominated_envelope
    (capMovingHeatGradientKernel eta R c t)
    (capMovingHeatGradientAbsKernel eta R c t)
    (capHeatGradientSchurEnvelope eta c t) q
    (capHeatGradientSchurMass eta c t)
    (capHeatGradientSchurMass_pos ht heta c).le
    (capMovingHeatGradientKernel_measurable ht eta R c)
    (capMovingHeatGradientAbsKernel_measurable ht eta R c)
    (capMovingHeatGradientAbsKernel_nonneg eta R c t)
    (capMovingHeatGradientKernel_abs eta R c t)
    (capMovingHeatGradientAbsKernel_le_envelope heta ht R c)
    (capHeatGradientSchurEnvelope_measurable ht eta c)
    (capHeatGradientSchurEnvelope_nonneg ht heta c)
    (capHeatGradientSchurEnvelope_row_integrable ht eta c)
    (capHeatGradientSchurEnvelope_row_mass ht eta c)
    (capHeatGradientSchurEnvelope_col_integrable ht eta c)
    (capHeatGradientSchurEnvelope_col_mass ht eta c)
    hq_meas hq_sq
  let S : ℝ → ℝ := fun x =>
    ∫ y : ℝ, capMovingHeatGradientKernel eta R c t x y * q y
  have hpoint : ∀ x, capWeight eta R x *
      |paper5MovingFrameHeatGradOp c t f x| ^ 2 =
        Real.exp (-t) ^ 2 * S x ^ 2 := by
    intro x
    rw [← capWeightSqrt_mul_sq_eq eta R x
      (paper5MovingFrameHeatGradOp c t f x),
      capWeightSqrt_mul_movingFrameHeatGradOp_eq ht]
    dsimp [S, q]
    ring
  have hout : Integrable (fun x => capWeight eta R x *
      |paper5MovingFrameHeatGradOp c t f x| ^ 2) := by
    refine (hk.1.const_mul (Real.exp (-t) ^ 2)).congr
      (Eventually.of_forall fun x => ?_)
    change Real.exp (-t) ^ 2 * S x ^ 2 =
      capWeight eta R x * |paper5MovingFrameHeatGradOp c t f x| ^ 2
    exact (hpoint x).symm
  refine ⟨hout, ?_⟩
  calc
    (∫ x : ℝ, capWeight eta R x *
        |paper5MovingFrameHeatGradOp c t f x| ^ 2) =
      Real.exp (-t) ^ 2 * ∫ x : ℝ, S x ^ 2 := by
        simp_rw [hpoint]
        rw [integral_const_mul]
    _ ≤ Real.exp (-t) ^ 2 *
        (capHeatGradientSchurMass eta c t ^ 2 * ∫ y : ℝ, q y ^ 2) :=
      mul_le_mul_of_nonneg_left hk.2 (sq_nonneg _)
    _ = (Real.exp (-t) * capHeatGradientSchurMass eta c t) ^ 2 *
        ∫ y : ℝ, capWeight eta R y * |f y| ^ 2 := by
      have hqeq : (∫ y : ℝ, q y ^ 2) =
          ∫ y : ℝ, capWeight eta R y * |f y| ^ 2 := by
        apply integral_congr_ae
        filter_upwards with y
        exact capWeightSqrt_mul_sq_eq eta R y (f y)
      rw [hqeq]
      ring

section AxiomAudit

#print axioms capWeight_monotone_space
#print axioms capWeight_le_exp_abs_mul
#print axioms capWeightSqrtRatio_le_exp_abs
#print axioms capWeight_frozenElliptic_gradient_difference_l2_bounded
#print axioms capHeatSchurEnvelope_l2_bounded
#print axioms capHeatGradientSchurEnvelope_l2_bounded
#print axioms capWeight_movingFrameHeatOp_l2_bounded
#print axioms capWeight_movingFrameHeatGradOp_l2_bounded

end AxiomAudit

end ShenWork.Paper1
