import ShenWork.PDE.HeatKernelGradientEstimates

/-!
# Interior `C²` smoothing of the cosine heat representation

This file proves the analytic heart of the interior-`C²` conjunct now required
by `intervalDomainClassicalRegularity`: for any `t > 0` and any bounded sequence
of Neumann cosine coefficients `a`, the cosine heat value
`x ↦ unitIntervalCosineHeatValue t a x` is a `C²` function on all of `ℝ`
(hence in particular `ContDiffOn ℝ 2 _ (Set.Ioo 0 1)`).

This is the heat-semigroup smoothing fact underlying the mild/Duhamel
solution: `u(t,·) = e^{tΔ_N}u₀ + ∫₀ᵗ e^{(t-s)Δ_N}F(u(s))ds` is spatially
`C^∞` on the interior for `t > 0`.

We build the second-derivative term-weight, prove the term-by-term `HasDerivAt`
chains using the existing first-derivative machinery, dominate the second
derivative by a summable reciprocal-square majorant, and assemble `ContDiff ℝ 2`
via `contDiff_succ_iff_deriv`.

The remaining gap toward fully discharging `RegularityBootstrap` is the
*identification* step: relating the abstract mild-solution trajectory `u t`
(a fixed point of `intervalCoupledDuhamelOperator`) to this concrete cosine
heat representation, i.e. proving that `intervalDomainLift (u t)` agrees on
`(0,1)` with `unitIntervalCosineHeatValue t (coeffs)`.  That algebraic bridge
is documented but not yet supplied here.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace ShenWork.IntervalDomainRegularityBootstrap

open ShenWork.IntervalDomain
open ShenWork.HeatKernelGradientEstimates

/-! ## Second spatial derivative of the cosine heat representation -/

/-- Pointwise coefficient multiplying the `n`-th cosine coefficient in the
*second* spatial derivative of the interval heat flow.  Differentiating
`-(nπ)·sin(nπx)` once more yields `-(nπ)²·cos(nπx)`. -/
def unitIntervalCosineHeatSecondPointWeight (t x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-t * unitIntervalCosineEigenvalue n) *
    (-((n : ℝ) * Real.pi) ^ 2 * Real.cos ((n : ℝ) * Real.pi * x))

/-- Cosine-coefficient model for the second spatial derivative of the interval
heat semigroup value at `x`. -/
def unitIntervalCosineHeatSecondValue (t : ℝ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' n, unitIntervalCosineHeatSecondPointWeight t x n * a n

/-- The gradient term-weight differentiates to the second term-weight. -/
theorem unitIntervalCosineHeatGradientPointWeight_hasDerivAt
    (t : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => unitIntervalCosineHeatGradientPointWeight t y n)
      (unitIntervalCosineHeatSecondPointWeight t x n) x := by
  have harg : HasDerivAt (fun y : ℝ => (n : ℝ) * Real.pi * y) ((n : ℝ) * Real.pi) x := by
    simpa using (hasDerivAt_id x).const_mul ((n : ℝ) * Real.pi)
  have hsin : HasDerivAt (fun y : ℝ => Real.sin ((n : ℝ) * Real.pi * y))
      (Real.cos ((n : ℝ) * Real.pi * x) * ((n : ℝ) * Real.pi)) x :=
    harg.sin
  -- gradient weight = exp(...) * (-(nπ)) * sin(nπ x)
  have h := (hsin.const_mul (-((n : ℝ) * Real.pi))).const_mul
    (Real.exp (-t * unitIntervalCosineEigenvalue n))
  simp only [unitIntervalCosineHeatGradientPointWeight,
    unitIntervalCosineHeatSecondPointWeight]
  convert h using 1
  ring

/-- The second term-weight (with a fixed coefficient) is the derivative of the
gradient term-weight (with the same coefficient). -/
theorem unitIntervalCosineHeatGradientTerm_hasDerivAt
    (t : ℝ) (a : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => unitIntervalCosineHeatGradientPointWeight t y n * a n)
      (unitIntervalCosineHeatSecondPointWeight t x n * a n) x :=
  (unitIntervalCosineHeatGradientPointWeight_hasDerivAt t n x).mul_const (a n)

/-! ## Summable majorants from the bounded-coefficient hypothesis -/

/-- Elementary Gaussian-tail estimate `x²·e^{-x} ≤ 4` re-used to control the
*second* derivative weight by a reciprocal-square trace. -/
lemma real_eigen_exp_le {t : ℝ} (ht : 0 < t) (n : ℕ) :
    ((n : ℝ) * Real.pi) ^ 2 *
        Real.exp (-t * unitIntervalCosineEigenvalue n) ≤
      4 / (t ^ 2 * ((n : ℝ) * Real.pi) ^ 2) := by
  by_cases hn : n = 0
  · subst n; simp
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hpi : 0 < Real.pi := Real.pi_pos
    set lam : ℝ := unitIntervalCosineEigenvalue n with hlam
    have hlam_eq : lam = ((n : ℝ) * Real.pi) ^ 2 := rfl
    have hlam_pos : 0 < lam := by
      rw [hlam_eq]; positivity
    set z : ℝ := t * lam with hz
    have hz_nonneg : 0 ≤ z := by rw [hz]; positivity
    have hgauss : z ^ 2 * Real.exp (-z) ≤ 4 :=
      real_sq_mul_exp_neg_le_four hz_nonneg
    have hden : 0 < t ^ 2 * lam := by positivity
    -- lam * exp(-t lam) = (1/(t² lam)) * (z² exp(-z))
    have hkey : lam * Real.exp (-t * lam) =
        (1 / (t ^ 2 * lam)) * (z ^ 2 * Real.exp (-z)) := by
      rw [hz]
      field_simp
    have hbound : lam * Real.exp (-t * lam) ≤ 4 / (t ^ 2 * lam) := by
      rw [hkey]
      calc (1 / (t ^ 2 * lam)) * (z ^ 2 * Real.exp (-z))
          ≤ (1 / (t ^ 2 * lam)) * 4 :=
            mul_le_mul_of_nonneg_left hgauss (by positivity)
        _ = 4 / (t ^ 2 * lam) := by ring
    rw [hlam_eq] at hbound
    simpa [hlam_eq] using hbound

/-- Reciprocal-square summand controlling the second-derivative series. -/
def reciprocalSquareTerm (n : ℕ) : ℝ := 1 / (n : ℝ) ^ 2

theorem reciprocalSquareTerm_summable : Summable reciprocalSquareTerm := by
  change Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2)
  exact Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)

/-- Absolute bound for the second derivative term-weight by a reciprocal square. -/
theorem unitIntervalCosineHeatSecondPointWeight_abs_le
    {t : ℝ} (ht : 0 < t) (x : ℝ) (n : ℕ) :
    |unitIntervalCosineHeatSecondPointWeight t x n| ≤
      (4 / (t ^ 2 * Real.pi ^ 2)) * reciprocalSquareTerm n := by
  by_cases hn : n = 0
  · subst n
    simp [unitIntervalCosineHeatSecondPointWeight, reciprocalSquareTerm,
      unitIntervalCosineEigenvalue]
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hpi : 0 < Real.pi := Real.pi_pos
    -- |weight| ≤ (nπ)² exp(-t λ_n) ≤ 4/(t² (nπ)²)
    have hcos : |Real.cos ((n : ℝ) * Real.pi * x)| ≤ 1 := Real.abs_cos_le_one _
    have hstep : |unitIntervalCosineHeatSecondPointWeight t x n| ≤
        ((n : ℝ) * Real.pi) ^ 2 *
          Real.exp (-t * unitIntervalCosineEigenvalue n) := by
      unfold unitIntervalCosineHeatSecondPointWeight
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _), abs_mul, abs_neg,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ ((n:ℝ) * Real.pi) ^ 2)]
      calc Real.exp (-t * unitIntervalCosineEigenvalue n) *
              (((n:ℝ) * Real.pi) ^ 2 * |Real.cos ((n:ℝ) * Real.pi * x)|)
          ≤ Real.exp (-t * unitIntervalCosineEigenvalue n) *
              (((n:ℝ) * Real.pi) ^ 2 * 1) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hcos (by positivity))
              (Real.exp_nonneg _)
        _ = ((n:ℝ) * Real.pi) ^ 2 *
              Real.exp (-t * unitIntervalCosineEigenvalue n) := by ring
    have hgauss := real_eigen_exp_le ht n
    have hfinal : 4 / (t ^ 2 * ((n : ℝ) * Real.pi) ^ 2) =
        (4 / (t ^ 2 * Real.pi ^ 2)) * reciprocalSquareTerm n := by
      unfold reciprocalSquareTerm
      field_simp
    calc |unitIntervalCosineHeatSecondPointWeight t x n|
        ≤ ((n : ℝ) * Real.pi) ^ 2 *
            Real.exp (-t * unitIntervalCosineEigenvalue n) := hstep
      _ ≤ 4 / (t ^ 2 * ((n : ℝ) * Real.pi) ^ 2) := hgauss
      _ = (4 / (t ^ 2 * Real.pi ^ 2)) * reciprocalSquareTerm n := hfinal

/-! ## Term-by-term differentiation of the gradient series -/

/-- The gradient series is differentiable, with derivative the second value
series, provided the coefficients are bounded by `M`. -/
theorem unitIntervalCosineHeatGradientValue_hasDerivAt
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n| ≤ M) (x : ℝ) :
    HasDerivAt (fun z : ℝ => unitIntervalCosineHeatGradientValue t a z)
      (unitIntervalCosineHeatSecondValue t a x) x := by
  set C : ℝ := 4 / (t ^ 2 * Real.pi ^ 2) with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  set u : ℕ → ℝ := fun n => C * reciprocalSquareTerm n * |M| with hu_def
  have hu_summable : Summable u := by
    have := (reciprocalSquareTerm_summable.mul_left C).mul_right |M|
    simpa [hu_def, mul_assoc] using this
  -- termwise derivative bound
  have hbound : ∀ n y,
      ‖unitIntervalCosineHeatSecondPointWeight t y n * a n‖ ≤ u n := by
    intro n y
    have hMn : |a n| ≤ |M| := le_trans (hM n) (le_abs_self M)
    rw [Real.norm_eq_abs, abs_mul]
    calc |unitIntervalCosineHeatSecondPointWeight t y n| * |a n|
        ≤ (C * reciprocalSquareTerm n) * |M| := by
          refine mul_le_mul (unitIntervalCosineHeatSecondPointWeight_abs_le ht y n)
            hMn (abs_nonneg _) ?_
          exact mul_nonneg hC0 (by unfold reciprocalSquareTerm; positivity)
      _ = u n := by rw [hu_def]
  -- the gradient series itself converges at x (it is the existing g')
  have hgrad_sum : Summable
      (fun n => unitIntervalCosineHeatGradientPointWeight t x n * a n) := by
    have hgbound : ∀ n,
        ‖unitIntervalCosineHeatGradientPointWeight t x n * a n‖ ≤
          (4 / (t ^ 2 * Real.pi ^ 3)) *
            unitIntervalCosineReciprocalCubeTerm n
              * |M| := by
      intro n
      have hMn : |a n| ≤ |M| := le_trans (hM n) (le_abs_self M)
      rw [Real.norm_eq_abs, abs_mul]
      have hw := unitIntervalCosineHeatGradientPointWeight_abs_le_reciprocal_cube
        ht x n
      calc |unitIntervalCosineHeatGradientPointWeight t x n| * |a n|
          ≤ ((4 / (t ^ 2 * Real.pi ^ 3)) *
              unitIntervalCosineReciprocalCubeTerm n) * |M| := by
            refine mul_le_mul hw hMn (abs_nonneg _) ?_
            exact mul_nonneg (by positivity)
              (unitIntervalCosineReciprocalCubeTerm_nonneg n)
        _ = _ := by ring
    have hmaj : Summable (fun n =>
        (4 / (t ^ 2 * Real.pi ^ 3)) *
          unitIntervalCosineReciprocalCubeTerm n * |M|) := by
      have := (unitIntervalCosineReciprocalCubeTerm_summable.mul_left
        (4 / (t ^ 2 * Real.pi ^ 3))).mul_right |M|
      simpa [mul_assoc] using this
    exact Summable.of_norm_bounded hmaj hgbound
  -- apply hasDerivAt_tsum
  have := hasDerivAt_tsum (𝕜 := ℝ) (F := ℝ) (u := u)
    (g := fun n z => unitIntervalCosineHeatGradientPointWeight t z n * a n)
    (g' := fun n z => unitIntervalCosineHeatSecondPointWeight t z n * a n)
    hu_summable
    (fun n y => unitIntervalCosineHeatGradientTerm_hasDerivAt t a n y)
    (fun n y => hbound n y)
    hgrad_sum x
  simpa [unitIntervalCosineHeatGradientValue, unitIntervalCosineHeatSecondValue]
    using this

/-- `deriv` form: the spatial derivative of the gradient series is the second
value series. -/
theorem unitIntervalCosineHeatGradientValue_deriv
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n| ≤ M) (x : ℝ) :
    deriv (fun z : ℝ => unitIntervalCosineHeatGradientValue t a z) x =
      unitIntervalCosineHeatSecondValue t a x :=
  (unitIntervalCosineHeatGradientValue_hasDerivAt ht hM x).deriv

/-! ## Continuity of the second-derivative series -/

/-- Each second-derivative term is continuous in `x`. -/
theorem unitIntervalCosineHeatSecondPointWeight_continuous (t : ℝ) (a : ℕ → ℝ)
    (n : ℕ) :
    Continuous (fun x => unitIntervalCosineHeatSecondPointWeight t x n * a n) := by
  unfold unitIntervalCosineHeatSecondPointWeight
  fun_prop

/-- The second-derivative series is continuous in `x`, by uniform (Weierstrass
`M`-test) convergence with the reciprocal-square majorant. -/
theorem unitIntervalCosineHeatSecondValue_continuous
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n| ≤ M) :
    Continuous (fun x => unitIntervalCosineHeatSecondValue t a x) := by
  set C : ℝ := 4 / (t ^ 2 * Real.pi ^ 2) with hC
  set u : ℕ → ℝ := fun n => C * reciprocalSquareTerm n * |M| with hu_def
  have hu_summable : Summable u := by
    have := (reciprocalSquareTerm_summable.mul_left C).mul_right |M|
    simpa [hu_def, mul_assoc] using this
  have hbound : ∀ n x,
      ‖unitIntervalCosineHeatSecondPointWeight t x n * a n‖ ≤ u n := by
    intro n x
    have hMn : |a n| ≤ |M| := le_trans (hM n) (le_abs_self M)
    rw [Real.norm_eq_abs, abs_mul]
    have hrec_nonneg : (0:ℝ) ≤ C * reciprocalSquareTerm n :=
      mul_nonneg (by rw [hC]; positivity)
        (by unfold reciprocalSquareTerm; positivity)
    calc |unitIntervalCosineHeatSecondPointWeight t x n| * |a n|
        ≤ (C * reciprocalSquareTerm n) * |M| :=
          mul_le_mul (unitIntervalCosineHeatSecondPointWeight_abs_le ht x n)
            hMn (abs_nonneg _) hrec_nonneg
      _ = u n := by rw [hu_def]
  exact continuous_tsum
    (fun n => unitIntervalCosineHeatSecondPointWeight_continuous t a n)
    hu_summable (fun n x => hbound n x)

/-! ## Assembled `C²` smoothing -/

/-- **Heat-semigroup interior smoothing (`C²`).**  For `t > 0` and bounded
Neumann cosine coefficients, the cosine heat value is twice continuously
differentiable on all of `ℝ`.  This is the spatial-regularity engine for the
mild solution. -/
theorem unitIntervalCosineHeatValue_contDiff_two
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n| ≤ M) :
    ContDiff ℝ 2 (fun x => unitIntervalCosineHeatValue t a x) := by
  -- First derivative everywhere = gradient value.
  have hval_summable : ∀ x, Summable
      (fun n => unitIntervalCosineHeatPointWeight t x n * a n) := by
    intro x
    have hbound : ∀ n,
        ‖unitIntervalCosineHeatPointWeight t x n * a n‖ ≤
          Real.exp (-t * unitIntervalCosineEigenvalue n) * |M| := by
      intro n
      have hMn : |a n| ≤ |M| := le_trans (hM n) (le_abs_self M)
      rw [Real.norm_eq_abs, abs_mul]
      have hw : |unitIntervalCosineHeatPointWeight t x n| ≤
          Real.exp (-t * unitIntervalCosineEigenvalue n) := by
        unfold unitIntervalCosineHeatPointWeight
        rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
        have : |unitIntervalCosineMode n x| ≤ 1 := by
          unfold unitIntervalCosineMode; exact Real.abs_cos_le_one _
        calc Real.exp (-t * unitIntervalCosineEigenvalue n) *
              |unitIntervalCosineMode n x|
            ≤ Real.exp (-t * unitIntervalCosineEigenvalue n) * 1 :=
              mul_le_mul_of_nonneg_left this (Real.exp_nonneg _)
          _ = Real.exp (-t * unitIntervalCosineEigenvalue n) := by ring
      exact mul_le_mul hw hMn (abs_nonneg _) (Real.exp_nonneg _)
    refine Summable.of_norm_bounded ?_ hbound
    exact (unitIntervalCosineHeatTrace_single_exp_summable
      ht).mul_right |M|
  -- gradient bound for the first-derivative termwise machinery
  set Cg : ℝ := 4 / (t ^ 2 * Real.pi ^ 3) with hCg
  have hCg0 : (0:ℝ) ≤ Cg := by rw [hCg]; positivity
  have hgrad_majorant : Summable (fun n =>
      Cg * unitIntervalCosineReciprocalCubeTerm n * |M|) := by
    have := (unitIntervalCosineReciprocalCubeTerm_summable.mul_left
      Cg).mul_right |M|
    simpa [mul_assoc] using this
  have hgrad_bound : ∀ n y,
      ‖unitIntervalCosineHeatGradientPointWeight t y n * a n‖ ≤
        Cg * unitIntervalCosineReciprocalCubeTerm n * |M| := by
    intro n y
    have hMn : |a n| ≤ |M| := le_trans (hM n) (le_abs_self M)
    rw [Real.norm_eq_abs, abs_mul]
    have hw := unitIntervalCosineHeatGradientPointWeight_abs_le_reciprocal_cube
      ht y n
    calc |unitIntervalCosineHeatGradientPointWeight t y n| * |a n|
        ≤ (Cg * unitIntervalCosineReciprocalCubeTerm n) * |M| := by
          refine mul_le_mul hw hMn (abs_nonneg _) ?_
          exact mul_nonneg hCg0
            (unitIntervalCosineReciprocalCubeTerm_nonneg n)
      _ = _ := by ring
  have hderiv1 : ∀ x, HasDerivAt (fun z => unitIntervalCosineHeatValue t a z)
      (unitIntervalCosineHeatGradientValue t a x) x := by
    intro x
    exact unitIntervalCosineHeatValue_hasDerivAt_of_summable_bound
      (t := t) (x := x) (x₀ := x) hgrad_majorant hgrad_bound (hval_summable x)
  -- second derivative everywhere = second value
  have hderiv2 : ∀ x, HasDerivAt
      (fun z => unitIntervalCosineHeatGradientValue t a z)
      (unitIntervalCosineHeatSecondValue t a x) x :=
    fun x => unitIntervalCosineHeatGradientValue_hasDerivAt ht hM x
  -- Now assemble ContDiff ℝ 2.
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x => (hderiv1 x).differentiableAt, by simp, ?_⟩
  -- deriv of value = gradient value (as a function)
  have hderiv_eq : deriv (fun z => unitIntervalCosineHeatValue t a z) =
      fun x => unitIntervalCosineHeatGradientValue t a x := by
    funext x; exact (hderiv1 x).deriv
  rw [hderiv_eq, contDiff_one_iff_deriv]
  refine ⟨fun x => (hderiv2 x).differentiableAt, ?_⟩
  have hderiv2_eq : deriv (fun z => unitIntervalCosineHeatGradientValue t a z) =
      fun x => unitIntervalCosineHeatSecondValue t a x := by
    funext x; exact (hderiv2 x).deriv
  rw [hderiv2_eq]
  exact unitIntervalCosineHeatSecondValue_continuous ht hM

/-- Interior-`C²` corollary in the exact shape demanded by
`intervalDomainClassicalRegularity`: if a function `f : intervalDomainPoint → ℝ`
agrees on the open interior `(0,1)` with a cosine heat value (`t > 0`, bounded
coefficients), then its zero-extension lift is `ContDiffOn ℝ 2` on `(0,1)`. -/
theorem intervalDomainLift_contDiffOn_two_of_eqOn_heatValue
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n| ≤ M)
    {f : intervalDomainPoint → ℝ}
    (hf : Set.EqOn (intervalDomainLift f)
      (fun x => unitIntervalCosineHeatValue t a x) (Set.Ioo (0 : ℝ) 1)) :
    ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Ioo (0 : ℝ) 1) :=
  ((unitIntervalCosineHeatValue_contDiff_two ht hM).contDiffOn).congr hf

end ShenWork.IntervalDomainRegularityBootstrap
