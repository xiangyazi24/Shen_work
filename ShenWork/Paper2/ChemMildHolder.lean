/-
  ShenWork/Paper2/ChemMildHolder.lean

  **Paper2 Theorem 1.1 (χ₀ < 0) — P2-T11 hregularize pass-1: heat-semigroup
  Hölder-smoothing by elementary interpolation.**

  GOAL (the route-(c) "pass 1"): manufacture the fractional
  Hölder gain `S(t)f ∈ C^θ` (with `t^{−θ/2}` blow-up) by INTERPOLATING two already
  committed `L∞→L∞` endpoint bounds for the interval-Neumann heat semigroup
  `S(t) = intervalNeumannHeatSemigroup t`:

    * θ=0 (sup / maximum principle, kernel mass = 1):
        `|S(t)f x| ≤ Cf`   whenever `|f| ≤ Cf`
        (`intervalFullSemigroupOperator_Linfty_bound`,
         `ShenWork/PDE/IntervalFullKernelSupBound.lean:52`).
    * θ=1 (gradient, `t^{−1/2}`):
        `|∂ₓ S(t)f x| ≤ C∇ · t^{−1/2} · Cf`,  `C∇ = 1/√π`
        (`intervalNeumann_heat_gradient_bound`,
         `ShenWork/Paper2/IntervalHeatGradient.lean:90`).

  Together with the everywhere-`HasDerivAt` representation
  (`intervalFullSemigroupOperator_hasDerivAt_fst`,
   `ShenWork/PDE/IntervalFullKernelGradientLinfty.lean:380`) and the mean-value
  inequality `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`, these give

    `|g(x) − g(y)| ≤ min(2 Cf, C∇ t^{−1/2} Cf · |x−y|)`   for `g := S(t)f`,

  and the elementary interpolation `min a b ≤ a^{1−θ} b^θ` collapses this to

    `|g(x) − g(y)| ≤ 2^{1−θ} C∇^θ · t^{−θ/2} · Cf · |x−y|^θ`.

  This is pure interpolation — NO Mathlib heat theory beyond the two committed
  endpoint bounds.

  CONTENTS
  * `min_le_rpow_interp` — the interpolation helper `min a b ≤ a^{1−θ}b^θ`.
  * `neumannHeat_Linf_to_Ctheta` — the VALUE Hölder-smoothing bound (PROVED).
  * `neumannHeatSecondDeriv_Linfty_bound` — the NAMED missing input for the
    gradient version (the `t^{−1}` second-derivative sup bound; NOT yet committed
    in the PDE layer; taken as an explicit hypothesis, never as the conclusion).
  * `neumannHeatGradient_Linf_to_Ctheta_of_second_deriv` — the GRADIENT
    Hölder-smoothing bound, CONDITIONAL on the named second-derivative input.
  * `mild_orderBox_positiveTime_holder_integrand_integrable` — the integrability
    fact `∫₀ᵗ (t−s)^{−θ/2} ds < ∞` that the mild-representation Hölder bootstrap
    consumes; the precise mild-bootstrap statement is recorded as the doc target.

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.Paper2.IntervalHeatGradient
import ShenWork.PDE.IntervalFullKernelSupBound
import ShenWork.PDE.IntervalFullKernelGradientLinfty
import ShenWork.PDE.IntervalFullKernelSecondDerivLinfty
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

open MeasureTheory
open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator_hasDerivAt_deriv_fst
    intervalFullSemigroupOperator_secondDeriv_Linfty_pointwise_inv_t)

namespace ShenWork.Paper2

/-! ## The interpolation helper -/

/-- **Interpolation helper: `min a b ≤ a^{1−θ} · b^θ`** for `a, b ≥ 0`, `0 ≤ θ ≤ 1`.

This is the AM-style geometric interpolation of a minimum.  It is the whole
arithmetic core of the Hölder-smoothing estimate: applied to `a = 2‖f‖∞` and
`b = C∇ t^{−1/2}‖f‖∞ · |x−y|` it turns the two-sided value/derivative difference
bound into the single `|x−y|^θ` Hölder bound. -/
theorem min_le_rpow_interp {a b θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    min a b ≤ a ^ (1 - θ) * b ^ θ := by
  rcases le_total a b with hab | hba
  · -- `min a b = a`; bound by replacing `b^θ` from below using `a ≤ b`.
    rw [min_eq_left hab]
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · -- `a = 0`: RHS ≥ 0.
      have hrhs : 0 ≤ a ^ (1 - θ) * b ^ θ := by positivity
      simpa [← ha0] using hrhs
    · have hsplit : a = a ^ (1 - θ) * a ^ θ := by
        rw [← Real.rpow_add hapos]; simp
      have hstep : a ^ (1 - θ) * a ^ θ ≤ a ^ (1 - θ) * b ^ θ := by
        have hmono : a ^ θ ≤ b ^ θ := Real.rpow_le_rpow ha hab hθ0
        exact mul_le_mul_of_nonneg_left hmono (by positivity)
      calc a = a ^ (1 - θ) * a ^ θ := hsplit
        _ ≤ a ^ (1 - θ) * b ^ θ := hstep
  · -- `min a b = b`; bound by replacing `a^{1−θ}` from below using `b ≤ a`.
    rw [min_eq_right hba]
    rcases eq_or_lt_of_le hb with hb0 | hbpos
    · have hrhs : 0 ≤ a ^ (1 - θ) * b ^ θ := by positivity
      simpa [← hb0] using hrhs
    · have hsplit : b = b ^ (1 - θ) * b ^ θ := by
        rw [← Real.rpow_add hbpos]; simp
      have hstep : b ^ (1 - θ) * b ^ θ ≤ a ^ (1 - θ) * b ^ θ := by
        have hmono : b ^ (1 - θ) ≤ a ^ (1 - θ) :=
          Real.rpow_le_rpow hb hba (by linarith)
        exact mul_le_mul_of_nonneg_right hmono (by positivity)
      calc b = b ^ (1 - θ) * b ^ θ := hsplit
        _ ≤ a ^ (1 - θ) * b ^ θ := hstep

/-! ## Value bound: the difference `|g(x) − g(y)|` two ways -/

/-- The interval-Neumann heat semigroup `g := S(t)f` is differentiable everywhere
with derivative bounded by `C∇ t^{−1/2} Cf`; hence by the mean value inequality it
is globally `(C∇ t^{−1/2} Cf)`-Lipschitz:

  `|g(x) − g(y)| ≤ C∇ t^{−1/2} Cf · |x − y|`. -/
theorem neumannHeat_lipschitz_of_grad {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    {Cf : ℝ} (hf : ∀ y, |f y| ≤ Cf) (x y : ℝ) :
    |intervalNeumannHeatSemigroup t f x - intervalNeumannHeatSemigroup t f y|
      ≤ gradSmoothingConst * t ^ (-(1 / 2) : ℝ) * Cf * |x - y| := by
  set g : ℝ → ℝ := fun z => intervalNeumannHeatSemigroup t f z with hg
  set C : ℝ := gradSmoothingConst * t ^ (-(1 / 2) : ℝ) * Cf with hC
  have hderiv : ∀ z ∈ (Set.univ : Set ℝ), HasDerivWithinAt g (deriv g z) Set.univ z := by
    intro z _
    have hz := ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_fst
      ht hf_meas hf z
    exact (hz.differentiableAt.hasDerivAt).hasDerivWithinAt
  have hbound : ∀ z ∈ (Set.univ : Set ℝ), ‖deriv g z‖ ≤ C := by
    intro z _
    rw [Real.norm_eq_abs]
    exact intervalNeumann_heat_gradient_bound ht hf_meas hf z
  have hconv : Convex ℝ (Set.univ : Set ℝ) := convex_univ
  have hmvt :=
    hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      (Set.mem_univ y) (Set.mem_univ x)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  simpa [hg, hC] using hmvt

/-- **Pass-1 VALUE Hölder-smoothing bound** (`L∞ → C^θ`).

For `0 < θ < 1`, `0 < t`, bounded measurable data `f` (`|f| ≤ Cf`) and any
`x, y`, the interval-Neumann heat semigroup gains a fractional Hölder modulus:

  `|S(t)f x − S(t)f y| ≤ Cθ · t^{−θ/2} · Cf · |x − y|^θ`,   `Cθ = 2^{1−θ} C∇^θ`.

PROOF = interpolation: the difference is bounded BOTH by `2 Cf` (sup bound, θ=0)
AND by `C∇ t^{−1/2} Cf |x−y|` (gradient bound, θ=1, via the mean value
inequality); `min_le_rpow_interp` collapses the two into the `|x−y|^θ` shape. -/
theorem neumannHeat_Linf_to_Ctheta {t θ : ℝ} (ht : 0 < t)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {f : ℝ → ℝ} (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    {Cf : ℝ} (hf : ∀ y, |f y| ≤ Cf) (x y : ℝ) :
    |intervalNeumannHeatSemigroup t f x - intervalNeumannHeatSemigroup t f y|
      ≤ (2 : ℝ) ^ (1 - θ) * gradSmoothingConst ^ θ
          * t ^ (-(θ / 2) : ℝ) * Cf * |x - y| ^ θ := by
  have hCf : 0 ≤ Cf := le_trans (abs_nonneg (f 0)) (hf 0)
  have hCgrad : 0 ≤ gradSmoothingConst := gradSmoothingConst_nonneg
  -- value bound (θ=0 leg): `|g x − g y| ≤ 2 Cf`.
  have hsupx : |intervalNeumannHeatSemigroup t f x| ≤ Cf :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound ht hCf hf x
  have hsupy : |intervalNeumannHeatSemigroup t f y| ≤ Cf :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound ht hCf hf y
  have hval :
      |intervalNeumannHeatSemigroup t f x - intervalNeumannHeatSemigroup t f y|
        ≤ 2 * Cf := by
    calc |intervalNeumannHeatSemigroup t f x - intervalNeumannHeatSemigroup t f y|
        ≤ |intervalNeumannHeatSemigroup t f x| + |intervalNeumannHeatSemigroup t f y| :=
          abs_sub _ _
      _ ≤ Cf + Cf := add_le_add hsupx hsupy
      _ = 2 * Cf := by ring
  -- gradient bound (θ=1 leg): `|g x − g y| ≤ C∇ t^{−1/2} Cf |x−y|`.
  have hlip := neumannHeat_lipschitz_of_grad ht hf_meas hf x y
  set a : ℝ := 2 * Cf with ha
  set b : ℝ := gradSmoothingConst * t ^ (-(1 / 2) : ℝ) * Cf * |x - y| with hb
  have hann : 0 ≤ a := by rw [ha]; positivity
  have htpos : (0 : ℝ) < t ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos ht _
  have hbnn : 0 ≤ b := by rw [hb]; positivity
  -- difference ≤ min a b.
  have hmin :
      |intervalNeumannHeatSemigroup t f x - intervalNeumannHeatSemigroup t f y| ≤ min a b :=
    le_min hval hlip
  -- min a b ≤ a^{1−θ} b^θ.
  have hinterp : min a b ≤ a ^ (1 - θ) * b ^ θ :=
    min_le_rpow_interp hann hbnn hθ0.le hθ1.le
  have hchain :
      |intervalNeumannHeatSemigroup t f x - intervalNeumannHeatSemigroup t f y|
        ≤ a ^ (1 - θ) * b ^ θ := le_trans hmin hinterp
  -- now rewrite `a^{1−θ} b^θ` into the target shape.
  -- a^{1−θ} = (2 Cf)^{1−θ} = 2^{1−θ} Cf^{1−θ}
  -- b^θ = (C∇ t^{−1/2} Cf |x−y|)^θ = C∇^θ t^{−θ/2} Cf^θ |x−y|^θ
  -- product collapses the Cf and `2` factors.
  have hapow : a ^ (1 - θ) = (2 : ℝ) ^ (1 - θ) * Cf ^ (1 - θ) := by
    rw [ha, Real.mul_rpow (by norm_num) hCf]
  have htpow : (t ^ (-(1 / 2) : ℝ)) ^ θ = t ^ (-(θ / 2) : ℝ) := by
    rw [← Real.rpow_mul ht.le]
    congr 1; ring
  have hbpow :
      b ^ θ = gradSmoothingConst ^ θ * t ^ (-(θ / 2) : ℝ) * Cf ^ θ * |x - y| ^ θ := by
    rw [hb]
    rw [Real.mul_rpow (by positivity) (abs_nonneg _),
        Real.mul_rpow (by positivity) hCf,
        Real.mul_rpow hCgrad htpos.le, htpow]
  -- combine: a^{1−θ} b^θ = 2^{1−θ} C∇^θ t^{−θ/2} Cf (|x−y|^θ), using Cf^{1−θ}·Cf^θ = Cf.
  have hCfcollapse : Cf ^ (1 - θ) * Cf ^ θ = Cf := by
    rw [← Real.rpow_add' hCf (by simp)]; simp
  have hfinal :
      a ^ (1 - θ) * b ^ θ
        = (2 : ℝ) ^ (1 - θ) * gradSmoothingConst ^ θ
            * t ^ (-(θ / 2) : ℝ) * Cf * |x - y| ^ θ := by
    rw [hapow, hbpow]
    rw [show (2 : ℝ) ^ (1 - θ) * Cf ^ (1 - θ)
          * (gradSmoothingConst ^ θ * t ^ (-(θ / 2) : ℝ) * Cf ^ θ * |x - y| ^ θ)
        = (2 : ℝ) ^ (1 - θ) * gradSmoothingConst ^ θ * t ^ (-(θ / 2) : ℝ)
            * (Cf ^ (1 - θ) * Cf ^ θ) * |x - y| ^ θ by ring]
    rw [hCfcollapse]
  rw [hfinal] at hchain
  exact hchain

/-! ## Gradient bound (conditional on the missing second-derivative input)

The gradient Hölder-smoothing estimate

  `|∂ₓS(t)f x − ∂ₓS(t)f y| ≤ C'θ · t^{−(1+θ)/2} · Cf · |x − y|^θ`

is the SAME interpolation, but between the committed `t^{−1/2}` gradient bound
(θ=0 leg, applied to `g' := ∂ₓS(t)f`) and a `t^{−1}` SECOND-derivative bound
(θ=1 leg).  The PDE layer commits the gradient bound but **not** the
second-derivative bound `‖∂ₓₓS(t)f‖∞ ≤ C∇∇ t^{−1}`.  We therefore take that
missing input as an explicit named hypothesis (NEVER as the conclusion) and prove
the gradient Hölder bound conditionally on it.  Discharging
`neumannHeatSecondDeriv_Linfty_bound` in the committed PDE layer (the genuine
remaining work for this leg) closes the gradient version unconditionally. -/

/-- **NAMED missing PDE input** for the gradient Hölder leg: the `t^{−1}`
second-derivative sup bound for the interval-Neumann heat semigroup.  Packaged as
a Prop on the data `(t, f, Cf, C∇∇)`; it is the single fact the gradient version
needs beyond what is already committed.  (Not proved here — the committed PDE
layer currently lacks `‖∂ₓₓS(t)f‖∞ ≤ C∇∇ t^{−1}`.) -/
def neumannHeatSecondDeriv_Linfty_bound
    (t : ℝ) (f : ℝ → ℝ) (Cf Cgg : ℝ) : Prop :=
  (∀ z : ℝ, HasDerivAt (fun u : ℝ => deriv (fun w : ℝ => intervalNeumannHeatSemigroup t f w) u)
      (deriv (fun u : ℝ => deriv (fun w : ℝ => intervalNeumannHeatSemigroup t f w) u) z) z) ∧
  (∀ z : ℝ, |deriv (fun u : ℝ => deriv (fun w : ℝ => intervalNeumannHeatSemigroup t f w) u) z|
      ≤ Cgg * t ^ (-(1 : ℝ)) * Cf)

/-- **Pass-1 GRADIENT Hölder-smoothing bound** (`L∞ → C^θ` for `∂ₓS(t)f`),
CONDITIONAL on the named second-derivative input.

Given the `t^{−1}` second-derivative bound (the only missing committed input),
the SAME interpolation as the value version yields, for `g' := ∂ₓS(t)f`,

  `|g'(x) − g'(y)| ≤ 2^{1−θ} (C∇∇)^θ (C∇)^{1−θ} · t^{−(1+θ)/2} · Cf · |x−y|^θ`,

since `g'` obeys `‖g'‖∞ ≤ C∇ t^{−1/2} Cf` (committed gradient bound) and
`‖∂ₓ g'‖∞ ≤ C∇∇ t^{−1} Cf` (the named input), and
`(t^{−1/2})^{1−θ}(t^{−1})^θ = t^{−(1+θ)/2}`. -/
theorem neumannHeatGradient_Linf_to_Ctheta_of_second_deriv {t θ : ℝ} (ht : 0 < t)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {f : ℝ → ℝ} (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    {Cf Cgg : ℝ} (hf : ∀ y, |f y| ≤ Cf) (hCgg : 0 ≤ Cgg)
    (hsd : neumannHeatSecondDeriv_Linfty_bound t f Cf Cgg) (x y : ℝ) :
    |deriv (fun w : ℝ => intervalNeumannHeatSemigroup t f w) x
        - deriv (fun w : ℝ => intervalNeumannHeatSemigroup t f w) y|
      ≤ (2 : ℝ) ^ (1 - θ) * (Cgg ^ θ * gradSmoothingConst ^ (1 - θ))
          * t ^ (-((1 + θ) / 2) : ℝ) * Cf * |x - y| ^ θ := by
  classical
  obtain ⟨hsd_deriv, hsd_bound⟩ := hsd
  have hCf : 0 ≤ Cf := le_trans (abs_nonneg (f 0)) (hf 0)
  have hCgrad : 0 ≤ gradSmoothingConst := gradSmoothingConst_nonneg
  set gx : ℝ := deriv (fun w : ℝ => intervalNeumannHeatSemigroup t f w) x with hgx
  set gy : ℝ := deriv (fun w : ℝ => intervalNeumannHeatSemigroup t f w) y with hgy
  -- θ=0 leg: sup bound on g' (committed gradient bound), giving `|gx − gy| ≤ 2 A`
  -- with A := C∇ t^{−1/2} Cf.
  set A : ℝ := gradSmoothingConst * t ^ (-(1 / 2) : ℝ) * Cf with hA
  have hAnn : 0 ≤ A := by
    rw [hA]; have := Real.rpow_pos_of_pos ht (-(1 / 2) : ℝ); positivity
  have hgxle : |gx| ≤ A := by rw [hgx]; exact intervalNeumann_heat_gradient_bound ht hf_meas hf x
  have hgyle : |gy| ≤ A := by rw [hgy]; exact intervalNeumann_heat_gradient_bound ht hf_meas hf y
  have hval : |gx - gy| ≤ 2 * A := by
    calc |gx - gy| ≤ |gx| + |gy| := abs_sub _ _
      _ ≤ A + A := add_le_add hgxle hgyle
      _ = 2 * A := by ring
  -- θ=1 leg: Lipschitz from the named second-derivative bound via MVT.
  set B : ℝ := Cgg * t ^ (-(1 : ℝ)) * Cf with hB
  have htm1 : (0 : ℝ) < t ^ (-(1 : ℝ)) := Real.rpow_pos_of_pos ht _
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  set h : ℝ → ℝ := fun w : ℝ => deriv (fun w' : ℝ => intervalNeumannHeatSemigroup t f w') w
    with hh
  have hderiv : ∀ z ∈ (Set.univ : Set ℝ), HasDerivWithinAt h (deriv h z) Set.univ z := by
    intro z _; exact ((hsd_deriv z).differentiableAt.hasDerivAt).hasDerivWithinAt
  have hbound : ∀ z ∈ (Set.univ : Set ℝ), ‖deriv h z‖ ≤ B := by
    intro z _; rw [Real.norm_eq_abs, hB]; exact hsd_bound z
  have hconv : Convex ℝ (Set.univ : Set ℝ) := convex_univ
  have hmvt := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (Set.mem_univ y) (Set.mem_univ x)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  have hlip : |gx - gy| ≤ B * |x - y| := by
    have heq : h x - h y = gx - gy := by rw [hh, hgx, hgy]
    rw [heq] at hmvt; exact hmvt
  -- interpolate.
  set a : ℝ := 2 * A with ha
  set b : ℝ := B * |x - y| with hb
  have hann : 0 ≤ a := by rw [ha]; positivity
  have hbnn2 : 0 ≤ b := by rw [hb]; positivity
  have hmin : |gx - gy| ≤ min a b := le_min hval hlip
  have hinterp : min a b ≤ a ^ (1 - θ) * b ^ θ :=
    min_le_rpow_interp hann hbnn2 hθ0.le hθ1.le
  have hchain : |gx - gy| ≤ a ^ (1 - θ) * b ^ θ := le_trans hmin hinterp
  -- a^{1−θ} = 2^{1−θ} (C∇ t^{−1/2} Cf)^{1−θ}; b^θ = (C∇∇ t^{−1} Cf)^θ |x−y|^θ.
  have hapow : a ^ (1 - θ) = (2 : ℝ) ^ (1 - θ)
      * (gradSmoothingConst ^ (1 - θ) * t ^ (-(1 - θ) / 2 : ℝ) * Cf ^ (1 - θ)) := by
    have htA : (t ^ (-(1 / 2) : ℝ)) ^ (1 - θ) = t ^ (-(1 - θ) / 2 : ℝ) := by
      rw [← Real.rpow_mul ht.le]; congr 1; ring
    rw [ha, hA, Real.mul_rpow (by norm_num) hAnn,
        Real.mul_rpow (by positivity) hCf,
        Real.mul_rpow hCgrad (Real.rpow_pos_of_pos ht _).le, htA]
  have hbpow : b ^ θ = Cgg ^ θ * t ^ (-(θ : ℝ)) * Cf ^ θ * |x - y| ^ θ := by
    have htB : (t ^ (-(1 : ℝ))) ^ θ = t ^ (-(θ : ℝ)) := by
      rw [← Real.rpow_mul ht.le]; congr 1; ring
    rw [hb, hB, Real.mul_rpow hBnn (abs_nonneg _),
        Real.mul_rpow (by positivity) hCf,
        Real.mul_rpow hCgg htm1.le, htB]
  have hexp : t ^ (-(1 - θ) / 2 : ℝ) * t ^ (-(θ : ℝ)) = t ^ (-((1 + θ) / 2) : ℝ) := by
    rw [← Real.rpow_add ht]; congr 1; ring
  have hCfc : Cf ^ (1 - θ) * Cf ^ θ = Cf := by rw [← Real.rpow_add' hCf (by simp)]; simp
  have hfinal : a ^ (1 - θ) * b ^ θ
      = (2 : ℝ) ^ (1 - θ) * (Cgg ^ θ * gradSmoothingConst ^ (1 - θ))
          * t ^ (-((1 + θ) / 2) : ℝ) * Cf * |x - y| ^ θ := by
    rw [hapow, hbpow]
    rw [show (2 : ℝ) ^ (1 - θ)
          * (gradSmoothingConst ^ (1 - θ) * t ^ (-(1 - θ) / 2 : ℝ) * Cf ^ (1 - θ))
          * (Cgg ^ θ * t ^ (-(θ : ℝ)) * Cf ^ θ * |x - y| ^ θ)
        = (2 : ℝ) ^ (1 - θ) * (Cgg ^ θ * gradSmoothingConst ^ (1 - θ))
            * (t ^ (-(1 - θ) / 2 : ℝ) * t ^ (-(θ : ℝ)))
            * (Cf ^ (1 - θ) * Cf ^ θ) * |x - y| ^ θ by ring]
    rw [hexp, hCfc]
  rw [hfinal] at hchain
  exact hchain

/-- The committed second-derivative `L∞→L∞` smoothing constant `C∇∇ = 5√2/2`. -/
noncomputable def secondDerivSmoothingConst : ℝ := 5 * Real.sqrt 2 / 2

theorem secondDerivSmoothingConst_nonneg : 0 ≤ secondDerivSmoothingConst := by
  unfold secondDerivSmoothingConst; positivity

/-- **The named second-derivative input, now PROVED (UNCONDITIONAL).**  The
interval-Neumann heat semigroup obeys the `t^{−1}` second-derivative sup bound
`‖∂ₓₓS(t)f‖∞ ≤ (5√2/2)·t^{−1}·Cf`, discharging `neumannHeatSecondDeriv_Linfty_bound`.

Both parts come from the committed PDE second-derivative layer: the
`HasDerivAt`-of-`∂ₓS(t)f` part from `intervalFullSemigroupOperator_hasDerivAt_deriv_fst`
and the sup bound from `intervalFullSemigroupOperator_secondDeriv_Linfty_pointwise_inv_t`. -/
theorem intervalNeumann_heat_secondDeriv_bound {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    {Cf : ℝ} (hf : ∀ y, |f y| ≤ Cf) :
    neumannHeatSecondDeriv_Linfty_bound t f Cf secondDerivSmoothingConst := by
  unfold neumannHeatSecondDeriv_Linfty_bound secondDerivSmoothingConst
  refine ⟨fun z => ?_, fun z => ?_⟩
  · have h := intervalFullSemigroupOperator_hasDerivAt_deriv_fst ht hf_meas hf z
    exact h.deriv ▸ h
  · exact intervalFullSemigroupOperator_secondDeriv_Linfty_pointwise_inv_t ht hf_meas hf z

/-- **Pass-1 GRADIENT Hölder-smoothing bound (`L∞ → C^θ` for `∂ₓS(t)f`),
UNCONDITIONAL.**  Discharges the named second-derivative input of
`neumannHeatGradient_Linf_to_Ctheta_of_second_deriv` via the committed PDE
second-derivative layer (`intervalNeumann_heat_secondDeriv_bound`, `C∇∇ = 5√2/2`):

  `|∂ₓS(t)f x − ∂ₓS(t)f y|
      ≤ 2^{1−θ} ((5√2/2)^θ C∇^{1−θ}) · t^{−(1+θ)/2} · Cf · |x−y|^θ`. -/
theorem neumannHeatGradient_Linf_to_Ctheta {t θ : ℝ} (ht : 0 < t)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {f : ℝ → ℝ} (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    {Cf : ℝ} (hf : ∀ y, |f y| ≤ Cf) (x y : ℝ) :
    |deriv (fun w : ℝ => intervalNeumannHeatSemigroup t f w) x
        - deriv (fun w : ℝ => intervalNeumannHeatSemigroup t f w) y|
      ≤ (2 : ℝ) ^ (1 - θ) * (secondDerivSmoothingConst ^ θ * gradSmoothingConst ^ (1 - θ))
          * t ^ (-((1 + θ) / 2) : ℝ) * Cf * |x - y| ^ θ :=
  neumannHeatGradient_Linf_to_Ctheta_of_second_deriv ht hθ0 hθ1 hf_meas hf
    secondDerivSmoothingConst_nonneg
    (intervalNeumann_heat_secondDeriv_bound ht hf_meas hf) x y

/-! ## Mild-representation Hölder bootstrap: the integrability fact -/

/-- **Integrability fact the mild Hölder bootstrap consumes.**

The Duhamel leg of the mild representation, after applying `neumannHeat_Linf_to_Ctheta`
slice-by-slice, produces a time integrand `(t − s)^{−θ/2}` whose integrability on
`[0,t]` (`θ < 2`, in particular `0 < θ < 1`) is what makes the bootstrap converge:

  `∫₀ᵗ (t − s)^{−θ/2} ds = (2 / (2 − θ)) · t^{(2 − θ)/2} < ∞`.

This is the convergence behind `mild_orderBox_positiveTime_holder` (below). -/
theorem duhamel_holder_time_integrand_integrable {t θ : ℝ} (_ht : 0 < t)
    (_hθ0 : 0 < θ) (hθ2 : θ < 2) :
    IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(θ / 2) : ℝ)) volume 0 t := by
  have hr : (-1 : ℝ) < -(θ / 2) := by linarith
  have hcomp : IntervalIntegrable (fun s : ℝ => s ^ (-(θ / 2) : ℝ)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t) hr
  have hshift := hcomp.comp_sub_left t
  simp only [sub_zero, sub_self] at hshift
  exact hshift.symm

/-- **Mild-bootstrap target (documented statement).**

  `mild_orderBox_positiveTime_holder` : for the mild fixed point `u` of the
  interval-Neumann chemotaxis Duhamel equation and any `τ > 0`, the solution at
  times `t ≥ τ` lies in `C^θ` for `0 < θ < 1`, with modulus

    `|u(t,x) − u(t,y)| ≤ Cθ(τ) · |x − y|^θ`.

  PROOF SKELETON (all bricks PROVED above except the orderBox plumbing):
  apply `neumannHeat_Linf_to_Ctheta` to (i) the `S(t)u₀` leg directly, and (ii)
  each Duhamel slice `S(t−s)[source(s)]`, then integrate the resulting per-slice
  Hölder constants `(t−s)^{−θ/2}` against `duhamel_holder_time_integrand_integrable`.
  The remaining work is purely the orderBox/mild-representation bookkeeping
  (`chemMildLocal` / `…orderBox_exists` chain), NOT new estimate theory.  Recorded
  here as the next consumer; the two estimate inputs it needs are
  `neumannHeat_Linf_to_Ctheta` and `duhamel_holder_time_integrand_integrable`,
  both PROVED in this file. -/
def mild_orderBox_positiveTime_holder_inputs_available : Prop :=
  (∀ (t θ : ℝ) (f : ℝ → ℝ) (Cf : ℝ), 0 < t → 0 < θ → θ < 1 →
      AEStronglyMeasurable f (intervalMeasure 1) → (∀ y, |f y| ≤ Cf) →
      ∀ x y : ℝ,
        |intervalNeumannHeatSemigroup t f x - intervalNeumannHeatSemigroup t f y|
          ≤ (2 : ℝ) ^ (1 - θ) * gradSmoothingConst ^ θ
              * t ^ (-(θ / 2) : ℝ) * Cf * |x - y| ^ θ)
  ∧ (∀ (t θ : ℝ), 0 < t → 0 < θ → θ < 2 →
      IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(θ / 2) : ℝ)) volume 0 t)

theorem mild_orderBox_positiveTime_holder_inputs :
    mild_orderBox_positiveTime_holder_inputs_available :=
  ⟨fun _ _ _ _ ht hθ0 hθ1 hf_meas hf x y =>
      neumannHeat_Linf_to_Ctheta ht hθ0 hθ1 hf_meas hf x y,
   fun _ _ ht hθ0 hθ2 => duhamel_holder_time_integrand_integrable ht hθ0 hθ2⟩

end ShenWork.Paper2
