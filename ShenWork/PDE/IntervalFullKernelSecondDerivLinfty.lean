/-
  ShenWork/PDE/IntervalFullKernelSecondDerivLinfty.lean

  **Second-derivative `L∞→L∞` estimate for the interval-Neumann heat semigroup.**

  TARGET (one derivative above the committed gradient bound):

    `|∂ₓₓ S(t) f (x)| ≤ Cgg · t^(−1) · ‖f‖∞`,   uniformly in `x`,

  for the interval-Neumann heat semigroup `S(t) = intervalFullSemigroupOperator t`
  on `[0,1]` and bounded measurable data `f` (`|f| ≤ Cf`).  This is the genuine
  remaining PDE input for the chemotaxis Hölder bootstrap: it unconditionalizes
  `neumannHeatGradient_Linf_to_Ctheta` in `ShenWork/Paper2/ChemMildHolder.lean`.

  ## Route (mirror of the committed GRADIENT construction, one derivative up)

  The whole-line heat kernel's second `x`-derivative is
    `∂ₓₓ heat = (1/(2t))·(x²/(2t) − 1)·heat`,
  whose `L¹` mass scales as `t^(−1)` (each spatial derivative costs `t^(−1/2)`).
  Mirror the gradient layer (`IntervalFullKernelGradientLinfty.lean`):

    * `abs_secondDeriv_heatKernel_le` — pointwise `t^(−3/2)·exp(−x²/(8t))` bound on
      `∂ₓₓ heat` (analogue of `abs_deriv_heatKernel_le`); quadratic prefactor
      absorbed by `s·exp(−s) ≤ 1` (`real_mul_exp_neg_le_one`).
    * `hasDerivAt_deriv_heatKernel_lattice_tsum` — termwise second differentiation
      of the lattice heat sum (analogue of `hasDerivAt_heatKernel_lattice_tsum`).
    * `hasDerivAt_deriv_intervalNeumannFullKernel_fst` — the full kernel's second
      `x`-derivative as a two-tsum series (analogue of `hasDerivAt_…_fst`).
    * `intervalNeumannFullKernel_secondDeriv_abs_interval_integral_le` — the `t^(−1)`
      `L¹` tiling bound (analogue of `…_deriv_abs_interval_integral_le`), here via a
      direct summable window majorant (no Poisson identity needed).
    * `intervalFullSemigroupOperator_hasDerivAt_deriv_fst` — the second-order DUI,
      differentiating the committed first-derivative integral representation once
      more (analogue of `intervalFullSemigroupOperator_hasDerivAt_fst`).
    * `intervalFullSemigroupOperator_secondDeriv_Linfty_pointwise_inv_t` — the
      `L∞→L∞` second-derivative bound (analogue of `…_deriv_Linfty_pointwise_sqrt_t`).

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.PDE.IntervalFullKernelGradientLinfty

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalNeumannFullKernel

open ShenWork.IntervalDomain

/-! ## Whole-line heat kernel: the second `x`-derivative -/

/-- **Second `x`-derivative of the heat kernel.**  For `t > 0`,
`deriv (deriv heatKernel t) x = (1/(2t))·(x²/(2t) − 1)·heatKernel t x`. -/
theorem heatKernel_secondDeriv_hasDerivAt {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
      ((1 / (2 * t)) * (x ^ 2 / (2 * t) - 1) * heatKernel t x) x := by
  have htne : t ≠ 0 := ne_of_gt ht
  -- `deriv heatKernel = fun u ↦ -(u/(2t))·heatKernel t u`.
  have hg : (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
      = fun u : ℝ => -(u / (2 * t)) * heatKernel t u := by
    funext u; rw [deriv_heatKernel ht]
  rw [hg]
  -- product rule for `u ↦ -(u/(2t)) · heatKernel t u`.
  have hlin : HasDerivAt (fun u : ℝ => -(u / (2 * t))) (-(1 / (2 * t))) x := by
    have h0 : HasDerivAt (fun u : ℝ => u / (2 * t)) (1 / (2 * t)) x := by
      simpa using (hasDerivAt_id x).div_const (2 * t)
    simpa using h0.neg
  have hprod := hlin.mul (heatKernel_hasDerivAt ht x)
  convert hprod using 1
  field_simp
  ring

/-- `deriv (deriv heatKernel t)` evaluated: the closed form. -/
theorem deriv_deriv_heatKernel {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) x
      = (1 / (2 * t)) * (x ^ 2 / (2 * t) - 1) * heatKernel t x :=
  (heatKernel_secondDeriv_hasDerivAt ht x).deriv

/-- The pointwise heat-Hessian bound constant `5·(1/(2t))·(4πt)^{−1/2}` (shape
`t^(−3/2)`). -/
noncomputable def heatHessPointwiseBound (t : ℝ) : ℝ :=
  5 * ((1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t)))

theorem heatHessPointwiseBound_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ heatHessPointwiseBound t := by unfold heatHessPointwiseBound; positivity

/-- **Pointwise Gaussian-Hessian bound.**  For `t > 0`,
`|∂ₓₓ heat t x| ≤ heatHessPointwiseBound t · exp(−x²/(8t))`.

The quadratic prefactor `|x²/(2t) − 1| ≤ x²/(2t) + 1` is absorbed into the
*half-rate* Gaussian `exp(−x²/(8t))` via `(x²/(8t))·exp(−x²/(8t)) ≤ 1`
(`real_mul_exp_neg_le_one`), giving `(x²/(2t)+1)·exp(−x²/(8t)) ≤ 5`.  The surviving
half-rate Gaussian `exp(−x²/(8t)) = exp(−x²/(4·2t))` is what makes the second
derivative lattice summable. -/
theorem abs_secondDeriv_heatKernel_le {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) x|
      ≤ heatHessPointwiseBound t * Real.exp (-x ^ 2 / (4 * (2 * t))) := by
  have h2t : (0 : ℝ) < 2 * t := by linarith
  have htne : t ≠ 0 := ne_of_gt ht
  -- absorb the quadratic factor into one half-rate Gaussian: `(x²/(2t)+1)·E ≤ 5·E`
  -- where `E = exp(−x²/(8t))`.
  have hquad : (x ^ 2 / (2 * t) + 1) * Real.exp (-x ^ 2 / (4 * (2 * t))) ≤ 5 := by
    have hs : 0 ≤ x ^ 2 / (4 * (2 * t)) := by positivity
    have hse : (x ^ 2 / (4 * (2 * t))) * Real.exp (-(x ^ 2 / (4 * (2 * t)))) ≤ 1 :=
      real_mul_exp_neg_le_one hs
    have hE1 : Real.exp (-x ^ 2 / (4 * (2 * t))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        apply div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg x]) (by positivity))
    have hkey : x ^ 2 / (2 * t) * Real.exp (-x ^ 2 / (4 * (2 * t))) ≤ 4 := by
      have hrw : x ^ 2 / (2 * t) * Real.exp (-x ^ 2 / (4 * (2 * t)))
          = 4 * ((x ^ 2 / (4 * (2 * t))) * Real.exp (-(x ^ 2 / (4 * (2 * t))))) := by
        rw [show -(x ^ 2 / (4 * (2 * t))) = -x ^ 2 / (4 * (2 * t)) by ring]
        field_simp
      rw [hrw]; nlinarith [hse]
    have hE0 : (0 : ℝ) < Real.exp (-x ^ 2 / (4 * (2 * t))) := Real.exp_pos _
    nlinarith [hkey, hE1, hE0]
  -- the half-rate split of the heat-rate Gaussian inside `heatKernel`.
  have hsplit : Real.exp (-x ^ 2 / (4 * t))
      = Real.exp (-x ^ 2 / (4 * (2 * t))) * Real.exp (-x ^ 2 / (4 * (2 * t))) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [deriv_deriv_heatKernel ht]
  unfold heatKernel heatHessPointwiseBound
  have hcoeff : 0 ≤ (1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t)) := by positivity
  have habs : |(1 / (2 * t)) * (x ^ 2 / (2 * t) - 1)
        * (1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-x ^ 2 / (4 * t)))|
      = (1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))
        * (|x ^ 2 / (2 * t) - 1| * Real.exp (-x ^ 2 / (4 * t))) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (2 * t)),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / Real.sqrt (4 * Real.pi * t)),
      abs_of_pos (Real.exp_pos _)]
    ring
  rw [habs]
  have hxsq : 0 ≤ x ^ 2 / (2 * t) := by positivity
  have htri : |x ^ 2 / (2 * t) - 1| ≤ x ^ 2 / (2 * t) + 1 := by
    rw [abs_le]; constructor <;> nlinarith [hxsq]
  calc (1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))
        * (|x ^ 2 / (2 * t) - 1| * Real.exp (-x ^ 2 / (4 * t)))
      ≤ (1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))
        * ((x ^ 2 / (2 * t) + 1) * Real.exp (-x ^ 2 / (4 * t))) := by
        refine mul_le_mul_of_nonneg_left ?_ hcoeff
        exact mul_le_mul_of_nonneg_right htri (Real.exp_pos _).le
    _ = (1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))
        * ((x ^ 2 / (2 * t) + 1) * Real.exp (-x ^ 2 / (4 * (2 * t)))
            * Real.exp (-x ^ 2 / (4 * (2 * t)))) := by rw [hsplit]; ring
    _ ≤ (1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))
        * (5 * Real.exp (-x ^ 2 / (4 * (2 * t)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hcoeff
        rw [← mul_assoc]
        have := mul_le_mul_of_nonneg_right hquad (Real.exp_pos (-x ^ 2 / (4 * (2 * t)))).le
        convert this using 2 <;> ring
    _ = 5 * ((1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t)))
        * Real.exp (-x ^ 2 / (4 * (2 * t))) := by ring

/-- **Hessian lattice summability.**  For `t > 0` the second-derivative lattice
`k ↦ ∂ₓₓ heat (z + 2k)` is summable (dominated by `heatHessPointwiseBound t ·
exp(−(z+2k)²/(8t))`, lattice sum `latticeExpSummable (2t)`). -/
theorem latticeGaussianHessSummable {t : ℝ} (ht : 0 < t) (z : ℝ) :
    Summable (fun k : ℤ =>
      deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (z + 2 * (k : ℝ))) := by
  have h2t : (0 : ℝ) < 2 * t := by linarith
  apply Summable.of_abs
  exact ((latticeExpSummable h2t z).mul_left (heatHessPointwiseBound t)).of_nonneg_of_le
    (fun k => abs_nonneg _) (fun k => abs_secondDeriv_heatKernel_le ht _)

/-- **Termwise second differentiation of the lattice heat sum.**  For `t > 0` and
any shift `b`, the first-derivative lattice `w ↦ ∑ₖ ∂ₓheat(w+b+2k)` is
differentiable in `w`, with derivative the termwise lattice sum of the heat-kernel
*second* derivatives.  Same `hasDerivAt_tsum_of_isPreconnected` engine as
`hasDerivAt_heatKernel_lattice_tsum`, with the half-rate-Gaussian majorant
`heatHessPointwiseBound t · exp(1/(8t)) · exp(−(x+b+2k)²/(16t))`. -/
theorem hasDerivAt_deriv_heatKernel_lattice_tsum {t : ℝ} (ht : 0 < t) (b x : ℝ) :
    HasDerivAt
      (fun w : ℝ => ∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (w + b + 2 * (k : ℝ)))
      (∑' k : ℤ,
        deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (x + b + 2 * (k : ℝ))) x := by
  have h4t : (0 : ℝ) < 4 * t := by linarith
  set u : ℤ → ℝ := fun k =>
    heatHessPointwiseBound t * Real.exp (1 / (4 * (2 * t)))
      * Real.exp (-(x + b + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t))) with hu_def
  have hu : Summable u :=
    (latticeExpSummable h4t (x + b)).mul_left
      (heatHessPointwiseBound t * Real.exp (1 / (4 * (2 * t))))
  -- per-term derivative (chain rule through the affine shift `w ↦ w+b+2k`).
  have hg : ∀ (k : ℤ) (w : ℝ), w ∈ Set.Ioo (x - 1) (x + 1) →
      HasDerivAt (fun w : ℝ => deriv (fun u : ℝ => heatKernel t u) (w + b + 2 * (k : ℝ)))
        (deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (w + b + 2 * (k : ℝ))) w := by
    intro k w _
    have hinner : HasDerivAt (fun w : ℝ => w + b + 2 * (k : ℝ)) 1 w := by
      simpa using ((hasDerivAt_id w).add_const b).add_const (2 * (k : ℝ))
    have hcomp := (heatKernel_secondDeriv_hasDerivAt ht (w + b + 2 * (k : ℝ))).comp w hinner
    rw [deriv_deriv_heatKernel ht]
    simpa using hcomp
  -- uniform second-derivative bound: pointwise Hessian bound + Young inequality.
  have hg' : ∀ (k : ℤ) (w : ℝ), w ∈ Set.Ioo (x - 1) (x + 1) →
      ‖deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (w + b + 2 * (k : ℝ))‖
        ≤ u k := by
    intro k w hw
    rw [Real.norm_eq_abs]
    refine (abs_secondDeriv_heatKernel_le ht (w + b + 2 * (k : ℝ))).trans ?_
    rw [hu_def]
    have hP : (1 / 2) * (x + b + 2 * (k : ℝ)) ^ 2 - 1 ≤ (w + b + 2 * (k : ℝ)) ^ 2 := by
      have hB : (w - x) ^ 2 ≤ 1 := by nlinarith [hw.1, hw.2]
      nlinarith [sq_nonneg (2 * w - x + b + 2 * (k : ℝ)), hB]
    have hexp : Real.exp (-(w + b + 2 * (k : ℝ)) ^ 2 / (4 * (2 * t)))
        ≤ Real.exp (1 / (4 * (2 * t)))
          * Real.exp (-(x + b + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have htne : t ≠ 0 := ne_of_gt ht
      have e1 : -(w + b + 2 * (k : ℝ)) ^ 2 / (4 * (2 * t))
          = (-2 * (w + b + 2 * (k : ℝ)) ^ 2) / (4 * (4 * t)) := by
        field_simp; ring
      have e2 : 1 / (4 * (2 * t)) + -(x + b + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t))
          = (2 - (x + b + 2 * (k : ℝ)) ^ 2) / (4 * (4 * t)) := by
        field_simp; ring
      rw [e1, e2]
      apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 4 * (4 * t))).mpr
      nlinarith [hP]
    calc heatHessPointwiseBound t
            * Real.exp (-(w + b + 2 * (k : ℝ)) ^ 2 / (4 * (2 * t)))
        ≤ heatHessPointwiseBound t * (Real.exp (1 / (4 * (2 * t)))
            * Real.exp (-(x + b + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t)))) :=
          mul_le_mul_of_nonneg_left hexp (heatHessPointwiseBound_nonneg ht)
      _ = heatHessPointwiseBound t * Real.exp (1 / (4 * (2 * t)))
            * Real.exp (-(x + b + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t))) := by ring
  have hg0 : Summable
      (fun k : ℤ => deriv (fun u : ℝ => heatKernel t u) (x + b + 2 * (k : ℝ))) := by
    have := latticeGaussianGradSummable ht (x + b)
    simpa using this
  exact hasDerivAt_tsum_of_isPreconnected (u := u) (t := Set.Ioo (x - 1) (x + 1))
    (g := fun (k : ℤ) (w : ℝ) => deriv (fun u : ℝ => heatKernel t u) (w + b + 2 * (k : ℝ)))
    (g' := fun (k : ℤ) (w : ℝ) =>
      deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (w + b + 2 * (k : ℝ)))
    hu isOpen_Ioo (convex_Ioo _ _).isPreconnected hg hg'
    (y₀ := x) (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩) hg0
    (y := x) (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩)

/-! ## The full kernel: second `x`-derivative as a lattice series -/

/-- **`∂ₓₓ` of the full periodised Neumann kernel as a two-tsum series.**  For
`t > 0`, `y ↦ ∂ₓ K_full(t,·,y)` (the committed first-derivative tsum) is again
differentiable in its first argument, with derivative the sum of the two
termwise-second-differentiated lattice series.  Differentiates the committed
first-derivative representation `hasDerivAt_intervalNeumannFullKernel_fst` once
more, via `hasDerivAt_deriv_heatKernel_lattice_tsum` (shifts `b = −y`, `b = y`). -/
theorem hasDerivAt_deriv_intervalNeumannFullKernel_fst {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (fun x : ℝ => deriv (fun x : ℝ => intervalNeumannFullKernel t x y) x)
      ((∑' k : ℤ,
          deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (x - y + 2 * (k : ℝ)))
        + (∑' k : ℤ,
          deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (x + y + 2 * (k : ℝ)))) x := by
  -- the committed first-derivative as the two-tsum function of `x`.
  have hfun : (fun x : ℝ => deriv (fun x : ℝ => intervalNeumannFullKernel t x y) x)
      = fun w : ℝ => (∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (w - y + 2 * (k : ℝ)))
          + (∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (w + y + 2 * (k : ℝ))) := by
    funext w; exact (hasDerivAt_intervalNeumannFullKernel_fst ht w y).deriv
  rw [hfun]
  have hL : HasDerivAt
      (fun w : ℝ => ∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (w - y + 2 * (k : ℝ)))
      (∑' k : ℤ,
        deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (x - y + 2 * (k : ℝ))) x := by
    simpa only [sub_eq_add_neg] using hasDerivAt_deriv_heatKernel_lattice_tsum ht (-y) x
  have hR : HasDerivAt
      (fun w : ℝ => ∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (w + y + 2 * (k : ℝ)))
      (∑' k : ℤ,
        deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (x + y + 2 * (k : ℝ))) x :=
    hasDerivAt_deriv_heatKernel_lattice_tsum ht y x
  exact hL.add hR

/-- Pointwise integrand bound: `|∂ₓₓ K_full(t,x,y)|` is dominated by the termwise
absolute second-derivative lattice sum. -/
theorem abs_secondDeriv_intervalNeumannFullKernel_fst_le {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    |deriv (fun x : ℝ => deriv (fun x : ℝ => intervalNeumannFullKernel t x y) x) x|
      ≤ ∑' k : ℤ,
          (|deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (x - y + 2 * (k : ℝ))|
            + |deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u)
                (x + y + 2 * (k : ℝ))|) := by
  rw [(hasDerivAt_deriv_intervalNeumannFullKernel_fst ht x y).deriv]
  have hsumA : Summable
      (fun k : ℤ => |deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u)
        (x - y + 2 * (k : ℝ))|) :=
    summable_abs_iff.mpr (latticeGaussianHessSummable ht (x - y))
  have hsumB : Summable
      (fun k : ℤ => |deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u)
        (x + y + 2 * (k : ℝ))|) :=
    summable_abs_iff.mpr (latticeGaussianHessSummable ht (x + y))
  have hA : |∑' k : ℤ,
        deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (x - y + 2 * (k : ℝ))|
      ≤ ∑' k : ℤ,
        |deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (x - y + 2 * (k : ℝ))| := by
    simpa [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun k : ℤ =>
        deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (x - y + 2 * (k : ℝ)))
        (by simpa [Real.norm_eq_abs] using hsumA)
  have hB : |∑' k : ℤ,
        deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (x + y + 2 * (k : ℝ))|
      ≤ ∑' k : ℤ,
        |deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (x + y + 2 * (k : ℝ))| := by
    simpa [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun k : ℤ =>
        deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (x + y + 2 * (k : ℝ)))
        (by simpa [Real.norm_eq_abs] using hsumB)
  calc |(∑' k : ℤ,
            deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (x - y + 2 * (k : ℝ)))
          + (∑' k : ℤ,
            deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (x + y + 2 * (k : ℝ)))|
      ≤ |∑' k : ℤ,
            deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (x - y + 2 * (k : ℝ))|
        + |∑' k : ℤ,
            deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (x + y + 2 * (k : ℝ))| :=
        abs_add_le _ _
    _ ≤ (∑' k : ℤ,
            |deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (x - y + 2 * (k : ℝ))|)
          + ∑' k : ℤ,
            |deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (x + y + 2 * (k : ℝ))| :=
        add_le_add hA hB
    _ = ∑' k : ℤ,
          (|deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (x - y + 2 * (k : ℝ))|
            + |deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (x + y + 2 * (k : ℝ))|) :=
        (Summable.tsum_add hsumA hsumB).symm

/-! ## The second-derivative kernel `L¹` bound `∫₀¹|∂ₓₓK| ≤ Cgg·t⁻¹` -/

/-- The Gaussian majorant `w ↦ heatHessPointwiseBound t · exp(−(1/(8t))·w²)` is
integrable; it dominates `|∂ₓₓ heat t ·|` (`abs_secondDeriv_heatKernel_le`). -/
theorem heatHessGaussianMajorant_integrable {t : ℝ} (ht : 0 < t) :
    MeasureTheory.Integrable
      (fun w : ℝ => heatHessPointwiseBound t * Real.exp (-(1 / (4 * (2 * t))) * w ^ 2)) := by
  have hb : 0 < 1 / (4 * (2 * t)) := by positivity
  exact (integrable_exp_neg_mul_sq hb).const_mul _

/-- `w ↦ ∂ₓₓ heat t w` is continuous (closed form `(1/(2t))(w²/(2t)−1)·heat`). -/
theorem continuous_secondDeriv_heatKernel {t : ℝ} (ht : 0 < t) :
    Continuous (fun w : ℝ => deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) w) := by
  have heq : (fun w : ℝ => deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) w)
      = fun w : ℝ => (1 / (2 * t)) * (w ^ 2 / (2 * t) - 1) * heatKernel t w := by
    funext w; rw [deriv_deriv_heatKernel ht]
  rw [heq]; unfold heatKernel; fun_prop

/-- `∂ₓₓ heat` is abs-integrable on `ℝ` (dominated by the integrable Gaussian
majorant via `abs_secondDeriv_heatKernel_le`). -/
theorem secondDeriv_heatKernel_abs_integrable {t : ℝ} (ht : 0 < t) :
    MeasureTheory.Integrable
      (fun w : ℝ => |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) w|) := by
  refine (heatHessGaussianMajorant_integrable ht).mono'
    (continuous_secondDeriv_heatKernel ht).abs.aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_abs]
  rw [show -(1 / (4 * (2 * t))) * w ^ 2 = -w ^ 2 / (4 * (2 * t)) by ring]
  exact abs_secondDeriv_heatKernel_le ht w

/-- **Whole-line second-derivative `L¹` mass bound `≤ (5√2/2)·t⁻¹`.**  From the
pointwise half-rate-Gaussian bound and `∫_ℝ exp(−w²/(8t)) = √(8πt)`:
`∫_ℝ|∂ₓₓheat| ≤ heatHessPointwiseBound t · √(8πt) = (5√2/2)·t⁻¹`. -/
theorem secondDeriv_heatKernel_abs_integral_le {t : ℝ} (ht : 0 < t) :
    (∫ w : ℝ, |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) w|)
      ≤ (5 * Real.sqrt 2 / 2) * t ^ (-(1 : ℝ)) := by
  have hb : 0 < 1 / (4 * (2 * t)) := by positivity
  have hbnd : (∫ w : ℝ, |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) w|)
      ≤ ∫ w : ℝ, heatHessPointwiseBound t * Real.exp (-(1 / (4 * (2 * t))) * w ^ 2) := by
    refine MeasureTheory.integral_mono (secondDeriv_heatKernel_abs_integrable ht)
      (heatHessGaussianMajorant_integrable ht) (fun w => ?_)
    rw [show -(1 / (4 * (2 * t))) * w ^ 2 = -w ^ 2 / (4 * (2 * t)) by ring]
    exact abs_secondDeriv_heatKernel_le ht w
  refine hbnd.trans (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, integral_gaussian (1 / (4 * (2 * t)))]
  -- `√(π/(1/(8t))) = √(8πt)`; collapse against `heatHessPointwiseBound`.
  unfold heatHessPointwiseBound
  have htne : t ≠ 0 := ne_of_gt ht
  have hsπt : Real.sqrt (4 * Real.pi * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have he1 : Real.sqrt (Real.pi / (1 / (4 * (2 * t))))
      = Real.sqrt (4 * (2 * t)) * Real.sqrt Real.pi := by
    rw [show Real.pi / (1 / (4 * (2 * t))) = (4 * (2 * t)) * Real.pi by field_simp,
      Real.sqrt_mul (by positivity)]
  have hrpow : t ^ (-(1 : ℝ)) = t⁻¹ := by rw [Real.rpow_neg_one]
  rw [he1, hrpow]
  -- `5·(1/(2t))·(1/√(4πt))·(√(8t)·√π) = (5√2/2)·t⁻¹`.
  have h8 : Real.sqrt (4 * (2 * t)) = 2 * Real.sqrt 2 * Real.sqrt t := by
    rw [show (4 * (2 * t) : ℝ) = (2 : ℝ) ^ 2 * (2 * t) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num), Real.sqrt_mul (by norm_num), ← mul_assoc]
  have h4 : Real.sqrt (4 * Real.pi * t) = 2 * Real.sqrt Real.pi * Real.sqrt t := by
    rw [show (4 * Real.pi * t : ℝ) = (2 : ℝ) ^ 2 * (Real.pi * t) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num), Real.sqrt_mul Real.pi_pos.le,
      ← mul_assoc]
  rw [h8, h4]
  have hsπ : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hst : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht)
  field_simp

/-- **Cell-integral summability for `|∂ₓₓheat|`.**  The reflected+direct `[0,1]`
heat-Hessian `L¹` masses are summable over the lattice (each pair equals the mass
over one period-`2` cell, `cell_integral_eq`; cell masses sum by countable
additivity of the integrable `|∂ₓₓheat|`). -/
theorem summable_cell_heatHess_interval_integral {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable (fun k : ℤ =>
        (∫ y in (0 : ℝ)..1,
          |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x - y + 2 * (k : ℝ))|)
          + (∫ y in (0 : ℝ)..1,
            |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
              (x + y + 2 * (k : ℝ))|)) := by
  have hg : Integrable
      (fun w : ℝ => |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) w|) :=
    secondDeriv_heatKernel_abs_integrable ht
  have hint : IntegrableOn
      (fun w : ℝ => |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) w|)
      (⋃ k : ℤ, Set.Ioc ((x - 1) + 2 * (k : ℝ)) ((x - 1) + 2 * (k : ℝ) + 2)) := by
    rw [ShenWork.iUnion_Ioc_offset_eq_univ]; exact hg.integrableOn
  have hsum := (hasSum_integral_iUnion (fun k : ℤ => measurableSet_Ioc)
    (ShenWork.pairwise_disjoint_Ioc_offset (x - 1)) hint).summable
  refine hsum.congr (fun k => ?_)
  have hset : Set.Ioc ((x - 1) + 2 * (k : ℝ)) ((x - 1) + 2 * (k : ℝ) + 2)
      = Set.Ioc (x + 2 * (k : ℝ) - 1) (x + 2 * (k : ℝ) + 1) := by congr 1 <;> ring
  rw [hset]
  exact (ShenWork.cell_integral_eq hg x k).symm

/-- **Continuity of `y ↦ ∂ₓₓ K_full(t,x,y)` on `[0,1]`.**  Each lattice second
derivative is continuous in `y`; the uniform majorant on `[0,1]` is the summable
`2·heatHessWindowBound`-style bound from `abs_secondDeriv_heatKernel_le` (radius-1
window).  Built like `continuousOn_deriv_intervalNeumannFullKernel_fst`. -/
theorem continuousOn_secondDeriv_intervalNeumannFullKernel_fst {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ContinuousOn
      (fun y : ℝ => deriv (fun x : ℝ => deriv (fun x : ℝ => intervalNeumannFullKernel t x y) x) x)
      (Set.Icc 0 1) := by
  have hcd := continuous_secondDeriv_heatKernel ht
  have hfun :
      (fun y : ℝ => deriv (fun x : ℝ => deriv (fun x : ℝ => intervalNeumannFullKernel t x y) x) x)
      = fun y : ℝ =>
          (∑' k : ℤ,
            deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x - y + 2 * (k : ℝ)))
          + (∑' k : ℤ,
            deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x + y + 2 * (k : ℝ))) := by
    funext y; exact (hasDerivAt_deriv_intervalNeumannFullKernel_fst ht x y).deriv
  rw [hfun]
  set u : ℤ → ℝ := fun k =>
    heatHessPointwiseBound t * Real.exp (1 / (4 * (2 * t)))
      * Real.exp (-(x + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t))) with hu_def
  have h4t : (0 : ℝ) < 4 * t := by linarith
  have hu : Summable u :=
    (latticeExpSummable h4t x).mul_left
      (heatHessPointwiseBound t * Real.exp (1 / (4 * (2 * t))))
  -- termwise bound on `[0,1]`: `|∂ₓₓheat(x±y+2k)| ≤ u k` (radius-1 Young slack).
  have hbnd : ∀ (s : ℝ), |s| ≤ (1 : ℝ) → ∀ k : ℤ,
      |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x + s + 2 * (k : ℝ))| ≤ u k := by
    intro s hs k
    refine (abs_secondDeriv_heatKernel_le ht (x + s + 2 * (k : ℝ))).trans ?_
    rw [hu_def]
    have hsb := abs_le.mp hs
    have hP : (1 / 2) * (x + 2 * (k : ℝ)) ^ 2 - 1 ≤ (x + s + 2 * (k : ℝ)) ^ 2 := by
      have hs2 : s ^ 2 ≤ 1 := by nlinarith [hsb.1, hsb.2]
      nlinarith [sq_nonneg (x + 2 * s + 2 * (k : ℝ)), hs2]
    have hexp : Real.exp (-(x + s + 2 * (k : ℝ)) ^ 2 / (4 * (2 * t)))
        ≤ Real.exp (1 / (4 * (2 * t)))
          * Real.exp (-(x + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have htne : t ≠ 0 := ne_of_gt ht
      have e1 : -(x + s + 2 * (k : ℝ)) ^ 2 / (4 * (2 * t))
          = (-2 * (x + s + 2 * (k : ℝ)) ^ 2) / (4 * (4 * t)) := by field_simp; ring
      have e2 : 1 / (4 * (2 * t)) + -(x + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t))
          = (2 - (x + 2 * (k : ℝ)) ^ 2) / (4 * (4 * t)) := by field_simp; ring
      rw [e1, e2]
      apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 4 * (4 * t))).mpr
      nlinarith [hP]
    calc heatHessPointwiseBound t * Real.exp (-(x + s + 2 * (k : ℝ)) ^ 2 / (4 * (2 * t)))
        ≤ heatHessPointwiseBound t * (Real.exp (1 / (4 * (2 * t)))
            * Real.exp (-(x + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t)))) :=
          mul_le_mul_of_nonneg_left hexp (heatHessPointwiseBound_nonneg ht)
      _ = heatHessPointwiseBound t * Real.exp (1 / (4 * (2 * t)))
            * Real.exp (-(x + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t))) := by ring
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_tsum (fun k => (hcd.comp (by fun_prop)).continuousOn) hu (fun k y hy => ?_)
    rw [Real.norm_eq_abs, show x - y + 2 * (k : ℝ) = x + (-y) + 2 * (k : ℝ) by ring]
    exact hbnd (-y) (by rw [abs_neg]; exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩) k
  · refine continuousOn_tsum (fun k => (hcd.comp (by fun_prop)).continuousOn) hu (fun k y hy => ?_)
    rw [Real.norm_eq_abs]
    exact hbnd y (abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩) k

/-- `y ↦ ∂ₓₓ K_full(t,x,y)` is interval-integrable on `[0,1]`. -/
theorem intervalIntegrable_secondDeriv_intervalNeumannFullKernel_fst {t : ℝ} (ht : 0 < t) (x : ℝ) :
    IntervalIntegrable
      (fun y : ℝ => deriv (fun x : ℝ => deriv (fun x : ℝ => intervalNeumannFullKernel t x y) x) x)
      MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact continuousOn_secondDeriv_intervalNeumannFullKernel_fst ht x

/-- **The second-derivative kernel `L¹` bound `∫₀¹|∂ₓₓK_full| ≤ (5√2/2)·t⁻¹`.**

  `∫₀¹ |∂ₓₓ K_full(t,x,y)| dy ≤ (5√2/2)·t^(−1)`.

Monotone bound by the dominating lattice series
(`abs_secondDeriv_intervalNeumannFullKernel_fst_le`), Tonelli interchange
`∫₀¹ ∑ₖ = ∑ₖ ∫₀¹` (summable cell masses), and the cell-tiling identity
(`tsum_cell_integral_eq_integral` with `g = |∂ₓₓheat|`) followed by the whole-line
mass bound `secondDeriv_heatKernel_abs_integral_le`.  Analogue of
`intervalNeumannFullKernel_deriv_abs_interval_integral_le`, one derivative up. -/
theorem intervalNeumannFullKernel_secondDeriv_abs_interval_integral_le
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∫ y in (0 : ℝ)..1,
        |deriv (fun x : ℝ => deriv (fun x : ℝ => intervalNeumannFullKernel t x y) x) x|)
      ≤ (5 * Real.sqrt 2 / 2) * t ^ (-(1 : ℝ)) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hcd := continuous_secondDeriv_heatKernel ht
  have hAcont : ∀ k : ℤ,
      Continuous (fun y : ℝ =>
        |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x - y + 2 * (k : ℝ))|) :=
    fun k => (hcd.comp (by fun_prop)).abs
  have hBcont : ∀ k : ℤ,
      Continuous (fun y : ℝ =>
        |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x + y + 2 * (k : ℝ))|) :=
    fun k => (hcd.comp (by fun_prop)).abs
  have hAii : ∀ k : ℤ, IntervalIntegrable
      (fun y : ℝ =>
        |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x - y + 2 * (k : ℝ))|)
      MeasureTheory.volume 0 1 := fun k => (hAcont k).intervalIntegrable 0 1
  have hBii : ∀ k : ℤ, IntervalIntegrable
      (fun y : ℝ =>
        |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x + y + 2 * (k : ℝ))|)
      MeasureTheory.volume 0 1 := fun k => (hBcont k).intervalIntegrable 0 1
  set hk : ℤ → ℝ → ℝ := fun k y =>
    |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x - y + 2 * (k : ℝ))|
      + |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x + y + 2 * (k : ℝ))|
    with hk_def
  have hk_nonneg : ∀ k y, 0 ≤ hk k y := fun k y => by rw [hk_def]; positivity
  -- summable majorant (radius-1 window bound, as in continuity).
  set u : ℤ → ℝ := fun k =>
    heatHessPointwiseBound t * Real.exp (1 / (4 * (2 * t)))
      * Real.exp (-(x + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t))) with hu_def
  have h4t : (0 : ℝ) < 4 * t := by linarith
  have hu2 : Summable (fun k : ℤ => 2 * u k) :=
    ((latticeExpSummable h4t x).mul_left
      (heatHessPointwiseBound t * Real.exp (1 / (4 * (2 * t))))).mul_left 2
  have hbnd : ∀ (s : ℝ), |s| ≤ (1 : ℝ) → ∀ k : ℤ,
      |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x + s + 2 * (k : ℝ))| ≤ u k := by
    intro s hs k
    refine (abs_secondDeriv_heatKernel_le ht (x + s + 2 * (k : ℝ))).trans ?_
    rw [hu_def]
    have hsb := abs_le.mp hs
    have hP : (1 / 2) * (x + 2 * (k : ℝ)) ^ 2 - 1 ≤ (x + s + 2 * (k : ℝ)) ^ 2 := by
      have hs2 : s ^ 2 ≤ 1 := by nlinarith [hsb.1, hsb.2]
      nlinarith [sq_nonneg (x + 2 * s + 2 * (k : ℝ)), hs2]
    have hexp : Real.exp (-(x + s + 2 * (k : ℝ)) ^ 2 / (4 * (2 * t)))
        ≤ Real.exp (1 / (4 * (2 * t)))
          * Real.exp (-(x + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have htne : t ≠ 0 := ne_of_gt ht
      have e1 : -(x + s + 2 * (k : ℝ)) ^ 2 / (4 * (2 * t))
          = (-2 * (x + s + 2 * (k : ℝ)) ^ 2) / (4 * (4 * t)) := by field_simp; ring
      have e2 : 1 / (4 * (2 * t)) + -(x + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t))
          = (2 - (x + 2 * (k : ℝ)) ^ 2) / (4 * (4 * t)) := by field_simp; ring
      rw [e1, e2]
      apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 4 * (4 * t))).mpr
      nlinarith [hP]
    calc heatHessPointwiseBound t * Real.exp (-(x + s + 2 * (k : ℝ)) ^ 2 / (4 * (2 * t)))
        ≤ heatHessPointwiseBound t * (Real.exp (1 / (4 * (2 * t)))
            * Real.exp (-(x + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t)))) :=
          mul_le_mul_of_nonneg_left hexp (heatHessPointwiseBound_nonneg ht)
      _ = heatHessPointwiseBound t * Real.exp (1 / (4 * (2 * t)))
            * Real.exp (-(x + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t))) := by ring
  have hk_bound : ∀ (k : ℤ) (y : ℝ), y ∈ Set.Icc (0 : ℝ) 1 → ‖hk k y‖ ≤ 2 * u k := by
    intro k y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (hk_nonneg k y)]
    have h1 := hbnd (-y)
      (by rw [abs_neg]; exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩) k
    have h2 := hbnd y (abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩) k
    rw [show x + (-y) + 2 * (k : ℝ) = x - y + 2 * (k : ℝ) by ring] at h1
    rw [hk_def]; linarith [h1, h2]
  have hDii : IntervalIntegrable (fun y : ℝ => ∑' k : ℤ, hk k y) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h01]
    exact continuousOn_tsum (fun k => ((hAcont k).add (hBcont k)).continuousOn) hu2 hk_bound
  -- Step 1: dominate by the lattice series.
  have hmono : (∫ y in (0 : ℝ)..1,
        |deriv (fun x : ℝ => deriv (fun x : ℝ => intervalNeumannFullKernel t x y) x) x|)
      ≤ ∫ y in (0 : ℝ)..1, ∑' k : ℤ, hk k y := by
    refine intervalIntegral.integral_mono_on h01
      (intervalIntegrable_secondDeriv_intervalNeumannFullKernel_fst ht x).abs hDii (fun y _ => ?_)
    rw [hk_def]
    exact abs_secondDeriv_intervalNeumannFullKernel_fst_le ht x y
  refine hmono.trans ?_
  -- Step 2: Tonelli + the cell-tiling identity + whole-line mass bound.
  have hμint : ∀ k : ℤ,
      Integrable (hk k) (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro k; rw [hk_def]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h01).mp ((hAii k).add (hBii k))
  have heq : ∀ k : ℤ,
      (∫ y, ‖hk k y‖ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)))
        = (∫ y in (0 : ℝ)..1,
            |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x - y + 2 * (k : ℝ))|)
          + (∫ y in (0 : ℝ)..1,
            |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
              (x + y + 2 * (k : ℝ))|) := by
    intro k
    have e1 : (∫ y, ‖hk k y‖ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)))
        = ∫ y in (0 : ℝ)..1, hk k y := by
      rw [intervalIntegral.integral_of_le h01]
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun y => Real.norm_of_nonneg (hk_nonneg k y))
    rw [e1]; exact intervalIntegral.integral_add (hAii k) (hBii k)
  have hμsum : Summable
      (fun k : ℤ => ∫ y, ‖hk k y‖ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
    (summable_cell_heatHess_interval_integral ht x).congr (fun k => (heq k).symm)
  have key := integral_tsum_of_summable_integral_norm
    (μ := MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) (F := hk) hμint hμsum
  have hval : (∫ y in (0 : ℝ)..1, ∑' k : ℤ, hk k y)
      = ∫ w : ℝ, |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) w| := by
    calc (∫ y in (0 : ℝ)..1, ∑' k : ℤ, hk k y)
        = ∫ y, (∑' k : ℤ, hk k y) ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
          intervalIntegral.integral_of_le h01
      _ = ∑' k : ℤ, ∫ y, hk k y ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := key.symm
      _ = ∑' k : ℤ,
            ((∫ y in (0 : ℝ)..1,
                |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x - y + 2 * (k : ℝ))|)
              + (∫ y in (0 : ℝ)..1,
                |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
                  (x + y + 2 * (k : ℝ))|)) := by
          refine tsum_congr (fun k => ?_)
          rw [← intervalIntegral.integral_of_le h01]
          exact intervalIntegral.integral_add (hAii k) (hBii k)
      _ = ∫ w : ℝ, |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) w| :=
          ShenWork.tsum_cell_integral_eq_integral (secondDeriv_heatKernel_abs_integrable ht) x
  rw [hval]
  exact secondDeriv_heatKernel_abs_integral_le ht

/-! ## The semigroup second `x`-derivative as `∫ ∂ₓₓK·f`, and the `L∞` bound -/

/-- Radius-`r` window majorant for the heat second derivative (no linear factor
beyond the half-rate Gaussian): `r²` Young slack gives `exp(r²/(8t))`. -/
noncomputable def heatHessWindowBound (t x r : ℝ) (k : ℤ) : ℝ :=
  heatHessPointwiseBound t * Real.exp (r ^ 2 / (4 * (2 * t)))
    * Real.exp (-(x + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t)))

theorem summable_heatHessWindowBound {t : ℝ} (ht : 0 < t) (x r : ℝ) :
    Summable (fun k : ℤ => heatHessWindowBound t x r k) := by
  have h4t : (0 : ℝ) < 4 * t := by linarith
  exact (latticeExpSummable h4t x).mul_left _

/-- **Radius-`r` uniform second-derivative bound.**  Whenever `|w − (x+2k)| ≤ r`,
`|∂ₓₓheat w| ≤ heatHessWindowBound t x r k` (Young `w² ≥ ½(x+2k)² − r²`). -/
theorem abs_secondDeriv_heatKernel_le_windowShift {t : ℝ} (ht : 0 < t) (x r : ℝ) (k : ℤ)
    {w : ℝ} (hw : |w - (x + 2 * (k : ℝ))| ≤ r) :
    |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) w|
      ≤ heatHessWindowBound t x r k := by
  refine (abs_secondDeriv_heatKernel_le ht w).trans ?_
  rw [heatHessWindowBound]
  have hr : 0 ≤ r := le_trans (abs_nonneg _) hw
  have hP : (1 / 2) * (x + 2 * (k : ℝ)) ^ 2 - r ^ 2 ≤ w ^ 2 := by
    have hB : (w - (x + 2 * (k : ℝ))) ^ 2 ≤ r ^ 2 := by
      rw [← sq_abs]; nlinarith [hw, abs_nonneg (w - (x + 2 * (k : ℝ)))]
    nlinarith [sq_nonneg (2 * w - (x + 2 * (k : ℝ))), hB]
  have hexp : Real.exp (-w ^ 2 / (4 * (2 * t)))
      ≤ Real.exp (r ^ 2 / (4 * (2 * t)))
        * Real.exp (-(x + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have htne : t ≠ 0 := ne_of_gt ht
    have e1 : -w ^ 2 / (4 * (2 * t)) = (-2 * w ^ 2) / (4 * (4 * t)) := by field_simp; ring
    have e2 : r ^ 2 / (4 * (2 * t)) + -(x + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t))
        = (2 * r ^ 2 - (x + 2 * (k : ℝ)) ^ 2) / (4 * (4 * t)) := by field_simp; ring
    rw [e1, e2]
    apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 4 * (4 * t))).mpr
    nlinarith [hP]
  calc heatHessPointwiseBound t * Real.exp (-w ^ 2 / (4 * (2 * t)))
      ≤ heatHessPointwiseBound t * (Real.exp (r ^ 2 / (4 * (2 * t)))
          * Real.exp (-(x + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t)))) :=
        mul_le_mul_of_nonneg_left hexp (heatHessPointwiseBound_nonneg ht)
    _ = heatHessPointwiseBound t * Real.exp (r ^ 2 / (4 * (2 * t)))
          * Real.exp (-(x + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t))) := by ring

/-- **Uniform constant bound on `∂ₓₓK_full` over `ball(x,1)×[0,1]`.**  For
`|z−x| ≤ 1` and `|y| ≤ 1`, `∂ₓₓK_full(z,y)` is dominated by the fixed constant
`∑ₖ 2·heatHessWindowBound t x 2 k` (radius-2 window).  Constant dominating
function for the second-order differentiation under the integral. -/
theorem abs_secondDeriv_intervalNeumannFullKernel_fst_le_const {t : ℝ} (ht : 0 < t) (x : ℝ)
    {z y : ℝ} (hz : |z - x| ≤ 1) (hy : |y| ≤ 1) :
    |deriv (fun z : ℝ => deriv (fun z : ℝ => intervalNeumannFullKernel t z y) z) z|
      ≤ ∑' k : ℤ, (heatHessWindowBound t x 2 k + heatHessWindowBound t x 2 k) := by
  refine (abs_secondDeriv_intervalNeumannFullKernel_fst_le ht z y).trans ?_
  have hzb := abs_le.mp hz
  have hyb := abs_le.mp hy
  refine Summable.tsum_le_tsum (fun k => ?_)
    ((summable_abs_iff.mpr (latticeGaussianHessSummable ht (z - y))).add
      (summable_abs_iff.mpr (latticeGaussianHessSummable ht (z + y))))
    ((summable_heatHessWindowBound ht x 2).add (summable_heatHessWindowBound ht x 2))
  have h1 : |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (z - y + 2 * (k : ℝ))|
      ≤ heatHessWindowBound t x 2 k :=
    abs_secondDeriv_heatKernel_le_windowShift ht x 2 k (by
      rw [show z - y + 2 * (k : ℝ) - (x + 2 * (k : ℝ)) = z - x - y by ring]
      exact abs_le.mpr ⟨by linarith [hzb.1, hyb.2], by linarith [hzb.2, hyb.1]⟩)
  have h2 : |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (z + y + 2 * (k : ℝ))|
      ≤ heatHessWindowBound t x 2 k :=
    abs_secondDeriv_heatKernel_le_windowShift ht x 2 k (by
      rw [show z + y + 2 * (k : ℝ) - (x + 2 * (k : ℝ)) = z - x + y by ring]
      exact abs_le.mpr ⟨by linarith [hzb.1, hyb.1], by linarith [hzb.2, hyb.2]⟩)
  linarith [h1, h2]

/-- **Second-order differentiation under the integral.**  For `t > 0` and bounded
measurable `f` (`|f| ≤ Cf`), the first `x`-derivative of the full propagator is
again differentiable at `x`, with derivative the integral of the kernel's second
derivative:

  `HasDerivAt (deriv (S_full t f)) (∫ y, ∂ₓₓK_full(t,·,y)·f y ∂(intervalMeasure 1)) x`.

`hasDerivAt_integral_of_dominated_loc_of_deriv_le` on `s = ball x 1`, with `F z y =
∂ₓK(z,y)·f y` (the committed first-derivative integrand, equal to `deriv (S t f) z`
by `intervalFullSemigroupOperator_hasDerivAt_fst`), constant dominating function
`(∑ₖ 2·heatHessWindowBound t x 2 k)·Cf`, and pointwise derivative from
`hasDerivAt_deriv_intervalNeumannFullKernel_fst`. -/
theorem intervalFullSemigroupOperator_hasDerivAt_deriv_fst {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    {Cf : ℝ} (hf : ∀ y, |f y| ≤ Cf) (x : ℝ) :
    HasDerivAt (fun z : ℝ => deriv (fun w : ℝ => intervalFullSemigroupOperator t f w) z)
      (∫ y, deriv (fun z : ℝ => deriv (fun z : ℝ => intervalNeumannFullKernel t z y) z) x * f y
        ∂(intervalMeasure 1)) x := by
  haveI : IsFiniteMeasure (intervalMeasure 1) := ⟨intervalMeasure_univ_lt_top 1⟩
  have hbdd : ∀ᵐ y ∂(intervalMeasure 1), ‖f y‖ ≤ Cf :=
    Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hf y
  set M : ℝ := ∑' k : ℤ, (heatHessWindowBound t x 2 k + heatHessWindowBound t x 2 k) with hM
  have hMnn : 0 ≤ M := by
    rw [hM]; exact tsum_nonneg fun k => by
      unfold heatHessWindowBound heatHessPointwiseBound; positivity
  -- the operator first derivative coincides with the first-derivative integrand.
  have hFeq : (fun z : ℝ => deriv (fun w : ℝ => intervalFullSemigroupOperator t f w) z)
      = fun z : ℝ =>
        ∫ y, deriv (fun w : ℝ => intervalNeumannFullKernel t w y) z * f y ∂(intervalMeasure 1) := by
    funext z; exact (intervalFullSemigroupOperator_hasDerivAt_fst ht hf_meas hf z).deriv
  rw [hFeq]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀ := x)
    (bound := fun _ => M * Cf)
    (F := fun z y => deriv (fun w : ℝ => intervalNeumannFullKernel t w y) z * f y)
    (F' := fun z y =>
      deriv (fun z' : ℝ => deriv (fun w : ℝ => intervalNeumannFullKernel t w y) z') z * f y)
    (Metric.ball_mem_nhds x one_pos)
    ?hFmeas ?hFint ?hF'meas ?hbound ?hbdint ?hdiff).2
  case hFmeas =>
    exact Filter.Eventually.of_forall fun z =>
      ((continuousOn_deriv_intervalNeumannFullKernel_fst ht z).aestronglyMeasurable
        measurableSet_Icc).mul hf_meas
  case hFint =>
    exact ((continuousOn_deriv_intervalNeumannFullKernel_fst ht x).integrableOn_Icc).mul_bdd
      hf_meas hbdd
  case hF'meas =>
    exact ((continuousOn_secondDeriv_intervalNeumannFullKernel_fst ht x).aestronglyMeasurable
      measurableSet_Icc).mul hf_meas
  case hbound =>
    simp only [intervalMeasure, intervalSet]
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun y hy z hz => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have hz1 : |z - x| ≤ 1 := by
      rw [← Real.dist_eq]; exact le_of_lt (Metric.mem_ball.mp hz)
    have hy1 : |y| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    exact mul_le_mul (abs_secondDeriv_intervalNeumannFullKernel_fst_le_const ht x hz1 hy1)
      (hf y) (abs_nonneg _) hMnn
  case hbdint => exact integrable_const _
  case hdiff =>
    refine Filter.Eventually.of_forall fun y z _ => ?_
    show HasDerivAt
      (fun z' : ℝ => deriv (fun w : ℝ => intervalNeumannFullKernel t w y) z' * f y)
      (deriv (fun z' : ℝ => deriv (fun w : ℝ => intervalNeumannFullKernel t w y) z') z * f y) z
    rw [(hasDerivAt_deriv_intervalNeumannFullKernel_fst ht z y).deriv]
    exact (hasDerivAt_deriv_intervalNeumannFullKernel_fst ht z y).mul_const (f y)

/-- **Second-derivative `L∞→L∞` bound for the full propagator (UNCONDITIONAL).**
For `t > 0` and bounded measurable `f` (`|f| ≤ Cf`),

  `|deriv (deriv (z ↦ S_full t f z)) x| ≤ (5√2/2)·t^(−1)·Cf`.

The second-order DUI representation `intervalFullSemigroupOperator_hasDerivAt_deriv_fst`
followed by `|∫ ∂ₓₓK·f| ≤ Cf·∫₀¹|∂ₓₓK_full| ≤ (5√2/2)t⁻¹·Cf`
(`intervalNeumannFullKernel_secondDeriv_abs_interval_integral_le`).  Analogue of
`intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t`, one derivative up. -/
theorem intervalFullSemigroupOperator_secondDeriv_Linfty_pointwise_inv_t {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    {Cf : ℝ} (hf : ∀ y, |f y| ≤ Cf) (x : ℝ) :
    |deriv (fun z : ℝ => deriv (fun w : ℝ => intervalFullSemigroupOperator t f w) z) x|
      ≤ (5 * Real.sqrt 2 / 2) * t ^ (-(1 : ℝ)) * Cf := by
  have hCf : 0 ≤ Cf := le_trans (abs_nonneg (f 0)) (hf 0)
  have hrepr := intervalFullSemigroupOperator_hasDerivAt_deriv_fst ht hf_meas hf x
  have hKint : Integrable
      (fun y : ℝ => deriv (fun z : ℝ => deriv (fun z : ℝ => intervalNeumannFullKernel t z y) z) x)
      (intervalMeasure 1) := by
    simp only [intervalMeasure, intervalSet]
    exact (continuousOn_secondDeriv_intervalNeumannFullKernel_fst ht x).integrableOn_Icc
  have hbdd : ∀ᵐ y ∂(intervalMeasure 1), ‖f y‖ ≤ Cf :=
    Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hf y
  have hprod_int : Integrable
      (fun y : ℝ =>
        deriv (fun z : ℝ => deriv (fun z : ℝ => intervalNeumannFullKernel t z y) z) x * f y)
      (intervalMeasure 1) := hKint.mul_bdd hf_meas hbdd
  have hint_le : (∫ y,
        |deriv (fun z : ℝ => deriv (fun z : ℝ => intervalNeumannFullKernel t z y) z) x|
        ∂(intervalMeasure 1))
      ≤ (5 * Real.sqrt 2 / 2) * t ^ (-(1 : ℝ)) := by
    have hcv : (∫ y,
          |deriv (fun z : ℝ => deriv (fun z : ℝ => intervalNeumannFullKernel t z y) z) x|
          ∂(intervalMeasure 1))
        = ∫ y in (0 : ℝ)..1,
          |deriv (fun z : ℝ => deriv (fun z : ℝ => intervalNeumannFullKernel t z y) z) x| := by
      simp only [intervalMeasure, intervalSet]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [hcv]
    exact intervalNeumannFullKernel_secondDeriv_abs_interval_integral_le ht x
  rw [hrepr.deriv]
  calc |∫ y,
          deriv (fun z : ℝ => deriv (fun z : ℝ => intervalNeumannFullKernel t z y) z) x * f y
          ∂(intervalMeasure 1)|
      ≤ ∫ y,
          ‖deriv (fun z : ℝ => deriv (fun z : ℝ => intervalNeumannFullKernel t z y) z) x * f y‖
          ∂(intervalMeasure 1) := by
        rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
    _ ≤ ∫ y,
          |deriv (fun z : ℝ => deriv (fun z : ℝ => intervalNeumannFullKernel t z y) z) x| * Cf
          ∂(intervalMeasure 1) := by
        refine MeasureTheory.integral_mono hprod_int.norm (hKint.abs.mul_const Cf) (fun y => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hf y) (abs_nonneg _)
    _ = (∫ y,
          |deriv (fun z : ℝ => deriv (fun z : ℝ => intervalNeumannFullKernel t z y) z) x|
          ∂(intervalMeasure 1)) * Cf := by rw [MeasureTheory.integral_mul_const]
    _ ≤ ((5 * Real.sqrt 2 / 2) * t ^ (-(1 : ℝ))) * Cf :=
        mul_le_mul_of_nonneg_right hint_le hCf

end ShenWork.IntervalNeumannFullKernel
