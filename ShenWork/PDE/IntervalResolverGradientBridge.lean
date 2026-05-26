/-
# Termwise-differentiation bridge for the elliptic resolver (sub-step b2)

The elliptic resolver value `intervalNeumannResolverR p u` is the cosine series
`∑' k, (v̂_k).re · cos(kπ y)`, and `intervalNeumannResolverRGrad p u` is the
termwise-differentiated series `∑' k, (v̂_k).re · (−kπ · sin(kπ y))`.  This file
proves that, under a summable majorant on the derivative terms, the spatial
derivative of the value series equals the gradient series — sub-step **(b2)**.

## The general termwise-differentiation lemma

For any real coefficient sequence `c : ℕ → ℝ` such that
`Summable (fun k => |c k| · (k·π))` (the gradient `ℓ¹` majorant), the function
`y ↦ ∑' k, c k · cos(kπ y)` is differentiable everywhere with derivative
`∑' k, c k · (−kπ · sin(kπ y))`.  This is Mathlib's Weierstrass M-test
`hasDerivAt_tsum`: each summand `y ↦ c k · cos(kπ y)` has derivative
`c k · (−kπ sin(kπ y))`, whose norm is `≤ |c k|·kπ` (the majorant), and the value
series converges at `0` (each cos(0)=1, summand `c k`, dominated by `|c k| ≤ |c k|·kπ`
for `k ≥ 1` plus the `k=0` term).

## The resolver specialization

Taking `c k = (intervalNeumannResolverCoeff p u k).re` gives, for every interval
point `x`,

  `HasDerivAt (fun y => intervalNeumannResolverR p u (lift y)) …
      = intervalNeumannResolverRGrad p u x`

(where `lift y` denotes the interval point at `y`), PROVIDED the gradient majorant
`Summable (fun k => |(v̂_k).re| · kπ)` holds.  Combined with the coefficient-level
elliptic characterization `solution_v_resolverCoeff_eq` (value equality) and the
`C²`-Neumann source decay (sub-step b1, supplying the majorant when the source
`ν u^γ` is `C²`-Neumann), this identifies the solution's spatial `v`-derivative with
the termwise series, closing the gradient control.

No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.PDE.IntervalNeumannEllipticResolverR
import ShenWork.PDE.IntervalCosineCoeffDecay
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Real.Pi.Bounds

open MeasureTheory
open ShenWork.IntervalDomain ShenWork.CosineSpectrum
open ShenWork.HeatKernelGradientEstimates
open ShenWork.Paper3 (unitIntervalNeumannSpectrum)
open scoped Topology BigOperators

namespace ShenWork.IntervalResolverGradientBridge

noncomputable section

/-! ## Derivative of a single cosine mode -/

/-- `y ↦ c · cos(kπ y)` has derivative `c · (−kπ · sin(kπ y))` at every `y`. -/
theorem cosineTerm_hasDerivAt (c : ℝ) (k : ℕ) (y : ℝ) :
    HasDerivAt (fun z : ℝ => c * Real.cos ((k : ℝ) * Real.pi * z))
      (c * (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * y))) y := by
  have hlin : HasDerivAt (fun z : ℝ => (k : ℝ) * Real.pi * z) ((k : ℝ) * Real.pi) y := by
    simpa using (hasDerivAt_id y).const_mul ((k : ℝ) * Real.pi)
  have hcos : HasDerivAt (fun z : ℝ => Real.cos ((k : ℝ) * Real.pi * z))
      (-Real.sin ((k : ℝ) * Real.pi * y) * ((k : ℝ) * Real.pi)) y :=
    (Real.hasDerivAt_cos _).comp y hlin
  have h := hcos.const_mul c
  convert h using 1
  ring

/-! ## The general termwise-differentiation bridge -/

/-- **General termwise-differentiation bridge.**  For a real coefficient sequence
`c` whose derivative-term magnitudes `|c k| · kπ` are summable, the cosine series
`y ↦ ∑' k, c k · cos(kπ y)` is differentiable with derivative the termwise series
`∑' k, c k · (−kπ · sin(kπ y))`. -/
theorem cosineSeries_hasDerivAt_of_gradSummable
    {c : ℕ → ℝ}
    (hmaj : Summable fun k : ℕ => |c k| * ((k : ℝ) * Real.pi))
    (y : ℝ) :
    HasDerivAt
      (fun z : ℝ => ∑' k : ℕ, c k * Real.cos ((k : ℝ) * Real.pi * z))
      (∑' k : ℕ, c k * (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * y))) y := by
  -- Majorant `u k = |c k|·kπ`.
  set u : ℕ → ℝ := fun k => |c k| * ((k : ℝ) * Real.pi) with hu
  -- The value series at `y₀ = 0` is `∑ c k` (cos 0 = 1); it is dominated by the
  -- majorant up to the `k = 0` term, hence summable.
  have hg0 : Summable fun k : ℕ => c k * Real.cos ((k : ℝ) * Real.pi * (0 : ℝ)) := by
    have heq : (fun k : ℕ => c k * Real.cos ((k : ℝ) * Real.pi * (0 : ℝ)))
        = fun k => c k := by
      funext k; simp
    rw [heq]
    -- `|c k| ≤ |c k|·kπ` for `k ≥ 1`; the majorant `hmaj` is summable, so `c` is.
    -- Drop the `k = 0` term and compare.
    rw [← summable_nat_add_iff 1]
    have hmaj1 : Summable fun k : ℕ => u (k + 1) :=
      (summable_nat_add_iff (f := u) 1).2 hmaj
    refine Summable.of_norm_bounded (hmaj1) ?_
    intro k
    rw [Real.norm_eq_abs, hu]
    -- `|c (k+1)| ≤ |c (k+1)| · ((k+1)π)` since `(k+1)π ≥ 1`.
    have hge1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * Real.pi := by
      have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
        have : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg k
        push_cast; linarith
      have hpi : (1 : ℝ) ≤ Real.pi := le_of_lt (lt_trans (by norm_num) Real.pi_gt_three)
      nlinarith [hk1, hpi]
    calc |c (k + 1)| = |c (k + 1)| * 1 := (mul_one _).symm
      _ ≤ |c (k + 1)| * (((k + 1 : ℕ) : ℝ) * Real.pi) :=
          mul_le_mul_of_nonneg_left hge1 (abs_nonneg _)
  -- Apply the M-test.
  exact hasDerivAt_tsum (𝕜 := ℝ) (F := ℝ) (u := u)
    (g := fun k z => c k * Real.cos ((k : ℝ) * Real.pi * z))
    (g' := fun k z => c k * (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * z)))
    hmaj
    (fun k z => cosineTerm_hasDerivAt (c k) k z)
    (fun k z => by
      rw [Real.norm_eq_abs, hu, abs_mul]
      have hsin : |(-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * z))|
          ≤ (k : ℝ) * Real.pi := by
        rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ) * Real.pi)]
        calc (k : ℝ) * Real.pi * |Real.sin ((k : ℝ) * Real.pi * z)|
            ≤ (k : ℝ) * Real.pi * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity)
          _ = (k : ℝ) * Real.pi := mul_one _
      exact mul_le_mul_of_nonneg_left hsin (abs_nonneg _))
    hg0 y

/-! ## The resolver specialization -/

open ShenWork.PDE

/-- The resolver value as a plain function of the real coordinate `y`:
`intervalNeumannResolverR p u (lift y) = ∑' k, (v̂_k).re · cos(kπ y)`. -/
theorem resolverR_apply_eq (p : CM2Params) (u : intervalDomainPoint → ℝ)
    (x : intervalDomainPoint) :
    intervalNeumannResolverR p u x
      = ∑' k : ℕ, (intervalNeumannResolverCoeff p u k).re *
          Real.cos ((k : ℝ) * Real.pi * x.1) := by
  simp only [intervalNeumannResolverR, unitIntervalCosineMode]

/-- The resolver gradient as a plain function of `y`:
`intervalNeumannResolverRGrad p u (lift y) = ∑' k, (v̂_k).re · (−kπ · sin(kπ y))`. -/
theorem resolverRGrad_apply_eq (p : CM2Params) (u : intervalDomainPoint → ℝ)
    (x : intervalDomainPoint) :
    intervalNeumannResolverRGrad p u x
      = ∑' k : ℕ, (intervalNeumannResolverCoeff p u k).re *
          (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x.1)) := by
  simp only [intervalNeumannResolverRGrad]

/-- **Termwise-differentiation bridge for the resolver (sub-step b2).**

If the resolver gradient coefficients are `ℓ¹` (`hmaj`: `∑ |(v̂_k).re|·kπ < ∞`),
then for every real coordinate `y` the spatial derivative of the resolver value
function `y ↦ intervalNeumannResolverR p u ⟨y,…⟩` (as a series in `y`) equals the
termwise-differentiated gradient series, i.e. the value of
`intervalNeumannResolverRGrad p u ⟨y,…⟩`.

The hypothesis `hmaj` is the gradient-series absolute summability; it is supplied
by the `C²`-Neumann source decay (sub-step b1) whenever the elliptic source
`ν u^γ` is `C²`-Neumann (then `|(v̂_k).re| ~ 1/k³`, so `|(v̂_k).re|·kπ ~ 1/k²`). -/
theorem resolverR_hasDerivAt_grad
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hmaj : Summable fun k : ℕ =>
      |(intervalNeumannResolverCoeff p u k).re| * ((k : ℝ) * Real.pi))
    (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun z : ℝ => ∑' k : ℕ, (intervalNeumannResolverCoeff p u k).re *
        Real.cos ((k : ℝ) * Real.pi * z))
      (intervalNeumannResolverRGrad p u ⟨y, hy⟩) y := by
  rw [resolverRGrad_apply_eq]
  exact cosineSeries_hasDerivAt_of_gradSummable
    (c := fun k => (intervalNeumannResolverCoeff p u k).re) hmaj y

/-! ## The gradient `ℓ¹` majorant from `C²`-Neumann source decay (b1 ⇒ b2 input) -/

/-- The resolver coefficient real part is `(source coeff).re / (μ + λ_k)`. -/
theorem resolverCoeff_re_eq (p : CM2Params) (u : intervalDomainPoint → ℝ) (k : ℕ) :
    (intervalNeumannResolverCoeff p u k).re =
      (intervalNeumannResolverSourceCoeff p u k).re /
        (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) := by
  have hden_pos : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue k :=
    intervalNeumannResolver_denom_pos p k
  have hne : (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) ≠ 0 := ne_of_gt hden_pos
  -- from `(μ+λ)·v̂ = â` (complex), take real parts.
  have hres := intervalNeumannResolverCoeff_elliptic p u k
  have hcast :
      ((p.μ : ℂ) + (unitIntervalNeumannSpectrum.eigenvalue k : ℂ)) =
        (((p.μ + unitIntervalNeumannSpectrum.eigenvalue k : ℝ)) : ℂ) := by
    push_cast; ring
  rw [hcast] at hres
  have hre := congrArg Complex.re hres
  rw [Complex.re_ofReal_mul] at hre
  -- hre : (μ+λ) · v̂.re = â.re
  rw [eq_div_iff hne]
  linarith [hre]

/-- **Gradient `ℓ¹` majorant from source-coefficient quadratic decay (b1 ⇒ b2).**

Given a quadratic decay `|(source coeff).re| ≤ C/(kπ)²` of the elliptic source's
cosine coefficients for `k ≥ 1` (this is exactly the output of sub-step b1
`cosineCoeff_decay` applied to the source `ν u^γ`, valid when that source is
`C²`-Neumann), the resolver gradient coefficients `|(v̂_k).re| · kπ` are absolutely
summable.  Indeed for `k ≥ 1`,

  `|(v̂_k).re|·kπ = |(source).re|/(μ+λ_k) · kπ ≤ (C/(kπ)²)/(kπ)² · kπ = (C/π³)·1/k³`,

summable by comparison with `∑ 1/k³`.  This discharges the gradient majorant
hypothesis of `resolverR_hasDerivAt_grad`. -/
theorem resolverGrad_majorant_summable_of_sourceDecay
    {p : CM2Params} {u : intervalDomainPoint → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ k : ℕ, 1 ≤ k →
      |(intervalNeumannResolverSourceCoeff p u k).re| ≤ C / ((k : ℝ) * Real.pi) ^ 2) :
    Summable fun k : ℕ =>
      |(intervalNeumannResolverCoeff p u k).re| * ((k : ℝ) * Real.pi) := by
  classical
  rw [← summable_nat_add_iff 1]
  -- Majorant `(C/π³)·1/(k+1)³`.
  have hmaj : Summable fun k : ℕ => (C / Real.pi ^ 3) * (1 / ((k : ℝ) + 1) ^ 3) := by
    have hp3 : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 3 := by
      have := (Real.summable_one_div_nat_pow (p := 3)).mpr (by norm_num)
      simpa using (summable_nat_add_iff (f := fun k : ℕ => 1 / (k : ℝ) ^ 3) 1).2 this
    exact hp3.mul_left _
  refine Summable.of_nonneg_of_le (fun k => by positivity) ?_ hmaj
  intro k
  -- Work at index `k+1 ≥ 1`.
  set m : ℕ := k + 1 with hm
  have hm1 : 1 ≤ m := Nat.le_add_left 1 k
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm1
  have hmpi_pos : (0 : ℝ) < (m : ℝ) * Real.pi := mul_pos hmpos Real.pi_pos
  have hden_pos : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue m :=
    intervalNeumannResolver_denom_pos p m
  -- denominator lower bound `(mπ)² ≤ μ+λ_m`.
  have hlam : unitIntervalNeumannSpectrum.eigenvalue m = (m : ℝ) ^ 2 * Real.pi ^ 2 := rfl
  have hdenlow : ((m : ℝ) * Real.pi) ^ 2 ≤ p.μ + unitIntervalNeumannSpectrum.eigenvalue m := by
    rw [hlam]; nlinarith [p.hμ.le, sq_nonneg ((m:ℝ) * Real.pi)]
  -- `(v̂_m).re = (source).re/(μ+λ_m)`, so `|(v̂_m).re|·mπ = |(source).re|·mπ/(μ+λ_m)`.
  rw [resolverCoeff_re_eq, abs_div, abs_of_pos hden_pos]
  -- numerator `|(source).re| ≤ C/(mπ)²`.
  have hnum := hdecay m hm1
  have hmpi_sq_pos : (0 : ℝ) < ((m : ℝ) * Real.pi) ^ 2 := by positivity
  -- `|src|/den · mπ ≤ (C/(mπ)²)/(mπ)² · mπ`.
  have hsrc_nonneg : 0 ≤ |(intervalNeumannResolverSourceCoeff p u m).re| := abs_nonneg _
  -- bound `|src|/den ≤ (C/(mπ)²)/(mπ)²` (numerator up, denominator down).
  have hfrac : |(intervalNeumannResolverSourceCoeff p u m).re| /
        (p.μ + unitIntervalNeumannSpectrum.eigenvalue m)
      ≤ (C / ((m : ℝ) * Real.pi) ^ 2) / ((m : ℝ) * Real.pi) ^ 2 := by
    have hden_inv : 1 / (p.μ + unitIntervalNeumannSpectrum.eigenvalue m)
        ≤ 1 / ((m : ℝ) * Real.pi) ^ 2 :=
      one_div_le_one_div_of_le hmpi_sq_pos hdenlow
    rw [div_eq_mul_one_div, div_eq_mul_one_div (C / ((m : ℝ) * Real.pi) ^ 2)]
    apply mul_le_mul hnum hden_inv (by positivity) (by positivity)
  have hstep : |(intervalNeumannResolverSourceCoeff p u m).re| /
        (p.μ + unitIntervalNeumannSpectrum.eigenvalue m) * ((m : ℝ) * Real.pi)
      ≤ (C / ((m : ℝ) * Real.pi) ^ 2) / ((m : ℝ) * Real.pi) ^ 2 * ((m : ℝ) * Real.pi) :=
    mul_le_mul_of_nonneg_right hfrac (le_of_lt hmpi_pos)
  refine hstep.trans (le_of_eq ?_)
  -- `(C/(mπ)²)/(mπ)²·mπ = (C/π³)/m³`.  And `m = k+1`.
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hmcast : (m : ℝ) = (k : ℝ) + 1 := by rw [hm]; push_cast; ring
  rw [hmcast]
  have hkne : ((k : ℝ) + 1) ≠ 0 := by positivity
  field_simp

end

end ShenWork.IntervalResolverGradientBridge
