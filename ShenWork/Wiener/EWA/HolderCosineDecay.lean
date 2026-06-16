/-
  ShenWork/Wiener/EWA/HolderCosineDecay.lean

  **P2-T11 endpoint route — pass-2 step (iii): Hölder ⇒ summable cosine
  coefficients with `n^{-(1+η)}` decay.**

  The bridge from the `C^{1+η}` Hölder bootstrap (pass 1, `ChemMildHolder.lean`)
  to the committed EWA / weighted-Wiener engine (`ShenWork/Wiener/EWA/Basic.lean`),
  which consumes a SUMMABLE cosine-coefficient envelope.

  GOAL.  For `f : ℝ → ℝ` with `Differentiable ℝ f`, Neumann data
  `deriv f 0 = deriv f 1 = 0`, and an `η`-Hölder derivative
  `∀ x y, |deriv f x − deriv f y| ≤ K |x − y|^η` (`0 < η ≤ 1`, `0 ≤ K`):

    * `holderCosineCoeff_decay`     — `∃ C ≥ 0, ∀ n ≥ 1, |cosineCoeffs f n| ≤ C n^{-(1+η)}`;
    * `holderCosineCoeff_summable`  — `Summable (fun n => |cosineCoeffs f n|)`.

  ROUTE.
  1. For `n ≥ 1`, `cosineCoeffs f n = 2 ∫₀¹ cos(nπx) f(x) dx`
     (`cosineCoeffs_eq_two_mul_integral`, from the committed
     `IntervalCosineInversion.cosineCoeffs_eq` + `fco_eq_ofReal`).
  2. IBP once with `v = sin(nπx)/(nπ)`, `v' = cos(nπx)`: the boundary term
     `[f · sin(nπx)/(nπ)]₀¹` VANISHES (`sin 0 = sin(nπ) = 0`), giving
     `∫₀¹ cos(nπx) f = −(1/(nπ)) ∫₀¹ (deriv f)(x) sin(nπx) dx`
     (`cos_integral_eq_neg_sine_integral`).
  3. Hölder–Fourier decay of `g := deriv f` via the HALF-PERIOD SHIFT
     `sin(nπ(x+1/n)) = −sin(nπx)`: `2S = D − A + B` with the main difference
     integral `D = ∫₀¹ (g(x) − g(x+1/n)) sin` bounded by `K n^{-η}` and the two
     overhang strips `A,B` of length `1/n ≤ n^{-η}` bounded by `M/n` each
     (`sine_integral_holder_decay`).
  4. Combine `|c_n| ≤ (2/(nπ)) · C_η n^{-η} = C n^{-(1+η)}` and run
     `summable_nat_rpow` (exponent `−(1+η) < −1 ⇔ η > 0`); `n = 0` is finite.

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.PDE.IntervalCosineInversion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.PSeries

open MeasureTheory
open scoped Real

noncomputable section

namespace ShenWork.Wiener.EWA

open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalCosineInversion

/-! ## Step 1 — the real cosine coefficient for `n ≥ 1`. -/

/-- For a continuous real `f` and `n ≥ 1`, the committed Neumann cosine coefficient
is twice the elementary cosine integral. -/
theorem cosineCoeffs_eq_two_mul_integral (f : ℝ → ℝ) (hf : Continuous f)
    {n : ℕ} (hn : 1 ≤ n) :
    cosineCoeffs f n = 2 * ∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * f x := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  rw [cosineCoeffs_eq f hf n, if_neg hn0, fco_eq_ofReal f hf (n : ℤ)]
  simp

/-! ## Step 2 — integration by parts (the boundary term vanishes). -/

/-- IBP step: with `v = sin(nπx)/(nπ)` (so `v' = cos(nπx)`) and the boundary term
killed by `sin 0 = sin(nπ) = 0`,
`∫₀¹ cos(nπx) f = −(1/(nπ)) ∫₀¹ (deriv f)(x) sin(nπx) dx`. -/
theorem cos_integral_eq_neg_sine_integral (f : ℝ → ℝ)
    (hf' : Differentiable ℝ f) (hderiv_cont : Continuous (deriv f)) {n : ℕ} (hn : 1 ≤ n) :
    (∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * f x) =
      -(1 / ((n : ℝ) * Real.pi)) *
        ∫ x in (0 : ℝ)..1, deriv f x * Real.sin ((n : ℝ) * Real.pi * x) := by
  have hnπ_pos : 0 < (n : ℝ) * Real.pi :=
    mul_pos (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn) Real.pi_pos
  have hnπ_ne : ((n : ℝ) * Real.pi) ≠ 0 := ne_of_gt hnπ_pos
  -- `v x = sin(nπx)/(nπ)`, with `HasDerivAt v (cos(nπx)) x` everywhere.
  set v : ℝ → ℝ := fun x => Real.sin ((n : ℝ) * Real.pi * x) / ((n : ℝ) * Real.pi) with hv
  have hv_deriv : ∀ x : ℝ, HasDerivAt v (Real.cos ((n : ℝ) * Real.pi * x)) x := by
    intro x
    have hinner : HasDerivAt (fun x : ℝ => (n : ℝ) * Real.pi * x) ((n : ℝ) * Real.pi) x := by
      simpa using (hasDerivAt_id x).const_mul ((n : ℝ) * Real.pi)
    have hs : HasDerivAt (fun x : ℝ => Real.sin ((n : ℝ) * Real.pi * x))
        (Real.cos ((n : ℝ) * Real.pi * x) * ((n : ℝ) * Real.pi)) x :=
      (Real.hasDerivAt_sin ((n : ℝ) * Real.pi * x)).comp x hinner
    have := hs.div_const ((n : ℝ) * Real.pi)
    simpa [hv, mul_div_assoc, mul_div_cancel_right₀ _ hnπ_ne] using this
  have hv_cont : Continuous v := by
    have : Continuous (fun x : ℝ => Real.sin ((n : ℝ) * Real.pi * x)) :=
      Real.continuous_sin.comp (continuous_const.mul continuous_id)
    exact this.div_const _
  -- `u = f`, `u' = deriv f`.
  have hf_cont : Continuous f := hf'.continuous
  have hu_io : ∀ x ∈ Set.Ioo (min (0 : ℝ) 1) (max 0 1), HasDerivAt f (deriv f x) x :=
    fun x _ => (hf' x).hasDerivAt
  have hv_io : ∀ x ∈ Set.Ioo (min (0 : ℝ) 1) (max 0 1),
      HasDerivAt v (Real.cos ((n : ℝ) * Real.pi * x)) x := fun x _ => hv_deriv x
  have hu'_int : IntervalIntegrable (deriv f) volume 0 1 := hderiv_cont.intervalIntegrable _ _
  have hcos_int : IntervalIntegrable
      (fun x => Real.cos ((n : ℝ) * Real.pi * x)) volume 0 1 :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hIBP :
      (∫ x in (0 : ℝ)..1, f x * Real.cos ((n : ℝ) * Real.pi * x)) =
        f 1 * v 1 - f 0 * v 0 - ∫ x in (0 : ℝ)..1, deriv f x * v x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hf_cont.continuousOn hv_cont.continuousOn hu_io hv_io hu'_int hcos_int
  -- boundary term vanishes: `v 0 = 0`, `v 1 = 0`.
  have hv0 : v 0 = 0 := by simp [hv]
  have hv1 : v 1 = 0 := by
    have hsin1 : Real.sin ((n : ℝ) * Real.pi * 1) = 0 := by
      rw [mul_one]; exact_mod_cast Real.sin_nat_mul_pi n
    show Real.sin ((n : ℝ) * Real.pi * 1) / ((n : ℝ) * Real.pi) = 0
    rw [hsin1, zero_div]
  rw [hv0, hv1] at hIBP
  -- rewrite LHS (commute) and pull the constant `1/(nπ)` out of the RHS integral.
  have hcomm : (∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * f x) =
      ∫ x in (0 : ℝ)..1, f x * Real.cos ((n : ℝ) * Real.pi * x) := by
    apply intervalIntegral.integral_congr; intro x _; ring
  have hpull : (∫ x in (0 : ℝ)..1, deriv f x * v x) =
      (1 / ((n : ℝ) * Real.pi)) *
        ∫ x in (0 : ℝ)..1, deriv f x * Real.sin ((n : ℝ) * Real.pi * x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr; intro x _
    show deriv f x * (Real.sin ((n : ℝ) * Real.pi * x) / ((n : ℝ) * Real.pi)) =
      1 / ((n : ℝ) * Real.pi) * (deriv f x * Real.sin ((n : ℝ) * Real.pi * x))
    ring
  rw [hcomm, hIBP, hpull]; ring

/-! ## Step 3 — Hölder–Fourier decay via the half-period shift. -/

/-- **Half-period shift identity.**  For any `g` and `n ≥ 1`, writing `h = 1/n`
and `S = ∫₀¹ g(x) sin(nπx) dx`, one has `2 S = D − A + B` where
`D = ∫₀¹ (g(x) − g(x+h)) sin(nπx) dx`, `A = ∫₁^{1+h} g sin`, `B = ∫₀^h g sin`.
This is the algebraic engine: `sin(nπ(x+h)) = −sin(nπx)`. -/
theorem sine_shift_identity (g : ℝ → ℝ)
    (hg : Continuous g) {n : ℕ} (hn : 1 ≤ n) :
    2 * (∫ x in (0 : ℝ)..1, g x * Real.sin ((n : ℝ) * Real.pi * x)) =
      (∫ x in (0 : ℝ)..1,
          (g x - g (x + 1 / (n : ℝ))) * Real.sin ((n : ℝ) * Real.pi * x))
        - (∫ x in (1 : ℝ)..(1 + 1 / (n : ℝ)), g x * Real.sin ((n : ℝ) * Real.pi * x))
        + (∫ x in (0 : ℝ)..(1 / (n : ℝ)), g x * Real.sin ((n : ℝ) * Real.pi * x)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  set h : ℝ := 1 / (n : ℝ) with hh
  -- pointwise: `g(x+h) · sin(nπ(x+h)) = - g(x+h) · sin(nπx)`.
  have hshift_sin : ∀ x : ℝ,
      Real.sin ((n : ℝ) * Real.pi * (x + h)) = - Real.sin ((n : ℝ) * Real.pi * x) := by
    intro x
    have harg : (n : ℝ) * Real.pi * (x + h) = (n : ℝ) * Real.pi * x + Real.pi := by
      have : (n : ℝ) * h = 1 := by rw [hh]; field_simp
      have hexp : (n : ℝ) * Real.pi * (x + h)
          = (n : ℝ) * Real.pi * x + Real.pi * ((n : ℝ) * h) := by ring
      rw [hexp, this, mul_one]
    rw [harg, Real.sin_add, Real.sin_pi, Real.cos_pi]; ring
  -- change of variables `x ↦ x + h` on the product `g · sin`.
  have hcomp : (∫ x in (0 : ℝ)..1,
        g (x + h) * Real.sin ((n : ℝ) * Real.pi * (x + h)))
      = ∫ x in (0 + h)..(1 + h), g x * Real.sin ((n : ℝ) * Real.pi * x) :=
    intervalIntegral.integral_comp_add_right
      (fun x => g x * Real.sin ((n : ℝ) * Real.pi * x)) h
  -- rewrite the LHS integrand using the shift sign.
  have hcompEq : (∫ x in (0 : ℝ)..1,
        - (g (x + h) * Real.sin ((n : ℝ) * Real.pi * x)))
      = ∫ x in (0 : ℝ)..1, g (x + h) * Real.sin ((n : ℝ) * Real.pi * (x + h)) := by
    apply intervalIntegral.integral_congr; intro x _
    simp only [hshift_sin x]; ring
  have hcomp2 : (∫ x in (0 : ℝ)..1,
        - (g (x + h) * Real.sin ((n : ℝ) * Real.pi * x)))
      = ∫ x in (0 + h)..(1 + h), g x * Real.sin ((n : ℝ) * Real.pi * x) :=
    hcompEq.trans hcomp
  -- continuity / integrability of the product.
  have hprod_cont : Continuous (fun x : ℝ => g x * Real.sin ((n : ℝ) * Real.pi * x)) :=
    hg.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  -- split `[0+h, 1+h] = [0,1] + (strip A at [1,1+h]) − (strip B at [0,h])` via additivity.
  have hsplitR :
      (∫ x in (0 + h)..(1 + h), g x * Real.sin ((n : ℝ) * Real.pi * x))
        = (∫ x in (0 : ℝ)..1, g x * Real.sin ((n : ℝ) * Real.pi * x))
          + (∫ x in (1 : ℝ)..(1 + h), g x * Real.sin ((n : ℝ) * Real.pi * x))
          - (∫ x in (0 : ℝ)..h, g x * Real.sin ((n : ℝ) * Real.pi * x)) := by
    have hi : ∀ a b : ℝ, IntervalIntegrable
        (fun x => g x * Real.sin ((n : ℝ) * Real.pi * x)) volume a b :=
      fun a b => hprod_cont.intervalIntegrable a b
    have e1 : (∫ x in (0 : ℝ)..1, g x * Real.sin ((n : ℝ) * Real.pi * x))
        + (∫ x in (1 : ℝ)..(1 + h), g x * Real.sin ((n : ℝ) * Real.pi * x))
          = ∫ x in (0 : ℝ)..(1 + h), g x * Real.sin ((n : ℝ) * Real.pi * x) :=
      intervalIntegral.integral_add_adjacent_intervals (hi 0 1) (hi 1 (1 + h))
    have e2 : (∫ x in (0 : ℝ)..h, g x * Real.sin ((n : ℝ) * Real.pi * x))
        + (∫ x in h..(1 + h), g x * Real.sin ((n : ℝ) * Real.pi * x))
          = ∫ x in (0 : ℝ)..(1 + h), g x * Real.sin ((n : ℝ) * Real.pi * x) :=
      intervalIntegral.integral_add_adjacent_intervals (hi 0 h) (hi h (1 + h))
    rw [zero_add]; linarith [e1, e2]
  -- assemble.  `-∫ g(x+h) sin(nπx) = R = S + A - B`, and `S` on the left.
  have hLeftEq : (∫ x in (0 : ℝ)..1, g (x + h) * Real.sin ((n : ℝ) * Real.pi * x))
      = - ((∫ x in (0 : ℝ)..1, g x * Real.sin ((n : ℝ) * Real.pi * x))
          + (∫ x in (1 : ℝ)..(1 + h), g x * Real.sin ((n : ℝ) * Real.pi * x))
          - (∫ x in (0 : ℝ)..h, g x * Real.sin ((n : ℝ) * Real.pi * x))) := by
    have := hcomp2
    rw [intervalIntegral.integral_neg] at this
    rw [hsplitR] at this
    linarith [this]
  -- `D = S - ∫ g(x+h) sin`: split the difference integrand, then use `hLeftEq`.
  have hshift_cont : Continuous (fun x : ℝ => g (x + h) * Real.sin ((n : ℝ) * Real.pi * x)) :=
    (hg.comp (continuous_id.add continuous_const)).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  have hD : (∫ x in (0 : ℝ)..1,
        (g x - g (x + h)) * Real.sin ((n : ℝ) * Real.pi * x))
      = (∫ x in (0 : ℝ)..1, g x * Real.sin ((n : ℝ) * Real.pi * x))
        - ∫ x in (0 : ℝ)..1, g (x + h) * Real.sin ((n : ℝ) * Real.pi * x) := by
    rw [show (fun x => (g x - g (x + h)) * Real.sin ((n : ℝ) * Real.pi * x))
        = fun x => g x * Real.sin ((n : ℝ) * Real.pi * x)
          - g (x + h) * Real.sin ((n : ℝ) * Real.pi * x) from by funext x; ring]
    exact intervalIntegral.integral_sub (hprod_cont.intervalIntegrable 0 1)
      (hshift_cont.intervalIntegrable 0 1)
  rw [hD, hLeftEq]; ring

/-- **Hölder–Fourier decay.**  If `g` is `η`-Hölder on `ℝ` (`0 < η ≤ 1`, `0 ≤ K`),
then for `n ≥ 1` the sine integral decays like `n^{-η}`, with the explicit constant
`(1/2)·(K + 2 M)` where `M = |g 0| + K·2^η` is a sup bound for `|g|` on `[0, 2]`. -/
theorem sine_integral_holder_decay (g : ℝ → ℝ) (hg : Continuous g)
    {η K : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (hK : 0 ≤ K)
    (hHolder : ∀ x y, |g x - g y| ≤ K * |x - y| ^ η) {n : ℕ} (hn : 1 ≤ n) :
    |∫ x in (0 : ℝ)..1, g x * Real.sin ((n : ℝ) * Real.pi * x)| ≤
      (1 / 2) * (K + 2 * (|g 0| + K * 2 ^ η)) * (n : ℝ) ^ (-η) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set h : ℝ := 1 / (n : ℝ) with hh
  have hh_pos : 0 < h := by rw [hh]; positivity
  have hh_le1 : h ≤ 1 := by rw [hh]; rw [div_le_one hnpos]; exact hn1
  set M : ℝ := |g 0| + K * 2 ^ η with hM
  have hM_nonneg : 0 ≤ M := by
    rw [hM]; have : (0:ℝ) ≤ K * 2 ^ η := mul_nonneg hK (by positivity)
    positivity
  -- sup bound: `|g x| ≤ M` for `x ∈ [0, 1+h]` (so on the strips).
  have hgsup : ∀ x : ℝ, 0 ≤ x → x ≤ 1 + h → |g x| ≤ M := by
    intro x hx0 hx1
    have hxle2 : |x| ^ η ≤ 2 ^ η := by
      apply Real.rpow_le_rpow (abs_nonneg x) _ (le_of_lt hη0)
      rw [abs_of_nonneg hx0]; linarith [hh_le1]
    have hbd := hHolder x 0
    rw [sub_zero] at hbd
    have hgxle : |g x| ≤ |g 0| + K * |x| ^ η := by
      have htri := abs_sub_abs_le_abs_sub (g x) (g 0)
      linarith [htri, hbd]
    calc |g x| ≤ |g 0| + K * |x| ^ η := hgxle
      _ ≤ |g 0| + K * 2 ^ η := by
          have : K * |x| ^ η ≤ K * 2 ^ η := mul_le_mul_of_nonneg_left hxle2 hK
          linarith
      _ = M := by rw [hM]
  -- the three pieces.
  set S := ∫ x in (0 : ℝ)..1, g x * Real.sin ((n : ℝ) * Real.pi * x) with hSdef
  set D := ∫ x in (0 : ℝ)..1,
      (g x - g (x + h)) * Real.sin ((n : ℝ) * Real.pi * x) with hDdef
  set A := ∫ x in (1 : ℝ)..(1 + h), g x * Real.sin ((n : ℝ) * Real.pi * x) with hAdef
  set B := ∫ x in (0 : ℝ)..h, g x * Real.sin ((n : ℝ) * Real.pi * x) with hBdef
  -- |D| ≤ K h^η.
  have hD_bd : |D| ≤ K * h ^ η := by
    have hpt : ∀ x ∈ Set.uIoc (0:ℝ) 1,
        ‖(g x - g (x + h)) * Real.sin ((n : ℝ) * Real.pi * x)‖ ≤ K * h ^ η := by
      intro x _
      rw [Real.norm_eq_abs, abs_mul]
      have hs : |Real.sin ((n : ℝ) * Real.pi * x)| ≤ 1 := Real.abs_sin_le_one _
      have hgg : |g x - g (x + h)| ≤ K * h ^ η := by
        have := hHolder x (x + h)
        have hxx : |x - (x + h)| = h := by rw [show x - (x+h) = -h by ring, abs_neg,
          abs_of_pos hh_pos]
        rwa [hxx] at this
      calc |g x - g (x + h)| * |Real.sin ((n : ℝ) * Real.pi * x)|
          ≤ (K * h ^ η) * 1 := by
            apply mul_le_mul hgg hs (abs_nonneg _)
            exact mul_nonneg hK (by positivity)
        _ = K * h ^ η := by ring
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1) hpt
    rw [Real.norm_eq_abs] at this
    have h1 : |(1:ℝ) - 0| = 1 := by norm_num
    rw [h1, mul_one] at this; rw [hDdef]; exact this
  -- |A| ≤ M h.
  have hA_bd : |A| ≤ M * h := by
    have hpt : ∀ x ∈ Set.uIoc (1:ℝ) (1 + h),
        ‖g x * Real.sin ((n : ℝ) * Real.pi * x)‖ ≤ M := by
      intro x hx
      rw [Set.uIoc_of_le (by linarith)] at hx
      rw [Real.norm_eq_abs, abs_mul]
      have hs : |Real.sin ((n : ℝ) * Real.pi * x)| ≤ 1 := Real.abs_sin_le_one _
      have hgx : |g x| ≤ M := hgsup x (by linarith [hx.1]) hx.2
      calc |g x| * |Real.sin ((n : ℝ) * Real.pi * x)| ≤ M * 1 :=
            mul_le_mul hgx hs (abs_nonneg _) hM_nonneg
        _ = M := mul_one M
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1:ℝ)) (b := 1 + h) hpt
    rw [Real.norm_eq_abs] at this
    have h1 : |(1 + h) - 1| = h := by rw [show (1+h) - 1 = h by ring, abs_of_pos hh_pos]
    rw [h1] at this; rw [hAdef]; exact this
  -- |B| ≤ M h.
  have hB_bd : |B| ≤ M * h := by
    have hpt : ∀ x ∈ Set.uIoc (0:ℝ) h,
        ‖g x * Real.sin ((n : ℝ) * Real.pi * x)‖ ≤ M := by
      intro x hx
      rw [Set.uIoc_of_le (le_of_lt hh_pos)] at hx
      rw [Real.norm_eq_abs, abs_mul]
      have hs : |Real.sin ((n : ℝ) * Real.pi * x)| ≤ 1 := Real.abs_sin_le_one _
      have hgx : |g x| ≤ M := hgsup x (le_of_lt hx.1) (by linarith [hx.2])
      calc |g x| * |Real.sin ((n : ℝ) * Real.pi * x)| ≤ M * 1 :=
            mul_le_mul hgx hs (abs_nonneg _) hM_nonneg
        _ = M := mul_one M
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := h) hpt
    rw [Real.norm_eq_abs] at this
    have h1 : |h - 0| = h := by rw [sub_zero, abs_of_pos hh_pos]
    rw [h1] at this; rw [hBdef]; exact this
  -- combine: |2S| = |D - A + B| ≤ |D| + |A| + |B| ≤ K h^η + 2 M h ≤ (K + 2M) h^η.
  have hhη : h ^ η = (n : ℝ) ^ (-η) := by
    rw [hh, one_div, Real.inv_rpow (le_of_lt hnpos), ← Real.rpow_neg (le_of_lt hnpos)]
  have hh_le_hη : h ≤ h ^ η := by
    -- for 0 < h ≤ 1 and η ≤ 1, `h ≤ h^η`.
    calc h = h ^ (1 : ℝ) := (Real.rpow_one h).symm
      _ ≤ h ^ η := Real.rpow_le_rpow_of_exponent_ge hh_pos hh_le1 hη1
  -- the shift identity already rewrote the goal LHS into `|D - A + B|`.
  have htri : |D - A + B| ≤ |D| + |A| + |B| := by
    have h1 : |D - A| ≤ |D| + |A| := abs_sub D A
    calc |D - A + B| ≤ |D - A| + |B| := abs_add_le _ _
      _ ≤ (|D| + |A|) + |B| := by linarith [h1]
  have hMh : M * h ≤ M * h ^ η := mul_le_mul_of_nonneg_left hh_le_hη hM_nonneg
  have hsum : |D - A + B| ≤ K * h ^ η + 2 * (M * h ^ η) := by
    calc |D - A + B| ≤ |D| + |A| + |B| := htri
      _ ≤ K * h ^ η + M * h + M * h := by linarith [hD_bd, hA_bd, hB_bd]
      _ ≤ K * h ^ η + 2 * (M * h ^ η) := by linarith [hMh]
  -- `2 S = D - A + B`, so `2 |S| = |D - A + B| ≤ K h^η + 2 M h^η`.
  have hshift : (2 : ℝ) * S = D - A + B := by
    rw [hSdef, hDdef, hAdef, hBdef]; exact sine_shift_identity g hg hn
  have habs2S : |(2 : ℝ) * S| = 2 * |S| := by rw [abs_mul]; norm_num
  have hSbound : 2 * |S| ≤ K * h ^ η + 2 * (M * h ^ η) := by
    rw [← habs2S, hshift]; exact hsum
  -- repackage RHS into the stated closed form with `n^{-η}` and divide by 2.
  have hRHS : (1 / 2 : ℝ) * (K + 2 * (|g 0| + K * 2 ^ η)) * (n : ℝ) ^ (-η)
      = (1 / 2) * (K * h ^ η + 2 * (M * h ^ η)) := by rw [hM, ← hhη]; ring
  rw [hRHS]; linarith [hSbound]

/-- A function `η`-Hölder on `ℝ` (`η > 0`) is continuous. -/
theorem continuous_of_holder {g : ℝ → ℝ} {η K : ℝ} (hη0 : 0 < η) (hK : 0 ≤ K)
    (hHolder : ∀ x y, |g x - g y| ≤ K * |x - y| ^ η) : Continuous g := by
  rw [Metric.continuous_iff]
  intro x ε hε
  -- pick `δ` with `K δ^η < ε` (and `δ ≤ 1`).  Take `δ = min 1 (ε/(K+1))^{1/η}`.
  set δ : ℝ := min 1 ((ε / (K + 1)) ^ (1 / η)) with hδ
  have hδ_pos : 0 < δ := by
    rw [hδ]; apply lt_min one_pos; apply Real.rpow_pos_of_pos; positivity
  refine ⟨δ, hδ_pos, fun y hy => ?_⟩
  rw [Real.dist_eq] at hy ⊢
  have hyx : |y - x| < δ := hy
  have hyx0 : 0 ≤ |y - x| := abs_nonneg _
  -- `|g y - g x| ≤ K |y-x|^η`.
  have hbd : |g y - g x| ≤ K * |y - x| ^ η := hHolder y x
  -- `|y-x|^η < δ^η ≤ ((ε/(K+1))^{1/η})^η = ε/(K+1)`.
  have hpow_lt : |y - x| ^ η ≤ δ ^ η := by
    apply Real.rpow_le_rpow hyx0 (le_of_lt hyx) (le_of_lt hη0)
  have hδη : δ ^ η ≤ ε / (K + 1) := by
    have hle : δ ≤ (ε / (K + 1)) ^ (1 / η) := min_le_right _ _
    calc δ ^ η ≤ ((ε / (K + 1)) ^ (1 / η)) ^ η :=
          Real.rpow_le_rpow (le_of_lt hδ_pos) hle (le_of_lt hη0)
      _ = ε / (K + 1) := by
          rw [← Real.rpow_mul (by positivity), one_div,
            inv_mul_cancel₀ (ne_of_gt hη0), Real.rpow_one]
  calc |g y - g x| ≤ K * |y - x| ^ η := hbd
    _ ≤ K * (ε / (K + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hK; exact le_trans hpow_lt hδη
    _ < ε := by
        rw [mul_div_assoc']
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [mul_nonneg hK (le_of_lt hε)]

/-! ## Step 4 — assembling the decay bound and summability. -/

/-- **Main decay bound.**  A `C^{1+η}` function with Neumann data has cosine
coefficients decaying like `n^{-(1+η)}`. -/
theorem holderCosineCoeff_decay (f : ℝ → ℝ) (hf' : Differentiable ℝ f)
    (hNeumann : deriv f 0 = 0 ∧ deriv f 1 = 0)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) {K : ℝ} (hK : 0 ≤ K)
    (hHolder : ∀ x y, |deriv f x - deriv f y| ≤ K * |x - y| ^ η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → |cosineCoeffs f n| ≤ C * (n : ℝ) ^ (-(1 + η)) := by
  have hg_cont : Continuous (deriv f) := continuous_of_holder hη0 hK hHolder
  have hf_cont : Continuous f := hf'.continuous
  set Cη : ℝ := (1 / 2) * (K + 2 * (|deriv f 0| + K * 2 ^ η)) with hCη
  have hCη_nonneg : 0 ≤ Cη := by
    rw [hCη]; have : (0:ℝ) ≤ K * 2 ^ η := mul_nonneg hK (by positivity); positivity
  refine ⟨2 * Cη / Real.pi, by positivity, fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hπpos : (0 : ℝ) < Real.pi := Real.pi_pos
  -- coefficient = `2 · (-(1/(nπ)) · S)`.
  rw [cosineCoeffs_eq_two_mul_integral f hf_cont hn,
    cos_integral_eq_neg_sine_integral f hf' hg_cont hn]
  set S := ∫ x in (0 : ℝ)..1, deriv f x * Real.sin ((n : ℝ) * Real.pi * x) with hSdef
  have hSbd : |S| ≤ Cη * (n : ℝ) ^ (-η) :=
    sine_integral_holder_decay (deriv f) hg_cont hη0 hη1 hK hHolder hn
  -- `|2 · (-(1/(nπ)) S)| = (2/(nπ)) |S|`.
  have habs : |2 * (-(1 / ((n : ℝ) * Real.pi)) * S)| = (2 / ((n : ℝ) * Real.pi)) * |S| := by
    rw [abs_mul, abs_mul, abs_neg]
    rw [abs_of_pos (show (0:ℝ) < 1 / ((n:ℝ) * Real.pi) by positivity)]
    rw [show |(2:ℝ)| = 2 by norm_num]; ring
  rw [habs]
  -- `n^{-η} = n^{-(1+η)} · n`, so `(2/(nπ)) · Cη · n^{-η} = (2Cη/π) n^{-(1+η)}`.
  have hrpow : (n : ℝ) ^ (-η) = (n : ℝ) ^ (-(1 + η)) * (n : ℝ) := by
    rw [show (-η : ℝ) = (-(1 + η)) + 1 by ring, Real.rpow_add hnpos, Real.rpow_one]
  calc (2 / ((n : ℝ) * Real.pi)) * |S|
      ≤ (2 / ((n : ℝ) * Real.pi)) * (Cη * (n : ℝ) ^ (-η)) := by
        apply mul_le_mul_of_nonneg_left hSbd; positivity
    _ = 2 * Cη / Real.pi * (n : ℝ) ^ (-(1 + η)) := by
        rw [hrpow]
        have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
        have hπne : Real.pi ≠ 0 := ne_of_gt hπpos
        field_simp

/-- **Summability of the cosine-coefficient envelope.**  Consumed by the EWA /
weighted-Wiener engine. -/
theorem holderCosineCoeff_summable (f : ℝ → ℝ) (hf' : Differentiable ℝ f)
    (hNeumann : deriv f 0 = 0 ∧ deriv f 1 = 0)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) {K : ℝ} (hK : 0 ≤ K)
    (hHolder : ∀ x y, |deriv f x - deriv f y| ≤ K * |x - y| ^ η) :
    Summable (fun n : ℕ => |cosineCoeffs f n|) := by
  obtain ⟨C, hC0, hCbd⟩ :=
    holderCosineCoeff_decay f hf' hNeumann hη0 hη1 hK hHolder
  -- envelope `C n^{-(1+η)}` is summable (exponent `< -1`), so the (nonneg) series is.
  have hsummable_tail : Summable (fun n : ℕ => C * (n : ℝ) ^ (-(1 + η))) := by
    apply Summable.mul_left
    rw [Real.summable_nat_rpow]; linarith
  -- bound term-by-term against the tail (the `n = 0` term is absorbed by adding `|c_0|`).
  apply Summable.of_norm_bounded_eventually_nat hsummable_tail
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs, abs_abs]
  exact hCbd n hn
