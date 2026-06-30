import ShenWork.Paper2.IntervalDomainTheorem11
import ShenWork.PDE.IntervalDomain

/-!
# 1D Agmon interpolation on the unit interval

For `f ∈ C¹[0,1]` with `f > 0`, we prove:
  `∫₀¹ f^q ≤ eps · ∫₀¹ f^{q-2}·(f')² + Ceps · (∫₀¹ f)^q`

This is the 1D specialization of the Gagliardo-Nirenberg interpolation
inequality, proved via the elementary sup-norm bound (FTC) and Hölder.

Proof chain:
1. Sup-norm bound: `sup f ≤ ∫₀¹ f + ∫₀¹ |f'|` (FTC + triangle)
2. Cauchy-Schwarz: `∫₀¹ |f'| ≤ (∫₀¹ f'²)^{1/2}`
3. Hölder: `∫₀¹ f^q ≤ (sup f)^{q-1} · ∫₀¹ f`
4. Young-epsilon assembly
-/

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

/-! ### Step 1: 1D sup-norm bound from the fundamental theorem of calculus -/

/-- On `[0,1]`, a nonneg continuous function satisfies
`f(x) ≤ ∫₀¹ f + ∫₀¹ |f'|` for every `x ∈ [0,1]`.

Proof: `f(x) = f(y) + ∫ᵧˣ f'` for any `y`, so
`f(x) ≤ f(y) + ∫₀¹ |f'|` for all `y`.  Averaging over `y ∈ [0,1]`:
`f(x) ≤ ∫₀¹ f(y) dy + ∫₀¹ |f'(y)| dy`. -/
theorem sup_le_integral_add_integral_deriv
    {f : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Icc 0 1))
    (hf_diff : DifferentiableOn ℝ f (Ioo 0 1))
    (hf_nonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x) :
    ∀ x ∈ Icc (0 : ℝ) 1,
      f x ≤ ∫ y in (0 : ℝ)..1, f y + ∫ y in (0 : ℝ)..1, |deriv f y| := by
  intro x hx
  -- Key: for every y ∈ [0,1], f(x) ≤ f(y) + ∫₀¹ |f'|
  -- because f(x) - f(y) = ∫ᵧˣ f' ≤ |∫ᵧˣ f'| ≤ ∫₀¹ |f'|
  have habs_deriv_int : ∀ y ∈ Icc (0 : ℝ) 1,
      f x - f y ≤ ∫ s in (0 : ℝ)..1, |deriv f s| := by
    intro y hy
    -- f(x) - f(y) = ∫ᵧˣ f' ≤ |∫ᵧˣ f'| ≤ ∫_{min}^{max} |f'| ≤ ∫₀¹ |f'|
    -- For the FTC we need HasDerivAt on the interior of [y,x] or [x,y]
    -- Use: DifferentiableOn + interior ⟹ HasDerivAt at interior points
    sorry
  -- Averaging: f(x) = f(x) · ∫₀¹ 1 ≤ ∫₀¹ (f(y) + C) = ∫f + C
  -- where C = ∫₀¹ |f'|
  set C := ∫ s in (0 : ℝ)..1, |deriv f s|
  have hpoint : ∀ y ∈ Icc (0 : ℝ) 1, f x ≤ f y + C := by
    intro y hy; linarith [habs_deriv_int y hy]
  -- ∫₀¹ (f(y) + C) = ∫f + C · 1 = ∫f + C
  have hle_integral : f x ≤ ∫ y in (0 : ℝ)..1, (f y + C) := by
    have h1 : f x = f x * (1 - 0) := by ring
    rw [h1]
    have h2 : f x * (1 - 0) = ∫ _y in (0 : ℝ)..1, f x := by
      rw [intervalIntegral.integral_const]; simp [smul_eq_mul]
    rw [h2]
    exact intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
      intervalIntegrable_const
      (hf_cont.intervalIntegrable_of_Icc (by norm_num) |>.add intervalIntegrable_const)
      (fun y hy => hpoint y hy)
  have hsplit : ∫ y in (0 : ℝ)..1, (f y + C) =
      (∫ y in (0 : ℝ)..1, f y) + C := by
    rw [intervalIntegral.integral_add
      (hf_cont.intervalIntegrable_of_Icc (by norm_num))
      intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp [smul_eq_mul]
  linarith

/-! ### Step 2: Cauchy-Schwarz on the unit interval -/

/-- Cauchy-Schwarz on `[0,1]`: `∫₀¹ |g| ≤ (∫₀¹ g²)^{1/2}`.
This is `‖g‖_{L¹} ≤ ‖g‖_{L²}` on the unit interval. -/
theorem integral_abs_le_sqrt_integral_sq
    {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 1) :
    ∫ y in (0 : ℝ)..1, |g y| ≤
      Real.sqrt (∫ y in (0 : ℝ)..1, g y ^ 2) := by
  sorry

/-! ### Step 3: Hölder/pointwise bound for Lq -/

/-- Pointwise bound: `∫₀¹ f^q ≤ (sup f)^{q-1} · ∫₀¹ f` for `f ≥ 0`.
This is just `f(x)^q = f(x)^{q-1} · f(x) ≤ (sup f)^{q-1} · f(x)`. -/
theorem integral_rpow_le_sup_rpow_mul_integral
    {f : ℝ → ℝ} {q M : ℝ}
    (hq : 1 ≤ q)
    (hf_pos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < f x)
    (hf_le : ∀ x ∈ Icc (0 : ℝ) 1, f x ≤ M)
    (hf_int_pow : IntervalIntegrable (fun y => f y ^ q) volume 0 1)
    (hf_int : IntervalIntegrable f volume 0 1) :
    ∫ y in (0 : ℝ)..1, f y ^ q ≤
      M ^ (q - 1) * ∫ y in (0 : ℝ)..1, f y := by
  have hpoint : ∀ y ∈ Icc (0 : ℝ) 1, f y ^ q ≤ M ^ (q - 1) * f y := by
    intro y hy
    have hfy_pos := hf_pos y hy
    have hfyM := hf_le y hy
    have h1 : f y ^ (q - 1) ≤ M ^ (q - 1) :=
      Real.rpow_le_rpow hfy_pos.le hfyM (by linarith)
    calc f y ^ q = f y ^ (q - 1 + 1) := by ring_nf
      _ = f y ^ (q - 1) * f y ^ (1 : ℝ) :=
          Real.rpow_add hfy_pos (q - 1) 1
      _ = f y ^ (q - 1) * f y := by rw [Real.rpow_one]
      _ ≤ M ^ (q - 1) * f y :=
          mul_le_mul_of_nonneg_right h1 hfy_pos.le
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hf_int_pow
    (hf_int.const_mul _) hpoint
  rwa [intervalIntegral.integral_const_mul] at hmono

/-! ### Step 4: Assembly — the 1D Agmon interpolation inequality -/

/-- The 1D Agmon interpolation inequality on `[0,1]` for positive C¹ functions:
`∫₀¹ f^q ≤ eps · ∫₀¹ f^{q-2}·(f')² + Ceps · (∫₀¹ f)^q`

Note: `f^{q-2}·(f')²` is the gradient-dissipation weight that appears in the
Moser iteration energy inequality.  For `f > 0` it equals
`(2/(q-1))² · |∂ₓ(f^{(q-1)/2})|²`. -/
theorem intervalDomain_agmon_interpolation
    {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x)
    (hf_cont : ContinuousOn (intervalDomainLift f) (Icc 0 1))
    (hf_diff : DifferentiableOn ℝ (intervalDomainLift f) (Ioo 0 1))
    {q : ℝ} (hq : 1 < q)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ Ceps > 0,
      intervalDomain.integral (fun x => f x ^ q) ≤
        eps * intervalDomain.integral
          (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2) +
        Ceps * (intervalDomain.integral f) ^ q := by
  sorry

/-! ### Step 5: Producer for `IntervalDomainClassicalSolutionPositiveInterpolation` -/

/-- Produce the classical-solution positive interpolation frontier from the
1D Agmon inequality applied to each time slice of the classical solution. -/
theorem intervalDomain_classicalSolutionPositiveInterpolation_of_agmon
    {params : CM2Params}
    (hagmon :
      ∀ (f : intervalDomain.Point → ℝ),
        (∀ x, 0 < f x) →
        ContinuousOn (intervalDomainLift f) (Icc 0 1) →
        DifferentiableOn ℝ (intervalDomainLift f) (Ioo 0 1) →
          ∀ q : ℝ, 1 < q →
            ∀ eps : ℝ, 0 < eps →
              ∃ Ceps > 0,
                intervalDomain.integral (fun x => f x ^ q) ≤
                  eps * intervalDomain.integral
                    (fun x => f x ^ (q - 2) *
                      (intervalDomain.gradNorm f x) ^ 2) +
                  Ceps * (intervalDomain.integral f) ^ q) :
    IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation
      params := by
  intro T u v hsol eps heps q hq
  sorry

#print axioms intervalDomain_agmon_interpolation

end ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

end
