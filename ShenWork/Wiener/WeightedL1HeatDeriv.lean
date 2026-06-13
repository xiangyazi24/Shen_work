import ShenWork.Wiener.WeightedL1Operators

/-!
# The `t^{-1/2}` divergence-smoothing operator bound on `A^r`

This brick bounds the operator `S(τ) ∂ₓ` — the heat semigroup composed with the
spatial derivative — acting on Fourier coefficients via the multiplier
`m_τ(n) = (i · nπ) · exp(−τ (nπ)²)`.  The heat factor `exp(−τ (nπ)²)` more than
cancels the derivative symbol `inπ`, yielding the uniform `t^{-1/2}` bound

  `‖S(τ) ∂ₓ a‖_{A^r} ≤ (1 / √(2 e τ)) · ‖a‖_{A^r}`.

The crux (Part A) is the real-analysis sup bound `y · e^{−τ y²} ≤ 1/√(2eτ)`,
which after substituting `u = 2 τ y²` reduces to `u · e^{−u} ≤ 1/e`, proved by
`Real.add_one_le_exp` at `u − 1`.  Part B is a direct application of the
committed `wNorm_wMul_le`.
-/

open scoped BigOperators

namespace ShenWork.Wiener

/-- The `S(τ) ∂ₓ` multiplier: `(i · nπ) · exp(−τ (nπ)²)` applied coefficientwise. -/
noncomputable def heatDerivMul (τ : ℝ) (a : ℤ → ℂ) : ℤ → ℂ :=
  wMul (fun n => (Complex.I * ((n : ℝ) * Real.pi)
    * Real.exp (-(τ) * ((n : ℝ) * Real.pi) ^ 2) : ℂ)) a

/-- The elementary calculus fact `u · e^{−u} ≤ 1/e` for all `u ≥ 0`, via
`Real.add_one_le_exp` at `u − 1`: `u ≤ e^{u−1}`, so `u · e^{−u} ≤ e^{−1}`. -/
theorem mul_exp_neg_le {u : ℝ} (hu : 0 ≤ u) :
    u * Real.exp (-u) ≤ Real.exp (-1) := by
  have hkey : u ≤ Real.exp (u - 1) := by
    have := Real.add_one_le_exp (u - 1)
    linarith
  have hexp : (0 : ℝ) ≤ Real.exp (-u) := (Real.exp_pos _).le
  calc u * Real.exp (-u)
      ≤ Real.exp (u - 1) * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right hkey hexp
    _ = Real.exp ((u - 1) + (-u)) := (Real.exp_add _ _).symm
    _ = Real.exp (-1) := by ring_nf

/-- **Part A — the kernel sup bound.** `‖m_τ(n)‖ = |nπ| · e^{−τ(nπ)²} ≤ 1/√(2eτ)`. -/
theorem heatDeriv_symbol_le {τ : ℝ} (hτ : 0 < τ) (n : ℤ) :
    ‖(Complex.I * ((n : ℝ) * Real.pi)
        * Real.exp (-(τ) * ((n : ℝ) * Real.pi) ^ 2) : ℂ)‖
      ≤ 1 / Real.sqrt (2 * Real.exp 1 * τ) := by
  -- Reduce the complex norm to `|nπ| · exp(−τ(nπ)²)` with `y := |nπ| ≥ 0`.
  set y : ℝ := |(n : ℝ) * Real.pi| with hy
  have hy0 : 0 ≤ y := abs_nonneg _
  have hnorm : ‖(Complex.I * ((n : ℝ) * Real.pi)
      * Real.exp (-(τ) * ((n : ℝ) * Real.pi) ^ 2) : ℂ)‖
      = y * Real.exp (-(τ) * ((n : ℝ) * Real.pi) ^ 2) := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_pos _).le]
    have hcast : ‖(((n : ℝ) : ℂ) * (Real.pi : ℂ))‖ = y := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, hy, ← abs_mul]
    rw [hcast]
  rw [hnorm]
  -- `exp(−τ(nπ)²) = exp(−τ y²)` since `y² = (nπ)²`.
  have hysq : y ^ 2 = ((n : ℝ) * Real.pi) ^ 2 := by rw [hy, sq_abs]
  have hexpeq : Real.exp (-(τ) * ((n : ℝ) * Real.pi) ^ 2)
      = Real.exp (-(τ) * y ^ 2) := by rw [hysq]
  rw [hexpeq]
  -- Constants.
  have he1 : 0 < Real.exp 1 := Real.exp_pos 1
  have hden : 0 < 2 * Real.exp 1 * τ := by positivity
  -- Squared target: suffices `(y · e^{−τy²})² ≤ 1/(2eτ)`; take √ and use monotonicity.
  set L : ℝ := y * Real.exp (-(τ) * y ^ 2) with hL
  have hLnn : 0 ≤ L := mul_nonneg hy0 (Real.exp_pos _).le
  -- The squared bound.
  have hsq : L ^ 2 ≤ 1 / (2 * Real.exp 1 * τ) := by
    have hexp2 : (Real.exp (-(τ) * y ^ 2)) ^ 2
        = Real.exp (-(2 * τ * y ^ 2)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hLsq : L ^ 2 = y ^ 2 * Real.exp (-(2 * τ * y ^ 2)) := by
      rw [hL, mul_pow, hexp2]
    -- substitute `u = 2 τ y²`
    set u : ℝ := 2 * τ * y ^ 2 with hu
    have hu0 : 0 ≤ u := by positivity
    have hue : u * Real.exp (-u) ≤ Real.exp (-1) := mul_exp_neg_le hu0
    -- `y² = u / (2τ)`
    have hτ0 : (2 : ℝ) * τ ≠ 0 := by positivity
    have hysq2 : y ^ 2 = u / (2 * τ) := by
      rw [hu]; field_simp
    have hLsq2 : L ^ 2 = (1 / (2 * τ)) * (u * Real.exp (-u)) := by
      rw [hLsq, hysq2]; ring
    rw [hLsq2]
    -- `(1/(2τ)) · (u e^{−u}) ≤ (1/(2τ)) · e^{−1} = 1/(2eτ)`
    have h2τ : 0 < 1 / (2 * τ) := by positivity
    calc (1 / (2 * τ)) * (u * Real.exp (-u))
        ≤ (1 / (2 * τ)) * Real.exp (-1) :=
          mul_le_mul_of_nonneg_left hue h2τ.le
      _ = 1 / (2 * Real.exp 1 * τ) := by
          rw [Real.exp_neg]
          have he : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
          field_simp
  -- Take square roots: `L = √(L²) ≤ √(1/(2eτ)) = 1/√(2eτ)`.
  have hstep : L = Real.sqrt (L ^ 2) := (Real.sqrt_sq hLnn).symm
  rw [← hL] at *
  calc L = Real.sqrt (L ^ 2) := hstep
    _ ≤ Real.sqrt (1 / (2 * Real.exp 1 * τ)) := Real.sqrt_le_sqrt hsq
    _ = 1 / Real.sqrt (2 * Real.exp 1 * τ) := by
        rw [Real.sqrt_div' 1 hden.le, Real.sqrt_one]

/-- **Part B closure** — the smoothing multiplier preserves `MemW`. -/
theorem memW_heatDerivMul {r : ℕ} {a : ℤ → ℂ} {τ : ℝ} (hτ : 0 < τ)
    (ha : MemW r a) : MemW r (heatDerivMul τ a) :=
  memW_wMul (fun n => heatDeriv_symbol_le hτ n) ha

/-- **Part B — the operator bound on `A^r`** (the `t^{-1/2}` divergence smoothing):
`‖S(τ) ∂ₓ a‖_{A^r} ≤ (1/√(2eτ)) · ‖a‖_{A^r}`. -/
theorem heatDerivMul_bound {r : ℕ} {a : ℤ → ℂ} {τ : ℝ} (hτ : 0 < τ)
    (ha : MemW r a) :
    wNorm r (heatDerivMul τ a)
      ≤ (1 / Real.sqrt (2 * Real.exp 1 * τ)) * wNorm r a := by
  have hCm : (0 : ℝ) ≤ 1 / Real.sqrt (2 * Real.exp 1 * τ) := by positivity
  exact wNorm_wMul_le hCm (fun n => heatDeriv_symbol_le hτ n) ha

end ShenWork.Wiener
