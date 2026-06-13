import ShenWork.Wiener.WeightedL1Operators

/-!
# Convolution powers, the submultiplicative power bound, heat contraction, and embeddings

Pure sequence algebra (no PDE, unconditional). Building on brick 1
(`wConv`, `wNorm_conv_le`, `memW_conv`) and brick 2 (`wMul`, `wNorm_wMul_le`),
this brick (3a) supplies the foundational facts needed to build the algebra
exponential and the heat semigroup on the weighted ℓ¹ Wiener algebra `A^r`.

* **Part A — convolution powers.** The Kronecker unit `wOne` and the iterated
  convolution `wPow a k = a^{⋆k}`, with the submultiplicative power bound
  `wNorm r (a^{⋆k}) ≤ (wNorm r a)^k` proved by induction on `wNorm_conv_le`.
  This is the key input to the convergence of `exp(a) = Σ a^{⋆k}/k!`.

* **Part B — heat-semigroup contraction.** The heat multiplier
  `h_τ(n) = exp(-(τ)(nπ)²)` has sup-norm `≤ 1` for `τ ≥ 0`, so multiplication
  by it is a contraction of `A^r` (a direct application of `wNorm_wMul_le`).

* **Part C — weight-monotone embedding.** Since `1 + |n| ≥ 1`, the weight is
  monotone in `r`, giving `A^r ⊆ A^s` and `wNorm s a ≤ wNorm r a` for `s ≤ r`.
-/

open scoped BigOperators

namespace ShenWork.Wiener

/-- The multiplicative unit (Kronecker delta at `0`). -/
def wOne : ℤ → ℂ := fun n => if n = 0 then 1 else 0

/-- Iterated convolution `wPow a k = a^{⋆k}` (`a^{⋆0} = wOne`). -/
noncomputable def wPow (a : ℤ → ℂ) : ℕ → (ℤ → ℂ)
  | 0     => wOne
  | (k+1) => wConv a (wPow a k)

/-- `wOne` lies in every weighted ℓ¹ space (it is finitely supported). -/
theorem memW_wOne (r : ℕ) : MemW r wOne := by
  rw [MemW]
  refine summable_of_hasFiniteSupport ?_
  apply Set.Finite.subset (Set.finite_singleton (0 : ℤ))
  intro n hn
  simp only [Function.mem_support, Set.mem_singleton_iff] at *
  by_contra hne
  apply hn
  simp [wOne, hne]

/-- Powers stay in `A^r`. -/
theorem memW_wPow {r : ℕ} {a : ℤ → ℂ} (ha : MemW r a) (k : ℕ) : MemW r (wPow a k) := by
  induction k with
  | zero => exact memW_wOne r
  | succ k ih => exact memW_conv ha ih

/-- The weighted norm of the unit is `≤ 1` (in fact `= 1`, since `wWeight r 0 = 1`). -/
theorem wNorm_wOne_le (r : ℕ) : wNorm r wOne ≤ 1 := by
  have hval : wNorm r wOne = 1 := by
    rw [wNorm]
    rw [tsum_eq_single (0 : ℤ)]
    · simp [wOne, wWeight]
    · intro n hn; simp [wOne, hn]
  rw [hval]

/-- `wNorm r a` is nonnegative (a tsum of nonnegative terms). -/
theorem wNorm_nonneg (r : ℕ) (a : ℤ → ℂ) : 0 ≤ wNorm r a := by
  rw [wNorm]
  exact tsum_nonneg (fun n => weightedNorm_nonneg r a n)

/-- **The submultiplicative power bound** `wNorm r (a^{⋆k}) ≤ (wNorm r a)^k`.
Induction on `k` via `wNorm_conv_le` (the Banach-algebra product bound). -/
theorem wNorm_wPow_le {r : ℕ} {a : ℤ → ℂ} (ha : MemW r a) (k : ℕ) :
    wNorm r (wPow a k) ≤ (wNorm r a) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero]; exact wNorm_wOne_le r
  | succ k ih =>
    have hstep : wNorm r (wPow a (k + 1)) ≤ wNorm r a * wNorm r (wPow a k) := by
      change wNorm r (wConv a (wPow a k)) ≤ wNorm r a * wNorm r (wPow a k)
      exact wNorm_conv_le r ha (memW_wPow ha k)
    calc wNorm r (wPow a (k + 1))
        ≤ wNorm r a * wNorm r (wPow a k) := hstep
      _ ≤ wNorm r a * (wNorm r a) ^ k :=
          mul_le_mul_of_nonneg_left ih (wNorm_nonneg r a)
      _ = (wNorm r a) ^ (k + 1) := by rw [pow_succ]; ring

/-! ### Part B — heat-semigroup contraction on `A^r` -/

/-- The heat multiplier `h_τ(n) = exp(-(τ)(nπ)²)`, applied as a pointwise multiplier. -/
noncomputable def heatMul (τ : ℝ) (a : ℤ → ℂ) : ℤ → ℂ :=
  wMul (fun n => (Real.exp (-(τ) * ((n : ℝ) * Real.pi) ^ 2) : ℂ)) a

/-- The heat multiplier has sup-norm `≤ 1` for `τ ≥ 0`, so it contracts `A^r`. -/
theorem heatMul_contraction {r : ℕ} {a : ℤ → ℂ} {τ : ℝ} (hτ : 0 ≤ τ) (ha : MemW r a) :
    wNorm r (heatMul τ a) ≤ wNorm r a := by
  have hbound : ∀ n : ℤ,
      ‖(Real.exp (-(τ) * ((n : ℝ) * Real.pi) ^ 2) : ℂ)‖ ≤ 1 := by
    intro n
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    rw [Real.exp_le_one_iff]
    have hsq : (0 : ℝ) ≤ ((n : ℝ) * Real.pi) ^ 2 := sq_nonneg _
    nlinarith [hτ, hsq]
  have hmul := wNorm_wMul_le (r := r)
    (m := fun n => (Real.exp (-(τ) * ((n : ℝ) * Real.pi) ^ 2) : ℂ))
    (a := a) (Cm := 1) (by norm_num) hbound ha
  rw [heatMul]
  calc wNorm r (wMul (fun n => (Real.exp (-(τ) * ((n : ℝ) * Real.pi) ^ 2) : ℂ)) a)
      ≤ 1 * wNorm r a := hmul
    _ = wNorm r a := one_mul _

/-! ### Part C — weight-monotone embedding `A^r ⊆ A^s` for `s ≤ r` -/

/-- The weight is monotone in `r` (base `1 + |n| ≥ 1`). -/
theorem wWeight_mono {s r : ℕ} (h : s ≤ r) (n : ℤ) : wWeight s n ≤ wWeight r n := by
  unfold wWeight
  refine pow_le_pow_right₀ ?_ h
  exact le_add_of_nonneg_right (abs_nonneg _)

/-- Termwise: the weighted summand is monotone in `r`. -/
private theorem wterm_mono {s r : ℕ} (h : s ≤ r) (a : ℤ → ℂ) (n : ℤ) :
    wWeight s n * ‖a n‖ ≤ wWeight r n * ‖a n‖ :=
  mul_le_mul_of_nonneg_right (wWeight_mono h n) (norm_nonneg _)

/-- **Embedding** `A^r ⊆ A^s`: if `a ∈ A^r` and `s ≤ r` then `a ∈ A^s`. -/
theorem memW_mono {s r : ℕ} (h : s ≤ r) {a : ℤ → ℂ} (ha : MemW r a) : MemW s a := by
  rw [MemW]
  refine Summable.of_nonneg_of_le
    (fun n => weightedNorm_nonneg s a n) (fun n => wterm_mono h a n) ha

/-- **Norm monotonicity** `wNorm s a ≤ wNorm r a` for `s ≤ r`. -/
theorem wNorm_mono_le {s r : ℕ} (h : s ≤ r) {a : ℤ → ℂ} (ha : MemW r a) :
    wNorm s a ≤ wNorm r a := by
  rw [wNorm, wNorm]
  exact Summable.tsum_mono (memW_mono h ha) ha (fun n => wterm_mono h a n)

end ShenWork.Wiener
