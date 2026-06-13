import ShenWork.Wiener.WeightedL1Operators
import ShenWork.Wiener.WeightedL1Power

/-!
# Wiener brick 3c — the elliptic resolver as a weight-GAINING multiplier on `A^r`

Pure sequence algebra (no PDE, unconditional). The Neumann resolvent
`R_μ = (μ − ∂ₓₓ)^{−1}` is diagonal in the Fourier basis with multiplier
`m_μ(n) = 1/(μ + (nπ)²)`. We define `resolverMul μ` as this pointwise multiplier
and prove two estimates:

* **Part A — same-weight bound** `‖R_μ a‖_{A^r} ≤ (1/μ) ‖a‖_{A^r}` for `μ > 0`,
  since `0 ≤ 1/(μ+(nπ)²) ≤ 1/μ`.

* **Part B — the `+2` weight GAIN** `‖R_μ a‖_{A^{r+2}} ≤ C_μ ‖a‖_{A^r}`, the
  resolver-SMOOTHING that lets `v = R_μ(ν u^γ)` sit two weights smoother than the
  source `u^γ` (the regularity gain that closes the fixed point). The gain symbol
  `g_μ(n) = (1+|n|)²/(μ+(nπ)²)` is bounded by the EXPLICIT finite constant

      C_μ = 2/μ + 2/π² ,

  derived termwise from `(1+|n|)² = 1 + 2|n| + n²`, `2|n| ≤ 1 + n²` (AM-GM
  `(|n|−1)² ≥ 0`), `n²/(μ+π²n²) ≤ 1/π²`, and `1/(μ+π²n²) ≤ 1/μ`.

* **Part C — the `∂ₓR_μ` same-weight bound** `‖∂ₓR_μ a‖_{A^r} ≤ (1/(2√μ)) ‖a‖_{A^r}`,
  the multiplier `(inπ)/(μ+(nπ)²)` bounded by `1/(2√μ)` via AM-GM `(|nπ|−√μ)² ≥ 0`.
-/

open scoped BigOperators

namespace ShenWork.Wiener

/-- The elliptic resolvent multiplier `(R_μ a)_n = a_n / (μ + (nπ)²)`. -/
noncomputable def resolverMul (μ : ℝ) (a : ℤ → ℂ) : ℤ → ℂ :=
  wMul (fun n => ((1 / (μ + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ)) a

/-- The denominator `μ + (nπ)²` is `≥ μ > 0`. -/
private theorem denom_pos {μ : ℝ} (hμ : 0 < μ) (n : ℤ) :
    0 < μ + ((n : ℝ) * Real.pi) ^ 2 := by
  have h : (0 : ℝ) ≤ ((n : ℝ) * Real.pi) ^ 2 := sq_nonneg _
  linarith

/-- The resolver symbol is nonnegative. -/
private theorem symbol_nonneg {μ : ℝ} (hμ : 0 < μ) (n : ℤ) :
    (0 : ℝ) ≤ 1 / (μ + ((n : ℝ) * Real.pi) ^ 2) :=
  le_of_lt (by have := denom_pos hμ n; positivity)

/-- The complex norm of the resolver symbol equals the real symbol. -/
private theorem symbol_norm {μ : ℝ} (hμ : 0 < μ) (n : ℤ) :
    ‖((1 / (μ + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ)‖
      = 1 / (μ + ((n : ℝ) * Real.pi) ^ 2) := by
  rw [Complex.norm_real, Real.norm_of_nonneg (symbol_nonneg hμ n)]

/-! ### Part A — same-weight bound `‖R_μ a‖_{A^r} ≤ (1/μ) ‖a‖_{A^r}` -/

/-- The resolver symbol is bounded by `1/μ` (denominator `≥ μ`). -/
private theorem symbol_le_inv {μ : ℝ} (hμ : 0 < μ) (n : ℤ) :
    ‖((1 / (μ + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ)‖ ≤ 1 / μ := by
  rw [symbol_norm hμ n]
  have hsq : (0 : ℝ) ≤ ((n : ℝ) * Real.pi) ^ 2 := sq_nonneg _
  exact one_div_le_one_div_of_le hμ (by linarith)

/-- **Part A (membership)**: `R_μ` maps `A^r` into `A^r`. -/
theorem memW_resolverMul {r : ℕ} {a : ℤ → ℂ} {μ : ℝ} (hμ : 0 < μ)
    (ha : MemW r a) : MemW r (resolverMul μ a) :=
  memW_wMul (fun n => symbol_le_inv hμ n) ha

/-- **Part A (norm bound)**: `‖R_μ a‖_{A^r} ≤ (1/μ) ‖a‖_{A^r}`. -/
theorem resolverMul_bound {r : ℕ} {a : ℤ → ℂ} {μ : ℝ} (hμ : 0 < μ)
    (ha : MemW r a) : wNorm r (resolverMul μ a) ≤ (1 / μ) * wNorm r a :=
  wNorm_wMul_le (by positivity) (fun n => symbol_le_inv hμ n) ha

/-! ### Part B — the `+2` weight GAIN `‖R_μ a‖_{A^{r+2}} ≤ C_μ ‖a‖_{A^r}` -/

/-- The explicit gain constant `C_μ = 2/μ + 2/π²`. -/
noncomputable def resolverGainConst (μ : ℝ) : ℝ := 2 / μ + 2 / Real.pi ^ 2

/-- `wWeight (r+2) n = wWeight r n · (1+|n|)²`. -/
private theorem wWeight_add_two (r : ℕ) (n : ℤ) :
    wWeight (r + 2) n = wWeight r n * (1 + |(n : ℝ)|) ^ 2 := by
  unfold wWeight; rw [pow_add]

/-- **The gain-symbol bound** `g_μ(n) = (1+|n|)²/(μ+(nπ)²) ≤ C_μ = 2/μ + 2/π²`.
This is the genuine explicit-constant inequality, cleared through the positive
denominator and discharged by `nlinarith` from `(|n|−1)² ≥ 0`, `(nπ)² = π²n²`,
and `μ, π² > 0`. -/
private theorem gain_symbol_le {μ : ℝ} (hμ : 0 < μ) (n : ℤ) :
    (1 + |(n : ℝ)|) ^ 2 * (1 / (μ + ((n : ℝ) * Real.pi) ^ 2))
      ≤ resolverGainConst μ := by
  unfold resolverGainConst
  have hd : 0 < μ + ((n : ℝ) * Real.pi) ^ 2 := denom_pos hμ n
  have hpi2 : 0 < Real.pi ^ 2 := by positivity
  have hpiμ : 0 < μ * Real.pi ^ 2 := by positivity
  rw [mul_one_div, div_le_iff₀ hd]
  have habs : |(n : ℝ)| ^ 2 = (n : ℝ) ^ 2 := sq_abs _
  have hmul : ((n : ℝ) * Real.pi) ^ 2 = (n : ℝ) ^ 2 * Real.pi ^ 2 := by ring
  rw [hmul]
  -- Goal: (1+|n|)² ≤ (2/μ + 2/π²) * (μ + n²·π²)
  have hsq : (0 : ℝ) ≤ (|(n : ℝ)| - 1) ^ 2 := sq_nonneg _
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have hkey : (2 / μ + 2 / Real.pi ^ 2) * (μ + (n : ℝ) ^ 2 * Real.pi ^ 2)
      = 2 + 2 / μ * ((n : ℝ) ^ 2 * Real.pi ^ 2) + 2 / Real.pi ^ 2 * μ
        + 2 * (n : ℝ) ^ 2 := by
    field_simp; ring
  rw [hkey]
  have hA : (0 : ℝ) ≤ 2 / μ * ((n : ℝ) ^ 2 * Real.pi ^ 2) := by positivity
  have hB : (0 : ℝ) ≤ 2 / Real.pi ^ 2 * μ := by positivity
  nlinarith [hsq, habs, hA, hB, hn2]

/-- The per-`n` termwise gain bound:
`wWeight (r+2) n · ‖R_μ a n‖ ≤ C_μ · (wWeight r n · ‖a n‖)`. -/
private theorem resolver_gain_term_le {r : ℕ} {μ : ℝ} (hμ : 0 < μ)
    (a : ℤ → ℂ) (n : ℤ) :
    wWeight (r + 2) n * ‖resolverMul μ a n‖
      ≤ resolverGainConst μ * (wWeight r n * ‖a n‖) := by
  unfold resolverMul wMul
  rw [norm_mul, symbol_norm hμ n, wWeight_add_two r n]
  have hw : (0 : ℝ) ≤ wWeight r n := wWeight_nonneg r n
  have ha : (0 : ℝ) ≤ ‖a n‖ := norm_nonneg _
  have hg := gain_symbol_le (μ := μ) hμ n
  -- LHS = (wWeight r n · ‖a n‖) · [ (1+|n|)² · symbol ]  ≤  (·) · C_μ
  calc wWeight r n * (1 + |(n : ℝ)|) ^ 2
        * (1 / (μ + ((n : ℝ) * Real.pi) ^ 2) * ‖a n‖)
      = ((1 + |(n : ℝ)|) ^ 2 * (1 / (μ + ((n : ℝ) * Real.pi) ^ 2)))
          * (wWeight r n * ‖a n‖) := by ring
    _ ≤ resolverGainConst μ * (wWeight r n * ‖a n‖) :=
        mul_le_mul_of_nonneg_right hg (mul_nonneg hw ha)

/-- **Part B (membership)**: `R_μ` maps `A^r` into `A^{r+2}` (the `+2` smoothing). -/
theorem resolverMul_gain {r : ℕ} {a : ℤ → ℂ} {μ : ℝ} (hμ : 0 < μ)
    (ha : MemW r a) : MemW (r + 2) (resolverMul μ a) := by
  rw [MemW]
  refine Summable.of_nonneg_of_le
    (fun n => weightedNorm_nonneg (r + 2) (resolverMul μ a) n)
    (fun n => resolver_gain_term_le hμ a n) ?_
  exact ha.mul_left (resolverGainConst μ)

/-- **Part B (norm bound)** — the resolver smoothing:
`‖R_μ a‖_{A^{r+2}} ≤ C_μ ‖a‖_{A^r}` with `C_μ = 2/μ + 2/π²`. -/
theorem resolverMul_gain_bound {r : ℕ} {a : ℤ → ℂ} {μ : ℝ} (hμ : 0 < μ)
    (ha : MemW r a) :
    wNorm (r + 2) (resolverMul μ a) ≤ resolverGainConst μ * wNorm r a := by
  have hL : Summable (fun n => wWeight (r + 2) n * ‖resolverMul μ a n‖) :=
    resolverMul_gain hμ ha
  have hR : Summable (fun n => resolverGainConst μ * (wWeight r n * ‖a n‖)) :=
    ha.mul_left (resolverGainConst μ)
  rw [wNorm]
  calc ∑' n, wWeight (r + 2) n * ‖resolverMul μ a n‖
      ≤ ∑' n, resolverGainConst μ * (wWeight r n * ‖a n‖) :=
        Summable.tsum_mono hL hR (fun n => resolver_gain_term_le hμ a n)
    _ = resolverGainConst μ * ∑' n, wWeight r n * ‖a n‖ := tsum_mul_left
    _ = resolverGainConst μ * wNorm r a := by rw [wNorm]

/-! ### Part C — the `∂ₓR_μ` same-weight bound `‖∂ₓR_μ a‖_{A^r} ≤ (1/(2√μ)) ‖a‖_{A^r}` -/

/-- The first-derivative resolver multiplier `(∂ₓR_μ a)_n = (inπ)/(μ+(nπ)²) · a_n`. -/
noncomputable def derivResolverMul (μ : ℝ) (a : ℤ → ℂ) : ℤ → ℂ :=
  wMul (fun n => (Complex.I * ((n : ℝ) * Real.pi : ℝ))
    * ((1 / (μ + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ)) a

/-- AM-GM: `|nπ|/(μ+(nπ)²) ≤ 1/(2√μ)` from `(|nπ| − √μ)² ≥ 0`. -/
private theorem derivSymbol_le {μ : ℝ} (hμ : 0 < μ) (n : ℤ) :
    ‖(Complex.I * ((n : ℝ) * Real.pi : ℝ))
        * ((1 / (μ + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ)‖
      ≤ 1 / (2 * Real.sqrt μ) := by
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, symbol_norm hμ n,
    Complex.norm_real]
  have hd : 0 < μ + ((n : ℝ) * Real.pi) ^ 2 := denom_pos hμ n
  have hsμ : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  set t : ℝ := (n : ℝ) * Real.pi with ht
  have hsq : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt (le_of_lt hμ)
  -- ‖t‖ = |t|; goal |t| · (1/(μ+t²)) ≤ 1/(2√μ)
  rw [Real.norm_eq_abs]
  rw [mul_one_div, div_le_div_iff₀ hd (by positivity)]
  -- |t| · (2√μ) ≤ μ + t²
  have hkey : (0 : ℝ) ≤ (|t| - Real.sqrt μ) ^ 2 := sq_nonneg _
  have habst : |t| ^ 2 = t ^ 2 := sq_abs _
  nlinarith [hkey, habst, hsq, hsμ]

/-- **Part C (membership)**: `∂ₓR_μ` maps `A^r` into `A^r`. -/
theorem memW_derivResolverMul {r : ℕ} {a : ℤ → ℂ} {μ : ℝ} (hμ : 0 < μ)
    (ha : MemW r a) : MemW r (derivResolverMul μ a) :=
  memW_wMul (fun n => derivSymbol_le hμ n) ha

/-- **Part C (norm bound)**: `‖∂ₓR_μ a‖_{A^r} ≤ (1/(2√μ)) ‖a‖_{A^r}`. -/
theorem derivResolverMul_bound {r : ℕ} {a : ℤ → ℂ} {μ : ℝ} (hμ : 0 < μ)
    (ha : MemW r a) :
    wNorm r (derivResolverMul μ a) ≤ (1 / (2 * Real.sqrt μ)) * wNorm r a := by
  have hsμ : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  exact wNorm_wMul_le (by positivity) (fun n => derivSymbol_le hμ n) ha

end ShenWork.Wiener
