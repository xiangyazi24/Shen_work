import ShenWork.Wiener.GWA.Convolution
import ShenWork.Wiener.WeightedL1HeatDeriv

/-!
# Generic coeffwise Fourier-multiplier operators on `GWA K r`

This file (brick E3) delivers the **master coeffwise-operator lemma**
`coeffwiseCLM`: any family of per-mode bounded operators `Op : ℤ → (K →L[ℂ] L)`
satisfying a weighted bound `gWeight s n · ‖Op n x‖ ≤ C · (gWeight r n · ‖x‖)`
assembles into a continuous linear map `GWA K r →L[ℂ] GWA L s` of norm `≤ C`.

Every diagonal Fourier multiplier is then a near one-liner via `scalarMultiplier`
(the special case `Op n = (m n) • ·`):

* `gDeriv  : GWA K (r+1) →L[ℂ] GWA K r`  — `m n = iπn`, `C = π`.
* `gResolver μ : GWA K r →L[ℂ] GWA K (r+2)` — `m n = 1/(μ+(nπ)²)`, `C = 2/μ+2/π²`.
* `gDerivResolver μ : GWA K r →L[ℂ] GWA K (r+1)` — `m n = inπ/(μ+(nπ)²)`,
  `C = 1/(2√μ)`.
* `gHeat τ : GWA K r →L[ℂ] GWA K r` — `m n = exp(−τ(nπ)²)`, `C = 1`.
* `gHeatDeriv τ : GWA K r →L[ℂ] GWA K r` — `m n = inπ·exp(−τ(nπ)²)`,
  `C = 1/√(2eτ)` (reuses the committed scalar `heatDeriv_symbol_le`).
* `incl (h : r ≤ s) : GWA K s →L[ℂ] GWA K r` — same coeffs, weight monotone.

The scalar weight-bound facts are `K`-independent (about `ℝ/ℂ` scalars and the
weights), mirroring the committed WA bricks (`WeightedL1Operators/Power/Resolver/
HeatDeriv`): `iπn` gain `|n|≤1+|n|`, resolver `+2` gain symbol, `|nπ|/(μ+(nπ)²)≤
1/(2√μ)`, heat `≤1`, and the reused `heatDeriv_symbol_le`.
-/

open scoped BigOperators

namespace ShenWork.GWA

namespace GWA

/-! ### Part A — the master coeffwise-operator lemma -/

section Master

variable {K L : Type*} [NormedCommRing K] [NormedAlgebra ℂ K] [CompleteSpace K]
  [NormedCommRing L] [NormedAlgebra ℂ L] [CompleteSpace L] {r s : ℕ}

/-- The output sequence `n ↦ Op n (a.toFun n)` is in `GMemW s`, from the weighted
operator bound, via `Summable.of_nonneg_of_le` against `C · (gWeight r · ‖a·‖)`. -/
theorem gMemW_coeffwise (Op : ℤ → (K →L[ℂ] L)) (C : ℝ)
    (hOp : ∀ n x, gWeight s n * ‖Op n x‖ ≤ C * (gWeight r n * ‖x‖))
    {a : ℤ → K} (ha : GMemW r a) :
    GMemW s (fun n => Op n (a n)) := by
  refine Summable.of_nonneg_of_le
    (fun n => by have := gWeight_nonneg s n; positivity)
    (fun n => hOp n (a n)) (ha.mul_left C)

/-- The underlying linear map `GWA K r →ₗ[ℂ] GWA L s`: coeffwise application of
`Op`, with the output membership supplied by `gMemW_coeffwise`. -/
noncomputable def coeffwiseLM (Op : ℤ → (K →L[ℂ] L)) (C : ℝ)
    (hOp : ∀ n x, gWeight s n * ‖Op n x‖ ≤ C * (gWeight r n * ‖x‖)) :
    GWA K r →ₗ[ℂ] GWA L s where
  toFun a := ⟨fun n => Op n (a.toFun n), gMemW_coeffwise Op C hOp a.mem⟩
  map_add' a b := by
    apply GWA.ext; funext n
    simp only [add_toFun, Pi.add_apply, map_add]
  map_smul' c a := by
    apply GWA.ext; funext n
    simp only [smul_toFun, Pi.smul_apply, map_smul, RingHom.id_apply]

@[simp] theorem coeffwiseLM_toFun (Op : ℤ → (K →L[ℂ] L)) (C : ℝ)
    (hOp : ∀ n x, gWeight s n * ‖Op n x‖ ≤ C * (gWeight r n * ‖x‖))
    (a : GWA K r) (n : ℤ) :
    (coeffwiseLM Op C hOp a).toFun n = Op n (a.toFun n) := rfl

/-- The norm bound `‖coeffwiseLM a‖ ≤ C · ‖a‖`, i.e. `gNorm s (Op·a) ≤ C·gNorm r a`,
proved termwise by `Summable.tsum_mono` + `tsum_mul_left`. -/
theorem norm_coeffwiseLM_le (Op : ℤ → (K →L[ℂ] L)) (C : ℝ) (hC : 0 ≤ C)
    (hOp : ∀ n x, gWeight s n * ‖Op n x‖ ≤ C * (gWeight r n * ‖x‖))
    (a : GWA K r) :
    ‖coeffwiseLM Op C hOp a‖ ≤ C * ‖a‖ := by
  have hL : GMemW s (fun n => Op n (a.toFun n)) := gMemW_coeffwise Op C hOp a.mem
  have hR : Summable (fun n => C * (gWeight r n * ‖a.toFun n‖)) := a.mem.mul_left C
  show gNorm s (coeffwiseLM Op C hOp a).toFun ≤ C * gNorm r a.toFun
  rw [gNorm, gNorm]
  calc ∑' n, gWeight s n * ‖(coeffwiseLM Op C hOp a).toFun n‖
      ≤ ∑' n, C * (gWeight r n * ‖a.toFun n‖) :=
        Summable.tsum_mono hL hR (fun n => hOp n (a.toFun n))
    _ = C * ∑' n, gWeight r n * ‖a.toFun n‖ := tsum_mul_left

/-- **The master lemma.** Any per-mode bounded family `Op` with a weighted bound
assembles into a CLM `GWA K r →L[ℂ] GWA L s` of operator norm `≤ C`. -/
noncomputable def coeffwiseCLM (Op : ℤ → (K →L[ℂ] L)) (C : ℝ) (hC : 0 ≤ C)
    (hOp : ∀ n x, gWeight s n * ‖Op n x‖ ≤ C * (gWeight r n * ‖x‖)) :
    GWA K r →L[ℂ] GWA L s :=
  (coeffwiseLM Op C hOp).mkContinuous C (norm_coeffwiseLM_le Op C hC hOp)

@[simp] theorem coeffwiseCLM_toFun (Op : ℤ → (K →L[ℂ] L)) (C : ℝ) (hC : 0 ≤ C)
    (hOp : ∀ n x, gWeight s n * ‖Op n x‖ ≤ C * (gWeight r n * ‖x‖))
    (a : GWA K r) (n : ℤ) :
    (coeffwiseCLM Op C hC hOp a).toFun n = Op n (a.toFun n) := rfl

end Master

/-! ### scalarMultiplier — the diagonal special case `Op n = (m n) • ·` -/

section Scalar

variable {K : Type*} [NormedCommRing K] [NormedAlgebra ℂ K] [CompleteSpace K]
  {r s : ℕ}

/-- A diagonal scalar Fourier multiplier `(m n) • ·` as a CLM, from the scalar
weight bound `gWeight s n · ‖m n‖ ≤ C · gWeight r n`. -/
noncomputable def scalarMultiplier (m : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ n, gWeight s n * ‖m n‖ ≤ C * gWeight r n) :
    GWA K r →L[ℂ] GWA K s :=
  coeffwiseCLM (fun n => ContinuousLinearMap.lsmul ℂ ℂ (m n)) C hC (by
    intro n x
    rw [ContinuousLinearMap.lsmul_apply, norm_smul (m n) x]
    have hx : (0 : ℝ) ≤ ‖x‖ := norm_nonneg _
    have := hm n
    calc gWeight s n * (‖m n‖ * ‖x‖)
        = (gWeight s n * ‖m n‖) * ‖x‖ := by ring
      _ ≤ (C * gWeight r n) * ‖x‖ := mul_le_mul_of_nonneg_right this hx
      _ = C * (gWeight r n * ‖x‖) := by ring)

@[simp] theorem scalarMultiplier_toFun (m : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ n, gWeight s n * ‖m n‖ ≤ C * gWeight r n) (a : GWA K r) (n : ℤ) :
    (scalarMultiplier (K := K) m C hC hm a).toFun n = m n • a.toFun n := by
  simp only [scalarMultiplier, coeffwiseCLM_toFun, ContinuousLinearMap.lsmul_apply]

end Scalar

/-! ### Part B — the operators -/

section Operators

variable {K : Type*} [NormedCommRing K] [NormedAlgebra ℂ K] [CompleteSpace K]
  {r : ℕ}

/-! #### Inclusion `GWA K s →L[ℂ] GWA K r` for `r ≤ s` (weight monotone). -/

/-- The weight is monotone in the exponent (base `1+|n| ≥ 1`). -/
theorem gWeight_mono {r s : ℕ} (h : r ≤ s) (n : ℤ) : gWeight r n ≤ gWeight s n := by
  unfold gWeight
  exact pow_le_pow_right₀ (le_add_of_nonneg_right (abs_nonneg _)) h

/-- **Inclusion** `GWA K s ↪ GWA K r` for `r ≤ s` (identity coefficients,
weight drops): a CLM of norm `≤ 1`. -/
noncomputable def incl {r s : ℕ} (h : r ≤ s) : GWA K s →L[ℂ] GWA K r :=
  scalarMultiplier (K := K) (fun _ => 1) 1 zero_le_one (by
    intro n
    rw [norm_one, mul_one, one_mul]
    exact gWeight_mono h n)

/-! #### `gDeriv : GWA K (r+1) →L[ℂ] GWA K r` — `m n = iπn`, `C = π`. -/

/-- `‖iπn‖ = π·|n|`. -/
theorem norm_iPiN (n : ℤ) :
    ‖(Complex.I * Real.pi * (n : ℂ))‖ = Real.pi * |(n : ℝ)| := by
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
  have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_of_nonneg Real.pi_nonneg]
  rw [hpi, Complex.norm_intCast]

/-- **Fourier derivative** `(∂ₓ a)_n = iπn·a_n`, `GWA K (r+1) → GWA K r`, `C = π`. -/
noncomputable def gDeriv : GWA K (r + 1) →L[ℂ] GWA K r :=
  scalarMultiplier (K := K) (fun n => Complex.I * Real.pi * (n : ℂ))
    Real.pi Real.pi_nonneg (by
    intro n
    rw [norm_iPiN]
    unfold gWeight
    have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_nonneg
    have habs : (0 : ℝ) ≤ |(n : ℝ)| := abs_nonneg _
    have hpow : (0 : ℝ) ≤ (1 + |(n : ℝ)|) ^ r := by positivity
    rw [pow_succ]
    nlinarith [hpi, habs, hpow])

/-! #### `gResolver μ : GWA K r →L[ℂ] GWA K (r+2)` — resolver `+2` gain. -/

/-- The explicit resolver gain constant `C_μ = 2/μ + 2/π²`. -/
noncomputable def resolverGainConst (μ : ℝ) : ℝ := 2 / μ + 2 / Real.pi ^ 2

/-- The resolver symbol `1/(μ+(nπ)²)` is nonnegative, with complex norm equal to
itself. -/
theorem resolverSymbol_norm {μ : ℝ} (hμ : 0 < μ) (n : ℤ) :
    ‖((1 / (μ + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ)‖
      = 1 / (μ + ((n : ℝ) * Real.pi) ^ 2) := by
  have hd : 0 < μ + ((n : ℝ) * Real.pi) ^ 2 := by positivity
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-- The gain-symbol bound `(1+|n|)²/(μ+(nπ)²) ≤ C_μ` (`K`-independent; mirrors the
committed WA `gain_symbol_le`). -/
theorem gain_symbol_le {μ : ℝ} (hμ : 0 < μ) (n : ℤ) :
    (1 + |(n : ℝ)|) ^ 2 * (1 / (μ + ((n : ℝ) * Real.pi) ^ 2))
      ≤ resolverGainConst μ := by
  unfold resolverGainConst
  have hd : 0 < μ + ((n : ℝ) * Real.pi) ^ 2 := by positivity
  have hpi2 : 0 < Real.pi ^ 2 := by positivity
  rw [mul_one_div, div_le_iff₀ hd]
  have habs : |(n : ℝ)| ^ 2 = (n : ℝ) ^ 2 := sq_abs _
  have hmul : ((n : ℝ) * Real.pi) ^ 2 = (n : ℝ) ^ 2 * Real.pi ^ 2 := by ring
  rw [hmul]
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

/-- **Elliptic resolver** `(R_μ a)_n = a_n/(μ+(nπ)²)`, the `+2` smoothing
`GWA K r → GWA K (r+2)`, `C = C_μ = 2/μ+2/π²`. -/
noncomputable def gResolver (μ : ℝ) (hμ : 0 < μ) : GWA K r →L[ℂ] GWA K (r + 2) :=
  scalarMultiplier (K := K)
    (fun n => ((1 / (μ + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ))
    (resolverGainConst μ) (by unfold resolverGainConst; positivity) (by
    intro n
    rw [resolverSymbol_norm hμ n]
    unfold gWeight
    have hpow : (0 : ℝ) ≤ (1 + |(n : ℝ)|) ^ r := by positivity
    have hg := gain_symbol_le (μ := μ) hμ n
    rw [pow_add]
    calc (1 + |(n : ℝ)|) ^ r * (1 + |(n : ℝ)|) ^ 2
          * (1 / (μ + ((n : ℝ) * Real.pi) ^ 2))
        = (1 + |(n : ℝ)|) ^ r
            * ((1 + |(n : ℝ)|) ^ 2 * (1 / (μ + ((n : ℝ) * Real.pi) ^ 2))) := by
          ring
      _ ≤ (1 + |(n : ℝ)|) ^ r * resolverGainConst μ :=
          mul_le_mul_of_nonneg_left hg hpow
      _ = resolverGainConst μ * (1 + |(n : ℝ)|) ^ r := by ring)

/-! #### `gDerivResolver μ : GWA K r →L[ℂ] GWA K (r+1)` — `C = 1/(2√μ)`. -/

/-- AM-GM symbol bound `|nπ|/(μ+(nπ)²) ≤ 1/(2√μ)` (`K`-independent; mirrors the
committed WA `derivSymbol_le`). -/
theorem derivResolverSymbol_le {μ : ℝ} (hμ : 0 < μ) (n : ℤ) :
    ‖(Complex.I * ((n : ℝ) * Real.pi : ℝ))
        * ((1 / (μ + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ)‖
      ≤ 1 / (2 * Real.sqrt μ) := by
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, resolverSymbol_norm hμ n,
    Complex.norm_real]
  have hd : 0 < μ + ((n : ℝ) * Real.pi) ^ 2 := by positivity
  have hsμ : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  set t : ℝ := (n : ℝ) * Real.pi with ht
  have hsq : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt (le_of_lt hμ)
  rw [Real.norm_eq_abs, mul_one_div, div_le_div_iff₀ hd (by positivity)]
  have hkey : (0 : ℝ) ≤ (|t| - Real.sqrt μ) ^ 2 := sq_nonneg _
  have habst : |t| ^ 2 = t ^ 2 := sq_abs _
  nlinarith [hkey, habst, hsq, hsμ]

/-- The derivative-resolver constant `1/(2√μ) + 1/π` (the `+1` weight version: the
extra `(1+|n|)` factor costs an extra `1/π`). -/
noncomputable def derivResolverConst (μ : ℝ) : ℝ := 1 / (2 * Real.sqrt μ) + 1 / Real.pi

/-- The weighted derivative-resolver symbol bound
`(1+|n|)·|nπ|/(μ+(nπ)²) ≤ 1/(2√μ)+1/π`.  Splits as `|nπ|/(μ+(nπ)²) ≤ 1/(2√μ)`
(AM-GM) plus `|n|·|nπ|/(μ+(nπ)²) ≤ (nπ)²/(π(μ+(nπ)²)) ≤ 1/π`. -/
theorem derivResolverWeightedSymbol_le {μ : ℝ} (hμ : 0 < μ) (n : ℤ) :
    (1 + |(n : ℝ)|) * ‖(Complex.I * ((n : ℝ) * Real.pi : ℝ))
        * ((1 / (μ + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ)‖
      ≤ derivResolverConst μ := by
  unfold derivResolverConst
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, resolverSymbol_norm hμ n,
    Complex.norm_real, Real.norm_eq_abs]
  have hd : 0 < μ + ((n : ℝ) * Real.pi) ^ 2 := by positivity
  have hsμ : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsq : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt (le_of_lt hμ)
  have habsn : |(n : ℝ)| * Real.pi = |(n : ℝ) * Real.pi| := by
    rw [abs_mul, abs_of_nonneg Real.pi_pos.le]
  set t : ℝ := (n : ℝ) * Real.pi with ht
  -- Split target: (1+|n|)·|t|·(1/(μ+t²)) ≤ 1/(2√μ) + 1/π.
  have hbound1 : |t| * (1 / (μ + t ^ 2)) ≤ 1 / (2 * Real.sqrt μ) := by
    rw [mul_one_div, div_le_div_iff₀ hd (by positivity)]
    nlinarith [sq_nonneg (|t| - Real.sqrt μ), sq_abs t, hsq, hsμ]
  have hbound2 : |(n : ℝ)| * (|t| * (1 / (μ + t ^ 2))) ≤ 1 / Real.pi := by
    have htabs : |(n : ℝ)| * |t| = t ^ 2 / Real.pi := by
      rw [← habsn, ht]
      have hnn : (0 : ℝ) ≤ |(n : ℝ)| := abs_nonneg _
      have h2 : |(n : ℝ)| ^ 2 = (n : ℝ) ^ 2 := sq_abs _
      field_simp
      nlinarith [h2, hpi]
    have heq : |(n : ℝ)| * (|t| * (1 / (μ + t ^ 2)))
        = (|(n : ℝ)| * |t|) / (μ + t ^ 2) := by ring
    rw [heq, htabs, div_div, div_le_div_iff₀ (by positivity) hpi, one_mul]
    have ht2 : (0 : ℝ) ≤ t ^ 2 := sq_nonneg _
    nlinarith [ht2, hμ, hpi]
  have hexpand : (1 + |(n : ℝ)|) * (|t| * (1 / (μ + t ^ 2)))
      = |t| * (1 / (μ + t ^ 2)) + |(n : ℝ)| * (|t| * (1 / (μ + t ^ 2))) := by ring
  rw [hexpand]
  linarith [hbound1, hbound2]

/-- **Derivative-resolver** `(∂ₓR_μ a)_n = (inπ)/(μ+(nπ)²)·a_n`,
`GWA K r → GWA K (r+1)`, `C = 1/(2√μ) + 1/π` (the `+1` weight costs the extra
`1/π`; same `inπ/(μ+(nπ)²)` symbol as the WA `derivResolverMul`). -/
noncomputable def gDerivResolver (μ : ℝ) (hμ : 0 < μ) :
    GWA K r →L[ℂ] GWA K (r + 1) :=
  scalarMultiplier (K := K)
    (fun n => Complex.I * ((n : ℝ) * Real.pi : ℝ)
      * ((1 / (μ + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ))
    (derivResolverConst μ) (by
      have hsμ : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
      have hpi : 0 < Real.pi := Real.pi_pos
      unfold derivResolverConst; positivity) (by
    intro n
    have hb := derivResolverWeightedSymbol_le (μ := μ) hμ n
    have hw1 : gWeight (r + 1) n = gWeight r n * (1 + |(n : ℝ)|) := by
      unfold gWeight; rw [pow_succ]
    have hwr : (0 : ℝ) ≤ gWeight r n := gWeight_nonneg r n
    rw [hw1]
    calc gWeight r n * (1 + |(n : ℝ)|)
          * ‖(Complex.I * ((n : ℝ) * Real.pi : ℝ))
            * ((1 / (μ + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ)‖
        = gWeight r n * ((1 + |(n : ℝ)|)
            * ‖(Complex.I * ((n : ℝ) * Real.pi : ℝ))
              * ((1 / (μ + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ)‖) := by ring
      _ ≤ gWeight r n * derivResolverConst μ :=
          mul_le_mul_of_nonneg_left hb hwr
      _ = derivResolverConst μ * gWeight r n := by ring)

/-! #### `gHeat τ : GWA K r →L[ℂ] GWA K r` — `m n = exp(−τ(nπ)²)`, `C = 1`. -/

/-- **Heat semigroup** `(S(τ)a)_n = exp(−τ(nπ)²)·a_n`, the same-weight contraction
`GWA K r → GWA K r`, `C = 1`. -/
noncomputable def gHeat (τ : ℝ) (hτ : 0 ≤ τ) : GWA K r →L[ℂ] GWA K r :=
  scalarMultiplier (K := K)
    (fun n => (Real.exp (-(τ) * ((n : ℝ) * Real.pi) ^ 2) : ℂ))
    1 zero_le_one (by
    intro n
    rw [one_mul]
    have hsymb : ‖(Real.exp (-(τ) * ((n : ℝ) * Real.pi) ^ 2) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _),
        Real.exp_le_one_iff]
      have hsq : (0 : ℝ) ≤ ((n : ℝ) * Real.pi) ^ 2 := sq_nonneg _
      nlinarith [hτ, hsq]
    calc gWeight r n * ‖(Real.exp (-(τ) * ((n : ℝ) * Real.pi) ^ 2) : ℂ)‖
        ≤ gWeight r n * 1 := mul_le_mul_of_nonneg_left hsymb (gWeight_nonneg r n)
      _ = gWeight r n := mul_one _)

/-! #### `gHeatDeriv τ : GWA K r →L[ℂ] GWA K r` — reuse committed `heatDeriv_symbol_le`. -/

/-- **Heat-derivative** `(S(τ)∂ₓ a)_n = inπ·exp(−τ(nπ)²)·a_n`, the `t^{-1/2}`
divergence smoothing `GWA K r → GWA K r`, `C = 1/√(2eτ)`.  Reuses the committed
scalar bound `ShenWork.Wiener.heatDeriv_symbol_le`. -/
noncomputable def gHeatDeriv (τ : ℝ) (hτ : 0 < τ) : GWA K r →L[ℂ] GWA K r :=
  scalarMultiplier (K := K)
    (fun n => (Complex.I * ((n : ℝ) * Real.pi)
      * Real.exp (-(τ) * ((n : ℝ) * Real.pi) ^ 2) : ℂ))
    (1 / Real.sqrt (2 * Real.exp 1 * τ)) (by positivity) (by
    intro n
    have hb := ShenWork.Wiener.heatDeriv_symbol_le (τ := τ) hτ n
    have hC : (0 : ℝ) ≤ 1 / Real.sqrt (2 * Real.exp 1 * τ) := by positivity
    calc gWeight r n * ‖(Complex.I * ((n : ℝ) * Real.pi)
          * Real.exp (-(τ) * ((n : ℝ) * Real.pi) ^ 2) : ℂ)‖
        ≤ gWeight r n * (1 / Real.sqrt (2 * Real.exp 1 * τ)) :=
          mul_le_mul_of_nonneg_left hb (gWeight_nonneg r n)
      _ = (1 / Real.sqrt (2 * Real.exp 1 * τ)) * gWeight r n := by ring)

end Operators

/-! ### Sanity tests -/

/-- The derivative CLM fires on a concrete instance. -/
noncomputable example : GWA ℂ 2 →L[ℂ] GWA ℂ 1 := gDeriv

end GWA

end ShenWork.GWA
