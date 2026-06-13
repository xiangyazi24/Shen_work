import ShenWork.Wiener.WeightedL1Convolution

/-!
# Two foundational operators on the weighted ℓ¹ Wiener algebra

Pure sequence algebra (no PDE, unconditional). Building on brick 1 (`wWeight`,
`MemW`, `wNorm` on `a : ℤ → ℂ`), this brick defines and bounds the two operators
that the elliptic machinery will need later:

* **Part A — the Fourier-derivative multiplier** `∂ₓ`, here `wDeriv`, sending
  `(a_n) ↦ (i π n · a_n)`. It lowers the weight by one (`W^{r+1} → W^r`) with
  `wNorm r (∂ₓ a) ≤ π · wNorm (r+1) a`. The crux is `|n| ≤ 1 + |n|`.

* **Part B — bounded pointwise multipliers** `wMul m`, sending `(a_n) ↦ (m_n a_n)`.
  If `‖m n‖ ≤ Cm` for all `n` then `wNorm r (m·a) ≤ Cm · wNorm r a`.

Both estimates are genuine (all `r`, all bounded `m`); the proofs are
`Summable.of_nonneg_of_le` + `Summable.tsum_mono` + `tsum_mul_left`.
-/

open scoped BigOperators

namespace ShenWork.Wiener

/-- The Fourier-derivative multiplier `(∂ₓ a)_n = i π n · a_n`. -/
noncomputable def wDeriv (a : ℤ → ℂ) : ℤ → ℂ :=
  fun n => (Complex.I * Real.pi * (n : ℂ)) * a n

/-- The bounded pointwise multiplier `(m · a)_n = m_n · a_n`. -/
def wMul (m a : ℤ → ℂ) : ℤ → ℂ := fun n => m n * a n

/-- `‖i π n‖ = π · |n|`. -/
private theorem norm_iPiN (n : ℤ) :
    ‖(Complex.I * Real.pi * (n : ℂ))‖ = Real.pi * |(n : ℝ)| := by
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
  have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_of_nonneg Real.pi_nonneg]
  rw [hpi, Complex.norm_intCast]

/-- The per-`n` termwise bound for `∂ₓ`:
`wWeight r n · ‖(∂ₓ a) n‖ ≤ π · (wWeight (r+1) n · ‖a n‖)`. -/
private theorem wDeriv_term_le (r : ℕ) (a : ℤ → ℂ) (n : ℤ) :
    wWeight r n * ‖wDeriv a n‖ ≤ Real.pi * (wWeight (r + 1) n * ‖a n‖) := by
  unfold wDeriv wWeight
  rw [norm_mul, norm_iPiN]
  have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_nonneg
  have habs : (0 : ℝ) ≤ |(n : ℝ)| := abs_nonneg _
  have ha : (0 : ℝ) ≤ ‖a n‖ := norm_nonneg _
  have hbase : (0 : ℝ) ≤ 1 + |(n : ℝ)| := by linarith
  have hkey : |(n : ℝ)| ≤ 1 + |(n : ℝ)| := by linarith
  have hpow : (0 : ℝ) ≤ (1 + |(n : ℝ)|) ^ r := by positivity
  rw [pow_succ]
  -- LHS: (1+|n|)^r * (π * |n| * ‖a n‖); RHS: π * ((1+|n|)^r * (1+|n|) * ‖a n‖)
  have hstep : Real.pi * |(n : ℝ)| ≤ Real.pi * (1 + |(n : ℝ)|) :=
    mul_le_mul_of_nonneg_left hkey hpi
  nlinarith [hstep, hpow, ha, mul_nonneg hpow ha,
    mul_le_mul_of_nonneg_right hstep (mul_nonneg hpow ha)]

/-- The per-`n` termwise bound for `wMul`:
`wWeight r n · ‖(m·a) n‖ ≤ Cm · (wWeight r n · ‖a n‖)`. -/
private theorem wMul_term_le {Cm : ℝ} (r : ℕ) (m a : ℤ → ℂ) (n : ℤ)
    (hm : ‖m n‖ ≤ Cm) : wWeight r n * ‖wMul m a n‖ ≤ Cm * (wWeight r n * ‖a n‖) := by
  unfold wMul
  rw [norm_mul]
  have hw : (0 : ℝ) ≤ wWeight r n := wWeight_nonneg r n
  have ha : (0 : ℝ) ≤ ‖a n‖ := norm_nonneg _
  have hstep : wWeight r n * (‖m n‖ * ‖a n‖) ≤ wWeight r n * (Cm * ‖a n‖) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm ha) hw
  calc wWeight r n * (‖m n‖ * ‖a n‖)
      ≤ wWeight r n * (Cm * ‖a n‖) := hstep
    _ = Cm * (wWeight r n * ‖a n‖) := by ring

/-- **Part A closure**: `∂ₓ` maps `W^{r+1}` into `W^r`. -/
theorem memW_wDeriv {r : ℕ} {a : ℤ → ℂ} (ha : MemW (r + 1) a) : MemW r (wDeriv a) := by
  rw [MemW]
  refine Summable.of_nonneg_of_le
    (fun n => weightedNorm_nonneg r (wDeriv a) n) (fun n => wDeriv_term_le r a n) ?_
  exact ha.mul_left Real.pi

/-- **Part A norm bound**: `wNorm r (∂ₓ a) ≤ π · wNorm (r+1) a`. -/
theorem wNorm_wDeriv_le {r : ℕ} {a : ℤ → ℂ} (ha : MemW (r + 1) a) :
    wNorm r (wDeriv a) ≤ Real.pi * wNorm (r + 1) a := by
  have hL : Summable (fun n => wWeight r n * ‖wDeriv a n‖) := memW_wDeriv ha
  have hR : Summable (fun n => Real.pi * (wWeight (r + 1) n * ‖a n‖)) := ha.mul_left Real.pi
  rw [wNorm]
  calc ∑' n, wWeight r n * ‖wDeriv a n‖
      ≤ ∑' n, Real.pi * (wWeight (r + 1) n * ‖a n‖) :=
        Summable.tsum_mono hL hR (fun n => wDeriv_term_le r a n)
    _ = Real.pi * ∑' n, wWeight (r + 1) n * ‖a n‖ := tsum_mul_left
    _ = Real.pi * wNorm (r + 1) a := by rw [wNorm]

/-- **Part B closure**: a bounded multiplier maps `W^r` into `W^r`. -/
theorem memW_wMul {r : ℕ} {m a : ℤ → ℂ} {Cm : ℝ} (hm : ∀ n, ‖m n‖ ≤ Cm)
    (ha : MemW r a) : MemW r (wMul m a) := by
  rw [MemW]
  refine Summable.of_nonneg_of_le
    (fun n => weightedNorm_nonneg r (wMul m a) n)
    (fun n => wMul_term_le r m a n (hm n)) ?_
  exact ha.mul_left Cm

/-- **Part B norm bound**: `wNorm r (m·a) ≤ Cm · wNorm r a`. -/
theorem wNorm_wMul_le {r : ℕ} {m a : ℤ → ℂ} {Cm : ℝ} (hCm : 0 ≤ Cm)
    (hm : ∀ n, ‖m n‖ ≤ Cm) (ha : MemW r a) :
    wNorm r (wMul m a) ≤ Cm * wNorm r a := by
  have hL : Summable (fun n => wWeight r n * ‖wMul m a n‖) := memW_wMul hm ha
  have hR : Summable (fun n => Cm * (wWeight r n * ‖a n‖)) := ha.mul_left Cm
  rw [wNorm]
  calc ∑' n, wWeight r n * ‖wMul m a n‖
      ≤ ∑' n, Cm * (wWeight r n * ‖a n‖) :=
        Summable.tsum_mono hL hR (fun n => wMul_term_le r m a n (hm n))
    _ = Cm * ∑' n, wWeight r n * ‖a n‖ := tsum_mul_left
    _ = Cm * wNorm r a := by rw [wNorm]

end ShenWork.Wiener
