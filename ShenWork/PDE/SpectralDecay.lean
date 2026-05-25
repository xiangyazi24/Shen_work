/-
  ShenWork/PDE/SpectralDecay.lean

  H3.1 spectral-gap subblock for the Neumann heat semigroup on an interval.

  Mathlib currently does not provide the concrete Neumann heat semigroup on
  `[0,L]`, its cosine-basis diagonalization, and the corresponding bounded
  operator norm statement as a ready-made theorem.  This file proves the
  coefficient Hilbert-space estimate supplied by that diagonalization: after
  removing the zero mode, the multiplier `exp (-λ_n t)` is bounded by
  `exp (-(π/L)^2 t)` in `ℓ²`.
-/
import ShenWork.Paper3.Statements

noncomputable section

namespace ShenWork.PDE.SpectralDecay

open ShenWork.Paper3

/-! ### Interval Neumann spectrum -/

/-- Neumann eigenvalue `λ_n = (nπ/L)^2` on the interval of length `L`. -/
def intervalNeumannEigenvalue (L : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * Real.pi / L) ^ 2

/-- The first nonzero Neumann eigenvalue on an interval of length `L`. -/
def intervalNeumannFirstNonzero (L : ℝ) : ℝ :=
  (Real.pi / L) ^ 2

/-- Spectral data for the one-dimensional Neumann interval of length `L`. -/
def intervalNeumannSpectrum (L : ℝ) : SpectralData where
  eigenvalue := intervalNeumannEigenvalue L
  firstNonzero := intervalNeumannFirstNonzero L

theorem intervalNeumannSpectrum_firstNonzero (L : ℝ) :
    (intervalNeumannSpectrum L).firstNonzero = (Real.pi / L) ^ 2 := by
  rfl

theorem intervalNeumannSpectrum_eigenvalue (L : ℝ) (n : ℕ) :
    (intervalNeumannSpectrum L).eigenvalue n =
      ((n : ℝ) * Real.pi / L) ^ 2 := by
  rfl

/-- For `0 < L`, the interval spectrum has first nonzero eigenvalue
`(π/L)^2`. -/
theorem intervalNeumannSpectrum_hasNeumannSpectrum {L : ℝ} (hL : 0 < L) :
    HasNeumannSpectrum (intervalNeumannSpectrum L) := by
  have hfreq_pos : 0 < Real.pi / L := div_pos Real.pi_pos hL
  refine
    { zero_eigenvalue := ?_
      eigenvalue_nonneg := ?_
      eigenvalue_pos_of_ne_zero := ?_
      firstNonzero_pos := ?_
      firstNonzero_le_eigenvalue := ?_ }
  · simp [intervalNeumannSpectrum, intervalNeumannEigenvalue]
  · intro n
    exact sq_nonneg _
  · intro n hn
    have hn_real : (n : ℝ) ≠ 0 := by
      exact_mod_cast hn
    have hmul_ne : (n : ℝ) * Real.pi / L ≠ 0 := by
      exact div_ne_zero (mul_ne_zero hn_real (ne_of_gt Real.pi_pos)) (ne_of_gt hL)
    exact sq_pos_of_ne_zero hmul_ne
  · exact sq_pos_of_ne_zero (ne_of_gt hfreq_pos)
  · intro n hn
    have hn_nat : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
    have hn_real : (1 : ℝ) ≤ n := by
      exact_mod_cast hn_nat
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    have hle_freq :
        Real.pi / L ≤ (n : ℝ) * (Real.pi / L) :=
      calc
        Real.pi / L = (1 : ℝ) * (Real.pi / L) := by ring
        _ ≤ (n : ℝ) * (Real.pi / L) :=
          mul_le_mul_of_nonneg_right hn_real hfreq_pos.le
    have hright_nonneg : 0 ≤ (n : ℝ) * (Real.pi / L) :=
      mul_nonneg hn_nonneg hfreq_pos.le
    have hsquare :
        (Real.pi / L) ^ 2 ≤ ((n : ℝ) * (Real.pi / L)) ^ 2 :=
      (sq_le_sq₀ hfreq_pos.le hright_nonneg).mpr hle_freq
    simpa [intervalNeumannSpectrum, intervalNeumannEigenvalue,
      intervalNeumannFirstNonzero, mul_div_assoc] using hsquare

/-! ### Coefficient `ℓ²` semigroup estimate -/

/-- Coefficient `ℓ²` energy. -/
def coeffL2Energy (a : ℕ → ℂ) : ℝ :=
  ∑' n : ℕ, ‖a n‖ ^ 2

/-- Coefficient `ℓ²` norm. -/
def coeffL2Norm (a : ℕ → ℂ) : ℝ :=
  Real.sqrt (coeffL2Energy a)

/-- Coefficient model of the projection `I - P₀`: remove the constant mode. -/
def removeZeroMode (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else a n

/-- Coefficient model of `e^{tA}`, where `A` has eigenvalues `-λ_n`. -/
def neumannSemigroupCoeff (S : SpectralData) (t : ℝ)
    (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (Real.exp (-(S.eigenvalue n) * t) : ℂ) * a n

theorem coeffL2Energy_nonneg (a : ℕ → ℂ) :
    0 ≤ coeffL2Energy a := by
  exact tsum_nonneg fun n => sq_nonneg _

theorem coeffL2Norm_nonneg (a : ℕ → ℂ) :
    0 ≤ coeffL2Norm a := by
  exact Real.sqrt_nonneg _

theorem coeffL2Norm_sq (a : ℕ → ℂ) :
    coeffL2Norm a ^ 2 = coeffL2Energy a := by
  simpa [coeffL2Norm, pow_two] using Real.sq_sqrt (coeffL2Energy_nonneg a)

theorem removeZeroMode_zero (a : ℕ → ℂ) :
    removeZeroMode a 0 = 0 := by
  simp [removeZeroMode]

theorem removeZeroMode_of_ne_zero {a : ℕ → ℂ} {n : ℕ} (hn : n ≠ 0) :
    removeZeroMode a n = a n := by
  simp [removeZeroMode, hn]

theorem removeZeroMode_sq_le (a : ℕ → ℂ) (n : ℕ) :
    ‖removeZeroMode a n‖ ^ 2 ≤ ‖a n‖ ^ 2 := by
  by_cases hn : n = 0
  · simp [removeZeroMode, hn]
  · simp [removeZeroMode, hn]

theorem removeZeroMode_l2_summable {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    Summable fun n : ℕ => ‖removeZeroMode a n‖ ^ 2 := by
  apply Summable.of_nonneg_of_le
    (fun n => sq_nonneg _)
    ?_
    ha
  intro n
  exact removeZeroMode_sq_le a n

theorem removeZeroMode_l2_energy_le {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    coeffL2Energy (removeZeroMode a) ≤ coeffL2Energy a := by
  have hremove := removeZeroMode_l2_summable ha
  have hle : ∀ n : ℕ, ‖removeZeroMode a n‖ ^ 2 ≤ ‖a n‖ ^ 2 :=
    removeZeroMode_sq_le a
  have htsum := hremove.tsum_le_tsum hle ha
  simpa [coeffL2Energy] using htsum

theorem removeZeroMode_l2_norm_le {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    coeffL2Norm (removeZeroMode a) ≤ coeffL2Norm a := by
  have henergy := removeZeroMode_l2_energy_le ha
  refine (sq_le_sq₀ (coeffL2Norm_nonneg _) (coeffL2Norm_nonneg _)).mp ?_
  simpa [coeffL2Norm_sq] using henergy

/-- Pointwise squared multiplier estimate on the zero-mean subspace. -/
theorem neumannSemigroupCoeff_removeZero_sq_le
    {S : SpectralData} (H : HasNeumannSpectrum S) {t : ℝ} (ht : 0 ≤ t)
    (a : ℕ → ℂ) (n : ℕ) :
    ‖neumannSemigroupCoeff S t (removeZeroMode a) n‖ ^ 2 ≤
      (Real.exp (-S.firstNonzero * t)) ^ 2 * ‖removeZeroMode a n‖ ^ 2 := by
  by_cases hn : n = 0
  · simp [neumannSemigroupCoeff, removeZeroMode, hn]
  · have hLambda : S.firstNonzero ≤ S.eigenvalue n :=
      H.firstNonzero_le_eigenvalue n hn
    have hmul0 : S.firstNonzero * t ≤ S.eigenvalue n * t :=
      mul_le_mul_of_nonneg_right hLambda ht
    have hmul : -(S.eigenvalue n) * t ≤ -S.firstNonzero * t := by
      linarith
    have hexp_le :
        Real.exp (-(S.eigenvalue n) * t) ≤
          Real.exp (-S.firstNonzero * t) :=
      Real.exp_le_exp.mpr hmul
    have hexp_nonneg : 0 ≤ Real.exp (-(S.eigenvalue n) * t) :=
      Real.exp_nonneg _
    have hfirst_nonneg : 0 ≤ Real.exp (-S.firstNonzero * t) :=
      Real.exp_nonneg _
    have hnorm_nonneg : 0 ≤ ‖removeZeroMode a n‖ := norm_nonneg _
    have hle :
        Real.exp (-(S.eigenvalue n) * t) * ‖removeZeroMode a n‖ ≤
          Real.exp (-S.firstNonzero * t) * ‖removeZeroMode a n‖ :=
      mul_le_mul_of_nonneg_right hexp_le hnorm_nonneg
    calc
      ‖neumannSemigroupCoeff S t (removeZeroMode a) n‖ ^ 2
          =
            (Real.exp (-(S.eigenvalue n) * t) *
              ‖removeZeroMode a n‖) ^ 2 := by
              rw [neumannSemigroupCoeff, norm_mul, Complex.norm_real,
                Real.norm_eq_abs, abs_of_nonneg hexp_nonneg]
      _ ≤ (Real.exp (-S.firstNonzero * t) *
              ‖removeZeroMode a n‖) ^ 2 := by
            exact
              (sq_le_sq₀
                (mul_nonneg hexp_nonneg hnorm_nonneg)
                (mul_nonneg hfirst_nonneg hnorm_nonneg)).mpr hle
      _ =
          (Real.exp (-S.firstNonzero * t)) ^ 2 *
            ‖removeZeroMode a n‖ ^ 2 := by
            ring

/-- The zero-mean Neumann semigroup preserves coefficient square-summability. -/
theorem neumannSemigroupCoeff_removeZero_l2_summable
    {S : SpectralData} (H : HasNeumannSpectrum S) {t : ℝ} (ht : 0 ≤ t)
    {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖removeZeroMode a n‖ ^ 2) :
    Summable fun n : ℕ =>
      ‖neumannSemigroupCoeff S t (removeZeroMode a) n‖ ^ 2 := by
  apply Summable.of_nonneg_of_le
    (fun n => sq_nonneg _)
    ?_
    (ha.mul_left ((Real.exp (-S.firstNonzero * t)) ^ 2))
  intro n
  exact neumannSemigroupCoeff_removeZero_sq_le H ht a n

/-- Squared `ℓ²`-energy decay for `e^{tA} (I-P₀)`. -/
theorem neumannSemigroupCoeff_removeZero_l2_energy_le
    {S : SpectralData} (H : HasNeumannSpectrum S) {t : ℝ} (ht : 0 ≤ t)
    {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖removeZeroMode a n‖ ^ 2) :
    coeffL2Energy (neumannSemigroupCoeff S t (removeZeroMode a)) ≤
      (Real.exp (-S.firstNonzero * t)) ^ 2 *
        coeffL2Energy (removeZeroMode a) := by
  have hs :
      Summable fun n : ℕ =>
        ‖neumannSemigroupCoeff S t (removeZeroMode a) n‖ ^ 2 :=
    neumannSemigroupCoeff_removeZero_l2_summable H ht ha
  have hmajor :
      Summable fun n : ℕ =>
        (Real.exp (-S.firstNonzero * t)) ^ 2 *
          ‖removeZeroMode a n‖ ^ 2 :=
    ha.mul_left ((Real.exp (-S.firstNonzero * t)) ^ 2)
  have hle :
      ∀ n : ℕ,
        ‖neumannSemigroupCoeff S t (removeZeroMode a) n‖ ^ 2 ≤
          (Real.exp (-S.firstNonzero * t)) ^ 2 *
            ‖removeZeroMode a n‖ ^ 2 :=
    neumannSemigroupCoeff_removeZero_sq_le H ht a
  have htsum := hs.tsum_le_tsum hle hmajor
  simpa [coeffL2Energy, ha.tsum_mul_left] using htsum

/-- `ℓ²`-norm decay for `e^{tA} (I-P₀)` on coefficients, with sharp constant
`C = 1`. -/
theorem neumannSemigroupCoeff_removeZero_l2_norm_le
    {S : SpectralData} (H : HasNeumannSpectrum S) {t : ℝ} (ht : 0 ≤ t)
    {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖removeZeroMode a n‖ ^ 2) :
    coeffL2Norm (neumannSemigroupCoeff S t (removeZeroMode a)) ≤
      Real.exp (-S.firstNonzero * t) * coeffL2Norm (removeZeroMode a) := by
  have henergy :=
    neumannSemigroupCoeff_removeZero_l2_energy_le H ht ha
  have hleft_nonneg :
      0 ≤ coeffL2Norm (neumannSemigroupCoeff S t (removeZeroMode a)) :=
    coeffL2Norm_nonneg _
  have hright_nonneg :
      0 ≤ Real.exp (-S.firstNonzero * t) *
        coeffL2Norm (removeZeroMode a) :=
    mul_nonneg (Real.exp_nonneg _) (coeffL2Norm_nonneg _)
  refine (sq_le_sq₀ hleft_nonneg hright_nonneg).mp ?_
  calc
    coeffL2Norm (neumannSemigroupCoeff S t (removeZeroMode a)) ^ 2
        = coeffL2Energy (neumannSemigroupCoeff S t (removeZeroMode a)) :=
      coeffL2Norm_sq _
    _ ≤ (Real.exp (-S.firstNonzero * t)) ^ 2 *
          coeffL2Energy (removeZeroMode a) :=
      henergy
    _ = (Real.exp (-S.firstNonzero * t) *
          coeffL2Norm (removeZeroMode a)) ^ 2 := by
      rw [← coeffL2Norm_sq (removeZeroMode a)]
      ring

/-! ### The interval-length form used by H3.1 -/

/-- Coefficient `ℓ²` norm form of
`‖e^{tA}(I-P₀)‖ ≤ exp (-(π/L)^2 t)` for the Neumann heat semigroup on an
interval of length `L`. -/
theorem intervalNeumann_semigroup_removeZero_l2_norm_le
    {L t : ℝ} (hL : 0 < L) (ht : 0 ≤ t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖removeZeroMode a n‖ ^ 2) :
    coeffL2Norm
        (neumannSemigroupCoeff (intervalNeumannSpectrum L) t
          (removeZeroMode a)) ≤
      Real.exp (-((Real.pi / L) ^ 2) * t) *
        coeffL2Norm (removeZeroMode a) := by
  simpa [intervalNeumannSpectrum, intervalNeumannFirstNonzero] using
    neumannSemigroupCoeff_removeZero_l2_norm_le
      (S := intervalNeumannSpectrum L)
      (intervalNeumannSpectrum_hasNeumannSpectrum hL) ht ha

/-- Same estimate with any prefactor `C ≥ 1`, matching the usual sectorial
semigroup notation. -/
theorem intervalNeumann_semigroup_removeZero_l2_norm_le_with_constant
    {C L t : ℝ} (hC : 1 ≤ C) (hL : 0 < L) (ht : 0 ≤ t)
    {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖removeZeroMode a n‖ ^ 2) :
    coeffL2Norm
        (neumannSemigroupCoeff (intervalNeumannSpectrum L) t
          (removeZeroMode a)) ≤
      C * Real.exp (-((Real.pi / L) ^ 2) * t) *
        coeffL2Norm (removeZeroMode a) := by
  have hbase :=
    intervalNeumann_semigroup_removeZero_l2_norm_le hL ht ha
  have hnonneg :
      0 ≤ Real.exp (-((Real.pi / L) ^ 2) * t) *
        coeffL2Norm (removeZeroMode a) :=
    mul_nonneg (Real.exp_nonneg _) (coeffL2Norm_nonneg _)
  calc
    coeffL2Norm
        (neumannSemigroupCoeff (intervalNeumannSpectrum L) t
          (removeZeroMode a))
        ≤ Real.exp (-((Real.pi / L) ^ 2) * t) *
            coeffL2Norm (removeZeroMode a) := hbase
    _ ≤ C *
        (Real.exp (-((Real.pi / L) ^ 2) * t) *
          coeffL2Norm (removeZeroMode a)) := by
        simpa using mul_le_mul_of_nonneg_right hC hnonneg
    _ = C * Real.exp (-((Real.pi / L) ^ 2) * t) *
        coeffL2Norm (removeZeroMode a) := by
        ring

/-- Coefficient operator-norm form:
`e^{tA} (I-P₀)` is bounded by `exp (-(π/L)^2 t)` on `ℓ²`. -/
theorem intervalNeumann_semigroup_I_sub_P0_l2_norm_le
    {L t : ℝ} (hL : 0 < L) (ht : 0 ≤ t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    coeffL2Norm
        (neumannSemigroupCoeff (intervalNeumannSpectrum L) t
          (removeZeroMode a)) ≤
      Real.exp (-((Real.pi / L) ^ 2) * t) * coeffL2Norm a := by
  have hbase :=
    intervalNeumann_semigroup_removeZero_l2_norm_le
      (L := L) (t := t) hL ht (removeZeroMode_l2_summable ha)
  have hproj := removeZeroMode_l2_norm_le ha
  exact hbase.trans
    (mul_le_mul_of_nonneg_left hproj (Real.exp_nonneg _))

/-- Coefficient operator-norm form with a sectorial prefactor `C ≥ 1`. -/
theorem intervalNeumann_semigroup_I_sub_P0_l2_norm_le_with_constant
    {C L t : ℝ} (hC : 1 ≤ C) (hL : 0 < L) (ht : 0 ≤ t)
    {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    coeffL2Norm
        (neumannSemigroupCoeff (intervalNeumannSpectrum L) t
          (removeZeroMode a)) ≤
      C * Real.exp (-((Real.pi / L) ^ 2) * t) * coeffL2Norm a := by
  have hbase :=
    intervalNeumann_semigroup_I_sub_P0_l2_norm_le
      (L := L) (t := t) hL ht ha
  have hnonneg :
      0 ≤ Real.exp (-((Real.pi / L) ^ 2) * t) * coeffL2Norm a :=
    mul_nonneg (Real.exp_nonneg _) (coeffL2Norm_nonneg _)
  calc
    coeffL2Norm
        (neumannSemigroupCoeff (intervalNeumannSpectrum L) t
          (removeZeroMode a))
        ≤ Real.exp (-((Real.pi / L) ^ 2) * t) *
            coeffL2Norm a := hbase
    _ ≤ C * (Real.exp (-((Real.pi / L) ^ 2) * t) *
          coeffL2Norm a) := by
        simpa using mul_le_mul_of_nonneg_right hC hnonneg
    _ = C * Real.exp (-((Real.pi / L) ^ 2) * t) * coeffL2Norm a := by
        ring

end ShenWork.PDE.SpectralDecay
