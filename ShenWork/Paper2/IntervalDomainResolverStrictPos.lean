/-
  Additive: resolver strict positivity (the ledger `Hvpos` residual), and the
  reusable `cosineCoeffs_const`.

  `Hvpos : 0 < mildChemicalConcentration p u t x` is needed by the frontier
  assembly.  Route: the source `ν·u^γ ≥ c₀ := ν·m^γ > 0` (m = min u on [0,1]),
  and the elliptic resolver of a source bounded below by the constant `c₀` is
  bounded below by `c₀/μ`:
    `R(u) = c₀/μ + (reconstruction of ν·u^γ − c₀)`,  the second term ≥ 0.

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.Paper2.IntervalMildPicardRegularity
import ShenWork.PDE.IntervalResolverPositivity
import ShenWork.PDE.IntervalNeumannEllipticResolverR
import ShenWork.PDE.IntervalFullKernelInterchange
import ShenWork.PDE.IntervalFullKernelSupBound

open Set Filter Topology MeasureTheory
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalNeumannFullKernel
  intervalFullSemigroupOperator intervalNeumannFullKernel_integrable
  intervalNeumannFullKernel_nonneg)
open ShenWork.IntervalResolverPositivity (intervalNeumannFullKernel_cosineKernel_identity)
open ShenWork.IntervalFullKernelInterchange
  (intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional)
open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.IntervalMildPicardRegularity (cosineCoeffs_eq_factor_mul_integral)

noncomputable section

namespace ShenWork.IntervalDomainResolverStrictPos

/-- **Cosine coefficients of a constant.**  `cosineCoeffs (const c) n = c` at the
zeroth mode and `0` for `n ≥ 1` (`∫₀¹ cos(nπx) dx = sin(nπ)/(nπ) = 0`). -/
theorem cosineCoeffs_const (c : ℝ) (n : ℕ) :
    cosineCoeffs (fun _ => c) n = if n = 0 then c else 0 := by
  rw [cosineCoeffs_eq_factor_mul_integral]
  by_cases hn : n = 0
  · subst hn
    simp only [Nat.cast_zero, zero_mul, Real.cos_zero, one_mul]
    rw [intervalIntegral.integral_const]
    norm_num
  · simp only [if_neg hn]
    have hcos_int : (∫ x in (0:ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x)) = 0 := by
      have key : ∀ x : ℝ,
          HasDerivAt (fun y => Real.sin ((n : ℝ) * Real.pi * y) / ((n : ℝ) * Real.pi))
            (Real.cos ((n : ℝ) * Real.pi * x)) x := by
        intro x
        have h1 : HasDerivAt (fun y : ℝ => (n : ℝ) * Real.pi * y) ((n : ℝ) * Real.pi) x := by
          simpa using (hasDerivAt_id x).const_mul ((n : ℝ) * Real.pi)
        have h2 : HasDerivAt (fun y => Real.sin ((n : ℝ) * Real.pi * y))
            (Real.cos ((n : ℝ) * Real.pi * x) * ((n : ℝ) * Real.pi)) x := h1.sin
        have hnp : (n : ℝ) * Real.pi ≠ 0 := by
          have : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
          positivity
        have h3 := h2.div_const ((n : ℝ) * Real.pi)
        convert h3 using 1
        field_simp
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => key x)
        ((Real.continuous_cos.comp (by fun_prop)).intervalIntegrable 0 1)]
      have h1 : (n : ℝ) * Real.pi * 1 = (n : ℝ) * Real.pi := by ring
      rw [h1, Real.sin_nat_mul_pi]; simp
    rw [intervalIntegral.integral_mul_const, hcos_int, zero_mul, mul_zero]

/-- **Heat value lower bound.**  If `f` is continuous, bounded, and `≥ c₀` on
all of `ℝ`, then the cosine-spectral heat value is `≥ c₀` at interior `x`
(`t > 0`): `S(t)f = ∫K·f ≥ ∫K·c₀ = S(t)(const c₀) = c₀`. -/
theorem heatValue_ge_const {f : ℝ → ℝ} {c₀ M : ℝ}
    (hf_cont : Continuous f) (hf_ge : ∀ y, c₀ ≤ f y) (hf_bdd : ∀ y, |f y| ≤ M)
    {t : ℝ} (ht : 0 < t) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    c₀ ≤ unitIntervalCosineHeatValue t (cosineCoeffs f) x := by
  have hker : ∀ y, intervalNeumannFullKernel t x y
      = ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
        (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y)) :=
    fun y => intervalNeumannFullKernel_cosineKernel_identity ht x y
  have hSf := intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional t ht f hf_cont x hx hker
  have hSc := intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional t ht
    (fun _ => c₀) continuous_const x hx hker
  have hConst : unitIntervalCosineHeatValue t (cosineCoeffs (fun _ => c₀)) x = c₀ := by
    rw [unitIntervalCosineHeatValue, tsum_eq_single 0
      (fun n hn => by rw [cosineCoeffs_const, if_neg hn, mul_zero])]
    rw [cosineCoeffs_const, if_pos rfl]
    simp [unitIntervalCosineHeatPointWeight, unitIntervalCosineEigenvalue,
      unitIntervalCosineMode]
  have hKint : Integrable (fun y => intervalNeumannFullKernel t x y) (intervalMeasure 1) :=
    intervalNeumannFullKernel_integrable ht x
  have hKc : Integrable (fun y => intervalNeumannFullKernel t x y * c₀) (intervalMeasure 1) :=
    hKint.mul_const c₀
  have hKf : Integrable (fun y => intervalNeumannFullKernel t x y * f y) (intervalMeasure 1) := by
    have h := hKint.bdd_mul hf_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => by rw [Real.norm_eq_abs]; exact hf_bdd y))
    refine h.congr ?_
    filter_upwards with y using mul_comm (f y) (intervalNeumannFullKernel t x y)
  have hmono : intervalFullSemigroupOperator t (fun _ => c₀) x
      ≤ intervalFullSemigroupOperator t f x := by
    simp only [intervalFullSemigroupOperator]
    refine integral_mono hKc hKf (fun y => ?_)
    exact mul_le_mul_of_nonneg_left (hf_ge y) (intervalNeumannFullKernel_nonneg ht x y)
  rw [← hSf]
  calc c₀ = unitIntervalCosineHeatValue t (cosineCoeffs (fun _ => c₀)) x := hConst.symm
    _ = intervalFullSemigroupOperator t (fun _ => c₀) x := hSc.symm
    _ ≤ intervalFullSemigroupOperator t f x := hmono

end ShenWork.IntervalDomainResolverStrictPos
