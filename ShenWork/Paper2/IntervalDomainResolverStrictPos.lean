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

open Set Filter Topology
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
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

end ShenWork.IntervalDomainResolverStrictPos
