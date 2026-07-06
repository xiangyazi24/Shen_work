import ShenWork.Paper2.IntervalMildSourceDecay
import ShenWork.Paper2.IntervalChemFluxHolderSourceDecay

open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.PDE (intervalNeumannResolverSourceCoeff)

namespace ShenWork.Paper2

noncomputable section

/-- Initial quadratic decay of the power-source coefficients.

This is a genuine initial-face regularity assumption; it is not implied by
`InitialDatumHolder`. -/
structure InitialPowerSourceCoeffQuadraticDecay
    (p : CM2Params) (u0 : intervalDomainPoint → ℝ) (C0 : ℝ) : Prop where
  C0_nonneg : 0 ≤ C0
  decay : ∀ k : ℕ, 1 ≤ k →
    |(intervalNeumannResolverSourceCoeff p u0 k).re| ≤
      C0 / ((k : ℝ) * Real.pi) ^ 2

/-- Duhamel-form coefficient estimate for the power source.

This is the real analytic frontier needed to propagate initial source
coefficient decay uniformly up to the initial face. -/
structure PowerSourceCoeffDuhamelBoundOn
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (u0 : intervalDomainPoint → ℝ) (T BR : ℝ) : Prop where
  BR_nonneg : 0 ≤ BR
  bound : ∀ t, 0 < t → t ≤ T → ∀ k : ℕ, 1 ≤ k →
    |(intervalNeumannResolverSourceCoeff p (u t) k).re| ≤
      |(intervalNeumannResolverSourceCoeff p u0 k).re| *
        Real.exp (-(((k : ℝ) * Real.pi) ^ 2 * t)) +
      BR / ((k : ℝ) * Real.pi) ^ 2

/-- Initial source coefficient decay plus a Duhamel coefficient estimate gives a
single uniform source-coefficient decay constant on `0 < t ≤ T`. -/
theorem UniformSourceCoeffQuadraticDecayOn_of_initialDecay_and_duhamelBound
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {u0 : intervalDomainPoint → ℝ} {T C0 BR : ℝ}
    (Hinit : InitialPowerSourceCoeffQuadraticDecay p u0 C0)
    (HD : PowerSourceCoeffDuhamelBoundOn p u u0 T BR) :
    UniformSourceCoeffQuadraticDecayOn p u T (C0 + BR) := by
  refine ⟨add_nonneg Hinit.C0_nonneg HD.BR_nonneg, ?_⟩
  intro t ht htT k hk
  set lam : ℝ := ((k : ℝ) * Real.pi) ^ 2 with hlam
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  have hlam_pos : 0 < lam := by
    rw [hlam]
    positivity
  have hexp_le_one : Real.exp (-(lam * t)) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by nlinarith [mul_pos hlam_pos ht])
  have hinit_le :
      |(intervalNeumannResolverSourceCoeff p u0 k).re| * Real.exp (-(lam * t))
        ≤ C0 / lam := by
    calc
      |(intervalNeumannResolverSourceCoeff p u0 k).re| * Real.exp (-(lam * t))
          ≤ |(intervalNeumannResolverSourceCoeff p u0 k).re| * 1 :=
            mul_le_mul_of_nonneg_left hexp_le_one (abs_nonneg _)
      _ = |(intervalNeumannResolverSourceCoeff p u0 k).re| := by ring
      _ ≤ C0 / lam := by
        simpa [lam] using Hinit.decay k hk
  have hbound := HD.bound t ht htT k hk
  calc
    |(intervalNeumannResolverSourceCoeff p (u t) k).re|
        ≤ |(intervalNeumannResolverSourceCoeff p u0 k).re| * Real.exp (-(lam * t)) +
            BR / lam := by
          simpa [lam] using hbound
    _ ≤ C0 / lam + BR / lam := add_le_add hinit_le le_rfl
    _ = (C0 + BR) / lam := by ring
    _ = (C0 + BR) / ((k : ℝ) * Real.pi) ^ 2 := by rw [hlam]

end

end ShenWork.Paper2
