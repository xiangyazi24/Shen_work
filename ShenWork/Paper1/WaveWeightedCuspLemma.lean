import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

namespace ShenWork.Paper1

noncomputable section

open Set

theorem weighted_rpow_increment_le
    {p M z δ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hM : 0 < M)
    (hz : 0 ≤ z) (hδ : 0 ≤ δ) (hzδ : z + δ ≤ M) :
    z * ((z + δ) ^ p - z ^ p) ≤ p * M ^ p * δ := by
  by_cases hz0 : z = 0
  · subst z
    simp only [zero_add, zero_mul]
    exact mul_nonneg (mul_nonneg hp0.le (Real.rpow_nonneg hM.le p)) hδ
  have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
  by_cases hδ0 : δ = 0
  · subst δ
    simp
  have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδ0)
  let f : ℝ → ℝ := fun x => x ^ p
  have hz_lt_zδ : z < z + δ := by linarith
  have hcont : ContinuousOn f (Icc z (z + δ)) := by
    exact continuousOn_id.rpow_const fun _ _ => Or.inr hp0.le
  have hderiv : ∀ x ∈ Ioo z (z + δ), HasDerivAt f (p * x ^ (p - 1)) x := by
    intro x hx
    exact Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (lt_trans hzpos hx.1)))
  obtain ⟨c, hc, hcderiv⟩ :=
    exists_hasDerivAt_eq_slope (f := f) (f' := fun x => p * x ^ (p - 1))
      hz_lt_zδ hcont hderiv
  have hinc_eq : (z + δ) ^ p - z ^ p = p * c ^ (p - 1) * δ := by
    have hden : (z + δ) - z = δ := by ring
    have hδne : δ ≠ 0 := ne_of_gt hδpos
    have hcderiv' : p * c ^ (p - 1) = ((z + δ) ^ p - z ^ p) / δ := by
      simpa [f, hden] using hcderiv
    have hmul := congrArg (fun t : ℝ => t * δ) hcderiv'
    change (p * c ^ (p - 1)) * δ = (((z + δ) ^ p - z ^ p) / δ) * δ at hmul
    rw [div_mul_cancel₀ _ hδne] at hmul
    exact hmul.symm
  have hc_pos : 0 < c := lt_trans hzpos hc.1
  have hpow_c_le_z : c ^ (p - 1) ≤ z ^ (p - 1) := by
    exact Real.rpow_le_rpow_of_nonpos hzpos hc.1.le (by linarith)
  have hz_mul_rpow : z * z ^ (p - 1) = z ^ p := by
    have h := Real.rpow_add hzpos (p - 1) 1
    calc
      z * z ^ (p - 1) = z ^ (p - 1) * z := by ring
      _ = z ^ ((p - 1) + 1) := by
        simpa [Real.rpow_one] using h.symm
      _ = z ^ p := by
        congr 1
        ring
  have hleft_le_z : z * ((z + δ) ^ p - z ^ p) ≤ p * z ^ p * δ := by
    calc
      z * ((z + δ) ^ p - z ^ p) = z * (p * c ^ (p - 1) * δ) := by
        rw [hinc_eq]
      _ = (p * δ) * (z * c ^ (p - 1)) := by ring
      _ ≤ (p * δ) * (z * z ^ (p - 1)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow_c_le_z hz)
          (mul_nonneg hp0.le hδ)
      _ = p * (z * z ^ (p - 1)) * δ := by ring
      _ = p * z ^ p * δ := by rw [hz_mul_rpow]
  have hz_le_M : z ≤ M := by linarith
  have hzpow_le_Mpow : z ^ p ≤ M ^ p :=
    Real.rpow_le_rpow hz hz_le_M hp0.le
  have hz_to_M : p * z ^ p * δ ≤ p * M ^ p * δ := by
    calc
      p * z ^ p * δ = (p * δ) * z ^ p := by ring
      _ ≤ (p * δ) * M ^ p := by
        exact mul_le_mul_of_nonneg_left hzpow_le_Mpow (mul_nonneg hp0.le hδ)
      _ = p * M ^ p * δ := by ring
  exact le_trans hleft_le_z hz_to_M

#print axioms weighted_rpow_increment_le

end

end ShenWork.Paper1
