import Mathlib.Analysis.Convex.SpecificFunctions.Basic

noncomputable section

namespace ShenWork.Paper1

/-- For positive exponents `g ≤ a`, the ratio
`(1 - t ^ g) / (1 - t ^ a)` is non-increasing on `(0, 1)`, stated after
cross-multiplication. -/
theorem one_sub_rpow_ratio_antitone
    {g a t1 t2 : ℝ} (hg : 0 < g) (hga : g <= a)
    (ht1 : 0 < t1) (h12 : t1 <= t2) (ht2 : t2 < 1) :
    (1 - t2 ^ g) * (1 - t1 ^ a) <= (1 - t1 ^ g) * (1 - t2 ^ a) := by
  rcases h12.eq_or_lt with rfl | h12
  · rfl
  have ht2_pos : 0 < t2 := ht1.trans h12
  have hp : 1 ≤ a / g := by
    rw [le_div_iff₀ hg]
    simpa using hga
  have hpow_lt : t1 ^ g < t2 ^ g := Real.rpow_lt_rpow ht1.le h12 hg
  have hpow_lt_one : t2 ^ g < 1 := Real.rpow_lt_one ht2_pos.le ht2 hg
  have hconv := (convexOn_rpow hp).secant_mono_aux1
    (Real.rpow_nonneg ht1.le g) (by simp : (1 : ℝ) ∈ Set.Ici 0)
    hpow_lt hpow_lt_one
  have hpow1 : (t1 ^ g) ^ (a / g) = t1 ^ a := by
    rw [← Real.rpow_mul ht1.le]
    congr 1
    field_simp
  have hpow2 : (t2 ^ g) ^ (a / g) = t2 ^ a := by
    rw [← Real.rpow_mul ht2_pos.le]
    congr 1
    field_simp
  rw [hpow1, hpow2] at hconv
  norm_num at hconv
  nlinarith

/-- A homogeneous factorization of the power gap at the large endpoint. -/
theorem rpow_large_prefactor_gap_eq
    {L U s g a : ℝ} (hL : 0 < L) (hLU : L <= U) (hs : 0 <= s)
    (hg : 0 < g) (ha : s + g = a) :
    U ^ s * (U ^ g - L ^ g) * (1 - (L / U) ^ a)
      = (1 - (L / U) ^ g) * (U ^ a - L ^ a) := by
  have hU : 0 < U := hL.trans_le hLU
  subst a
  rw [Real.rpow_add_of_nonneg (div_pos hL hU).le hs hg.le,
    Real.rpow_add_of_nonneg hU.le hs hg.le,
    Real.rpow_add_of_nonneg hL.le hs hg.le]
  simp_rw [Real.div_rpow hL.le hU.le]
  field_simp

/-- The large-endpoint prefactor gap is controlled by the combined-exponent
gap with the ratio coefficient evaluated at any lower bound for `L / U`. -/
theorem rpow_large_prefactor_gap_le_of_ratio_ge
    {L U s g a t0 : ℝ} (hL : 0 < L) (hLU : L <= U) (hs : 0 <= s)
    (hg : 0 < g) (ha : s + g = a) (ht0 : 0 < t0) (ht0L : t0 <= L / U)
    (hlt : L < U) :
    U ^ s * (U ^ g - L ^ g)
      <= ((1 - t0 ^ g) / (1 - t0 ^ a)) * (U ^ a - L ^ a) := by
  have hU : 0 < U := hL.trans hlt
  have ha_pos : 0 < a := by linarith
  have hga : g <= a := by linarith
  have ht_pos : 0 < L / U := div_pos hL hU
  have ht_lt : L / U < 1 := (div_lt_one hU).2 hlt
  have ht0_lt : t0 < 1 := ht0L.trans_lt ht_lt
  have ht_pow_lt : (L / U) ^ a < 1 :=
    Real.rpow_lt_one ht_pos.le ht_lt ha_pos
  have ht0_pow_lt : t0 ^ a < 1 :=
    Real.rpow_lt_one ht0.le ht0_lt ha_pos
  have ht_den_pos : 0 < 1 - (L / U) ^ a := sub_pos.mpr ht_pow_lt
  have ht0_den_pos : 0 < 1 - t0 ^ a := sub_pos.mpr ht0_pow_lt
  have hcross := one_sub_rpow_ratio_antitone hg hga ht0 ht0L ht_lt
  have hratio :
      (1 - (L / U) ^ g) / (1 - (L / U) ^ a) <=
        (1 - t0 ^ g) / (1 - t0 ^ a) := by
    exact (div_le_div_iff₀ ht_den_pos ht0_den_pos).2 hcross
  have hgap_nonneg : 0 <= U ^ a - L ^ a := by
    exact sub_nonneg.mpr (Real.rpow_le_rpow hL.le hLU ha_pos.le)
  have hidentity := rpow_large_prefactor_gap_eq hL hLU hs hg ha
  have hprefactor :
      U ^ s * (U ^ g - L ^ g) =
        ((1 - (L / U) ^ g) / (1 - (L / U) ^ a)) *
          (U ^ a - L ^ a) := by
    calc
      U ^ s * (U ^ g - L ^ g) =
          ((1 - (L / U) ^ g) * (U ^ a - L ^ a)) /
            (1 - (L / U) ^ a) :=
        (eq_div_iff ht_den_pos.ne').2 hidentity
      _ = ((1 - (L / U) ^ g) / (1 - (L / U) ^ a)) *
          (U ^ a - L ^ a) := by ring
  rw [hprefactor]
  exact mul_le_mul_of_nonneg_right hratio hgap_nonneg

#print axioms one_sub_rpow_ratio_antitone
#print axioms rpow_large_prefactor_gap_eq
#print axioms rpow_large_prefactor_gap_le_of_ratio_ge

end ShenWork.Paper1
