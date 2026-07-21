import ShenWork.Paper1.WholeLineChiPosEquilibriumRoot

/-!
# Root location for the positive-sensitivity scalar equilibrium

The equilibrium residual is strictly increasing above one in the
supercritical regime.  Comparing its selected zero with an explicit
supersolution gives the sharp scalar ceiling used in Proposition 1.1.
-/

open Real Set

noncomputable section

namespace ShenWork.Paper1

/-- For a positive lower exponent and a larger upper exponent, the scalar
equilibrium residual is strictly increasing on the half-line above one when
the coefficient of the lower power is less than one. -/
theorem strictMonoOn_supercriticalEquilibriumResidual
    {q alpha chi : ℝ} (hq : 0 < q) (hgap : q < alpha) (hchi : chi < 1) :
    StrictMonoOn
      (fun x : ℝ => x ^ alpha - chi * x ^ q - 1) (Set.Ici 1) := by
  intro x hx y hy hxy
  change x ^ alpha - chi * x ^ q - 1 <
    y ^ alpha - chi * y ^ q - 1
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hy0 : 0 < y := hx0.trans hxy
  have hd : 0 < alpha - q := sub_pos.mpr hgap
  have hxq_lt : x ^ q < y ^ q :=
    Real.rpow_lt_rpow hx0.le hxy hq
  have hxd_lt : x ^ (alpha - q) < y ^ (alpha - q) :=
    Real.rpow_lt_rpow hx0.le hxy hd
  have hchi_xd : chi < x ^ (alpha - q) :=
    hchi.trans_le (Real.one_le_rpow hx hd.le)
  have hprod :
      x ^ q * (x ^ (alpha - q) - chi) <
        y ^ q * (y ^ (alpha - q) - chi) := by
    exact mul_lt_mul hxq_lt (sub_lt_sub_right hxd_lt chi).le
      (sub_pos.mpr hchi_xd) (Real.rpow_pos_of_pos hy0 q).le
  have hxsplit : x ^ alpha = x ^ q * x ^ (alpha - q) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hysplit : y ^ alpha = y ^ q * y ^ (alpha - q) := by
    rw [← Real.rpow_add hy0]
    congr 1
    ring
  rw [hxsplit, hysplit]
  nlinarith

/-- A zero of a strictly increasing residual on `[1, ∞)` lies below every
nonnegative point of the residual in that half-line. -/
theorem root_le_of_strictMonoOn_Ici_one
    {f : ℝ → ℝ} {M T : ℝ}
    (hmono : StrictMonoOn f (Set.Ici 1))
    (hM : 1 ≤ M) (hT : 1 ≤ T)
    (hMzero : f M = 0) (hTnonneg : 0 ≤ f T) :
    M ≤ T := by
  by_contra hMT
  have hTM : T < M := lt_of_not_ge hMT
  have hstrict : f T < f M := hmono hT hM hTM
  rw [hMzero] at hstrict
  exact (not_lt_of_ge hTnonneg) hstrict

/-- In the supercritical positive-sensitivity regime, the selected scalar
equilibrium is bounded by the explicit root of `(1 - chi) * T ^ alpha = 1`. -/
theorem chiPosEquilibriumCeiling_le_supercritical_bound
    (p : CMParams) (hchi_pos : 0 < p.χ) (hchi_lt_one : p.χ < 1)
    (hsuper : p.m + p.γ - 1 < p.α) :
    chiPosEquilibriumCeiling p ≤
      (1 / (1 - p.χ)) ^ (1 / p.α) := by
  let q : ℝ := p.m + p.γ - 1
  let T : ℝ := (1 / (1 - p.χ)) ^ (1 / p.α)
  have hq : 0 < q := by
    dsimp [q]
    linarith [p.hm, p.hγ]
  have halpha : 0 < p.α := zero_lt_one.trans_le p.hα
  have hden : 0 < 1 - p.χ := sub_pos.mpr hchi_lt_one
  have hbase_one : 1 < 1 / (1 - p.χ) := by
    rw [lt_div_iff₀ hden]
    nlinarith
  have hT_strict : 1 < T :=
    Real.one_lt_rpow hbase_one (by positivity : 0 < 1 / p.α)
  have hT : 1 ≤ T := hT_strict.le
  have hbase_nonneg : 0 ≤ 1 / (1 - p.χ) := (le_of_lt hbase_one).trans' zero_le_one
  have hTpow : T ^ p.α = 1 / (1 - p.χ) := by
    dsimp [T]
    rw [one_div p.α, Real.rpow_inv_rpow hbase_nonneg halpha.ne']
  have hTqalpha : T ^ q < T ^ p.α :=
    Real.rpow_lt_rpow_of_exponent_lt hT_strict
      (by simpa [q] using hsuper)
  have hchi_pow : p.χ * T ^ q < p.χ * T ^ p.α :=
    mul_lt_mul_of_pos_left hTqalpha hchi_pos
  have hidentity : T ^ p.α - p.χ * T ^ p.α - 1 = 0 := by
    rw [hTpow]
    field_simp [hden.ne']
    all_goals ring
  have hTpositive : 0 < chiPosEquilibriumEq p T := by
    unfold chiPosEquilibriumEq
    dsimp [q] at hchi_pow
    nlinarith
  have hmono : StrictMonoOn (chiPosEquilibriumEq p) (Set.Ici 1) := by
    simpa [chiPosEquilibriumEq, q] using
      (strictMonoOn_supercriticalEquilibriumResidual
        (q := q) (alpha := p.α) (chi := p.χ) hq (by simpa [q] using hsuper)
          hchi_lt_one)
  exact root_le_of_strictMonoOn_Ici_one hmono
    (chiPosEquilibriumCeiling_one_le p hchi_pos.le hsuper) hT
    (chiPosEquilibriumCeiling_eq_zero p hchi_pos.le hsuper) hTpositive.le

section AxiomAudit

#print axioms chiPosEquilibriumCeiling_le_supercritical_bound

end AxiomAudit

end ShenWork.Paper1
