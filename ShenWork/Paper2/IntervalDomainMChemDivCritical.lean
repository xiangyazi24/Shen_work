/-
  Critical-point factorization for the faithful general-m interval flux.

  At a positive spatial critical point of U, differentiating

      U^m V_x (1 + V)^(-beta)

  kills the derivative of U^m.  The remaining factor is U^m times the same
  elliptic coefficient used in the linear-flux minimum argument.  For m >= 1
  and 0 <= U <= M this is U times a coefficient bounded by
  M^(m-1) * fluxCoeffConst beta (nu * M^gamma).
-/
import ShenWork.Paper2.IntervalDomainFluxIntegrandDeriv
import ShenWork.Paper2.IntervalDomainMinPointEstimate
import ShenWork.Paper2.IntervalDomainFluxCoeffBound
import ShenWork.PDE.IntervalDomain

open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainMMinPersistence

/-- The faithful general-`m` chemotaxis divergence at a positive spatial
critical point. -/
theorem chemDivM_at_critical
    {p : CM2Params} {u v : intervalDomainPoint → ℝ} {x : intervalDomainPoint}
    {vx vxx : ℝ}
    (hu_pos : 0 < intervalDomainLift u x.1)
    (hux : HasDerivAt (intervalDomainLift u) 0 x.1)
    (hv : HasDerivAt (intervalDomainLift v) vx x.1)
    (hvxx : HasDerivAt (deriv (intervalDomainLift v)) vxx x.1)
    (hvnn : ∀ y, 0 ≤ intervalDomainLift v y) :
    intervalDomainChemotaxisDivM p u v x =
      intervalDomainLift u x.1 ^ p.m *
        (-p.β * (1 + intervalDomainLift v x.1) ^ (-p.β - 1) * vx ^ 2
          + (1 + intervalDomainLift v x.1) ^ (-p.β) * vxx) := by
  set V : ℝ → ℝ := intervalDomainLift v with hV_def
  set U : ℝ → ℝ := intervalDomainLift u with hU_def
  have hpos : ∀ y, (0 : ℝ) < 1 + V y := fun y => by
    have := hvnn y
    rw [hV_def]
    linarith
  have hPeq : (fun y => deriv V y / (1 + V y) ^ p.β) =
      (fun y => deriv V y * (1 + V y) ^ (-p.β)) := by
    funext y
    rw [Real.rpow_neg (le_of_lt (hpos y)), div_eq_mul_inv]
  have hP : HasDerivAt (fun y => deriv V y / (1 + V y) ^ p.β)
      (-p.β * (1 + V x.1) ^ (-p.β - 1) * vx ^ 2
        + (1 + V x.1) ^ (-p.β) * vxx) x.1 := by
    rw [hPeq]
    exact ShenWork.MinPersistenceAtoms.flux_integrand_hasDerivAt
      hv hvxx (hpos x.1)
  have hUpow : HasDerivAt (fun y => U y ^ p.m) 0 x.1 := by
    have hchain := hux.rpow_const (p := p.m)
      (Or.inl (ne_of_gt hu_pos))
    convert hchain using 1 <;> ring
  have hFeq :
      (fun y => U y ^ p.m * deriv V y / (1 + V y) ^ p.β) =
        (fun y => U y ^ p.m * (deriv V y / (1 + V y) ^ p.β)) := by
    funext y
    rw [mul_div_assoc]
  have hmul : HasDerivAt
      (fun y => U y ^ p.m * (deriv V y / (1 + V y) ^ p.β))
      (0 * (deriv V x.1 / (1 + V x.1) ^ p.β) +
        U x.1 ^ p.m *
          (-p.β * (1 + V x.1) ^ (-p.β - 1) * vx ^ 2
            + (1 + V x.1) ^ (-p.β) * vxx)) x.1 := by
    simpa only [Pi.mul_apply] using hUpow.mul hP
  rw [intervalDomainChemotaxisDivM, ← hU_def, ← hV_def, hFeq, hmul.deriv]
  ring

/-- Extract one factor of a positive base from a real power. -/
theorem rpow_eq_rpow_sub_one_mul
    {z q : ℝ} (hz : 0 < z) :
    z ^ q = z ^ (q - 1) * z := by
  calc
    z ^ q = z ^ ((q - 1) + 1) := by ring_nf
    _ = z ^ (q - 1) * z ^ (1 : ℝ) := Real.rpow_add hz _ _
    _ = z ^ (q - 1) * z := by rw [Real.rpow_one]

/-- The coefficient multiplying the minimum in the faithful general-`m`
Hamilton inequality. -/
def generalMMinSlopeConst (p : CM2Params) (M : ℝ) : ℝ :=
  |p.χ₀| * (M ^ (p.m - 1) *
    ShenWork.MinPersistenceAtoms.fluxCoeffConst p.β (p.ν * M ^ p.γ)) +
    p.b * M ^ p.α

/-- Net linear growth left at a spatial minimum after bounding the faithful
chemotaxis and logistic damping terms by a slice ceiling. -/
def generalMMinGrowthRate (p : CM2Params) (M : ℝ) : ℝ :=
  p.a - generalMMinSlopeConst p M

/-- Interior critical-point Hamilton estimate for the faithful general-`m`
flux, retaining the positive linear reaction. -/
theorem min_point_estimate_interior_M_allChi_with_growth
    {p : CM2Params} {u v : intervalDomainPoint → ℝ} {x : intervalDomainPoint}
    {vx vxx M uT : ℝ}
    (hm : 1 ≤ p.m)
    (hux : HasDerivAt (intervalDomainLift u) 0 x.1)
    (hv : HasDerivAt (intervalDomainLift v) vx x.1)
    (hvxx : HasDerivAt (deriv (intervalDomainLift v)) vxx x.1)
    (hvnn : ∀ y, 0 ≤ intervalDomainLift v y)
    (hM : 0 ≤ M)
    (hvx_bd : |vx| ≤ 2 * (p.ν * M ^ p.γ))
    (hvxx_bd : |vxx| ≤ 2 * (p.ν * M ^ p.γ))
    (hu_pos : 0 < intervalDomainLift u x.1)
    (hu_le : intervalDomainLift u x.1 ≤ M)
    (huxx : 0 ≤ deriv (deriv (intervalDomainLift u)) x.1)
    (hpde : uT = deriv (deriv (intervalDomainLift u)) x.1
        - p.χ₀ * intervalDomainChemotaxisDivM p u v x
        + intervalDomainLift u x.1 *
            (p.a - p.b * intervalDomainLift u x.1 ^ p.α)) :
    generalMMinGrowthRate p M * intervalDomainLift u x.1 ≤ uT := by
  let U : ℝ := intervalDomainLift u x.1
  let B : ℝ := p.ν * M ^ p.γ
  let K : ℝ := ShenWork.MinPersistenceAtoms.fluxCoeffConst p.β B
  let G : ℝ :=
    -p.β * (1 + intervalDomainLift v x.1) ^ (-p.β - 1) * vx ^ 2
      + (1 + intervalDomainLift v x.1) ^ (-p.β) * vxx
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg p.hν.le (Real.rpow_nonneg hM _)
  have hG : |G| ≤ K := by
    exact ShenWork.MinPersistenceAtoms.flux_coeff_bound
      p.hβ hB (hvnn x.1) hvx_bd hvxx_bd
  have hpow_le : U ^ (p.m - 1) ≤ M ^ (p.m - 1) :=
    Real.rpow_le_rpow hu_pos.le hu_le (by linarith)
  have hpow_nonneg : 0 ≤ U ^ (p.m - 1) :=
    Real.rpow_nonneg hu_pos.le _
  have hG' : |U ^ (p.m - 1) * G| ≤ M ^ (p.m - 1) * K := by
    rw [abs_mul, abs_of_nonneg hpow_nonneg]
    exact mul_le_mul hpow_le hG (abs_nonneg _) (Real.rpow_nonneg hM _)
  have hcd0 := chemDivM_at_critical (p := p) hu_pos hux hv hvxx hvnn
  have hcd : intervalDomainChemotaxisDivM p u v x =
      U * (U ^ (p.m - 1) * G) := by
    rw [hcd0]
    dsimp [U, G]
    rw [rpow_eq_rpow_sub_one_mul hu_pos]
    ring
  have hmain := ShenWork.MinPersistenceAtoms.min_point_estimate_allChi_with_growth
    p.hb p.hα.le hu_pos.le hu_le huxx hcd hG' hpde
  simpa [generalMMinGrowthRate, generalMMinSlopeConst, U, B, K] using hmain

/-- Interior critical-point Hamilton estimate in its historical form, with
the nonnegative linear reaction discarded. -/
theorem min_point_estimate_interior_M_allChi
    {p : CM2Params} {u v : intervalDomainPoint → ℝ} {x : intervalDomainPoint}
    {vx vxx M uT : ℝ}
    (hm : 1 ≤ p.m)
    (hux : HasDerivAt (intervalDomainLift u) 0 x.1)
    (hv : HasDerivAt (intervalDomainLift v) vx x.1)
    (hvxx : HasDerivAt (deriv (intervalDomainLift v)) vxx x.1)
    (hvnn : ∀ y, 0 ≤ intervalDomainLift v y)
    (hM : 0 ≤ M)
    (hvx_bd : |vx| ≤ 2 * (p.ν * M ^ p.γ))
    (hvxx_bd : |vxx| ≤ 2 * (p.ν * M ^ p.γ))
    (hu_pos : 0 < intervalDomainLift u x.1)
    (hu_le : intervalDomainLift u x.1 ≤ M)
    (huxx : 0 ≤ deriv (deriv (intervalDomainLift u)) x.1)
    (hpde : uT = deriv (deriv (intervalDomainLift u)) x.1
        - p.χ₀ * intervalDomainChemotaxisDivM p u v x
        + intervalDomainLift u x.1 *
            (p.a - p.b * intervalDomainLift u x.1 ^ p.α)) :
    -generalMMinSlopeConst p M * intervalDomainLift u x.1 ≤ uT := by
  have hgrowth := min_point_estimate_interior_M_allChi_with_growth hm hux hv
    hvxx hvnn hM hvx_bd hvxx_bd hu_pos hu_le huxx hpde
  unfold generalMMinGrowthRate at hgrowth
  nlinarith [mul_nonneg p.ha hu_pos.le]

section AxiomAudit

#print axioms chemDivM_at_critical
#print axioms rpow_eq_rpow_sub_one_mul
#print axioms min_point_estimate_interior_M_allChi_with_growth
#print axioms min_point_estimate_interior_M_allChi

end AxiomAudit

end ShenWork.Paper2.IntervalDomainMMinPersistence
