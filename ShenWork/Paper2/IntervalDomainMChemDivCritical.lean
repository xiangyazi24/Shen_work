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

open Filter Topology
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

/-- The faithful all-sign loss coefficient vanishes with a positive slice
ceiling.  This includes the endpoint `m = 1`: the factor `M^(m-1)` may tend
to one, but the elliptic flux coefficient still tends to zero. -/
theorem generalMMinSlopeConst_tendsto_zero_nhdsGT
    (p : CM2Params) (hm : 1 ≤ p.m) :
    Tendsto (generalMMinSlopeConst p) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hbase : Tendsto (fun M : ℝ => M) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hm1 : 0 ≤ p.m - 1 := by linarith
  have hpow_m1 : Tendsto (fun M : ℝ => M ^ (p.m - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 ((0 : ℝ) ^ (p.m - 1))) :=
    hbase.rpow_const (Or.inr hm1)
  have hpow_gamma : Tendsto (fun M : ℝ => M ^ p.γ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [Real.zero_rpow p.hγ.ne'] using
      hbase.rpow_const (Or.inr p.hγ.le)
  have hB : Tendsto (fun M : ℝ => p.ν * M ^ p.γ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hpow_gamma
  have h2B : Tendsto (fun M : ℝ => 2 * (p.ν * M ^ p.γ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hB
  have hflux : Tendsto
      (fun M : ℝ => ShenWork.MinPersistenceAtoms.fluxCoeffConst p.β
        (p.ν * M ^ p.γ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hsquare := h2B.pow 2
    have hconst_beta : Tendsto (fun _ : ℝ => p.β)
        (𝓝[>] (0 : ℝ)) (𝓝 p.β) := tendsto_const_nhds
    have hfirst := hconst_beta.mul hsquare
    simpa [ShenWork.MinPersistenceAtoms.fluxCoeffConst] using hfirst.add h2B
  have hchem : Tendsto
      (fun M : ℝ => |p.χ₀| * (M ^ (p.m - 1) *
        ShenWork.MinPersistenceAtoms.fluxCoeffConst p.β
          (p.ν * M ^ p.γ))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hprod := hpow_m1.mul hflux
    simpa using tendsto_const_nhds.mul hprod
  have hpow_alpha : Tendsto (fun M : ℝ => M ^ p.α)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [Real.zero_rpow p.hα.ne'] using
      hbase.rpow_const (Or.inr p.hα.le)
  have hlogistic : Tendsto (fun M : ℝ => p.b * M ^ p.α)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hpow_alpha
  simpa [generalMMinSlopeConst] using hchem.add hlogistic

/-- Positive linear growth dominates the faithful all-sign minimum loss under
a sufficiently small positive slice ceiling. -/
theorem exists_pos_generalMMinGrowthRate
    (p : CM2Params) (hm : 1 ≤ p.m) (ha : 0 < p.a) :
    ∃ M : ℝ, 0 < M ∧ 0 < generalMMinGrowthRate p M := by
  have hloss : ∀ᶠ M : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      generalMMinSlopeConst p M < p.a :=
    (generalMMinSlopeConst_tendsto_zero_nhdsGT p hm).eventually
      (Iio_mem_nhds ha)
  have hpos : ∀ᶠ M : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < M :=
    self_mem_nhdsWithin
  rcases (hloss.and hpos).exists with ⟨M, hlossM, hM⟩
  exact ⟨M, hM, by simp only [generalMMinGrowthRate]; linarith⟩

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
#print axioms generalMMinSlopeConst_tendsto_zero_nhdsGT
#print axioms exists_pos_generalMMinGrowthRate
#print axioms min_point_estimate_interior_M_allChi_with_growth
#print axioms min_point_estimate_interior_M_allChi

end AxiomAudit

end ShenWork.Paper2.IntervalDomainMMinPersistence
