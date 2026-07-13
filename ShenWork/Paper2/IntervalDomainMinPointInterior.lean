/-
  B2 (MinPersistence): the interior min-point estimate, assembled.

  Composes the five min-point atoms into a single callable inequality at an
  interior spatial argmin `x*` of `u(t,·)`:
    `−K · u(x*) ≤ u_t(x*)`,   `K := |χ₀|·K₁(β, νM'^γ) + b·M'^α`,
  from the local `HasDerivAt` data (`u_x = 0`, `v`, `v_x` derivatives), the
  B4 coefficient bounds on `v` at `x*`, `u'' ≥ 0`, the bounds `0 ≤ u(x*) ≤ M'`,
  and the parabolic PDE value relation.  `K₁ = fluxCoeffConst`.

  This is the clean target the conjunct-extraction wrapper (Phase A) feeds
  from `IsPaper2ClassicalSolution`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainChemDivCritical
import ShenWork.Paper2.IntervalDomainMinPointEstimate
import ShenWork.Paper2.IntervalDomainFluxCoeffBound

open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- **Interior min-point estimate (assembled).**  At an interior spatial argmin
`x*` of `u(t,·)`, with `χ₀ ≤ 0` and the B4 derivative bounds `|v_x|,|v_xx| ≤
2νM'^γ`, the parabolic time derivative obeys
`−(|χ₀|·K₁ + b·M'^α)·u(x*) ≤ u_t(x*)`, `K₁ = fluxCoeffConst β (νM'^γ)`. -/
theorem min_point_estimate_interior_allChi
    {p : CM2Params} {u v : intervalDomainPoint → ℝ} {x : intervalDomainPoint}
    {vx vxx M' uT : ℝ}
    (hux : HasDerivAt (intervalDomainLift u) 0 x.1)
    (hv : HasDerivAt (intervalDomainLift v) vx x.1)
    (hvxx : HasDerivAt (deriv (intervalDomainLift v)) vxx x.1)
    (hvnn : ∀ y, 0 ≤ intervalDomainLift v y)
    (hM'pos : 0 ≤ M')
    (hvx_bd : |vx| ≤ 2 * (p.ν * M' ^ p.γ))
    (hvxx_bd : |vxx| ≤ 2 * (p.ν * M' ^ p.γ))
    (hu_nonneg : 0 ≤ intervalDomainLift u x.1)
    (hu_le : intervalDomainLift u x.1 ≤ M')
    (huxx : 0 ≤ deriv (deriv (intervalDomainLift u)) x.1)
    (hpde : uT = deriv (deriv (intervalDomainLift u)) x.1
        - p.χ₀ * intervalDomainChemotaxisDiv p u v x
        + intervalDomainLift u x.1 * (p.a - p.b * (intervalDomainLift u x.1) ^ p.α)) :
    -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α)
        * intervalDomainLift u x.1 ≤ uT := by
  set B : ℝ := p.ν * M' ^ p.γ with hB_def
  have hB_nonneg : 0 ≤ B := by
    rw [hB_def]; exact mul_nonneg p.hν.le (Real.rpow_nonneg hM'pos _)
  -- chemDiv = u(x*) · G,  G the flux coefficient.
  have hcd := chemDiv_at_critical (p := p) hux hv hvxx hvnn
  -- |G| ≤ K₁.
  have hG := flux_coeff_bound (β := p.β) (v := intervalDomainLift v x.1)
    (vx := vx) (vxx := vxx) (B := B) p.hβ hB_nonneg (hvnn x.1) hvx_bd hvxx_bd
  -- Apply the abstract min-point estimate.
  exact min_point_estimate_allChi p.ha p.hb p.hα.le hu_nonneg hu_le huxx hcd hG hpde

/-- Compatibility wrapper for the former `χ₀ ≤ 0` interface. -/
theorem min_point_estimate_interior
    {p : CM2Params} {u v : intervalDomainPoint → ℝ} {x : intervalDomainPoint}
    {vx vxx M' uT : ℝ}
    (_hχ : p.χ₀ ≤ 0)
    (hux : HasDerivAt (intervalDomainLift u) 0 x.1)
    (hv : HasDerivAt (intervalDomainLift v) vx x.1)
    (hvxx : HasDerivAt (deriv (intervalDomainLift v)) vxx x.1)
    (hvnn : ∀ y, 0 ≤ intervalDomainLift v y)
    (hM'pos : 0 ≤ M')
    (hvx_bd : |vx| ≤ 2 * (p.ν * M' ^ p.γ))
    (hvxx_bd : |vxx| ≤ 2 * (p.ν * M' ^ p.γ))
    (hu_nonneg : 0 ≤ intervalDomainLift u x.1)
    (hu_le : intervalDomainLift u x.1 ≤ M')
    (huxx : 0 ≤ deriv (deriv (intervalDomainLift u)) x.1)
    (hpde : uT = deriv (deriv (intervalDomainLift u)) x.1
        - p.χ₀ * intervalDomainChemotaxisDiv p u v x
        + intervalDomainLift u x.1 * (p.a - p.b * (intervalDomainLift u x.1) ^ p.α)) :
    -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α)
        * intervalDomainLift u x.1 ≤ uT :=
  min_point_estimate_interior_allChi hux hv hvxx hvnn hM'pos hvx_bd hvxx_bd
    hu_nonneg hu_le huxx hpde

end ShenWork.MinPersistenceAtoms
