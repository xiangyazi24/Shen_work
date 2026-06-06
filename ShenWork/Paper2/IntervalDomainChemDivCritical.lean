/-
  B2 (MinPersistence): chemotaxis divergence at a spatial critical point.

  At a spatial argmin `x*` of `u(t,·)` (so `u_x(x*) = 0`), the chemotaxis flux
  divergence factors as `chemDiv = u(x*)·P'`, where
    `P' = −β·(1+v)^{−β−1}·v_x² + (1+v)^{−β}·v_xx`
  is the flux coefficient bounded by `flux_coeff_bound` (≤ K₁).  This is the
  `hcd : cd = m·G` input of `min_point_estimate`.

  Combines the φ chain rule (`flux_integrand_hasDerivAt`), the division→`rpow`
  bridge (`Real.rpow_neg`, valid since `1 + v ≥ 1 > 0`), and the product rule
  with `u_x = 0`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainFluxIntegrandDeriv
import ShenWork.PDE.IntervalDomain

open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- **Chemotaxis divergence at a spatial critical point.**  If `u_x(x*) = 0`,
the chemical profile `v = lift` is `C²` near `x*` with `1+v ≥ 1 > 0` (from
`v ≥ 0`), then the chemotaxis divergence equals `u(x*)·P'`, `P'` the flux
coefficient. -/
theorem chemDiv_at_critical
    {p : CM2Params} {u v : intervalDomainPoint → ℝ} {x : intervalDomainPoint}
    {vx vxx : ℝ}
    (hux : HasDerivAt (intervalDomainLift u) 0 x.1)
    (hv : HasDerivAt (intervalDomainLift v) vx x.1)
    (hvxx : HasDerivAt (deriv (intervalDomainLift v)) vxx x.1)
    (hvnn : ∀ y, 0 ≤ intervalDomainLift v y) :
    intervalDomainChemotaxisDiv p u v x =
      intervalDomainLift u x.1 *
        (-p.β * (1 + intervalDomainLift v x.1) ^ (-p.β - 1) * vx ^ 2
          + (1 + intervalDomainLift v x.1) ^ (-p.β) * vxx) := by
  set V : ℝ → ℝ := intervalDomainLift v with hV_def
  set U : ℝ → ℝ := intervalDomainLift u with hU_def
  -- `1 + V y > 0` everywhere (V ≥ 0).
  have hpos : ∀ y, (0:ℝ) < 1 + V y := fun y => by
    have := hvnn y; rw [hV_def]; linarith [hvnn y]
  -- Division form of the flux integrand equals the `rpow`-`(−β)` form.
  have hPeq : (fun y => deriv V y / (1 + V y) ^ p.β)
      = (fun y => deriv V y * (1 + V y) ^ (-p.β)) := by
    funext y
    rw [Real.rpow_neg (le_of_lt (hpos y)), div_eq_mul_inv]
  -- The flux integrand has derivative `P'` at `x.1`.
  have hP : HasDerivAt (fun y => deriv V y / (1 + V y) ^ p.β)
      (-p.β * (1 + V x.1) ^ (-p.β - 1) * vx ^ 2
        + (1 + V x.1) ^ (-p.β) * vxx) x.1 := by
    rw [hPeq]
    exact flux_integrand_hasDerivAt hv hvxx (hpos x.1)
  -- `chemDiv = deriv (U · P_div) x.1`, factored via `mul_div_assoc`.
  have hFeq : (fun y => U y * deriv V y / (1 + V y) ^ p.β)
      = (fun y => U y * (deriv V y / (1 + V y) ^ p.β)) := by
    funext y; rw [mul_div_assoc]
  -- Product rule with `U_x = 0` (annotate the lambda so `.deriv` matches).
  have hmul : HasDerivAt (fun y => U y * (deriv V y / (1 + V y) ^ p.β))
      (0 * (deriv V x.1 / (1 + V x.1) ^ p.β)
        + U x.1 * (-p.β * (1 + V x.1) ^ (-p.β - 1) * vx ^ 2
          + (1 + V x.1) ^ (-p.β) * vxx)) x.1 := hux.mul hP
  rw [intervalDomainChemotaxisDiv, ← hU_def, ← hV_def, hFeq, hmul.deriv]
  ring

end ShenWork.MinPersistenceAtoms
