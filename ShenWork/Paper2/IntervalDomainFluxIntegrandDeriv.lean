/-
  B2 (MinPersistence): the flux-integrand derivative (φ chain rule).

  The chemotaxis flux integrand is `u · P`, where `P(y) = v_x(y)·φ(v(y))`,
  `φ(w) = (1+w)^{−β}`.  This file computes `P'` at a point, which is the
  `g`-coefficient bounded by `flux_coeff_bound`:
    `P' = φ(v)·v_xx − β·(1+v)^{−β−1}·v_x²`.
  Stated for an abstract `C²` profile `V` (= `intervalDomainLift (v t)` in the
  application), with `v_x = deriv V`, `v_xx = deriv (deriv V)`, on `1+V > 0`.

  Combined with `HasDerivAt.mul` (and `u_x = 0` at a spatial critical point),
  this gives `chemDiv = u·P'`, feeding `min_point_estimate`'s `hcd`/`hG`.

  No `sorry`/`admit`/custom `axiom`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- **Flux-integrand derivative (multiplicative form).**  For a profile `V`
with `HasDerivAt V vx x` and `HasDerivAt (deriv V) vxx x` and `1 + V x > 0`,
the flux integrand `y ↦ deriv V y · (1 + V y)^{−β}` has derivative
`−β·(1+V x)^{−β−1}·vx² + (1+V x)^{−β}·vxx` at `x`. -/
theorem flux_integrand_hasDerivAt
    {V : ℝ → ℝ} {β vx vxx x : ℝ}
    (hV : HasDerivAt V vx x)
    (hVxx : HasDerivAt (deriv V) vxx x)
    (hpos : 0 < 1 + V x) :
    HasDerivAt (fun y => deriv V y * (1 + V y) ^ (-β))
      (-β * (1 + V x) ^ (-β - 1) * vx ^ 2 + (1 + V x) ^ (-β) * vxx) x := by
  -- Derivative of the denominator factor `(1+V)^{−β}` via the rpow chain rule.
  have hbase : HasDerivAt (fun y => 1 + V y) vx x := hV.const_add 1
  have hφ : HasDerivAt (fun y => (1 + V y) ^ (-β))
      (vx * (-β) * (1 + V x) ^ (-β - 1)) x :=
    hbase.rpow_const (Or.inl (ne_of_gt hpos))
  -- Product rule with the numerator `deriv V` (derivative `vxx`, value `vx`).
  have hmul := hVxx.mul hφ
  rw [hV.deriv] at hmul
  -- Reconcile the two derivative expressions.
  convert hmul using 1
  ring

end ShenWork.MinPersistenceAtoms
