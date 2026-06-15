import ShenWork.Wiener.EWA.SourceClassicalExistence

/-!
# EWA χ₀<0 Route-A′ — SOURCE POSITIVITY of the realized slice

The realized real-space slice of a fixed point `u* = Φ(u*)`,
`realSlice u* t x = (evalST ⟨t,_⟩ (x.1 : WA.Circ) (incl u*)).re`
(`SourceClassicalExistence.lean:93`), is **strictly positive** at every interior
time/space point, by the SAME committed floor-ball technique that discharges the
`hVdFloor` leg of the χ₀<0 fixed point.

The heat datum `heatEWA u₀E` carries `UniformFloor (heatEWA u₀E) δ`
(`heatEWA_uniformFloor`, `HeatFloor.lean:403`, from a continuous source `u₀ ≥ δ`).
The floor-ball lemma `uniformFloor_on_ball` (`SourceFixedPointAbs.lean:120`)
propagates this to every `u ∈ closedBall (heatEWA u₀E) ρ` as `UniformFloor u (δ−ρ)`,
i.e. `∀ τ x, δ−ρ ≤ (evalST τ x (incl u)).re`.  Applied to the fixed point `u*` at the
slice point `⟨t,h⟩`, `(x.1 : WA.Circ)`, this is exactly the lower bound `δ−ρ` on
`realSlice u* t x`.  With `0 < δ−ρ` (carried) we conclude `0 < realSlice u* t x`.

NO `sorry`, `axiom`, `native_decide`, or `admit`.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain (intervalDomainPoint)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-- **The committed floor lower bound on the realized slice.**  For a fixed point
`u_star ∈ closedBall (heatEWA u₀E) ρ` whose heat datum has uniform floor `δ`, the
realized slice is bounded below by the ball-floor `δ − ρ` at every time `t ∈ [0,T]`
and every interior point `x`.  This is `uniformFloor_on_ball` read at the slice point. -/
theorem realSlice_ge_floor {u₀E : WA 1} {δ ρ : ℝ}
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ)
    {u_star : EWA T 1} (hu : u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (x : intervalDomainPoint) :
    δ - ρ ≤ realSlice u_star t x := by
  have hfloor : UniformFloor u_star (δ - ρ) := uniformFloor_on_ball hheat hu
  have hpt := hfloor (⟨t, ht⟩ : TimeDom T) ((x.1 : ℝ) : WA.Circ)
  rw [realSlice, dif_pos ht]
  exact hpt

/-- **SOURCE POSITIVITY (χ₀<0).**  Under the heat floor `δ`, the ball radius
`ρ` with `0 < δ − ρ`, and a fixed point `u_star ∈ closedBall (heatEWA u₀E) ρ`, the
realized real-space slice is strictly positive at every `t ∈ [0,T]` and interior
point `x`:  `0 < realSlice u_star t x`. -/
theorem realSlice_pos {u₀E : WA 1} {δ ρ : ℝ} (hδρ : 0 < δ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ)
    {u_star : EWA T 1} (hu : u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (x : intervalDomainPoint) :
    0 < realSlice u_star t x :=
  lt_of_lt_of_le hδρ (realSlice_ge_floor hheat hu ht x)

end ShenWork.EWA
