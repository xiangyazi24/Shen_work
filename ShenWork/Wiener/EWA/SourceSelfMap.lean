import ShenWork.Wiener.EWA.SourceFixedPoint

/-!
# EWA BRICK 2 (χ₀<0 Route A′) — the source-form self-map `hself : MapsTo Φ B B`

This file discharges the carried hypothesis
`hself : MapsTo (picardEWA …) B B` of `picardEWA_exists_fixedPoint`
(`SourceFixedPoint.lean`), where `B = Metric.closedBall (heatEWA u₀E) ρ`.

`hself`'s type is a **bare metric ball** `MapsTo Φ (closedBall …) (closedBall …)`:
there is no floor in the type, so the self-map is the *radius* invariance.

The Picard map factors as a heat datum plus the two Duhamel nonlinear terms:
`Φ(u) = heatEWA u₀E + (−χ₀)•𝒟(Q(u)) + 𝒱(G(u))`, with `Q = chemFluxEWA`,
`G = growthEWA`, `𝒟 = divDuhamelEWA` (the `C₀√T` divergence Duhamel) and
`𝒱 = valDuhamelEWA` (the `T` value Duhamel).  So the *perturbation* off the heat
centre keeps only the two nonlinear terms:

  `Φ(u) − heatEWA u₀E = (−χ₀)•𝒟(Q(u)) + 𝒱(G(u))`,

whose norm is `≤ |χ₀|·C₀√T·‖Q(u)‖ + T·‖G(u)‖` (the BRICK-2 Duhamel perturbation
smallness, from `divDuhamelEWA_bound`/`valDuhamelEWA_bound`).  On the ball, the
BRICK-1 flux/growth norm bounds `‖Q(u)‖ ≤ M_Q`, `‖G(u)‖ ≤ M_G` (carried per
element exactly as the BRICK-1 Lipschitz data `hLipQ`/`hLipG` is carried in
`picardEWA_exists_fixedPoint`) make this `≤ ρ` for small `T`, i.e. `Φ(u) ∈ B`.

* `picardEWA_sub_heat` — the perturbation identity (heat datum cancels).
* `picardEWA_perturbation_norm_le` — `‖Φ(u) − heatEWA u₀E‖ ≤ |χ₀|·C₀√T·‖Q(u)‖ + T·‖G(u)‖`.
* `picardEWA_mapsTo` — the assembled `hself : MapsTo Φ B B`, the radius self-map.
  It carries the uniform flux/growth norm bounds `M_Q`, `M_G` on `B` and the
  small-time smallness `|χ₀|·C₀√T·M_Q + T·M_G ≤ ρ` as hypotheses, exactly as
  `picardEWA_exists_fixedPoint` carries the BRICK-1 Lipschitz data and the
  small-time `hK`/`hKnn` (the ball `B = closedBall (heatEWA u₀E) ρ` lives in the
  `T`-indexed type `EWA T 1`, so `T` cannot be re-chosen after fixing `M_Q`/`M_G`).
-/

open scoped BigOperators
open Set Metric
open ShenWork.GWA ShenWork.Wiener

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### BRICK 2a — the perturbation identity (the heat datum cancels). -/

/-- **The Picard perturbation identity.**  Off the heat centre `heatEWA u₀E`, the
Picard map keeps only the two nonlinear Duhamel terms. -/
theorem picardEWA_sub_heat (p : CM2Params) {μ ν γ : ℝ} (hμ : 0 < μ) (hT : 0 ≤ T)
    (u₀E : WA 1) (u : EWA T 1) :
    picardEWA p μ ν γ hμ hT u₀E u - heatEWA u₀E
      = ((-p.χ₀ : ℝ) : ℂ) • divDuhamelEWA hT (chemFluxEWA μ ν p.β γ hμ u)
        + valDuhamelEWA hT (growthEWA p.α p.a p.b u) := by
  simp only [picardEWA]
  abel

/-! ### BRICK 2b — the Duhamel perturbation smallness. -/

/-- **BRICK 2 (Duhamel perturbation smallness).**  The Picard perturbation off the
heat centre is bounded by the two Duhamel gains on the flux/growth norms:
`‖Φ(u) − heatEWA u₀E‖ ≤ |χ₀|·C₀√T·‖Q(u)‖ + T·‖G(u)‖`. -/
theorem picardEWA_perturbation_norm_le (p : CM2Params) {μ ν γ : ℝ} (hμ : 0 < μ)
    (hT : 0 ≤ T) (u₀E : WA 1) (u : EWA T 1) :
    ‖picardEWA p μ ν γ hμ hT u₀E u - heatEWA u₀E‖
      ≤ |p.χ₀| * (C₀ * Real.sqrt T) * ‖chemFluxEWA μ ν p.β γ hμ u‖
        + T * ‖growthEWA p.α p.a p.b u‖ := by
  rw [picardEWA_sub_heat p hμ hT u₀E u]
  refine le_trans (norm_add_le _ _) ?_
  refine add_le_add ?_ ?_
  · -- chemotaxis term: `|χ₀|·C₀√T·‖Q(u)‖`.
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_neg]
    calc |p.χ₀| * ‖divDuhamelEWA hT (chemFluxEWA μ ν p.β γ hμ u)‖
        ≤ |p.χ₀| * ((C₀ * Real.sqrt T) * ‖chemFluxEWA μ ν p.β γ hμ u‖) :=
          mul_le_mul_of_nonneg_left (divDuhamelEWA_bound hT _) (abs_nonneg _)
      _ = |p.χ₀| * (C₀ * Real.sqrt T) * ‖chemFluxEWA μ ν p.β γ hμ u‖ := by ring
  · -- growth term: `T·‖G(u)‖`.
    exact valDuhamelEWA_bound hT _

/-! ### BRICK 2c — the radius self-map `hself : MapsTo Φ B B`. -/

/-- **BRICK 2 (self-map, raw form).**  If on the good ball `B = closedBall
(heatEWA u₀E) ρ` the flux/growth norms are uniformly bounded — `‖Q(u)‖ ≤ M_Q`,
`‖G(u)‖ ≤ M_G` for every `u ∈ B` (the BRICK-1 norm data, carried per element just
as the Lipschitz data `hLipQ`/`hLipG` is carried) — and small time makes the total
Duhamel perturbation `≤ ρ`, then `Φ` maps `B` into `B`.  This is exactly the
`hself` consumed by `picardEWA_exists_fixedPoint`. -/
theorem picardEWA_mapsTo {p : CM2Params} {μ ν γ ρ M_Q M_G : ℝ}
    (hμ : 0 < μ) (hT : 0 ≤ T) (u₀E : WA 1)
    (hMQ : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      ‖chemFluxEWA μ ν p.β γ hμ u‖ ≤ M_Q)
    (hMG : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      ‖growthEWA p.α p.a p.b u‖ ≤ M_G)
    (hsmall : |p.χ₀| * (C₀ * Real.sqrt T) * M_Q + T * M_G ≤ ρ) :
    MapsTo (picardEWA p μ ν γ hμ hT u₀E)
      (Metric.closedBall (heatEWA u₀E) ρ) (Metric.closedBall (heatEWA u₀E) ρ) := by
  intro u hu
  rw [Metric.mem_closedBall, dist_eq_norm]
  refine le_trans (picardEWA_perturbation_norm_le p hμ hT u₀E u) ?_
  refine le_trans (add_le_add ?_ ?_) hsmall
  · -- `|χ₀|·C₀√T·‖Q(u)‖ ≤ |χ₀|·C₀√T·M_Q`.
    refine mul_le_mul_of_nonneg_left (hMQ u hu) ?_
    have := C₀_nonneg; positivity
  · -- `T·‖G(u)‖ ≤ T·M_G`.
    exact mul_le_mul_of_nonneg_left (hMG u hu) hT

end ShenWork.EWA

#print axioms ShenWork.EWA.picardEWA_sub_heat
#print axioms ShenWork.EWA.picardEWA_perturbation_norm_le
#print axioms ShenWork.EWA.picardEWA_mapsTo
