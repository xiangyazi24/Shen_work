import ShenWork.Wiener.EWA.SourceSelfMap

/-!
# EWA brick (χ₀<0 Route A′) — HEAT-FLOOR POSITIVITY + the ABSOLUTE source-form fixed point

This file turns the *conditional* fixed point `picardEWA_exists_fixedPoint`
(`SourceFixedPoint.lean`) into an **absolute** χ₀<0 source-form fixed point by
discharging the carried floor-dependent regularity hypotheses (`hLipQ`/`hLipG`) from a
single positivity input on the heat datum — the **uniform spectral floor of the
Neumann heat flow** `UniformFloor (heatEWA u₀E) δ`.

## The mechanism (floor → Lipschitz → fixed point)

1. **The eval bound** `evalST_incl_re_abs_le`: the `A⁰→C⁰` synthesis bound
   `|Re(evalST τ x (incl g))| ≤ ‖g‖`, assembled from the committed
   `evalLin_norm_le` (`‖evalLin a‖ ≤ ‖a‖`), `norm_sliceWA_le` (`‖sliceWA τ a‖ ≤ ‖a‖`)
   and `norm_incl_apply_le` (`‖incl g‖ ≤ ‖g‖`).  The eval constant is `C_eval = 1`.

2. **The floor-ball lemma** `uniformFloor_of_ball`: if `UniformFloor h δ` and
   `‖u − h‖ ≤ ρ` then `UniformFloor u (δ − ρ)`, because at every `(τ,x)`,
   `Re(evalST τ x (incl u)) = Re(evalST τ x (incl h)) + Re(evalST τ x (incl (u−h)))`
   `≥ δ − ‖u − h‖ ≥ δ − ρ`.  Hence on the ball `closedBall (heatEWA u₀E) ρ`, every `u`
   has floor `δ − ρ`; with `ρ ≤ δ/2` this is `≥ δ/2 > 0`.

3. **The Lipschitz discharge** `picardEWA_exists_fixedPoint_floorBall`: with the common
   ball-floor `δ/2 > 0`, brick-1 `chemFluxEWA_lipschitz`/`growthEWA_lipschitz` apply for
   every pair in the ball with the *uniform* constants `L_Q`/`L_G`, discharging the
   carried `hLipQ`/`hLipG`.  The remaining brick-1 side-data (the radius `R`, the
   derivative bounds `Md`/`Mdv`, the `1+v` floor `δv`) are uniform on the ball and are
   carried as the standard analytic inputs.

## Honest accounting — the one genuine gap

The **heat-floor positivity** `UniformFloor (heatEWA u₀E) δ` from `u₀ ≥ δ > 0` is NOT
committed in the current tree: the heat eval bridge for `heatEWA` (the EWA analogue of
`intervalFullSemigroupOperator_eq_cosineHeatValue`) is flagged MODERATE/gated in
`ROUTE.md` (it needs `hkernel = intervalNeumannFullKernel_eq_cosineKernel` plus the
`FullKernelIntegralInterchange` Prop), and `HeatFlow.lean` is a pure construction
(norm bound only, no eval, no positivity, no constant preservation).  The MISSING lemma
is precisely:

  `heatEWA_evalST_eq : evalST τ x (incl (heatEWA u₀E))
      = intervalFullSemigroupOperator τ.1 u₀ x`   (heat eval bridge, gated)

together with `intervalFullSemigroupOperator_nonneg` (positivity-preserving) and
`intervalFullSemigroupOperator_const` (`S(t)1 = 1`, constant preservation), which give
`evalST τ x (incl (heatEWA u₀E)) ≥ δ` for `u₀ ≥ δ`.  Until that bridge is committed we
take `UniformFloor (heatEWA u₀E) δ` as a NAMED hypothesis `hheat`.  Everything else —
the eval bound, the floor-ball derivation, the Lipschitz discharge and the fixed point —
is proved.  This collapses the χ₀<0 fixed point to the single standard positivity input
`hheat` (plus the brick-1 analytic side-data, all uniform on the ball).
-/

open scoped BigOperators
open Set Metric
open ShenWork.GWA ShenWork.Wiener

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### Part 1 — the `A⁰→C⁰` eval bound `|Re(evalST τ x (incl g))| ≤ ‖g‖` (`C_eval = 1`). -/

/-- **The synthesis eval bound** (committed pieces, `C_eval = 1`).  For every time `τ`
and spatial point `x`, the real part of the EWA point-evaluation of the grade-drop
`incl g` is dominated by the `EWA 1` norm of `g`:
`|Re(evalST τ x (incl g))| ≤ ‖g‖`.

Assembled from `Complex.abs_re_le_norm`, `ContinuousMap.norm_coe_le_norm`,
`WA.evalLin_norm_le`, `norm_sliceWA_le` and `norm_incl_apply_le`. -/
theorem evalST_incl_re_abs_le (τ : TimeDom T) (x : WA.Circ) (g : EWA T 1) :
    |(evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) g)).re| ≤ ‖g‖ := by
  rw [evalST_apply, WA.evalAt_apply]
  -- `|Re(evalLin b x)| ≤ ‖evalLin b x‖ ≤ ‖evalLin b‖ ≤ ‖b‖ = ‖sliceWA τ (incl g)‖ ≤ ‖g‖`.
  set b : WA 0 := sliceWA τ (GWA.incl (by omega : (0:ℕ) ≤ 1) g) with hb
  have h1 : |(WA.evalLin b x).re| ≤ ‖WA.evalLin b x‖ := Complex.abs_re_le_norm _
  have h2 : ‖WA.evalLin b x‖ ≤ ‖WA.evalLin b‖ := ContinuousMap.norm_coe_le_norm (WA.evalLin b) x
  have h3 : ‖WA.evalLin b‖ ≤ ‖b‖ := WA.evalLin_norm_le b
  have h4 : ‖b‖ ≤ ‖GWA.incl (by omega : (0:ℕ) ≤ 1) g‖ := by
    rw [hb]; exact norm_sliceWA_le τ _
  have h5 : ‖GWA.incl (by omega : (0:ℕ) ≤ 1) g‖ ≤ ‖g‖ := norm_incl_apply_le _ _
  linarith [h1, h2, h3, h4, h5]

/-! ### Part 2 — the FLOOR-BALL lemma: `UniformFloor h δ` + `‖u − h‖ ≤ ρ` ⟹
`UniformFloor u (δ − ρ)`. -/

/-- **The floor-ball lemma** (`C_eval = 1`).  If the centre `h` has uniform floor `δ`
and `u` is within `ρ` of `h`, then `u` has floor `δ − ρ`:
at every `(τ,x)`, `incl` is additive so
`Re(evalST τ x (incl u)) = Re(evalST τ x (incl h)) + Re(evalST τ x (incl (u−h)))`,
and the second summand is `≥ −‖u−h‖ ≥ −ρ` by `evalST_incl_re_abs_le`. -/
theorem uniformFloor_of_ball {h u : EWA T 1} {δ ρ : ℝ}
    (hh : UniformFloor h δ) (hu : ‖u - h‖ ≤ ρ) :
    UniformFloor u (δ - ρ) := by
  intro τ x
  -- additivity of `incl` (a CLM) and `evalST` (a ring hom) on the difference.
  have hincl : GWA.incl (by omega : (0:ℕ) ≤ 1) (u - h)
      = GWA.incl (by omega : (0:ℕ) ≤ 1) u - GWA.incl (by omega : (0:ℕ) ≤ 1) h :=
    ContinuousLinearMap.map_sub _ u h
  have heval : evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) (u - h))
      = evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) u)
        - evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) h) := by
    rw [hincl, RingHom.map_sub]
  have hadd : (evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) u)).re
      = (evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) h)).re
        + (evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) (u - h))).re := by
    rw [heval, Complex.sub_re]; ring
  rw [hadd]
  have hfloor : δ ≤ (evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) h)).re := hh τ x
  have hpert : |(evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) (u - h))).re| ≤ ρ :=
    le_trans (evalST_incl_re_abs_le τ x (u - h)) hu
  have hge : -ρ ≤ (evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) (u - h))).re :=
    (abs_le.mp hpert).1
  linarith

/-- **Floor on the ball.**  Every `u ∈ closedBall (heatEWA u₀E) ρ` has uniform floor
`δ − ρ`, provided the heat datum has floor `δ`. -/
theorem uniformFloor_on_ball {u₀E : WA 1} {δ ρ : ℝ}
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ)
    {u : EWA T 1} (hu : u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ) :
    UniformFloor u (δ - ρ) := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hu
  exact uniformFloor_of_ball hheat hu

/-! ### Part 3 — the absolute fixed point via the floor-ball Lipschitz discharge.

The brick-1 Lipschitz bounds need a *common* floor on `u,w` (for the WL1 power) and on
`1+v` (for the WL2 factor), a radius `R`, derivative bounds `Md`/`Mdv`.  The floor-ball
lemma supplies the `u`-floor `δ − ρ` uniformly on the ball; the remaining analytic
side-data (`R`, `Md`, `Mdv`, the `1+v` floor `δv`) are uniform on the ball and carried
as standard inputs, exactly as `picardEWA_mapsTo` carries the `M_Q`/`M_G` norm bounds. -/

/-- **THE ABSOLUTE χ₀<0 SOURCE-FORM FIXED POINT (floor-ball form).**

Starting from the heat-floor `hheat : UniformFloor (heatEWA u₀E) δ` (the single
positivity input, χ₀<0 enters through the Picard map `picardEWA`), the ball-radius
smallness `hρδ : ρ ≤ δ` (so the ball-floor `δ − ρ ≥ 0`) together with `0 < δ − ρ`
(`hδρpos`), and the brick-1 analytic side-data uniform on the ball
(radius `R`, derivative bounds `Md`/`Mdv`, the `1+v` floor `δv`), the floor-ball lemma
discharges the carried `hLipQ`/`hLipG` of `picardEWA_exists_fixedPoint` with the uniform
constants `L_Q`/`L_G`.  Feeding the self-map `hself` and the small-time contraction
`hK`/`hKnn` yields the fixed point `∃ u* ∈ B, u* = Φ(u*)`. -/
theorem picardEWA_abs_fixedPoint {p : CM2Params} {μ ν γ ρ δ δv Md Mdv R L_Q L_G : ℝ}
    (hμ : 0 < μ) (hT : 0 ≤ T) (u₀E : WA 1) (hρ : 0 ≤ ρ)
    (hγ : 0 ≤ γ) (hMd : 0 ≤ Md) (hMdv : 0 ≤ Mdv) (hR : 0 ≤ R)
    (hδρpos : 0 < δ - ρ) (hδvpos : 0 < δv)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ)
    -- the brick-1 side-data, uniform on the ball:
    (hMD : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ, ‖GWA.gDeriv u‖ ≤ Md)
    (hRad : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ, ‖u‖ ≤ R)
    (hVdFloor : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      UniformFloor (1 + vdEWA μ ν γ hμ u) δv)
    (hVdD : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      ‖GWA.gDeriv (vdEWA μ ν γ hμ u)‖ ≤ Mdv)
    -- the brick-1 Lipschitz constants pinned to the ball-floor `δ − ρ`:
    (hLQ : L_Q = (Real.pi * (GWA.resolverGainConst μ * (|ν| *
              (R ^ (Nat.floor γ + 1)
                * negNormConst ((Nat.floor γ + 1 : ℝ) - γ) (δ - ρ) Md))))
            * negNormConst p.β δv Mdv * 1
          + R * negNormConst p.β δv Mdv * (Real.pi * (GWA.resolverGainConst μ * (|ν| *
              ((Nat.floor γ + 1 : ℝ) * R ^ ((Nat.floor γ + 1) - 1)
                  * negNormConst ((Nat.floor γ + 1 : ℝ) - γ) (δ - ρ) Md
                + R ^ (Nat.floor γ + 1)
                  * negLipConst ((Nat.floor γ + 1 : ℝ) - γ) (δ - ρ) Md))))
          + R * (Real.pi * (GWA.resolverGainConst μ * (|ν| *
              (R ^ (Nat.floor γ + 1)
                * negNormConst ((Nat.floor γ + 1 : ℝ) - γ) (δ - ρ) Md))))
            * (negLipConst p.β δv Mdv * (GWA.resolverGainConst μ * (|ν| *
                ((Nat.floor γ + 1 : ℝ) * R ^ ((Nat.floor γ + 1) - 1)
                    * negNormConst ((Nat.floor γ + 1 : ℝ) - γ) (δ - ρ) Md
                  + R ^ (Nat.floor γ + 1)
                    * negLipConst ((Nat.floor γ + 1 : ℝ) - γ) (δ - ρ) Md)))))
    (hLG : L_G = R * (|p.b| * ((Nat.floor p.α + 1 : ℝ) * R ^ ((Nat.floor p.α + 1) - 1)
              * negNormConst ((Nat.floor p.α + 1 : ℝ) - p.α) (δ - ρ) Md
            + R ^ (Nat.floor p.α + 1)
              * negLipConst ((Nat.floor p.α + 1 : ℝ) - p.α) (δ - ρ) Md))
          + (|p.a| * ‖(1 : EWA T 1)‖ + |p.b| *
              (R ^ (Nat.floor p.α + 1)
                * negNormConst ((Nat.floor p.α + 1 : ℝ) - p.α) (δ - ρ) Md)))
    (hβ : 0 < p.β) (hα : 0 ≤ p.α)
    -- the self-map (brick 2) and the small-time contraction (brick 3):
    (hself : MapsTo (picardEWA p μ ν γ hμ hT u₀E)
      (Metric.closedBall (heatEWA u₀E) ρ) (Metric.closedBall (heatEWA u₀E) ρ))
    (hKnn : (0 : ℝ) ≤ |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T)
    (hK : |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T < 1) :
    ∃ u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      u_star = picardEWA p μ ν γ hμ hT u₀E u_star := by
  -- the common ball-floor on `u` (for the WL1 power) from the heat-floor.
  have hfloor : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      UniformFloor u (δ - ρ) := fun u hu => uniformFloor_on_ball hheat hu
  -- discharge `hLipQ` via `chemFluxEWA_lipschitz` with the uniform ball-floor `δ − ρ`.
  have hLipQ : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      ∀ w ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      ‖chemFluxEWA μ ν p.β γ hμ u - chemFluxEWA μ ν p.β γ hμ w‖ ≤ L_Q * ‖u - w‖ := by
    intro u hu w hw
    rw [hLQ]
    exact chemFluxEWA_lipschitz hμ hγ hβ hδρpos hδvpos hMd hMdv (hfloor u hu) (hfloor w hw)
      (hMD u hu) (hMD w hw) (hRad u hu) (hRad w hw) hR (hVdFloor u hu) (hVdFloor w hw)
      (hVdD u hu) (hVdD w hw)
  -- discharge `hLipG` via `growthEWA_lipschitz` with the same uniform ball-floor.
  have hLipG : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      ∀ w ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      ‖growthEWA p.α p.a p.b u - growthEWA p.α p.a p.b w‖ ≤ L_G * ‖u - w‖ := by
    intro u hu w hw
    rw [hLG]
    exact growthEWA_lipschitz hα hδρpos hMd (hfloor u hu) (hfloor w hw)
      (hMD u hu) (hMD w hw) (hRad u hu) (hRad w hw) hR
  -- feed the conditional fixed point with the discharged data.
  exact picardEWA_exists_fixedPoint hμ hT u₀E hρ hself hLipQ hLipG hKnn hK

end ShenWork.EWA

#print axioms ShenWork.EWA.evalST_incl_re_abs_le
#print axioms ShenWork.EWA.uniformFloor_of_ball
#print axioms ShenWork.EWA.picardEWA_abs_fixedPoint
