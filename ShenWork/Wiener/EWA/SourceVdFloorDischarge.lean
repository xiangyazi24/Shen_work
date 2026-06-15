import ShenWork.Wiener.EWA.SourceResolverFloor
import ShenWork.Wiener.EWA.SourceFixedPointAbs
import ShenWork.Wiener.EWA.SourceFixedPointClean

/-!
# EWA brick (χ₀<0 Route A′) — DISCHARGING the carried `hVdFloor` ball-hypothesis

`picardEWA_abs_fixedPoint` (`SourceFixedPointAbs.lean`) carries the ∀-ball hypothesis
`hVdFloor : ∀ u ∈ closedBall (heatEWA u₀E) ρ, UniformFloor (1 + vdEWA μ ν γ hμ u) δv`.
This file collapses that ball hypothesis to a SINGLE concrete center floor through a
two-layer reduction (a nonlinear floor-ball lemma + a center floor), then assembles the
discharge.

## LAYER 1 — the nonlinear floor-ball lemma (`vdUniformFloor_of_ball`)

Mirrors `uniformFloor_of_ball` exactly but on the *nonlinear* `1 + vdEWA · u`: at each
`(τ,x)`, write `1 + vdEWA u = (1 + vdEWA center) + (vdEWA u − vdEWA center)`; `incl` is a
CLM and `evalST` a ring hom, so the real part splits as `(≥ δc) + (≥ −b)`.  The
perturbation is dominated by `evalST_incl_re_abs_le` together with the resolver-distance
bound `hb`.

## LAYER 2 — the center floor (`vdEWA_center_floor`)

Re-derives `vdEWA_uniformFloor`'s body but with PER-τ realization data (`uR τ.1`, `f τ`)
instead of a single frozen `uR`, because the heat center is τ-dependent.  The per-slice
realization sub-inputs (`hWslice`/`hsum`/`hf_*`) — the FnegEWA fractional-power realization,
the framework-wide carried analytic atom — are carried as NAMED hypotheses.

## LAYER 3 — the discharge (`picardEWA_abs_fixedPoint_vdDischarged`)

The ball-floor on `u` (`δ−ρ`) comes from `uniformFloor_on_ball hheat`; the per-ball
resolver distance `b := Lv·ρ` comes from `vdEWA_lipschitz` (center at distance `0` from
itself; `u` at distance `≤ ρ`).  `vdUniformFloor_of_ball` with `δc = 1` then yields
`UniformFloor (1 + vdEWA u) (1 − Lv·ρ)`, and `hsmall : Lv·ρ ≤ 1 − δv` drops the floor to
`δv` (monotone-decreasing floor lemma `UniformFloor.mono`).  The discharged `hVdFloor`
feeds `picardEWA_abs_fixedPoint`.

No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/

open scoped BigOperators
open Set Metric
open ShenWork.GWA ShenWork.Wiener ShenWork.CosineSpectrum
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.PDE (intervalNeumannResolverR intervalNeumannResolverCoeff
  intervalNeumannResolverSourceCoeff)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### LAYER 1 — the nonlinear floor-ball lemma. -/

/-- **A trivial monotone-decreasing property of `UniformFloor`.** A floor of `a` implies
any smaller floor `b ≤ a`. -/
theorem UniformFloor.mono {F : EWA T 1} {a b : ℝ} (h : UniformFloor F a) (hba : b ≤ a) :
    UniformFloor F b := fun τ x => le_trans hba (h τ x)

/-- **The nonlinear floor-ball lemma** (`C_eval = 1`).  If the resolved center field
`1 + vdEWA center` has uniform floor `δc` and the resolver distance
`‖vdEWA u − vdEWA center‖ ≤ b`, then `1 + vdEWA u` has floor `δc − b`.

Mirrors `uniformFloor_of_ball`: at every `(τ,x)`, `incl` is additive (a CLM) so
`Re(evalST(incl(1+vdEWA u))) = Re(evalST(incl(1+vdEWA center)))
  + Re(evalST(incl(vdEWA u − vdEWA center)))`, where the first summand is `≥ δc` by `hc`
and the second is `≥ −‖vdEWA u − vdEWA center‖ ≥ −b` by `evalST_incl_re_abs_le`. -/
theorem vdUniformFloor_of_ball {μ ν γ : ℝ} (hμ : 0 < μ) {center u : EWA T 1} {δc b : ℝ}
    (hc : UniformFloor (1 + vdEWA μ ν γ hμ center) δc)
    (hb : ‖vdEWA μ ν γ hμ u - vdEWA μ ν γ hμ center‖ ≤ b) :
    UniformFloor (1 + vdEWA μ ν γ hμ u) (δc - b) := by
  intro τ x
  -- write `1 + vdEWA u = (1 + vdEWA center) + (vdEWA u − vdEWA center)`.
  set g : EWA T 1 := vdEWA μ ν γ hμ u - vdEWA μ ν γ hμ center with hg
  have hsplit : (1 + vdEWA μ ν γ hμ u) = (1 + vdEWA μ ν γ hμ center) + g := by
    rw [hg]; ring
  -- additivity of `incl` (a CLM) and `evalST` (a ring hom).
  have hincl : GWA.incl (by omega : (0:ℕ) ≤ 1) (1 + vdEWA μ ν γ hμ u)
      = GWA.incl (by omega : (0:ℕ) ≤ 1) (1 + vdEWA μ ν γ hμ center)
        + GWA.incl (by omega : (0:ℕ) ≤ 1) g := by
    rw [hsplit, ContinuousLinearMap.map_add]
  have heval : evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) (1 + vdEWA μ ν γ hμ u))
      = evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) (1 + vdEWA μ ν γ hμ center))
        + evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) g) := by
    rw [hincl, RingHom.map_add]
  have hadd : (evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) (1 + vdEWA μ ν γ hμ u))).re
      = (evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) (1 + vdEWA μ ν γ hμ center))).re
        + (evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) g)).re := by
    rw [heval, Complex.add_re]
  rw [hadd]
  have hfloor : δc ≤ (evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1)
      (1 + vdEWA μ ν γ hμ center))).re := hc τ x
  have hpert : |(evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) g)).re| ≤ b :=
    le_trans (evalST_incl_re_abs_le τ x g) hb
  have hge : -b ≤ (evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) g)).re :=
    (abs_le.mp hpert).1
  linarith

/-! ### LAYER 2 — the center floor (carried heat-realization sub-inputs). -/

/-- **THE CENTER FLOOR.**  For the heat center `heatEWA u₀E`, whose resolver slice at every
time `τ` realizes the resolver source of a *nonneg continuous* real source `f τ` of the
PER-τ heat realization `uR τ.1` (the carried per-slice realization sub-inputs
`hWslice`/`hsum`/`hf_*`, the FnegEWA fractional-power realization atom), the resolved center
field `1 + vdEWA μ ν γ hμ (heatEWA u₀E)` has uniform floor `1`.

This is `vdEWA_uniformFloor` re-derived with PER-τ realization data — the heat center is
τ-dependent, so the realization datum `uR τ.1`/`f τ` varies with `τ`.  At every `(τ,x)`:
`evalST(incl(1+vd)) = 1 + evalST(incl(vd))`; the resolver eval bridge (A)
`evalST_gResolver_eq_resolverSynthesis_all` turns the second term into the resolved cosine
synthesis `∑' k (v̂_k).re·cosineMode k x`, which is `≥ 0` by `resolverSynthesis_nonneg_all`
(O1 positivity of the nonneg source `f τ`).  Hence `1 + (≥ 0) ≥ 1`. -/
theorem vdEWA_center_floor (p : CM2Params) (u₀E : WA 1)
    (uR : ℝ → intervalDomainPoint → ℝ)
    (hsum : ∀ τ : TimeDom T, ResolverSourceSummable p (uR τ.1))
    (hWslice : ∀ τ : TimeDom T, (sliceWA τ (GWA.incl (by omega : (0:ℕ) ≤ 1)
        ((p.ν : ℂ) • realPowEWA (heatEWA (T := T) u₀E) p.γ))).toFun
      = ofCosineCoeffs (resolverSourceReCoeff p (uR τ.1)))
    (f : ℝ → ℝ → ℝ) (hf_cont : ∀ τ : TimeDom T, Continuous (f τ.1))
    (hf_nonneg : ∀ (τ : TimeDom T) (y : ℝ), 0 ≤ f τ.1 y)
    (hf_coeff : ∀ (τ : TimeDom T) (k : ℕ),
      cosineCoeffs (f τ.1) k = (intervalNeumannResolverSourceCoeff p (uR τ.1) k).re)
    (hâ : ∀ τ : TimeDom T, Summable (fun k => (cosineCoeffs (f τ.1) k) ^ 2)) :
    UniformFloor (1 + vdEWA p.μ p.ν p.γ p.hμ (heatEWA (T := T) u₀E)) 1 := by
  intro τ x
  -- lift the circle point `x : WA.Circ = AddCircle 2` to a real representative.
  induction x using QuotientAddGroup.induction_on with
  | _ x =>
    -- `evalST(incl(1+vd)) = 1 + evalST(incl(vd))` (ring-hom structure of `evalST ∘ incl`).
    have hincl_one : GWA.incl (by omega : (0:ℕ) ≤ 1) (1 : EWA T 1) = 1 := by
      rw [← GWA.gIncl_apply, map_one]
    have hincl_add :
        GWA.incl (by omega : (0:ℕ) ≤ 1)
            (1 + vdEWA p.μ p.ν p.γ p.hμ (heatEWA (T := T) u₀E))
        = GWA.incl (by omega : (0:ℕ) ≤ 1) (1 : EWA T 1)
          + GWA.incl (by omega : (0:ℕ) ≤ 1)
              (vdEWA p.μ p.ν p.γ p.hμ (heatEWA (T := T) u₀E)) := by
      rw [← GWA.gIncl_apply, map_add, GWA.gIncl_apply, GWA.gIncl_apply]
    -- the resolver value at `x` via the eval bridge (A), with PER-τ realization datum.
    have hvd : evalST τ (x : WA.Circ)
          (GWA.incl (by omega : (0:ℕ) ≤ 1)
            (vdEWA p.μ p.ν p.γ p.hμ (heatEWA (T := T) u₀E)))
        = ((∑' k : ℕ, (intervalNeumannResolverCoeff p (uR τ.1) k).re * cosineMode k x : ℝ)
            : ℂ) := by
      rw [vdEWA, vFieldEWA]
      exact evalST_gResolver_eq_resolverSynthesis_all p (uR τ.1)
        ((p.ν : ℂ) • realPowEWA (heatEWA (T := T) u₀E) p.γ) τ x (hsum τ) (hWslice τ)
    rw [hincl_add, (evalST τ (x : WA.Circ)).map_add, hincl_one,
      (evalST τ (x : WA.Circ)).map_one, hvd]
    -- `Re(1 + (R : ℂ)) = 1 + R ≥ 1`.
    rw [Complex.add_re, Complex.one_re, Complex.ofReal_re]
    have hR : 0 ≤ ∑' k : ℕ,
        (intervalNeumannResolverCoeff p (uR τ.1) k).re * cosineMode k x :=
      resolverSynthesis_nonneg_all p (uR τ.1) (hf_cont τ) (hf_nonneg τ) (hf_coeff τ) (hâ τ) x
    linarith

/-! ### LAYER 3 — the discharge: collapse the ∀-ball `hVdFloor` to the center floor. -/

/-- **THE DISCHARGED χ₀<0 SOURCE-FORM FIXED POINT.**

`picardEWA_abs_fixedPoint` carries `hVdFloor : ∀ u ∈ ball, UniformFloor (1 + vdEWA u) δv`.
Here it is discharged INTERNALLY from the single center floor `vdEWA_center_floor` (carried
through `hcenter`, floor `1`) plus the resolver-Lipschitz constant `Lv` of `vdEWA_lipschitz`
and the smallness `hsmall : Lv·ρ ≤ 1 − δv`:

* the ball-floor on `u` (`δ−ρ`) comes from `uniformFloor_on_ball hheat`;
* for each `u` in the ball, `vdEWA_lipschitz` (with `u` and the center both in the ball,
  the center at distance `0`) gives `‖vdEWA u − vdEWA center‖ ≤ Lv·ρ`;
* `vdUniformFloor_of_ball` (`δc = 1`, `b = Lv·ρ`) yields `UniformFloor (1 + vdEWA u)
  (1 − Lv·ρ)`, and `hsmall` drops it to `δv` via `UniformFloor.mono`.

The discharged `hVdFloor` feeds `picardEWA_abs_fixedPoint`. -/
theorem picardEWA_abs_fixedPoint_vdDischarged
    {p : CM2Params} {ρ δ δv Md Mdv R L_Q L_G : ℝ}
    (hT : 0 ≤ T) (u₀E : WA 1) (hρ : 0 ≤ ρ)
    (hMd : 0 ≤ Md) (hMdv : 0 ≤ Mdv) (hR : 0 ≤ R)
    (hδρpos : 0 < δ - ρ) (hδvpos : 0 < δv)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ)
    -- the brick-1 side-data, uniform on the ball:
    (hMD : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ, ‖GWA.gDeriv u‖ ≤ Md)
    (hRad : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ, ‖u‖ ≤ R)
    (hVdD : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      ‖GWA.gDeriv (vdEWA p.μ p.ν p.γ p.hμ u)‖ ≤ Mdv)
    -- the center is in the ball (distance `0`), so its side-data are the ball's:
    (hcenterMD : ‖GWA.gDeriv (heatEWA (T := T) u₀E)‖ ≤ Md)
    (hcenterR : ‖heatEWA (T := T) u₀E‖ ≤ R)
    -- LAYER 2 center floor, carried:
    (hcenter : UniformFloor (1 + vdEWA p.μ p.ν p.γ p.hμ (heatEWA (T := T) u₀E)) 1)
    -- the resolver-Lipschitz constant and the smallness collapsing `1 − Lv·ρ` to `δv`:
    (hsmall : (GWA.resolverGainConst p.μ * (|p.ν| *
          ((Nat.floor p.γ + 1 : ℝ) * R ^ ((Nat.floor p.γ + 1) - 1)
              * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md
            + R ^ (Nat.floor p.γ + 1)
              * negLipConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md))) * ρ
        ≤ 1 - δv)
    -- the brick-1 Lipschitz constants pinned to the ball-floor `δ − ρ`:
    (hLQ : L_Q = (Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
              (R ^ (Nat.floor p.γ + 1)
                * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md))))
            * negNormConst p.β δv Mdv * 1
          + R * negNormConst p.β δv Mdv
            * (Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
              ((Nat.floor p.γ + 1 : ℝ) * R ^ ((Nat.floor p.γ + 1) - 1)
                  * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md
                + R ^ (Nat.floor p.γ + 1)
                  * negLipConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md))))
          + R * (Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
              (R ^ (Nat.floor p.γ + 1)
                * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md))))
            * (negLipConst p.β δv Mdv * (GWA.resolverGainConst p.μ * (|p.ν| *
                ((Nat.floor p.γ + 1 : ℝ) * R ^ ((Nat.floor p.γ + 1) - 1)
                    * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md
                  + R ^ (Nat.floor p.γ + 1)
                    * negLipConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md)))))
    (hLG : L_G = R * (|p.b| * ((Nat.floor p.α + 1 : ℝ) * R ^ ((Nat.floor p.α + 1) - 1)
              * negNormConst ((Nat.floor p.α + 1 : ℝ) - p.α) (δ - ρ) Md
            + R ^ (Nat.floor p.α + 1)
              * negLipConst ((Nat.floor p.α + 1 : ℝ) - p.α) (δ - ρ) Md))
          + (|p.a| * ‖(1 : EWA T 1)‖ + |p.b| *
              (R ^ (Nat.floor p.α + 1)
                * negNormConst ((Nat.floor p.α + 1 : ℝ) - p.α) (δ - ρ) Md)))
    (hβ : 0 < p.β) (hα : 0 ≤ p.α)
    -- the self-map (brick 2) and the small-time contraction (brick 3):
    (hself : MapsTo (picardEWA p p.μ p.ν p.γ p.hμ hT u₀E)
      (Metric.closedBall (heatEWA u₀E) ρ) (Metric.closedBall (heatEWA u₀E) ρ))
    (hKnn : (0 : ℝ) ≤ |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T)
    (hK : |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T < 1) :
    ∃ u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      u_star = picardEWA p p.μ p.ν p.γ p.hμ hT u₀E u_star := by
  -- the center lies in the ball (distance `0`).
  have hcenter_mem : heatEWA (T := T) u₀E ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ := by
    rw [Metric.mem_closedBall]; simpa using hρ
  -- the ball-floor on `u` (for `vdEWA_lipschitz`'s WL1 power) from the heat-floor.
  have hfloor : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      UniformFloor u (δ - ρ) := fun u hu => uniformFloor_on_ball hheat hu
  -- abbreviate the resolver-Lipschitz constant `Lv` (the `vdEWA_lipschitz` bound).
  set Lv : ℝ := GWA.resolverGainConst p.μ * (|p.ν| *
      ((Nat.floor p.γ + 1 : ℝ) * R ^ ((Nat.floor p.γ + 1) - 1)
          * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md
        + R ^ (Nat.floor p.γ + 1)
          * negLipConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md)) with hLv
  -- `0 ≤ Lv` (the building constants are all nonnegative on the ball-floor `δ−ρ`).
  have hsγ : 0 < (Nat.floor p.γ + 1 : ℝ) - p.γ := by
    have := Nat.lt_floor_add_one p.γ; linarith
  have hnegNγ : (0 : ℝ) ≤ negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md :=
    negNormConst_nonneg hsγ hδρpos hMd
  have hnegLγ : (0 : ℝ) ≤ negLipConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md :=
    negLipConst_nonneg hsγ hδρpos hMd
  have hgain : (0 : ℝ) ≤ GWA.resolverGainConst p.μ := by
    have hμpos : 0 < p.μ := p.hμ
    rw [GWA.resolverGainConst]; positivity
  have hLvnn : (0 : ℝ) ≤ Lv := by
    rw [hLv]
    have hRpow1 : (0 : ℝ) ≤ R ^ ((Nat.floor p.γ + 1) - 1) := by positivity
    have hRpow2 : (0 : ℝ) ≤ R ^ (Nat.floor p.γ + 1) := by positivity
    have hfloornn : (0 : ℝ) ≤ (Nat.floor p.γ + 1 : ℝ) := by positivity
    have : (0 : ℝ) ≤ (Nat.floor p.γ + 1 : ℝ) * R ^ ((Nat.floor p.γ + 1) - 1)
            * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md
          + R ^ (Nat.floor p.γ + 1)
            * negLipConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md := by
      have h1 : (0:ℝ) ≤ (Nat.floor p.γ + 1 : ℝ) * R ^ ((Nat.floor p.γ + 1) - 1)
          * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md := by
        apply mul_nonneg (mul_nonneg hfloornn hRpow1) hnegNγ
      have h2 : (0:ℝ) ≤ R ^ (Nat.floor p.γ + 1)
          * negLipConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md :=
        mul_nonneg hRpow2 hnegLγ
      linarith
    exact mul_nonneg hgain (mul_nonneg (abs_nonneg _) this)
  -- DISCHARGE `hVdFloor`: each `u` in the ball gets the floor `δv`.
  have hVdFloor : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      UniformFloor (1 + vdEWA p.μ p.ν p.γ p.hμ u) δv := by
    intro u hu
    -- the resolver distance `‖vdEWA u − vdEWA center‖ ≤ Lv·ρ` from `vdEWA_lipschitz`.
    have hdist_le : ‖u - heatEWA (T := T) u₀E‖ ≤ ρ := by
      have := hu; rw [Metric.mem_closedBall, dist_eq_norm] at this; exact this
    have hlip : ‖vdEWA p.μ p.ν p.γ p.hμ u
          - vdEWA p.μ p.ν p.γ p.hμ (heatEWA (T := T) u₀E)‖
        ≤ Lv * ‖u - heatEWA (T := T) u₀E‖ := by
      rw [hLv]
      exact vdEWA_lipschitz p.hμ p.hγ.le hδρpos hMd (hfloor u hu) (hfloor _ hcenter_mem)
        (hMD u hu) hcenterMD (hRad u hu) hcenterR hR
    have hb : ‖vdEWA p.μ p.ν p.γ p.hμ u
          - vdEWA p.μ p.ν p.γ p.hμ (heatEWA (T := T) u₀E)‖
        ≤ Lv * ρ :=
      le_trans hlip (mul_le_mul_of_nonneg_left hdist_le hLvnn)
    -- floor-ball (`δc = 1`, `b = Lv·ρ`) then drop the floor to `δv` via `hsmall`.
    have hfb : UniformFloor (1 + vdEWA p.μ p.ν p.γ p.hμ u) (1 - Lv * ρ) :=
      vdUniformFloor_of_ball p.hμ hcenter hb
    exact hfb.mono (by rw [hLv] at hsmall ⊢; linarith)
  -- feed the discharged data into `picardEWA_abs_fixedPoint`.
  exact picardEWA_abs_fixedPoint p.hμ hT u₀E hρ p.hγ.le hMd hMdv hR hδρpos hδvpos hheat
    hMD hRad hVdFloor hVdD hLQ hLG hβ hα hself hKnn hK

end ShenWork.EWA
