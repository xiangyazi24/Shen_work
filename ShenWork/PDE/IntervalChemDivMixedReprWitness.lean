import ShenWork.PDE.IntervalChemDivMixedReprConstruct
import ShenWork.PDE.IntervalIteratePicardJointC2
import ShenWork.PDE.IntervalCosineSliceRegularity
import ShenWork.PDE.IntervalResolverJointC2PhysicalConcrete

/-!
# Assembling the `ChemDivMixedReprData` witness

This file BUILDS a concrete `ChemDivMixedReprData p u τ δ` witness, feeding
`chemDivMixedTimeDerivClosedRepr_of_data` and so discharging `htime_cont` (the
`χ₀<0` regularity half) down to the honest spectral/time/floor data.

`coupledChemDivTimeDerivativeLift p u t x = ∂ₓ (flux-time-deriv)` where the flux
time derivative is the explicit three-term algebraic combination of the slice
fields `U,Ut,v,vt` and their `x`-gradients.  `mixedAlgebra` is that outer `∂ₓ`
written explicitly (product/quotient/`rpow` rule on the three terms).

The witness consists of:
* **the spatial `∂ₓ` chain rule** `fluxTimeDeriv_hasDerivAt_space` — the pointwise
  identity `∂ₓ(flux-time-deriv)(x) = mixedAlgebra(reps)(t,x)`, from `HasDerivAt`
  facts of the six base fields and their needed `x`-derivatives (this discharges
  `agree`);
* **globally-continuous representatives** of the ten slice quantities, supplied as
  an honest reduction bundle `ChemDivMixedReprWitnessData` whose continuous
  representatives come from the bounded-weight value/grad/time joint series
  (v-side from `PhysicalResolverJointC2Data`, u-side from the iterate joint data),
  and whose closed-slab `HasDerivAt` connections come from those series + the
  endpoint junk-value/Neumann boundary facts.

The honest analytic input is exactly: globally-continuous closed-slab
representatives of `{U,∂ₜU,∂ₓ∂ₜU,∂ₓU, v,∂ₓv,∂ₓ²v,∂ₜv,∂ₓ∂ₜv,∂ₓ²∂ₜv}`, with the
closed-slab `HasDerivAt` facts identifying each `mixedAlgebra` base factor with the
corresponding `x`-derivative of the lift, the floor `1+v>0`, and the rep-value =
lift-value matching on the closed slab.  No outer-commute atom, no resolver `C²`
field, no FAC conclusion, no `htime_cont` hypothesis.
-/

open ShenWork.IntervalDomain
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalChemDivMixedReprConstruct
open ShenWork.IntervalResolverJointC2Physical
open ShenWork.IntervalResolverJointC2PhysicalConcrete (resolverTimeCoeff
  PhysicalResolverJointC2Data coupledChemical_lift_eq_series)
open ShenWork.IntervalResolverSpectralJointC2Concrete (valueCosWeight gradCosWeight)
open ShenWork.CosineSpectrum (cosineMode cosineMode_deriv)
open ShenWork.IntervalDuhamelClosedC2 (cosineCoeffSeries_grad_hasDerivAt
  cosineCoeffSeries_grad2_hasDerivAt)
open Set Filter Topology

noncomputable section

namespace ShenWork.IntervalChemDivMixedReprWitness

/-! ## The spatial `∂ₓ` chain rule producing `mixedAlgebra`. -/

/-- **Algebraic spatial-derivative chain rule.**  The flux time-derivative is the
three-term combination
  `Ut·Vx/B^β + U·Vtx/B^β − β·U·Vx·Vt/B^(β+1)`, `B = 1+V`.
Differentiating in `x` with the product/quotient/`rpow` rule, with the `x`-deriv
facts `U'=Ux, Ut'=Utx, V'=Vx, Vx'=Vxx, Vt'=Vtx, Vtx'=Vtxx`, gives the six-factor
`mixedAlgebra` value. -/
theorem fluxTimeDeriv_hasDerivAt_space
    (β : ℝ) {U Ut Utx Ux V Vx Vxx Vt Vtx Vtxx x : ℝ}
    {Uf Utf Vf Vxf Vtf Vtxf : ℝ → ℝ}
    (hU : HasDerivAt Uf Ux x) (hUval : Uf x = U)
    (hUt : HasDerivAt Utf Utx x) (hUtval : Utf x = Ut)
    (hV : HasDerivAt Vf Vx x) (hVval : Vf x = V)
    (hVx : HasDerivAt Vxf Vxx x) (hVxval : Vxf x = Vx)
    (hVt : HasDerivAt Vtf Vtx x) (hVtval : Vtf x = Vt)
    (hVtx : HasDerivAt Vtxf Vtxx x) (hVtxval : Vtxf x = Vtx)
    (hB : 0 < 1 + V) :
    HasDerivAt
      (fun y : ℝ =>
        Utf y * Vxf y / (1 + Vf y) ^ β +
          Uf y * Vtxf y / (1 + Vf y) ^ β -
          β * Uf y * Vxf y * Vtf y / (1 + Vf y) ^ (β + 1))
      (((Utx * Vx + Ut * Vxx) / (1 + V) ^ β - β * Ut * Vx * Vx / (1 + V) ^ (β + 1)) +
        ((Ux * Vtx + U * Vtxx) / (1 + V) ^ β - β * U * Vtx * Vx / (1 + V) ^ (β + 1)) -
        (β * (Ux * Vx * Vt + U * Vxx * Vt + U * Vx * Vtx) / (1 + V) ^ (β + 1)
          - β * (β + 1) * U * Vx * Vt * Vx / (1 + V) ^ (β + 2)))
      x := by
  subst hUval hUtval hVval hVxval hVtval hVtxval
  set B := 1 + Vf x with hBdef
  have hBpos : 0 < B := hB
  have hBne : B ≠ 0 := ne_of_gt hBpos
  have hBb : B ^ β ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hBpos β)
  have hBb1 : B ^ (β + 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hBpos (β + 1))
  have hBb2 : B ^ (β + 2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hBpos (β + 2))
  -- `B(y) = 1 + Vf y` has deriv `Vxf x`.
  have hBd : HasDerivAt (fun y => 1 + Vf y) (Vxf x) x := by
    have h := (hasDerivAt_const x (1 : ℝ)).add hV
    simpa only [zero_add] using h
  -- `B^β`, deriv `Vxf x·β·B^(β-1)`.
  have hPβ : HasDerivAt (fun y => (1 + Vf y) ^ β) (Vxf x * β * B ^ (β - 1)) x := by
    have h := hBd.rpow_const (x := x) (p := β) (Or.inl hBne)
    simpa only [hBdef] using h
  have hPβ1 : HasDerivAt (fun y => (1 + Vf y) ^ (β + 1))
      (Vxf x * (β + 1) * B ^ (β + 1 - 1)) x := by
    have h := hBd.rpow_const (x := x) (p := β + 1) (Or.inl hBne)
    simpa only [hBdef] using h
  -- Term 1: `Utf·Vxf / B^β`.
  have hT1 : HasDerivAt (fun y => Utf y * Vxf y / (1 + Vf y) ^ β)
      (((Utx * Vxf x + Utf x * Vxx) * B ^ β - Utf x * Vxf x * (Vxf x * β * B ^ (β - 1)))
        / (B ^ β) ^ 2) x :=
    ((hUt.mul hVx).div hPβ hBb)
  -- Term 2: `Uf·Vtxf / B^β`.
  have hT2 : HasDerivAt (fun y => Uf y * Vtxf y / (1 + Vf y) ^ β)
      (((Ux * Vtxf x + Uf x * Vtxx) * B ^ β - Uf x * Vtxf x * (Vxf x * β * B ^ (β - 1)))
        / (B ^ β) ^ 2) x :=
    ((hU.mul hVtx).div hPβ hBb)
  -- Term 3: `β·Uf·Vxf·Vtf / B^(β+1)`.
  have hN3 : HasDerivAt (fun y => β * Uf y * Vxf y * Vtf y)
      (β * (Ux * Vxf x * Vtf x + Uf x * Vxx * Vtf x + Uf x * Vxf x * Vtxf x)) x := by
    have h := (((hasDerivAt_const x β).mul hU).mul hVx).mul hVt
    have he : (((0 : ℝ) * Uf x + β * Ux) * Vxf x + β * Uf x * Vxx) * Vtf x
        + β * Uf x * Vxf x * Vtxf x
        = β * (Ux * Vxf x * Vtf x + Uf x * Vxx * Vtf x + Uf x * Vxf x * Vtxf x) := by ring
    rw [← he]; exact h
  have hT3 : HasDerivAt (fun y => β * Uf y * Vxf y * Vtf y / (1 + Vf y) ^ (β + 1))
      ((β * (Ux * Vxf x * Vtf x + Uf x * Vxx * Vtf x + Uf x * Vxf x * Vtxf x) * B ^ (β + 1)
        - β * Uf x * Vxf x * Vtf x * (Vxf x * (β + 1) * B ^ (β + 1 - 1)))
        / (B ^ (β + 1)) ^ 2) x := by
    exact hN3.div hPβ1 hBb1
  have hsum := (hT1.add hT2).sub hT3
  convert hsum using 1
  -- Reduce each quotient to the `mixedAlgebra` shape.  Two helper ratio facts:
  -- `B^(β-1)/(B^β)^2 = 1/B^(β+1)` and `B^(β+1-1)/(B^(β+1))^2 = 1/B^(β+2)`.
  have hr1 : B ^ (β - 1) / (B ^ β) ^ 2 = 1 / B ^ (β + 1) := by
    rw [← Real.rpow_natCast (B ^ β) 2, ← Real.rpow_mul hBpos.le, ← Real.rpow_sub hBpos,
      show β - 1 - β * (2 : ℕ) = -(β + 1) by push_cast; ring,
      Real.rpow_neg hBpos.le, one_div]
  have hr2 : B ^ (β + 1 - 1) / (B ^ (β + 1)) ^ 2 = 1 / B ^ (β + 2) := by
    rw [← Real.rpow_natCast (B ^ (β + 1)) 2, ← Real.rpow_mul hBpos.le,
      ← Real.rpow_sub hBpos,
      show β + 1 - 1 - (β + 1) * (2 : ℕ) = -(β + 2) by push_cast; ring,
      Real.rpow_neg hBpos.le, one_div]
  -- Split each `(num·B^e - tail·B^(e-1))/(B^e)^2` into the two `mixedAlgebra` terms.
  -- self-ratio facts `B^e/(B^e)^2 = 1/B^e`.
  have hself1 : B ^ β / (B ^ β) ^ 2 = 1 / B ^ β := by
    rw [sq, ← div_div, div_self hBb]
  have hself2 : B ^ (β + 1) / (B ^ (β + 1)) ^ 2 = 1 / B ^ (β + 1) := by
    rw [sq, ← div_div, div_self hBb1]
  have hsplit1 : ∀ (a c : ℝ),
      (a * B ^ β - c * (Vxf x * β * B ^ (β - 1))) / (B ^ β) ^ 2
        = a / B ^ β - β * (c * Vxf x) / B ^ (β + 1) := by
    intro a c
    rw [sub_div, mul_div_assoc, hself1,
      show c * (Vxf x * β * B ^ (β - 1)) = (β * (c * Vxf x)) * B ^ (β - 1) by ring,
      mul_div_assoc, hr1, mul_one_div, mul_one_div]
  have hsplit2 : ∀ (a c : ℝ),
      (a * B ^ (β + 1) - c * (Vxf x * (β + 1) * B ^ (β + 1 - 1))) / (B ^ (β + 1)) ^ 2
        = a / B ^ (β + 1) - (β + 1) * (c * Vxf x) / B ^ (β + 2) := by
    intro a c
    rw [sub_div, mul_div_assoc, hself2,
      show c * (Vxf x * (β + 1) * B ^ (β + 1 - 1))
          = ((β + 1) * (c * Vxf x)) * B ^ (β + 1 - 1) by ring,
      mul_div_assoc, hr2, mul_one_div, mul_one_div]
  rw [hsplit1 (Utx * Vxf x + Utf x * Vxx) (Utf x * Vxf x),
      hsplit1 (Ux * Vtxf x + Uf x * Vtxx) (Uf x * Vtxf x),
      hsplit2 (β * (Ux * Vxf x * Vtf x + Uf x * Vxx * Vtf x + Uf x * Vxf x * Vtxf x))
        (β * Uf x * Vxf x * Vtf x)]
  ring

/-! ## The honest reduction bundle and the `ChemDivMixedReprData` witness. -/

/-- **Honest reduction bundle for the mixed-time-derivative representative.**

Ten globally-continuous closed-slab representatives of the slice quantities
`{U,∂ₜU,∂ₓ∂ₜU,∂ₓU, v,∂ₓv,∂ₓ²v,∂ₜv,∂ₓ∂ₜv,∂ₓ²∂ₜv}`, plus, at every closed-slab
point, the `HasDerivAt`-in-`x` facts identifying the six base flux factors with
their `x`-derivatives (the rep values), the closed-slab value matches of the four
"value" reps `Uc,Utc,Vc,Vtc` with the corresponding lift slice fields, and the
floor `1+Vc>0`.  Each rep is the bounded-weight value/grad/time joint series, so
its global continuity is `ContDiff`/`Continuous`; the `HasDerivAt` facts come from
the series term-by-term differentiation, holding on the *closed* `Icc 0 1` because
the gradient sin-series vanish at the endpoints.  No outer-commute atom, no
resolver `C²` field, no FAC conclusion, no `htime_cont` hypothesis. -/
structure ChemDivMixedReprWitnessData
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ δ : ℝ) where
  Uc : ℝ × ℝ → ℝ
  Utc : ℝ × ℝ → ℝ
  Utxc : ℝ × ℝ → ℝ
  Uxc : ℝ × ℝ → ℝ
  Vc : ℝ × ℝ → ℝ
  Vxc : ℝ × ℝ → ℝ
  Vxxc : ℝ × ℝ → ℝ
  Vtc : ℝ × ℝ → ℝ
  Vtxc : ℝ × ℝ → ℝ
  Vtxxc : ℝ × ℝ → ℝ
  cont_Uc : Continuous Uc
  cont_Utc : Continuous Utc
  cont_Utxc : Continuous Utxc
  cont_Uxc : Continuous Uxc
  cont_Vc : Continuous Vc
  cont_Vxc : Continuous Vxc
  cont_Vxxc : Continuous Vxxc
  cont_Vtc : Continuous Vtc
  cont_Vtxc : Continuous Vtxc
  cont_Vtxxc : Continuous Vtxxc
  floor : ∀ q : ℝ × ℝ, 0 < 1 + Vc q
  /-- `U`-value rep agrees with the lifted iterate on the closed slab. -/
  Uc_eq : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
    Uc (t, x) = intervalDomainLift (u t) x
  /-- `∂ₜU`-value rep agrees with `slopeSlice` on the closed slab. -/
  Utc_eq : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
    Utc (t, x) = ShenWork.Paper2.PicardLimitK1.slopeSlice u t x
  /-- `v`-value rep agrees with the lifted concentration on the closed slab. -/
  Vc_eq : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
    Vc (t, x) = intervalDomainLift (coupledChemicalConcentration p u t) x
  /-- `∂ₜv`-value rep agrees with the time-derivative lift on the closed slab. -/
  Vtc_eq : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
    Vtc (t, x) = coupledChemicalTimeDerivativeLift p u t x
  /-- `∂ₓU`: at each *interior* point, `lift u` has `x`-deriv `Uxc`. -/
  hUx : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Ioo (0 : ℝ) 1,
    HasDerivAt (fun y => intervalDomainLift (u t) y) (Uxc (t, x)) x
  /-- `∂ₓ∂ₜU`: at each *interior* point, `slopeSlice` has `x`-deriv `Utxc`. -/
  hUtx : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Ioo (0 : ℝ) 1,
    HasDerivAt (fun y => ShenWork.Paper2.PicardLimitK1.slopeSlice u t y)
      (Utxc (t, x)) x
  /-- `∂ₓv`: at each *interior* point, `lift v` has `x`-deriv `Vxc`. -/
  hVx : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Ioo (0 : ℝ) 1,
    HasDerivAt (fun y => intervalDomainLift (coupledChemicalConcentration p u t) y)
      (Vxc (t, x)) x
  /-- `∂ₓ²v`: at each *interior* point, the `∂ₓv` field has `x`-deriv `Vxxc`. -/
  hVxx : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Ioo (0 : ℝ) 1,
    HasDerivAt
      (fun y => deriv (intervalDomainLift (coupledChemicalConcentration p u t)) y)
      (Vxxc (t, x)) x
  /-- `∂ₓ∂ₜv`: at each *interior* point, `∂ₜv` has `x`-deriv `Vtxc`. -/
  hVtx : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Ioo (0 : ℝ) 1,
    HasDerivAt (fun y => coupledChemicalTimeDerivativeLift p u t y) (Vtxc (t, x)) x
  /-- `∂ₓ²∂ₜv`: at each *interior* point, `∂ₓ∂ₜv` has `x`-deriv `Vtxxc`. -/
  hVtxx : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Ioo (0 : ℝ) 1,
    HasDerivAt (fun y => deriv (coupledChemicalTimeDerivativeLift p u t) y)
      (Vtxxc (t, x)) x
  /-- The `∂ₓv` rep `Vxc` agrees with `deriv (lift v)` on the *interior*. -/
  Vxc_eq : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Ioo (0 : ℝ) 1,
    Vxc (t, x) = deriv (intervalDomainLift (coupledChemicalConcentration p u t)) x
  /-- The `∂ₓ∂ₜv` rep `Vtxc` agrees with `deriv (∂ₜv)` on the *interior*. -/
  Vtxc_eq : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Ioo (0 : ℝ) 1,
    Vtxc (t, x) = deriv (coupledChemicalTimeDerivativeLift p u t) x
  /-- **Boundary leg.**  At the endpoints `x ∈ {0,1}` the lift is non-differentiable
  (junk-value), so the outer `∂ₓ` of the flux time-derivative is the junk-value
  `0`, matched to `mixedAlgebra` of the reps at the endpoint by the Neumann
  sin-series boundary fact.  Supplied directly. -/
  boundary_agree : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ ({0, 1} : Set ℝ),
    coupledChemDivTimeDerivativeLift p u t x =
      mixedAlgebra p.β Uc Utc Utxc Uxc Vc Vxc Vxxc Vtc Vtxc Vtxxc (t, x)

/-- **The `agree` field, derived.**  At each closed-slab point the committed
`coupledChemDivTimeDerivativeLift` (the outer `∂ₓ` of the three-term flux) equals
`mixedAlgebra` of the ten representatives, by the spatial chain rule
`fluxTimeDeriv_hasDerivAt_space` instantiated with the bundle's `HasDerivAt`
facts and value matches. -/
theorem witness_agree
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {τ δ : ℝ}
    (W : ChemDivMixedReprWitnessData p u τ δ)
    (t : ℝ) (ht : t ∈ Icc (τ - δ) (τ + δ)) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    coupledChemDivTimeDerivativeLift p u t x =
      mixedAlgebra p.β W.Uc W.Utc W.Utxc W.Uxc W.Vc W.Vxc W.Vxxc
        W.Vtc W.Vtxc W.Vtxxc (t, x) := by
  -- Split closed `[0,1]` into the open interior and the two endpoints.
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · exact W.boundary_agree t ht x (by simp [← hx0])
  rcases eq_or_lt_of_le hx.2 with hx1 | hx1
  · exact W.boundary_agree t ht x (by simp [hx1])
  have hxIoo : x ∈ Ioo (0 : ℝ) 1 := ⟨hx0, hx1⟩
  have hfloor : 0 < 1 + intervalDomainLift (coupledChemicalConcentration p u t) x := by
    have := W.floor (t, x); rwa [W.Vc_eq t ht x hx] at this
  -- The spatial chain rule, with reps as the derivative/value data.
  have hderiv := fluxTimeDeriv_hasDerivAt_space (β := p.β) (x := x)
    (Uf := fun y => intervalDomainLift (u t) y)
    (Utf := fun y => ShenWork.Paper2.PicardLimitK1.slopeSlice u t y)
    (Vf := fun y => intervalDomainLift (coupledChemicalConcentration p u t) y)
    (Vxf := fun y => deriv (intervalDomainLift (coupledChemicalConcentration p u t)) y)
    (Vtf := fun y => coupledChemicalTimeDerivativeLift p u t y)
    (Vtxf := fun y => deriv (coupledChemicalTimeDerivativeLift p u t) y)
    (hU := W.hUx t ht x hxIoo) (hUval := rfl)
    (hUt := W.hUtx t ht x hxIoo) (hUtval := rfl)
    (hV := W.hVx t ht x hxIoo) (hVval := rfl)
    (hVx := W.hVxx t ht x hxIoo) (hVxval := (W.Vxc_eq t ht x hxIoo).symm)
    (hVt := W.hVtx t ht x hxIoo) (hVtval := rfl)
    (hVtx := W.hVtxx t ht x hxIoo) (hVtxval := (W.Vtxc_eq t ht x hxIoo).symm)
    (hB := hfloor)
  -- `coupledChemDivTimeDerivativeLift p u t x` is *definitionally* `deriv (flux) x`.
  have hcdt : coupledChemDivTimeDerivativeLift p u t x =
      deriv (fun y : ℝ =>
        ShenWork.Paper2.PicardLimitK1.slopeSlice u t y *
            deriv (intervalDomainLift (coupledChemicalConcentration p u t)) y /
            (1 + intervalDomainLift (coupledChemicalConcentration p u t) y) ^ p.β +
          intervalDomainLift (u t) y *
            deriv (coupledChemicalTimeDerivativeLift p u t) y /
            (1 + intervalDomainLift (coupledChemicalConcentration p u t) y) ^ p.β -
          p.β * intervalDomainLift (u t) y *
            deriv (intervalDomainLift (coupledChemicalConcentration p u t)) y *
            coupledChemicalTimeDerivativeLift p u t y /
            (1 + intervalDomainLift (coupledChemicalConcentration p u t) y) ^ (p.β + 1)) x :=
    rfl
  rw [hcdt, hderiv.deriv]
  -- The chain-rule already pins `Vx = Vxc`, `Vtx = Vtxc`; the remaining value
  -- factors `U,Ut,V,Vt` are lift-slice values, matched to the reps here.
  unfold mixedAlgebra
  simp only
  rw [W.Uc_eq t ht x hx, W.Utc_eq t ht x hx, W.Vc_eq t ht x hx, W.Vtc_eq t ht x hx]

/-- **The assembled `ChemDivMixedReprData` witness.**  Packages the ten
continuous representatives, the floor, and the derived `agree` field. -/
def witnessData
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {τ δ : ℝ}
    (W : ChemDivMixedReprWitnessData p u τ δ) :
    ChemDivMixedReprData p u τ δ where
  Uc := W.Uc; Utc := W.Utc; Utxc := W.Utxc; Uxc := W.Uxc
  Vc := W.Vc; Vxc := W.Vxc; Vxxc := W.Vxxc
  Vtc := W.Vtc; Vtxc := W.Vtxc; Vtxxc := W.Vtxxc
  cont_Uc := W.cont_Uc; cont_Utc := W.cont_Utc; cont_Utxc := W.cont_Utxc
  cont_Uxc := W.cont_Uxc; cont_Vc := W.cont_Vc; cont_Vxc := W.cont_Vxc
  cont_Vxxc := W.cont_Vxxc; cont_Vtc := W.cont_Vtc; cont_Vtxc := W.cont_Vtxc
  cont_Vtxxc := W.cont_Vtxxc
  floor := W.floor
  agree := fun t ht x hx => witness_agree W t ht x hx

/-- **`htime_cont` discharged from the witness bundle.**  Feeding the assembled
`ChemDivMixedReprData` to `chemDivMixedTimeDerivClosedRepr_of_data` produces the
closed-slab spectral representative `ChemDivMixedTimeDerivClosedRepr`, which is
exactly the `htime_cont` input of the `χ₀<0` FAC chain. -/
theorem chemDivMixedTimeDerivClosedRepr_of_witness
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {τ δ : ℝ}
    (W : ChemDivMixedReprWitnessData p u τ δ) :
    ShenWork.IntervalCoupledRegularityBootstrap.ChemDivMixedTimeDerivClosedRepr
      p u τ δ :=
  chemDivMixedTimeDerivClosedRepr_of_data (witnessData W)

/-! ## v-side series grounding (from `PhysicalResolverJointC2Data`).

The v-VALUE/GRAD legs of the witness bundle are genuinely grounded in the
committed bounded-weight resolver series: the value rep `Vc` and gradient rep
`Vxc` are globally `ContDiff ℝ 2` (hence continuous), and the closed-slab
`HasDerivAt` of `lift v` is the termwise sin-series gradient, valid on the *closed*
`[0,1]` (the sin-series is differentiable everywhere, including the endpoints).
This shows the v-side legs are not free hypotheses — they are produced from the
honest `PhysicalResolverJointC2Data`.  (The `∂ₜv`/u-side time-derivative legs need
the analogous `∂ₜ`-coefficient series, which is the isolated minimal honest
interface; see the report.) -/

/-- Per-time eigenvalue-weighted summability of the resolver value coefficients,
extracted from the order-2 value joint majorant (cf.
`coupledChemical_grad_jointContDiffAt_two`). -/
theorem resolver_eigSummable
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt) (t : ℝ) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k * |resolverTimeCoeff p u k t|) := by
  have heignn : ∀ k : ℕ, 0 ≤ unitIntervalCosineEigenvalue k := fun k => by
    show (0 : ℝ) ≤ ((k : ℝ) * Real.pi) ^ 2; positivity
  set b : ℕ → ℝ := fun k => resolverTimeCoeff p u k t with hb
  have hbnn : ∀ i k : ℕ, i ≤ 2 → 0 ≤ Bt i k := fun i k hi =>
    le_trans (norm_nonneg _) (H.coeff_bound i k t hi)
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (heignn k) (abs_nonneg _)) (fun k => ?_)
    (H.value_summable 2 le_rfl)
  have hbk : |b k| ≤ Bt 0 k := by
    have h0 := H.coeff_bound 0 k t (by norm_num)
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h0
  have hi0le : unitIntervalCosineEigenvalue k * |b k| ≤
      Bt 0 k * unitIntervalCosineEigenvalue k := by
    rw [mul_comm (Bt 0 k)]; exact mul_le_mul_of_nonneg_left hbk (heignn k)
  refine hi0le.trans ?_
  rw [boundedWeightJointMajorant, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  have hi0 : (Nat.choose 2 0 : ℝ) * Bt 0 k * valueCosWeight (2 - 0) k =
      Bt 0 k * unitIntervalCosineEigenvalue k := by
    norm_num [valueCosWeight]
  have hnn1 : (0 : ℝ) ≤ (Nat.choose 2 1 : ℝ) * Bt 1 k * valueCosWeight (2 - 1) k :=
    mul_nonneg (mul_nonneg (by positivity) (hbnn 1 k (by norm_num)))
      (ShenWork.IntervalResolverSpectralJointC2Concrete.valueCosWeight_nonneg _ _)
  have hnn2 : (0 : ℝ) ≤ (Nat.choose 2 2 : ℝ) * Bt 2 k * valueCosWeight (2 - 2) k :=
    mul_nonneg (mul_nonneg (by positivity) (hbnn 2 k (by norm_num)))
      (ShenWork.IntervalResolverSpectralJointC2Concrete.valueCosWeight_nonneg _ _)
  rw [hi0]; linarith

/-- **v-side `∂ₓv` interior `HasDerivAt` leg.**  On the *open* `Ioo 0 1` the lifted
concentration `lift v` has `x`-derivative the termwise sin-series gradient.  (On
the interior the lift agrees with the cosine series on a whole neighbourhood, so
the genuine derivative transfers; at the endpoints the lift is non-differentiable
by the junk-value convention and its `deriv` is the Neumann zero — handled
separately in the boundary leg of `agree`.)  This grounds the bundle's interior
`hVx` leg in the committed resolver value series. -/
theorem resolver_lift_hasDerivAt_grad
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt) (t x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y => intervalDomainLift (coupledChemicalConcentration p u t) y)
      (∑' k : ℕ, resolverTimeCoeff p u k t *
        (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x))) x := by
  have heig := resolver_eigSummable H t
  have hgrad := cosineCoeffSeries_grad_hasDerivAt heig x
  refine hgrad.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  have he := coupledChemical_lift_eq_series (p := p) (u := u) (t := t) (x := y)
    (Ioo_subset_Icc_self hy)
  simpa [boundedWeightJointTerm] using he


/-! ## `d_t`-series interface: the time-derivative cosine series.

The `d_t`-series legs of `ChemDivMixedReprWitnessData` (`Vtc,Vtxc,Vtxxc` on the
resolver side, `Utc,Utxc` on the u-side) are the GLOBALLY-continuous closed-slab
representatives of the time-derivatives `∂ₜv, ∂ₓ∂ₜv, ∂ₓ²∂ₜv` and `∂ₜU=slopeSlice,
∂ₓ∂ₜU`.  They are built by the SAME bounded-weight mechanism as the value legs,
applied to the `d_t`-coefficient family `d_t c_k`: from the committed
`ContDiff ℝ 2`-in-`t` coefficient data (resolver `PhysicalResolverJointC2Data`,
iterate `IteratePicardJointC2Data`), the `d_t`-coefficients are `ContDiff 1` in
`t` with bound `Bt 1 k`, and the bounded-weight series `∑ (d_t c_k) cos(kπx)` is
the `d_t`-series — its global continuity and termwise `x`-gradient come from the
`Bt 1`-summability extracted from the committed value/grad majorants.  NO
eigen-cube ladder, NO resolver `C²` field, NO `d_t`-series taken as hypothesis. -/

/-- **Termwise time differentiation of a cosine series.**  If each coefficient
`c k` is `ContDiff ℝ 1` in `t` with `‖deriv (c k) r‖ ≤ Bt1 k` for a summable
`Bt1`, and the value series is summable at `r`, then differentiating the cosine
series in `t` (at fixed `x`) goes termwise: the `d_t`-series `∑ (deriv c_k) cos`. -/
theorem cosineSeries_timeDeriv_hasDerivAt
    {c : ℕ → ℝ → ℝ} {Bt1 : ℕ → ℝ} (x : ℝ)
    (hc : ∀ k, Differentiable ℝ (c k))
    (hb : ∀ k r, ‖deriv (c k) r‖ ≤ Bt1 k)
    (hsum : Summable Bt1)
    {r : ℝ} (hval : Summable (fun k => c k r * cosineMode k x)) :
    HasDerivAt (fun s => ∑' k : ℕ, c k s * cosineMode k x)
      (∑' k : ℕ, deriv (c k) r * cosineMode k x) r := by
  refine hasDerivAt_tsum (𝕜 := ℝ) (F := ℝ) (u := Bt1)
    (g := fun k s => c k s * cosineMode k x)
    (g' := fun k s => deriv (c k) s * cosineMode k x)
    hsum
    (fun k s => (((hc k) s).hasDerivAt).mul_const (cosineMode k x))
    (fun k s => ?_) hval r
  rw [Real.norm_eq_abs, abs_mul]
  have hcos : |cosineMode k x| ≤ 1 := by unfold cosineMode; exact Real.abs_cos_le_one _
  calc |deriv (c k) s| * |cosineMode k x| ≤ |deriv (c k) s| * 1 :=
        mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
    _ = |deriv (c k) s| := mul_one _
    _ = ‖deriv (c k) s‖ := (Real.norm_eq_abs _).symm
    _ ≤ Bt1 k := hb k s

/-- The `iteratedFDeriv 1` bound transfers to a `deriv` bound. -/
theorem deriv_norm_le_of_iteratedFDeriv {f : ℝ → ℝ} {t M : ℝ}
    (h : ‖iteratedFDeriv ℝ 1 f t‖ ≤ M) : ‖deriv f t‖ ≤ M := by
  rw [norm_iteratedFDeriv_one] at h
  refine le_trans ?_ h
  rw [deriv]
  calc ‖fderiv ℝ f t 1‖
      ≤ ‖fderiv ℝ f t‖ * ‖(1 : ℝ)‖ := (fderiv ℝ f t).le_opNorm 1
    _ = ‖fderiv ℝ f t‖ := by simp

/-! ### Summability extraction from the bounded-weight majorants. -/

/-- `Bt 1 k ≤ boundedWeightJointMajorant Bt 1 k`, so the order-1 time-bound is
summable from the committed order-1 value majorant summability. -/
theorem Bt1_summable_of_value
    {Bt : ℕ → ℕ → ℝ}
    (hnn0 : ∀ k, 0 ≤ Bt 0 k) (hnn1 : ∀ k, 0 ≤ Bt 1 k)
    (hv : Summable (boundedWeightJointMajorant Bt 1)) :
    Summable (Bt 1) := by
  refine Summable.of_nonneg_of_le (fun k => hnn1 k) (fun k => ?_) hv
  rw [boundedWeightJointMajorant, Finset.sum_range_succ, Finset.sum_range_one]
  have h0 : (0 : ℝ) ≤ (Nat.choose 1 0 : ℝ) * Bt 0 k * valueCosWeight (1 - 0) k :=
    mul_nonneg (mul_nonneg (by positivity) (hnn0 k))
      (ShenWork.IntervalResolverSpectralJointC2Concrete.valueCosWeight_nonneg _ _)
  have h1 : (Nat.choose 1 1 : ℝ) * Bt 1 k * valueCosWeight (1 - 1) k = Bt 1 k := by
    norm_num [valueCosWeight]
  linarith [h1]

/-- `λ_k · Bt 1 k ≤ boundedWeightJointGradMajorant Bt 2 k`, so the eigenvalue-
weighted order-1 time-bound is summable from the committed order-2 gradient
majorant summability. -/
theorem eigBt1_summable_of_grad
    {Bt : ℕ → ℕ → ℝ}
    (hnn0 : ∀ k, 0 ≤ Bt 0 k) (hnn1 : ∀ k, 0 ≤ Bt 1 k) (hnn2 : ∀ k, 0 ≤ Bt 2 k)
    (hg : Summable (boundedWeightJointGradMajorant Bt 2)) :
    Summable (fun k => unitIntervalCosineEigenvalue k * Bt 1 k) := by
  have heignn : ∀ k : ℕ, 0 ≤ unitIntervalCosineEigenvalue k := fun k => by
    show (0 : ℝ) ≤ ((k : ℝ) * Real.pi) ^ 2; positivity
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (heignn k) (hnn1 k)) (fun k => ?_) hg
  rw [boundedWeightJointGradMajorant, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  have hgw1 : gradCosWeight 1 k = unitIntervalCosineEigenvalue k := rfl
  have h1 : (Nat.choose 2 1 : ℝ) * Bt 1 k * gradCosWeight (2 - 1) k =
      2 * (unitIntervalCosineEigenvalue k * Bt 1 k) := by
    rw [show (2 - 1 : ℕ) = 1 from rfl, hgw1]; norm_num; ring
  have h0 : (0 : ℝ) ≤ (Nat.choose 2 0 : ℝ) * Bt 0 k * gradCosWeight (2 - 0) k :=
    mul_nonneg (mul_nonneg (by positivity) (hnn0 k))
      (ShenWork.IntervalResolverSpectralJointC2Concrete.gradCosWeight_nonneg _ _)
  have h2 : (0 : ℝ) ≤ (Nat.choose 2 2 : ℝ) * Bt 2 k * gradCosWeight (2 - 2) k :=
    mul_nonneg (mul_nonneg (by positivity) (hnn2 k))
      (ShenWork.IntervalResolverSpectralJointC2Concrete.gradCosWeight_nonneg _ _)
  have hself : unitIntervalCosineEigenvalue k * Bt 1 k ≤
      2 * (unitIntervalCosineEigenvalue k * Bt 1 k) := by
    nlinarith [mul_nonneg (heignn k) (hnn1 k)]
  linarith [h1, hself]

/-- `|kπ| · Bt 1 k ≤ boundedWeightJointGradMajorant Bt 1 k`. -/
theorem gradBt1_summable_of_grad
    {Bt : ℕ → ℕ → ℝ}
    (hnn0 : ∀ k, 0 ≤ Bt 0 k) (hnn1 : ∀ k, 0 ≤ Bt 1 k)
    (hg : Summable (boundedWeightJointGradMajorant Bt 1)) :
    Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Bt 1 k) := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (abs_nonneg _) (hnn1 k)) (fun k => ?_) hg
  rw [boundedWeightJointGradMajorant, Finset.sum_range_succ, Finset.sum_range_one]
  have hgw0 : gradCosWeight 0 k = |(k : ℝ) * Real.pi| := rfl
  have h1 : (Nat.choose 1 1 : ℝ) * Bt 1 k * gradCosWeight (1 - 1) k =
      |(k : ℝ) * Real.pi| * Bt 1 k := by
    rw [show (1 - 1 : ℕ) = 0 from rfl, hgw0]; norm_num; ring
  have h0 : (0 : ℝ) ≤ (Nat.choose 1 0 : ℝ) * Bt 0 k * gradCosWeight (1 - 0) k :=
    mul_nonneg (mul_nonneg (by positivity) (hnn0 k))
      (ShenWork.IntervalResolverSpectralJointC2Concrete.gradCosWeight_nonneg _ _)
  linarith [h1]

/-! ### Resolver `d_t`-series legs (from `PhysicalResolverJointC2Data`). -/

variable {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}

/-- Nonnegativity of the resolver order bounds. -/
private theorem resolver_Bt_nonneg (H : PhysicalResolverJointC2Data p u Bt)
    (i k : ℕ) (hi : i ≤ 2) : 0 ≤ Bt i k :=
  le_trans (norm_nonneg _) (H.coeff_bound i k 0 hi)

/-- `‖deriv (resolverTimeCoeff p u k) t‖ ≤ Bt 1 k`. -/
private theorem resolver_coeff_deriv_bound (H : PhysicalResolverJointC2Data p u Bt)
    (k : ℕ) (t : ℝ) : ‖deriv (resolverTimeCoeff p u k) t‖ ≤ Bt 1 k :=
  deriv_norm_le_of_iteratedFDeriv (H.coeff_bound 1 k t (by norm_num))

/-- Each resolver coefficient is differentiable. -/
private theorem resolver_coeff_diff (H : PhysicalResolverJointC2Data p u Bt) (k : ℕ) :
    Differentiable ℝ (resolverTimeCoeff p u k) :=
  (H.coeff_contDiff k).differentiable (by norm_num)

/-- `∑ Bt 1 k` summable (resolver). -/
private theorem resolver_Bt1_summable (H : PhysicalResolverJointC2Data p u Bt) :
    Summable (Bt 1) :=
  Bt1_summable_of_value (fun k => resolver_Bt_nonneg H 0 k (by norm_num))
    (fun k => resolver_Bt_nonneg H 1 k (by norm_num))
    (H.value_summable 1 (by norm_num))

/-- The committed `coupledChemicalTimeDerivativeLift` equals the resolver
`d_t`-coefficient cosine series on the closed slab.  Time differentiation of the
value series `lift v = ∑ rtc_k cos` goes termwise. -/
theorem resolver_timeDeriv_eq_series
    (H : PhysicalResolverJointC2Data p u Bt) (t x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    coupledChemicalTimeDerivativeLift p u t x =
      ∑' k : ℕ, deriv (resolverTimeCoeff p u k) t * cosineMode k x := by
  have hfun : (fun r => intervalDomainLift (coupledChemicalConcentration p u r) x)
      = fun r => ∑' k : ℕ, resolverTimeCoeff p u k r * cosineMode k x := by
    funext r
    have he := coupledChemical_lift_eq_series (p := p) (u := u) (t := r) (x := x) hx
    simpa [boundedWeightJointTerm] using he
  unfold coupledChemicalTimeDerivativeLift
  rw [hfun]
  have hBt0 : Summable (Bt 0) :=
    (H.value_summable 0 (by norm_num)).congr (fun k => by
      simp [boundedWeightJointMajorant, valueCosWeight])
  have hval : Summable (fun k => resolverTimeCoeff p u k t * cosineMode k x) := by
    refine Summable.of_norm_bounded hBt0 (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have hcos : |cosineMode k x| ≤ 1 := by unfold cosineMode; exact Real.abs_cos_le_one _
    have h0 := resolver_coeff_deriv_bound H k t
    have hb0 : |resolverTimeCoeff p u k t| ≤ Bt 0 k := by
      have := H.coeff_bound 0 k t (by norm_num)
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    calc |resolverTimeCoeff p u k t| * |cosineMode k x|
        ≤ |resolverTimeCoeff p u k t| * 1 := mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
      _ = |resolverTimeCoeff p u k t| := mul_one _
      _ ≤ Bt 0 k := hb0
  exact (cosineSeries_timeDeriv_hasDerivAt x (resolver_coeff_diff H)
    (resolver_coeff_deriv_bound H) (resolver_Bt1_summable H) hval).deriv


/-! ### Resolver `d_t`-series representatives (continuity + interior `HasDerivAt`). -/

/-- The resolver `d_t`-value rep: `∂ₜv` as the `d_t`-coefficient cosine series. -/
def resolverDtValue (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) :
    ℝ × ℝ → ℝ :=
  fun q => ∑' k : ℕ, deriv (resolverTimeCoeff p u k) q.1 * cosineMode k q.2

/-- The resolver `d_t`-gradient rep: `∂ₓ∂ₜv`. -/
def resolverDtGrad (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) :
    ℝ × ℝ → ℝ :=
  fun q => ∑' k : ℕ, deriv (resolverTimeCoeff p u k) q.1 *
    (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * q.2))

/-- The resolver `d_t`-second-gradient rep: `∂ₓ²∂ₜv`. -/
def resolverDtGrad2 (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) :
    ℝ × ℝ → ℝ :=
  fun q => ∑' k : ℕ, deriv (resolverTimeCoeff p u k) q.1 *
    (-(((k : ℝ) * Real.pi) ^ 2) * Real.cos ((k : ℝ) * Real.pi * q.2))

/-- Continuity of the resolver `d_t`-coefficient `deriv (resolverTimeCoeff)`. -/
private theorem resolver_coeff_deriv_cont (H : PhysicalResolverJointC2Data p u Bt)
    (k : ℕ) : Continuous (deriv (resolverTimeCoeff p u k)) :=
  (H.coeff_contDiff k).continuous_deriv (by norm_num)

/-- Per-time eigenvalue-weighted summability of the resolver `d_t`-coefficients. -/
theorem resolver_dt_eigSummable (H : PhysicalResolverJointC2Data p u Bt) (t : ℝ) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k * |deriv (resolverTimeCoeff p u k) t|) := by
  have hsum := eigBt1_summable_of_grad
    (fun k => resolver_Bt_nonneg H 0 k (by norm_num))
    (fun k => resolver_Bt_nonneg H 1 k (by norm_num))
    (fun k => resolver_Bt_nonneg H 2 k (by norm_num)) (H.grad_summable 2 (by norm_num))
  have heignn0 : ∀ k : ℕ, (0 : ℝ) ≤ unitIntervalCosineEigenvalue k := fun k => by
    show (0 : ℝ) ≤ ((k : ℝ) * Real.pi) ^ 2; positivity
  refine hsum.of_nonneg_of_le (fun k => mul_nonneg (heignn0 k) (abs_nonneg _)) (fun k => ?_)
  have heignn : (0 : ℝ) ≤ unitIntervalCosineEigenvalue k := heignn0 k
  have hb : |deriv (resolverTimeCoeff p u k) t| ≤ Bt 1 k :=
    (Real.norm_eq_abs _ ▸ resolver_coeff_deriv_bound H k t)
  exact mul_le_mul_of_nonneg_left hb heignn

/-- Continuity of the resolver `d_t`-value rep, via `continuous_tsum` with the
order-1 majorant `Bt 1`. -/
theorem resolverDtValue_continuous (H : PhysicalResolverJointC2Data p u Bt) :
    Continuous (resolverDtValue p u) := by
  refine continuous_tsum (fun k => ?_) (resolver_Bt1_summable H) (fun k q => ?_)
  · have h1 : Continuous (fun q : ℝ × ℝ => deriv (resolverTimeCoeff p u k) q.1) :=
      (resolver_coeff_deriv_cont H k).comp continuous_fst
    have h2 : Continuous (fun q : ℝ × ℝ => cosineMode k q.2) :=
      (by unfold cosineMode; fun_prop : Continuous (cosineMode k)).comp continuous_snd
    exact h1.mul h2
  · rw [Real.norm_eq_abs, abs_mul]
    have hcos : |cosineMode k q.2| ≤ 1 := by
      unfold cosineMode; exact Real.abs_cos_le_one _
    calc |deriv (resolverTimeCoeff p u k) q.1| * |cosineMode k q.2|
        ≤ |deriv (resolverTimeCoeff p u k) q.1| * 1 :=
          mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
      _ = ‖deriv (resolverTimeCoeff p u k) q.1‖ := by rw [mul_one, Real.norm_eq_abs]
      _ ≤ Bt 1 k := resolver_coeff_deriv_bound H k q.1

/-- Continuity of the resolver `d_t`-gradient rep, via `continuous_tsum` with the
order-1 gradient majorant `|kπ|·Bt 1 k`. -/
theorem resolverDtGrad_continuous (H : PhysicalResolverJointC2Data p u Bt) :
    Continuous (resolverDtGrad p u) := by
  have hmaj : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Bt 1 k) :=
    gradBt1_summable_of_grad (fun k => resolver_Bt_nonneg H 0 k (by norm_num))
      (fun k => resolver_Bt_nonneg H 1 k (by norm_num)) (H.grad_summable 1 (by norm_num))
  refine continuous_tsum (fun k => ?_) hmaj (fun k q => ?_)
  · have h1 : Continuous (fun q : ℝ × ℝ => deriv (resolverTimeCoeff p u k) q.1) :=
      (resolver_coeff_deriv_cont H k).comp continuous_fst
    have h2 : Continuous (fun q : ℝ × ℝ =>
        -((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * q.2)) :=
      (by fun_prop : Continuous (fun y : ℝ =>
        -((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * y))).comp continuous_snd
    exact h1.mul h2
  · rw [Real.norm_eq_abs, abs_mul, mul_comm]
    have hdb : |deriv (resolverTimeCoeff p u k) q.1| ≤ Bt 1 k := by
      rw [← Real.norm_eq_abs]; exact resolver_coeff_deriv_bound H k q.1
    have hcb : |(-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * q.2))|
        ≤ |(k : ℝ) * Real.pi| := by
      rw [abs_mul, abs_neg]
      calc |(k : ℝ) * Real.pi| * |Real.sin ((k : ℝ) * Real.pi * q.2)|
          ≤ |(k : ℝ) * Real.pi| * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
        _ = |(k : ℝ) * Real.pi| := mul_one _
    exact mul_le_mul hcb hdb (abs_nonneg _) (abs_nonneg _)

/-- Continuity of the resolver `d_t`-second-gradient rep, via `continuous_tsum`
with the order-2 eigenvalue majorant `λ_k·Bt 1 k`. -/
theorem resolverDtGrad2_continuous (H : PhysicalResolverJointC2Data p u Bt) :
    Continuous (resolverDtGrad2 p u) := by
  have hmaj : Summable (fun k => unitIntervalCosineEigenvalue k * Bt 1 k) :=
    eigBt1_summable_of_grad (fun k => resolver_Bt_nonneg H 0 k (by norm_num))
      (fun k => resolver_Bt_nonneg H 1 k (by norm_num))
      (fun k => resolver_Bt_nonneg H 2 k (by norm_num)) (H.grad_summable 2 (by norm_num))
  refine continuous_tsum (fun k => ?_) hmaj (fun k q => ?_)
  · have h1 : Continuous (fun q : ℝ × ℝ => deriv (resolverTimeCoeff p u k) q.1) :=
      (resolver_coeff_deriv_cont H k).comp continuous_fst
    have h2 : Continuous (fun q : ℝ × ℝ =>
        -(((k : ℝ) * Real.pi) ^ 2) * Real.cos ((k : ℝ) * Real.pi * q.2)) :=
      (by fun_prop : Continuous (fun y : ℝ =>
        -(((k : ℝ) * Real.pi) ^ 2) * Real.cos ((k : ℝ) * Real.pi * y))).comp continuous_snd
    exact h1.mul h2
  · have hlam : unitIntervalCosineEigenvalue k = ((k : ℝ) * Real.pi) ^ 2 := by
      unfold unitIntervalCosineEigenvalue; ring
    rw [Real.norm_eq_abs, abs_mul, mul_comm, hlam]
    have hdb : |deriv (resolverTimeCoeff p u k) q.1| ≤ Bt 1 k := by
      rw [← Real.norm_eq_abs]; exact resolver_coeff_deriv_bound H k q.1
    have hcb : |(-(((k : ℝ) * Real.pi) ^ 2) * Real.cos ((k : ℝ) * Real.pi * q.2))|
        ≤ ((k : ℝ) * Real.pi) ^ 2 := by
      rw [abs_mul, abs_neg]
      calc |((k : ℝ) * Real.pi) ^ 2| * |Real.cos ((k : ℝ) * Real.pi * q.2)|
          ≤ |((k : ℝ) * Real.pi) ^ 2| * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
        _ = ((k : ℝ) * Real.pi) ^ 2 := by rw [mul_one, abs_of_nonneg (by positivity)]
    exact mul_le_mul hcb hdb (abs_nonneg _) (by positivity)

/-- Interior `HasDerivAt` of `∂ₜv` in `x`: on `Ioo 0 1` the committed
`coupledChemicalTimeDerivativeLift` has `x`-derivative `resolverDtGrad p u (t,x)`. -/
theorem resolver_dt_lift_hasDerivAt_grad (H : PhysicalResolverJointC2Data p u Bt)
    (t x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y => coupledChemicalTimeDerivativeLift p u t y)
      (resolverDtGrad p u (t, x)) x := by
  have heig := resolver_dt_eigSummable H t
  have hgrad := cosineCoeffSeries_grad_hasDerivAt heig x
  refine hgrad.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact (resolver_timeDeriv_eq_series H t y (Ioo_subset_Icc_self hy))

/-- Interior `HasDerivAt` of `∂ₓ∂ₜv` in `x`: on `Ioo 0 1` the field
`deriv (∂ₜv)` has `x`-derivative `resolverDtGrad2 p u (t,x)`. -/
theorem resolver_dt_lift_hasDerivAt_grad2 (H : PhysicalResolverJointC2Data p u Bt)
    (t x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y => deriv (coupledChemicalTimeDerivativeLift p u t) y)
      (resolverDtGrad2 p u (t, x)) x := by
  have heig := resolver_dt_eigSummable H t
  have hgrad2 := cosineCoeffSeries_grad2_hasDerivAt heig x
  refine hgrad2.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact (resolver_dt_lift_hasDerivAt_grad H t y hy).deriv


/-! ### u-side `d_t`-series legs (from `IteratePicardJointC2Data` + iterate
gradient summability).

`slopeSlice u t x = ∂ₜ(lift u)` is built by the SAME mechanism as the resolver
`∂ₜv`, applied to the iterate's own `d_t`-coefficient family `deriv (c k)`.  The
iterate value summability gives global continuity of the `d_t`-value rep; the
iterate gradient summability `Hg : Summable (boundedWeightJointGradMajorant Bt 2)`
— the honest companion of the resolver's committed `grad_summable`, i.e. the
iterate's spatial gradient `ℓ¹` datum — grounds the `d_t`-gradient rep and the
interior `HasDerivAt` of `slopeSlice`. -/

open ShenWork.IntervalIteratePicardJointC2 (IteratePicardJointC2Data)

variable {c : ℕ → ℝ → ℝ}

/-- Iterate order bounds are nonnegative. -/
private theorem iterate_Bt_nonneg (H : IteratePicardJointC2Data u c Bt)
    (i k : ℕ) (hi : i ≤ 2) : 0 ≤ Bt i k :=
  le_trans (norm_nonneg _) (H.coeff_bound i k 0 hi)

/-- `‖deriv (c k) t‖ ≤ Bt 1 k` (iterate). -/
private theorem iterate_coeff_deriv_bound (H : IteratePicardJointC2Data u c Bt)
    (k : ℕ) (t : ℝ) : ‖deriv (c k) t‖ ≤ Bt 1 k :=
  deriv_norm_le_of_iteratedFDeriv (H.coeff_bound 1 k t (by norm_num))

/-- Each iterate coefficient is differentiable. -/
private theorem iterate_coeff_diff (H : IteratePicardJointC2Data u c Bt) (k : ℕ) :
    Differentiable ℝ (c k) := (H.coeff_contDiff k).differentiable (by norm_num)

/-- Continuity of the iterate `d_t`-coefficient. -/
private theorem iterate_coeff_deriv_cont (H : IteratePicardJointC2Data u c Bt)
    (k : ℕ) : Continuous (deriv (c k)) :=
  (H.coeff_contDiff k).continuous_deriv (by norm_num)

/-- `∑ Bt 1 k` summable (iterate, from value majorant order 1). -/
private theorem iterate_Bt1_summable (H : IteratePicardJointC2Data u c Bt) :
    Summable (Bt 1) :=
  Bt1_summable_of_value (fun k => iterate_Bt_nonneg H 0 k (by norm_num))
    (fun k => iterate_Bt_nonneg H 1 k (by norm_num)) (H.value_summable 1 (by norm_num))

/-- The committed `slopeSlice` equals the iterate `d_t`-coefficient cosine series
on the closed slab.  Time differentiation of `lift u = ∑ c_k cos` goes termwise. -/
theorem iterate_slopeSlice_eq_series (H : IteratePicardJointC2Data u c Bt)
    (t x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    ShenWork.Paper2.PicardLimitK1.slopeSlice u t x =
      ∑' k : ℕ, deriv (c k) t * cosineMode k x := by
  have hfun : (fun r => intervalDomainLift (u r) x)
      = fun r => ∑' k : ℕ, c k r * cosineMode k x := by
    funext r; exact H.lift_eq_series (t := r) (x := x) hx
  unfold ShenWork.Paper2.PicardLimitK1.slopeSlice
  rw [hfun]
  have hBt0 : Summable (Bt 0) :=
    (H.value_summable 0 (by norm_num)).congr (fun k => by
      simp [boundedWeightJointMajorant, valueCosWeight])
  have hval : Summable (fun k => c k t * cosineMode k x) := by
    refine Summable.of_norm_bounded hBt0 (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have hcos : |cosineMode k x| ≤ 1 := by unfold cosineMode; exact Real.abs_cos_le_one _
    have hb0 : |c k t| ≤ Bt 0 k := by
      have := H.coeff_bound 0 k t (by norm_num)
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    calc |c k t| * |cosineMode k x| ≤ |c k t| * 1 :=
          mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
      _ = |c k t| := mul_one _
      _ ≤ Bt 0 k := hb0
  exact (cosineSeries_timeDeriv_hasDerivAt x (iterate_coeff_diff H)
    (iterate_coeff_deriv_bound H) (iterate_Bt1_summable H) hval).deriv

/-- The u-side `d_t`-value rep (slopeSlice as a `d_t`-coefficient cosine series). -/
def iterateDtValue (c : ℕ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun q => ∑' k : ℕ, deriv (c k) q.1 * cosineMode k q.2

/-- The u-side `d_t`-gradient rep (`∂ₓ slopeSlice`). -/
def iterateDtGrad (c : ℕ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun q => ∑' k : ℕ, deriv (c k) q.1 *
    (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * q.2))

/-- Per-time eigenvalue-weighted summability of the iterate `d_t`-coefficients,
from the iterate gradient majorant `Hg`. -/
theorem iterate_dt_eigSummable (H : IteratePicardJointC2Data u c Bt)
    (Hg : Summable (boundedWeightJointGradMajorant Bt 2)) (t : ℝ) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k * |deriv (c k) t|) := by
  have hsum := eigBt1_summable_of_grad
    (fun k => iterate_Bt_nonneg H 0 k (by norm_num))
    (fun k => iterate_Bt_nonneg H 1 k (by norm_num))
    (fun k => iterate_Bt_nonneg H 2 k (by norm_num)) Hg
  have heignn0 : ∀ k : ℕ, (0 : ℝ) ≤ unitIntervalCosineEigenvalue k := fun k => by
    show (0 : ℝ) ≤ ((k : ℝ) * Real.pi) ^ 2; positivity
  refine hsum.of_nonneg_of_le (fun k => mul_nonneg (heignn0 k) (abs_nonneg _)) (fun k => ?_)
  have hb : |deriv (c k) t| ≤ Bt 1 k := Real.norm_eq_abs _ ▸ iterate_coeff_deriv_bound H k t
  exact mul_le_mul_of_nonneg_left hb (heignn0 k)

/-- Continuity of the u-side `d_t`-value rep. -/
theorem iterateDtValue_continuous (H : IteratePicardJointC2Data u c Bt) :
    Continuous (iterateDtValue c) := by
  refine continuous_tsum (fun k => ?_) (iterate_Bt1_summable H) (fun k q => ?_)
  · have h1 : Continuous (fun q : ℝ × ℝ => deriv (c k) q.1) :=
      (iterate_coeff_deriv_cont H k).comp continuous_fst
    have h2 : Continuous (fun q : ℝ × ℝ => cosineMode k q.2) :=
      (by unfold cosineMode; fun_prop : Continuous (cosineMode k)).comp continuous_snd
    exact h1.mul h2
  · rw [Real.norm_eq_abs, abs_mul]
    have hcos : |cosineMode k q.2| ≤ 1 := by unfold cosineMode; exact Real.abs_cos_le_one _
    calc |deriv (c k) q.1| * |cosineMode k q.2| ≤ |deriv (c k) q.1| * 1 :=
          mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
      _ = ‖deriv (c k) q.1‖ := by rw [mul_one, Real.norm_eq_abs]
      _ ≤ Bt 1 k := iterate_coeff_deriv_bound H k q.1

/-- Continuity of the u-side `d_t`-gradient rep, from the `|kπ|·Bt 1`
summability (itself extracted from the iterate order-2 gradient majorant). -/
theorem iterateDtGrad_continuous (H : IteratePicardJointC2Data u c Bt)
    (hmaj : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Bt 1 k)) :
    Continuous (iterateDtGrad c) := by
  refine continuous_tsum (fun k => ?_) hmaj (fun k q => ?_)
  · have h1 : Continuous (fun q : ℝ × ℝ => deriv (c k) q.1) :=
      (iterate_coeff_deriv_cont H k).comp continuous_fst
    have h2 : Continuous (fun q : ℝ × ℝ =>
        -((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * q.2)) :=
      (by fun_prop : Continuous (fun y : ℝ =>
        -((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * y))).comp continuous_snd
    exact h1.mul h2
  · rw [Real.norm_eq_abs, abs_mul, mul_comm]
    have hdb : |deriv (c k) q.1| ≤ Bt 1 k := by
      rw [← Real.norm_eq_abs]; exact iterate_coeff_deriv_bound H k q.1
    have hcb : |(-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * q.2))|
        ≤ |(k : ℝ) * Real.pi| := by
      rw [abs_mul, abs_neg]
      calc |(k : ℝ) * Real.pi| * |Real.sin ((k : ℝ) * Real.pi * q.2)|
          ≤ |(k : ℝ) * Real.pi| * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
        _ = |(k : ℝ) * Real.pi| := mul_one _
    exact mul_le_mul hcb hdb (abs_nonneg _) (abs_nonneg _)

/-- Interior `HasDerivAt` of `slopeSlice` in `x`: on `Ioo 0 1`, `slopeSlice u t`
has `x`-derivative `iterateDtGrad c (t,x)`. -/
theorem iterate_slopeSlice_hasDerivAt_grad (H : IteratePicardJointC2Data u c Bt)
    (Hg : Summable (boundedWeightJointGradMajorant Bt 2)) (t x : ℝ)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y => ShenWork.Paper2.PicardLimitK1.slopeSlice u t y)
      (iterateDtGrad c (t, x)) x := by
  have heig := iterate_dt_eigSummable H Hg t
  have hgrad := cosineCoeffSeries_grad_hasDerivAt heig x
  refine hgrad.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact (iterate_slopeSlice_eq_series H t y (Ioo_subset_Icc_self hy))


/-! ### Value-side series representatives (globally-continuous closed-slab reps of
`lift v, ∂ₓv, ∂ₓ²v` and `lift u, ∂ₓu`), via the same bounded-weight mechanism
applied to the VALUE coefficient family `c k t` (resolver `resolverTimeCoeff`,
iterate `c`).  These ground the bundle's value/grad legs `Vc,Vxc,Vxxc,Uc,Uxc`. -/

/-- Generic globally-continuous value cosine-series rep. -/
def valueSeriesRep (c : ℕ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun q => ∑' k : ℕ, c k q.1 * cosineMode k q.2

/-- Generic globally-continuous gradient cosine-series rep. -/
def gradSeriesRep (c : ℕ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun q => ∑' k : ℕ, c k q.1 *
    (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * q.2))

/-- Generic globally-continuous second-gradient cosine-series rep. -/
def grad2SeriesRep (c : ℕ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun q => ∑' k : ℕ, c k q.1 *
    (-(((k : ℝ) * Real.pi) ^ 2) * Real.cos ((k : ℝ) * Real.pi * q.2))

/-- Generic value-rep continuity from a coefficient family that is continuous
in `t` and bounded by a summable envelope `B0`. -/
theorem valueSeriesRep_continuous {c : ℕ → ℝ → ℝ} {B0 : ℕ → ℝ}
    (hcont : ∀ k, Continuous (c k)) (hb : ∀ k t, |c k t| ≤ B0 k)
    (hsum : Summable B0) : Continuous (valueSeriesRep c) := by
  refine continuous_tsum (fun k => ?_) hsum (fun k q => ?_)
  · exact ((hcont k).comp continuous_fst).mul
      ((by unfold cosineMode; fun_prop : Continuous (cosineMode k)).comp continuous_snd)
  · rw [Real.norm_eq_abs, abs_mul]
    have hcos : |cosineMode k q.2| ≤ 1 := by unfold cosineMode; exact Real.abs_cos_le_one _
    calc |c k q.1| * |cosineMode k q.2| ≤ |c k q.1| * 1 :=
          mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
      _ = |c k q.1| := mul_one _
      _ ≤ B0 k := hb k q.1

/-- Generic gradient-rep continuity from a coefficient family bounded by `B0`
with summable `|kπ|·B0`. -/
theorem gradSeriesRep_continuous {c : ℕ → ℝ → ℝ} {B0 : ℕ → ℝ}
    (hcont : ∀ k, Continuous (c k)) (hb : ∀ k t, |c k t| ≤ B0 k)
    (hsum : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * B0 k)) :
    Continuous (gradSeriesRep c) := by
  refine continuous_tsum (fun k => ?_) hsum (fun k q => ?_)
  · refine ((hcont k).comp continuous_fst).mul ?_
    exact (by fun_prop : Continuous (fun y : ℝ =>
      -((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * y))).comp continuous_snd
  · rw [Real.norm_eq_abs, abs_mul, mul_comm]
    have hcb : |(-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * q.2))|
        ≤ |(k : ℝ) * Real.pi| := by
      rw [abs_mul, abs_neg]
      calc |(k : ℝ) * Real.pi| * |Real.sin ((k : ℝ) * Real.pi * q.2)|
          ≤ |(k : ℝ) * Real.pi| * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
        _ = |(k : ℝ) * Real.pi| := mul_one _
    exact mul_le_mul hcb (hb k q.1) (abs_nonneg _) (abs_nonneg _)

/-- Generic second-gradient-rep continuity from `B0` with summable `λ_k·B0`. -/
theorem grad2SeriesRep_continuous {c : ℕ → ℝ → ℝ} {B0 : ℕ → ℝ}
    (hcont : ∀ k, Continuous (c k)) (hb : ∀ k t, |c k t| ≤ B0 k)
    (hsum : Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * B0 k)) :
    Continuous (grad2SeriesRep c) := by
  refine continuous_tsum (fun k => ?_) hsum (fun k q => ?_)
  · refine ((hcont k).comp continuous_fst).mul ?_
    exact (by fun_prop : Continuous (fun y : ℝ =>
      -(((k : ℝ) * Real.pi) ^ 2) * Real.cos ((k : ℝ) * Real.pi * y))).comp continuous_snd
  · have hlam : unitIntervalCosineEigenvalue k = ((k : ℝ) * Real.pi) ^ 2 := by
      unfold unitIntervalCosineEigenvalue; ring
    rw [Real.norm_eq_abs, abs_mul, mul_comm, hlam]
    have hcb : |(-(((k : ℝ) * Real.pi) ^ 2) * Real.cos ((k : ℝ) * Real.pi * q.2))|
        ≤ ((k : ℝ) * Real.pi) ^ 2 := by
      rw [abs_mul, abs_neg]
      calc |((k : ℝ) * Real.pi) ^ 2| * |Real.cos ((k : ℝ) * Real.pi * q.2)|
          ≤ |((k : ℝ) * Real.pi) ^ 2| * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
        _ = ((k : ℝ) * Real.pi) ^ 2 := by rw [mul_one, abs_of_nonneg (by positivity)]
    exact mul_le_mul hcb (hb k q.1) (abs_nonneg _) (by positivity)


/-! ### Value-side summability helpers (from value/grad majorants). -/

/-- `∑ λ_k B0 k` ⟹ `∑ |kπ| B0 k` (since `|kπ| ≤ λ_k = (kπ)²` for the relevant
range and both vanish at `k=0`). -/
theorem gradB0_of_eigB0 {B0 : ℕ → ℝ} (hnn : ∀ k, 0 ≤ B0 k)
    (h : Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * B0 k)) :
    Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * B0 k) := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (hnn k))
    (fun k => ?_) h
  have hpi : |(k : ℝ) * Real.pi| ≤ unitIntervalCosineEigenvalue k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · simp [hk, unitIntervalCosineEigenvalue]
    · have hk1 : (1 : ℝ) ≤ (k : ℝ) * Real.pi := by
        have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        have hpi1 : (1 : ℝ) ≤ Real.pi := le_of_lt (lt_trans (by norm_num) Real.pi_gt_three)
        nlinarith
      rw [abs_of_nonneg (by positivity)]
      show (k : ℝ) * Real.pi ≤ ((k : ℝ) * Real.pi) ^ 2
      nlinarith [hk1]
  exact mul_le_mul_of_nonneg_right hpi (hnn k)

/-- `λ_k · Bt 0 k ≤ boundedWeightJointMajorant Bt 2 k`, so eigenvalue-weighted
order-0 bound is summable from the order-2 value majorant. -/
theorem eigBt0_summable_of_value {Bt : ℕ → ℕ → ℝ}
    (hnn0 : ∀ k, 0 ≤ Bt 0 k) (hnn1 : ∀ k, 0 ≤ Bt 1 k) (hnn2 : ∀ k, 0 ≤ Bt 2 k)
    (hv : Summable (boundedWeightJointMajorant Bt 2)) :
    Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * Bt 0 k) := by
  have heignn : ∀ k : ℕ, 0 ≤ unitIntervalCosineEigenvalue k := fun k => by
    show (0 : ℝ) ≤ ((k : ℝ) * Real.pi) ^ 2; positivity
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (heignn k) (hnn0 k))
    (fun k => ?_) hv
  rw [boundedWeightJointMajorant, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  have hi0 : (Nat.choose 2 0 : ℝ) * Bt 0 k * valueCosWeight (2 - 0) k =
      unitIntervalCosineEigenvalue k * Bt 0 k := by
    simp only [valueCosWeight]; norm_num; ring
  have hnn1' : (0 : ℝ) ≤ (Nat.choose 2 1 : ℝ) * Bt 1 k * valueCosWeight (2 - 1) k :=
    mul_nonneg (mul_nonneg (by positivity) (hnn1 k))
      (ShenWork.IntervalResolverSpectralJointC2Concrete.valueCosWeight_nonneg _ _)
  have hnn2' : (0 : ℝ) ≤ (Nat.choose 2 2 : ℝ) * Bt 2 k * valueCosWeight (2 - 2) k :=
    mul_nonneg (mul_nonneg (by positivity) (hnn2 k))
      (ShenWork.IntervalResolverSpectralJointC2Concrete.valueCosWeight_nonneg _ _)
  rw [hi0]; linarith

/-! ### Generic value-side interior `HasDerivAt` (the value cosine series). -/

/-- Interior `HasDerivAt`: if `f y = valueSeriesRep c (t,y)` near interior `x`,
then `f` has `x`-derivative `gradSeriesRep c (t,x)`. -/
theorem valueRep_hasDerivAt_grad {c : ℕ → ℝ → ℝ} {f : ℝ → ℝ} (t x : ℝ)
    (heig : Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * |c k t|))
    (heq : ∀ᶠ y in 𝓝 x, f y = valueSeriesRep c (t, y)) :
    HasDerivAt f (gradSeriesRep c (t, x)) x :=
  (cosineCoeffSeries_grad_hasDerivAt heig x).congr_of_eventuallyEq heq

/-- Interior `HasDerivAt`: `gradSeriesRep c (t,·)` (= the `∂ₓ` field) has
`x`-derivative `grad2SeriesRep c (t,x)`. -/
theorem gradRep_hasDerivAt_grad2 {c : ℕ → ℝ → ℝ} {g : ℝ → ℝ} (t x : ℝ)
    (heig : Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * |c k t|))
    (heq : ∀ᶠ y in 𝓝 x, g y = gradSeriesRep c (t, y)) :
    HasDerivAt g (grad2SeriesRep c (t, x)) x :=
  (cosineCoeffSeries_grad2_hasDerivAt heig x).congr_of_eventuallyEq heq

/-- Iterate value eigenvalue-summability `∑ λ_k |c_k t|` (from `value_summable 2`). -/
theorem iterate_value_eigSummable (H : IteratePicardJointC2Data u c Bt) (t : ℝ) :
    Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * |c k t|) := by
  refine (eigBt0_summable_of_value (fun k => iterate_Bt_nonneg H 0 k (by norm_num))
    (fun k => iterate_Bt_nonneg H 1 k (by norm_num))
    (fun k => iterate_Bt_nonneg H 2 k (by norm_num))
    (H.value_summable 2 (by norm_num))).of_nonneg_of_le
    (fun k => mul_nonneg (by show (0:ℝ) ≤ ((k:ℝ)*Real.pi)^2; positivity) (abs_nonneg _))
    (fun k => ?_)
  have hb : |c k t| ≤ Bt 0 k := by
    have := H.coeff_bound 0 k t (by norm_num)
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  exact mul_le_mul_of_nonneg_left hb (by show (0:ℝ) ≤ ((k:ℝ)*Real.pi)^2; positivity)

/-! ### The full `ChemDivMixedReprWitnessData` assembly. -/

/-- Iterate value-coefficient bound `|c k t| ≤ Btu 0 k`. -/
private theorem iterate_coeff0_bound (H : IteratePicardJointC2Data u c Bt)
    (k : ℕ) (t : ℝ) : |c k t| ≤ Bt 0 k := by
  have := H.coeff_bound 0 k t (by norm_num)
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

/-- Resolver value-coefficient bound `|rtc k t| ≤ Bt 0 k`. -/
private theorem resolver_coeff0_bound (H : PhysicalResolverJointC2Data p u Bt)
    (k : ℕ) (t : ℝ) : |resolverTimeCoeff p u k t| ≤ Bt 0 k := by
  have := H.coeff_bound 0 k t (by norm_num)
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

/-- `∑ Bt 0 k` summable (value majorant order 0). -/
private theorem Bt0_summable {Bt : ℕ → ℕ → ℝ}
    (hv : Summable (boundedWeightJointMajorant Bt 0)) : Summable (Bt 0) :=
  hv.congr (fun k => by simp [boundedWeightJointMajorant, valueCosWeight])

/-- `∑ |kπ| Btu 1 k` from the iterate order-2 gradient majorant. -/
private theorem iterate_gradBt1_of_grad2 (Hu : IteratePicardJointC2Data u c Bt)
    (Hg2 : Summable (boundedWeightJointGradMajorant Bt 2)) :
    Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Bt 1 k) :=
  gradB0_of_eigB0 (fun k => iterate_Bt_nonneg Hu 1 k (by norm_num))
    (eigBt1_summable_of_grad (fun k => iterate_Bt_nonneg Hu 0 k (by norm_num))
      (fun k => iterate_Bt_nonneg Hu 1 k (by norm_num))
      (fun k => iterate_Bt_nonneg Hu 2 k (by norm_num)) Hg2)

/-- **The assembled `ChemDivMixedReprWitnessData`** from the resolver joint-`C²`
data, the iterate joint-`C²` data + its order-2 gradient summability, the floor,
and the boundary leg.  All ten reps are bounded-weight cosine series. -/
def mkWitnessData {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {c : ℕ → ℝ → ℝ} {Bt Btu : ℕ → ℕ → ℝ} {τ δ : ℝ}
    (H : PhysicalResolverJointC2Data p u Bt)
    (Hu : IteratePicardJointC2Data u c Btu)
    (Hg2u : Summable (boundedWeightJointGradMajorant Btu 2))
    (hfloor : ∀ q : ℝ × ℝ, 0 < 1 + valueSeriesRep (resolverTimeCoeff p u) q)
    (bdry : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ ({0, 1} : Set ℝ),
      coupledChemDivTimeDerivativeLift p u t x =
        mixedAlgebra p.β (valueSeriesRep c) (iterateDtValue c) (iterateDtGrad c)
          (gradSeriesRep c) (valueSeriesRep (resolverTimeCoeff p u))
          (gradSeriesRep (resolverTimeCoeff p u))
          (grad2SeriesRep (resolverTimeCoeff p u)) (resolverDtValue p u)
          (resolverDtGrad p u) (resolverDtGrad2 p u) (t, x)) :
    ChemDivMixedReprWitnessData p u τ δ where
  Uc := valueSeriesRep c
  Utc := iterateDtValue c
  Utxc := iterateDtGrad c
  Uxc := gradSeriesRep c
  Vc := valueSeriesRep (resolverTimeCoeff p u)
  Vxc := gradSeriesRep (resolverTimeCoeff p u)
  Vxxc := grad2SeriesRep (resolverTimeCoeff p u)
  Vtc := resolverDtValue p u
  Vtxc := resolverDtGrad p u
  Vtxxc := resolverDtGrad2 p u
  cont_Uc := valueSeriesRep_continuous (fun k => (Hu.coeff_contDiff k).continuous)
    (iterate_coeff0_bound Hu) (Bt0_summable (Hu.value_summable 0 (by norm_num)))
  cont_Utc := iterateDtValue_continuous Hu
  cont_Utxc := iterateDtGrad_continuous Hu (iterate_gradBt1_of_grad2 Hu Hg2u)
  cont_Uxc := gradSeriesRep_continuous (fun k => (Hu.coeff_contDiff k).continuous)
    (iterate_coeff0_bound Hu)
    (gradB0_of_eigB0 (fun k => iterate_Bt_nonneg Hu 0 k (by norm_num))
      (eigBt0_summable_of_value (fun k => iterate_Bt_nonneg Hu 0 k (by norm_num))
        (fun k => iterate_Bt_nonneg Hu 1 k (by norm_num))
        (fun k => iterate_Bt_nonneg Hu 2 k (by norm_num)) (Hu.value_summable 2 (by norm_num))))
  cont_Vc := valueSeriesRep_continuous (fun k => (H.coeff_contDiff k).continuous)
    (resolver_coeff0_bound H) (Bt0_summable (H.value_summable 0 (by norm_num)))
  cont_Vxc := gradSeriesRep_continuous (fun k => (H.coeff_contDiff k).continuous)
    (resolver_coeff0_bound H)
    (gradB0_of_eigB0 (fun k => resolver_Bt_nonneg H 0 k (by norm_num))
      (eigBt0_summable_of_value (fun k => resolver_Bt_nonneg H 0 k (by norm_num))
        (fun k => resolver_Bt_nonneg H 1 k (by norm_num))
        (fun k => resolver_Bt_nonneg H 2 k (by norm_num)) (H.value_summable 2 (by norm_num))))
  cont_Vxxc := grad2SeriesRep_continuous (fun k => (H.coeff_contDiff k).continuous)
    (resolver_coeff0_bound H)
    (eigBt0_summable_of_value (fun k => resolver_Bt_nonneg H 0 k (by norm_num))
      (fun k => resolver_Bt_nonneg H 1 k (by norm_num))
      (fun k => resolver_Bt_nonneg H 2 k (by norm_num)) (H.value_summable 2 (by norm_num)))
  cont_Vtc := resolverDtValue_continuous H
  cont_Vtxc := resolverDtGrad_continuous H
  cont_Vtxxc := resolverDtGrad2_continuous H
  floor := hfloor
  Uc_eq := fun t _ht x hx => (Hu.lift_eq_series hx).symm
  Utc_eq := fun t _ht x hx => (iterate_slopeSlice_eq_series Hu t x hx).symm
  Vc_eq := fun t _ht x hx => (coupledChemical_lift_eq_series hx).symm
  Vtc_eq := fun t _ht x hx => (resolver_timeDeriv_eq_series H t x hx).symm
  hUx := fun t _ht x hx => valueRep_hasDerivAt_grad t x
    (iterate_value_eigSummable Hu t) (by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact Hu.lift_eq_series (Ioo_subset_Icc_self hy))
  hUtx := fun t _ht x hx => iterate_slopeSlice_hasDerivAt_grad Hu Hg2u t x hx
  hVx := fun t _ht x hx => valueRep_hasDerivAt_grad t x
    (resolver_eigSummable H t) (by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact coupledChemical_lift_eq_series (Ioo_subset_Icc_self hy))
  hVxx := fun t _ht x hx => gradRep_hasDerivAt_grad2 t x (resolver_eigSummable H t) (by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact (valueRep_hasDerivAt_grad t y (resolver_eigSummable H t) (by
        filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
        exact coupledChemical_lift_eq_series (Ioo_subset_Icc_self hz))).deriv)
  hVtx := fun t _ht x hx => resolver_dt_lift_hasDerivAt_grad H t x hx
  hVtxx := fun t _ht x hx => resolver_dt_lift_hasDerivAt_grad2 H t x hx
  Vxc_eq := fun t _ht x hx => (valueRep_hasDerivAt_grad t x (resolver_eigSummable H t) (by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact coupledChemical_lift_eq_series (Ioo_subset_Icc_self hy))).deriv.symm
  Vtxc_eq := fun t _ht x hx => (resolver_dt_lift_hasDerivAt_grad H t x hx).deriv.symm
  boundary_agree := bdry

/-- **`htime_cont` discharged from {`PhysicalResolverJointC2Data` + iterate
joint-`C²` + iterate gradient summability + floor + boundary}.**  The full
`ChemDivMixedReprWitnessData` is assembled from the committed resolver/iterate
joint regularity, so the `χ₀<0` regularity half's `htime_cont` reduces to exactly
that honest data — all spectral interfaces grounded. -/
theorem chemDivMixedTimeDerivClosedRepr_of_mkWitness
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {c : ℕ → ℝ → ℝ}
    {Bt Btu : ℕ → ℕ → ℝ} {τ δ : ℝ}
    (H : PhysicalResolverJointC2Data p u Bt)
    (Hu : IteratePicardJointC2Data u c Btu)
    (Hg2u : Summable (boundedWeightJointGradMajorant Btu 2))
    (hfloor : ∀ q : ℝ × ℝ, 0 < 1 + valueSeriesRep (resolverTimeCoeff p u) q)
    (bdry : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ ({0, 1} : Set ℝ),
      coupledChemDivTimeDerivativeLift p u t x =
        mixedAlgebra p.β (valueSeriesRep c) (iterateDtValue c) (iterateDtGrad c)
          (gradSeriesRep c) (valueSeriesRep (resolverTimeCoeff p u))
          (gradSeriesRep (resolverTimeCoeff p u))
          (grad2SeriesRep (resolverTimeCoeff p u)) (resolverDtValue p u)
          (resolverDtGrad p u) (resolverDtGrad2 p u) (t, x)) :
    ShenWork.IntervalCoupledRegularityBootstrap.ChemDivMixedTimeDerivClosedRepr
      p u τ δ :=
  chemDivMixedTimeDerivClosedRepr_of_witness (mkWitnessData H Hu Hg2u hfloor bdry)

end ShenWork.IntervalChemDivMixedReprWitness
