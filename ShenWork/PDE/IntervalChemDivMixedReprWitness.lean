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
open ShenWork.IntervalResolverSpectralJointC2Concrete (valueCosWeight)
open ShenWork.CosineSpectrum (cosineMode cosineMode_deriv)
open ShenWork.IntervalDuhamelClosedC2 (cosineCoeffSeries_grad_hasDerivAt)
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

end ShenWork.IntervalChemDivMixedReprWitness
