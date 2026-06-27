# Q1029 (cron2) — direct resolver inner commute without `PhysicalResolverJointC2Data`

Static repo inspection only; I did **not** run Lean.

I read `ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean`. The existing theorem

```lean
theorem coupledChemical_innerCommute_of_physicalJointC2
```

uses `PhysicalResolverJointC2Data` only to obtain resolver-value joint `C²` at the points needed for the two bridge steps:

1. `hFC2` at `(s, y)` for the Clairaut theorem,
2. C² eventually in `r` at `(r, y)` for the spatial-derivative bridge,
3. C² eventually in `z` at `(s, z)` for the time-derivative bridge.

The replacement below takes (1) and (2) directly. For (3), it uses the locality theorem `ContDiffAt.eventually` from `hv_c2`, then pulls that eventual fact back along `z ↦ (s, z)`.

```lean
import ShenWork.PDE.IntervalChemDivFACCommuteDischarge

open ShenWork.IntervalDomain
open ShenWork.IntervalCoupledRegularityBootstrap
open Set Filter Topology

noncomputable section

namespace ShenWork.Paper2.Level0DirectResolverCommute

/-- Direct resolver inner commute from local joint `C²` hypotheses, without
`PhysicalResolverJointC2Data`.

This is the same Clairaut/bridge proof as
`coupledChemical_innerCommute_of_physicalJointC2`, but the resolver regularity is
supplied directly:

* `hv_c2` gives joint `C²` at `(s,y)` for Clairaut and, by locality of
  `ContDiffAt`, joint `C²` at `(s,z)` for `z` near `y`;
* `hv_time` gives joint `C²` at `(r,y)` for `r` near `s`, which is exactly the
  spatial bridge needed for
  `r ↦ deriv (intervalDomainLift (coupledChemicalConcentration p u r)) y`.
-/
theorem coupledChemical_innerCommute_of_directJointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s y : ℝ}
    (hv_c2 : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
      (s, y))
    (hv_time : ∀ᶠ r in 𝓝 s, ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
      (r, y)) :
    HasDerivAt
      (fun r => deriv (intervalDomainLift (coupledChemicalConcentration p u r)) y)
      (deriv (coupledChemicalTimeDerivativeLift p u s) y) s := by
  set F : ℝ → ℝ → ℝ :=
    fun r => intervalDomainLift (coupledChemicalConcentration p u r) with hF
  have hFC2 : ContDiffAt ℝ 2 (Function.uncurry F) (s, y) := by
    simpa [F, Function.uncurry] using hv_c2

  -- Spatial bridge: `∂ₓ(F r)` is the `(0,1)` Fréchet partial for `r` near `s`.
  have hspatial :
      (fun r : ℝ => deriv (F r) y) =ᶠ[𝓝 s]
        (fun r : ℝ => fderiv ℝ (Function.uncurry F) (r, y) (0, 1)) := by
    filter_upwards [hv_time] with r hrv
    have hgr : ContDiffAt ℝ 2 (Function.uncurry F) (r, y) := by
      simpa [F, Function.uncurry] using hrv
    have hdiff : DifferentiableAt ℝ (Function.uncurry F) (r, y) :=
      hgr.differentiableAt (by norm_num)
    simpa [F, Function.uncurry] using
      real_twoVar_spatial_deriv_eq_fderiv_of_differentiableAt hdiff

  -- Time bridge: `∂ₜ(F · z)` is the `(1,0)` Fréchet partial for `z` near `y`.
  -- Unlike the physical proof, this uses only locality of `hv_c2` near `(s,y)`.
  have htime :
      (fun z : ℝ => coupledChemicalTimeDerivativeLift p u s z) =ᶠ[𝓝 y]
        (fun z : ℝ => fderiv ℝ (Function.uncurry F) (s, z) (1, 0)) := by
    have hFC2_eventually :
        ∀ᶠ q in 𝓝 (s, y), ContDiffAt ℝ 2 (Function.uncurry F) q :=
      hFC2.eventually (by norm_num)
    have hpair_tendsto : Tendsto (fun z : ℝ => (s, z)) (𝓝 y) (𝓝 (s, y)) := by
      simpa using (continuous_const.prod continuous_id).continuousAt
    have hFC2_y :
        ∀ᶠ z in 𝓝 y, ContDiffAt ℝ 2 (Function.uncurry F) (s, z) :=
      hpair_tendsto.eventually hFC2_eventually
    filter_upwards [hFC2_y] with z hz
    have hdiff : DifferentiableAt ℝ (Function.uncurry F) (s, z) :=
      hz.differentiableAt (by norm_num)
    have hbridge := real_twoVar_time_deriv_eq_fderiv_of_differentiableAt hdiff
    simpa [coupledChemicalTimeDerivativeLift, F, Function.uncurry] using hbridge

  simpa [F] using
    real_twoVar_clairaut_hasDerivAt_of_fderiv_partials
      (F := F) (Ft := coupledChemicalTimeDerivativeLift p u)
      hFC2 hspatial htime

end ShenWork.Paper2.Level0DirectResolverCommute
```

## Notes

The theorem intentionally has no `hy : y ∈ Ioo 0 1` hypothesis. The old theorem needed `hy` only to obtain joint `C²` from `PhysicalResolverJointC2Data`; here the joint `C²` facts are supplied directly.

The only slightly delicate line is:

```lean
hFC2.eventually (by norm_num)
```

This uses Mathlib's locality theorem for `ContDiffAt n` when `n ≠ ∞`. Since `n = 2`, the side condition should discharge by `norm_num`.
