# Q828 (cron2) — 2A-core, smooth cosine-representative flux derivative

Static repo inspection only; I did not run a local Lean build.

## Short answer

Yes, the repo applies `chemFlux_contDiff_three` / `chemFluxDeriv_contDiff_two` to cosine representatives, but only in the **fixed-time spatial** sense.  I did **not** find a committed theorem giving the full joint `(s,x)` regularity of

```lean
fun q : ℝ × ℝ => chemFluxFun β (U_cos q.1) (V_cos q.1) q.2
```

or of its spatial derivative.  For 2A-core, the correct move is to clone/adapt the existing joint flux infrastructure from the coupled/lifted lane, not to try to reuse `chemFlux_contDiff_three` directly.

## What exists: fixed-time cosine-representative flux regularity

In

```text
ShenWork/Paper2/IntervalChemDivSpatialC2.lean
```

we have:

```lean
def chemFluxFun (β : ℝ) (u v : ℝ → ℝ) (y : ℝ) : ℝ :=
  u y * deriv v y / (1 + v y) ^ β
```

and the fixed-spatial calculus lemmas:

```lean
theorem chemFlux_contDiff_three
    {β : ℝ} {u v : ℝ → ℝ}
    (hu : ContDiff ℝ 4 u)
    (hv : ContDiff ℝ 4 v)
    (hv_pos : ∀ x, (0 : ℝ) < 1 + v x)
    (hβnn : 0 ≤ β) :
    ContDiff ℝ 3 (chemFluxFun β u v)

theorem chemFluxDeriv_contDiff_two
    {β : ℝ} {u v : ℝ → ℝ}
    (hu : ContDiff ℝ 4 u) (hv : ContDiff ℝ 4 v)
    (hv_pos : ∀ x, (0 : ℝ) < 1 + v x) (hβnn : 0 ≤ β) :
    ContDiff ℝ 2 (deriv (chemFluxFun β u v))
```

The cosine-representative consumer is:

```lean
noncomputable def chemDivSource_weakH2_of_cosineRep
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    {U_cos V_cos : ℝ → ℝ}
    (hu_cos : ContDiff ℝ 4 U_cos)
    (hv_cos : ContDiff ℝ 4 V_cos)
    (hv_cos_pos : ∀ x, (0 : ℝ) < 1 + V_cos x)
    ... :
    IntervalWeakH2Neumann (chemDivLift p u v) := by
  set F := deriv (chemFluxFun p.β U_cos V_cos)
  have hF_C2 : ContDiff ℝ 2 F :=
    chemFluxDeriv_contDiff_two hu_cos hv_cos hv_cos_pos p.hβ
  ...
```

So: **yes**, `chemFlux_contDiff_three` is used on `U_cos`, `V_cos`, but it is for one frozen time `s`, with `U_cos V_cos : ℝ → ℝ`.

`IntervalConjugateLevel0BFormSourceOn.lean` also builds exactly this fixed-time setup: it defines

```lean
set U_cos := fun x => ∑' k,
  (Real.exp (-s * unitIntervalCosineEigenvalue k) * heatCoeff u₀ k) * cosineMode k x
```

then proves `hU_C4 : ContDiff ℝ 4 U_cos` via `heatSemigroup_contDiff_four`, proves agreement with the level-0 lift using `hagree_zero`, and introduces a `V_cos` resolver representative package with `ContDiff ℝ 4 V_cos`, positivity, agreement, and parity fields.  Again, this is per fixed `s`, not joint in `s`.

## What exists for joint regularity: the lifted coupled-flux lane

The useful joint template is in

```text
ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean
```

The core theorem is:

```lean
theorem coupledChemDivFlux_contDiffAt_of_factorJointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s x : ℝ}
    (hu : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x))
    (hv : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
      (s, x))
    (hgradv : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
      (s, x))
    (hbase : 0 <
      1 + intervalDomainLift (coupledChemicalConcentration p u s) x) :
    ContDiffAt ℝ 2
      (Function.uncurry (coupledChemDivFluxLift p u)) (s, x)
```

This is exactly the product/quotient/rpow argument you want, but for the lifted coupled flux, not the smooth representatives.  The proof constructs

```lean
1 + v,  (1+v)^β,  u * gradv / (1+v)^β
```

using `ContDiffAt.add`, `ContDiffAt.rpow_const_of_ne`, `ContDiffAt.mul`, and `ContDiffAt.div`.

The same file also has the fixed-time spatial derivative bridge:

```lean
theorem real_twoVar_spatial_deriv_eq_fderiv_of_differentiableAt
    {F : ℝ × ℝ → ℝ} {s x : ℝ}
    (hF : DifferentiableAt ℝ F (s, x)) :
    deriv (fun y : ℝ => F (s, y)) x =
      fderiv ℝ F (s, x) (0, 1)
```

This is the bridge from `deriv (chemFluxFun β (U_cos s) (V_cos s)) x` to the spatial Fréchet partial of the joint function.

## Existing resolver gradient joint regularity is a separate field

One important correction to the route as stated: from joint `C²` of `V(s,x)` alone, the spatial derivative `V_x(s,x)` is only joint `C¹` by the usual derivative-loses-one principle.  To get flux `ContDiffAt ℝ 2` from the rational formula, the existing coupled theorem assumes the gradient factor itself is joint `C²`:

```lean
hgradv : ContDiffAt ℝ 2
  (fun q : ℝ × ℝ => deriv (... q.1) q.2) (s, x)
```

That is not derived from `hv` in the flux theorem; it is supplied separately.

In the resolver physical lane, this separate gradient regularity is produced by:

```lean
theorem coupledChemical_grad_jointContDiffAt_two
    (H : PhysicalResolverJointC2Data p u Bt) {s x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
      (s, x)
```

It uses a separate bounded-weight gradient assembler and an eventual equality that rewrites the derivative of the lifted resolver to the gradient cosine series.

For the smooth representative version, you want the same data shape: joint regularity of `U`, joint regularity of `V`, and joint regularity of `V_x`.  If you only have `U,V : C²_joint`, then you can still prove the flux is `C¹_joint`, which is enough for continuity of the spatial derivative; but you should not expect `Φ : C²_joint` unless `V_x` is also `C²_joint` (or `V` is joint `C³` with the right API).

## Recommended 2A-core lemma shape

Define the smooth representative joint flux:

```lean
def smoothChemFluxJoint (β : ℝ) (U V : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun q => chemFluxFun β (U q.1) (V q.1) q.2
```

Then prove a representative analogue of `coupledChemDivFlux_contDiffAt_of_factorJointC2`:

```lean
theorem smoothChemFluxJoint_contDiffAt_of_factor
    {β : ℝ} {U V : ℝ → ℝ → ℝ} {s x : ℝ}
    (hU : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => U q.1 q.2) (s, x))
    (hV : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => V q.1 q.2) (s, x))
    (hVx : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => deriv (V q.1) q.2) (s, x))
    (hbase : 0 < 1 + V s x) :
    ContDiffAt ℝ 1 (smoothChemFluxJoint β U V) (s, x) := by
  -- same proof as `coupledChemDivFlux_contDiffAt_of_factorJointC2`, with order 1
  -- unfold `smoothChemFluxJoint`, `chemFluxFun`
  -- build `1 + V`, `(1 + V)^β`, then `(U * Vx) / denom`
```

Use order `2` instead of order `1` if you really have `hVx : ContDiffAt ℝ 2 ...`; but for mere continuity of the chemDiv source, order `1` is enough.

Then convert the spatial derivative to a continuous function on the rectangle.  Let

```lean
R : Set (ℝ × ℝ) := Set.Icc c T ×ˢ Set.Icc (0 : ℝ) 1
Φ : ℝ × ℝ → ℝ := smoothChemFluxJoint β U V
Ψ : ℝ × ℝ → ℝ := fun q => deriv (chemFluxFun β (U q.1) (V q.1)) q.2
ΨF : ℝ × ℝ → ℝ := fun q => fderiv ℝ Φ q (0, 1)
```

From `hΦ : ∀ q ∈ R, ContDiffAt ℝ 1 Φ q`, prove continuity of `ΨF` pointwise using `fderiv_right` at order zero:

```lean
have hΨF_cont : ContinuousOn ΨF R := by
  intro q hq
  let ex : ℝ × ℝ := (0, 1)
  let evalEx : (ℝ × ℝ →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ) ex
  have hfd : ContDiffAt ℝ 0 (fun q => fderiv ℝ Φ q) q :=
    (hΦ q hq).fderiv_right (m := 0) (n := 1) (by norm_num)
  exact (evalEx.continuous.continuousAt.comp q hfd.continuousAt).continuousWithinAt
```

Then identify `Ψ` and `ΨF` on `R` using the repo theorem:

```lean
have hΨ_eq : ∀ q ∈ R, Ψ q = ΨF q := by
  intro q hq
  rcases q with ⟨s, x⟩
  have hd : DifferentiableAt ℝ Φ (s, x) :=
    (hΦ (s, x) hq).differentiableAt (by norm_num)
  simpa [Φ, Ψ, ΨF, smoothChemFluxJoint] using
    ShenWork.IntervalCoupledRegularityBootstrap
      .real_twoVar_spatial_deriv_eq_fderiv_of_differentiableAt
        (F := Φ) hd
```

Finally:

```lean
exact hΨF_cont.congr hΨ_eq
```

(or do the `intro q hq` version manually if `ContinuousOn.congr` inference is annoying).

## Bottom line

* `chemFlux_contDiff_three` is already applied to cosine representatives, but only for fixed `s` / spatial regularity.
* The repo does **not** appear to have a joint `(s,x)` cosine-representative theorem for `deriv (chemFluxFun β (U_cos s) (V_cos s)) x`.
* The right source to copy is `coupledChemDivFlux_contDiffAt_of_factorJointC2` plus `real_twoVar_spatial_deriv_eq_fderiv_of_differentiableAt`.
* For 2A-core `ContinuousOn`, proving joint `C¹` of the smooth flux representative is enough; proving joint `C²` is stronger and requires a separately joint-`C²` gradient factor `V_x`, just as the coupled lane explicitly assumes/produces `hgradv_c2`.
