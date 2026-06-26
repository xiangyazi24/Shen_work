# Q824 / cron1: `ContDiffAt` algebra for chem-div flux

Repo inspected: `xiangyazi24/Shen_work`
Source ref inspected: `main`
Branch written: `chatgpt-scratch`

## Verdict

Yes.  The repo already has exactly the product/quotient/rpow `ContDiffAt` calculus you need, packaged as a chem-div flux producer:

```lean
ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivFlux_contDiffAt_of_factorJointC2
```

File:

```text
ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean
```

It proves joint `C²` of the uncurried lifted chemotactic flux

```lean
Function.uncurry (coupledChemDivFluxLift p u)
```

from joint `C²` of the three factors:

```lean
hu     : ContDiffAt ℝ 2 (fun q => intervalDomainLift (u q.1) q.2) (s, x)
hv     : ContDiffAt ℝ 2 (fun q => intervalDomainLift (coupledChemicalConcentration p u q.1) q.2) (s, x)
hgradv : ContDiffAt ℝ 2 (fun q => deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2) (s, x)
hbase  : 0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) x
```

and concludes:

```lean
ContDiffAt ℝ 2
  (Function.uncurry (coupledChemDivFluxLift p u)) (s, x)
```

## Exact algebra names/usages

Inside the theorem, the repo uses these exact Mathlib method names:

```lean
-- constant + resolver value
have hbase_fun : ContDiffAt ℝ 2
    (fun q : ℝ × ℝ =>
      1 + intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
    (s, x) := by
  simpa using (contDiffAt_const (c := (1 : ℝ))).add hv

-- rpow denominator
have hden : ContDiffAt ℝ 2
    (fun q : ℝ × ℝ =>
      (1 + intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
        ^ p.β)
    (s, x) :=
  hbase_fun.rpow_const_of_ne (ne_of_gt hbase)

-- denominator nonzero
have hden_ne :
    (1 + intervalDomainLift (coupledChemicalConcentration p u s) x) ^ p.β ≠ 0 :=
  ne_of_gt (Real.rpow_pos_of_pos hbase p.β)

-- product and quotient
have hquot := (hu.mul hgradv).div hden hden_ne
```

So the relevant names are:

```lean
ContDiffAt.mul              -- used as hu.mul hgradv
ContDiffAt.div              -- used as (hu.mul hgradv).div hden hden_ne
ContDiffAt.rpow_const_of_ne -- used as hbase_fun.rpow_const_of_ne (ne_of_gt hbase)
ContDiffAt.add              -- used as (contDiffAt_const ...).add hv
contDiffAt_const            -- for the constant `1`
```

## Flux definition

The target flux is also already in the repo:

```lean
def coupledChemDivFluxLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s y : ℝ) : ℝ :=
  let v : ℝ → ℝ := intervalDomainLift (coupledChemicalConcentration p u s)
  intervalDomainLift (u s) y * deriv v y / (1 + v y) ^ p.β
```

This is the same algebraic shape as

```lean
chemFluxFun β u v = u · deriv v / (1 + v)^β
```

but in the coupled/lifted API.

## How to use it for the Level0 route

Once `heatSemigroup_jointContDiffAt_two` gives the `hu` factor and the physical resolver route gives `hv` and `hgradv`, the flux `ContDiffAt` step should be just:

```lean
have hflux : ContDiffAt ℝ 2
    (Function.uncurry (coupledChemDivFluxLift p (conjugatePicardIter p u₀ 0))) (s, x) :=
  ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivFlux_contDiffAt_of_factorJointC2
    hu hv hgradv hbase
```

where `hbase` is the local positivity of `1 + v`.

## Derivative / outer-commute support already nearby

The same producer file also has a bridge from joint differentiability of a two-variable map to the spatial directional Fréchet derivative:

```lean
theorem real_twoVar_spatial_deriv_eq_fderiv_of_differentiableAt
    {F : ℝ × ℝ → ℝ} {s x : ℝ}
    (hF : DifferentiableAt ℝ F (s, x)) :
    deriv (fun y : ℝ => F (s, y)) x =
      fderiv ℝ F (s, x) (0, 1)
```

and `IntervalChemDivOuterCommuteProducer.lean` uses `ContDiffAt ℝ 2` plus `hf.fderiv_right` to get the second-derivative / Clairaut bridge.  In particular, it has:

```lean
(hf.fderiv_right (m := 1) (n := 2) (by norm_num)).differentiableAt
```

and packages the primitive requirement as `CoupledChemDivFluxJointC2Hyp`, whose local slab field includes:

```lean
∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
  ContDiffAt ℝ 2
    (Function.uncurry (coupledChemDivFluxLift p u)) (s, x)
```

## Practical conclusion

For 1A / 2A-core, do **not** need to re-prove the product/quotient/rpow calculus.  The repo already has it as `coupledChemDivFlux_contDiffAt_of_factorJointC2`.  The remaining work is to supply the factor hypotheses:

1. `hu`: heat level-0 lifted value joint `C²`, from `heatSemigroup_jointContDiffAt_two` plus `hagree_zero` / eventual equality on the spatial interior.
2. `hv`: resolver value joint `C²`, from the physical resolver joint C² data.
3. `hgradv`: resolver spatial-gradient joint `C²`, from the same physical resolver route.
4. `hbase`: local positivity of `1 + v`.

Then call the existing theorem and use the existing derivative/fderiv bridge infrastructure for the chemDiv source derivative continuity.