# Q827 / cron1: does `coupledChemDivFlux_contDiffAt_of_factorJointC2` work for smooth reps?

Repo inspected: `xiangyazi24/Shen_work`
Source ref inspected: `main`
Branch written: `chatgpt-scratch`

## Verdict

`coupledChemDivFlux_contDiffAt_of_factorJointC2` **does not take arbitrary smooth representatives** `U_cos` / `V_cos` directly.  It is hard-wired to the coupled lifted API:

```lean
hu : ContDiffAt ℝ 2
  (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)

hv : ContDiffAt ℝ 2
  (fun q : ℝ × ℝ =>
    intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
  (s, x)

hgradv : ContDiffAt ℝ 2
  (fun q : ℝ × ℝ =>
    deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
  (s, x)
```

and concludes:

```lean
ContDiffAt ℝ 2
  (Function.uncurry (coupledChemDivFluxLift p u)) (s, x)
```

So the theorem takes the `intervalDomainLift` versions, **not** a hypothesis of the form

```lean
hu : ContDiffAt ℝ 2 (fun q => U_cos q.1 q.2) (s, x)
```

## Exact target flux

The target is also hard-wired:

```lean
def coupledChemDivFluxLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s y : ℝ) : ℝ :=
  let v : ℝ → ℝ := intervalDomainLift (coupledChemicalConcentration p u s)
  intervalDomainLift (u s) y * deriv v y / (1 + v y) ^ p.β
```

That is the lifted/coupled flux, not the smooth representative

```lean
deriv
  (ShenWork.Paper2.ChemDivSpatialC2.chemFluxFun p.β
    (fun x => U_cos s x)
    (fun x => V_cos s x)) x
```

or its uncurried version.

## What this means for sub-sorry `2A-core`

For `2A-core`, which asks for continuity of the **smooth representative** built from `U_cos` and `V_cos`, do not call `coupledChemDivFlux_contDiffAt_of_factorJointC2` directly.  There are two clean routes:

### Route A: prove a generic smooth-representative analogue

Use the existing theorem as a template and make a local/generic lemma with arbitrary factors:

```lean
-- schematic
theorem smoothChemFlux_contDiffAt_of_factorJointC2
    {β : ℝ} {U V G : ℝ × ℝ → ℝ} {q0 : ℝ × ℝ}
    (hU : ContDiffAt ℝ 2 U q0)
    (hV : ContDiffAt ℝ 2 V q0)
    (hG : ContDiffAt ℝ 2 G q0)
    (hbase : 0 < 1 + V q0) :
    ContDiffAt ℝ 2 (fun q => U q * G q / (1 + V q) ^ β) q0 := by
  have hbase_fun : ContDiffAt ℝ 2 (fun q => 1 + V q) q0 := by
    simpa using (contDiffAt_const (c := (1 : ℝ))).add hV
  have hden : ContDiffAt ℝ 2 (fun q => (1 + V q) ^ β) q0 :=
    hbase_fun.rpow_const_of_ne (ne_of_gt hbase)
  have hden_ne : (1 + V q0) ^ β ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hbase β)
  simpa using (hU.mul hG).div hden hden_ne
```

Then instantiate:

```lean
U q := U_cos q.1 q.2
V q := V_cos q.1 q.2
G q := deriv (V_cos q.1) q.2
```

This matches the actual `2A-core` smooth-representative statement.

### Route B: prove continuity for lifted flux, then transfer by agreement

You can use `coupledChemDivFlux_contDiffAt_of_factorJointC2` for the lifted/coupled flux, then use the separate agreement subgoal (`2A-agree`) to transfer `ContinuousOn` by `ContinuousOn.congr`.

But that does **not** prove `2A-core` as currently written if `2A-core` specifically names the smooth representative.  It proves the coupled lifted flux/source continuity and relies on agreement to rewrite.

## Existing spatial-only smooth-representative lemma

There is already a one-variable smooth-representative lemma in:

```text
ShenWork/Paper2/IntervalChemDivSpatialC2.lean
```

It defines:

```lean
def chemFluxFun (β : ℝ) (u v : ℝ → ℝ) (y : ℝ) : ℝ :=
  u y * deriv v y / (1 + v y) ^ β
```

and proves, for global spatial functions:

```lean
theorem chemFlux_contDiff_three
    {β : ℝ} {u v : ℝ → ℝ}
    (hu : ContDiff ℝ 4 u)
    (hv : ContDiff ℝ 4 v)
    (hv_pos : ∀ x, (0 : ℝ) < 1 + v x)
    (hβnn : 0 ≤ β) :
    ContDiff ℝ 3 (chemFluxFun β u v)
```

and:

```lean
theorem chemFluxDeriv_contDiff_two
    {β : ℝ} {u v : ℝ → ℝ}
    (hu : ContDiff ℝ 4 u) (hv : ContDiff ℝ 4 v)
    (hv_pos : ∀ x, (0 : ℝ) < 1 + v x) (hβnn : 0 ≤ β) :
    ContDiff ℝ 2 (deriv (chemFluxFun β u v))
```

These are spatial-only, not joint `(s,x)` lemmas.  For `2A-core`, the missing piece is the joint analogue/localization of this smooth-representative calculus.

## Practical conclusion

Answer to the specific question:

```text
coupledChemDivFlux_contDiffAt_of_factorJointC2 requires intervalDomainLift inputs.
It does not accept U_cos/V_cos directly.
```

For `2A-core`, either:

1. add a generic `smoothChemFlux_contDiffAt_of_factorJointC2` using the same five-line `ContDiffAt.add` / `.rpow_const_of_ne` / `.mul` / `.div` proof, then get continuity of the derivative/fderiv of the smooth representative; or
2. use the existing coupled theorem only after translating the problem to the lifted coupled flux and then use `2A-agree`/`ContinuousOn.congr` to connect back to the smooth representative.
