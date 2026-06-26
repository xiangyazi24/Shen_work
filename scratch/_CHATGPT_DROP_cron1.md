# Q829 / cron1: generic smooth-representative `ContDiffAt` for `chemFluxFun`

Repo inspected: `xiangyazi24/Shen_work`
Source ref inspected: `main`
Branch written: `chatgpt-scratch`

## Verdict

There is **not** an already-factored generic smooth-representative lemma of the exact form

```lean
ContDiffAt ℝ 2 (fun q => chemFluxFun β (U q.1) (V q.1) q.2) (s, x)
```

or named something like `smoothChemFlux_contDiffAt...` / `chemFlux_contDiffAt...` that I found.

But the repo already demonstrates the exact Mathlib calculus methods you need in the coupled/lifted theorem:

```lean
ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivFlux_contDiffAt_of_factorJointC2
```

File:

```text
ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean
```

That proof uses:

```lean
(contDiffAt_const (c := (1 : ℝ))).add hv
hbase_fun.rpow_const_of_ne (ne_of_gt hbase)
(hu.mul hgradv).div hden hden_ne
```

So for Route A, build the generic smooth-representative lemma directly from Mathlib using the same proof skeleton.  You do **not** need new analytic infrastructure for the product/quotient/rpow part.

## `chemFluxFun` definition check

Yes.  In

```text
ShenWork/Paper2/IntervalChemDivSpatialC2.lean
```

`chemFluxFun` unfolds exactly as desired:

```lean
/-- The chemotaxis flux function whose spatial derivative is the chemDiv source.
`φ(y) = lift(u)(y) · deriv(lift(v))(y) / (1 + lift(v)(y))^β` -/
def chemFluxFun (β : ℝ) (u v : ℝ → ℝ) (y : ℝ) : ℝ :=
  u y * deriv v y / (1 + v y) ^ β
```

Therefore:

```lean
chemFluxFun β (U q.1) (V q.1) q.2
```

is definitionally:

```lean
U q.1 q.2 * deriv (V q.1) q.2 / (1 + V q.1 q.2) ^ β
```

## Existing non-generic theorem as template

The coupled theorem has hypotheses hard-wired to `intervalDomainLift`:

```lean
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
```

and concludes:

```lean
ContDiffAt ℝ 2
  (Function.uncurry (coupledChemDivFluxLift p u)) (s, x)
```

So it is not directly usable for `U_cos`/`V_cos`, but its proof is exactly the generic proof you want.

## Suggested generic lemma

A local lemma should be short:

```lean
theorem smoothChemFlux_contDiffAt_of_factorJointC2
    {β : ℝ} {U V : ℝ → ℝ → ℝ} {s x : ℝ}
    (hU : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => U q.1 q.2) (s, x))
    (hV : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => V q.1 q.2) (s, x))
    (hgradV : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => deriv (V q.1) q.2) (s, x))
    (hbase : 0 < 1 + V s x) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        ShenWork.Paper2.ChemDivSpatialC2.chemFluxFun β (U q.1) (V q.1) q.2)
      (s, x) := by
  unfold ShenWork.Paper2.ChemDivSpatialC2.chemFluxFun
  have hbase_fun : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => 1 + V q.1 q.2) (s, x) := by
    simpa using (contDiffAt_const (c := (1 : ℝ))).add hV
  have hden : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => (1 + V q.1 q.2) ^ β) (s, x) :=
    hbase_fun.rpow_const_of_ne (ne_of_gt hbase)
  have hden_ne : (1 + V s x) ^ β ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hbase β)
  exact (hU.mul hgradV).div hden hden_ne
```

If the final `exact` leaves a definitional mismatch because of pair simplification, use:

```lean
  simpa using (hU.mul hgradV).div hden hden_ne
```

or keep the `unfold chemFluxFun` before the denominator proof as shown.

## Existing spatial-only smooth-representative lemmas

`IntervalChemDivSpatialC2.lean` has one-variable/global spatial lemmas:

```lean
theorem chemFlux_contDiff_three
    {β : ℝ} {u v : ℝ → ℝ}
    (hu : ContDiff ℝ 4 u)
    (hv : ContDiff ℝ 4 v)
    (hv_pos : ∀ x, (0 : ℝ) < 1 + v x)
    (hβnn : 0 ≤ β) :
    ContDiff ℝ 3 (chemFluxFun β u v)
```

The proof uses the same algebraic ingredients:

```lean
have hprod : ContDiff ℝ 3 (fun y => u y * deriv v y) := hu3.mul hv3
have h1v : ContDiff ℝ 3 (fun y => 1 + v y) := contDiff_const.add hv3'
exact h1v.rpow_const_of_ne (fun x => ne_of_gt (hv_pos x))
exact hprod.div hdenom (fun x => hdenom_pos x)
```

and it also has:

```lean
theorem chemFluxDeriv_contDiff_two ... :
  ContDiff ℝ 2 (deriv (chemFluxFun β u v))
```

Those are useful confirmation, but they are not the joint `(s,x)` lemma required for `2A-core`.

## Practical answer

Use Mathlib directly, copying the existing coupled theorem proof style.  The exact standard method names are already working in this repo:

```lean
ContDiffAt.add
ContDiffAt.mul
ContDiffAt.div
ContDiffAt.rpow_const_of_ne
contDiffAt_const
```

The generic smooth-representative lemma should be a small local lemma, not a new hard analytic subproblem.