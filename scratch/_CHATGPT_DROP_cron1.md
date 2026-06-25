# Q463 / cron1: `chemDivLift_contDiffOn_two` from global flux regularity

## Executive verdict

Yes, the **equality bridge** is the right route:

```lean
chemDivLift p u v = deriv (chemFluxFun p.β (intervalDomainLift u) (intervalDomainLift v))
```

on `Set.Icc 0 1`, by unfolding `chemDivLift`, `intervalDomainLift`, `intervalDomainChemotaxisDiv`, and `chemFluxFun`.

But the theorem exactly as stated with only

```lean
hu : ContDiffOn ℝ 4 (intervalDomainLift u) (Icc 0 1)
hv : ContDiffOn ℝ 4 (intervalDomainLift v) (Icc 0 1)
```

cannot be proved using your existing theorem

```lean
chemFluxDeriv_contDiff_two :
  ContDiff ℝ 4 u → ContDiff ℝ 4 v → ... →
  ContDiff ℝ 2 (deriv (chemFluxFun β u v))
```

because that theorem requires **global** `ContDiff`, not merely `ContDiffOn`.  Also, because `deriv` is the ambient derivative, endpoint behavior is not controlled by `ContDiffOn` alone.  This is exactly the zero-extension endpoint trap that has appeared elsewhere in the repo.

For the heat/cosine-series case where you really have global `C⁴` of the actual functions

```lean
ContDiff ℝ 4 (intervalDomainLift u)
ContDiff ℝ 4 (intervalDomainLift v)
```

the proof should go through by the two-step plan.

Recommended landed theorem:

```lean
namespace ShenWork.Paper2.ChemDivSpatialC2

open Set
open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalDomainChemotaxisDiv)
open ShenWork.IntervalBFormSpectral (chemDivLift)

/-- On `[0,1]`, the lifted physical chem-div slice is exactly the ambient
spatial derivative of the flux function built from the lifted fields. -/
theorem chemDivLift_eq_deriv_chemFluxFun_on_Icc
    {p : CM2Params} {u v : intervalDomainPoint → ℝ} :
    Set.EqOn (chemDivLift p u v)
      (deriv (chemFluxFun p.β (intervalDomainLift u) (intervalDomainLift v)))
      (Set.Icc (0 : ℝ) 1) := by
  intro x hx
  simp [chemDivLift, chemFluxFun, intervalDomainChemotaxisDiv,
    intervalDomainLift, hx]

/-- Global-C⁴ version of the chem-div source `C²` theorem.

This is the theorem closed by the already-landed global flux lemma
`chemFluxDeriv_contDiff_two`.  It is the right form for heat/cosine-series
profiles when the lifted fields are genuinely global `C⁴`. -/
theorem chemDivLift_contDiffOn_two_of_global
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    (hu : ContDiff ℝ 4 (intervalDomainLift u))
    (hv : ContDiff ℝ 4 (intervalDomainLift v))
    (hv_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (0 : ℝ) < 1 + intervalDomainLift v x) :
    ContDiffOn ℝ 2 (chemDivLift p u v) (Set.Icc (0 : ℝ) 1) := by
  have hv_pos_global : ∀ x, (0 : ℝ) < 1 + intervalDomainLift v x := by
    intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · exact hv_pos x hx
    · simp [intervalDomainLift, hx]
  have hderiv : ContDiffOn ℝ 2
      (deriv (chemFluxFun p.β (intervalDomainLift u) (intervalDomainLift v)))
      (Set.Icc (0 : ℝ) 1) :=
    (chemFluxDeriv_contDiff_two
      (β := p.β)
      (u := intervalDomainLift u)
      (v := intervalDomainLift v)
      hu hv hv_pos_global p.hβ).contDiffOn
  refine hderiv.congr ?_
  intro x hx
  exact (chemDivLift_eq_deriv_chemFluxFun_on_Icc
    (p := p) (u := u) (v := v) x hx).symm

end ShenWork.Paper2.ChemDivSpatialC2
```

If `hderiv.congr` has the opposite orientation in your local elaborator, replace the final block by:

```lean
  exact hderiv.congr (fun x hx => by
    exact (chemDivLift_eq_deriv_chemFluxFun_on_Icc
      (p := p) (u := u) (v := v) x hx).symm)
```

or, if that still orients the other way:

```lean
  exact hderiv.congr (fun x hx => by
    exact chemDivLift_eq_deriv_chemFluxFun_on_Icc
      (p := p) (u := u) (v := v) x hx)
```

The only possible fragility is the `simp` line in the equality lemma.  If Lean does not unfold the imported `chemDivLift` due to namespace resolution, use the fully qualified name:

```lean
  simp [ShenWork.IntervalBFormSpectral.chemDivLift, chemFluxFun,
    intervalDomainChemotaxisDiv, intervalDomainLift, hx]
```

---

## Why the original theorem statement is not closed by this proof

Current file `ShenWork/Paper2/IntervalChemDivSpatialC2.lean` already has exactly this skeleton:

```lean
theorem chemDivLift_contDiffOn_two
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    (hu : ContDiffOn ℝ 4 (intervalDomainLift u) (Icc (0 : ℝ) 1))
    (hv : ContDiffOn ℝ 4 (intervalDomainLift v) (Icc (0 : ℝ) 1))
    (hv_pos : ∀ x ∈ Icc (0 : ℝ) 1, (0 : ℝ) < 1 + intervalDomainLift v x) :
    ContDiffOn ℝ 2 (chemDivLift p u v) (Icc (0 : ℝ) 1) := by
  sorry
  -- For global C⁴ u,v: use chemFluxDeriv_contDiff_two + show chemDivLift = deriv(flux) on [0,1]
```

The comment is accurate: the route works **for global `C⁴` u,v**.  It does not close the theorem as stated because `chemFluxDeriv_contDiff_two` has global hypotheses:

```lean
theorem chemFluxDeriv_contDiff_two
    {β : ℝ} {u v : ℝ → ℝ}
    (hu : ContDiff ℝ 4 u) (hv : ContDiff ℝ 4 v)
    (hv_pos : ∀ x, (0 : ℝ) < 1 + v x) (hβnn : 0 ≤ β) :
    ContDiff ℝ 2 (deriv (chemFluxFun β u v))
```

A `ContDiffOn` hypothesis on a closed set does not give this global `ContDiff` premise.  More importantly, the target function contains the ambient `deriv`, not `derivWithin`.  At endpoints, `ContDiffOn` alone is not enough to control the ambient derivative of a zero-extended function.

So there are two honest theorem variants:

1. **Global/heat version**, proved as above:

```lean
ContDiff ℝ 4 (intervalDomainLift u) →
ContDiff ℝ 4 (intervalDomainLift v) →
ContDiffOn ℝ 2 (chemDivLift p u v) (Icc 0 1)
```

2. **Pure closed-interval version**, which requires a separate `ContDiffOn` calculus theorem for `deriv (chemFluxFun ...)`, and probably extra endpoint/ambient-derivative compatibility assumptions.  It is not a direct corollary of the global theorem.

---

## Important endpoint caveat

Be careful with the phrase “`intervalDomainLift u` is globally C⁴.”  In this repo, `intervalDomainLift` is the zero-extension of an interval function.  If the interval function is nonzero at `0` or `1`, the zero-extension is not even globally continuous.  Several repo comments record this endpoint trap for chem-div/const-extension representatives.

Thus the `_of_global` theorem is valid and useful only when the actual function named `intervalDomainLift u` is indeed globally `C⁴`.  If the heat/cosine object you have is a separate global cosine representative that merely agrees with the interval lift on `[0,1]`, then instantiate the theorem with that representative at the flux level, or prove a variant whose equality hypothesis is stated against the representative:

```lean
Set.EqOn (intervalDomainLift u) U (Icc 0 1)
Set.EqOn (intervalDomainLift v) V (Icc 0 1)
ContDiff ℝ 4 U
ContDiff ℝ 4 V
```

Then show the resulting flux derivative agrees with `chemDivLift` on `Icc`.  That variant avoids falsely claiming global smoothness of the zero-extension.

---

## Final answer

* The equality step is correct and should be a `simp` lemma.
* The proof using `chemFluxDeriv_contDiff_two.contDiffOn` works for a strengthened global-C⁴ theorem.
* It does **not** prove the theorem with only `ContDiffOn` hypotheses.
* For the heat-semigroup route, use/produce the global-C⁴ hypotheses for the actual global representative, then transfer by `Set.EqOn` to `chemDivLift` on `[0,1]`.
