# Q730 / cron1: is sub-sorry 1A the same as joint continuity?

Repo inspected: `xiangyazi24/Shen_work`.  Scratch write target: branch `chatgpt-scratch`.

## Verdict

Sub-sorry 1A is **not solved by the abstract `IntervalWeakH2Neumann` certificate alone**.  It is essentially a **joint-continuity/compactness argument for a canonical second-derivative representative**.

More precisely:

* If sub-sorry 2A means joint continuity of the **source value**

```lean
(s,x) ↦ coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s x
```

then 1A is **not the same**.  1A needs the same type of compactness argument, but for the **second spatial derivative** of the chemDiv source representative:

```lean
(s,x) ↦ deriv (deriv F_s) x
```

where `F_s` is the classical chemDiv-source representative.

* If sub-sorry 2A means joint continuity of this **second derivative field**, then yes: sub-sorry 1A is just the compactness corollary of that statement.

The clean route is:

```lean
have hJ : ContinuousOn G (Icc c T ×ˢ Icc (0 : ℝ) 1)
-- where G (s,x) = deriv (deriv F_s) x
have hbd : ∃ C, 0 ≤ C ∧ ∀ s ∈ Icc c T, ∀ x ∈ Icc 0 1, |G (s,x)| ≤ C :=
  -- compactness of `Icc c T ×ˢ Icc 0 1` plus continuity of `|G|`
```

Then transfer from `G` to the proof-dependent field:

```lean
(hH2_per_slice s hs).secondDeriv x = G (s,x)
```

or avoid mentioning `hH2_per_slice.secondDeriv` until after choosing the same canonical `G` in the H² certificate.

## Why the abstract H² certificate does not give 1A

`IntervalWeakH2Neumann` is defined in:

```text
ShenWork/PDE/IntervalMildSourceDecayHelper.lean
```

as:

```lean
structure IntervalWeakH2Neumann (f : ℝ → ℝ) where
  secondDeriv : ℝ → ℝ
  second_intervalIntegrable : IntervalIntegrable secondDeriv volume (0 : ℝ) 1
  second_abs_integral_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∫ x in (0 : ℝ)..1, |secondDeriv x| ≤ B
  weak_cosine_laplacian : ∀ k : ℕ,
    (∫ x in (0 : ℝ)..1,
        Real.cos ((k : ℝ) * Real.pi * x) * secondDeriv x) =
      -((k : ℝ) * Real.pi) ^ 2 *
        ∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * f x
```

So the structure only gives:

```lean
∃ B, 0 ≤ B ∧ ∫ |secondDeriv| ≤ B
```

**per slice**.  It does not give a uniform-in-`s` bound, and it does not say `secondDeriv` is continuous, canonical, or definitionally equal to a classical derivative unless you know how the certificate was built.

Therefore there is no shortcut from:

```lean
hH2_per_slice : ∀ s ∈ Icc c T,
  IntervalWeakH2Neumann (... s)
```

to:

```lean
∃ C, 0 ≤ C ∧ ∀ s ∈ Icc c T, ∀ x ∈ Icc 0 1,
  |(hH2_per_slice s hs).secondDeriv x| ≤ C
```

without extra uniform information.

## The constructor path does choose a canonical second derivative

The constructor in `IntervalMildSourceDecayHelper.lean` is:

```lean
noncomputable def intervalWeakH2Neumann_of_contDiffOn
    {g : ℝ → ℝ}
    (hgC2 : ContDiffOn ℝ 2 g (Set.Icc (0 : ℝ) 1))
    ... :
    IntervalWeakH2Neumann g where
  secondDeriv := deriv (deriv g)
  second_intervalIntegrable := ...
  second_abs_integral_bound := by
    refine ⟨∫ x in (0 : ℝ)..1, |deriv (deriv g) x|, ?_, le_rfl⟩
  weak_cosine_laplacian := ...
```

So if `hH2_per_slice s hs` is built directly by this constructor, then the `secondDeriv` is exactly the classical expression `deriv (deriv g)`.

In the heat/chemDiv path, the file:

```text
ShenWork/Paper2/IntervalChemDivSpatialC2.lean
```

builds:

```lean
set F := deriv (chemFluxFun p.β U_cos V_cos)
have hF_H2 : IntervalWeakH2Neumann F :=
  intervalWeakH2Neumann_of_contDiffOn hF_C2on htend0 htend1 hbc0 hbc1
```

Then it transfers to `chemDivLift p u v` using the **same** second derivative:

```lean
exact {
  secondDeriv := hF_H2.secondDeriv
  second_intervalIntegrable := hF_H2.second_intervalIntegrable
  second_abs_integral_bound := hF_H2.second_abs_integral_bound
  weak_cosine_laplacian := ... }
```

Thus in this specific path, the abstract proof-dependent field is really the canonical classical field:

```lean
(hH2_per_slice s hs).secondDeriv = deriv (deriv F_s)
```

up to unfolding/reconstructing the same local witness `F_s`.

## Why proof-dependence matters

The term:

```lean
(hH2_per_slice s hs).secondDeriv
```

is proof-dependent because it depends on the actual `IntervalWeakH2Neumann` value returned by `hH2_per_slice s hs`.  Another proof of the same proposition could choose a different weak second derivative representative, as long as it satisfies the weak IBP identity and integrability fields.

So for Lean, it is usually better not to prove compactness directly about that opaque field unless you have a definitional equation for it.  Better options:

1. **Expose the canonical representative** `G s x := deriv (deriv F_s) x` and prove joint continuity/boundedness for `G`.
2. Build `hH2_per_slice` from `G`, so that `secondDeriv` is definitionally `G s` or at least easily reducible to it.
3. Prove a lemma for the specific constructor path:

```lean
(hH2_per_slice s hs).secondDeriv x = deriv (deriv F_s) x
```

then rewrite before compactness/bounding.

## Is there a shortcut?

There are only two real shortcuts:

### Shortcut A: prove uniform L¹ bound directly

Sub-sorry 1A is stronger than needed for `hL1_uniform`.  The actual consumer only needs:

```lean
∃ B, 0 ≤ B ∧ ∀ s ∈ Icc c T,
  ∫ x in (0 : ℝ)..1, |(hH2_per_slice s hs).secondDeriv x| ≤ B
```

So you can skip pointwise boundedness if you can prove a uniform integral estimate directly, for example by spectral estimates or an analytic inequality.  But that still needs a uniform handle on the chosen `secondDeriv`; the abstract per-slice `second_abs_integral_bound` is not uniform.

### Shortcut B: prove continuity of the integral map

Instead of a pointwise bound, prove:

```lean
ContinuousOn
  (fun s => ∫ x in (0 : ℝ)..1, |G s x|)
  (Icc c T)
```

Then compactness of `Icc c T` gives a uniform bound on the integral.  This is weaker than pointwise compactness on `[c,T]×[0,1]`, but in practice it still requires enough joint continuity/dominated convergence infrastructure for `G`.

## Practical recommendation

For this proof, treat 1A as the **second-derivative analogue** of the joint-continuity compactness argument, not as a consequence of the already-existing source-value continuity.

The best Lean design is to introduce a canonical closed-slab representative:

```lean
def chemDivSecondDerivRep (s x : ℝ) : ℝ :=
  deriv (deriv (deriv (chemFluxFun p.β (U_cos s) (V_cos s)))) x
```

or whatever the exact `F_s` unfolding is, prove:

```lean
ContinuousOn (Function.uncurry chemDivSecondDerivRep)
  (Icc c T ×ˢ Icc (0 : ℝ) 1)
```

then compactness gives:

```lean
∃ C, 0 ≤ C ∧ ∀ s ∈ Icc c T, ∀ x ∈ Icc 0 1,
  |chemDivSecondDerivRep s x| ≤ C
```

and finally connect it to the H² certificate by construction/equality:

```lean
(hH2_per_slice s hs).secondDeriv x = chemDivSecondDerivRep s x
```

Bottom line: **no free shortcut from `IntervalWeakH2Neumann`; 1A is basically the joint-continuity+compactness task for the second derivative.**  It is analogous to 2A, but at a higher derivative level and with proof-dependence that should be eliminated by using a canonical representative.
