ANSWER Q82 3294a506

# Verdict

Yes: the supercritical branch admits the same restart-compatible exponential-ceiling architecture as the committed critical branch.

Put

and let

For any C\ge M, the simplest certified barrier is

It is a spatially constant supersolution of the scalar upper equation arising at a whole-line approximate maximum. More strongly, the same algebra certifies every rate

Thus one may instead use

with the fastest rate directly supplied by the calculation, \lambda=dM^\alpha. For Lean, \lambda=d is the cleaner choice: it is positive immediately from the strict supercritical inequality and avoids carrying an extra factor through every restart theorem.

There is no smallness condition on \chi>0. The only load-bearing hypothesis is d>0.

# Current repository state

Audited default main at

```plain text
be15c181c4e688b46b5b24cfc89433cdbfeb0e73
```

The relevant committed sources are:

- ShenWork/Paper1/WholeLineCauchyGlobalBounds.lean:53-59: wholeLineCauchyParameterCeiling.

- WholeLineCauchyGlobalBounds.lean:96-139: wholeLineCauchyParameterCeiling_margin_of_supercritical.

- ShenWork/Paper1/WholeLineCauchyChiPosLongTimeBound.lean:27-79: the critical relaxing ceiling and restart identity.

- WholeLineCauchyChiPosLongTimeBound.lean:81-136: the critical Bernoulli/rpow step and supersolution inequality.

- WholeLineCauchyChiPosLongTimeBound.lean:218-510: the critical slab comparison.

- WholeLineCauchyChiPosLongTimeBound.lean:513-899: segment propagation, restart induction, global bound, and limsup.

The current positive-time file is hardcoded to

```javascript
p.α = p.m + p.γ - 1
```

and to MChi p. The supercritical result should therefore be added in a parallel file rather than forced through the critical theorem by rewriting hypotheses.

# 1. The correct worst-case scalar field

The equation is

Expanding the flux gives

For \chi>0 and v\ge0, the term -\chi u^m v is favorable and may be discarded in an upper estimate. The drift term is not discarded pointwise; at the approximate maximum it is bounded by

using the slab ceiling 0\le u\le A and the existing resolver-gradient estimate |v_x|\le A^\gamma.

The zeroth-order scalar field is therefore exactly

There is no extra Vfactor in this scalar reaction. The resolver upper bound is used for the first-derivative drift coefficient. After using v_{xx}=v-u^\gamma, the bad zeroth-order contribution is exactly +\chi u^{m+\gamma}, while -\chi u^m v\le0.

This is the first sign guard for the Lean implementation: do not replace the exact field by \chi u^q\|v\|_\infty.

# 2. The parameter-ceiling power inequality

The committed parameter ceiling is

```javascript
def wholeLineCauchyParameterCeiling (p : CMParams) : ℝ :=
  if p.m + p.γ - 1 < p.α then
    max 1
      ((1 + max p.χ 0) ^
        (1 / (p.α - (p.m + p.γ - 1))))
  else MChi p
```

In the branch 0\le\chi and q<\alpha, set d=\alpha-q. The reusable quantitative fact should be exported from the local calculation already present in wholeLineCauchyParameterCeiling_margin_of_supercritical:

```javascript
theorem wholeLineCauchyParameterCeiling_pow_gap_of_supercritical
    (p : CMParams) (hχ : 0 ≤ p.χ)
    (hsuper : p.m + p.γ - 1 < p.α) :
    1 + p.χ ≤
      (wholeLineCauchyParameterCeiling p) ^
        (p.α - (p.m + p.γ - 1))
```

For strictly positive \chi, the maximum with 1 is redundant and equality holds:

The weaker inequality 1+\chi\le M^d is better as an interface: it avoids normalizing the max and is all the supersolution proof needs.

The other immediate facts are

# 3. The rpow inequality replacing the critical Bernoulli step

The critical proof uses

In the supercritical proof the correct normalized gap is:

For r\ge1, q\ge0, and d>0,

d(r-1)le r^{q+1}(r^d-1).

A Lean-facing statement is:

```javascript
theorem rpow_supercritical_gap
    {r q d : ℝ} (hr : 1 ≤ r) (hq : 0 ≤ q) (hd : 0 < d) :
    d * (r - 1) ≤ r ^ (q + 1) * (r ^ d - 1)
```

The proof uses one generalized tangent-line inequality:

```javascript
theorem rpow_tangent_at_one_of_one_le
    {r n : ℝ} (hr : 1 ≤ r) (hn : 1 ≤ n) :
    n * r - (n - 1) ≤ r ^ n
```

This is the exact generalization of the committed rpow_bernoulli. The existing theorem assumes 2 ≤ n, which is insufficient here because d+1 may lie strictly between 1 and 2.

Apply the tangent theorem with n=d+1:

Rearranging gives

Since q\ge0 and r\ge1,

Hence

which proves the claimed gap.

A useful scaled version, closer to the final consumer, is:

```javascript
theorem rpow_supercritical_scaled_gap
    {M B q d : ℝ}
    (hM : 0 < M) (hMB : M ≤ B)
    (hq : 0 ≤ q) (hd : 0 < d) :
    d * M ^ (q + d) * (B - M) ≤
      B ^ (q + 1) * (B ^ d - M ^ d)
```

Indeed, with r=B/M,

After substituting q+d=\alpha, this becomes

# 4. Explicit supersolution inequality

Let B\ge M. Since q=m+\gamma-1\ge1, we have 1\le B^q. Therefore

Every step has a simple source:

1. 1\le B^q;

1. 1+\chi\le M^d;

1. \alpha=q+d;

1. rpow_supercritical_scaled_gap.

Consequently the strongest direct statement is

Since M^\alpha\ge1, it follows that

Thus the recommended rate is

More generally, every 0<\lambda\le dM^\alpha is certified.

A consumer-ready Lean statement should be expressed with the actual source term:

```javascript
theorem chiPosSupercriticalCeiling_supersolution
    (p : CMParams) (hχ : 0 ≤ p.χ)
    (hsuper : p.m + p.γ - 1 < p.α)
    {B : ℝ}
    (hB : wholeLineCauchyParameterCeiling p ≤ B) :
    p.χ * B ^ (p.m + p.γ) + reactionFun p.α B +
        (p.α - (p.m + p.γ - 1)) *
          (B - wholeLineCauchyParameterCeiling p) ≤ 0
```

The stronger sibling may retain the factor

```javascript
(p.α - (p.m + p.γ - 1)) *
  (wholeLineCauchyParameterCeiling p) ^ p.α
```

as its rate.

# 5. The explicit barrier and its derivative

Define additively:

```javascript
def wholeLineCauchyChiPosSupercriticalRate (p : CMParams) : ℝ :=
  p.α - (p.m + p.γ - 1)


def wholeLineCauchyChiPosSupercriticalCeiling
    (p : CMParams) (C t : ℝ) : ℝ :=
  wholeLineCauchyParameterCeiling p +
    (C - wholeLineCauchyParameterCeiling p) *
      Real.exp (-wholeLineCauchyChiPosSupercriticalRate p * t)
```

Under hsuper, the rate is positive. If C\ge M,

Combining the derivative identity with the supersolution inequality gives

This is exactly the scalar sign used in the positive part of the slab maximum argument.

The barrier gives the quantitative entry time into any prescribed M'>M. If C>M'>M, then

whenever

# 6. The restart identity survives unchanged

For any fixed base M and fixed rate \lambda,

Hence:

```javascript
theorem wholeLineCauchyChiPosSupercriticalCeiling_restart
    (p : CMParams) (C a s : ℝ) :
    wholeLineCauchyChiPosSupercriticalCeiling p
        (wholeLineCauchyChiPosSupercriticalCeiling p C a) s =
      wholeLineCauchyChiPosSupercriticalCeiling p C (a + s)
```

The proof is the same Real.exp_add calculation as

```javascript
wholeLineCauchyChiPosCeiling_restart
```

in the critical file. Therefore all of the following committed architecture mirrors mechanically:

```plain text
slab comparison
→ BUCMildFixedPoint Ico
→ endpoint Icc by time continuity
→ step ceiling
→ successor/restart identity
→ recursive datum/segment induction
→ canonical global pointwise estimate
→ UniformLimsupLe
```

The final target should be:

```javascript
theorem
    wholeLineCauchyGlobal_uniformLimsupLe_parameterCeiling_of_chi_pos_supercritical
    (p : CMParams) (hχ : 0 < p.χ)
    (hsuper : p.m + p.γ - 1 < p.α)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x) :
    UniformLimsupLe
      (wholeLineCauchyGlobalU p u₀)
      (wholeLineCauchyParameterCeiling p)
```

The WholeLineCauchyCeilingRegime witness is constructed internally as

```javascript
Or.inr ⟨hχ.le, Or.inl hsuper⟩
```

so it need not remain a theorem argument.

# 7. The slab-comparison changes are small

The critical slab theorem uses

```javascript
G r = Kreact * max (-r) 0 - p.α * max r 0
```

for the error w=u-B. In the supercritical mirror use

```javascript
G r = Kreact * max (-r) 0 - d * max r 0
```

where d=\alpha-q>0.

For w\ge0, u\ge B\ge M, and the new supersolution theorem gives

Therefore

For w<0, so u\le B, one needs a one-sided Lipschitz estimate. This is easier than it first appears. Write

For 0\le u\le B\le A,

The chemotactic power difference is favorable here because \chi\ge0 and u\le B. Therefore there is no need for a new q+1 Lipschitz constant. The existing

```javascript
effectiveReactionLip p A := 1 + (p.α + 1) * A ^ p.α
```

is already large enough. Only a new theorem proving the supercritical field's one-sided difference estimate is needed:

```javascript
theorem supercriticalEffectiveReaction_sub_le
    {p : CMParams}
    (hχ : 0 ≤ p.χ)
    {u B A : ℝ}
    (hu : 0 ≤ u) (huB : u ≤ B) (hBA : B ≤ A) (hA : 0 ≤ A) :
    (p.χ * u ^ (p.m + p.γ) + reactionFun p.α u) -
        (p.χ * B ^ (p.m + p.γ) + reactionFun p.α B) ≤
      effectiveReactionLip p A * (B - u)
```

Together with the supersolution inequality at B, this gives the negative-w branch of the same scalar maximum theorem.

# 8. What is and is not an obstruction

## No mathematical obstruction

The supercritical case is not harder than the critical case for the upper ceiling:

- no condition \chi<1 is needed;

- M is finite for every \chi>0 because d>0;

- the restart identity is exact;

- the nonlocal drift treatment is unchanged;

- the zeroth-order resolver term remains favorable;

- the same whole-line slab maximum theorem applies after changing the scalar function G.

## The base is not an exact equilibrium

Unlike M_\chi in the critical case, M_{\rm sup} is generally not the positive zero of F. It is a convenient explicit upper threshold obtained from

For \chi>0, M>1, and in fact

This is not a problem. A relaxing supersolution need only satisfy

not equality. As B(t)\downarrow M, its derivative tends to zero while the scalar field at M is still nonpositive.

## The critical rate must not be copied

The critical file uses rate \alpha. In the supercritical proof, copying that rate is unjustified. The directly certified parameter-only rate is

or, with the stronger bound retained,

The simple rate degenerates as the supercritical exponent approaches the critical exponent. That is expected: the proof changes character at d=0 and the critical Bernoulli normalization takes over.

## Lean-specific missing atom

The existing rpow_bernoulli assumes exponent at least 2. The supercritical gap needs the tangent inequality for every exponent at least 1, because d+1 can lie in (1,2). This generalized tangent theorem is the only genuinely new scalar-calculus lemma.

The rest is an additive clone/factorization of the already compiled critical chain.

# Recommended build order

Create ShenWork/Paper1/WholeLineCauchyChiPosSupercriticalLongTimeBound.lean and land:

1. rpow_tangent_at_one_of_one_le.

1. rpow_supercritical_gap and optionally rpow_supercritical_scaled_gap.

1. wholeLineCauchyParameterCeiling_pow_gap_of_supercritical.

1. wholeLineCauchyChiPosSupercriticalRate and the ceiling's zero/derivative/base/le/restart lemmas.

1. chiPosSupercriticalCeiling_supersolution.

1. supercriticalEffectiveReaction_sub_le.

1. The slab theorem, copied from wholeLineSlab_le_chiPosCeiling_of_positive_resolver_pde with the general field F and rate d.

1. Ico/Icc segment wrappers.

1. Step-ceiling successor identity and global segment induction.

1. The global pointwise estimate and UniformLimsupLe capstone.

No entropy argument, stronger exponential weight, assumed package, or new PDE regularity is required.