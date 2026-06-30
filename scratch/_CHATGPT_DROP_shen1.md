# Q2308 shen1 — strict exponential superbarrier audit

Repo audited: `xiangyazi24/Shen_work` on `main`.

Scope: only the exponential field

```lean
exp_strict_super_at_contact :
  forall x, Real.exp (-(kappa c) * x) < MChi p ->
    U x = Real.exp (-(kappa c) * x) ->
      frozenWaveOperator p c U (upperBarrier (kappa c) (MChi p)) x < 0
```

## Conclusion

This field should not be a Route-A/fixed-point residual.  It should be proved by strengthening the committed positive exponential-region superbarrier from non-strict to strict.

The important caveat is that the repo’s positive superbarrier API needs the scalar side condition

```lean
hmk : p.m * kappa c <= 1
```

If that side condition is included, the strict inequality is true by the existing proof route.  If the assumption list is read without this side condition, the committed repo has no path even to the non-strict positive exponential superbarrier.

No lower pin, right-tail asymptotic, no-left-plateau, stationarity, or C2 regularity is needed for this field.  The contact equality is also unused; only the exponential-region hypothesis is needed.

## Existing theorems to reuse

The core formula is already committed:

```lean
theorem frozenWaveOperator_exp_full_eq
    (p : CMParams) {c kappa : Real} {u : Real -> Real}
    (hc : 2 <= c) (hk : kappa = kappa c)
    (hu : IsCUnifBdd u) (hu_nonneg : forall x, 0 <= u x) (x : Real)
    (hV_diff : DifferentiableAt Real (deriv (frozenElliptic p u)) x) :
    frozenWaveOperator p c u (expDecay kappa) x =
      -(expDecay kappa x) * (expDecay kappa x) ^ p.alpha
      - p.chi * (expDecay kappa x) ^ p.m *
        (-(p.m * kappa) * deriv (frozenElliptic p u) x +
          frozenElliptic p u x - (u x) ^ p.gamma)
```

I wrote this snippet with ASCII field names for readability; the actual file uses the Unicode Lean names `p.α`, `p.χ`, `p.γ`, and type `ℝ`.

The branch rewrite is committed as:

```lean
theorem frozenWaveOperator_upperBarrier_exp_region_eq
    (p : CMParams) {c kappa M : Real} {u : Real -> Real}
    {x : Real} (hx : expDecay kappa x < M) :
    frozenWaveOperator p c u (upperBarrier kappa M) x =
      frozenWaveOperator p c u (expDecay kappa) x
```

The current non-strict positive exp theorem is:

```lean
theorem frozenWaveOperator_exp_nonpos_of_chi_nonneg
    (p : CMParams) {c kappa M : Real} {u : Real -> Real}
    (hc : 2 <= c) (hk_eq : kappa = kappa c)
    (hchi_nonneg : 0 <= p.chi) (hchi_le_one : p.chi <= 1)
    (ha : p.alpha = p.m + p.gamma - 1)
    (hk_nonneg : 0 <= kappa) (hmk : p.m * kappa <= 1)
    (hu : InWaveTrapSet kappa M u) {x : Real}
    (hV_diff : DifferentiableAt Real (deriv (frozenElliptic p u)) x) :
    frozenWaveOperator p c u (expDecay kappa) x <= 0
```

And the current upper-barrier wrapper is:

```lean
theorem frozenWaveOperator_upperBarrier_exp_region_nonpos_of_chi_nonneg
    (p : CMParams) {c kappa M : Real} {u : Real -> Real}
    (hc : 2 <= c) (hk_eq : kappa = kappa c)
    (hchi_nonneg : 0 <= p.chi) (hchi : p.chi < chiStar p)
    (ha : p.alpha = p.m + p.gamma - 1)
    (hk_nonneg : 0 <= kappa) (hmk : p.m * kappa <= 1)
    {x : Real} (hx : expDecay kappa x < M)
    (hu : InWaveTrapSet kappa M u)
    (hV_diff : DifferentiableAt Real (deriv (frozenElliptic p u)) x) :
    frozenWaveOperator p c u (upperBarrier kappa M) x <= 0
```

The whole-line positive theorem `whole_line_super_barrier_pos` also explicitly requires `hmk : p.m * kappa <= 1`.

## Why strictness follows

Inside `frozenWaveOperator_exp_nonpos_of_chi_nonneg`, set `E := expDecay kappa x`.  The proof already derives

```lean
chemotactic_term <= p.chi * E ^ p.m * E ^ p.gamma
                 = p.chi * E ^ (p.alpha + 1)
```

using `p.alpha = p.m + p.gamma - 1`.

The current proof then uses only `p.chi <= 1` to conclude

```lean
p.chi * E ^ (p.alpha + 1) <= E * E ^ p.alpha.
```

For the positive branch, `p.chi < min (1 / 2) (chiStar p)`, hence `p.chi < 1`.  Also `0 < E ^ (p.alpha + 1)` because `E > 0`.  So the same line is strict:

```lean
p.chi * E ^ (p.alpha + 1) < E * E ^ p.alpha.
```

After rewriting with `frozenWaveOperator_exp_full_eq`, the residual is `< 0`.

The case `p.chi = 0` is not a problem: the chemotaxis term vanishes and the exponential logistic part is strictly negative.  The only boundary where the proof loses strictness is if one allows `p.chi = 1`, which is outside the positive branch.

## Minimal producer statement

Add a strict version of the exp theorem, not a Route-A theorem:

```lean
theorem frozenWaveOperator_exp_neg_of_chi_nonneg
    (p : CMParams) {c kappa M : Real} {u : Real -> Real}
    (hc : 2 <= c) (hk_eq : kappa = kappa c)
    (hchi_nonneg : 0 <= p.chi) (hchi_lt_one : p.chi < 1)
    (ha : p.alpha = p.m + p.gamma - 1)
    (hk_nonneg : 0 <= kappa) (hmk : p.m * kappa <= 1)
    (hu : InWaveTrapSet kappa M u) {x : Real}
    (hV_diff : DifferentiableAt Real (deriv (frozenElliptic p u)) x) :
    frozenWaveOperator p c u (expDecay kappa) x < 0
```

Then add the upper-barrier wrapper:

```lean
theorem frozenWaveOperator_upperBarrier_exp_region_neg_of_chi_nonneg
    (p : CMParams) {c kappa M : Real} {u : Real -> Real}
    (hc : 2 <= c) (hk_eq : kappa = kappa c)
    (hchi_nonneg : 0 <= p.chi) (hchi_lt_one : p.chi < 1)
    (ha : p.alpha = p.m + p.gamma - 1)
    (hk_nonneg : 0 <= kappa) (hmk : p.m * kappa <= 1)
    {x : Real} (hx : expDecay kappa x < M)
    (hu : InWaveTrapSet kappa M u)
    (hV_diff : DifferentiableAt Real (deriv (frozenElliptic p u)) x) :
    frozenWaveOperator p c u (upperBarrier kappa M) x < 0
```

Finally produce the residual field from ordinary positive branch data plus `hmk`:

```lean
theorem positiveUpperBarrier_expStrictSuperAtContact_of_positive_region
    {p : CMParams} {c : Real} {U : Real -> Real}
    (ha : p.alpha = p.m + p.gamma - 1)
    (hchi_nonneg : 0 <= p.chi)
    (hchi_small : p.chi < min (1 / 2 : Real) (chiStar p))
    (hc : 2 < c)
    (hmk : p.m * kappa c <= 1)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U) :
    PositiveUpperBarrierExpStrictContactResidual p c U
```

This wrapper uses `hx` to enter the exp region and supplies

```lean
frozenElliptic_deriv_differentiableAt p htrap.trap.cunif_bdd htrap.nonneg x
```

The contact equality argument is ignored.

## No existing strict producer

I found no committed theorem whose conclusion is the strict exp-region upper-superbarrier or the exact residual field.  Existing theorem names to reuse are:

```lean
frozenWaveOperator_exp_full_eq
frozenWaveOperator_exp_nonpos_of_chi_nonneg
frozenWaveOperator_upperBarrier_exp_region_eq
frozenWaveOperator_upperBarrier_exp_region_nonpos_of_chi_nonneg
whole_line_super_barrier_pos
frozenElliptic_deriv_differentiableAt
kappa_pos_of_two_lt
chiStar_le_one
```

## Route selection

Prove the strict exp-region theorem next.  Do not route this through raw lower pins, right-tail asymptotics, no-left-plateau, stationarity, or C2 regularity.  Those are unnecessary for this field.

The only producer-side issue is ensuring `hmk : p.m * kappa c <= 1` is available wherever the positive superbarrier is used.
