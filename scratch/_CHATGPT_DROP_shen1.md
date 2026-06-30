# Q2331 shen1 — design audit for positive upper-contact interface narrowing

Repo audited: `xiangyazi24/Shen_work` on `main`.

Question: whether the planned interface layer

* adds `PositiveUpperBarrierConstLeftPlateauResidual`,
* bridges it to `PositiveUpperBarrierRemainingContactResidual` using the strict exponential theorem plus `hmκ`, and
* adds `Paper1PositiveLowerRawCapRouteAHmkConstParamData`

is a genuine interface reduction or just a no-op/rename/residual-smuggling layer.

## Verdict

This is an honest net narrowing **provided the new package carries only the constant-left-plateau residual and carries `hmκ` explicitly**.

It is a genuine reduction on the `hmκ` subregime because the exponential residual is no longer supplied by Route-A data.  It is produced internally by

```lean
positiveUpperBarrier_expStrictSuperAtContact_of_positive_region
```

from positive scalar hypotheses, `hmκ : p.m * kappa c <= 1`, and trap membership.  The remaining carried contact atom is then only the constant-branch left-plateau obstruction.

It is still honest because prior audit showed `hmκ` is not derivable from the base positive branch assumptions.  So `hmκ` is a real extra frontier, not a hidden theorem.

## No-op / smuggling checks

The design is clean if all of these are true.

1. `PositiveUpperBarrierConstLeftPlateauResidual` has exactly one field:

```lean
structure PositiveUpperBarrierConstLeftPlateauResidual
    (p : CMParams) (c : Real) (U : Real -> Real) : Prop where
  no_const_left_plateau :
    forall x, MChi p < Real.exp (-(kappa c) * x) ->
      (forall y, y <= x -> U y = MChi p) -> False
```

It must not be an abbrev or wrapper around `PositiveUpperBarrierRemainingContactResidual`, `PositiveUpperBarrierExpStrictContactResidual`, or `PositiveUpperBarrierContactContradictions`.

2. The bridge has the shape:

```lean
theorem PositiveUpperBarrierRemainingContactResidual.of_constLeftPlateau_positiveRegion
    {p : CMParams} {c : Real} {U : Real -> Real}
    (ha : p.alpha = p.m + p.gamma - 1)
    (hchi_nonneg : 0 <= p.chi)
    (hchi_small : p.chi < min (1 / 2 : Real) (chiStar p))
    (hc : 2 < c)
    (hmk : p.m * kappa c <= 1)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hconst : PositiveUpperBarrierConstLeftPlateauResidual p c U) :
    PositiveUpperBarrierRemainingContactResidual p c U
```

and the `exp_strict_super_at_contact` field is filled only by

```lean
(positiveUpperBarrier_expStrictSuperAtContact_of_positive_region
  (p := p) (c := c) (U := U)
  ha hchi_nonneg hchi_small hc hmk htrap).exp_strict_super_at_contact
```

The bridge should not take any old exp-contact residual as an argument.

3. `Paper1PositiveLowerRawCapRouteAHmkConstParamData` should not carry any of these old residuals:

```lean
PositiveUpperBarrierRemainingContactResidual p c U
PositiveUpperBarrierExpStrictContactResidual p c U
PositiveUpperBarrierSmoothBranchNoContact p c U
PositiveUpperBarrierContactContradictions p c U
```

It should carry only

```lean
PositiveUpperBarrierConstLeftPlateauResidual p c U
```

for produced profiles.

4. The conversion

```lean
paper1_routeARemainingParamData_of_routeAHmkConstParamData
```

should construct the remaining residual by calling the bridge above, not by projecting a remaining residual from the new data package.

If those four checks hold, this is not a no-op rename.  It removes a strictly stronger field from the Route-A data and replaces it with a scalar frontier plus a smaller constant-branch residual.

## Vacuity check

The package is stronger because it covers only the `hmκ` subregime.  That is not a vacuity problem as long as the name advertises it, for example with `Hmk` in the name.

Prefer exposing `hmκ` as an explicit conjunct before the Route-A existential payload:

```lean
structure Paper1PositiveLowerRawCapRouteAHmkConstParamData : Prop where
  produce :
    forall p : CMParams, forall ha : p.alpha = p.m + p.gamma - 1,
      forall hchi_nonneg : 0 <= p.chi,
        forall hchi_small : p.chi < min (1 / 2 : Real) (chiStar p),
          forall c : Real, forall hc : 2 < c,
            p.m * kappa c <= 1 /\
            exists lam D L : Real,
              -- same Route-A payload as RemainingParamData, but carrying only
              -- PositiveUpperBarrierConstLeftPlateauResidual for produced U
              True
```

Putting `hmκ` inside the returned existential also works logically, but it is easier to miss in reviews.  A top-level conjunct makes the subregime visible.

Do not mutate the existing

```lean
Paper1PositiveLowerRawCapRouteARemainingParamData
```

into an `hmκ`-requiring package.  Keep the old residual path available for regimes where `hmκ` is unavailable, and add the `HmkConst` package as an optional stronger interface.

## Why `hmκ` must remain carried

The current positive branch condition package is:

```lean
structure PositivePaperLemma42ExactConditions
    (p : CMParams) (c k kt M : Real) : Prop where
  hκ0 : 0 < k
  hκ1 : k < 1
  hgap : k < kt
  hrange : kt <= min ((1 + p.alpha) * k) (min (p.m * k + 1 / 2) 1)
  hM : 1 <= M
  hc : c = k + k^-1
  hχ_nonneg : 0 <= p.chi
  hχ_small : p.chi < min (1 / 2 : Real) (chiStar p)
  hα_eq : p.alpha = p.m + p.gamma - 1
```

The branch-cap constructor

```lean
positivePaperLemma42ExactConditions_of_branchCap
```

fills these fields but does not prove or store `p.m * kappa c <= 1`.

The nearby projection

```lean
PositivePaperLemma42ExactConditions.kappaTilde_le_m_kappa_add_half
```

only proves a bound on `kappaTilde`, not on `p.m * kappa`.

The repo has the exact false-premise detector:

```lean
theorem not_Lemma_4_1_positive_hypotheses_force_m_kappa_le_one :
    not (forall p : CMParams, 0 <= p.chi -> p.chi < chiStar p ->
      p.alpha = p.m + p.gamma - 1 ->
      forall k : Real, 0 < k -> k < 1 -> p.m * k <= 1)
```

So an interface that “derives” `hmκ` from base positive data would be unsound.  Carrying `hmκ` explicitly is the right frontier.

## Minimal conversion sketch

The conversion from the new hmk-const package to the existing remaining package should look like this, modulo exact local binder names:

```lean
theorem paper1_routeARemainingParamData_of_routeAHmkConstParamData
    (hData : Paper1PositiveLowerRawCapRouteAHmkConstParamData) :
    Paper1PositiveLowerRawCapRouteARemainingParamData := by
  refine ⟨?_⟩
  intro p ha hchi_nonneg hchi_small c hc
  rcases hData.produce p ha hchi_nonneg hchi_small c hc with
    ⟨hmk, lam, D, L, hpar, hD_ge_one, hD_gt, hL0, hLM,
      hconv, hsmp, hreg, hconst⟩
  exact
    ⟨lam, D, L, hpar, hD_ge_one, hD_gt, hL0, hLM, hconv, hsmp, hreg,
      fun U hpin hprofile =>
        PositiveUpperBarrierRemainingContactResidual.of_constLeftPlateau_positiveRegion
          (p := p) (c := c) (U := U)
          ha hchi_nonneg hchi_small hc hmk hpin.bare
          (hconst U hpin hprofile)⟩
```

This is the critical anti-smuggling line: the returned `PositiveUpperBarrierRemainingContactResidual` is built from `hconst` plus the strict exp theorem, not carried directly.

Then reuse existing downstream wrappers:

```lean
paper1_positiveRawSmoothContactData_of_routeARemainingParamData
paper1_positiveContactBranch_of_routeARemainingParamData
paper1_positiveStrictBarrierBranch_of_routeARemainingParamData
```

Optional convenience wrappers can be added, but they should be one-line calls through `paper1_routeARemainingParamData_of_routeAHmkConstParamData`.

## Design tradeoff

Add both layers:

1. A theorem-level bridge in `UpperBarrierContact.lean`.
   This is the reusable mathematical reduction and should exist even if Route-A is not used.

2. An optional hmk-aware Route-A data package in `PositiveRawRouteAAssembly.lean`.
   This prevents every caller from manually building the remaining residual while keeping the `hmκ` restriction explicit.

Do not replace the existing remaining-residual package.  The old package remains the fully general residual route.  The new package is the stricter but cleaner hmk subroute.

## Clean-audit checklist

Inspect these exact signatures with `#check`:

```lean
#check PositiveUpperBarrierConstLeftPlateauResidual
#check PositiveUpperBarrierRemainingContactResidual.of_constLeftPlateau_positiveRegion
#check positiveUpperBarrier_expStrictSuperAtContact_of_positive_region
#check Paper1PositiveLowerRawCapRouteAHmkConstParamData
#check paper1_routeARemainingParamData_of_routeAHmkConstParamData
#check paper1_positiveRawSmoothContactData_of_routeARemainingParamData
#check paper1_positiveContactBranch_of_routeARemainingParamData
#check paper1_positiveStrictBarrierBranch_of_routeARemainingParamData
```

Run `#print axioms` on the proof-bearing bridges before calling the design clean:

```lean
#print axioms frozenWaveOperator_exp_neg_of_chi_nonneg
#print axioms frozenWaveOperator_upperBarrier_exp_region_neg_of_chi_nonneg
#print axioms positiveUpperBarrier_expStrictSuperAtContact_of_positive_region
#print axioms PositiveUpperBarrierRemainingContactResidual.of_constLeftPlateau_positiveRegion
#print axioms paper1_routeARemainingParamData_of_routeAHmkConstParamData
#print axioms paper1_positiveRawSmoothContactData_of_routeARemainingParamData
#print axioms paper1_positiveContactBranch_of_routeARemainingParamData
#print axioms paper1_positiveStrictBarrierBranch_of_routeARemainingParamData
```

Also inspect the field projection:

```lean
#check Paper1PositiveLowerRawCapRouteAHmkConstParamData.produce
```

The projection should reveal only `hmκ` and the constant-left-plateau residual as new contact-related obligations.  If it reveals `PositiveUpperBarrierRemainingContactResidual`, `PositiveUpperBarrierExpStrictContactResidual`, `PositiveUpperBarrierSmoothBranchNoContact`, or `PositiveUpperBarrierContactContradictions`, then the package is smuggling the old residual and should be rejected.

## Final assessment

The proposed plan is a genuine interface narrowing on the `hmκ` subregime.  It removes the strict exponential contact residual from Route-A data and replaces it with a theorem-level proof obligation already solved by the strict positive exponential superbarrier bridge.  The remaining carried data is smaller: `hmκ` plus the constant left-plateau residual.  Since `hmκ` is explicitly not derivable from the base positive branch hypotheses, this is an honest stronger subroute, not a vacuous proof of the full route.
