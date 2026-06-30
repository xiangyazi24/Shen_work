# Q2328 shen1 — positive strict exp bridge / hmκ routing audit

Repo audited: `xiangyazi24/Shen_work` on `main`.

Context assumed: local patch has added strict positive exponential superbarrier theorems and

```lean
positiveUpperBarrier_expStrictSuperAtContact_of_positive_region
```

which produces `PositiveUpperBarrierExpStrictContactResidual p c U` from the standard positive branch data plus

```lean
hmκ : p.m * kappa c ≤ 1
```

## 1. Can `hmκ` be derived from current positive branch packages?

No.  It is not derivable from the currently committed positive branch conditions.

The relevant committed package is:

```lean
structure PositivePaperLemma42ExactConditions
    (p : CMParams) (c κ κtilde M : ℝ) : Prop where
  hκ0 : 0 < κ
  hκ1 : κ < 1
  hgap : κ < κtilde
  hrange : κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1)
  hM : 1 ≤ M
  hc : c = κ + κ⁻¹
  hχ_nonneg : 0 ≤ p.χ
  hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p)
  hα_eq : p.α = p.m + p.γ - 1
```

The branch-cap constructor is:

```lean
theorem positivePaperLemma42ExactConditions_of_branchCap
    (p : CMParams) {c : ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c) :
    PositivePaperLemma42ExactConditions p c (kappa c)
      (positiveBranchTailCap p c) (MChi p)
```

It fills only the fields above.  There is no `hmκ` field.

The exact positive-condition projection close to this is:

```lean
theorem PositivePaperLemma42ExactConditions.kappaTilde_le_m_kappa_add_half
    {p : CMParams} {c κ κtilde M : ℝ}
    (h : PositivePaperLemma42ExactConditions p c κ κtilde M) :
    κtilde ≤ p.m * κ + 1 / 2
```

This is a bound on the **lower-barrier exponent** `κtilde`; it does not imply `p.m * κ ≤ 1`.

The repo contains the exact counterexample theorem:

```lean
theorem not_Lemma_4_1_positive_hypotheses_force_m_kappa_le_one :
    ¬ (∀ p : CMParams, 0 ≤ p.χ → p.χ < chiStar p →
      p.α = p.m + p.γ - 1 →
      ∀ κ : ℝ, 0 < κ → κ < 1 → p.m * κ ≤ 1)
```

Its witness is essentially `p.m = 3`, `p.α = 3`, `p.γ = 1`, `p.χ = 0`, and `κ = 1 / 2`, giving `p.m * κ = 3 / 2`.

This also shows why `positiveBranchTailCap` does not rescue the situation: for that witness,

```lean
positiveBranchTailCap p c = min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1)
```

can still be above `κ`, while `p.m * κ ≤ 1` is false.  The cap controls admissible `κtilde`, not `mκ`.

So `hmκ` must be carried explicitly wherever the strict positive exponential superbarrier is used.  Existing packages that do not carry it include:

```lean
Paper1PositiveLowerRawCapRouteAParamData
Paper1PositiveLowerRawCapRouteASmoothParamData
Paper1PositiveLowerRawCapRouteARemainingParamData
```

## 2. Minimal wrapper/data change to remove the strict exp residual when `hmκ` is available

The clean local theorem should live in `UpperBarrierContact.lean` and convert a **constant-branch-only** residual into the existing remaining residual by using the new strict exp theorem.

Add this small residual:

```lean
structure PositiveUpperBarrierConstLeftPlateauResidual
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop where
  no_const_left_plateau :
    ∀ x, MChi p < Real.exp (-(kappa c) * x) →
      (∀ y, y ≤ x → U y = MChi p) → False
```

Then add this bridge:

```lean
theorem PositiveUpperBarrierRemainingContactResidual.of_constLeftPlateau_positiveRegion
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c)
    (hmκ : p.m * kappa c ≤ 1)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hconst : PositiveUpperBarrierConstLeftPlateauResidual p c U) :
    PositiveUpperBarrierRemainingContactResidual p c U :=
  { no_const_left_plateau := hconst.no_const_left_plateau
    exp_strict_super_at_contact :=
      (positiveUpperBarrier_expStrictSuperAtContact_of_positive_region
        (p := p) (c := c) (U := U)
        hα hχ_nonneg hχ_small hc hmκ htrap).exp_strict_super_at_contact }
```

This removes the old strict exponential residual from the carried analytic package.  The remaining carried upper-contact atom is only the constant left-plateau obstruction.

For Route-A, add a new hmk-aware data package in `PositiveRawRouteAAssembly.lean` rather than changing the existing packages:

```lean
structure Paper1PositiveLowerRawCapRouteAHmkConstParamData : Prop where
  produce :
    ∀ p : CMParams, ∀ hα : p.α = p.m + p.γ - 1,
      ∀ hχ_nonneg : 0 ≤ p.χ,
        ∀ hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p),
          ∀ c : ℝ, ∀ hc : 2 < c,
            ∃ lam D Λ : ℝ,
              let hcond :
                  PositivePaperLemma42ExactConditions p c (kappa c)
                    (positiveBranchTailCap p c) (MChi p) :=
                positivePaperLemma42ExactConditions_of_branchCap
                  p hα hχ_nonneg hχ_small hc
              ∃ hpar :
                PaperLowerRawParabolicFloorRouteAParamCoreNoBar
                  p c lam (MChi p) (kappa c)
                  (positiveBranchTailCap p c) D Λ
                  hcond.hκ0.le (le_trans zero_le_one hcond.hM),
                  p.m * kappa c ≤ 1 ∧
                  1 ≤ D ∧
                  paperDMin p.χ (MChi p) (kappa c)
                    (positiveBranchTailCap p c) p.m p.γ c < D ∧
                  0 ≤ Λ ∧ Λ ≤ MChi p ∧
                  PaperLowerPinnedStationaryFlatFloor p c (kappa c)
                    (MChi p)
                    (lowerBarrierRaw (kappa c)
                      (positiveBranchTailCap p c) D)
                    (rotheSeqOfPaperFromPositiveCond p c lam (MChi p)
                      (kappa c) (positiveBranchTailCap p c) Λ hcond
                      (fun u =>
                        paperLowerRawRouteAParamProducer
                          (hpar.producer u))) ∧
                  StationaryStrongMaxPrinciple p c (kappa c) (MChi p) ∧
                  StationaryC2RegularityFromEquation p c (kappa c) (MChi p) ∧
                  (∀ U : ℝ → ℝ,
                    InLowerPinnedMonotoneTrap (kappa c) (MChi p)
                      (lowerBarrierRaw (kappa c)
                        (positiveBranchTailCap p c) D) U →
                    FrozenStationaryWaveProfile p c U →
                    PositiveUpperBarrierConstLeftPlateauResidual p c U)
```

Then the conversion to the existing remaining package is direct:

```lean
theorem paper1_routeARemainingParamData_of_routeAHmkConstParamData
    (hData : Paper1PositiveLowerRawCapRouteAHmkConstParamData) :
    Paper1PositiveLowerRawCapRouteARemainingParamData := by
  refine ⟨?_⟩
  intro p hα hχ_nonneg hχ_small c hc
  rcases hData.produce p hα hχ_nonneg hχ_small c hc with
    ⟨lam, D, Λ, hpar, hmκ, hD_ge_one, hD_gt, hΛ0, hΛM,
      hconv, hsmp, hreg, hconst⟩
  exact
    ⟨lam, D, Λ, hpar, hD_ge_one, hD_gt, hΛ0, hΛM, hconv, hsmp, hreg,
      fun U hpin hprofile =>
        PositiveUpperBarrierRemainingContactResidual.of_constLeftPlateau_positiveRegion
          (p := p) (c := c) (U := U)
          hα hχ_nonneg hχ_small hc hmκ hpin.bare
          (hconst U hpin hprofile)⟩
```

This keeps all downstream existing theorems usable, because you can reuse:

```lean
paper1_positiveRawSmoothContactData_of_routeARemainingParamData
paper1_positiveContactBranch_of_routeARemainingParamData
paper1_positiveStrictBarrierBranch_of_routeARemainingParamData
```

## 3. Theorem-level bridge only, or also a new Hmk ParamData?

Do both, but in two layers.

### Layer 1: theorem-level bridge in `UpperBarrierContact.lean`

This is mandatory and minimal.  It proves the mathematical fact:

```lean
constant-left-plateau residual + hmκ + positive branch scalar data + trap
  ⇒ PositiveUpperBarrierRemainingContactResidual
```

It is reusable outside Route-A and avoids mixing contact logic into the Route-A producer files.

### Layer 2: optional `...Hmk...ParamData` in `PositiveRawRouteAAssembly.lean`

Add this if you want Route-A users to stop carrying `exp_strict_super_at_contact` explicitly.  The new package should be an optional stronger package, not a replacement for the existing `Paper1PositiveLowerRawCapRouteARemainingParamData`.

Reason: `hmκ` is not derivable from the current branch assumptions.  If you mutate the existing package to require `hmκ`, you silently narrow the theorem.  A new name such as

```lean
Paper1PositiveLowerRawCapRouteAHmkConstParamData
```

makes the restriction visible and lets the old residual route remain available for regimes without `hmκ`.

### Payload style choice

Putting `hmκ` as a field inside the produced Sigma payload, as above, lets you convert into the existing remaining-contact package.  This is the easiest wiring route.

If instead you put `hmκ` as an extra input to `produce`, then the package is logically cleaner for an hmk-restricted theorem, but it will not convert to the old hmk-free `Paper1PositiveLowerRawCapRouteARemainingParamData`; you will need parallel `...Hmk...Branch` statement wrappers.  That is heavier and not necessary unless the final Paper1 statement itself is being split by `hmκ`.

## Recommended next step

Implement the two small bridges above.  Do not try to derive `hmκ` from `PositivePaperLemma42ExactConditions`, `positiveBranchTailCap`, or the current Route-A param data: the committed theorem

```lean
not_Lemma_4_1_positive_hypotheses_force_m_kappa_le_one
```

is the exact false-premise detector.
