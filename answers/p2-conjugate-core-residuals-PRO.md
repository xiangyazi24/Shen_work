# Q249: Paper 2 conjugate B-form core residuals

## Executive verdict

The two residual fields in `ConjugateMildExistenceCore` should be closed by two local bricks.

* `hB_int` is the second-variable-kernel analogue of the already proved gradient-Duhamel time-integrability atom.  Do not route through the old `∂x S(t-s)` Duhamel operator.  Prove measurability of the B-form parameter integral and dominate it by the same integrable singularity `(t-s)^(-1/2)`.
* `hmapsTo_pos` is a one-step floor argument for the Picard map.  It should not be proved from `bform_strictPos_closed`, because that theorem is downstream of `ConjugateMildExistenceData`.  The field itself must show that every ball element `w` is mapped to a positive function by `Φᴮ`.

After these are supplied, the existing bridge `ConjugateMildExistenceCore.toData` gives `ConjugateMildExistenceData`; then the current B-form classical/frontier route closes the local theorem and hence the Paper 2 chain.

## 1. `hB_int`: interval-integrability of the B-form chemotaxis leg

The target integrand is

```lean
fun s : ℝ =>
  intervalConjugateKernelOperator (t - s)
    (chemFluxLifted p (w s)) x.1
```

where

```lean
intervalConjugateKernelOperator τ Q x
  = -∫ y, deriv (fun y' => intervalNeumannFullKernel τ x y') y * Q y
      ∂ intervalMeasure 1
```

The minimal abstract lemma should be source-level, not trajectory-level:

```lean
theorem conjugateDuhamel_intervalIntegrable_of_measurable_bound
    {t Cq : ℝ} (ht : 0 < t) (hCq : 0 ≤ Cq)
    {q : ℝ → ℝ → ℝ} {x : ℝ}
    (hB_meas : AEStronglyMeasurable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s) (q s) x)
      (volume.restrict (Set.Icc 0 t)))
    (hq_int : ∀ s, 0 ≤ s → s < t → Integrable (q s) (intervalMeasure 1))
    (hq_sup : ∀ s, 0 ≤ s → s < t → ∀ y, |q s y| ≤ Cq) :
    IntervalIntegrable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s) (q s) x)
      volume 0 t
```

The proof is a direct domination proof.  For `0 ≤ s < t`, set `τ = t-s`; then `0 < τ`, and the existing B-kernel bound gives

```lean
|intervalConjugateKernelOperator (t - s) (q s) x|
  ≤ heatGradientLinftyLinftyConstant * (t-s)^(-(1/2) : ℝ) * Cq.
```

The dominator

```lean
fun s => heatGradientLinftyLinftyConstant * Cq * (t-s)^(-(1/2) : ℝ)
```

is interval-integrable on `(0,t)` by `intervalIntegrable_sub_rpow_neg_half`.  The endpoint `s=t` is a singleton and is removed by the standard `ae_restrict_iff' measurableSet_Icc` plus `volume_singleton` step.

The measurability premise should be supplied by a separate parameter-integral lemma:

```lean
theorem intervalConjugateKernelOperator_lag_aestronglyMeasurable
    {t x : ℝ} {q : ℝ → ℝ → ℝ}
    (hq : AEStronglyMeasurable
      (fun z : ℝ × ℝ => q z.1 z.2)
      (volume.prod (intervalMeasure 1))) :
    AEStronglyMeasurable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s) (q s) x)
      (volume.restrict (Set.Icc 0 t))
```

Its proof has four steps.

1. Prove joint measurability of the lagged second-variable kernel derivative:

```lean
theorem measurable_deriv_snd_intervalNeumannFullKernel_lag (t x : ℝ) :
  Measurable (fun z : ℝ × ℝ =>
    deriv (fun y' => intervalNeumannFullKernel (t - z.1) x y') z.2)
```

Use the existing formula from `hasDerivAt_intervalNeumannFullKernel_snd`: the derivative is the difference of two `ℤ`-tsums of heat-kernel derivatives.  Each summand is measurable by `fun_prop`; the `tsum` is measurable by the same measurable-tsum infrastructure already used for the full Neumann kernel.

2. Multiply by the source:

```lean
(fun z : ℝ × ℝ =>
  deriv (fun y' => intervalNeumannFullKernel (t - z.1) x y') z.2 * q z.1 z.2)
```

is `AEStronglyMeasurable` on `volume.prod (intervalMeasure 1)`.

3. Apply the parameterized Bochner-integral measurability lemma, in the same style as the existing semigroup parameter measurability lemmas:

```lean
AEStronglyMeasurable (fun s =>
  ∫ y, deriv (fun y' => intervalNeumannFullKernel (t - s) x y') y * q s y
    ∂ intervalMeasure 1) volume
```

4. Rewrite by the definition of `intervalConjugateKernelOperator` and restrict to `Set.Icc 0 t`.

For a trajectory, instantiate `q` as

```lean
q s y = chemFluxLifted p (w s) y.
```

The trajectory-level theorem should be:

```lean
theorem conjugateChemFlux_duhamel_intervalIntegrable_of_ball
    (p : CM2Params) {T M CQ : ℝ}
    (hM : 0 ≤ M) (hCQ : 0 ≤ CQ)
    {w : ℝ → intervalDomainPoint → ℝ}
    (hbound : ∀ τ, 0 < τ → τ ≤ T → ∀ x, |w τ x| ≤ M)
    (hnonneg : ∀ τ, 0 < τ → τ ≤ T → ∀ x, 0 ≤ w τ x)
    (hcont : HasContinuousSlices T w)
    (hmeas : HasJointMeasurability w)
    (hQbound : ∀ τ, 0 < τ → τ ≤ T → ∀ y,
      |chemFluxLifted p (w τ) y| ≤ CQ)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : intervalDomainPoint) :
    IntervalIntegrable
      (fun s => intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p (w s)) x.1)
      volume 0 t
```

For each `0 < s ≤ T`, spatial integrability follows from the already available continuous-slice flux theorem:

```lean
chemFluxLifted_integrable_of_continuous p
  (hbound s hs hsT) hM (hcont s hs hsT) (hnonneg s hs hsT)
```

The uniform `CQ` must come from the ball-level resolver estimates, not from a per-slice compactness existential.  If the public theorem does not already exist, extract it as:

```lean
theorem chemFluxLifted_sup_bound_of_ball
    (p : CM2Params) {M CQ : ℝ} (hM : 0 ≤ M)
    {u : intervalDomainPoint → ℝ}
    (hu_cont : Continuous u)
    (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_bound : ∀ x, |u x| ≤ M) :
    ∀ y, |chemFluxLifted p u y| ≤ CQ
```

with `CQ` chosen from the existing resolver value/gradient constants.

For the contraction fields, add the same theorem for

```lean
fun y => chemFluxLifted p (u s) y - chemFluxLifted p (w s) y
```

with bound `CQ * d`.  This fills `hflux_duhamel_integrable_left`, `hflux_duhamel_integrable_right`, and `hflux_duhamel_diff_integrable`.

## 2. `hmapsTo_pos`: one-step strict positivity of the Picard map

The field has shape

```lean
hmapsTo_pos : ∀ w,
  (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
  (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
  HasContinuousSlices T w →
  ∀ t, 0 < t → t ≤ T → ∀ x,
    0 < intervalConjugateDuhamelMap p u₀ w t x
```

The reusable one-step lower-bound lemma is:

```lean
theorem intervalConjugateDuhamelMap_ge_half_floor_of_banked
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T CQ CL : ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hCQ : 0 ≤ CQ) (hCL : 0 ≤ CL)
    (hsmall :
      |p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * CQ)
        + T * CL ≤ paperPositiveFloor hu₀ / 2)
    {w : ℝ → intervalDomainPoint → ℝ}
    (hQ_int : ∀ s, Integrable (chemFluxLifted p (w s)) (intervalMeasure 1))
    (hQ_bound : ∀ s y, |chemFluxLifted p (w s) y| ≤ CQ)
    (hL_bound : ∀ s y, |logisticLifted p (w s) y| ≤ CL)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : intervalDomainPoint)
    (hB_int : IntervalIntegrable
      (fun s => intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p (w s)) x.1) volume 0 t)
    (hL_int : IntervalIntegrable
      (fun s => intervalFullSemigroupOperator (t - s)
        (logisticLifted p (w s)) x.1) volume 0 t) :
    paperPositiveFloor hu₀ / 2 ≤ intervalConjugateDuhamelMap p u₀ w t x
```

The proof is the existing Picard-iterate proof with `w` replacing the iterate.

Let

```lean
S = intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
B = ∫ s in (0:ℝ)..t,
      intervalConjugateKernelOperator (t-s) (chemFluxLifted p (w s)) x.1
R = ∫ s in (0:ℝ)..t,
      intervalFullSemigroupOperator (t-s) (logisticLifted p (w s)) x.1
```

Then:

```lean
paperPositiveFloor hu₀ ≤ S
```

by `intervalFullSemigroupOperator_ge_paperPositiveFloor`.  Also

```lean
|B| ≤ heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * CQ
```

by `conjugateDuhamel_sup_bound` or the localized version, and

```lean
|R| ≤ T * CL
```

by `valueDuhamel_sup_bound`.  Therefore

```lean
Φᴮ(w) = S + (-p.χ₀) * B + R
      ≥ floor - |p.χ₀| * Cg * 2√T * CQ - T * CL
      ≥ floor / 2.
```

The strict version is just:

```lean
theorem intervalConjugateDuhamelMap_pos_of_banked_floor ... :
    0 < intervalConjugateDuhamelMap p u₀ w t x := by
  have hhalf := intervalConjugateDuhamelMap_ge_half_floor_of_banked ...
  have hhalf_pos : 0 < paperPositiveFloor hu₀ / 2 := by
    linarith [paperPositiveFloor_pos hu₀]
  exact lt_of_lt_of_le hhalf_pos hhalf
```

Inside the `ConjugateMildExistenceCore` constructor, `CL` is the ball-level logistic bound, e.g.

```lean
CL = M * (p.a + p.b * M ^ p.α)
```

or the already chosen local constant.  `CQ` is the ball-level chemotaxis-flux bound.  The smallness condition needed for `hmapsTo_pos` is

```lean
|p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * CQ)
  + T * CL ≤ paperPositiveFloor huPaper / 2.
```

This is independent of the ball maps-to budget

```lean
M₀ + |p.χ₀| * Cg * 2√T * CQ + T * CL ≤ M.
```

In practice choose `T` small enough to satisfy both.

## 3. Relationship to `bform_strictPos_closed`

Use `bform_strictPos_closed` after the core is turned into data.  It proves strict positivity of the Picard limit using the floor, the inf-threshold smallness package, and the B-form linear-strip comparison.  It is not the right tool for the `hmapsTo_pos` field because that field is needed before `DB : ConjugateMildExistenceData` exists.

The correct flow is:

```text
single-step floor lemma
  -> hmapsTo_pos
  -> ConjugateMildExistenceCore
  -> ConjugateMildExistenceData
  -> Picard limit
  -> bform_strictPos_closed for final closed-domain positivity
  -> IsPaper2ClassicalSolution
  -> paper2_theorem_1_1
```

## 4. Minimal implementation order

1. Add `measurable_deriv_snd_intervalNeumannFullKernel_lag`.
2. Add `intervalConjugateKernelOperator_lag_aestronglyMeasurable`.
3. Add `conjugateDuhamel_intervalIntegrable_of_measurable_bound`.
4. Instantiate it for `chemFluxLifted p (w s)` and for the flux difference.
5. Add `intervalConjugateDuhamelMap_ge_half_floor_of_banked` and its strict-positive corollary.
6. Fill the core fields:

```lean
hflux_duhamel_integrable_left  := conjugateChemFlux_duhamel_intervalIntegrable_of_ball ...
hflux_duhamel_integrable_right := conjugateChemFlux_duhamel_intervalIntegrable_of_ball ...
hflux_duhamel_diff_integrable  := conjugateChemFlux_duhamel_diff_intervalIntegrable_of_ball ...
hmapsTo_pos                   := intervalConjugateDuhamelMap_pos_of_banked_floor ...
```

That is the shortest Lean route.  The only genuinely delicate Lean sub-brick is joint measurability of the lagged `∂y` kernel integral; the analytic estimate itself is already present in the B-form kernel files.