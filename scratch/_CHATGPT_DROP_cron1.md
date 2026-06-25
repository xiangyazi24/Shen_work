# ChatGPT git-drop (cron1)

## Q352 — `hregularize` audit: canonical χ₀=0 chain vs. EWA/cosine regularity

### Executive verdict

`regularityBootstrap_of_gradientMildSolutionData` **does not** take an order-box contraction fixed point and prove `RegularityBootstrap` from scratch.

It takes:

```lean
D : GradientMildSolutionData p u0
hInitialApproach : ...
hclassical : IsPaper2ClassicalSolution intervalDomain p D.T D.u
  (mildChemicalConcentration p D.u)
```

and then repackages the already-classical solution into `RegularityBootstrap`.

So it is **not** the missing `hregularize` needed by

```lean
exactLocalClassicalSolution_of_coupledDuhamel_resolver_estimates
```

because that `hregularize` must upgrade an arbitrary coupled Duhamel fixed point, merely known to be bounded and to satisfy the mild identity, into `RegularityBootstrap`.

For χ₀=0, the repo does **not** get `hregularize` from the bare order-box contraction alone.  It uses the canonical Picard/restart chain plus an explicit residual ledger `LimitRegularityInputs`.  That ledger carries half-step restart/cosine/source-time-C¹/frontier data.  This is canonical in the sense “not EWA reduced core,” but it is **not** free of cosine/source-regularity inputs.

Thus the answer to the key question is:

```text
No: hregularize cannot currently be filled from the canonical contraction fixed point alone.
Yes: χ₀=0 uses the canonical Picard/restart chain, but that chain still needs additional regularity data, including cosine/restart/source-time-C¹ fields, carried in LimitRegularityInputs.
```

---

## 1. What `exactLocalClassicalSolution_of_coupledDuhamel_resolver_estimates` needs

The theorem in `IntervalDomainThm11ChiNegResidual.lean` has the regularization hypothesis:

```lean
(hregularize :
  ∀ u v : ℝ → intervalDomainPoint → ℝ,
    intervalTrajectoryBoundedOn T M u →
    (∀ t x, 0 ≤ t → t ≤ T →
      u t x = intervalCoupledDuhamelOperator p R u0 u t x) →
    (∀ t, v t = R (u t)) →
      RegularityBootstrap p T u0 u)
```

It first constructs the fixed point:

```lean
obtain ⟨u, vR, hu_ball, hfp, hvR⟩ :=
  intervalCoupledDuhamel_fixed_point_exists_on_closed_ball
    p R u0 hA hM hT hAT hM hmap hcontr hbase
```

then applies:

```lean
obtain ⟨v, hpos, hvnn, hpde_u, hpde_v, hbc, hclassreg, htrace⟩ :=
  hregularize u vR hu_ball hfp hvR
```

and finally builds the classical solution:

```lean
IsPaper2ClassicalSolution.of_components hT hclassreg hpos hvnn hpde_u hpde_v hbc
```

So `hregularize` is not a light wrapper.  It is the full regularity/PDE bootstrap from a coupled mild fixed point to the paper's classical solution package.

---

## 2. What `regularityBootstrap_of_gradientMildSolutionData` actually takes

The theorem is:

```lean
theorem regularityBootstrap_of_gradientMildSolutionData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u0)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (hclassical : IsPaper2ClassicalSolution intervalDomain p D.T D.u
      (mildChemicalConcentration p D.u)) :
    RegularityBootstrap p D.T u0 D.u
```

Inside the proof it extracts closed spatial `C²` and one-sided Neumann inputs from

```lean
hclassical.regularity
```

and uses `hclassical` again for:

```lean
mildSolution_parabolicPDE p D hclassical
mildSolution_classicalRegularity p D hclassical
```

Therefore this theorem is **downstream** of an `IsPaper2ClassicalSolution`, not an upstream theorem that proves one.

It is useful as a repackaging bridge:

```text
GradientMildSolutionData + initial approach + already-classical solution
  → RegularityBootstrap.
```

It is not the requested analytic theorem:

```text
bounded mild fixed point + Duhamel identity + resolver identity
  → RegularityBootstrap.
```

---

## 3. The restart/cosine variants still need classical/core data

The repo has variants that reduce the amount of full classical data required, for example:

```lean
regularityBootstrap_of_gradientMildSolutionData_of_halfStepRestartData_and_coreData
```

with type shape:

```lean
theorem regularityBootstrap_of_gradientMildSolutionData_of_halfStepRestartData_and_coreData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u0)
    (R : GradientMildHalfStepRestartData D)
    (hInitialApproach : ...)
    (C : GradientMildClassicalCoreData p D) :
    RegularityBootstrap p D.T u0 D.u
```

But this still needs:

```lean
R : GradientMildHalfStepRestartData D
C : GradientMildClassicalCoreData p D
```

and the core contains:

```lean
hpde_u : ...
hclassicalRegularity : intervalDomainClassicalRegularity D.T D.u
  (mildChemicalConcentration p D.u)
```

There is also a frontier-core version:

```lean
regularityBootstrap_of_gradientMildSolutionData_of_halfStepRestartData_and_frontierCore
```

with:

```lean
R : GradientMildHalfStepRestartData D
C : GradientMildClassicalFrontierCoreData p D
```

but `GradientMildClassicalFrontierCoreData` still carries:

```lean
hpde_u : ...
hregularityFrontier : GradientMildClassicalRegularityFrontierData p D
```

So these variants are genuine improvements over requiring a full classical solution, but they still need substantial regularity/PDE input.  They do not derive that input from the order-box fixed point alone.

---

## 4. How χ₀=0 produces `hlocal`

The χ₀=0 local route is in `IntervalDomainMildLocalChi0.lean`.

The file-level comments describe the chain:

1. `D` is built from cone existence:

```lean
coneGradientMildSolutionData_exists
```

2. `R : GradientMildHalfStepRestartData D` is built from limit regularity inputs: K2 spatial-slice families, K1 source-coefficient time-`C¹` families, datum continuity / `ℓ¹` coefficient data, and the mild fixed-point equation.

3. `HasRestartCosineRepresentations D.T D.u` follows from `R`.

4. The frontier core is assembled from `Hrestart`, resolver spectral data `Hv`, and residual fields `Hu`, `HsupNorm`, `Hvpos`, plus carried `hpde_u`.

This is encoded in the ledger:

```lean
structure LimitRegularityInputs
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (D : GradientMildSolutionData p u₀) where
  ...
```

The ledger contains, among many fields:

```lean
hu₀_cont : Continuous u₀
M₀ : ℝ
hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀
hsrc0 : DuhamelSourceBddOn ... D.T
bc : ℝ → ℕ → ℝ
hbsum : ∀ σ, 0 < σ → σ < D.T →
  Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|)
hagree : ∀ σ, 0 < σ → σ < D.T →
  Set.EqOn (intervalDomainLift (D.u σ))
    (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc 0 1)
adott : ℝ → ℕ → ℝ
hderivt : ... HasDerivAt ...
hadotcontt : ...
hMdott : ...
hpde_u : ...
Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u
Hvsrc : ... DuhamelSourceTimeC1 ... clamped resolver source witness ...
Hvpos : ...
```

So the χ₀=0 chain is canonical Picard/restart, not EWA reduced core, but it **does** rely on coefficient/restart/source-regularity data.  It is not just the output of a `C([0,T],C)` contraction.

The top-level χ₀=0 local-data theorem is:

```lean
theorem hMildLocal_chi0_zero_of_inputs
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (hα_ge : 1 ≤ p.α)
    (H : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        D.u = ShenWork.IntervalMildPicard.picardLimit p u₀ D.T →
        LimitRegularityInputs p u₀ D) :
    RestartLocalWiring.IntervalDomainGradientMildHalfStepRestartFrontierCoreLocalData p
```

It builds `D` by:

```lean
coneGradientMildSolutionData_exists p hχ0 hM hα_ge
```

then obtains the ledger:

```lean
have I : LimitRegularityInputs p u₀ D := H u₀ hu₀ D hDu'
```

and returns:

```lean
⟨D, restartData_of_inputs hχ0 I, initialApproach, frontierCore_of_inputs hχ0 I⟩
```

This is then converted to `hlocal` by:

```lean
RestartLocalWiring.localExistence_of_gradientMildHalfStepRestartFrontierCoreLocalData
```

which destructures:

```lean
⟨D, R, hInitialApproach, hCore⟩
```

and calls:

```lean
localExistence_of_gradientMildSolutionData_of_halfStepRestartData_and_frontierCore
```

---

## 5. Does χ₀=0 use the EWA/source-regularity chain?

It does **not** use the EWA reduced core path.

The imports and structure of `IntervalDomainMildLocalChi0.lean` are the canonical Picard/restart stack:

```lean
import ShenWork.Paper2.IntervalPicardLimitSourceData
import ShenWork.Paper2.IntervalPicardLimitRestartWeak
import ShenWork.Paper2.IntervalRegularityFrontierWiring
import ShenWork.Paper2.IntervalDomainConeQuantBridge
import ShenWork.Paper2.IntervalDomainConstExtendAdapter
import ShenWork.Paper2.IntervalDomainRestartPackaging
```

This is separate from the `ShenWork/Wiener/EWA` reduced-core track.

But it is still spectral/restart based.  The ledger explicitly contains cosine coefficients, summability, restart cosine representations, source time-`C¹`, and clamped resolver source `DuhamelSourceTimeC1` witnesses.  So if by “EWA/cosine-summable data” you mean “any Fourier/cosine/restart regularity,” then χ₀=0 still needs such data.  It just gets them from the canonical Picard-limit/restart ledger, not from `EWA`.

---

## 6. Can `hregularize` be filled from the canonical order-box fixed point alone?

No, not with the current repo theorems.

The bare canonical order-box fixed point supplies something like:

```lean
intervalTrajectoryBoundedOn T M u
∀ t x, 0 ≤ t → t ≤ T →
  u t x = intervalCoupledDuhamelOperator p R u0 u t x
∀ t, v t = R (u t)
```

The required `hregularize` must turn those into:

```lean
RegularityBootstrap p T u0 u
```

which includes positivity, chemical nonnegativity, PDE identities, Neumann boundary data, classical regularity, and initial trace.  The existing canonical theorems do not derive all of that from the fixed-point identity alone.

The χ₀=0 chain fills the gap by carrying and wiring:

```lean
GradientMildHalfStepRestartData D
GradientMildClassicalFrontierCoreData p D
```

or a stronger `GradientMildClassicalCoreData p D`.  Those packages include the missing regularity/PDE source data.

Therefore a direct `hregularize` for `exactLocalClassicalSolution_of_coupledDuhamel_resolver_estimates` would be a new theorem.  Its honest statement would need either:

```lean
-- strong canonical regularity inputs
GradientMildHalfStepRestartData / H²-source data / source-time-C¹ / frontier core
```

or a genuine PDE theorem:

```lean
bounded coupled Duhamel fixed point
  → parabolic smoothing + source regularity + resolver regularity
  → RegularityBootstrap.
```

That theorem is not currently present.

---

## Final answer

* `regularityBootstrap_of_gradientMildSolutionData` is **not** the desired regularization theorem from a mild fixed point.  It repackages an already-classical solution, or via variants, a solution plus separate core/frontier regularity data.
* The χ₀=0 local route uses the **canonical Picard/restart chain**, not the EWA reduced core.
* However, the canonical χ₀=0 route still depends on a large `LimitRegularityInputs` ledger containing cosine/restart/source-time-C¹/resolver-frontier data.
* Therefore, `hregularize` for the χ₀<0 coupled-Duhamel fixed point cannot currently be filled from the canonical order-box contraction alone.  It needs additional regularity/frontier data, or a new parabolic regularization theorem.
