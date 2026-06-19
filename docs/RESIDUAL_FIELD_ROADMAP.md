I found the exact residual record. One correction: the current `WholeLineWaveExistenceConsolidatedResidualData` has **14 fields** as written, not 11: the scalar fields plus the flow/limit/profile/left-tail fields. The record itself lists them from `kappa_lt_kappat` through `translate_limit_identification`. fileciteturn60file0L29-L92

## Executive verdict

**Directly wire now, assuming the recently closed lemmas expose the expected statement shapes:**

`kappa_lt_kappat`, `D_ge_one`, `paper3_chi_nonpos`, `spatial_antitone`, `auxiliaryDuhamel_continuity`, `finite_time_slice_continuity`, `longTime_time_antitone`, `longTime_evolution_eq`, and `translate_limit_identification`.

**Still genuine analytic remainder:**

`longTime_derivative_convergence`, `longTime_image_derivative_bridge`, `fixedPoint_profile_regularity`, and `fixedPoint_flat_left`.

**Ambiguous / depends on exact theorem already closed:**

`longTime_uniform_tail`. In this repo that name means **uniform convergence of finite-time slices to the long-time profile on compact spatial windows**, not right-tail spatial decay. If your new continuity package proves exactly `LongTimeMapUniformTail`, wire it. If it only proves compactness/continuity of the map, this field still needs a Dini/uniform-in-parameter convergence lemma.

---

## Field-by-field audit

| Residual field | Verdict | Wire from / minimal missing lemma |
|---|---:|---|
| `kappa_lt_kappat` | **Discharge now** | Scalar side condition from the choice of \(\tilde\kappa\). Add only a tiny arithmetic wrapper if not already exposed: `waveExponent_lt_kappat_of_speed_choices`. |
| `D_ge_one` | **Discharge now** | Scalar side condition from the choice of large \(D\). Add wrapper `one_le_D_of_D_ge_threshold`. |
| `paper3_chi_nonpos` | **Discharge now** | From the paper-parameter bridge identifying the nonpositive sensitivity branch. If `p3.χ₀` is definitionally/lemma-equal to `p.χ`, this is from `hχ : p.χ ≤ 0`; otherwise add `paper3_chi_nonpos_of_paper1_chi_nonpos`. |
| `spatial_antitone` | **Discharge now, if the closed orbit monotonicity theorem returns the witness record** | The residual wants `WholeLineSpatialAntitoneWitness`, not merely `∀ t, Antitone`. The repo already has the witness-shaped orbit data: `WholeLineOrbitPropertiesData.spatial` returns exactly that witness for each trapped `U`. fileciteturn79file0L208-L218 If your closed theorem only proves antitonicity, add a wrapper producing the witness from the differentiated weak-comparison data. |
| `auxiliaryDuhamel_continuity` | **Discharge now** | From the newly closed continuity of the auxiliary Duhamel/mild map. The field is exactly local-uniform continuity of `residualAuxDuhamelOnTrap p c Haux.raw_w Haux.raw_wx t`. fileciteturn60file0L40-L44 The repo already has the downstream wrapper `residualAuxReactionDuhamel_continuity`, which consumes this local-uniform continuity field. fileciteturn64file0L111-L126 |
| `finite_time_slice_continuity` | **Discharge now with a small wrapper** | From `AuxiliaryMildSolutionOn` plus spatial continuity of the mild map, and for negative time from the upper-barrier extension. `AuxiliaryMildSolutionOn` stores the mild equality and barrier trap on `[0,T]`. fileciteturn84file0L181-L188 Minimal wrapper: `wholeLineForwardOrbitExtension_continuous_of_auxiliaryMildSolutionOn`. |
| `longTime_uniform_tail` | **Only discharge now if your closed long-time package proves exactly this field** | In the current repo, `LongTimeMapUniformTail` means: for each compact window `[-R,R]` and ε, there is one time `τ` working uniformly for all trapped `u`. fileciteturn90file0L50-L57 This is **not** the same as right spatial tail decay; the repo explicitly separates right-tail decay from this field. fileciteturn89file0L27-L33 If you have only Ascoli compactness plus continuity, add a uniform Dini-style lemma: `longTime_uniform_tail_of_time_antitone_finite_slice_continuity_image_continuity`, with uniformity over the trap. |
| `longTime_image_derivative_bridge` | **Needs more / likely refactor** | Finite-time Duhamel differentiation gives differentiability of finite-time slices, not automatically differentiability of the long-time image. The repo’s derivative-limit file explicitly says uniform derivative bounds alone give only a Lipschitz limit, and keeps local-uniform convergence of derivatives as an input. fileciteturn87file0L14-L21 Minimal lemma: `longTime_image_derivative_bridge_of_localUniform_derivative_convergence`, using finite-time derivative formulas plus local-uniform convergence of `∂x w(t_n)` to a limit. |
| `longTime_time_antitone` | **Discharge now if the time-shift comparison is closed** | This field is exactly `∀ x, Antitone (fun t => forwardOrbit U t x)`. It does **not** follow from spatial antitonicity; it needs the time-comparison / supersolution orbit argument. If that is among the newly closed pieces, wire directly. Otherwise minimal lemma: `wholeLine_forward_orbit_time_antitone_of_auxiliary_comparison`. |
| `longTime_derivative_convergence` | **Needs genuine analytic work** | The field is a three-part convergence package: `wt(t,x) → 0`, `wx(t,x) → deriv U x`, and `wxx(t,x) → iteratedDeriv 2 U x`. fileciteturn74file0L3-L11 Time monotonicity plus a spatial gradient bound is **not enough** to prove this. You need a Barbalat/parabolic compactness lemma for `wt`, plus derivative convergence for `wx,wxx`. Minimal lemma below. |
| `longTime_evolution_eq` | **Discharge now, if `wt` is chosen concretely** | If you instantiate `wt` as `concreteLongTimeAuxiliaryWt`, the residual equality is literally `rfl` via `concreteLongTimeAuxiliaryWt_evolution_eq`. fileciteturn71file0L3-L27 For the stronger statement “this `wt` is the actual time derivative of the mild flow for positive time,” use the generator/Duhamel classical bootstrap, specifically `auxiliaryGlobalMild_evolution_eq_pos_of_movingFrame`. fileciteturn70file0L187-L223 |
| `fixedPoint_profile_regularity` | **Needs more unless derivative convergence is closed** | The field asks for `WholeLineProfileRegularityData`, not merely continuity or boundedness. That structure includes `HasDerivAt U`, continuity of `Ux`, second-derivative data after the resolvent identity, and continuity of `Uxx`. fileciteturn95file0L79-L91 Finite-time Duhamel differentiation is not enough; you need a long-time passage for first and second spatial derivatives. |
| `fixedPoint_flat_left` | **Needs genuine derivative-tail bridge** | The repo already says the monotone-bounded part is closed from `WaveTrap`, but `FrozenStationaryFlatAtLeft` contains derivative tails, so a separate parabolic tail bridge is still named explicitly. fileciteturn97file0L5-L11 Minimal lemma: `fixedPoint_flat_left_of_parabolic_tail_decay`, or use the existing named interface `FixedPointFlatLeftParabolicTailFromMonotoneLimit`. fileciteturn97file0L38-L61 |
| `translate_limit_identification` | **Discharge now if the left-tail identification bridge is closed** | The repo has exactly the wrapper `translate_limit_identification_of_T10`, which turns `TranslateLimitIdentificationParabolicData` into the residual field. fileciteturn97file0L98-L113 The follow-up theorem identifies the limit as `1` in the nonpositive-sensitivity branch once `p3.χ₀ ≤ 0` is available. fileciteturn97file0L115-L131 |

---

## The two specific questions

### Does `longTime_evolution_eq` now follow from the heat-generator + Duhamel differentiation?

**For the residual field: yes, even more directly.**  
Instantiate

```lean
wt := concreteLongTimeAuxiliaryWt p c (waveExponent c) Haux.raw_w Haux.raw_wx wxx
```

Then `longTime_evolution_eq` is discharged by:

```lean
concreteLongTimeAuxiliaryWt_evolution_eq
```

because `concreteLongTimeAuxiliaryWt` is defined to be the PDE right-hand side. fileciteturn71file0L3-L27

**For the mathematical statement “the mild flow solves equation (4.12) classically”: yes for positive time, but only through the classical bootstrap.** The relevant theorem is:

```lean
auxiliaryGlobalMild_evolution_eq_pos_of_movingFrame
```

It consumes the global mild solution, the gradient identification, second-Duhamel regularity, and the moving-frame time-generator data, then proves the positive-time PDE identity. fileciteturn70file0L187-L223

So wire the residual using the concrete `wt`; separately keep the positive-time classical theorem as the honest “solves (4.12)” certificate.

### Does `longTime_derivative_convergence` follow from time monotonicity + the parabolic gradient bound?

**No.**

Time monotonicity gives pointwise convergence of \(w(t,x)\). If `wt` is the actual time derivative and \(w(t,x)\) is decreasing and bounded below, then

\[
\int_0^\infty -w_t(t,x)\,dt < \infty.
\]

But integrability of a derivative does **not** imply \(w_t(t,x)\to0\) without additional regularity such as uniform continuity in time. Narrow derivative spikes can have finite integral but fail to tend to zero.

A spatial gradient bound also does not imply convergence of spatial derivatives:

\[
w(t,\cdot)\to U
\]

locally uniformly plus uniform Lipschitz bounds implies \(U\) is Lipschitz, but it does not imply

\[
w_x(t,x)\to U_x(x),
\qquad
w_{xx}(t,x)\to U_{xx}(x).
\]

That needs a parabolic compactness/regularity passage for derivatives.

The minimal additional lemma should be a single packaged theorem:

```lean
theorem wholeLine_parabolicDerivativeConvergence_of_classical_trapped_orbit
    (hclassical :
      ∀ T > 0,
        IsAuxiliaryClassicalSolutionOn p c V Vx T w wx wxx wt)
    (htime :
      ∀ x, Antitone fun t : ℝ => w t x)
    (hlower :
      ∀ t x, lowerBarrier κ κt D x ≤ w t x)
    (hlocalUniformLimit :
      LongTimeMapUniformTail κ κt D (fun _ => w))
    (hparabolicDerivativeCompact :
      -- e.g. local equicontinuity / local-uniform precompactness of
      -- wt, wx, wxx on [T,∞) × compact spatial windows
      ParabolicDerivativeCompactness w wt wx wxx)
    :
      WholeLineParabolicDerivativeConvergence
        w wt wx wxx (wholeLineLongTimeLimit w)
```

In practice I would split this into two lemmas:

```lean
theorem timeDerivative_tendsto_zero_of_monotone_bounded_uniformContinuous
```

and

```lean
theorem spatialDerivatives_tendsto_of_localUniform_C2_parabolic_compactness
```

Then package them into `WholeLineParabolicDerivativeConvergence`.

---

## What to wire immediately

Wire these now:

```lean
kappa_lt_kappat
D_ge_one
paper3_chi_nonpos
spatial_antitone
auxiliaryDuhamel_continuity
finite_time_slice_continuity
longTime_time_antitone       -- if time-comparison theorem is already closed
longTime_evolution_eq        -- with concreteLongTimeAuxiliaryWt
translate_limit_identification
```

Also wire `longTime_uniform_tail` **only if** the new theorem is exactly `LongTimeMapUniformTail`; otherwise keep it as a named Dini/uniform-convergence target.

Focus remaining effort on this dependency chain:

```text
parabolic derivative compactness / Barbalat
  ⇒ longTime_derivative_convergence
  ⇒ fixedPoint_profile_regularity
  ⇒ fixedPoint_flat_left
```

The analytic heart is therefore not the PDE identity anymore; it is the long-time derivative convergence and the left-end derivative-tail flatness.
