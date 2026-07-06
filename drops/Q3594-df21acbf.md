ANSWER Q3594 df21acbf

# Q3594 patched-chemical `v_x` zero-face audit

Repo/audit point: `xiangyazi24/Shen_work`, current main at `dc26e5f0837718e4febad5352d315bb0687003c3` (`Task 145: add patched slice derivative zero-face reducer`).

This is source-side only. I did not use downstream H1 bounded-before, physical-RHS, sqrt-bound, finite-sigma, or constant special-case routes as producers.

## 1. Existing theorem status

There is **no existing non-circular theorem** in the current repo that proves the exact v-side derivative zero-face target

```lean
deriv (intervalDomainLift (patchedChemical p u₀ u t)) x
  → deriv (intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p u₀)) x
```

uniformly in `x ∈ Set.Icc 0 1`, or jointly/relatively at `(0, x)` on a closed zero slab.

What exists now:

* `ShenWork/Paper2/IntervalChiNegH1BFormZeroStartTraceProducer.lean`
  * `patchedChemical_timeContinuousAt_zero_of_patchedSlice_ball`
  * `patchedChemical_lift_zeroFace_of_timeContinuousAt_zero`
  * `PatchedSliceDerivUniformApproachAtZero`
  * `patchedSlice_ux_zeroFace_of_derivUniformApproachAt_zero`

  These close the **value** zero face for `patchedChemical` and provide a **u-side derivative** metric reducer. They do not prove `v_x` zero-face continuity.

* `ShenWork/PDE/P3MoserDxJointContinuity.lean`
  * `intervalDomain_dx_v_jointlyContinuous`

  This gives strict positive-time continuity of

  ```lean
  Function.uncurry
    (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (v t)) x)
  ```

  only on

  ```lean
  Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1
  ```

  It does not include `t = 0`.

* `ShenWork/Paper2/IntervalChiNegH1ZeroStartPrimitiveTraceReducer.lean`
  * `continuousOn_zeroClosedSlab_of_strictTime_and_zeroFace`
  * `H1ZeroStartInitializedPrimitiveC1SignSource_of_classical_zeroFace`

  These are reducers/consumers. They explicitly require the zero-face derivative trace as input. They do not produce it.

* `ShenWork/Paper2/IntervalResolverWeakBounds.lean`
  * `resolverGrad_diff_sup_le_of_bounded`

  This is important and non-circular, but it controls the **series gradient representative**

  ```lean
  resolverGradReal p u x
  ```

  not the actual field required by the zero-face record:

  ```lean
  deriv (intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p u)) x
  ```

* `ShenWork/Paper2/IntervalDuhamelIntegrability.lean`
  * `resolverGradReal_continuous_of_continuousOn`

  This gives spatial continuity of `resolverGradReal` for continuous input profiles. Again, it is about `resolverGradReal`, not `deriv (intervalDomainLift (intervalNeumannResolverR ...))`.

* `ShenWork/PDE/IntervalResolverGradientBridge.lean`
  * `resolverR_hasDerivAt_grad`
  * `resolverGrad_majorant_summable_of_sourceDecay`
  * `resolverRGrad_apply_eq`

  These are fixed-slice series differentiation tools. They are relevant for an eventual derivative-identification bridge, but they do not currently prove the patched-chemical zero-time convergence theorem.

* `ShenWork/Paper2/IntervalMildToClassical.lean`
  * private `resolver_lift_deriv_eq_resolverGrad_of_sourceDecay`

  This identifies the derivative of the resolver lift with `resolverGradReal` for an interior spatial point under `SourceCoeffQuadraticDecay`, but it is private, fixed-slice, and not a zero-time continuity theorem. It is also not enough for the closed `Set.Icc 0 1` endpoint-inclusive target without additional endpoint handling.

So the honest answer is:

> The repo has strong ingredients for `resolverGradReal`, including a non-circular Lipschitz estimate, but it does not yet have the deriv-of-lift zero-face theorem needed by `vx_zeroFace`.

## 2. Safe next reducer: yes, add the pure metric v-side reducer

It is useful and safe to add the exact v-side analogue of the u-side reducer. It is non-circular because it consumes an explicit analytic approach hypothesis and only performs metric/topological packaging into `ContinuousWithinAt` at the zero face.

Recommended placement: either append to `ShenWork/Paper2/IntervalChiNegH1BFormZeroStartTraceProducer.lean` after the u-side reducer, or create a small new file importing it. If appending to the existing file, omit the `import` and repeated `open` lines below.

```lean
import ShenWork.Paper2.IntervalChiNegH1BFormZeroStartTraceProducer

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalMildPicard (GradientMildSolutionData)

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents

/-- Uniform-in-space initial approach of the spatial derivative of the patched
chemical resolver. This is the explicit analytic v-derivative input, not a
producer of that input. -/
def PatchedChemicalDerivUniformApproachAtZero
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∀ ε > 0, ∃ δ > 0,
    ∀ t ∈ Set.Icc (0 : ℝ) D.T, |t| < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (intervalDomainLift (patchedChemical p u₀ D.u t)) x -
          deriv (intervalDomainLift
            (ShenWork.PDE.intervalNeumannResolverR p u₀)) x| < ε

/-- The v-derivative zero face follows from uniform derivative approach at zero
and spatial continuity of the initial resolver derivative.

This is the patched-chemical analogue of
`patchedSlice_ux_zeroFace_of_derivUniformApproachAt_zero`. It is non-circular:
it does not assume `H1ZeroStartPrimitiveDerivativeZeroFaceTrace`; it only
packages the explicit v-side derivative approach into the required zero-face
`ContinuousWithinAt` field. -/
theorem patchedChemical_vx_zeroFace_of_derivUniformApproachAt_zero
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hv₀x_cont :
      ContinuousOn
        (fun x : ℝ =>
          deriv (intervalDomainLift
            (ShenWork.PDE.intervalNeumannResolverR p u₀)) x)
        (Set.Icc (0 : ℝ) 1))
    (hdvx : PatchedChemicalDerivUniformApproachAtZero (p := p) (u₀ := u₀) D) :
    ∀ {b : ℝ}, 0 ≤ b → b ≤ D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ContinuousWithinAt
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv (intervalDomainLift (patchedChemical p u₀ D.u t)) x))
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1) (0, x) := by
  intro b _hb0 hbT x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨δt, hδt_pos, hδt⟩ := hdvx (ε / 2) hε2
  have hx_cont :
      ContinuousWithinAt
        (fun x : ℝ =>
          deriv (intervalDomainLift
            (ShenWork.PDE.intervalNeumannResolverR p u₀)) x)
        (Set.Icc (0 : ℝ) 1) x :=
    hv₀x_cont x hx
  rw [Metric.continuousWithinAt_iff] at hx_cont
  obtain ⟨δx, hδx_pos, hδx⟩ := hx_cont (ε / 2) hε2
  refine ⟨min δt δx, lt_min hδt_pos hδx_pos, ?_⟩
  rintro ⟨t, y⟩ ⟨htb, hy⟩ hdist
  have hdist_t : dist t (0 : ℝ) < δt := by
    have hprod : dist (t, y) (0, x) < δt :=
      lt_of_lt_of_le hdist (min_le_left _ _)
    have hle : dist t (0 : ℝ) ≤ dist (t, y) (0, x) := by
      rw [Prod.dist_eq]
      exact le_max_left _ _
    exact lt_of_le_of_lt hle hprod
  have hdist_x : dist y x < δx := by
    have hprod : dist (t, y) (0, x) < δx :=
      lt_of_lt_of_le hdist (min_le_right _ _)
    have hle : dist y x ≤ dist (t, y) (0, x) := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    exact lt_of_le_of_lt hle hprod
  have htD : t ∈ Set.Icc (0 : ℝ) D.T := ⟨htb.1, le_trans htb.2 hbT⟩
  have htime :
      |deriv (intervalDomainLift (patchedChemical p u₀ D.u t)) y -
        deriv (intervalDomainLift
          (ShenWork.PDE.intervalNeumannResolverR p u₀)) y| < ε / 2 := by
    exact hδt t htD (by simpa [Real.dist_eq] using hdist_t) y hy
  have hspace :
      |deriv (intervalDomainLift
          (ShenWork.PDE.intervalNeumannResolverR p u₀)) y -
        deriv (intervalDomainLift
          (ShenWork.PDE.intervalNeumannResolverR p u₀)) x| < ε / 2 := by
    have h := hδx hy (by simpa [Real.dist_eq] using hdist_x)
    simpa [Real.dist_eq] using h
  have hval_ty :
      Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv (intervalDomainLift (patchedChemical p u₀ D.u t)) x) (t, y) =
        deriv (intervalDomainLift (patchedChemical p u₀ D.u t)) y := by
    simp [Function.uncurry]
  have hval_0x :
      Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv (intervalDomainLift (patchedChemical p u₀ D.u t)) x) (0, x) =
        deriv (intervalDomainLift
          (ShenWork.PDE.intervalNeumannResolverR p u₀)) x := by
    simp [Function.uncurry, patchedChemical_zero]
  rw [hval_ty, hval_0x, Real.dist_eq]
  calc
    |deriv (intervalDomainLift (patchedChemical p u₀ D.u t)) y -
        deriv (intervalDomainLift
          (ShenWork.PDE.intervalNeumannResolverR p u₀)) x|
        = |(deriv (intervalDomainLift (patchedChemical p u₀ D.u t)) y -
              deriv (intervalDomainLift
                (ShenWork.PDE.intervalNeumannResolverR p u₀)) y) +
            (deriv (intervalDomainLift
                (ShenWork.PDE.intervalNeumannResolverR p u₀)) y -
              deriv (intervalDomainLift
                (ShenWork.PDE.intervalNeumannResolverR p u₀)) x)| := by
          ring_nf
    _ ≤ |deriv (intervalDomainLift (patchedChemical p u₀ D.u t)) y -
          deriv (intervalDomainLift
            (ShenWork.PDE.intervalNeumannResolverR p u₀)) y| +
        |deriv (intervalDomainLift
            (ShenWork.PDE.intervalNeumannResolverR p u₀)) y -
          deriv (intervalDomainLift
            (ShenWork.PDE.intervalNeumannResolverR p u₀)) x| :=
          abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add htime hspace
    _ = ε := by ring

#print axioms patchedChemical_vx_zeroFace_of_derivUniformApproachAt_zero

end ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents
```

This proof is only the metric `ε/2` argument. It does not manufacture the analytic convergence. That separation is exactly why it is safe.

## 3. What stronger analytic producer should eventually discharge `PatchedChemicalDerivUniformApproachAtZero`?

The eventual producer should use the existing **resolver-gradient representative** Lipschitz theorem, but it still needs a bridge from the representative to the actual derivative-of-lift field.

Relevant existing ingredients:

* `ShenWork/Paper2/IntervalResolverWeakBounds.lean`
  * `resolverGrad_diff_sup_le_of_bounded`
  * `source_coeffL2Norm_diff_le_of_bounded`
  * `resolverSourceCoeff_diff_re_sq_summable_of_continuousOn`
  * `resolver_sineSeries_summable_of_sourceL2`

* `ShenWork/Paper2/IntervalDuhamelIntegrability.lean`
  * `resolverGradReal_continuous_of_continuousOn`

* `ShenWork/PDE/IntervalResolverGradientBridge.lean`
  * `resolverR_hasDerivAt_grad`
  * `resolverGrad_majorant_summable_of_sourceDecay`
  * `resolverRGrad_apply_eq`
  * `resolverRGrad_apply_eq` / `resolverGradReal_eq` style bridges used in downstream proofs

* `ShenWork/PDE/IntervalNeumannEllipticResolverR.lean`
  * `intervalNeumannResolverCoeff`
  * `intervalNeumannResolverR`
  * `intervalNeumannResolverCoeff_elliptic`
  * `intervalNeumannResolverWeight_sq_summable`
  * `intervalNeumannResolverGradWeight_sq_summable`
  * `intervalNeumannResolverR_grad_sup_lipschitz`

* `ShenWork/Paper2/IntervalMildToClassical.lean`
  * private `resolver_lift_deriv_eq_resolverGrad_of_sourceDecay`

The exact missing theorem is a **deriv-level resolver-gradient Lipschitz theorem**, not just a `resolverGradReal` theorem. A good public target is:

```lean
/-- Missing analytic bridge: deriv-of-lift Lipschitz for the static resolver on a
bounded nonnegative ball.  This should be proved from
`resolverGrad_diff_sup_le_of_bounded` plus a public derivative-identification
bridge between `deriv (intervalDomainLift (intervalNeumannResolverR p w))` and
`resolverGradReal p w`. -/
theorem intervalNeumannResolverR_lift_deriv_diff_sup_le_of_bounded
    (p : CM2Params) (hγ : 1 ≤ p.γ)
    {u₁ u₂ : intervalDomainPoint → ℝ} {M D : ℝ}
    (hUc₁ : ContinuousOn (intervalDomainLift u₁) (Set.Icc (0 : ℝ) 1))
    (hUc₂ : ContinuousOn (intervalDomainLift u₂) (Set.Icc (0 : ℝ) 1))
    (hmem₁ : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift u₁ x ∈ Set.Icc (0 : ℝ) M)
    (hmem₂ : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift u₂ x ∈ Set.Icc (0 : ℝ) M)
    (hD : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |intervalDomainLift u₁ x - intervalDomainLift u₂ x| ≤ D)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |deriv (intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p u₁)) x -
      deriv (intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p u₂)) x| ≤
      Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * (p.γ * M ^ (p.γ - 1)) * D))
```

Once that theorem exists, the patched-chemical approach producer should be the gradient analogue of the current value producer:

```lean
/-- Expected future producer: uniform initial approach of the patched chemical
spatial derivative from the patched u-slice value approach plus the deriv-level
resolver Lipschitz theorem. -/
theorem patchedChemical_derivUniformApproachAt_zero_of_patchedSlice_ball
    {p : CM2Params} (hγ : 1 ≤ p.γ) {u₀ : intervalDomainPoint → ℝ}
    (hu₀cont : Continuous u₀) (D : GradientMildSolutionData p u₀)
    {M : ℝ} (hM : 0 < M)
    (hu₀_mem : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift u₀ x ∈ Set.Icc (0 : ℝ) M)
    (hpatch_mem : ∀ t ∈ Set.Icc (0 : ℝ) D.T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (patchedSlice u₀ D.u t) x ∈ Set.Icc (0 : ℝ) M) :
    PatchedChemicalDerivUniformApproachAtZero (p := p) (u₀ := u₀) D
```

The intended proof would mirror `patchedChemical_timeContinuousAt_zero_of_patchedSlice_ball`:

1. Use `patchedSlice_timeContinuousAt_zero` to obtain a uniform sup-norm bound
   `|patchedSlice u₀ D.u t - u₀| ≤ η`.
2. For `t > 0`, rewrite `patchedChemical p u₀ D.u t` to
   `mildChemicalConcentration p D.u t`, hence to the static resolver
   `intervalNeumannResolverR p (D.u t)`. At `t = 0`, rewrite to
   `intervalNeumannResolverR p u₀`.
3. Apply the missing deriv-level resolver Lipschitz theorem above with
   `u₁ = D.u t`, `u₂ = u₀`, and `D = η`.
4. Choose
   ```lean
   η = ε /
     (Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
       (2 * (p.ν * (p.γ * M ^ (p.γ - 1)))) + 1)
   ```
   exactly as the current value proof uses the resolver-value weight.

The genuinely missing part is the deriv-level bridge. The repo already has the `resolverGradReal` Lipschitz theorem; what is not yet present is a public theorem proving that the actual closed-interval field demanded by the zero-face record,

```lean
deriv (intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w)) x
```

is controlled by that `resolverGradReal` machinery for every `x ∈ Set.Icc 0 1`, including endpoint handling.

## 4. Circular/dead routes to avoid

* Do not use `H1ZeroStartInitializedPrimitiveC1SignSource_of_classical_zeroFace` as a producer. It consumes `H1ZeroStartPrimitiveC1ZeroFaceTrace`, including `vx_zeroFace`.

* Do not use `H1ZeroStartInitializedPrimitiveC1SignSource_of_BFormDirect_zeroFace` or `H1ZeroStartInitializedPrimitiveC1SignSource_of_BFormSq_zeroFace` as producers. Both consume the full zero-face trace frontier.

* Do not treat `intervalDomain_dx_v_jointlyContinuous` as a zero-face theorem. It is strict-time only.

* Do not treat `patchedChemical_lift_zeroFace_of_timeContinuousAt_zero` as a derivative theorem. It is value-only.

* Do not treat `resolverGrad_diff_sup_le_of_bounded` alone as the final theorem. It controls `resolverGradReal`, not the `deriv (intervalDomainLift ...)` field in the trace record.

## Bottom line

Add the v-side metric reducer. It is safe, small, and non-circular. The real analytic frontier is the deriv-level static resolver Lipschitz/identification theorem that upgrades the existing `resolverGradReal` Lipschitz machinery to the exact `deriv (intervalDomainLift (intervalNeumannResolverR ...))` field used by `H1ZeroStartPrimitiveDerivativeZeroFaceTrace.vx_zeroFace`.
