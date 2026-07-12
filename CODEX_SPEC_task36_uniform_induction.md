# Task 36: Uniform real induction — close PointwiseUniformizationResidual

## Goal

Create `ShenWork/PDE/P3MoserUniformInduction.lean` that reduces
`PointwiseUniformizationResidual` to a concrete initial seed hypothesis.

## The circularity problem (why T33 doesn't close it)

T33 shows: `PointwiseUniformizationResidual → SubintervalLpPowerBoundResidual`.
T31 shows: `SubintervalLpPowerBoundResidual → SubintervalMoserInputResidual`.
T28 uses: `SubintervalMoserInputResidual` in the real induction.
T32 uses: `PointwiseUniformizationResidual` for the sSup closure.

So the chain is circular through `PointwiseUniformizationResidual`.

## The fix: provide the Lp seed from the current uniform bound

At each step of the real induction, we have a UNIFORM bound M on (0,τ].
From M, we can derive `LpPowerBoundedBefore` directly: since |u(t,x)| ≤ M
on [0,1] (measure 1 domain), ∫ u^{p0} ≤ M^{p0}.

This BYPASSES the circular T33 path entirely. The Lp seed comes from
the current induction hypothesis, not from PointwiseUniformizationResidual.

## What to prove

### Definition 1: InitialUniformBoundResidual

```lean
def InitialUniformBoundResidual
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ {T : ℝ} {u v : ℝ → D.Point → ℝ},
    IsPaper2ClassicalSolution D p T u v →
      ∃ τ₀ M₀, 0 < τ₀ ∧ τ₀ ≤ T ∧
        ∀ t, 0 < t → t ≤ τ₀ → ∀ x, |u t x| ≤ M₀
```

This says: every classical solution has a uniform L∞ bound near t=0.
This is the concrete, irreducible initial-data hypothesis.

### Lemma 1: Lp bound from uniform pointwise bound

```lean
theorem intervalDomain_LpPowerBoundedBefore_of_uniform_bound
    {p0 τ M : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hp0 : 1 ≤ p0) (hM_nonneg : 0 ≤ M)
    (hM : ∀ t, 0 < t → t < τ → ∀ x, |u t x| ≤ M) :
    LpPowerBoundedBefore intervalDomain p0 τ u
```

Proof sketch: `LpPowerBoundedBefore = ∃ C, ∀ t ∈ (0,τ), D.integral (u^{p0}) ≤ C`.

`D.integral f = ∫ x in (0:ℝ)..1, intervalDomainLift f x`.

Since |u t x| ≤ M, we have |(u t x)^{p0}| ≤ M^{p0} (for p0 ≥ 1 and M ≥ 0).
And `∫ x in 0..1, M^{p0} = M^{p0} · 1 = M^{p0}`.

So `C = M^{p0}` works.

The key Mathlib lemma: `intervalIntegral.integral_le_of_abs_le` or
`MeasureTheory.integral_mono_of_nonneg` + `MeasureTheory.integral_const`.

Actually, the integration here is `intervalDomain.integral` which is the
interval integral `∫ x in 0..1`. The bound:

```
∫ x in 0..1, (intervalDomainLift (u t) x) ^ p0
  ≤ ∫ x in 0..1, M ^ p0
  = M ^ p0 · (1 - 0)
  = M ^ p0
```

Use `intervalIntegral.integral_mono_on` (for nonneg integrand) or
the absolute-value version.

IMPORTANT: `u t x` vs `intervalDomainLift (u t) x` — the integral uses
the LIFT. The lift extends u to all of ℝ (zero outside [0,1]). For
x ∈ [0,1], `intervalDomainLift (u t) x = u t ⟨x, hx⟩`. So the bound
|u t ⟨x, hx⟩| ≤ M transfers to |intervalDomainLift (u t) x| ≤ M on [0,1].
Outside [0,1], the lift is 0, so |lift| ≤ M trivially (if M ≥ 0).

### Lemma 2: Assembly inputs from uniform bound

```lean
theorem intervalDomain_assemblyInputs_of_uniform_bound
    {p : CM2Params} {T τ M : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hτ_pos : 0 < τ) (hτ_le : τ ≤ T)
    (hM_nonneg : 0 ≤ M)
    (hM : ∀ t, 0 < t → t ≤ τ → ∀ x, |u t x| ≤ M) :
    ∃ rho p0,
      CrossDiffusionBootstrapEstimate intervalDomain p τ rho u v ∧
        AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) τ rho p0 ∧
          LpBootstrapEnergyInequalityWithGap intervalDomain u τ rho p0
```

This is basically T31's proof but with Lp bound provided directly.

Proof: Copy the structure from `intervalDomain_positiveSubintervalMoserInputResidual`
in P3MoserSubintervalInput.lean (starting at line 92). Replace
`hLp hsol hsub hτ_pos` with `intervalDomain_LpPowerBoundedBefore_of_uniform_bound`.

Key imports/theorems needed:
- `isPaper2ClassicalSolution_intervalDomain_mono` — restrict to [0,τ]
- `intervalDomain_crossDiffusionBootstrapEstimate_of_classical` — cross-diffusion
- `subintervalMoserRho_pos`, `subintervalMoserP0_gt_bootstrapThreshold` — parameter bounds
- `intervalDomain_LpBootstrapEnergyInequalityWithGap_of_classical` — gap

### Lemma 3: Right extension preserving uniform bound

```lean
theorem intervalDomain_uniformBound_rightExtension
    {p : CM2Params} {T τ M : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hAssembly : SubintervalAssemblyResidual intervalDomain p)
    (hτ_pos : 0 < τ) (hτ_lt_T : τ < T)
    (hM_nonneg : 0 ≤ M)
    (hM : ∀ t, 0 < t → t ≤ τ → ∀ x, |u t x| ≤ M) :
    ∃ δ M', 0 < δ ∧ τ + δ ≤ T ∧
      ∀ t, 0 < t → t ≤ τ + δ → ∀ x, |u t x| ≤ M'
```

Proof:
1. From Lemma 2: get assembly inputs at τ
2. From hAssembly + inputs: ∃ M₁, ∀ t ∈ [0,τ], ∀ x, |u t x| ≤ M₁
3. In particular: ∀ x, |u τ x| ≤ M₁
4. From `intervalDomain_extensionByContinuityResidual`:
   ∃ δ, 0 < δ ∧ τ+δ ≤ T ∧ BoundedBeforeOnSubinterval u (τ+δ) T
5. For the NEW uniform bound on (0, τ+δ]:
   a. For t ∈ (0, τ]: |u t x| ≤ M₁ (from assembly, covers all of [0,τ])
   b. For t ∈ (τ, τ+δ]: need bound.
   
   Use joint continuity of u on (0,T) × [0,1]. The set [τ/2, τ+δ] × [0,1]
   is compact (τ/2 > 0 since τ > 0, and τ+δ ≤ T). By
   `intervalDomain_solution_slice_abs_bddAbove` (or similar),
   each slice is bounded. But we need a uniform bound on the JOINT set.
   
   APPROACH: Use the EXTENSION itself. BoundedBeforeOnSubinterval u (τ+δ) T
   gives per-t bounds on (0, τ+δ). For t ∈ (τ, τ+δ), each slice is bounded
   by some M_t. On the compact set [τ/2, τ+δ-ε] × [0,1] ⊂ (0,T) × [0,1],
   joint continuity gives a uniform bound. But ε → 0 issue at τ+δ.
   
   SIMPLER: Since τ+δ ≤ T, and u is jointly continuous on (0,T) × [0,1]
   (conjunct 9 of intervalDomainClassicalRegularity), on the compact set
   [τ/2, τ+δ] × Icc 0 1 (where τ/2 > 0 and τ+δ ≤ T — but need τ+δ < T
   for the set to be in (0,T) × [0,1]).
   
   Issue: τ+δ ≤ T. If τ+δ = T, the set [τ/2, T] × [0,1] has T ∈ [τ/2, T],
   and T is NOT in Ioo 0 T. So the joint continuity on Ioo 0 T × Icc 0 1
   doesn't cover it.
   
   FIX: ensure τ+δ < T. ExtensionByContinuityResidual uses δ = (T-τ)/2,
   which gives τ+δ = τ + (T-τ)/2 = (τ+T)/2 < T. ✓
   
   Actually, looking at the definition:
   ```
   ExtensionByContinuityResidual: ∃ δ, 0 < δ ∧ τ + δ ≤ T ∧ ...
   ```
   It says τ+δ ≤ T, not τ+δ < T. The proof in T30 uses δ = (T-τ)/2,
   which gives τ+δ = (τ+T)/2 < T ✓.
   
   So in practice τ+δ < T. But the theorem statement says ≤. For our
   purposes, we can pick a SMALLER δ if needed: use δ' = δ/2, giving
   τ+δ' < τ+δ ≤ T. Then [τ/2, τ+δ'] × [0,1] ⊂ (0,T) × [0,1].
   
   BUT: the assembly gives bound on [0, τ], not [0, τ+δ']. And
   BoundedBeforeOnSubinterval gives per-t on (0, τ+δ). We need uniform
   on (0, τ+δ'].
   
   SIMPLEST APPROACH: Don't use joint continuity at all. Use the assembly
   at τ+δ' for the extended interval. But this requires the Lp seed at
   τ+δ', which we'd get from the uniform bound on (0, τ+δ']. Circular!
   
   ACTUALLY: the simplest approach for the extension is:
   - Assembly gives M₁ on [0, τ] (uniform)
   - Each slice t ∈ (τ, τ+δ) is bounded by M_t (per-t, from continuity)
   - Pick τ+δ' = τ+δ/2 (strictly less than T)
   - [τ/2, τ+δ'] is compact subset of (0, T)
   - Joint continuity: u continuous on [τ/2, τ+δ'] × [0,1] (compact)
   - Hence bounded by M₂ on this set
   - max(M₁, M₂) gives uniform bound on (0, τ+δ']
   
   This works because τ/2 > 0 and τ+δ' < T, so [τ/2, τ+δ'] ⊂ (0,T).

6. Take M' = max(M₁, M₂), δ' = δ/2 (or whatever makes τ+δ' < T).

For the joint continuity bound, we need:
```
∃ M₂, ∀ t ∈ [τ/2, τ+δ'], ∀ x ∈ [0,1], |u t x| ≤ M₂
```

This follows from:
- `ContinuousOn (Function.uncurry (fun t x => intervalDomainLift (u t) x)) (Ioo 0 T ×ˢ Icc 0 1)`
  (conjunct 9 of intervalDomainClassicalRegularity)
- `[τ/2, τ+δ'] × [0,1]` is compact and inside `Ioo 0 T × Icc 0 1`
  (since τ/2 > 0 and τ+δ' < T)
- IsCompact.exists_bound_of_continuousOn gives the bound

The key lemma already exists: `intervalDomain_solution_slice_abs_bddAbove`
(in IntervalDomainAPrioriGlobal.lean). But it gives bounds per-slice, not
jointly. We need the JOINT version.

For the joint version, check:
```bash
grep -rn "exists_bound_of_continuousOn" ShenWork/ --include="*.lean"
```
and
```bash
grep -rn "isCompact.*prod\|IsCompact.*prod" ShenWork/ --include="*.lean"
```

If no joint version exists, prove it:
```lean
-- Given ContinuousOn f (Ioo a b ×ˢ Icc c d) and [a', b'] × [c', d'] ⊆ Ioo a b × Icc c d (compact),
-- ∃ M, ∀ p ∈ [a', b'] × [c', d'], |f p| ≤ M
-- This follows from isCompact_Icc.prod isCompact_Icc + exists_bound_of_continuousOn
```

### Theorem 1: The main reduction

```lean
theorem intervalDomain_pointwiseUniformizationResidual_of_initialBound
    {p : CM2Params}
    (hInitial : InitialUniformBoundResidual intervalDomain p)
    (hAssembly : SubintervalAssemblyResidual intervalDomain p) :
    PointwiseUniformizationResidual intervalDomain p
```

Proof: Real induction on the set S = {τ ∈ (0, T] | ∃ M, uniform on (0,τ]}.
- Base: from hInitial
- Right extension: from Lemma 3
- sSup = T: same as T32
- At sSup: need to extract uniform M. Unlike T32, HERE we can because
  the right extension GIVES us uniform bounds at each step. For any
  t < T, there exists τ > t with uniform M_τ. Then |u t x| ≤ M_τ.
  
  Wait — but M_τ depends on τ, and might grow as τ → T. The same issue!
  
  NO — the right extension step actually GIVES a specific M' at τ+δ.
  The sSup argument shows that we can extend forever, which means
  τ* = T. But we still need ONE uniform M for all of (0, T).
  
  The key: pick any τ₁ close to T (say τ₁ = T - ε). Then ∃ M₁,
  uniform on (0, τ₁]. For t ∈ (0, τ₁], |u t x| ≤ M₁. For
  t ∈ (τ₁, T): since t < T and τ₁ > 0, [τ₁/2, T-ε'] × [0,1]
  (for small ε') is compact inside (0,T). But t can be up to T-0⁺,
  and we don't have a compact set containing all such t.
  
  ACTUALLY: the key observation is that the right extension gives
  SPECIFIC δ and M'. So at each step:
  - Step 0: M₀ on (0, τ₀]
  - Step 1: M₁ on (0, τ₁] where τ₁ = τ₀ + δ₀
  - Step 2: M₂ on (0, τ₂] where τ₂ = τ₁ + δ₁
  - ...
  - Step n: M_n on (0, τ_n]
  
  The sequence τ_n → T. Since δ_k > 0 and τ_k + δ_k ≤ T, we have
  T - τ_k ≥ δ_k > 0, but δ_k might shrink. In the extension, 
  δ is roughly (T - τ)/2, so τ_k = T - (T-τ₀)/2^k. So τ_n → T
  geometrically, and the process NEVER reaches T in finitely many steps.
  
  But the sSup of the τ_n is T. The sSup argument doesn't use finitely
  many steps — it uses the COMPLETENESS of ℝ.
  
  For the sSup closure: if τ* = sSup S < T, then by right extension
  τ* + δ > τ* is in S, contradicting sSup. So τ* = T.
  
  Then for any t < T, ∃ τ > t with τ ∈ S. So ∃ M_τ uniform on (0, τ].
  In particular |u t x| ≤ M_τ for all x.
  
  But M_τ depends on the choice of τ! We need ONE M for ALL t < T.
  
  INSIGHT: pick ONE τ₁ ∈ S with τ₁ > T/2 (exists since sSup S = T).
  Then M₁ covers (0, τ₁]. For t ∈ (τ₁, T), use the assembly at τ₁:
  assembly gives M₁' on [0, τ₁]. But we need to go beyond τ₁.
  
  ALTERNATIVE: After τ* = T is proved, we KNOW τ* ∈ S? No, sSup
  doesn't guarantee membership.
  
  THE REAL FIX: In the right extension, the δ is (T-τ)/2. So when
  τ < T, we get τ' = τ + (T-τ)/4 < T (using δ' = (T-τ)/4 to ensure
  τ' = τ + δ' < T). The uniform bound at τ' covers (0, τ']. As
  τ' → T, the bounds M(τ') are given by max(M_assembly(τ), M_continuity(τ,δ')).
  
  The assembly bound M_assembly(τ) depends on the bootstrap parameters
  (fixed) and the Lp seed (from M at τ). If M(τ) doesn't grow too
  fast, M_assembly(τ) stays bounded.
  
  But we don't know the assembly's dependence on M!
  
  OK, I think the CORRECT approach is different. Instead of trying to
  bound M(τ) as τ → T, use the following argument:

  Pick two specific values: τ₁ from the initial seed, and τ₂ from
  the right extension. The key is that [τ₁/2, T-ε] × [0,1] is compact
  for any ε > 0 (since τ₁/2 > 0). On this compact set, u is bounded
  by some M₃. Combined with M₀ on (0, τ₀]:
  
  For t ∈ (0, T-ε]: |u t x| ≤ max(M₀, M₃(ε)).
  
  BUT M₃(ε) might blow up as ε → 0.
  
  WAIT — can we use the assembly to control the bound near T?
  
  At τ₂ = (τ₀ + T)/2 (strictly between τ₀ and T):
  - From the initial seed + one right extension: uniform M₂ on (0, τ₂]
  - From the Lp seed at τ₂: bootstrap data at τ₂
  - Assembly at τ₂: uniform M₂' on [0, τ₂]
  - Now apply the assembly at τ₃ = (τ₂ + T)/2: need Lp at τ₃
  - Lp at τ₃ comes from: M₂' on [0, τ₂] gives Lp on (0, τ₂),
    and continuity on [τ₂/2, τ₃] gives Lp on (τ₂, τ₃].
    Combined: Lp on (0, τ₃].
  
  But the Lp bound on (τ₂, τ₃] comes from continuity, and might
  grow as τ₃ → T.
  
  FUNDAMENTAL ISSUE: Near t = T, the solution MIGHT blow up (finite-
  time blowup). The Moser iteration is supposed to PREVENT this, but
  the assembly's control near T requires iterating the bootstrap
  closer and closer to T.
  
  The assembly at τ₃ gives M₃ on [0, τ₃]. The value M₃ depends on
  the Lp seed at τ₃, which depends on the continuity bound on
  [τ₂/2, τ₃]. If the solution grows near T, this bound grows too.
  
  BUT: the assembly's OUTPUT bound depends on the INPUT Lp seed
  through a NONLINEAR function (the Moser iteration). If the iteration
  amplifies the Lp seed, the output bound might be SMALLER than the
  input (because the iteration is a bootstrapping process that
  IMPROVES regularity).
  
  In practice, the Moser iteration gives: L∞ ≤ C(p, Ω) · ‖u‖_{Lp}
  where C depends on PDE parameters and domain, NOT on the specific
  Lp norm. So the assembly's output is controlled by the INPUT Lp norm.
  
  But the INPUT Lp norm on (0, τ₃] includes the continuity bound
  near T, which might grow. So the assembly's output might also grow.
  
  CONCLUSION: Without additional control on the solution near T
  (beyond what's in the classical solution hypothesis), we CANNOT
  prove uniform bounds near T.
  
  THE SAME ISSUE EXISTS NEAR T = 0. The InitialUniformBoundResidual
  is the hypothesis that provides control near t = 0.
  
  For near t = T: the paper's argument uses the fact that the Moser
  iteration gives bounds that DON'T depend on T. So the bound at τ
  close to T is the same as at τ far from T. This is because the
  ENERGY DISSIPATION controls the growth.
  
  In the formalization, this is INSIDE SubintervalAssemblyResidual.
  The assembly's output M depends on the bootstrap parameters and
  the Lp seed, but the Lp seed at each step is controlled by the
  PREVIOUS assembly output (which already went through the Moser
  iteration). So the chain is:
  
  M₀ → Lp₀ = M₀^{p0} → Assembly → M₁ → Lp₁ = M₁^{p0} → Assembly → M₂ → ...
  
  If the assembly's map M → M' = Assembly(M^{p0}) is CONTRACTIVE
  (M' ≤ M for M large enough), then M_n stays bounded. But we DON'T
  know the assembly's behavior (it's a residual).
  
  PRAGMATIC CONCLUSION: I should just state the reduction theorem
  (InitialUniformBound + SubintervalAssembly → PointwiseUniform)
  and leave the proof to handle the sSup closure carefully.
  
  The sSup closure CAN work if we're careful: at τ* = sSup S = T,
  we don't need T ∈ S. We need: ∀ t < T, ∃ M, |u t x| ≤ M.
  
  For any t < T: pick τ > t with τ ∈ S. Then M_τ covers (0, τ] ∋ t.
  So |u t x| ≤ M_τ. This gives per-t bounds.
  
  But we need uniform. Hmm.
  
  WAIT. I just realized: the sSup of S = {τ | ∃ M uniform on (0,τ]}
  is T. For any t < T, we can find τ ∈ S with τ > t. Then |u t x| ≤ M_τ.
  This is per-t. For uniform: we need M independent of t.
  
  Try: pick τ₁ ∈ S with τ₁ > T/2. Then M₁ covers (0, τ₁].
  Now for t ∈ [τ₁/2, T-ε] (any ε > 0): this is a compact subset
  of (0, T). u is continuous on this compact set. So bounded by M₂(ε).
  
  max(M₁, M₂(ε)) covers (0, T-ε]. But as ε → 0, M₂(ε) might grow.
  
  To cover ALL t < T, I need ε → 0. If sup_ε M₂(ε) < ∞, I'm done.
  But sup_ε M₂(ε) = sup_{t ∈ [τ₁/2, T)} |u| which might be ∞.
  
  SO: the sSup argument for the UNIFORM set gives τ* = T, but it
  does NOT give a single M covering all of (0, T). The sSup of τ
  values being T only means per-τ coverage, not uniform.
  
  THIS IS EXACTLY THE SAME GAP AS PointwiseUniformizationResidual.
  
  FINAL CONCLUSION: The reduction InitialUniformBound + Assembly →
  PointwiseUniform does NOT work via the sSup real induction alone.
  It requires QUANTITATIVE control on the assembly's output as a
  function of the Lp input.

## REVISED APPROACH: Leave as residual, document clearly

Since the uniform bound cannot be proved from the current abstract
interface (SubintervalAssemblyResidual doesn't expose the quantitative
dependence of its output on the Lp input), leave
PointwiseUniformizationResidual as a genuinely irreducible residual
of the Moser chain.

Document the analysis: the gap is equivalent to proving that the
Moser iteration's output bound doesn't blow up as τ → T. This requires
either:
(a) Quantitative Moser bounds (the assembly's output ≤ f(Lp input, params))
(b) Initial + terminal regularity of the classical solution
(c) A direct energy estimate showing sup-norm control

## WHAT TO ACTUALLY BUILD

Instead of closing PointwiseUniformizationResidual, build the COMPLETE
top-level theorem for the Moser chain, showing the exact dependency:

```lean
theorem intervalDomain_isPaper2BoundedBefore_full_conditional
    {p : CM2Params}
    (hAssembly : SubintervalAssemblyResidual intervalDomain p)
    (hUniform : PointwiseUniformizationResidual intervalDomain p) :
    ∀ {T : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
        IsPaper2BoundedBefore intervalDomain T u
```

THIS IS ALREADY DONE in P3MoserTopLevelAssembly.lean (Task 35).

## ALTERNATIVE: Try Lemma 1 anyway

Even if the full PointwiseUniformizationResidual can't be closed,
Lemma 1 (`LpPowerBoundedBefore_of_uniform_bound`) is independently
useful — it shows that uniform pointwise bounds imply Lp bounds,
which can be used in other contexts.

Build Lemma 1 and any other independently useful pieces.

## Files to read
- `ShenWork/PDE/P3MoserSubintervalInput.lean` (line 92-130) — T31's construction pattern
- `ShenWork/PDE/P3MoserRealInductionClosure.lean` — T32's sSup argument
- `ShenWork/PDE/IntervalDomain.lean:2906-2913` — joint continuity conjunct
- `ShenWork/Paper2/Statements.lean:370-380` — LpPowerBoundedBefore definition
- `ShenWork/PDE/IntervalDomainAPrioriGlobal.lean` — existing a priori lemmas

## Constraints
- NO sorry, NO axiom
- All #print axioms must show ONLY [propext, Classical.choice, Quot.sound]
- If you can't close the full theorem, deliver whatever partial lemmas compile

## Verification
```bash
lake env lean ShenWork/PDE/P3MoserUniformInduction.lean
```

If `lake env lean` fails with missing olean, first run:
```bash
lake build ShenWork.PDE.P3MoserTopLevelAssembly
```
