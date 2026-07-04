# Task 36: Bridge SubintervalAssemblyResidual from Moser ladder

## Goal

Create `ShenWork/PDE/P3MoserSubintervalAssemblyBridge.lean` that reduces
`SubintervalAssemblyResidual` to existing Moser ladder infrastructure.

## The architecture

`SubintervalAssemblyResidual` says: given bootstrap data at τ, produce
∃ M on [0,τ] pointwise. The existing codebase already has the FULL Moser
iteration chain:

```
LpBootstrapEnergyInequalityWithGap
  → IntegratedHigherPowerEnergyWindowCoeffFrontier
    → IntegratedMoserFirstCrossingStep
      → moser_iteration_chain (all Lp)
        → IsPaper2BoundedBefore (L∞)
```

But SubintervalAssemblyResidual operates on a SUBINTERVAL [0,τ] while the
existing chain works on [0,T]. The bridge:

1. Restrict classical solution to [0,τ] via `isPaper2ClassicalSolution_intervalDomain_mono`
2. Apply the existing chain on [0,τ]
3. Convert `IsPaper2BoundedBefore` (supNorm) to pointwise bounds
4. Handle t=0 separately

## What to prove

### Theorem 1: The bridge

```lean
theorem intervalDomain_subintervalAssemblyResidual_of_step_and_endpoint
    {p : CM2Params}
    (hstep :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
        LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0 →
          IntegratedMoserFirstCrossingStep intervalDomain u T rho p0)
    (hEndpoint :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
          ∃ pSeq rootBound : ℕ → ℝ,
            (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
              IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound)
    (hInitial :
      ∀ {T : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
          ∃ M₀, ∀ x, |u 0 x| ≤ M₀) :
    SubintervalAssemblyResidual intervalDomain p
```

### Proof sketch

```
intro T τ rho p0 u v hsol hsub hcross hboot hgap
-- 1. Restrict to [0,τ]
have hτ_pos : 0 < τ := ... -- from hboot (which has T_pos field)
have hτ_le : τ ≤ T := hsub.1
have hsolτ := isPaper2ClassicalSolution_intervalDomain_mono hτ_pos hτ_le hsol
-- 2. Cross-diffusion, bootstrap, gap on [0,τ] — already given or derivable
-- hcross is CrossDiffusionBootstrapEstimate at τ (already for the subinterval)
-- hboot is AbstractLpBootstrapHypothesis at τ (already for the subinterval)  
-- hgap is LpBootstrapEnergyInequalityWithGap at τ (already for the subinterval)
-- 3. Get IntegratedMoserFirstCrossingStep on [0,τ]
have hstepτ := hstep hsolτ hcross hboot hgap
-- 4. Get endpoint on [0,τ]
rcases hEndpoint hsolτ hcross hboot with ⟨pSeq, rootBound, hEndpt⟩
-- 5. IsPaper2BoundedBefore on (0,τ)
have hBounded := intervalDomain_hBoundedBefore_of_integrated_step_and_endpoint
    hsolτ hcross hboot hstepτ hEndpt
-- 6. Convert to pointwise on (0,τ)
rcases hBounded with ⟨M, hM⟩
-- 7. Handle t=0
rcases hInitial hsol with ⟨M₀, hM₀⟩
-- 8. Combine
refine ⟨max M M₀, fun t ht x => ?_⟩
rcases eq_or_lt_of_le ht.1 with h0 | h0_lt
· -- t = 0: use hM₀
  subst h0
  exact (hM₀ x).trans (le_max_right _ _)
· -- t > 0: use hM
  have htτ : t < τ + 1 := ... -- t ≤ τ
  -- need: supNorm(u t) ≤ M → |u t x| ≤ M
  exact (intervalDomain_supNorm_le_implies_pointwise (hM t h0_lt ht.2)).trans (le_max_left _ _)
```

Wait — IsPaper2BoundedBefore gives supNorm ≤ M for t ∈ (0, τ). And
SubintervalAssemblyResidual asks for |u t x| ≤ M for t ∈ [0, τ].

Key conversion: `intervalDomain.supNorm f ≤ M → ∀ x, |f x| ≤ M`.
This is the CONVERSE of `intervalDomain_supNorm_le_of_pointwise_abs_bound`.
Need: `∀ x, |f x| ≤ intervalDomain.supNorm f` (or `|f x| ≤ M` when supNorm ≤ M).

For intervalDomain: `supNorm f = sSup (range (|f ·|))`. So `|f x| ≤ sSup (range (|f ·|))`.
This holds by `le_csSup` if range is bounded above (which it is since supNorm is finite).

Check: does `intervalDomain_abs_le_supNorm` or similar exist?

```bash
grep -rn 'abs_le_supNorm\|pointwise_le_supNorm\|le_intervalDomainSupNorm' ShenWork/ --include="*.lean"
```

## Key files to read

- `ShenWork/PDE/P3MoserFirstCrossingContinuation.lean` — SubintervalAssemblyResidual definition (line 77)
- `ShenWork/PDE/P3MoserBoundedBeforeProducer.lean` — `intervalDomain_hBoundedBefore_of_integrated_step_and_endpoint` (line 95)
- `ShenWork/PDE/P3MoserRealInduction.lean` — `intervalDomain_supNorm_le_of_pointwise_abs_bound` (line 96)
- `ShenWork/PDE/IntervalDomainExistence.lean` — `isPaper2ClassicalSolution_intervalDomain_mono`
- `ShenWork/PDE/P3MoserIntegratedClosure.lean` — `IntegratedMoserFirstCrossingStep` (line 49), `moser_iteration_chain_of_integrated_first_crossing_step` (line 2676)
- `ShenWork/Paper2/Statements.lean` — `IsPaper2BoundedBefore` (line 352), `LpPowerBoundedBefore` (line 370)
- `ShenWork/PDE/P3MoserIntegratedDissipationPDEv2.lean` — `LpBootstrapEnergyInequalityWithGap` (line 30)

## Key concern: types match?

SubintervalAssemblyResidual inputs have rho and p0 as UNIVERSALLY QUANTIFIED:
```
∀ {T τ rho p0 : ℝ} {u v : ℝ → D.Point → ℝ}, ...
```

The suppliers in hstep and hEndpoint also take rho and p0. So the types should match:
- SubintervalAssemblyResidual's rho,p0 → pass to hstep and hEndpoint's rho,p0.
- SubintervalAssemblyResidual's τ → restrict classical solution to τ, then pass T=τ to suppliers.

BUT: SubintervalAssemblyResidual takes CrossDiffusionBootstrapEstimate at τ. After restricting to [0,τ], the classical solution has horizon τ. So hstep needs cross-diffusion at τ with the restricted solution — which is exactly what hcross provides.

Similarly, AbstractLpBootstrapHypothesis at τ with the restricted solution — from hboot.

And LpBootstrapEnergyInequalityWithGap at τ — from hgap.

So the type matching should work: SubintervalAssemblyResidual's inputs feed directly into hstep after restriction.

## The |u t x| ≤ supNorm conversion

Need: `∀ x, |u t x| ≤ intervalDomain.supNorm (u t)` for any t.

`intervalDomainSupNorm f = sSup (range (fun x => |f x|))`.

By definition, `|f x| ∈ range (fun y => |f y|)`, so `|f x| ≤ sSup ...` by `le_csSup`.
Need: `BddAbove (range (fun y => |f y|))`. This is `∃ M, ∀ y, |f y| ≤ M`.

For classical solutions on [0,1]: u(t) is continuous on compact [0,1] → bounded → range bounded above.
But u(0) might not be continuous (no regularity at t=0).

For t > 0: u(t) is continuous on [0,1] (from classicalRegularity conjunct 1). So bounded above.

For t = 0: we use hInitial.

So: `∀ x, |u t x| ≤ intervalDomain.supNorm (u t)` holds for t > 0 (continuous ↠ bounded range ↠ le_csSup).

And `IsPaper2BoundedBefore T u` says `∃ M, ∀ t ∈ (0,T), supNorm(u t) ≤ M`.

Combining: `∀ t ∈ (0,T), ∀ x, |u t x| ≤ supNorm(u t) ≤ M`.

So `∀ t ∈ (0,T), ∀ x, |u t x| ≤ M`. ✓

For t=0: use hInitial to get M₀. Take max(M, M₀).

## Alternative: skip hInitial and produce bounds on (0,τ] only

If the SubintervalAssemblyResidual output at t=0 is never used (verified: the
continuation chain only evaluates at t=τ where τ > 0), we could:

1. Prove the bound on (0,τ] from the Moser iteration
2. Extend to [0,τ] by taking M' = max(M, 0) + 1 and noting that u(0,x) is...

Actually, we can't extend to t=0 without a bound on u(0). Let's keep hInitial.

## Constraints

- NO sorry, NO axiom
- `#print axioms` = `[propext, Classical.choice, Quot.sound]`
- If hInitial is impossible to discharge, flag it and deliver the theorem with hInitial carried

## Verification

```bash
lake env lean ShenWork/PDE/P3MoserSubintervalAssemblyBridge.lean
```

If that fails with missing olean:
```bash
lake build ShenWork.PDE.P3MoserTopLevelAssembly
```
then retry.
