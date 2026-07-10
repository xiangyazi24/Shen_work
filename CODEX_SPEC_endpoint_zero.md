# Task: Prove IntervalDomainPowerEnergyEndpointContinuity at t=0 from InitialTrace

## Goal
Add to `ShenWork/PDE/P3MoserEnergyContinuity.lean` (or create a new file
`ShenWork/Paper2/IntervalDomainEnergyEndpointZero.lean`) a theorem:

```lean
theorem intervalDomainPowerEnergyContinuousWithinAt_zero_of_initialTrace
    {p : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hp0 : 1 ≤ p0) :
    ContinuousWithinAt
      (fun t => intervalDomain.integral
        (fun x : intervalDomain.Point => (u t x) ^ p0))
      (Set.Icc 0 T) 0
```

## Mathematical argument

1. `InitialTrace` says: `∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ → supNorm(u t - u₀) < ε`.
   This is uniform convergence `u(t) → u₀` as `t → 0+`.

2. On the unit interval [0,1], uniform convergence implies Lp convergence:
   if `supNorm(f - g) < ε` and both are bounded, then
   `|∫ f^p - ∫ g^p| ≤ C * ε` for some C depending on the sup bounds and p.

3. Specifically: for `a, b > 0` bounded, `|a^p - b^p| ≤ p * max(a,b)^{p-1} * |a - b|`
   (mean value theorem for `x ↦ x^p`). So:
   `|∫(u(t,x))^p - ∫(u₀(x))^p| ≤ p * M^{p-1} * ∫|u(t,x) - u₀(x)| ≤ p * M^{p-1} * sup|u(t) - u₀|`
   where M bounds both u(t) and u₀ (which exists by BddAbove from PaperPositiveInitialDatum + solution regularity).

4. So the energy function `E(t) = ∫(u(t,x))^p` converges to `E₀ = ∫(u₀(x))^p` as t → 0+.

5. The value at t=0 is `∫(u(0,x))^p`. We need this to equal the limit. If the function u(0,·) doesn't
   necessarily equal u₀(·), we might need `ContinuousWithinAt` at 0 for the function AS DEFINED,
   not at its limit value. The `ContinuousWithinAt f S 0` means `f(t) → f(0)` as t → 0 within S.
   So we need `∫(u(t,x))^p → ∫(u(0,x))^p`, which might differ from `∫(u₀(x))^p`.

   Actually, looking at the existing `intervalDomain_initialTracePowerEnergyTendsto_of_paperPositive`
   (P3MoserEnergyContinuity.lean:520), it proves the TENDSTO to the u₀ energy. For ContinuousWithinAt
   at 0, we need tendsto to the VALUE at 0 (which is `∫(u(0,·))^p`).

   If u(0,·) ≠ u₀(·), these might differ. Check: does InitialTrace guarantee u(0) = u₀?
   Looking at the definition: `InitialTrace D u₀ u` says `supNorm(u t - u₀) → 0` as `t → 0+`.
   This does NOT imply u(0) = u₀ necessarily.

   **Option A**: If we can show `u(0,·) = u₀(·)` from the trace condition + regularity, then done.
   **Option B**: Weaken the goal to `Tendsto (fun t => ∫(u(t,x))^p) (nhdsWithin 0 (Set.Ioi 0)) (nhds _)`
   without specifying the limit equals ∫(u(0))^p.
   **Option C**: The existing `IntervalDomainPowerEnergyEndpointContinuity` structure has two fields:
   - `atZero`: `ContinuousWithinAt ... (Icc 0 T) 0` — needs f(t) → f(0)
   - `atRight`: `ContinuousWithinAt ... (Icc 0 T) T` — needs f(t) → f(T)

   For `atZero`, we need `∫(u(t,x))^p → ∫(u(0,x))^p` as `t → 0` within [0,T].
   The uniform convergence gives `∫(u(t,x))^p → ∫(u₀(x))^p`. So if `u(0,·) = u₀(·)`, we're done.

   **Check existing results**: `intervalDomainWithInitialSlice` (P3MoserEnergyContinuity.lean:181)
   re-anchors the trajectory by replacing `u(0)` with `u₀`. This suggests u(0) ≠ u₀ in general,
   and the existing code works around this by modifying the function.

   **So use `intervalDomainWithInitialSlice`**: define `ũ(t) = u₀ if t=0, u(t) if t>0`, and prove
   continuity of `∫(ũ(t))^p` at 0. Then `ContinuousWithinAt ... (Icc 0 T) 0` holds for ũ.

   Then the theorem would produce the endpoint continuity for the modified trajectory, not the original.
   Check if this is compatible with how the frontier is consumed.

   Actually, a simpler approach: just prove the `Tendsto` version and package it.
   Look at `IntervalDomainPowerEnergyEndpointContinuity` more carefully to see what it actually needs.

## Existing infrastructure to use
1. `intervalDomain_initialTracePowerEnergyTendsto_of_paperPositive` (line 520) — already proves
   `Tendsto (fun t => ∫(u(t,x))^p) ... (nhds (∫(u₀(x))^p))` for global solutions
2. `intervalDomain_initialTrace_pointwise_abs_lt` (line 496) — pointwise control from InitialTrace
3. `intervalDomain_traceDiff_slice_abs_bddAbove_of_global` (line 477) — boundedness of trace diff
4. `real_rpow_uniformContinuousOn_Icc_of_pos_left` (in same file) — uniform continuity of x^p
5. `IntervalDomainPowerEnergyEndpointContinuity` definition (line 122)

## Key issue
The existing `intervalDomain_initialTracePowerEnergyTendsto_of_paperPositive` requires
`IsPaper2GlobalClassicalSolution` (global, all T). For finite-horizon, the same proof works but
needs adaptation. The core argument is:
- Uniform convergence u(t) → u₀ (from InitialTrace)
- Boundedness of u(t) on compact domain (from classical solution regularity at positive times)
- Uniform continuity of x ↦ x^p on bounded intervals
- These give L^p convergence

Adapt this proof for finite-horizon classical solutions.

## Build command
```bash
cd ~/repos/Shen_work && lake env lean <your-file> 2>&1 | tail -30
```

## Rules
- No sorry, no axiom, no native_decide
- If the `u(0) ≠ u₀` issue causes difficulty, you may:
  (a) Produce a theorem for the `WithInitialSlice` version (replacing u(0) with u₀)
  (b) Or add `u(0) = u₀` as a hypothesis
  (c) Or prove the Tendsto version (not ContinuousWithinAt) and note the gap
- Deliver what compiles + precise stall report if stuck
- Work only in /Users/huangx/repos/Shen_work/
