# CODEX_SPEC: Fix unsatisfiable coefficient gap — combined energy-surplus route

## Problem

`intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE` (in
`P3MoserIntegratedDissipationPDE.lean`) takes:

```lean
(hgap : ∀ q, p0 ≤ q → ∀ A K : ℝ, 0 < A → 0 < K → (2 : ℝ) < q * A)
```

This is **UNSATISFIABLE**: it says `2 < q * A` for ALL positive A, but
for `A = 1/(2q)` we get `2 < 1/2`, which is false. So the theorem is
vacuously true and can never be applied.

The root cause is in `P3MoserIntegratedClosure.lean`, line 816-818:
```lean
(hsurplus :
  ∀ p, p0 ≤ p → ∀ A K, 0 < A → 0 < K →
    ∃ eps, 0 < eps ∧ (p * K) * eps ≤ p * A - theta)
```
universally quantifies over A,K, but the proof (lines 821-822) only uses the
SPECIFIC A,K from `LpBootstrapEnergyInequality`:
```lean
rcases henergy p hp with ⟨A, hA, B, hB, K, hK, L_const, hpoint_raw⟩
rcases hsurplus p hp A K hA hK with ⟨eps, heps, habsorb⟩
```

## Fix

Create `ShenWork/PDE/P3MoserIntegratedDissipationPDEv2.lean` that provides the
SAME conclusion `IntegratedMoserDissipationDropBefore` but with a SATISFIABLE
hypothesis. The fix: combine the energy inequality with the gap into a single
hypothesis where the gap only applies to the SPECIFIC A from the energy inequality.

## Architecture

### New definition

```lean
/-- LpBootstrapEnergyInequality PLUS the gap condition on the specific A. -/
def LpBootstrapEnergyInequalityWithGap
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ) (T rho p0 : ℝ) : Prop :=
  ∀ pExp, p0 ≤ pExp →
    ∃ A > 0, ∃ B > 0, ∃ K > 0, ∃ L,
      (∀ t, 0 < t → t < T →
        (1 / pExp) *
            deriv (fun τ => D.integral (fun x => (u τ x) ^ pExp)) t +
          A *
            D.integral
              (fun x =>
                (D.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) +
          B * D.integral (fun x => (u t x) ^ pExp) ≤
        K * D.integral (fun x => (u t x) ^ (pExp + rho)) + L) ∧
      (2 : ℝ) < pExp * A
```

This says: for each exponent, the energy inequality holds with SPECIFIC A,B,K,L
AND pExp * A > 2 for THOSE specific constants. This is satisfiable — it's a
condition on the PDE parameters, not on all positive numbers.

### New theorems

**Theorem 1:** Derive the surplus from the combined hypothesis.

```lean
theorem surplus_of_energyWithGap
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (heg : LpBootstrapEnergyInequalityWithGap D u T rho p0) :
    ∀ pExp, p0 ≤ pExp →
      ∃ A > 0, ∃ B > 0, ∃ K > 0, ∃ L,
        (∀ t, 0 < t → t < T → [energy ineq]) ∧
        ∃ eps, 0 < eps ∧ (pExp * K) * eps ≤ pExp * A - 2
```

Proof: from `heg pExp hp`, get the energy inequality with `2 < pExp * A`,
then apply `exists_pos_eps_mul_le_sub_of_coeff_gap` (already proved at line 242)
with `theta := 2`.

**Theorem 2:** Build the higher-power window frontier from the combined hypothesis.

```lean
theorem higherPowerWindowCoeffFrontier_of_energyWithGap ...
```

Proof: follow the same structure as
`integratedHigherPowerEnergyWindowCoeffFrontier_of_LpBootstrapEnergyInequality`
(line 789), but instead of using separate `henergy` + `hsurplus`, use the combined
`heg` which gives BOTH the energy inequality AND the surplus for the same A,K.

The key proof step (mirroring lines 820-822):
```lean
intro p hp
rcases heg p hp with ⟨A, hA, B, hB, K, hK, L, hpoint_raw, hgap⟩
-- hgap : 2 < p * A
have hsurp := exists_pos_eps_mul_le_sub_of_coeff_gap (theta := 2) (p := p) (A := A) (K := K) hgap
rcases hsurp with ⟨eps, heps, habsorb⟩
-- Now we have the energy inequality (hpoint_raw) AND the absorption surplus (habsorb)
-- for the SAME A, K. Proceed exactly as in the original proof.
```

**Theorem 3 (main):** The full PDE-facing dissipation theorem.

```lean
theorem intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE_v2
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hftc : IntegratedMoserEnergyWindowFTC intervalDomain u T p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hdata : IntervalDomainIntegratedMoserClassicalRegularityData u T p0)
    (hgap : LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0) :
    IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
```

## Implementation strategy

The MOST ECONOMICAL approach: DON'T rewrite the proof of
`integratedHigherPowerEnergyWindowCoeffFrontier_of_LpBootstrapEnergyInequality` from
scratch. Instead, DERIVE `LpBootstrapEnergyInequality` from
`LpBootstrapEnergyInequalityWithGap` (just drop the gap condition) and produce the
surplus from the gap condition, then apply the EXISTING theorem with the derived
energy inequality + surplus:

```lean
theorem intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE_v2
    ... (hgap : LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0) :
    IntegratedMoserDissipationDropBefore intervalDomain u T rho p0 := by
  -- 1. Derive plain energy inequality from combined
  have henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0 := by
    intro pExp hp
    rcases hgap pExp hp with ⟨A, hA, B, hB, K, hK, L, hpoint, _hgap_val⟩
    exact ⟨A, hA, B, hB, K, hK, L, hpoint⟩
  -- 2. Derive surplus from combined
  have hsurplus : ∀ p, p0 ≤ p → ∀ A K : ℝ, 0 < A → 0 < K →
      ∃ eps : ℝ, 0 < eps ∧ (p * K) * eps ≤ p * A - 2 := by
    -- THIS IS STILL UNIVERSALLY QUANTIFIED AND UNSATISFIABLE!
    -- WRONG: we can't derive the universal surplus from the specific gap.
```

Wait — that approach doesn't work because the existing theorem still demands the
universal surplus.

**Correct approach:** Write a new version of the higher-power frontier that takes
the combined form. The proof mirrors
`integratedHigherPowerEnergyWindowCoeffFrontier_of_LpBootstrapEnergyInequality`
but replaces lines 820-822.

## The actual proof structure

The existing proof (lines 789-853) does:

```
intro p hp
rcases henergy p hp with ⟨A, hA, B, hB, K, hK, L, hpoint_raw⟩
rcases hsurplus p hp A K hA hK with ⟨eps, heps, habsorb⟩
... [rest of proof using A, B, K, L, eps, hpoint_raw, habsorb]
```

The new proof needs to do:

```
intro p hp
rcases heg p hp with ⟨A, hA, B, hB, K, hK, L, hpoint_raw, hgap_val⟩
have ⟨eps, heps, habsorb⟩ := exists_pos_eps_mul_le_sub_of_coeff_gap hgap_val
... [EXACT SAME rest of proof using A, B, K, L, eps, hpoint_raw, habsorb]
```

The rest of the proof after extracting A, B, K, L, eps is IDENTICAL. So copy the
proof from line 823 to 853, it works verbatim.

But this means we need to copy all the intermediate hypotheses too (hFTC, hG_int,
hY_int, etc.). The cleanest approach: write a combined frontier theorem, then
chain it through the same downstream path.

## Files to create

1. `ShenWork/PDE/P3MoserIntegratedDissipationPDEv2.lean` — new file with:
   - `LpBootstrapEnergyInequalityWithGap` definition
   - `higherPowerWindowCoeffFrontier_of_energyWithGap` — the frontier theorem
     using combined hypothesis
   - `intervalDomain_integratedMoserDissipationDropBefore_of_energyWithGap` — full
     closure from combined hypothesis
   - `intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE_v2` — the
     PDE-facing theorem

2. Update `ShenWork.lean` — add import

## Key reference code to read

1. `P3MoserIntegratedClosure.lean:242` — `exists_pos_eps_mul_le_sub_of_coeff_gap`
   (converts `theta < p * A` to surplus form)

2. `P3MoserIntegratedClosure.lean:789-853` —
   `integratedHigherPowerEnergyWindowCoeffFrontier_of_LpBootstrapEnergyInequality`
   (the theorem to mirror)

3. `P3MoserIntegratedClosure.lean:1687-1777` —
   `higherPowerWindowCoeffFrontier_of_regularEnergy_coeffGap` and
   `intervalDomain_integratedMoserDissipationDropBefore_of_regularEnergy_coeffGap`
   (the downstream chain to mirror)

4. `P3MoserIntegratedDissipationPDE.lean` — the current (unsatisfiable) PDE theorem
   to mirror

## What the combined hypothesis looks like (fully spelled out)

```lean
def LpBootstrapEnergyInequalityWithGap
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ pExp, p0 ≤ pExp →
    ∃ A > 0, ∃ B > 0, ∃ K > 0, ∃ L,
      (∀ t, 0 < t → t < T →
        (1 / pExp) *
            deriv (fun τ => D.integral (fun x => (u τ x) ^ pExp)) t +
          A * D.integral (fun x =>
            (D.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) +
          B * D.integral (fun x => (u t x) ^ pExp) ≤
        K * D.integral (fun x => (u t x) ^ (pExp + rho)) + L) ∧
      (2 : ℝ) < pExp * A
```

## Rules

- 0 sorry, 0 custom axiom, 0 native_decide
- #print axioms = [propext, Classical.choice, Quot.sound]
- Do NOT modify existing files except ShenWork.lean (for import)
- Verify with `lake env lean ShenWork/PDE/P3MoserIntegratedDissipationPDEv2.lean`
- IMPORTANT: The body of `LpBootstrapEnergyInequality` is in
  `ShenWork/Paper2/Statements.lean:1095`. Read it EXACTLY to match the energy
  inequality terms. Use `D.integral` not `intervalDomain.integral` etc. in the
  abstract definition.

## Verification

```bash
lake env lean ShenWork/PDE/P3MoserIntegratedDissipationPDEv2.lean
# must show no errors
# #print axioms must show [propext, Classical.choice, Quot.sound]
```
