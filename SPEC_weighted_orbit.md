# SPEC — Instantiate the weighted entropy engine for the real co-moving orbit

## Goal (unconditional bridge)
Instantiate the abstract `ChiOneWeightedEntropySlice` (from
`ShenWork/Paper1/WholeLineChiPosWeightedEntropyDissipation.lean`) for the ACTUAL
whole-line co-moving Cauchy orbit `wholeLineCauchyGlobalU p u₀` at each time `t`,
so `weighted_sharp_entropy_production_le` yields the sharp weighted dissipation
bound for the real solution. This bridges the new engine to the orbit; it is
unconditional (no floor needed at this stage — the floor only enters the later
sup-over-translates convergence step, which is NOT part of this spec).

## Location
NEW file `ShenWork/Paper1/WholeLineChiPosWeightedEntropyOrbit.lean`.
Import `WholeLineChiPosWeightedEntropyDissipation`. DO NOT edit existing files.

## CHECK-EXISTING FIRST (mandatory)
`grep -rn "WeightedEntropyOrbit\|weighted.*orbit\|ChiOneWeightedEntropySlice" ShenWork/`.
Also READ these to find the exact orbit regularity/PDE API you must feed the slice:
- `ShenWork/Paper1/WholeLineWeightedRegularitySlice.lean`
  (`wholeLineCauchyGlobalU_coMoving_contDiff_two_positive`,
   `wholeLineCauchyGlobalU_slice_contDiff_two_positive`)
- `ShenWork/Paper1/WholeLineWeightedRegularityCoMovingComparisonNatural.lean`
  (`wholeLineCauchyGlobalU_joint_hasFDerivAt_positive`)
- whatever lemma states the co-moving PDE that `wholeLineCauchyGlobalU` satisfies
  (grep `population_pde`, `IsGlobalCauchySolutionFrom`, the co-moving `u_t =` form).
Report the exact signatures you will use before building.

## Task
For the co-moving profile `U_t(x) = coMovingPath c (wholeLineCauchyGlobalU p u₀) t x`
(or whatever the co-moving spatial slice at time `t` is called in the regularity
lemmas — use the EXACT existing object), and a FIXED user-supplied positive
slowly-varying weight `w` on `[a,b]` (take `w, w'` as hypotheses with the same
`w_pos`, `w_deriv`, `w'_cont`, `w_slow` conditions as the structure — do NOT
invent a concrete `w`; keep it abstract so the caller supplies e.g. a sech
profile), produce:

```
theorem wholeLineCauchyGlobalU_weighted_sharp_dissipation
    (p : CMParams) (u₀ : WholeLineBUC) (hp : p.m = 1 ∧ p.γ = 1 ∧ p.α = 1)
    (a b ell : ℝ) (w w' : ℝ → ℝ) (t : ℝ)
    (hw_pos : ∀ x, 0 < w x) (hw_deriv : ∀ x, HasDerivAt w (w' x) x)
    (hw'_cont : Continuous w') (hw_slow : ∀ x, |w' x| ≤ (1/ell) * w x)
    (hab : a ≤ b) (hell : 0 < ell) :
    (∫ x in a..b, w x * chiOneEntropyMultiplier (<u at (t,x)>) * <u_t at (t,x)>)
      ≤ -(1 - p.χ^2/16) * (∫ x in a..b, w x * (<u at (t,x)> - 1)^2)
        + <the explicit (C/ell)(E+…) + resolver-correction + boundary terms
           exactly as in weighted_sharp_entropy_production_le> := by
  -- build the ChiOneWeightedEntropySlice record from the orbit's regularity:
  --   u_pos, u_deriv, ux_deriv, r_deriv, rx_deriv, uxx/rxx/ut continuity,
  --   population_pde, resolver_pde  — all from the existing orbit lemmas above.
  -- then `exact (theSlice).weighted_sharp_entropy_production_le (by …)`.
```
Fill `<u at (t,x)>`, `<u_t at (t,x)>`, `<r ...>` with the EXACT co-moving objects
the regularity lemmas provide (spatial derivatives `ux,uxx`, time derivative `ut`,
resolver `r,rx,rxx`). If the orbit's co-moving PDE has the drift `c` and the
`m=γ=α=1` reductions, discharge them from `hp`.

## If the PDE/resolver API is not directly available
If the orbit lemmas give regularity + positivity but NOT the pointwise co-moving
PDE in the exact `population_pde` shape, then:
- Locate the lemma that DOES give the PDE (the Cauchy solution definition
  `IsGlobalCauchySolutionFrom` almost certainly unfolds to it) and adapt.
- If genuinely no lemma provides the pointwise `ut = uxx + c·ux − χ(...) + u(1−u)`
  for the co-moving orbit, STOP and report exactly which PDE fact is missing and
  where the lab-frame vs co-moving-frame mismatch is — do NOT fabricate the PDE,
  do NOT insert sorry/axiom, do NOT assume it as a hypothesis to paper over.

## Hard rules
- 0 sorry / 0 axiom / 0 admit / 0 native_decide. Clean-3 only.
- `set_option maxHeartbeats 1000000` if needed.
- Verify with the single-file `lean` command (repo LEAN_PATH); paste the clean
  compile + `#print axioms wholeLineCauchyGlobalU_weighted_sharp_dissipation`
  showing `[propext, Classical.choice, Quot.sound]`.
- Line length ≤ 100.

## Acceptance
`wholeLineCauchyGlobalU_weighted_sharp_dissipation` compiles clean-3, added to
`ShenWork.lean` closure (imports the dissipation file). Report the axioms output
verbatim, and report the exact orbit PDE/regularity lemmas you consumed.
