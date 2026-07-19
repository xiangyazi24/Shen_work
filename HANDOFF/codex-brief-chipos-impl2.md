# Codex Brief — χ>0 Whole-Line Rectangle Squeeze (Prop 1.2(2), Phase 2)

Prereq: phase 1 (codex-brief-chipos-impl1.md) delivered. Repo rules unchanged
(0 sorry, new files only, lake build gate, no commit).

Target: `Proposition12PositiveBranch` (Proposition12Assembly.lean:22-29) — the named
open positive branch of Paper 1 Prop 1.2: for 0 < χ < 1/2, m+γ−1 ≤ α,
PaperNonnegativeInitialDatum + UniformlyPositive u₀ ⇒ global solution with
`UniformConvergesToConstant u 1`. Phase 2 does the critical case α = m+γ−1 first;
the supercritical α > m+γ−1 extension is phase 3 (different ceiling).

## Item 0 (NEW, from phase-1 review): b^m-weighted floor comparison variant

Phase 1's `leftHalfLine_ge_of_positive_resolver_reaction_subsolution` uses a constant
defect H with `hpdeb : b' + H ≤ reaction(b)`. From a tiny seed floor (b ≈ d ≪ 1,
reaction(d) ≈ d) with H = O(1) this budget is unsatisfiable — the m=1 burn-in fails.
Add the weighted variant `leftHalfLine_ge_of_weighted_resolver_reaction_subsolution`:
replace hchem/hpdeb by
  hresolver : ∀ t x (slab, x < x₀), frozenElliptic p (q t) x ≤ Dup    (constant Dup)
  hpdeb     : ∀ t ∈ Ioc 0 T, deriv b t + p.χ * (b t)^p.m * Dup ≤ reactionFun p.α (b t)
and inside, at the touching point the solution value w satisfies w ≤ b t (the sliding
max-principle contradiction point has q below the barrier), so
  χ w^m (V − w^γ) ≤ χ w^m V ≤ χ w^m Dup ≤ χ (b t)^m Dup  (x^m monotone, w ≥ 0).
This makes the defect b-proportional and the exponential barrier
L − (L−C)e^{−λt} viable from arbitrarily small C with
λ = C·φmin/(L−C), φmin = min over [C,L] of ((1−x^α) − χ x^{m−1} Dup) > 0.
The ceiling side does NOT need a weighted variant (barrier values ≥ 1).

## Architecture: mirror the two existing one-sided whole-line chains

- FLOOR template: WholeLineCauchyLongTimeFloor.lean (χ≤0): slab exp-floor
  (`wholeLineSlab_ge_expFloor_of_nonpositive_resolver_pde` :20), mild fixed-point
  Ico/Icc transfer (:417/:553), step/restart (:609-648), global induction (:728),
  liminf (:764), convergence (:780).
- CEILING template: WholeLineCauchyChiPosLongTimeBound.lean (χ>0, done).
- Coupling: each squeeze round n has a rectangle [ℓₙ, Mₙ] valid eventually
  (∀ t ≥ Tₙ, ∀ x). Within a round:
  * ceiling slab for χ>0 with resolver LOWER bound hypothesis V ≥ ℓₙ^γ
    (whole-line uniform floor ⇒ frozenElliptic ≥ ℓₙ^γ: kernel mass 1; check for an
    existing lemma near frozenElliptic_le_of_rpow_le, Statements.lean:2811; add the
    ≥ mirror if missing — trivial from the same integral computation);
  * floor slab for χ>0 with resolver UPPER bound V ≤ Mₙ^γ
    (`frozenElliptic_le_of_rpow_le` exists).
  * CRITICAL: contact estimates keep the b^m factor:
    floor: χ b^m (b^γ − V) ≥ −χ b^m (Mₙ^γ − b^γ) for b ∈ [ℓₙ, target];
    ceiling: χ a^m (a^γ − V) ≤ χ a^m (a^γ − ℓₙ^γ) for a ∈ [target, Mₙ].
    Constant-in-b defects DO NOT work at small floors (m=1 burn-in fails).
- Round targets: choose ℓₙ₊₁, Mₙ₊₁ as near-roots of the coupled equilibrium
  inequalities so that the delivered bounds are exactly the hypotheses of
  `chiPos_squeeze_gap_step` (WholeLineChiPosSqueezeAlgebra.lean, committed b7790735):
    1 − ℓₙ₊₁^α ≤ χ ℓₙ₊₁^{m−1}(Mₙ^γ − ℓₙ₊₁^γ) + δ
    Mₙ₊₁^α − 1 ≤ χ Mₙ₊₁^{m−1}(Mₙ₊₁^γ − ℓₙ₊₁^γ) + δ
  with δ the barrier finite-time slack (choose δ = δₙ → 0 or fixed δ(ε) — pick
  whichever composes cleanly; the recurrence gives gapₙ ≤ (2χ)^n gap₀ + 2δ/(1−2χ)
  via `affine_recurrence_iterate_le`).
- Seed: round 0 from UniformlyPositive u₀ (global inf floor c₀ > 0):
  finite-time floor survival on the first slab (the floor template's exp-floor with
  crude resolver bound V ≤ G^γ gives ℓ₀ = εc₀-type floor; G = max(MChi p) ‖u₀‖ via
  wholeLineCauchyGlobal_le_max_of_chi_pos, committed). Ceiling seed M₀ from the same
  range bound; after a burn-in slab, M ≤ MChi + r via the existing limsup theorem.
  Sanity for m=1: φ(0) = 1 − χMₙ^γ ≥ 1 − χ(MChi+r)^γ > 0 for χ < 1/2 at critical
  exponent (χ·MChi^γ = χ(1−χ)^{−γ/α}; at m=1, γ=α: = χ/(1−χ) < 1) — prove this as a
  named lemma with the r-margin.
- Endgame: gapₙ < ε via `abs_sub_one_le_rpow_gap` ⇒ UniformConvergesToConstant u 1.

## Deliverables
1. Resolver lower-bound mirror lemma (if missing).
2. New file WholeLineChiPosRectangleSqueeze.lean: the two coupled slab comparisons
   + step/restart + round induction + `wholeLineCauchyGlobal_uniformConvergesToConstant_one_of_chi_pos_half`
   (hypotheses: 0 < χ, χ < 1/2, α = m+γ−1, ceiling regime, UniformlyPositive datum).
3. New file Proposition12PositiveBranchCritical.lean: package into the
   Proposition12PositiveBranch shape restricted to the critical case (state as its own
   theorem; the α > β case remains open for phase 3).
All with #print axioms, lake build green, imports appended to ShenWork.lean.
