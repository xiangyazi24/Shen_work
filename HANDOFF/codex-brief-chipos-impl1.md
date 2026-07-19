# Codex Brief — χ>0 Squeeze Implementation Phase 1

Repo ~/Shen_work, HEAD 7ea4d1db + your uncommitted WholeLineCauchyChiPosRangeBound.lean
(verified green, keep it). Your design HANDOFF/codex-chipos-squeeze-design.md is ADOPTED
with primary hypothesis χ < 1/2 (decision recorded in HANDOFF/fable-chipos-lefteq-design.md).
Rules: 0 sorry, 0 axiom, new files only, `lake build ShenWork.Paper1.<Module>` green before
claiming each item done. Do NOT commit.

Implement items 1–3 of your §7 list, in dependency order:

## Item 1 — new file ShenWork/Paper1/WholeLineHalfLineResolverUpperNatural.lean
`frozenElliptic_upper_of_left_halfLine_ceiling`:
for x ≤ x₀, if 0 ≤ u ≤ G everywhere and u ≤ M on (−∞, x₀+R], then
  frozenElliptic p u x ≤ (1 − τ)·M^γ + τ·G^γ  where τ = exp(−R)/2
(state it in the same style as `frozenElliptic_lower_of_left_halfLine_floor`,
WholeLineWeightedRegularityHalfLineResolverLowerNatural.lean:23-30; reuse its kernel-mass
split at :43-59 — do not re-derive the Psi analysis).
Also the combined pinching corollary (both bounds under both hypotheses).
If the exact constant arrangement (1−τ)M^γ + τG^γ is awkward, the weaker
M^γ + τ·G^γ is acceptable — it is what the H± budgets actually consume.

## Item 2 — new file ShenWork/Paper1/WholeLineChiPosTargetCeilingNatural.lean
Scalar dual of chiZeroKPPFloor (WholeLineWeightedRegularityChiZeroKPPFloorNatural.lean:19-104):
  chiPosTargetCeiling (Ahat D lam : ℝ) (t : ℝ) : ℝ := Ahat + (D − Ahat) * Real.exp (−lam * t)
with lemmas: value at 0 = D; range Ahat ≤ ceiling ≤ D (for Ahat ≤ D, t ≥ 0); hasDerivAt;
tendsto Ahat; restart identity (mirror wholeLineCauchyChiPosCeiling_restart);
and the defect-budget lemma (your §4 upper-barrier chain):
  chiPosTargetCeiling_deriv_ge_reaction_add_defect :
  for 1 < Ahat ≤ b ≤ D, Hplus < Ahat*(Ahat^α − 1), lam = (Ahat*(Ahat^α−1) − Hplus)/(D−Ahat+1):
  deriv ceiling ≥ ceiling*(1 − ceiling^α) + Hplus  (pointwise, at each t ≥ 0)
plus the rate-positivity lemma (mirror chiNegKPPFloorRate_pos). Use rpow throughout
(α : ℝ), matching reactionFun conventions.

## Item 3 — new file ShenWork/Paper1/WholeLineChiPosBufferedComparisonNatural.lean
The two generic buffered half-line comparisons for χ>0, template =
`leftHalfLine_ge_of_buffered_nonpositive_resolver_reaction_subsolution`
(WholeLineWeightedRegularityChiNegBufferedHalfLineComparisonNatural.lean:27-66, proof
through :466) and the scalar half-line maximum theorem
(WholeLineWeightedRegularityHalfLineMaximumNatural.lean:353-377, χ-free):

(a) `leftHalfLine_ge_of_buffered_chiPos_floor`: hypotheses = continuity, range
  [0,G] global, [ℓ, M] on (−∞, x₀+R] slab, buffer floor bminus ≤ q on [x₀,x₀+R],
  init floor at t=0, PDE (nondivergence form as in ChiNegLeftEquilibriumNatural.lean:31-41),
  hchi_pos : 0 < p.χ, and the Hminus budget with
  Hminus = χ*M^m*((M^γ−ℓ^γ) + τ*(G^γ−M^γ)) — your §3 lower-contact inequality:
  at contact q = b ∈ [ℓ,M]: χ*b^m*(b^γ−V) ≥ −Hminus via the resolver LOWER bound
  (frozenElliptic_lower_of_left_halfLine_floor). Conclusion: floor barrier
  chiZeroKPPFloor stays below q on (−∞, x₀] for the slab.
(b) `leftHalfLine_le_of_buffered_chiPos_ceiling`: mirror with the resolver UPPER bound
  (Item 1) at contact q = a: χ*a^m*(a^γ−V) ≤ Hplus = χ*M^m*((M^γ−ℓ^γ) + τ*ℓ^γ),
  ceiling barrier from Item 2, conclusion q ≤ ceiling on (−∞, x₀].

Mind the sign bookkeeping: for χ>0 the chemotaxis PDE term is +χ q^m (q^γ − V)
in the nondivergence expansion — derive your contact inequalities from the exact
repository expansion, do not assume my sign convention; verify against
paperWaveOperator_fixedPoint_eq_bufferedForm_of_pos
(ChiNegLeftEquilibriumNatural.lean:31-63).

Deliverables: 3 files building green with #print axioms sections, +imports appended to
ShenWork.lean. Report per-item status precisely; if an item is blocked, say exactly where
and leave the others green.
