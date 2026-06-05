# DESIGN_ROUND5_CODEX.md

## Verdict

Accept the Round 4 consensus gap list.

I do not see a mathematical showstopper in G0-G7, assuming the target theorem is
the current gamma-ge-one route used by the existing resolver/local-existence
infrastructure. The line estimate `1580-2630` is plausible as an engineering
estimate, but only if G2/G3/G4 are developed in the right order and no missing
uniqueness/gluing theorem has to be built from scratch.

## Final Concerns

### C1. "No showstopper" should mean "no known obstruction", not "low risk"

G2, G3, and G4 remain high-risk formal analysis work. The consensus is correct
that they are well-defined; it does not make them routine. In particular, G4's
`hpde_u` and joint time-derivative continuity can easily exceed the estimate if
the existing `GradientMildClassicalRegularityFrontierData` fields do not align
with the spectral Duhamel lemmas.

### C2. G2/G3 must be staged to avoid circular proof dependencies

Round 4 correctly says G2 and G3 are entangled. The implementation should not
let `DuhamelSourceTimeC1` depend on the final gradient-to-standard conversion
that itself depends on `DuhamelSourceTimeC1`.

The clean staging is:

1. Prove Picard iterate time differentiability directly from the Picard map.
2. Prove resolver time differentiability from spectral algebra and chain rule.
3. Build total-source `DuhamelSourceTimeC1`.
4. Then prove gradient-to-standard IBP and spectral agreement.

If this staging fails, G2/G3 becomes the main place where the estimate breaks.

### C3. G7 hides a possible uniqueness/gluing sub-gap

The restart-before-end argument is standard, but Lean still needs an overlap
uniqueness or locality theorem strong enough to glue the old and restarted
classical solutions. If the existing code only has existence and a-priori
bounds, this becomes an extra sub-gap under G7.

I would not call this a showstopper, but it is the final risk I would audit
before starting G7.

### C4. Gamma scope must be kept explicit

The consensus route is credible for `1 <= gamma`. If the final Paper2 Theorem
1.1 is intended to cover `0 < gamma < 1`, then the resolver chain rule and
Lipschitz bounds near zero are not resolved by G1a. That would be a separate
real analysis problem, not wiring.

## Final Position

Accept G0-G7 as the final working design.

No additional top-level gap is needed. The only additions I would record are:

- a G3 staging note: prove time differentiability before spectral conversion;
- a G7 sub-gap audit: verify overlap uniqueness/gluing already exists;
- an explicit theorem-scope note: this plan is for the gamma-ge-one route unless
  the statement is deliberately strengthened.
