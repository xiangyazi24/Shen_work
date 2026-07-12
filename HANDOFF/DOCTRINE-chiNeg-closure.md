# DOCTRINE — χ<0 closure (2026-07-11, automode)

## Goal (one sentence)
Make `paper2_chiNeg` UNCONDITIONAL and axiom-clean by discharging the two remaining
V6 producer gaps, so the interval-domain χ₀<0 Theorem 1.1 holds with no hypothesis
structure carried.

## Ground truth (verified today)
- hcontr_grad REMOVED (3cce40b1); full uisai2 cold build green, 9207 jobs, 0 sorryAx.
- Unconditional positive-time Lipschitz floor is now available upstream.
- `paper2_chiNeg_v6` (IntervalChiNegV6Assembly.lean) is 0-sorry, axiom-clean, CONDITIONAL on
  `UniformTruncatedV6AssemblyInputs p + HSpectral`.

## The two gaps (what "unconditional" needs)
1. **energy** — field `energy : UniformTruncatedEnergyDataV6 p` / consumer wants
   `TruncatedNegativePartEnergyCoreRegularData p HT.toData`. Route A: FTC coefficient ODE +
   truncated-source C0 (truncated source is continuous / 1-Lipschitz). Negative-part weak-energy
   identity → Gronwall → nonnegativity.
2. **HSpectral** — `BFormMildSpectralBootstrapData` (4 fields): hResolverPos ✅;
   hResolverData (DuhamelSourceTimeC1 witness) ⚠; hTimeNhd ⚠ (⊆ hPdeAgreement);
   hPdeAgreement (ℓ¹ ladder + source identity + Fourier data) ⚠.

## Avenues (ranked)
- **(a) PRIMARY — V6 producer discharge.** Build unconditional producers for energy + HSpectral,
  feed `paper2_chiNeg_v6`. Fewest, best-scoped gaps; V6 already eliminated fullAgreement.
- **(b) FALLBACK — V5 self-contained.** Close the 5 sorries in IntervalChiNegV5SelfContained
  (+1 TestedSpectral): fullAgreement (easiest, pure induction), energy_continuous / energy_has_deriv
  (ChatGPT code exists), jensenStrictPosData, spectralData (hardest).
- **(c) HYBRID.** Take whichever sub-lemmas are furthest along from (a)/(b); the jensen + spectral
  leaves are shared between routes.

## Terminal conditions
- SUCCESS: an unconditional `paper2_chiNeg` (no assumption structure) verifying green cold on uisai2
  with `#print axioms` = only propext/Classical.choice/Quot.sound (no sorryAx).
- Per-gap failure verdict: a written proof that a producer cannot be built without a genuinely
  missing analytic fact (name it), not "hard".

## Division of labor
- Codex (tmux window 6 / `codex exec`): heavy proof grinding of the producer leaves.
- ChatGPT tabs: analysis routes (weak-energy identity, ℓ¹ summability, DuhamelSourceTimeC1).
- Me: gap mapping (Explore agents), doctrine, dispatch, verification, assembly, easy leaves (fullAgreement).

## Fixed rules
- Do NOT re-derive existing producers (check-before-build; many *Spectral*/*Provider* files exist).
- Verify each milestone: lake env lean single-file + cold uisai2 for assembly-level.
- No local `lake build` (hook-blocked); uisai2 for full build.
