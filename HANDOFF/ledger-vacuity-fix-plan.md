# Ledger vacuity fix — complete conversion plan (reverse-engineered 2026-06-06)

GOAL: make LimitRegularityInputs / ReducedLimitRegularityInputs satisfiable
(currently provably False: global `ContDiff ℝ 2 (intervalDomainLift (D.u σ))`
⊥ `hpost` endpoint positivity, because the 0-extension can't be globally C²).

## Key discovery
The decay machinery is ALREADY one-sided-clean:
- `IntervalWeakH2Neumann f` (IntervalMildSourceDecayHelper.lean) = abstract
  {secondDeriv, integrable, bound, weak_cosine_laplacian IBP identity over [0,1]}.
- `intervalWeakH2Neumann_of_contDiffOn` ALREADY takes
  `ContDiffOn ℝ 2 g (Icc 0 1)` + one-sided `Tendsto (deriv g) 𝓝[>]0/𝓝[<]1 (𝓝 0)`
  + `deriv g 0 = 0`, `deriv g 1 = 0`. (hbc0/hbc1 ARE used: passed to
  `intervalCosineLaplacianCoeff_eq_of_contDiffOn`.)
- `powerSource_intervalWeakH2Neumann` (same file) already does νu^γ — relevant to Hvsrc.

So global C² is used ONLY in the CONSTRUCTION layer that feeds this. Convert that.

## DESIGN: thread (ContDiffOn-Icc + F's one-sided facts) as HYPOTHESES up the chain
Avoids the wall that F's two-sided `deriv F 0 = 0` is unprovable for abstract
ContDiffOn-Icc g. Pass the facts through; they become satisfiable LEDGER FIELDS
(genuine Neumann limits of the real solution; `deriv F 0 = 0` is junk=0, true
for the 0-extension via deriv_zero_of_not_differentiableAt at the jump).

### Lemma-by-lemma (IntervalMildPicardRegularity.lean unless noted)
1. `logisticSourceFun_contDiffOn_Icc` (l.105): input `ContDiff ℝ 2 g` →
   `ContDiffOn ℝ 2 g (Icc 0 1)`. Body:
     unfold logisticSourceFun; ContDiffOn.mul hg;
     ContDiffOn.sub contDiffOn_const;
     (hg.rpow_const_of_ne (fun x hx => ne_of_gt (hpos x hx))).const_smul b
   (ContDiffOn.rpow_const_of_ne EXISTS — used at l.91.)
2. `logisticSourceFun_intervalWeakH2Neumann` (l.257): make it a PASSTHROUGH —
   take hgC2:ContDiffOn-Icc, hpos, htend0/htend1 (F's one-sided), hbc0/hbc1
   (F's deriv-zero), return `intervalWeakH2Neumann_of_contDiffOn
   (logisticSourceFun_contDiffOn_Icc hgC2 hpos) htend0 htend1 hbc0 hbc1`.
   DELETE the internal logisticSourceFun_tendsto_deriv_* / _deriv_zero_at_* uses.
3. The g→F derivation lemmas (`logisticSourceFun_tendsto_deriv_left/right` l.201/229,
   `logisticSourceFun_deriv_zero_at_zero/one` l.115/158): RE-STATE for the
   0-extension case — add hyp `hgext : ∀ x, x ∉ Icc 0 1 → g x = 0` + ContDiffOn-Icc
   + g's one-sided Neumann; OR drop them and require F-facts at the ledger.
   (For the lift these hold; deriv F endpoint = 0 via jump non-differentiability.)
4. Thread the new hyps through callers: l.279 (decay), l.314, l.665, and
   IntervalLogisticSourceQuantBound.lean l.286 (set hf), l.237/274 (integral+decay
   lemmas gain htend/hbc hyps), → logisticSource_duhamelSourceTimeC1.
5. `secondDeriv_eq_F2` (IntervalLogisticSourceQuantBound l.118): uses
   `exists_pos_neighborhood_of_compact_positive hg.continuous` (OPEN nbhd, needs
   global). Re-prove for x ∈ Ioo(0,1): ContDiffOn-Icc ⟹ ContDiffAt at interior x;
   the integral_mono_on only needs the bound a.e. on (0,1) (endpoints measure 0).
6. CONSUMERS (the named 2): `limitSource_duhamelSourceTimeC1`
   (IntervalPicardLimitSourceData l.169) + `Hu_of_restart`
   (IntervalPicardLimitTimeNhd l.~) — hypotheses
   `∀ σ, ContDiff ℝ 2 (lift (w σ))` → `ContDiffOn ℝ 2 (lift (w σ)) (Icc 0 1)`,
   add the one-sided Neumann tendsto + deriv-zero hyps, thread to the decay chain.
7. LEDGER (LimitRegularityInputs, ReducedLimitRegularityInputs): hC2t global →
   ContDiffOn-Icc; ADD fields: htend0t/htend1t (one-sided deriv limits of the
   logistic source of lift(D.u σ)) and the F deriv-zero facts (or g's). Keep
   hN0t/hN1t (`deriv (lift) 0/1 = 0`, junk=0, still valid). Update wiring
   frontierCore_of_inputs / weakSource_of_reduced / Hu_of_reduced to pass them.
8. M3 iterate `IntervalPicardIterateSourceC1` l.~ — same hypothesis retype +
   threading (mirror of the limit case).

## Verification
ONLY uisai1 (mini has no oleans, can't build). Build bottom-up, refreshing each
olean: `lake env lean -o ...olean file.lean`. BLOCKED while codex + rfl-build
lake run (clobber/cache-corruption risk). Run when uisai1 idle.
Audit after: `#print axioms` + re-run the vacuity False-proof (must now FAIL to
typecheck = structure satisfiable).

---

## UPDATE (2026-06-06): ADDITIVE ADAPTER LANDED — the right fix, no shared edits

The retype-the-shared-structures approach was abandoned (cascades + breaks the
auto-pushed shared main). New working approach per Xiang: ADDITIVE adapters that
consume the COSINE REPRESENTATION instead of the unsatisfiable global-C²-of-lift.

KEY: the restart cosine representation gives `lift w =ᴵᶜᶜ (x ↦ ∑ₙ bₙ cos(nπx))`,
and the cosine series IS genuinely globally C² (`cosineCoeffSeries_contDiff_two`,
from `∑ₙ λₙ|bₙ| < ∞`). That series is the honest global-C² witness (the role the
clamp was meant to play — and it's truly C², not the clamp's mere C¹). Feed it to
the EXISTING global-C² constructors, transfer to the lift via [0,1]-agreement.

LANDED (axiom-clean, verified via single-file `lake env lean` on uisai1 — safe,
read-only, no interference with codex; committed + pushed):
- `ShenWork/Paper2/IntervalDomainLogisticWeakH2Adapter.lean`:
  * `IntervalWeakH2Neumann.congr_on_Icc` — transfer the weak certificate across
    [0,1]-agreement (it uses f only via ∫₀¹cos·f).
  * `logisticSource_intervalWeakH2Neumann_of_eigenvalue_summable` — logistic
    source `u(a−bu^α)` weak-H² from (eigenvalue-summable coeffs + EqOn-Icc repr +
    positivity). NO global-C² of lift.
  * `logisticSource_cosineCoeff_quadratic_decay_of_representation` — the |ĉₖ| ≤
    C/(kπ)² decay corollary.

ALREADY PRESENT (power source νu^γ, mirror — discovered in
IntervalMildSourceDecayHelper.lean):
- `intervalWeakH2Neumann_of_eigenvalue_summable` (same recipe, junk-deriv route
  works there since νu^γ>0 strictly at endpoints).
- `powerSource_cosineCoeff_quadratic_decay_of_chain_rule`.

NEXT: build representation-based DuhamelSourceTimeC1 producers (logistic + power)
using these decay results + the K1 time-C¹ data, additively; then a
representation-based `limitSource_duhamelSourceTimeC1` / `Hu` / the ledger fields
restated to carry the cosine representation (`hagree` + summable coeffs) instead
of `hC2t` global. The ledger then becomes SATISFIABLE (the real restart rep
supplies hagree) — all additively, no breaking edits to the shared chain.

---

## UPDATE (2026-06-06): adapter layer COMPLETE — Hvsrc dischargeable from representation

`ShenWork/Paper2/IntervalDomainLogisticWeakH2Adapter.lean` now contains the full
additive adapter layer (all axiom-clean, verified via single-file `lake env lean`
on uisai1, committed + pushed origin+uisai1):

  1. `IntervalWeakH2Neumann.congr_on_Icc` — weak-cert transfer across [0,1]-agreement.
  2. `logisticSource_intervalWeakH2Neumann_of_eigenvalue_summable` — logistic weak-H²
     from cosine representation.
  3. `logisticSource_cosineCoeff_quadratic_decay_of_representation` — logistic decay.
  4. `logisticSource_duhamelSourceTimeC1_of_representation` — logistic
     `DuhamelSourceTimeC1` from representation (swaps hC2/hN0/hN1 for hbsum/hagree/hpos).
  5. `powerSource_duhamelSourceTimeC1_of_representation` — power `νu^γ` version.
  6. `resolverSourceCoeff_re_eq_cosineCoeffs` — bridge
     `(intervalNeumannResolverSourceCoeff p u k).re = cosineCoeffs (νu^γ) k`.
  7. `resolverSource_duhamelSourceTimeC1_of_representation` — produces the EXACT
     ledger `Hvsrc` shape
     `DuhamelSourceTimeC1 (fun s k => (intervalNeumannResolverSourceCoeff p (w s) k).re)`
     from the cosine representation. **Hvsrc is now dischargeable from satisfiable
     data (the restart cosine representation), with NO global-C² of the lift.**

Engine throughout: the cosine series `∑ₙ bₙcos(nπx)` from the restart representation
IS genuinely globally C² (`cosineCoeffSeries_contDiff_two`); feed it to the existing
global-C² constructors, transfer to the lift via [0,1]-agreement.

### Remaining to a fully satisfiable χ₀=0 ledger
- `Hvsrc` — DONE (adapter #7 above; the ledger field can be filled from the slice's
  cosine representation + K1 time-C¹ data the ledger already carries).
- `Hvpos` — resolver strict positivity `0 < mildChemicalConcentration`. Route from
  earlier scoping: source `νu^γ ≥ c₀ = ν·m^γ` ⟹ `R(u) ≥ c₀/μ` (spectral
  decomposition / heat-Laplace lower bound). Additive, standalone.
- `HsupNorm` — sup-norm max principle on D.u (mirror of MinPersistence min-principle).
- `hpde_u` — spectral→pointwise PDE bridge (the hardest).
- Then: a new SATISFIABLE ledger struct carrying per-slice cosine representations
  (hbsum+hagree) instead of `hC2t` global; fill its source field via adapter #7;
  re-run the vacuity False-proof (must FAIL = satisfiable); re-thread
  `paper2_theorem_1_1_chiZero_*` onto it.
