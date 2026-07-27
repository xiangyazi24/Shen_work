# Errata to the chemotaxis–logistic trilogy, found by formalization

The Lean 4 formalization uncovered several printed statements that are **false or overstated**
for the papers' own data class. Each is *formally refuted* in Lean (a machine-checked
counterexample or impossibility theorem), and a **faithful corrected form is proved**. Per the
project's rule, correcting a wrong printed statement counts as completing it. Axiom audits use
exactly the standard classical axioms `[propext, Classical.choice, Quot.sound]`.

## Paper 1 (whole-line traveling wave)

- **Lemma 4.1 (upper-barrier supersolution).** The printed statement is **false**:
  `not_Lemma_4_1` (`Paper1/Statements.lean`) — the positive/negative hypotheses in fact *force*
  `m·κ ≤ 1` / `γ·κ < 1`, which the intended regime violates. Refuted at the interface via
  `not_differentiableAt_upperBarrier_of_interface` (the barrier is not `C¹` across the interface).
  **Corrected:** the away-from-the-interface supersolution
  (`Lemma_4_1_strengthened_away_from_interface_direct`, both sign branches) is proved.
- **Lemma 4.2 (constant / lower subsolution).** Printed statement **refuted**: `not_Lemma_4_2`
  (and `paper1_lower_subsolution_gap_not_Lemma_4_2 : ¬ Lemma_4_2`); the χ=0 hypotheses force
  `κ̃ ≤ 2κ`, `D ≥ 1`, incompatible with the claim. **Corrected:** the χ=0 slice form is proved.
- **Remark 4.2 / constant-subsolution threshold.** `not_constantSubsolutionThreshold_implies_frozen_smallness`.
- **Lemma 2.1 (∀-domain form).** `not_forall_Lemma_2_1` — the fully-universal statement fails;
  the faithful concrete form holds.

## Paper 2 (bounded interval, mild / linear flux)

- **Theorem 1.2 (raw guard).** The printed statement is **refuted for `a>0, b=0`**; the correct
  guard is `a=0 ∨ 0<b`. `Theorem_1_2_intervalDomain_unconditional` proves the corrected form.
- **Theorem 1.3 (frontier data).** The printed `FrontierData` is **not constructible**:
  `not_IntervalDomainTheorem13FrontierData_of_real_regime` (its `hGN` / `hglobalExtension` fields
  are false in the real regime). **Corrected:** `Theorem_1_3_intervalDomainM_from_minimal_honest_residual`
  carries only the paper's genuine case-(iv) gap; case-(iv) is then closed for `m≥1`
  (`..._caseIV_with_paperConstants`) and `m<1` (`..._of_m_lt_one`), the latter noting the printed
  theorem gates its global conjunct on `1≤m`, so for `m<1` its whole content is the bounded local
  branch (`Theorem_1_3_intervalDomainM_caseIVGuardCounter` is the audit's guard counterexample,
  which nonetheless satisfies the printed Theorem 1.3).
- **Lemma 2.7.** As literally stated it is **FALSE**: `not_Lemma_2_7_intervalDomain` (explicit
  counterexample `u = t⁻¹`). **Corrected:** `Lemma_2_7_intervalDomain_from_continuous_bound`.
- **Lemma 2.6.** The abstract L^p-bootstrap is circular with the L∞ bound for arbitrary `u`;
  the faithful closed-`[0,T]` L^p-mass continuity form `Lemma_2_6_intervalDomain_from_continuous_lp_bounds`
  is proved (not the printed L∞ bound).

## Paper 3 (bounded interval, nonlinear u^m flux)

- **Theorems 2.1–2.5, "all-time" C¹ decay.** The printed **all-time** decay is a **short-time
  regularity overstatement** — FALSE for the paper's data class (`u₀ ∈ C(Ω̄)`, `inf u₀ > 0`, but
  not `C¹`): there is an immediate cusp and only `t^{-1/2}` parabolic smoothing. The faithful
  renderings are the **eventual** forms (from any `t₀ > 0`), which are the proved headlines
  (`intervalDomainM_Theorem_2_{1..5}_...Eventual...`). All-time should not be pursued.
- **Theorem 2.1 (Part 1).** The printed Part 1 omits a reaction guard; the corrected form
  `Theorem_2_1_corrected_intervalDomainM` adds it (and supplies physical positive-time mass for
  Part 4).

## Beyond the printed papers (sharp-limit findings, not errata per se)

- **Far-left stability threshold.** The papers state stability near `χ*≈1`; the sharp threshold is
  `χ = 4`, and **unconditional far-left `χ<4` is false** (convective-escape counterexample) — the
  basin/closeness hypothesis is necessary. See `research_notes/FARLEFT_CHI4_RESOLUTION.md`.
- **General-m minimal stability.** Global stability is **false for `m ≳ 2.9` at large `χ₀`**
  (subcritical steady pattern); the sharp divider is a bifurcation threshold, not the `m=2`
  energy-method limit. See `research_notes/GENERAL_M_STABILITY_RESOLUTION.md`.

The repository README lists the public headline results and their principal Lean entry points.
