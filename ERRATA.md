# Errata and statement audit for the chemotaxis–logistic trilogy

The detailed public record is [`ERRATA.pdf`](ERRATA.pdf), with source in
[`ERRATA.tex`](ERRATA.tex). It gives the original claim, the calculation or
counterexample, the corrected form, and the exact Lean certificates.

The audit distinguishes four outcomes:

- **False statement:** the printed hypotheses admit an explicit counterexample.
- **Proof gap:** a printed step is invalid, but no counterexample to the conclusion is claimed.
- **Clarification:** the intended result needs a maximal-continuation or positive-time formulation.
- **Lean-interface issue:** an earlier formal definition was stronger than the paper; its refutation
  is not a paper erratum.

The project is pinned to Lean 4.30.0 / Mathlib v4.30.0. The cited headline
certificates are `sorry`-free and use only
`[propext, Classical.choice, Quot.sound]`.

## Traveling-wave paper

- **Theorems 1.2–1.3 — proof gap and corrected weight window.** The Section 5
  coefficient satisfies `q(κ)=Aκ+B>0`, so the written argument does not prove
  decay for every `η>κ`; it proves the corrected range above the perturbed
  lower root. The printed laboratory weight differs from the co-moving weight
  by `exp(2ηct)`, the displayed decay factor has the wrong sign, and four
  coefficient estimates require correction. The corrected headline theorems
  quantify over the repaired root window.
- **Lemma 4.2(2) — false as written.** A continuous trap-set profile with an
  interior zero makes the frozen elliptic response positive there. For a
  permitted positive sensitivity, the printed constant `d` has strictly
  negative frozen operator and is not a subsolution. Lean:
  `not_Lemma_4_2`. A valid repair adds pointwise or uniform control of the
  frozen elliptic forcing; the repository proves several such strengthened
  forms.

`not_Lemma_4_1`, `not_differentiableAt_upperBarrier_of_interface`, and
`not_forall_Lemma_2_1` are **not** paper refutations: the corresponding Lean
interfaces omitted printed hypotheses or quantified over fabricated abstract
semigroup data.

## Part I: boundedness and global existence

- **Theorem 1.2 — false for `a>0, b=0`.** The spatially constant solution
  `u(t)=c exp(at)`, `v=(ν/μ)u^γ` is global and unbounded. The corrected guard is
  `a=0 ∨ b>0`. Lean:
  `not_Theorem_1_2_intervalDomain_of_a_pos_b_zero`; corrected headline:
  `Theorem_1_2_intervalDomain_unconditional`.
- **Theorem 1.3(iv) — proof gap.** The proof invokes Proposition 2.2 at
  `s(P)=(P+α)/γ`, which requires `P>2-2m`. Its seed
  `q*=max{1,Nα/2}` need not satisfy this. The concrete admitted tuple
  `N=1, m=1/4, γ=7/2, α=2, β=1` has `s(q*)=6/7`. The formalization records the
  proof-supported guard and also closes the printed one-dimensional conclusion
  by a separate `m<1` analysis.
- **Proposition 1.1 — maximal-continuation clarification.** The finite endpoint
  alternative belongs to the distinguished maximal continuation, not to every
  arbitrary finite local witness. The corrected endpoint-tail version is
  `correctedProposition_1_1_intervalDomainM`.
- **Lemma 2.7 — false without initial-endpoint control.** The interior function
  `u(t,x)=t⁻¹` satisfies the required differential inequality on `(0,1)` but is
  unbounded at `t=0`. Lean: `not_Lemma_2_7_intervalDomain`; corrected:
  `Lemma_2_7_intervalDomain_from_continuous_bound`.

The old `FrontierData` nonconstructibility result and the abstract Lemma 2.6
frontier are Lean-interface findings, not independent counterexamples to the
paper.

## Part II: persistence and stabilization

- **Theorem 2.1(1) — false for `a=0<b`.** The constant solution
  `u(t)=(c⁻ᵅ+αbt)⁻¹/ᵅ`, `v=(ν/μ)u^γ` is global, bounded, and positive, but tends
  to zero. Lean: `not_Theorem_2_1_part1_intervalDomain_pureDecay`; corrected:
  `Theorem_2_1_corrected_intervalDomainM`.
- **Theorems 2.2–2.5 — all-time `C¹` overstatement.** The shared estimate
  (2.12) is required at `t=0`, although the data are merely continuous or
  `L∞`-small. On `(0,1)`,
  `u₀,N=u*+N⁻¹ᐟ² cos(Nπx)` is small in `L∞` but has unbounded `C¹` norm.
  The faithful statements are all-time decay from a strong fractional norm,
  or eventual `C¹` decay after a positive smoothing time. The repository's
  public headlines use the eventual form.

## Beyond the papers

The sharp-limit results are separate from the errata:

- [`research_notes/FARLEFT_CHI4_RESOLUTION.pdf`](research_notes/FARLEFT_CHI4_RESOLUTION.pdf)
- [`research_notes/GENERAL_M_STABILITY_RESOLUTION.pdf`](research_notes/GENERAL_M_STABILITY_RESOLUTION.pdf)

Their Markdown summaries and LaTeX sources are in the same directory.
