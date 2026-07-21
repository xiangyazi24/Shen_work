# Theorems by paper and by number — SOURCE-VERIFIED status

Verified 2026-07-21 by reading the actual Lean source (three parallel source-only
audits, cross-checked; NOT read off PAPER_INVENTORY.md, which is stale and undersells
all three papers). Repo is **0 sorry, 0 axiom** (grep-verified; all "sorry" string hits
are docstrings asserting their own absence). `ShenWork` builds green (10004 jobs this
session; χ>0 stability axiom-audited clean-3). ~801K LOC, 2,119 files, ~5,550 theorems.

## The one structural fact you must read this table with

Every headline exists in **two layers**:
- an **abstract layer** — the literal paper statement quantified over *all* bounded
  domains (`Theorem_1_1 D p`, `Theorem_2_3 D p`, …). These are mostly **NOT proved**:
  the hard content is carried as *assumed package fields* (`…RawData`, `Paper3Constants`,
  frontier bundles), and the ∀-domain forms are *actively refuted* by obstruction lemmas
  (`not_forall_Theorem_…`). "Sorry-free" here means "reduced to an assumed hypothesis,"
  not "proved."
- a **concrete layer** — the faithful model on a specific physical domain
  (`intervalDomain`, `intervalDomainM`, `wholeLineCauchyGlobalU`). **This is where the
  genuine, unconditional PDE proofs are.**

Status marks: ✅ genuine proof · ✅◐ conditional on the standard hypotheses (wave exists
/ regularity / closeness) · ◐ only a branch or one regime real · ○ hard content assumed
(not proved) · ✗ original statement formally refuted.

---

## Paper 1 — Traveling waves on the line (Shen). **Core trilogy genuinely (largely) complete.**

| # | Item | Real status | Evidence |
|---|------|-------------|----------|
| Prop 1.1 | global existence + a-priori bounds, general datum | ○ assumed | `paper1_Proposition_1_1_of_frontierData`: existence+max-principle+bounds carried as frontier fields; only `u₀≡1` branch unconditional |
| Prop 1.2 | constant-state stability, uniformly-positive datum | ✅ genuine, unconditional | `Proposition_1_2.unconditional` — constructs the solution, arbitrary uniformly-positive `u₀` |
| **Thm 1.1** | **existence of the traveling wave** | ✅ **genuine, unconditional** | `Theorem_1_1.unconditional` (Rothe for χ≤0, Schauder for χ>0); non-vacuous witness χ=¼,c=3,`U(0)>0` |
| **Thm 1.2** | **asymptotic stability** | ✅◐ **conditional-proved, arbitrary `u₀`** | `…_chi_{neg,zero,pos}_natural` + `paper1_Theorem_1_2_paperDatum_of_chi_lt_half`: weighted-L²+uniform convergence; smoothing step *discharged*; assumes wave+regularity+tail+L²-closeness; **regimes χ<0, χ=0, 0<χ<½ (critical α=m+γ−1)**; non-vacuous (`…concrete_nonvacuous`, χ=¼). **[½, chiStar) OPEN.** |
| **Thm 1.3** | **uniqueness of the wave** | ✅◐ **conditional-proved** | `Theorem_1_3_amended_of_chi_lt_half` (+`_chi_nonpos`): uses the *proved* stability, does not assume Cauchy-uniqueness; χ≤0 and 0<χ<½ |
| Lem 2.1 | heat-semigroup L∞ estimates | ✅ | real whole-line kernel branches, `PDE/HeatSemigroup.lean` |
| Lem 2.2–2.4 | elliptic resolvent kernel / derivative / exp bounds | ✅ | `Lemma_2_{2,3,4}_direct` |
| Lem 2.5 | weighted small-weight resolvent estimate | ✅ | `lemma_2_5` (faithful small-weight form) |
| Lem 4.1 | upper-barrier supersolution | ✗→◐ | original **refuted** (`not_Lemma_4_1`); corrected away-from-interface version proved |
| Lem 4.2 | constant/lower subsolution | ✗→◐ | original **refuted** (`not_Lemma_4_2`); corrected χ=0 slices proved |
| Rmk 4.2 | finite-time trap | ✗→◐ | original + M=1 slice **refuted**; corrected χ=0 slices proved |
| Lem 5.1 / 5.2 / 5.3 | signal bound / log-deriv / weighted elliptic | ◐ | branches proved; arbitrary-wave cases open |

Note: the literal original `Theorem_1_2` def (weight `1/(1+|χ|^{1/6})`, no regularity) is
only closed via `of_assumed_stability_branch` (assumes the conclusion) or self-data (`u₀=U`,
vacuous). The genuine content is the "amended/natural" route above. Also `…amended_of_…Step4`
closes the full amended def but carries `hcore` = Henry semigroup smoothing as an assumption.

## Paper 2 — Boundedness & global existence, bounded domains (Chen–Ruau–Shen I)

Abstract ∀-domain forms are **obstructed** (`not_forall_Theorem_1_X`). Real proofs are on
`intervalDomain` (1-D).

| # | Item | Real status | Evidence |
|---|------|-------------|----------|
| Def 1.1 | classical solution | ✅ faithful def | `IsPaper2ClassicalSolution` — real PDE + Neumann BC |
| **Thm 1.1** | **global existence, χ₀≤0** | ✅ **genuine on intervalDomain, full χ₀≤0** | `paper2_chiNonpos` (unconditional; χ<0 + χ=0 both constructed). Abstract ∀-domain form obstructed |
| Thm 1.2 | global existence, weak cross-diffusion | ◐ partial + ✗ | only m=1 critical branch genuine (`…critical_branch_unconditional`); 0<m<1 branch **assumes its conclusion**; raw stmt **refuted** for a>0,b=0 (needs guard) |
| Thm 1.3 | global existence, strong logistic | ◐ slice only | only χ₀≤0, m=1 max-principle slice genuine (bypasses strong-logistic premise); real strong-logistic regime rests on an assumed frontier bundle |
| Lem 2.5 | scalar entropy inequality | ✅ | `Lemma_2_5_direct` + sharpness/attainment/full-range — fully proved from weighted AM-GM |
| Lem 2.1–2.4, 2.6–2.7, 3.1, 4.1; Prop 1.1, 2.1–2.5; Cor 2.1 | semigroup/energy estimates | ○ | target + obstruction (`not_forall_…`) or assumed; analytic proofs open |

## Paper 3 — Persistence & stabilization (Chen–Ruau–Shen II)

Abstract track: nonlinear conclusions **assumed** via bridges the source labels
*"TAUTOLOGY (no math content)"*; ∀-domain forms **refuted**. Concrete `intervalDomainM`
track: genuine unconditional proofs of faithful **eventual** reformulations.

| # | Item | Real status (abstract) | Real status (concrete intervalDomainM) |
|---|------|------------------------|----------------------------------------|
| **Thm 2.1** | uniform persistence | ○ assumed field; ∀-form refuted | ✅ `Theorem_2_1_corrected_intervalDomainM`, unconditional |
| **Thm 2.2** | linear stab/instab + local exp | ◐ linear/spectral **proved**; local-exp **assumed** | ✅ eventual form, unconditional |
| **Thm 2.3** | global stability, χ₀≤0 | ◐ linear proved; nonlinear assumed | ✅ eventual form, unconditional (~1000 lines real Gronwall/coercivity — strongest) |
| **Thm 2.4** | global stability, strong logistic | ◐ linear proved; nonlinear assumed | ✅ eventual form, unconditional (entropy + rectangle routes, all 4 branches) |
| **Thm 2.5** | global stability, minimal model | ◐ linear proved; nonlinear assumed | ✅ eventual form (entropy/signal-energy branches) |
| Def 2.1 | linear stability / Neumann spectrum | ✅ | per-mode critical χ* formula (2.10), χ*>0, spectral algebra — all real |
| Lem A.6 | power-difference inequality | ✅ | `Lemma_A_6_direct`, constant `C_{α,γ}`, sinh-convexity |
| Lem A.7–A.8 | threshold comparisons | ✅ (algebra) | proved inequalities feeding the linear branches |
| Lem 3.1 | uniform regularity | ✅ | from the global-solution package |
| Lem 3.2–3.5, 7.1, A.1 | compactness / continuity / resolvent / sectorial | ○ | assumed fields + obstruction lemmas |

Two caveats on the concrete Paper-3 track: the proofs are **eventual** (asymptotics from
some t₀>0, which the source explicitly distinguishes from the printed all-time statement),
and non-vacuity rests on small-data global existence in the linearly-stable regime.

---

## Honest one-paragraph summary

Read by the *concrete* layer (the faithful physical-domain models), the project is much
further along than the abstract ∀-domain statements suggest. **Paper 1**: existence
(Thm 1.1) is genuinely proved unconditionally; stability (Thm 1.2) and uniqueness (Thm 1.3)
are genuinely proved conditional on the standard "a wave exists + is regular + data is
close" hypotheses (which existence supplies), for χ<0, χ=0, and 0<χ<½ at the critical
exponent — the window [½, chiStar) is the open edge. **Paper 2**: the negative-sensitivity
global existence (Thm 1.1, χ₀≤0) is genuinely proved on the interval domain, as is the
scalar entropy Lemma 2.5; the weak-cross-diffusion and strong-logistic headlines are only
partially real (one branch each) and still rest on assumed analytic packages. **Paper 3**:
persistence and all four stability theorems (2.1–2.5) have genuine unconditional proofs of
faithful *eventual* forms on the concrete `intervalDomainM`, plus real linear-spectral
stability, the critical-χ* formula, and Lemma A.6 in the abstract layer; the abstract
arbitrary-domain nonlinear theorems themselves are assumed/obstructed, not proved.
In all three papers the abstract ∀-domain forms are deliberately obstructed
(`not_forall_…`) rather than proved — the genuine mathematics lives on the concrete models.
