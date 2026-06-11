# SHEN_WORK ROADMAP — Paper 2 (Chen–Ruau–Shen) proof status + attack plan

Built 2026-06-11 from an independent read-only inventory + paper2.pdf §2–3 +
clean-tree certification. Verdict labels: FAITHFUL / CONDITIONAL / FRAGMENT /
IMPOSTOR / MISSING / REFUTED. All "positive" content is on `intervalDomain` =
`Subtype (Icc 0 1)` — **N = 1**; the general `BoundedDomainData` (N-general)
forms of all three theorems are REFUTED (`not_forall_*`).

## Honest one-line state
**Zero of the three main theorems (1.1, 1.2, 1.3) is proved**, even at N=1.
Genuinely-closed faithful pieces: **Lemma 3.1 (max principle, N=1)**, **Lemma 2.5
(algebraic)**, and the **PDE foundation toolkit** (heat kernel Lᵖ, GN, Agmon,
Poincaré, sectorial resolvent). The χ₀=0 Theorem 1.1 is the only main theorem
within reach; it is a 5-axis FRAGMENT (χ₀=0 / N=1 / a,b>0 / 1≤α / 1≤γ) and still
CONDITIONAL on the open `hsrc0` residual + an uninhabited provider core.
~173 sorrys remain in the (incomplete) attempts to discharge those conditions —
NOT in the conditional capstone's own closure (which is axiom-clean, certified).

## Status table

| Paper result | Lean (file:line) | Verdict | Gap |
|---|---|---|---|
| Thm 1.1 general Ω⊂ℝᴺ | Statements:4342; not_forall:4360 | **REFUTED (abstract)** | N-general form false on degenerate domains → forces N=1 |
| Thm 1.1 χ₀=0 (best) | ChiZeroCoreProvider:926 `..._unconditional` | **FRAGMENT + CONDITIONAL** | χ₀=0 (decoupled, not chemotaxis), N=1, a,b>0, 1≤α,1≤γ; conditional on Hiter+HWdata → `hsrc0`. Axiom-clean (no sorryAx). |
| Thm 1.1 χ₀=0 "final" | ChiZeroFinal:225 `..._final` | **CONDITIONAL (premise ~unsatisfiable)** | Hcore = ~15 unproven analytic fields; file has 4 sorrys |
| Thm 1.2 (0<m≤1,β≥1) | Statements:4397; IntervalDomainTheorem12:270 | **REFUTED (abstract) + MISSING** | interval wrappers conditional on Cor 2.1/Prop 2.5/energy frontiers — never inhabited; no unconditional result |
| Thm 1.3 (regimes i–iv) | Statements:4458; IntervalDomainTheorem13:147 | **REFUTED + MISSING** | same uninhabited Cor 2.1/Prop 2.5/energy bundles |
| Thm 1.X `..._of_assumed_solutions_branch` | Statements:4907,4935,4962 | **IMPOSTOR (tautological)** | assumes the whole conclusion as hypotheses |
| Prop 1.1 (local existence) | Statements:4277; StatementAssembly:260 | **REFUTED + MISSING (concrete)** | no unconditional classical local-existence on intervalDomain; the 173-sorry Picard tower |
| **Lemma 3.1 (max principle)** | **IntervalLemma31Closure:941** | **FAITHFUL (N=1)** ✅ | real max-principle, no sorry. The key χ₀≤0 ingredient — ALREADY DONE. |
| Lemma 2.5 (sharp Ψ_β bound) | Statements:1855 `..._direct` | **FAITHFUL** ✅ | weighted AM-GM, sharp |
| Lemmas 2.1–2.4 (semigroup Lᵖ-Lq) | Statements:1420 `..._zero_data` | **IMPOSTOR (vacuous)** | proved only for `zeroSemigroupEstimateData` (all bounds 0≤0); real heat-kernel bounds live in PDE/ but don't feed the statement layer |
| Foundation (heat/GN/Agmon/resolvent) | PDE/HeatKernelLpEstimates etc. | **FAITHFUL** ✅ | unconditional, sorry-free toolkit |

## χ₀<0 ASSESSMENT (the mountain, sized honestly)
Counter-intuitive but verified from paper §3: **the χ₀<0 case of Theorem 1.1 is
NOT the Lᵖ/Riesz-Thorin mountain** (that's 1.2/1.3). Paper §3 proves Theorem 1.1
for ALL χ₀≤0 by a **parabolic maximum-principle / comparison argument** (Lemma
3.1): at the spatial max of u, the chemotaxis term −χ₀·(uᵐ/(1+v)^β)·(μv−νuᵞ) ≤ 0
because χ₀≤0 AND μv̄−νūᵞ≤0 (elliptic v=(μI−Δ)⁻¹νuᵞ, uᵞ≤ūᵞ). Remark 3.1 says they
DELIBERATELY avoid Lᵖ-bootstrap because it's hard for χ₀<0, γ>1.
**Crucially: Lemma 3.1 (the max principle) is ALREADY proved faithfully on N=1.**
So the χ₀<0 obstruction is NOT the bound machinery — it is:
  - D1. LOCAL EXISTENCE of the COUPLED classical solution with a live chemotaxis
    flux (Prop 1.1 / §2.2 analytic semigroups). Our χ₀=0 route is logistic-only
    mild/Picard and is "blocked by design" for χ₀<0 (the restart source carries a
    flux-divergence not realizable as a logistic source — INTEGRITY_GAPS:902-918).
    Needs a different mild representation keeping the flux. THE big block.
  - the parabolic max principle on the cylinder (Mathlib lacks it; Lemma 3.1's
    proof already builds the N=1 version — reusable).
  - elliptic v-regularity + Hopf (a=b=0 branch).
So χ₀<0 ≈ "coupled local existence + (already-built) max principle". Medium-hard,
mostly DISJOINT from our χ₀=0 semigroup tower (low reuse).

## PRIORITIZED ATTACK LIST (dependency order)
**(D2/D3) cheap adapters — quick wins.**
- D3. GN frontier `IntervalDomainInterpolation` — RECLASSIFIED (opus 2026-06-11): NOT a low adapter. The proved `gagliardoNirenberg_interval` is only the p=2, r=4 endpoint; the frontier needs the general-p Agmon→Young chain (the bulk of the Lᵖ proof). Belongs to avenue C, not a quick win.
- D2. DONE (banners, commit abcb884): the zero_data + of_assumed_solutions IMPOSTORs are now banner-flagged in-source. Wiring the REAL HeatKernelLpEstimates into Lemma_2_1..2_4 D p S remains (LOW-MED, route-independent).

**(A) finish the χ₀=0 fragment — make it unconditional (IN PROGRESS, codex W7→W9).**
- A1. Discharge `hsrc0` — the σ=T endpoint via Route A (W7 hasDerivWithinAt_tsum
  DONE+audited; W8 one-sided interface+endpoint builder in flight; W9 wiring+delete).
  This makes the FRAGMENT unconditional (honestly labeled). HIGH leverage.
- A2. Inhabit the provider core (Hvpos resolver positivity, Hvsrc, hubt/hG1t/hG2t
  per-compact bounds, hpdeData) — the ~5 sorrys converging in TowerSupply/Final.

**(D1) local existence on intervalDomain — the big block, gates B/C.**
- The 173-sorry mild→classical Picard tower. Every existence hypothesis in B/C owes here.

**(C) Theorems 1.2 / 1.3 — from scratch above D1.**
- C1. Inhabit `Paper2BootstrapEstimateBranchData` (Moser/Lᵖ energy on [0,1]) — unlocks
  Lemma 2.6 / Cor 2.1 / Prop 2.5 → both 1.2 and all 1.3 wrappers. The Lᵖ mountain.
- C2. m=1 critical global frontier (1.2) + strong-logistic regimes i–iv (1.3).

**(B) extend Thm 1.1 to χ₀<0 and a=b=0.**
- B2. a=b=0 (source-free branch; tied to D1).
- B1. χ₀<0 — re-architecture (coupled local existence keeping the flux) + the
  already-built Lemma 3.1 max principle. Hardest; disjoint from the χ₀=0 tower.

## Cleanup debt (playbook IMPOSTOR flags to fix)
- `Lemma_2_X_zero_data` (vacuous) and `..._of_assumed_solutions_branch` (tautological)
  should be renamed/banner-flagged so they cannot be mistaken for real proofs.
