# Shen_work — HEADLINE THEOREMS 清单 (authoritative, audited 2026-06-15)

The repo formalizes the **Chen–Ruau–Shen trilogy** on one chemotaxis-growth system.
THREE papers. Models: `CMParams` (traveling waves, Paper1), `CM2Params` + `BoundedDomainData`
(bounded-domain dynamics, Paper2 & Paper3).

## ⚠️ HONEST BOTTOM LINE (verified audit, no build)
**0 of 28 headline Props are UNCONDITIONAL.** Every headline closer is an `of_assumed_*_branch` /
`of_*Data` reduction that ASSUMES the headline's hard content as a hypothesis; several are literal
tautologies (`:= hexist`, source-tagged "TAUTOLOGY (no math content)"). The repo is **0 sorry / 0 axiom /
0 native_decide** — but 0-sorry ≠ proven: the genuine unconditional content is the **shared PDE
infrastructure** (below) and linear-spectral sub-claims, NOT the headlines. The only "unconditional"
headline-shaped results are on the **degenerate `unitPointDomain`** (Point=Unit, gradNorm=0, boundary=∅
— a 0-d ODE that discards the PDE); those do NOT establish the bounded-domain headline.

Legend: **B** = conditional (assumed branch). No headline is A (unconditional) or C (stub) right now.

---

## Paper2 — bounded-domain classical solutions (existence/boundedness) — CLOSEST to a real headline
| Thm | what | status | remaining hard content |
|---|---|---|---|
| Theorem_1_1 | χ₀≤0 positive classical solution + InitialTrace + sup-bound + (m≥1 global) | **B** | reduced to exactly **2 named frontier hyps**: `hQuant` (χ₀<0 datum-uniform local classical existence = the EWA real-PDE source-regularity floor) + `hMildLocal`. χ₀=0 hQuant wired (ConeQuantBridge, modulo PicardLimitRestartFrontier). 🔧 ACTIVE |
| Theorem_1_2 | slow/critical-regime time-decay | **B** | Lp-energy / eventual-sup-bound frontier |
| Theorem_1_3 | m-regime decay | **B** | Lp/mass-gradient frontier |
| Prop_1_1, Prop_2_1..2_5 | local existence + the resolvent/gradient/mass/Moser estimates | **B** | several are tautology-closers (`:= hbound`/`hest`) needing real reductions |

## Paper1 — traveling waves — FARTHEST (least mechanism behind the branches)
| Thm | what | status | remaining hard content |
|---|---|---|---|
| Theorem_1_1 (B1) | monotone traveling-wave existence + Shen upper bounds + right-tail asymptotics | **B** | the wave-profile CONSTRUCTION. 🔧 ACTIVE: G1 (Brouwer→Schauder principle, near done) + G2 (Rothe implicit-Green orbit — deepest gate, now decomposed into tractable bricks) + 5 bridge wrappers (hVmono done; rest ride on the orbit) |
| Theorem_1_2 (B?) | nonlinear orbital STABILITY of the wave | **B** | weighted-L² + uniform moving-frame convergence (Section 5) — essentially stubbed |
| Theorem_1_3 (B2) | profile UNIQUENESS | **B** | reduces to Theorem_1_2 + cauchy-unique + resolvent + tail |
| Prop_1_1, Prop_1_2 | global existence + bounds/convergence | **B** | global Cauchy existence (Section 3) — essentially stubbed |

## Paper3 — long-time dynamics (stability / persistence / critical sensitivity) — MIDDLE
Sits ON TOP of Paper2's solution objects (imports Paper2.Statements/Defs; inherits Paper2's existence floor).
| Thm | what | status | remaining hard content |
|---|---|---|---|
| Theorem_2_1 (+4 parts) | uniform PERSISTENCE / lower-envelope bounds | **B** | persistence lower bounds (pointwise + boundary) |
| Theorem_2_2 | nonlinear local exponential C¹ convergence to equilibrium | **B** | the nonlinear half (linear dichotomy IS unconditional, but only that half) |
| Theorem_2_3 | negative-sensitivity convergence-rate formula (sectorial) | **B** | sectorial-operator stability analysis |
| Theorem_2_4 | full nonlinear stability + critical-sensitivity threshold | **B** | (linear stability formula unconditional but carries a condition) |
| Theorem_2_5 | full nonlinear stability (companion regime) | **B** | |
| Prop_1_2/1_3/1_4 | global bounded solutions | **B** | (Prop_1_4 unconditional only on the 0-d unitPointDomain) |

---

## Shared infrastructure (the genuine UNCONDITIONAL proven base — Paper2 built it)
`ShenWork.PDE.Interval*` — bounded-interval Neumann backbone: `IntervalNeumannEllipticResolverR`,
`IntervalFullKernel*` (Green-kernel mass/gradient/boundary regularity), `IntervalDuhamel*`/`IntervalCosine*`/
`IntervalSemigroupNeumann`/`SpectralDecay`, `IntervalResolverPositivity`. **Paper3 imports this + 4 Paper2
modules directly** (its whole stability layer rides on `IsPaper2GlobalClassicalSolution`/`IsPaper2Bounded`).
**Paper1** shares only `PDE.HeatSemigroup`/`ResolventEstimate`/`HeatKernelLpEstimates` + its own
Brouwer/Sperner/Schauder fixed-point stack. The `Wiener/EWA` weighted-ℓ¹ algebra (intended engine for the
χ₀<0 `hQuant`) is **standalone scaffolding, imported by NO Paper file yet** — the unbuilt floor under Paper2 Th_1_1.

## "Will the later papers go faster?" — half yes, half no
- **Faster (the shared base is paid once):** resolver/Green-kernel/cosine-spectral/regularity + the
  `of_assumed_branch` assembly architecture are reused → assembly/wrappers/scaffolding go fast.
- **NOT faster (each paper's own deep analytic gate is new):** Paper1/B1 = Rothe parabolic orbit;
  Paper3 = Lyapunov/energy/sectorial stability. Unconditionalizing = discharging the assumed branches =
  the real PDE analysis, paper-specific.

## Grind order (active, 并进 2026-06-15)
- **Paper2 Th_1_1 (closest):** discharge χ₀<0 `hQuant`/`hMildLocal` (EWA floor) → first genuinely-unconditional headline + unlocks Paper3's existence base.
- **Paper1 B1 (parallel):** finish G1 Schauder principle (Brouwer K2′/K3) + G2 Rothe orbit (per-step contraction → trapping → limit) + bridge wrappers → B1 modulo nothing.
- Then B2 (uniqueness, rides on B1) · Paper3 stability · Paper1/Paper2 remaining decay/energy theorems.

Codex out of credits till Jun 18 → Opus carries all subagents.
