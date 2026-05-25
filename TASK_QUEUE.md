# ShenWork Breakthrough Queue — PDE Foundations

Updated 2026-05-25. Replaces the slot-based queue. Goal (Xiang): close the
remaining analytic blockers one by one until the three papers' main theorems are
unconditional, not assumption-projected.

Discipline (unchanged):
- 0 sorry / 0 admit / 0 native_decide / 0 custom axiom.
- `export PATH="$HOME/.elan/bin:$PATH" && lake build ShenWork` must pass after each commit.
- `rg -n '\bsorry\b' ShenWork/` before every commit.
- `#print axioms` on each new top theorem = only `[propext, Classical.choice, Quot.sound]`.
- One file = one writer. Cross-file lemma names must not collide (namespace it).
- 17-point playbook, group C: a theorem that projects from an assumption package
  is NOT closed. The analytic estimate must be derived, or the field narrowed to
  the exact remaining analytic hypothesis.

---

## What is actually proven (foundation, do not redo)

- Concrete domain: `intervalDomain : BoundedDomainData` on `[0,L]`, with
  `intervalDomain_hasNeumannSpectrum` PROVEN (cosine basis). This is the real
  domain that replaces the too-broad abstract `BoundedDomainData` API.
- Heat semigroup on `[0,L]`: `intervalHeatSemigroup_Lp_Lq_bound` (H0.1),
  `intervalHeatSemigroup_grad_Lp_Lq_bound` (H0.2) — both unconditional.
- Interpolation/embedding: `gagliardoNirenberg_interval`, `agmon_inequality_interval`,
  `poincare_interval`, Sobolev `H1→L∞`.
- Differentiation under the integral: `LeibnizRule.lean` (Psi_deriv family).
- Mild-solution contraction: `mild_solution_operator_contracting` (Banach FP).
- ODE uniqueness (H0.5), sectorial resolvent estimate, fractional power space,
  Neumann spectral decay (`intervalNeumannSpectrum_hasNeumannSpectrum`),
  analytic semigroup generation + physical-L² transport.
- Honest negative results (keep): `not_Lemma_4_1/4_2`, `not_Remark_4_2*`,
  `not_forall_*` obstructions proving the arbitrary-domain APIs are too broad,
  `Theorem_1_2` is FALSE on the `(a>0,b=0)` unitPoint slice (unbounded ODE).

The remaining work is to connect these on the CONCRETE `intervalDomain` and
discharge the weak-solution analytic estimates, in the dependency order below.

---

## B1 — Semigroup estimate data on intervalDomain  [unlocks P2: Paper2 2.1–2.4, Paper3 A.2–A.5]

Instantiate `Paper2.SemigroupEstimateData intervalDomain` from the proven
heat-kernel bounds (H0.1 + H0.2) instead of carrying it as an abstract field.

- File: `ShenWork/Paper2/IntervalDomainLemma21.lean` (sole writer).
- Output: a concrete `intervalDomainSemigroupEstimateData : SemigroupEstimateData intervalDomain`
  whose fields are the H0.1/H0.2 theorems, then route `Lemma_2_1`–`Lemma_2_4`
  for `intervalDomain` through it.
- Gap to discharge: match the paper's `t^{-N/2(1/p-1/q)}` time singularity to the
  proved absolute-convergence endpoint (sharpening to `t^{-1/2}` is a later task).

## B2 — Local mild solution → Proposition 1.1 on intervalDomain  [P3/P5]

From `mild_solution_operator_contracting` build a local-in-time mild solution and
derive `Proposition_1_1 intervalDomain p` (local existence/regularity).

- Files: `ShenWork/PDE/MildSolution.lean`, `ShenWork/PDE/IntervalDomainExistence.lean`.
- Gap: `classicalRegularity` must come from the concrete interval domain's
  Duhamel iterate (do NOT use the arbitrary-domain API — it's refuted).

## B3 — Lp bootstrap → L∞ boundedness → Paper2 Theorem 1.1  [P3, main analytic frontier]

The weak-solution energy chain. This is where the overnight agents stopped.

- Files (one writer each): `IntervalDomainEnergyStep.lean`,
  `IntervalDomainLpMonotonicity.lean`, `IntervalDomainMoserClosure.lean`,
  `IntervalDomainBootstrap.lean`, `IntervalDomainCorollary21.lean`,
  `IntervalDomainTheorem11.lean`.
- Precise gaps to build (the honest frontier list from the agents):
  1. Integration by parts for the weak/classical interval solution (boundary terms
     vanish under Neumann) — feeds the Lp energy identity.
  2. Time-derivative through the spatial integral (Leibniz at the PDE level) — use
     `LeibnizRule` + dominated convergence; this is the `d/dt ∫|u|^p` step.
  3. Cross-diffusion energy estimate (the `∇·(u^m ∇v)` term) bounded via
     `gagliardoNirenberg_interval` + Young.
  4. Moser iteration closing `Lp → L∞` uniformly in p (the `IntervalDomainMoserClosure`).
  5. Eventual sup bound / mass control → `IsPaper2Bounded` → `Theorem_1_1`.
- Target: `Theorem_1_1 intervalDomain p` unconditional for the admissible parameter
  range (respect the proved `(a>0,b=0)` refutation — that slice stays false).

## B4 — Paper3 stability on intervalDomain  [P4]

Replace `StabilityNorms`, `CompactnessData`, `Paper3Constants` fields by concrete
definitions from the spectral/sectorial theory already proved.

- Files: `IntervalDomainSectorial.lean`, `IntervalDomainStabilityChain.lean`,
  `IntervalDomainTheorem21Part1.lean`, `IntervalDomainTierChain.lean`.
- Discharge `SectorialLocalExponentialRaw` (Theorem_2_2 blocker) from the proved
  analytic-semigroup spectral decay (`SpectralDecay.lean`).
- Then: norm continuity, compactness, upper-envelope monotonicity, persistence,
  convergence-to-exponential → `Theorem_2_1`–`Theorem_2_5` on intervalDomain.

## B5 — Paper1 whole-line traveling-wave stability/uniqueness  [P1, semi-independent]

Whole-line (not bounded-domain), built on the proved whole-line heat kernel.

- Files: `Paper1/Statements.lean`, `PDE/TravelingWaveConstruction.lean`,
  `PDE/ResolventEstimate.lean`, `Paper1/Lemma25Helpers.lean`.
- Targets: Lemma 2.1 (heat semigroup), Lemma 2.5 (weighted resolvent — the
  `ExponentialWeight k_dab` boundedness gap), Section 5 arbitrary-wave estimates,
  Cauchy theory + Schauder construction, `Theorem_1_2` (stability),
  `Theorem_1_3` (uniqueness).
- Current real branches: `Theorem_1_2_self_initial_data_branch` (degenerate u₀=U),
  `of_assumed_stability_branch`, `of_assumed_uniqueness_branch`. These must be
  upgraded to genuine nearby-data stability, not the self-data trivial case.

---

## Dependency order

B1 → B2 → B3 → B4 (B3 is the long pole). B5 runs in parallel (whole-line, independent).
Within B3, items 1–3 are independent and parallelizable; item 4 (Moser) needs 1–3;
item 5 needs 4.
