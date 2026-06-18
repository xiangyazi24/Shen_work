# ⚠️ CORRECTED GOAL (Xiang, 2026-06-18)

**The goal is to BUILD THE PARABOLIC PDE LIBRARY over several months and GENUINELY DISCHARGE every
floor — NOT to harvest the easy unconditional branches and label the heavy PDE floors as named
frontiers.** That "harvest + honest-label" framing below (from a ChatGPT consult) was answering the
WRONG question. Playbook audit = ALL floors genuinely proven.

So Paper 3's heavy floors (P3.1 global classical existence/boundedness, P3.4 sectorial/analytic
semigroups, P3.5 Aubin-Lions/parabolic compactness, P3.6 Lyapunov→global convergence + C¹ exponential)
are the ACTUAL TARGETS. We build the Lean infrastructure bottom-up to prove them.

## PDE-library build plan (dependency-ordered, the multi-month campaign)
Target domain = `intervalDomain` (1D, explicit Neumann kernels — the tractable entry to real PDE theory).
1. **1D Neumann elliptic layer** — Green/resolvent kernel for `−∂xx + 1` on [0,1] Neumann; elliptic
   regularity + gradient estimates (discharges Lemma 7.1, feeds v-equation `0 = Δv − v + u^γ`).
2. **Interval parabolic local existence** — Neumann heat semigroup + Duhamel/contraction for the
   u-equation; positivity, continuation criterion. (entry to P3.1)
3. **Maximum principles + comparison** — parabolic SMP, sub/super-solutions on the interval. (P3.2 lower
   envelope, P3.5 upper-envelope monotonicity)
4. **A-priori bounds / boundedness** — energy + logistic-damping `L^p→L^∞` bootstrap; negative-sensitivity
   first. (P3.1 global existence from local + boundedness)
5. **Compactness** — time-translate / parabolic-smoothing compactness on the interval (Arzelà-Ascoli on
   parabolic Hölder, or an Aubin-Lions slice). (P3.2, P3.5, P3.6 moment→uniform)
6. **Sectorial / analytic semigroup** — sectoriality of the interval Neumann linearized operator,
   fractional domains `X_p^σ`, smoothing estimates → nonlinear local exponential stability. (P3.4, P3.3 nonlinear part)
7. **Lyapunov + LaSalle** — dissipation identities → ω-limit → global convergence → C¹ exponential upgrade. (P3.6)
Build 1→7; discharge P3.1–P3.6 as each layer matures. Each layer is itself a real campaign.

## Immediate concrete bricks (real proven content, the first stones)
- Paper 1 per-step (in flight) — genuine elliptic/Rothe PDE; finish it.
- P3.3 formula/spectral umbrella `Paper3FormulaSpectralTargets` — already-proven linear/spectral content,
  assemble it (a first honest unconditional brick, NOT the endpoint).
- Layer 1 (1D Neumann elliptic) — the natural first PDE-library module to start building.

---

## Bottom line

For a playbook audit, **do not try to turn Paper 3 fully unconditional now**. The honest split is:

**Unconditional / near-unconditional:** formula algebra, spectral-threshold algebra, negative-sensitivity linear stability, explicit interval Neumann spectral decay, some interval max-principle/norm bookkeeping.

**Conditional but honest:** global classical PDE existence, boundedness, uniform persistence from time-translate compactness, sectorial nonlinear orbit estimates, Aubin–Lions/Arzelà compactness, Lyapunov-to-uniform convergence, C¹ exponential upgrades.

The repo’s own status notes already enforce this distinction: it says `0 sorry` does not mean the paper main theorems are proved, and projection/accessor lemmas from `Prop` targets or package fields are not mathematical proofs unless backed by direct lower-level derivations. fileciteturn51file0L5-L13 fileciteturn51file0L23-L29 That is exactly the right standard for Paper 3.

---

## (1) Floor-by-floor feasibility

### P3.1 — global classical existence + boundedness

**Classification: heavy-defer, except restricted branches.**

This is the foundational PDE floor. It requires real bounded-domain parabolic-elliptic Keller–Segel theory: local classical solvability, positivity, Neumann compatibility, continuation criteria, elliptic regularity for \(v\), \(L^p/L^\infty\) bootstrap, and logistic damping estimates. Mathlib does not hand you that as a ready theorem, and your repo’s abstraction reflects that: Proposition 1 frontier data still asks for `NegativeSensitivityGlobalEventualBound` and existence branches for Propositions 1.3 and 1.4. fileciteturn25file0L25-L46

**Tractable subpieces:**

- The **negative-sensitivity eventual bound** is the easiest real PDE sub-branch, because \(\chi_0\le 0\) removes the aggregating drift. But it still assumes or needs global classical solutions; proving existence from scratch is still a PDE-library task.
- The repo already has a bridge deriving Paper3 Proposition 1.3 from Paper2 Theorem 1.3, so if Paper2’s global bounded branch is eventually discharged, Paper3’s Proposition 1.3 follows with little extra Paper3 work. fileciteturn25file0L107-L143
- The ODE/unit-point branch is already the right unconditional toy/degenerate case, but it should not be sold as the bounded-domain theorem.

**Do not attack full P3.1 first** unless the project goal shifts to building a serious parabolic PDE library.

---

### P3.2 — uniform persistence, Theorem 2.1

**Classification: partially tractable, but the full theorem is heavy.**

The four raw parts split well. The repo exposes them separately: interval wrappers take `UniformPersistencePart1Raw`, `Part2Raw`, `Part3Raw`, and `Part4Raw` and assemble Theorem 2.1 from them. fileciteturn34file0L74-L91

**Tractable:**

- ODE comparison algebra.
- Logistic scalar subsolution inequalities.
- Threshold formula manipulations.
- Some minimal-model mass bookkeeping.

**Heavy:**

- Time-translate compactness.
- Strong maximum principle on omega-limit limits.
- Uniform lower envelope from parabolic positivity.
- Elliptic Neumann transfer from \(u\)-lower-bound to \(v\)-lower-bound.

The abstract API is not strong enough to prove persistence automatically. There is even a formal counterexample showing Theorem 2.1(1) cannot follow from the current abstract `BoundedDomainData` alone: the lower-envelope functional can be fake, with positive constant solutions but `infValue ≡ 0`. fileciteturn45file0L24-L42

So P3.2 should remain conditional unless you instantiate a real interval-domain lower envelope and prove the analytic compactness/strong maximum principle package.

---

### P3.3 — linear stability dichotomy, Theorem 2.2

**Classification: tractable for the linear/formula part; full theorem partially heavy.**

This is the best target for more unconditional coverage. The repo already contains a lot of the right algebra:

- `sigma` threshold facts.
- `LinearlyStable_of_chi_nonpos_a_pos`.
- `LinearlyStable_of_chi_lt_sigmaCriticalChi`.
- `LinearlyUnstable_of_sigmaCriticalChi_lt_chi`.
- Bridges from `Paper3ConstantsUsesCriticalSpectrum` to positive/minimal equilibrium stability and instability. fileciteturn42file0L141-L199

For negative sensitivity, the stable linear branch is already elementary: \(\chi_0\le0\) makes the chemotactic contribution nonpositive and the nonzero Neumann modes decay. The repo has exactly this shape in `LinearlyStable_of_chi_nonpos_a_pos` and its Neumann-specialized positive-equilibrium version. fileciteturn42file0L112-L119 fileciteturn42file0L222-L229

**But full Theorem 2.2 includes nonlinear local exponential stability.** That part depends on P3.4 sectorial/local semigroup estimates and small-data global existence. The repo’s sectorial interval bridge explicitly separates the proved spectral-decay piece from the remaining nonlinear orbit-comparison frontier. fileciteturn35file0L168-L199

So: make a direct **linear dichotomy target** unconditional; keep the nonlinear local exponential part conditional.

---

### P3.4 — sectorial local exponential decay

**Classification: heavy-defer, with one important proved subblock.**

The full H3.1 framework is not a “few lemmas” job. It needs sectoriality, fractional domains or \(X_p^\sigma\), Duhamel estimates, nonlinear Lipschitz bounds in the correct spaces, parabolic smoothing, and bootstrapping to \(C^1\).

The repo is already honest here: `IntervalDomainSectorial.lean` states that it **does not prove sectoriality** of the interval Neumann linearized operator; it records the exact H3.1 hypothesis and routes it through the Paper3 raw API. fileciteturn35file0L3-L12 It then proves the interval Neumann spectral decay part and leaves the nonlinear orbit-comparison estimate as the named frontier. fileciteturn35file0L126-L137

**Tractable / already mostly done:**

- Unit-interval Neumann spectrum.
- First nonzero eigenvalue \(\pi^2\).
- Coefficient-space heat semigroup decay on the zero-mean subspace.
- Converting spectral decay into the exponential factor once a nonlinear orbit bound is assumed. fileciteturn36file0L28-L55 fileciteturn35file0L168-L199

**Heavy:**

- The nonlinear Duhamel orbit estimate.
- Actual sectorial semigroup theory for the linearized Keller–Segel operator.
- Fractional-domain norm equivalences.
- Regularization to \(C^1\).

Keep P3.4 conditional, but rename the frontier very explicitly, as the repo already does: `IntervalDomainSpectralSemigroupOrbitBoundRaw` is much better than a vague `SectorialLocalExponentialRaw`.

---

### P3.5 — compactness / regularization, Lemmas 3.1–3.5 and 7.1

**Classification: mixed.**

Some of P3.5 is already reduced to concrete interval bookkeeping. In `IntervalDomainStabilityChain.lean`, the interval upper-envelope monotonicity is routed through a concrete sup-norm max-principle bridge, while the remaining analytic frontiers are listed explicitly: time-translate compactness, initial norm-continuity, minimal upper bounds, and a Neumann-resolvent gradient estimate. fileciteturn33file0L200-L235

**Tractable:**

- `Lemma_3_1` if it only projects already-present classical regularity.
- Interval-domain upper-envelope monotonicity, already essentially done through the sup-norm max principle. fileciteturn33file0L150-L170
- Initial norm-continuity if your concrete \(X_p^\sigma\) gauge is definitionally a sup norm, as in the interval files. fileciteturn33file0L67-L107
- `Lemma_7_1` on the unit interval may be medium difficulty if you use an explicit Neumann Green kernel/resolvent estimate rather than full elliptic regularity.

**Heavy:**

- Time-translate compactness of full PDE solution families.
- Parabolic regularization compactness.
- Any Aubin–Lions-style route.
- Uniform compactness of \(u,v\) on infinite time translates.

P3.5 is worth attacking only in **slices**. Do not try to prove the whole compactness package in one pass.

---

### P3.6 — global stability, Theorems 2.3–2.5

**Classification: partially tractable, but full global stability is heavy.**

The **algebraic Lyapunov identities and threshold comparisons** are tractable. The repo already has substantial formula-level threshold infrastructure, including raw Lemma A.7 comparison forms and first-mode lower-bound reductions. fileciteturn47file0L148-L227

The **global convergence theorem** is heavy. It needs:

- P3.1 global bounded classical solutions.
- P3.2 persistence/lower bounds.
- P3.5 compactness or moment-to-uniform upgrade.
- Lyapunov dissipation.
- LaSalle/omega-limit logic or a substitute.
- \(C^1\) exponential upgrade for the final stability versions.

The raw negative-sensitivity global stability package explicitly includes both uniform convergence and exponential \(C^1\)-decay conclusions, so it is not merely algebra. fileciteturn45file0L214-L246

So P3.6 should be split into:

1. **Lyapunov algebra target** — tractable.
2. **Moment decay target** — medium/heavy depending on how analytic the integrals are.
3. **Moment-to-uniform target** — heavy.
4. **Uniform-to-exponential \(C^1\) upgrade** — heavy.

---

## (2) Dependency-correct attack sequence

### First: harvest unconditional algebra/spectral wins

Attack or audit-complete P3.3 formula/spectral branches first:

```lean
Paper3LinearFormulaTargets
Paper3CriticalSensitivityFormulaTargets
Paper3NegativeSensitivityLinearTargets
Paper3ThresholdComparisonTargets
```

This gives honest partial closure without touching parabolic existence. It also improves Theorem 2.2 reporting: you can say the **linear critical threshold mechanism** is proved, while nonlinear local exponential stability remains conditional.

### Second: clean the interval-domain concrete wrappers

Finish all “projection-free but low-PDE” interval facts:

```lean
intervalDomainStabilityNorms_xpSigma_le_supNorm
intervalDomain_Lemma_3_3_for_concreteStabilityNorms
intervalDomain_upperEnvelopeMonotonicityRaw_supNorm
intervalDomain_Lemma_3_4_of_upperEnvelope_eq_supNorm
```

Most of this is already present. The repo’s interval assembly states that the core interval target currently needs only the canonical core existence package and concrete initial-continuity frontier; it adds no new analytic frontier. fileciteturn38file0L3-L10

### Third: try the explicit 1D Neumann resolvent gradient estimate

This is the most plausible nontrivial analytic target that does **not** require building full parabolic theory. Prove `Lemma_7_1` on `intervalDomain` from an explicit Green kernel. It is isolated, useful, and much smaller than Aubin–Lions.

### Fourth: P3.2 ODE-comparison subpieces

Prove scalar logistic comparison and minimal-model mass algebra as standalone lemmas. Keep the compactness/strong-max-principle input explicit.

### Fifth: restricted P3.1 only if you can reuse Paper2

Do not build global PDE existence from scratch inside Paper3. Route P3.1 through Paper2-style theorem branches when possible. The StatementAssembly file already supports this for Proposition 1.3 via `Paper2.Theorem_1_3`. fileciteturn25file0L117-L143

### Last: P3.4 and full P3.6

These are multi-month infrastructure efforts unless a previous bounded-domain parabolic library is available. Keep them as named, non-vacuous frontiers.

---

## (3) Small-data / negative-sensitivity route for P3.1

Yes, the paper structure supports useful restricted branches, but there is a sharp distinction:

### Negative sensitivity makes boundedness easier, not classical existence free

When \(\chi_0\le0\), the chemotaxis term is repulsive or non-aggregating, so the standard maximum/energy estimates are much easier. In Lean terms, the **eventual bound** branch is plausible. But proving:

```lean
∃ u v, IsPaper2GlobalClassicalSolution D p u v ∧ ...
```

still requires the full local-existence + continuation framework.

So an honest negative-sensitivity theorem should be shaped as either:

```lean
theorem negativeSensitivity_eventualBound_of_globalClassical
    (hχ : p.χ₀ ≤ 0)
    (hglobal : IsPaper2GlobalClassicalSolution D p u v)
    ...
    : EventuallyUpperBound ...
```

or, if using Paper2:

```lean
theorem paper3_Proposition_1_2_of_Paper2_negative_branch
    (hP2 : Paper2NegativeSensitivityGlobalExistenceAndBoundedness D p)
    : Proposition_1_2 D p
```

Do not claim full P3.1 is easy unless the Paper2 global-existence input is actually discharged.

### Small-data global existence is also not cheap

Small-data near a constant equilibrium is easier analytically, but still needs a local classical theory, stability norm control, and continuation. In the sectorial route, it appears exactly as a side input to convert \(X_p^\sigma\)-small local decay into local exponential stability from a sup-norm neighborhood. fileciteturn53file0L28-L49

That means small-data global existence is best treated as a **separate named restricted frontier**, not as a quick proof.

### Best restricted unconditional branch

The best restricted **unconditional** branch is not “global PDE existence”; it is:

```lean
χ₀ ≤ 0 → linear stability / spectral gap at equilibrium
```

This is already structurally in the repo. For example, the interval sectorial file proves the negative-sensitivity positive-equilibrium branch up to the remaining sectorial/small-data hypotheses, while the linear stability input itself is discharged from the unit-interval Neumann spectrum. fileciteturn53file0L204-L242

---

## (4) How to make `Paper3MainlineTargets` partially unconditional

Do **not** make the existing umbrella look more unconditional than it is. Its definition includes all five major target packages: propositions, persistence, Theorem 2.2, compactness/regularization, and stability 2.3–2.5. fileciteturn28file0L8-L20 Its data structure still carries proposition, persistence, theorem22, compactness, and stability fields. fileciteturn28file0L21-L30

Instead add smaller, honest umbrella targets.

### Add a formula/spectral partial target

```lean
def Paper3FormulaSpectralTargets
    (S : SpectralData) (p : CM2Params) : Prop :=
  HasNeumannSpectrum S ∧
  -- critical sensitivity formula facts
  -- linearly stable below χ*
  -- linearly unstable above χ*
  -- χ₀ ≤ 0 linear stability branch
  -- Lemma A.6/A.7/A.8 formula comparisons already proved
```

This is the cleanest “partial unconditional” story. Your own audit inventory already says the nonpositive-sensitivity and `paperCriticalSensitivity` threshold linear branches of Theorem 2.2 are directly proved, while the full local-exponential theorem remains externalized. fileciteturn50file0L48-L50

### Add an interval spectral-decay target

```lean
def IntervalDomainSpectralDecayTargets : Prop :=
  HasNeumannSpectrum unitIntervalNeumannSpectrum ∧
  ∀ t ≥ 0,
    ‖unitIntervalNeumannHeatSemigroupP0Compl t ht‖ ≤
      Real.exp (-(Real.pi^2) * t)
```

This is real and useful. The repo’s `PDE/SpectralDecay.lean` builds interval Neumann eigenvalues and the coefficient heat semigroup, then proves operator-norm decay for the zero-mode complement. fileciteturn36file0L28-L55 fileciteturn37file0L63-L70

### Add a conditional-but-sharper sectorial target

Replace vague assumptions like:

```lean
SectorialLocalExponentialRaw ...
```

with the smaller honest frontier:

```lean
IntervalDomainSpectralSemigroupOrbitBoundRaw p N
```

because the interval spectral decay part is already proved and only the nonlinear orbit comparison remains. The repo explicitly says this is weaker and more precise than assuming the raw sectorial package directly. fileciteturn35file0L126-L137

### Add a negative-sensitivity linear target, not full Theorem 2.3

A faithful partial theorem is:

```lean
theorem paper3_negativeSensitivity_linear_stability_interval
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2
```

A full negative-sensitivity Theorem 2.3 would claim global asymptotic or exponential \(C^1\) convergence of nonlinear solutions. That still needs P3.1/P3.2/P3.5/P3.6 analytic content. Do not advertise it as unconditional.

---

## Recommended status labels

Use these labels in the repo and status docs:

```text
P3.1 global existence/boundedness:
  heavy-defer; restricted negative-sensitivity/eventual-bound branch plausible.

P3.2 persistence:
  partial; ODE comparison tractable, compactness/SMP lower-bound heavy.

P3.3 linear stability:
  tractable/direct for spectral-formula dichotomy;
  nonlinear local exponential branch depends on P3.4/P3.1.

P3.4 sectorial local exponential:
  heavy-defer; interval linear spectral decay done; nonlinear orbit bound remains.

P3.5 compactness/regularization:
  mixed; interval max-principle/norm bookkeeping tractable/done;
  time-translate compactness heavy; explicit 1D Neumann resolvent estimate medium.

P3.6 global stability:
  partial; Lyapunov algebra and threshold comparisons tractable;
  moment-to-uniform and C¹ exponential upgrades heavy.
```

The highest-leverage next move is **not** P3.1. It is to create a clean partial Paper3 report layer:

```lean
Paper3FormulaSpectralTargets
IntervalDomainSpectralDecayTargets
IntervalDomainConcreteBookkeepingTargets
Paper3ConditionalPDEFrontiers
```

Then the project can honestly say:

**“Paper 3 is statement-complete; its formula/spectral/ODE-algebra branches are increasingly unconditional; the remaining full bounded-domain theorem is conditional exactly on named parabolic PDE compactness, existence, sectorial, and Lyapunov-convergence frontiers.”**
