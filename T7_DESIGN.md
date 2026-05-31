# T7 — From the T6 atom to Paper 1/2 Theorem 1.1

Status doc opened 2026-05-30, right after **T6 closed** (HEAD `c04465a`,
`#print axioms` = core three, build green).  T6's atom

```
intervalDuhamelTerm_closedC2_of_timeC1_source
    (src : DuhamelSourceTimeC1 a) (ht : 0 < t) :
  ContDiff ℝ 2 (fun x => ∫ s in 0..t, unitIntervalCosineHeatValue (t-s) (a s) x)
    ∧ deriv (…) 0 = 0 ∧ deriv (…) 1 = 0
    ∧ ∀ x, ∂ₓₓ(…) x = ∑' n, duhamelSpectralCoeff a t n · (−(nπ)² cos(nπx))
```

(`ShenWork/PDE/IntervalDuhamelClosedC2.lean:1516`) is the previously-missing
spatial-`C²` regularity of the Duhamel term `D(t)=∫₀ᵗ S(t−s)g(s)ds` for a
time-`C¹` cosine source.

This doc records the three orientation findings the session was asked to make,
the **precise remaining ring** from the atom to Theorem 1.1, and the chosen
tractable subgoal.

---

## Finding 1 — the atom's exact interface

`DuhamelSourceTimeC1 a` (`IntervalDuhamelClosedC2.lean:1373`) is the **honest
source-regularity package** the atom consumes — no smuggled hard half:

| field | meaning |
|-------|---------|
| `adot : ℝ → ℕ → ℝ`, `hderiv` | each cosine coeff `s ↦ a s n` is `C¹` in time with deriv `adot s n` |
| `hadotcont` | `s ↦ adot s n` continuous |
| `envelope : ℕ → ℝ`, `henv_summable`, `henv_bound` | ℓ¹ envelope dominating `|a s n|` **uniformly in `s`** |
| `derivBound`, `hderivBound` | uniform sup bound on `|adot s n|` |

The atom's `C²` core is the **generic cosine-series engine** (also in-file),
which is what makes it reusable beyond the Duhamel term:

```
cosineCoeffSeries_contDiff_two   {b} (hb : Summable (n ↦ λₙ·|bₙ|)) :
    ContDiff ℝ 2 (x ↦ ∑' n, bₙ · cosineMode n x)
cosineCoeffSeries_deriv_at_zero / _at_one   : Neumann endpoints = 0
cosineCoeffSeries_deriv2_eq                 : ∂ₓₓ = ∑' bₙ·(−(nπ)²cos)
```

with `λₙ = unitIntervalCosineEigenvalue n = (nπ)²`.  **Key fact:** the engine's
only hypothesis is `Summable (n ↦ λₙ|bₙ|)` for an *arbitrary* coefficient
sequence `b`.  Both building blocks of a mild solution slice are cosine series
of this exact form:

* homogeneous semigroup `S_t u₀ = unitIntervalCosineHeatValue t û₀
    = ∑ (e^{−tλₙ}û₀ₙ)·cosineMode n x`  (coeff `bₙ = e^{−tλₙ}û₀ₙ`, summable
    `λₙ|bₙ|` for any bounded `û₀` since `λₙe^{−tλₙ}` decays);
* Duhamel term `D_t = ∑ duhamelSpectralCoeff·cosineMode`  (the atom).

So **the full mild-solution slice `u_t = S_t u₀ + D_t` is itself a single cosine
series** `∑ cₙ cos`, `cₙ = e^{−tλₙ}û₀ₙ + duhamelSpectralCoeff a t n`, with
`∑ λₙ|cₙ| < ∞`.  This is the structural pivot for everything below.

---

## Finding 2 — what `localExistence` actually demands

`IsPaper2ClassicalSolution intervalDomain p T u v` (`Paper2/Statements.lean:70`)
is a **7-part** conjunction:

1. `0 < T`
2. `intervalDomainClassicalRegularity T u v`  — the regularity bundle (below)
3. `0 < u t x` on `(0,T)` (closed-domain positivity)
4. `0 ≤ v t x`
5. `u`-PDE: `∂ₜu = Δu − χ₀·chemDiv + u(a−bu^α)` on the interior
6. `v`-elliptic: `0 = Δv − μv + νu^γ`
7. Neumann BC for `u,v` (definitionally on `intervalDomainNormalDeriv`)

Part 2, `intervalDomainClassicalRegularity` (`IntervalDomain.lean:2768`), is a
**9-conjunct** bundle.  Mapping the T6 atom onto it:

| conj | content | atom relevance |
|------|---------|----------------|
| (1)(2) | sup-norm antitone on `Ioc/Ioo` (regime) | — (max principle, T4/T5 machinery) |
| (3) | spatial `ContDiffOn ℝ 2` on **open** `(0,1)` | **atom**: `ContDiff` ⇒ `ContDiffOn` |
| (4) | interior time `C¹` + `∂ₜ` continuous in `t` | time-coeff regularity (R1) |
| (5) | joint `(t,x)` `∂ₜ` continuity on `Ioo×Ioo` | Weierstrass-M (R1) |
| (6) | one-sided Neumann **limits** `deriv(lift)→0` at `0⁺,1⁻` | **atom** (genuine Neumann) |
| **(7)** | **closed `ContDiffOn ℝ 2` on `Icc 0 1` + endpoint `deriv=0`** | **atom — the conjunct it was built for** |
| (8) | closed-slab joint `∂ₜ` continuity on `Ioo×Icc` | time-coeff Weierstrass-M (R1) |
| (9) | closed-slab joint **solution-field** continuity on `Ioo×Icc` | space-time Weierstrass-M |

The atom directly supplies the spatial half: **(3),(6),(7)**.  The remaining
regularity conjuncts (4),(5),(8),(9) are *time* regularity / joint
space-time continuity — they need the coefficient sequence's **time**
dependence (`cₙ(t)` jointly summable with its `t`-derivative), a separate
(also cosine-series-Weierstrass-M) argument, not the spatial atom.

**Subtlety (the endpoint `deriv`):** conjunct (7) asks for the *two-sided*
`deriv (intervalDomainLift (u t)) 0 = 0`.  `intervalDomainLift` zero-extends
outside `[0,1]`, so at the endpoint the lift jumps (value `u t 0 ≠ 0` for a
positive solution vs. `0` outside) ⇒ not differentiable ⇒ `deriv = 0` by the
Mathlib junk-value convention — exactly how the constant constructor discharges
it (`intervalDomainLift_const_deriv_endpoint_zero`).  The *genuine* Neumann
content lives in conjunct (6) (the one-sided limit), which is the atom's real
`deriv(cosineSeries) 0 = 0`.

---

## Finding 3 — the remaining ring (atom → Theorem 1.1)

Theorem 1.1 is **already proved conditional on `localExistence`** (the umbrella
`Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound`,
`Paper2/IntervalDomainTheorem11Umbrella.lean`) — the entire gluing / uniqueness
/ L²-energy / maximal-continuation apparatus is axiom-clean (T8 note).  The sole
remaining frontier is **genuine `localExistence`**: construct, for every
positive admissible datum `u₀`, a `(u,v)` satisfying all 7 parts above.

Ring from the atom to that:

```
[A] cosine-series slice  ──conjunct(7) bridge──▶  conj (7) of the reg bundle   ← THIS SESSION
[B] same                 ──spatial──▶            conj (3),(6)
[C] time-coeff regularity ──Weierstrass-M──▶      conj (4),(5),(8),(9)
[D] the coupled FIXED POINT: construct (u,v) as cosine profiles whose
    coefficients cₙ(t) are the mild-solution coefficients of the *nonlinear*
    coupled system, AND prove the source g = −χ∇·(u∇v/(1+v)^β)+u(a−bu^α)
    satisfies `DuhamelSourceTimeC1` (the bootstrap closing [C]'s hypotheses),
    AND that (u,v) satisfy parts 5,6 (the PDEs) and parts 3,4 (positivity).
    ── this is the DEEP WALL (T8 §7): no Banach/Picard fixed point for this
       coupled chemotaxis system exists in Mathlib.  The atom removed the
       hardest *analytic* sub-obstruction (∂ₓₓ of the (t−s)^{−3/2}-singular
       Duhamel integral); the *construction* (fixed point + bootstrap +
       positivity via strong maximum principle) remains.
```

**Honest status:** T7's "final assembly" is **blocked at [D]** — the coupled
fixed-point construction — exactly the existence wall recorded for T8.  The atom
is one conjunct of nine of one part of seven; it does not by itself build
`localExistence`.  What IS closeable now, and makes the atom directly
consumable by any future cosine-profile constructor, is **[A]/[B]/[C]**: the
bridges turning "slice = cosine series with `∑λₙ|cₙ|<∞`" into the repo's exact
regularity-conjunct shapes.

---

## Chosen subgoal (this session): [A] — the conjunct-(7) cosine-slice bridge

`ShenWork/PDE/IntervalCosineSliceRegularity.lean` (new):

```
intervalDomainCosineSlice_conjunct7
  {b : ℕ → ℝ} {w : intervalDomainPoint → ℝ}
  (hb : Summable (n ↦ unitIntervalCosineEigenvalue n · |b n|))
  (hagree : EqOn (intervalDomainLift w) (x ↦ ∑' n, b n · cosineMode n x) (Icc 0 1))
  (hne0 : intervalDomainLift w 0 ≠ 0) (hne1 : intervalDomainLift w 1 ≠ 0) :
  ContDiffOn ℝ 2 (intervalDomainLift w) (Icc 0 1)
    ∧ deriv (intervalDomainLift w) 0 = 0
    ∧ deriv (intervalDomainLift w) 1 = 0
```

Proof: `ContDiffOn` by `(cosineCoeffSeries_contDiff_two hb).contDiffOn.congr
hagree`; endpoint `deriv = 0` by junk-value non-differentiability of the
zero-extension (generalising the constant constructor's argument).  The
`hne0/hne1` hypotheses are **faithful** — the paper studies *positive* classical
solutions, so `u t 0 > 0`, `u t 1 > 0`.

This is the precise "atom ⇒ conjunct (7)" wiring step.  Follow-ups: [B] the
(3)/(6) bridges, then [C] the time-coefficient Weierstrass-M conjuncts.  [D]
remains the documented frontier.
