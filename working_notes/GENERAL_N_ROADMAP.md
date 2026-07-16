# General-N port roadmap — Chen–Ruau–Shen trilogy (planning synthesis 2026-07-16)

Synthesis of four ChatGPT (SOL Pro, shen1–4) planning passes on generalizing the
Lean formalization from the 1D interval `[0,1]` Neumann to a bounded smooth
domain `Ω ⊂ ℝ^N`. Raw answers live in Xiang's ChatGPT history (shen1–4).

## 0. Load-bearing model correction (VERIFIED in-code)

The faithful Chen–Ruau–Shen model has **LINEAR diffusion** `Δu`, with the exponent
`m` in the **chemotactic mobility flux**:

    u_t = Δu − χ₀ ∇·( u^m/(1+v)^β · ∇v ) + a u − b u^{1+α},    0 = Δv − μ v + ν u^γ.

It is **NOT** porous-medium `Δ(u^m)`, and **NOT** the (separate) porous-medium /
signal-consumption series (`u_t=Δu^m − χ∇·(u∇v)+…`, `v_t=Δv−uv`) — that is a
different paper family with different `m`-meaning and consumption signal equation.

**Verified in the Lean code (2026-07-16):**
- `intervalFluxM p u v y = (u y)^p.m · deriv(v) y / (1+v y)^p.β`  (`Paper2/IntervalDomainMFlux.lean:24`) — `m` is in the flux.
- `intervalDomainM.laplacian := intervalDomainLaplacian` (linear Δu, same as `intervalDomain` — NOT `(u^m)_xx`); `intervalDomainM.chemotaxisDiv := intervalDomainChemotaxisDivM` (`PDE/IntervalDomain.lean:3035`).

⟹ The entire session's `intervalDomainM` general-`m` work is on the faithful model.
"general-m" = generalizing the chemotaxis mobility exponent, not the diffusion.
**Do NOT** ever replace `Δu` by `Δ(u^m)` "for generality" — that changes the paper.

## 1. Strategic facts

- **The papers are ALREADY general-N.** Statements are on bounded smooth `Ω⊂ℝ^N`
  with N-dependent conditions (`p>max{N,mN,γN}`, `(Nα−2)_+`, `max{2,γN}`,
  `p₀>ρN/2`). The 1D restriction is a **Lean-infrastructure** limitation, NOT a
  math limitation. General-N = infrastructure port, not new mathematics.
- **Cleanest first math target: Theorem 2.2 LINEAR dichotomy.** Uses NO 1D fact —
  only the full Neumann spectrum. Mode rates
  `σ_n = −λ_n − aα + χ₀νγ(u*)^{m+γ−1}/(1+v*)^β · λ_n/(μ+λ_n)`.
  ⚠ **λ₁ alone is NOT enough for the exact threshold**: `g(λ)=(λ+aα)(μ+λ)/λ` has
  interior minimum at `√(aαμ)`, so a HIGHER mode can bind `χ*` unless
  `λ₁ ≥ √(aαμ)`. The abstract interface must expose the FULL nonzero spectrum (or
  the `inf` defining `χ*`), not just the first gap.

## 2. Where dimension genuinely bites (the real walls)

- **Part I boundedness** — most N-sensitive. Hardest single named lemma =
  **Prop 2.2 weighted elliptic gradient estimate** for `v` (needs W^{2,p} Neumann
  regularity + Hessian estimates). Then the GN bootstrap (Lemma 2.6, seed
  `p₀>ρN/2`) and the `L^p→L^∞` endpoint (Prop 2.5, `p>max{N,mN,γN}`).
- **`H¹↪L^∞` is the 1D crutch** — holds N=1, FAILS N≥2. Replace by `X^α↪C¹`
  (needs `2α>1+N/p`, i.e. `α>½+N/2p`, `p>N`) OR the **uniform-Hölder + L²→L^∞**
  bridge (`[f]_{C^θ}≤H, |f(x₀)|≥ε` ⇒ lower bound on `|f|₂` via `|B(x₀,r)∩Ω|≥cr^N`).
  The Hölder bridge is the Lean-friendliest replacement.
- **The `(t−s)^{−1/2}` kernel is NOT 1D** — it's one spatial derivative of a 2nd-order
  semigroup, fine in any N. But a naive `A^σ·divergence` Volterra copy gives
  `t^{−σ}(1+t^{−1/2})`, non-integrable at 0 for `σ>½` — use the operator-theoretic
  sectorial formulation, not one scalar convolution.
- **Thm 2.3** needs strong maximum principle + Neumann Hopf + time-translate
  Schauder compactness + connectedness propagation — more than a spectrum abstraction.
- **Thm 2.4/2.5 entropy algebra is dimension-FREE** (`h_m`, Young, power-difference
  `(u^γ−(u*)^γ)² ≤ C(u*)^{2γ−α−1}(u−u*)(u^α−(u*)^α)` under `2γ≤α+1`). Only the
  **dissipation→uniform-convergence endpoint** is N-sensitive (same H¹↪L^∞ issue).

## 3. What can be FALSE for N≥2 (do NOT port blindly)

- **Attractive minimal boundedness** under 1D hypotheses — Keller–Segel finite-time
  blow-up occurs for N≥2. Never transport a boundedness statement without restoring
  its N-dependent exponent thresholds.
- **"Every datum is global+bounded+converges"** — the stability theorems quantify
  ONLY over already-global-bounded orbits. Preserve that quantifier; the strengthening
  is false in dimensions where some data blow up.

## 4. m-vs-N threshold (faithful Chen model)

No unconditional "all N, all m>0, all params" theorem. Dimension-independent strict
regimes: `α>m+γ−1` (any β≥0), or `α>2m+γ−2` (β≥½). At the critical equalities,
boundedness needs `χ₀` smallness with N-dependent thresholds (e.g. m=1,β≥1:
`χ₀<2(2β−1)/max{2,γN}`). `0<m<1` proved for β≥1 but has a positive-infimum loss
obstruction on continuation (this is open in the paper itself). NB the Tao–Winkler
`m>2−2/N` belongs to the porous-medium *production* system, NOT this model.

## 5. Lean architecture — the deliverable

**Keep `BoundedDomainData` as the STATEMENT carrier; add a lawful capability layer.**
`BoundedDomainData` has bare function-valued fields (integral/supNorm/laplacian/
chemotaxisDiv/normalDeriv) with no laws — fine for statements, NOT an analytic proof
interface (repo's own THEOREM_STATUS says exactly this).

Layering:
```
BoundedDomainData            = PDE + theorem-statement syntax (stays)
LawfulBoundedDomain + Neumann capability classes = semantics + analytic laws
Paper2.Generic / Paper3.Generic = proofs using ONLY those laws
Interval instance            = existing 1D code proves the laws
General-Ω instance           = smooth bounded Ω⊂ℝ^N proves (or conditionally assumes) same laws
```

Composable capability bundles (do NOT make one monolithic `[NeumannDomain D]`):
- `LawfulBoundedDomain` — measure μ, finite measure, compact, integral/supNorm/inf specs.
- `NeumannVectorCalculus` — grad/div, Green identities (IBP), zero-normal-flux.
- `NeumannHilbertGap` — mean projection P/Q, gap decay `‖S t (Qf)‖≤M e^{−λ₁t}‖Qf‖`, resolver contraction, Poincaré. (Thm 2.4 lives almost entirely here.)
- `AnalyticSmoothingScale` — X₀/X_α, `‖S_α t f‖≤C t^{−α}‖f‖`, α<1. (Abstract Henry consumes THIS, not a `Sectorial` field.)
- `NeumannLpResolver` — one `p>N`, `X^α↪C¹` embedding constant, elliptic resolver bounds.
- `NeumannFunctionalInequalities` — Poincaré/GN as **dimension-aware predicates**, not fixed formulas.
- Spectrum split: `NeumannSpectralGap` (gap-only, enough for most) vs `DiscreteNeumannSpectrum` (full eigenbasis, only for exact threshold/instability).

Mathlib gap: Banach fixed-point / L^p / compact-self-adjoint spectral / Lax–Milgram
EXIST. The **big missing piece** is the bounded-domain PDE backend: Sobolev/trace/
extension → Neumann form → compact resolvent → W^{2,p} regularity → analytic heat
smoothing + fractional powers of unbounded sectorial operators. Strategy: interface
the CONSEQUENCES stability uses; build full sectorial Neumann theory later. Do an
**N-dim box instance** (explicit product cosine modes) as intermediate proof-of-
genericity before arbitrary Ω.

## 6. Refactor order (consumer-first: "copy up, wrap down")

Start at capstones, extract generic spine, make interval a provider, add general-Ω last.
- **PR1** lawful base (`LawfulBoundedDomain` + interval/intervalM instances + `ParametersMatchDomain` replacing `p.N=1` gates + `DomainNeumannSpectrum intervalDomainM`).
- **PR2** generic headline assembly (`correctedTheorem12_of_domain` etc.; interval capstones become one-line wrappers; NO analytic change).
- **PR3** continuation/gluing kernel (reachable-horizon, overlap uniqueness, bounded-before-vs-blowup — domain-independent; small-data global existence consumes 4 provider records).
- **PR4** Green/energy IBP layer (mass identity, L² uniqueness, power-test diffusion identity, chemotaxis-div IBP).
- **PR5** elliptic/GN/L^p/Moser (resolver estimates, cross-diffusion, dimension-aware GN, Moser ladder — Moser is NOT an interface field, prove once from GN capability).
- **PR6** sectorial/fractional layer (replace `xpSigmaDistance:=supNorm` with a genuine fractional scale; admissibility predicates; weak-basin/strong-bootstrap/eventual-C¹).
- **PR7** interval regression (all `..._intervalDomainM` become thin wrappers; add a **non-unit-length interval** as leak detector).
- **PR8** general-Ω conditional instance (smooth bounded Euclidean skeleton; conditional general-N capstones immediately).
- **PR9+** discharge assumed fields with real analytic constructions.

## 7. Abstraction risk register (each with a leak-detector test)

1. Lawless `D` — require `LawfulBoundedDomain` + exact capabilities; no bare-`D` analytic theorem.
2. **Hidden unit volume** — carry `D.volume` or use normalized averages; TEST on interval of length ≠ 1.
3. **Hidden `H¹↪L^∞`** — use `SobolevAdmissible D k p q`; TEST a `dim=2` poison instance must NOT synthesize it.
4. **Hardcoded `3/4<σ`, `7/8`** — use `C1Admissible σ p`; forbid those literals in generic files.
5. **Fake `X^σ = supNorm`** — genuine Banach `X σ p` + realization + embedding; no `SupClose→XσClose` at t=0 (only positive-time smoothing).
6. Incomplete spectrum — split gap-only vs full eigenbasis; `HasNeumannSpectrum` currently does NOT certify completeness/multiplicity.
7. Disconnected domain — require connectedness / `ker Δ_N = constants`.
8. `p.N` vs actual dimension — `ParametersMatchDomain`.
9. Scalar boundary-derivative leakage — generic code sees only normal traces/Green forms; forbid `intervalDomainLift`, `Icc 0 1`, `Real.pi`, `cosine`, `deriv (fun x=>…)` in generic spatial files.
10. Non-uniform constants (Moser/continuation need uniform-in-exponent/horizon/restart) — expose constants as functions with growth property.
11. Monolithic typeclass — typeclasses for canonical facts, explicit records for theorem-specific choices.
12. Assumed-as-proved — two namespaces `AssumedNeumann` vs `ConcreteNeumann`; general-Ω stays explicitly conditional until instance proved.

## 8. My read (Zinan, 2026-07-16)

- **Highest-leverage, lowest-risk, start-now:** the lawful-layer + consumer-first
  refactor (PR1–3) done PURELY on existing 1D code. Costs no new math, yields a
  general-Ω-CONDITIONAL headline immediately, and the leak-detector tests
  (non-unit-length interval, dim=2 poison) will MEASURE how much of the 766k LOC is
  genuinely domain-generic vs secretly 1D — the real unknown. Worth doing regardless
  of whether we commit to full general-N, because it also hardens the 1D work.
- **Cleanest first MATH win:** Thm 2.2 linear dichotomy (full-spectrum abstraction only).
- **The genuine mountain:** the bounded-domain PDE backend Mathlib lacks (Prop 2.2
  weighted gradient + sectorial Neumann + W^{2,p} + Sobolev/trace). Multi-person,
  long-horizon; different scale from the current 1D headline sprint.
- **Paper 1 (traveling waves) stays a SEPARATE whole-line branch** — planar-wave
  profile reduces to the 1D profile problem (profile existence/uniqueness may lift),
  but transverse N-dim stability is a genuinely new (possibly false) problem; do not
  force it into the bounded-Ω abstraction.
- **Hardest danger to police:** silently keeping unit-volume / H¹↪L^∞ / σ>3/4 /
  `xpSigmaDistance=supNorm` while type-variable-izing the domain → a generic-LOOKING
  API that is still mathematically 1D. The risk register tests are mandatory.
