# F2-core design reply — classical local existence for Paper 2 Thm 1.1

Independent blind review. Worktree `~/repos/shen_work`. All lemma names below are
copied from the actual source; line numbers are at time of reading (2026-06-06).

PDE-analyst summary first, infrastructure second, as mandated.

---

## 0. The mathematically lightest honest proof (analyst's verdict, before Lean)

The problem is 1D, on `[0,1]`, Neumann, scalar `u`, with `v` slaved to `u`
through an **elliptic** resolvent (so `v` and `∂ₓv = resolverGradReal` are as
smooth as the elliptic theory gives, with `R ≥ 0`, `(1+R)^β` bounded below — no
parabolic coupling, no `v`-time-derivative to track). The chemotaxis term is in
**divergence form** `−χ₀ ∂ₓ[u φ(v) ∂ₓv]`, with the flux `Q = u·∂ₓR/(1+R)^β`
being a **C⁰ object on the C⁰ ball** (it never needs `∂ₓQ` — confirmed:
`chemFluxLifted`, `IntervalGradientDuhamelMap.lean:47`).

For a 1D scalar equation with a C⁰ divergence-form drift and a Lipschitz
(globally, on a ball, sub-linear-after-truncation) reaction, the lightest honest
local theory is **not** a high-regularity Schauder fixed point and **not** a
spectral Picard in a weighted ℓ¹ sequence space. It is:

> **Mild Picard in C⁰ (already done) + a single quantitative parabolic
> smoothing step that lands the solution in C^{1,γ}_x for every t>0, promoted to
> the *spectral* C² class on each half-step by the Wiener-algebra envelope of the
> source.**

The reason this is the lightest: the C⁰ contraction is *already proved*
(`gradDuhamel_sup_bound`, `valueDuhamel_sup_bound`, and their `diff` Lipschitz
twins — `IntervalGradDuhamelBound.lean:72,129,180,227`). The map is a genuine
contraction on the C⁰ ball with the parabolic `√T` / `T` gains. The mild
solution exists (Picard, `intervalMildSolution_exists_picard`). The *only*
residual is upgrading regularity of that fixed point to feed the
classical-bridge (`RestartCosineRepresentation`), and the cheapest currency for
that upgrade in this repo is **eigenvalue-weighted ℓ¹ of the half-step restart
source coefficients**, which is exactly what `DuhamelSourceTimeC1` already
consumes (`IntervalDuhamelClosedC2.lean:1373`).

So the analyst's route is a **hybrid**: keep the C⁰ mild map; do **one**
smoothing round in physical space to get `u(·,t) ∈ C^{0,γ}` then `Q(u) ∈
C^{0,γ}`; convert that Hölder gain into an absolutely-summable cosine envelope
for the restart source. This is route **R3′** below (a sharpened R3), and it
wins. Details and the satisfiability audit follow.

---

## 1. Obstruction verification

### Obstruction 1 — logistic-only `hagree` unsatisfiable for χ₀≠0. **CONFIRMED, real.**

`INTEGRITY_GAPS.md` 2026-06-06 is correct and the fix is already in place. The
logistic source `z(a−bz^α)` has range bounded above by `max_{z>0} z(a−bz^α)`
(finite for α≥1), while the flux-divergence contribution to the restart source
is unbounded in general. The committed fix —
`GradientMildHalfStepRestartData` carrying an **arbitrary**
`DuhamelSourceTimeC1` family (`IntervalMildRegularityBootstrap.lean:422`) — is
the right abstraction and is faithfully wired
(`paper2_theorem_1_1_from_two_restart`). **No action needed; do not route the
general regime through the logistic package.** Verified by reading the structure:
`GradientMildHalfStepRestartData.a : ℝ → ℝ → ℕ → ℝ` is unconstrained except
through `src : DuhamelSourceTimeC1` and `hagree` — it can carry the flux modes.

### Obstruction 2 — two-semigroup mixing `∂ₓ[S^N(r)g] = S^D(r)[g′]`. **CONFIRMED at kernel level, but MIS-SCOPED — it does NOT touch the winning route.**

Kernel-level verification (from the proved spectral kernel,
`IntervalFullKernelSpectralClean.lean:72`):

```
K_full t x y = ∑_{m∈ℤ} e^{−t(mπ)²} cos(mπx) cos(mπy)
∂ₓ K_full t x y = ∑_{m∈ℤ} e^{−t(mπ)²} (−mπ sin(mπx)) cos(mπy)
```

i.e. `∂ₓ` turns the **cosine** (Neumann) eigenfunction in `x` into a **sine**
(Dirichlet) eigenfunction in `x`, with the *same* eigenvalue `(mπ)²` and the
*same* cosine in `y`. So yes: differentiating a Neumann-propagated function
produces a Dirichlet-propagated object, and `∂ₓ S^N(r) g ≠ S^N(r)[∂ₓ g]` as
operators (the boundary terms differ). The brief's identity
`∂ₓK_N(x,y) = −∂_y K_D(x,y)` is the correct statement of this.

**However, this obstruction is fatal only for a route that tries to push `∂ₓ`
through `S` and then re-apply the Neumann cocycle to the *derivative*.** The
divergence-form Atom-D bound does **not** do this. `gradDuhamel_sup_bound`
(`IntervalGradDuhamelBound.lean:72`) differentiates `z ↦ S(t−s) q(s) z`
**directly** at the point `x` — it never splits `∂ₓ[S g] = S[g′]` and never
needs a two-semigroup identity. The per-slice singularity `(t−s)^{−1/2}` comes
from `intervalFullCoupledDuhamel_grad_integrand_pointwise_bound`, a *pointwise
kernel-derivative* bound, not a semigroup composition. **So obstruction 2 is
real but inert for any route built on the existing divergence-form Atom D.** It
*would* bite a naive "restart the flux part via the Neumann cocycle" plan (R2's
weakest form), which is one reason R2 ranks low.

The genuine variation-of-constants restart
`u(t) = S^N(τ)u(t/2) + ∫₀^τ S^N(τ−σ)[−χ₀(Q)_x + L]dσ` is **true for classical
solutions** and is exactly the route's target; the circularity the brief flags
(classical regularity is what we want to prove) is dissolved by the
**spectral** restart used in `RestartCosineRepresentation`: there the cocycle is
proved at the **coefficient** level (`e^{−tλ}=e^{−τλ}e^{−(t−τ)λ}`, TASK_QUEUE
S2), where everything is a cosine series and the Dirichlet/Neumann distinction
is absorbed into the eigenvalue algebra — no kernel Chapman–Kolmogorov, no
two-semigroup identity. Confirmed against `restartDuhamelCoeff`
(`IntervalMildRegularityBootstrap.lean:35`) and
`duhamelSpectral_eq_cosineSeries` (`IntervalDuhamelClosedC2.lean:1394`).

### Obstruction 3 — Wiener envelope `∑ₙ supₛ|aₙ(s)| < ∞` needs more than C². **CONFIRMED, and this is the true mathematical frontier.**

`DuhamelSourceTimeC1.henv_summable` requires a **summable** envelope dominating
`|aₙ(s)|` uniformly in `s` (`IntervalDuhamelClosedC2.lean:1380-1385`). For the
flux part, `aₙ ⊇` cosine coeffs of `(Q)_x`. The cosine coefficients of a C⁰
function are merely `o(1)` (Riemann–Lebesgue); of an `H²_N`/C² function they are
`O(1/n²)` — *summable*. So the envelope needs `(Q)_x ∈ H¹`-ish, i.e. `Q ∈ H²`,
i.e. `u ∈ H²` with `∂ₓR/(1+R)^β ∈ C²` (the latter from elliptic regularity, the
former is the unknown). **One smoothing round from C⁰ does NOT reach summable
cosine coefficients of `(Q)_x`** — it reaches C^{0,γ} for `u`, hence C^{0,γ} for
`Q`, whose cosine coefficients are `O(n^{−1−γ})`, summable **only for the
function itself, not its derivative**. To get `∑ₙ|cₙ((Q)_x)| < ∞` you need the
*derivative's* coefficients summable, i.e. `cₙ(Q) = O(n^{−2−δ})`, i.e. `Q ∈
C^{1,γ}` with a Dini/Hölder modulus — **two** smoothing rounds (C⁰→C^{0,γ}→C^{1,γ})
or one `Lᵖ→W^{1,p}` Calderón–Zygmund-type round followed by Sobolev embedding.
The repo's `duhamelSourceTimeC1_of_H2Neumann_timeC1`
(`IntervalSemigroupNeumann.lean:828`) already encodes the *consumption* side:
it takes `IntervalWeakH2Neumann` (an `H²_N` certificate, weak second derivative
with `L¹` bound, `IntervalMildSourceDecayHelper.lean:49`) and a `1/(kπ)²`
coefficient-decay hypothesis (`hdecay`,
`IntervalMildRegularityBootstrap.lean:450`) and produces the full
`DuhamelSourceTimeC1`. **So the envelope is reachable from `H²_N` + `O(1/k²)`
decay of the source — the frontier is producing that `H²_N`/decay certificate
for `Q(u(t/2+σ))`, not the envelope assembly.** The brief's "needs a second
bootstrap round" is exactly right.

### Obstruction 4 — `S(0)≠id` definitional degeneracy. **CONFIRMED, fully diagnosed, fix is known.**

`IntervalSemigroupAtZero.lean` proves `intervalFullSemigroupOperator 0 f x = 0`
for every `f,x` (kernel is identically 0 at `t=0` because `heatKernel 0 ≡ 0`),
hence `IntervalSemigroupIdentityAtZero f ↔ f|_{(0,1)} ≡ 0`
(`intervalSemigroupIdentityAtZero_iff_zero`, line 91) — **vacuous except for the
trivial solution.** `intervalDuhamelRepresentation_of`
(`IntervalDuhamelRepresentation.lean:206`) consumes `hid` in this unsatisfiable
form. **Confirmed mis-stated.** The fix is the one named in the file's own
docstring: replace the value-at-0 predicate by the one-sided limit
`Tendsto (fun t => S t f x) (𝓝[>]0) (𝓝 (f x))`, and run the FTC as an ε-restart
(`g(ε)→g(0⁺)`). The winning route below **avoids
`intervalDuhamelRepresentation_of` entirely** — it never invokes `S(0)=id`,
because the spectral restart `RestartCosineRepresentation` evaluates the cosine
*series* (which reconstructs `f x` at `τ→0⁺` via cosine completeness, with `τ>0`
strictly throughout) rather than the degenerate kernel. So obstruction 4 is
**circumvented, not solved**, by staying on the spectral side with `τ = t/2 > 0`.

---

## 2. Ranked comparison R1–R5

Scoring axes: **NC** = new-code estimate (Lean lines), **AA** = genuinely-new
analytic atoms (theorems with real ε-δ content, not bookkeeping), **HR** =
hidden-unsatisfiable-hypothesis risk, **RU** = reuse of the 8k-job infra.

| Route | NC | AA | HR | RU | Verdict |
|---|---|---|---|---|---|
| **R1** Spectral-space Picard (weighted ℓ¹) | ~3500 | 6–8 | **HIGH** | low | reject |
| **R2** Iterate induction + two-semigroup split | ~4000 | 7–9 | high | medium | reject |
| **R3** Classical-first Schauder-lite | ~2800 | 5–6 | medium | medium | runner-up |
| **R4** χ₀=0 first | ~1500 | 3 | **low** | **high** | adopt as **stage 1** |
| **R5 = R3′** Hybrid: keep C⁰ mild map, one Lᵖ→Hölder smoothing round → `H²_N`+decay certificate → existing envelope | ~2200 | **4** | **low–med** | **HIGH** | **winner** |

### Why R1 loses
A weighted-ℓ¹ Picard (`sup_t ∑_k(1+λ_k)|û_k(t)|`) must re-derive the *contraction*
in coefficient space, including the flux mode-mixing `c_k((Q)_x)` (sine↔cosine
coupling — obstruction 2 reappears as an off-diagonal operator on the sequence
space). The Duhamel integral "regains one power of λ" only against `e^{−(t−s)λ}`,
giving `∫₀ᵗ(t−s)^{−1/2}` per mode — the same `√T` gain, but now you must prove
**summability of the mixed-mode operator norm**, which is a genuinely new
infinite-matrix estimate with **high hidden-hypothesis risk** (the sine↔cosine
mixing matrix is not diagonal and its ℓ¹→ℓ¹ norm is the crux). And it throws
away the entire proved C⁰ Atom-D contraction. **NC high, AA high, HR high, RU low.**

### Why R2 loses
Carrying C² with uniform constants through the Picard induction
(`PicardIterateHasC2Slices` exists but qualitative) requires building the
**Dirichlet kernel/semigroup** to even *state* the two-semigroup split (currently
absent — confirmed no `S^D` in repo). That is a large, genuinely-new module.
G2.5 (`duhamelSourceTimeC1_of_uniform_limit`) is nice but the per-iterate
uniform C² constants are the hard part, and obstruction 2 is *live* here. **NC
highest, RU medium.**

### Why R3 is runner-up not winner
R3 (classical-first C^{2,γ} fixed point) is sound and avoids restart entirely,
but a C^{2,γ} *fixed point* needs the heat semigroup as a bounded map
`C^{0,γ}→C^{2,γ}` with the **Schauder constant**, which the repo's toolkit does
**not** currently express: there is `intervalHeatSemigroup_Lp_Lq_bound`
(`HeatKernelLpEstimates.lean:881`, the `t^{−½(1/p−1/q)}` Lᵖ→Lq smoothing) and the
pointwise gradient `(t−s)^{−1/2}` and the spectral `1/t` gradient L²→L∞, but **no
Hölder-seminorm semigroup bound and no fractional-power / interpolation-space
machinery.** Building Schauder-on-the-interval from scratch is ~2800 lines of
genuinely-new harmonic analysis. R5 reuses the **existing** C⁰ contraction and
needs only the *one* smoothing estimate that the repo can already almost express.

### Why R4 is stage 1 (not the whole answer)
χ₀=0 kills obstructions 1–2 outright (single semigroup, logistic-only restart is
faithful, cocycle clean — TASK_QUEUE S2–S6). It is **low-risk, high-reuse**, and
closes a genuine sub-regime of Theorem 1.1. But it is **not** the general
theorem (χ₀<0 is the physical chemotaxis case). **Adopt R4 as the de-risking
first milestone**, then layer the flux on top via R5.

### Why R5 (= R3′ hybrid) wins
- Keeps the **proved** C⁰ mild map and its contraction (RU high).
- The single new analytic atom is a **physical-space parabolic smoothing
  estimate** turning the C⁰ mild fixed point into a `H²_N` + `O(1/k²)`-decay
  certificate for the *half-step* restart source `Q(u(t/2+σ))`. This is exactly
  what `duhamelSourceTimeC1_of_H2Neumann_timeC1` consumes — **the envelope
  assembly is already done.**
- Obstruction 2 is inert (divergence-form Atom D, no two-semigroup split).
- Obstruction 4 is circumvented (spectral restart, `τ=t/2>0`).
- Obstruction 3 is *the* remaining work, but it is localized to one certificate.
- The flux's sine↔cosine mixing is handled **once**, inside the `H²_N`
  certificate for `Q` (its weak second derivative), not as an operator on a
  sequence space.

**Winner: R5, staged behind R4.**

---

## 3. Winner R5 — dependency DAG and first three module signatures

### 3.1 Dependency DAG

```
                 [proved infra, reuse as-is]
  IntervalGradDuhamelBound (Atom D: gradDuhamel_sup_bound, valueDuhamel_sup_bound,
                            *_diff_sup_bound)                         ── C⁰ contraction
  IntervalGradientDuhamelMap (Φ, IntervalMildSolution)               ── fixed point
  HeatKernelLpEstimates.intervalHeatSemigroup_Lp_Lq_bound           ── Lᵖ→Lq smoothing
  HeatKernelGradientEstimates.*_L1_Linfty / *_L2_Linfty             ── gradient smoothing
  IntervalDuhamelClosedC2.{DuhamelSourceTimeC1,                      ── envelope→C²
        duhamelSpectral_eq_cosineSeries,
        duhamelSpectralCoeff_eigenvalue_summable}
  IntervalSemigroupNeumann.duhamelSourceTimeC1_of_H2Neumann_timeC1  ── H²→envelope
  IntervalMildSourceDecayHelper.{IntervalWeakH2Neumann,             ── H² certificate
        intervalWeakH2Neumann_of_contDiffOn}
  IntervalMildRegularityBootstrap.{RestartCosineRepresentation,     ── classical bridge
        GradientMildHalfStepRestartData, hasRestart...}
  IntervalNeumannEllipticResolverR / IntervalResolverSpatialC2      ── v, ∂ₓv regularity
                                   │
                                   ▼
   ┌──────────────────────────────────────────────────────────────────────┐
   │ NEW MODULE A  IntervalMildSmoothingHolder.lean                         │
   │   mild C⁰ fixed point  ⟹  u(·,t) ∈ C^{0,γ}_x, with quantitative        │
   │   Hölder seminorm, for every t>0   (one Lᵖ→C^{0,γ} round via           │
   │   intervalHeatSemigroup_Lp_Lq_bound + Morrey/Sobolev embedding 1D)     │
   └──────────────────────────────────────────────────────────────────────┘
                                   │
                                   ▼
   ┌──────────────────────────────────────────────────────────────────────┐
   │ NEW MODULE B  IntervalFluxH2Certificate.lean                           │
   │   u ∈ C^{0,γ} (+ elliptic ∂ₓR/(1+R)^β ∈ C²)  ⟹                          │
   │   Q(u(s)) ∈ IntervalWeakH2Neumann  with cosine-coeff decay O(1/k²)      │
   │   uniformly in s on each half-step  (second smoothing round)           │
   └──────────────────────────────────────────────────────────────────────┘
                                   │
                                   ▼
   ┌──────────────────────────────────────────────────────────────────────┐
   │ NEW MODULE C  IntervalGradientRestartAssembly.lean                     │
   │   modules A,B + duhamelSourceTimeC1_of_H2Neumann_timeC1 + spectral      │
   │   restart cocycle  ⟹  GradientMildHalfStepRestartData D                 │
   │   (discharges hMildLocal-abstract via hasRestartCosineRepresentations…) │
   └──────────────────────────────────────────────────────────────────────┘
                                   │
                                   ▼
        paper2_theorem_1_1_from_two_restart  (hMildLocal closed; hQuant via Q1–Q4)
```

The DAG is a **chain of 3 new modules** on top of existing infra — no new kernel,
no fractional powers, no Dirichlet semigroup.

### 3.2 First three module signatures (Lean statements, NO proofs)

These are *signatures only*. Every hypothesis is audited for satisfiability in §4.

**Module A — Hölder smoothing of the mild fixed point.**

```lean
-- IntervalMildSmoothingHolder.lean
namespace ShenWork.IntervalMildSmoothingHolder
open ShenWork.IntervalGradientDuhamelMap ShenWork.IntervalDomain

/-- One parabolic smoothing round: a C⁰ mild fixed point is, at every positive
time, Hölder-continuous in space with a quantitative seminorm growing like
t^{-(1/2 - γ/2 - …)}.  Proved from the value/gradient Duhamel sup bounds plus the
Lᵖ→Lq smoothing `intervalHeatSemigroup_Lp_Lq_bound` and 1D Morrey embedding
W^{1,p}↪C^{0,1-1/p}.  γ is any exponent in (0,1). -/
theorem intervalMild_holder_of_mildSolution
    {p : CM2Params} {T : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {M : ℝ}
    (hmild : IntervalMildSolution p T u₀ u)
    (hbound : ∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M)
    (hpos   : ∀ t, 0 < t → t ≤ T → ∀ x, 0 < u t x)
    (γ : ℝ) (hγ : γ ∈ Set.Ioo (0:ℝ) 1) :
    ∃ Cγ : ℝ → ℝ,   -- t ↦ Hölder constant, finite for t>0
      (∀ t, 0 < t → t < T → 0 ≤ Cγ t) ∧
      (∀ t, 0 < t → t < T → ∀ x y : ℝ, x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 →
        |intervalDomainLift (u t) x - intervalDomainLift (u t) y|
          ≤ Cγ t * |x - y| ^ γ)
```

**Module B — `H²_N` + decay certificate for the half-step flux source.**

```lean
-- IntervalFluxH2Certificate.lean
namespace ShenWork.IntervalFluxH2Certificate
open ShenWork.IntervalGradientDuhamelMap ShenWork.IntervalMildSourceDecayHelper
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

/-- Second smoothing round: from the spatial Hölder bound on `u(s)` (Module A)
and the elliptic C²-regularity of the resolver factor, the chemotaxis flux
`Q(u(s))` smoothed by S(τ−σ) admits a weak-H²-Neumann certificate whose cosine
coefficients decay like C/(kπ)². This is the exact pair of facts consumed by
`duhamelSourceTimeC1_of_H2Neumann_timeC1`. -/
theorem intervalFlux_H2Neumann_and_decay
    {p : CM2Params} {T : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hmild : IntervalMildSolution p T u₀ u)
    (hholder : /- the conclusion of Module A, as a hypothesis -/ True)  -- placeholder; see §4
    {t : ℝ} (ht : 0 < t) (htT : t < T) :
    ∀ σ : ℝ, 0 ≤ σ →
      IntervalWeakH2Neumann
        (fun y => chemFluxLifted p (u (t/2 + σ)) y) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
        |cosineCoeffs (fun y => chemFluxLifted p (u (t/2 + σ)) y) k|
          ≤ C / ((k : ℝ) * Real.pi) ^ 2
```

**Module C — restart data assembly (closes hMildLocal-abstract).**

```lean
-- IntervalGradientRestartAssembly.lean
namespace ShenWork.IntervalGradientRestartAssembly
open ShenWork.IntervalMildRegularityBootstrap ShenWork.IntervalMildPicard

/-- Assemble the faithful half-step restart data for the gradient mild solution
from the two smoothing modules. The `src` field comes from
`gradientMildHalfStepRestartData_of_H2SourceData` once Module B supplies the
`GradientMildHalfStepH2SourceData` fields; `hagree` comes from the spectral
restart cocycle (e^{-tλ}=e^{-τλ}e^{-(t-τ)λ} + duhamelSpectral_eq_cosineSeries),
with τ = t/2 > 0 throughout (no S(0)=id). -/
noncomputable def gradientMildHalfStepRestartData_of_smoothing
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (HA : /- Module A conclusion for D.u -/ True)   -- placeholder; see §4
    (HB : /- Module B conclusion for D.u -/ True) : -- placeholder; see §4
    GradientMildHalfStepRestartData D
```

(The `True` placeholders in B/C are flagged as **must-be-replaced-by-real-data**
in §4 — they are exactly the spots where an unsatisfiable interface could hide.)

---

## 4. Satisfiability audit of every new predicate

Precedents to honor: `S(0)=id` (a value-at-0 predicate that turned out to force
trivial data — `intervalSemigroupIdentityAtZero_iff_zero`) and logistic-`hagree`
(bounded range cannot represent unbounded flux). Both were *plausible-looking but
unsatisfiable*. Audit each new obligation against that bar.

| # | Predicate / field | Satisfiable? | Evidence / risk |
|---|---|---|---|
| A1 | `∃ Cγ, …Hölder bound` (Module A conclusion) | **YES** | This is a *theorem about the existing solution*, not an interface the caller must guess. The mild fixed point is `S(t)u₀ + Duhamel`; `S(t)u₀` is C^∞ for t>0 (cosine series, `…contDiff_two_clean`), the value-Duhamel of a bounded source is C^{0,1} (Lipschitz, from `t^{-½(1/p−1/q)}` smoothing + Morrey), the gradient-Duhamel of a bounded flux is C^{0,γ} for γ<1/2 (the `(t−s)^{−1/2}` integrand gives a finite γ<1/2 Hölder seminorm — standard 1D parabolic). **The exponent ceiling γ<1/2 is real** and is the only subtlety. |
| A2 | inputs `hbound`, `hpos` | **YES** | `hbound` is `GradientMildSolutionData.hbound`; `hpos` is `D.hpos` (already in the structure, `IntervalMildRegularityBootstrap.lean:529-536` use it). No new burden. |
| B1 | `IntervalWeakH2Neumann (chemFluxLifted p (u(s)))` | **CONDITIONAL — the crux.** | Requires `Q(u(s)) ∈ H²_N` after one S(τ−σ) smoothing. **Risk:** γ<1/2 from A1 gives `u ∈ C^{0,γ}`, `Q ∈ C^{0,γ}`; *one more* heat smoothing S(τ−σ) lifts C^{0,γ}→C^{2,γ'} only if the elliptic factor `∂ₓR/(1+R)^β` is itself C² (it is — `IntervalResolverSpatialC2.lean`). The genuine content: **product of C^{0,γ} (=u) and C² (=elliptic factor) is C^{0,γ}; smoothed once by the heat semigroup it becomes C^{1,γ}; smoothed by the *integrated* Duhamel it is C^{2,γ'}.** This needs the **value-Duhamel C² regularity** which the repo HAS in spectral form (`intervalDuhamelTerm_closedC2_of_timeC1_source`) but only *given* the envelope — so B1 must be proved by a **direct physical-space second-derivative bound**, not by re-using the spectral C². **This is the single new ε-δ atom and the main 2-week risk.** |
| B2 | cosine-coeff decay `≤ C/(kπ)²` | **YES given B1** | `IntervalWeakH2Neumann` already *contains* `weak_cosine_laplacian` (line 54), which gives `cₖ(Q)·(kπ)² = −cₖ(Q'')`; with `Q'' ∈ L¹` (the `second_abs_integral_bound`, line 52) Riemann–Lebesgue gives `|cₖ(Q)| ≤ ‖Q''‖_{L¹}/(kπ)²`. So **B2 is an algebraic consequence of B1**, not independent. Mirrors `duhamelSourceTimeC1_of_H2Neumann_timeC1.hdecay`. Low risk. |
| C1 | `GradientMildHalfStepH2SourceData` fields (source, C, hH2, hdecay, adot, hderiv, hadotcont, Mdot, hMdot, ha0_bound) | **YES given A,B + time-C¹** | All of these are *consumed* by the proved `gradientMildHalfStepRestartData_of_H2SourceData` (`IntervalMildRegularityBootstrap.lean:475`). The non-trivial new ones beyond B are the **time-derivative** fields (`adot`, `hderiv`, `hadotcont`, `hMdot`): `s ↦ cₙ(Q(u(t/2+s)))` must be C¹ in `s` with uniformly bounded derivative. **Risk: medium** — needs time-regularity of the mild path, which Picard gives as Lipschitz-in-time on the C⁰ ball (the Duhamel integrand is continuous; `∂ₛ` of the half-step source = coeff of `∂ₛ(Q∘u)`, and `∂ₛ u` is controlled by the mild equation). This is the analogue of TASK_QUEUE S3/S5 for the flux. |
| C2 | `hagree` (spectral restart cocycle) | **YES, τ=t/2>0** | The agreement `u(t) = ∑ₙ restartDuhamelCoeff(a₀,a,t/2)ₙ cosₙ` is the **spectral** restart identity, proved from `e^{−tλ}=e^{−(t/2)λ}e^{−(t/2)λ}` (homogeneous part) and `duhamelSpectral_eq_cosineSeries` (`IntervalDuhamelClosedC2.lean:1394`) for the source part, with `a₀ = gradientMildHalfStepInitialCoeff D t` (cosine coeffs of `u(t/2)`, already bounded by `gradientMildHalfStepInitialCoeff_abs_le`). **No `S(0)=id`** because every exponential carries `τ=t/2>0`. The cosine *completeness* needed to identify the series with `u(t)` is `intervalFullSemigroupOperator_eq_cosineHeatValue_clean` at t/2>0. **This is the obstruction-4 circumvention; satisfiable.** |
| C3 | the `True` placeholders in §3.2 B/C signatures | **MUST be replaced** | Flagged explicitly: in the *final* Lean these become the **actual conclusion types** of Modules A and B (a Hölder-bound proposition and the H²+decay proposition). They are `True` in this design only to keep signatures readable. **The audit requirement: never ship C with a `True`/`trivial` field — that would be the new "S(0)=id".** Each must carry the real data so the structure is non-vacuous. |

**Verdict:** the only genuinely-new ε-δ atom is **B1** (physical-space C² /
`H²_N` bound on the smoothed flux). Everything else is either reuse, algebraic
consequence, or time-regularity bookkeeping. No predicate is unsatisfiable-by-
construction in the `S(0)=id` / logistic sense, **provided C ships real fields
(C3)**.

---

## 5. Risk register — what could kill R5 after 2 weeks

1. **(B1, HIGH) The Hölder exponent ceiling γ<1/2 is too low for `H²`.**
   The gradient-Duhamel integrand `(t−s)^{−1/2}` caps the *first* smoothing round
   at C^{0,γ}, γ<1/2. Reaching `H²_N` for `Q` then needs the *second* round to
   buy two full derivatives off C^{0,γ<1/2}. In 1D this is fine in principle
   (heat semigroup maps C^{0,γ}→C^{2,γ} with the `t^{−1}` cost), but the repo has
   **no Hölder-norm semigroup bound** — only Lᵖ→Lq and pointwise gradient. **If
   the physical-space second-derivative bound for the Duhamel flux term cannot be
   closed without a Schauder estimate, R5 collapses into R3 and the 2 weeks are
   lost on harmonic analysis.** Mitigation: prove B1 via the **spectral** second
   derivative `cosineCoeffSeries_deriv2_eq` route *backwards* — i.e. get the
   coefficient decay first (from `H²` weak-IBP, which only needs `Q'' ∈ L¹`, a
   much weaker `W^{2,1}` not `C^{2,γ}` requirement) and skip pointwise C². The
   `IntervalWeakH2Neumann` structure is deliberately `L¹`-based (line 52), so
   **target `Q ∈ W^{2,1}` not `Q ∈ C^{2,γ}`** — this is the key de-risking move
   and should be tried first.

2. **(C1, MEDIUM) Time-C¹ of the flux coefficients.**
   `s ↦ cₙ(Q(u(t/2+s)))` C¹ with uniform `Mdot` requires `∂ₛ u` control. Picard
   gives time-Lipschitz, not obviously C¹. If only Lipschitz is available,
   `DuhamelSourceTimeC1.hderiv` (which wants `HasDerivAt`) fails. Mitigation:
   strengthen the Picard iterate time-regularity (TASK_QUEUE S3 analogue) or relax
   `DuhamelSourceTimeC1` to an a.e.-derivative form — but the latter touches a
   proved 8k-job structure and is itself risky.

3. **(elliptic, LOW–MEDIUM) Resolver factor C² uniformity.**
   `∂ₓR/(1+R)^β ∈ C²` must hold *uniformly* as `u` ranges over the ball and as a
   function of the (only C^{0,γ}) `u`. `IntervalResolverSpatialC2.lean` gives
   spatial C² of `R` for fixed data; the **composition** with a merely-Hölder `u`
   may drop regularity. Need: `R[u] ∈ C²` with constants depending only on
   `‖u‖_{C⁰}` (elliptic gain, plausible since `R` solves `−R''+R=u`-type, gaining
   2 derivatives). Skimmed `IntervalNeumannEllipticResolverR.lean` (709 lines) —
   the machinery is present; the *uniform-in-Hölder-u* statement may not be.

4. **(scope, MEDIUM) hQuant is orthogonal and also open.**
   Even with hMildLocal closed via R5, Theorem 1.1 needs hQuant (uniform δ(M),
   inf-u₀-independent). TASK_QUEUE Q1–Q4 route it through cone invariance; for
   χ₀≠0 it needs the kernel-derivative comparison `|∂ₓK(r,x,y)| ≤ C r^{−1/2}
   K(2r,x,y)` (Q3, "hard, defer"). **R5 does not address hQuant.** Risk that the
   theorem is still blocked on hQuant after hMildLocal lands.

5. **(staging, LOW) R4-first might absorb the calendar.**
   Doing χ₀=0 first (recommended) is genuinely ~1500 lines and could consume the
   2 weeks by itself, leaving the flux (the actual frontier) untouched. Mitigation:
   timebox R4 to the spectral cocycle (S1–S2 already half-built) and move to B1
   early, since B1 is the true unknown.

---

## 6. Bottom line

- **Obstructions 1, 3, 4 confirmed real**; **2 confirmed real but inert** for any
  divergence-form route. The current interface fixes (abstract restart data) are
  correct.
- **Winner: R5** — keep the proved C⁰ mild contraction; add **3 modules** whose
  only genuinely-new analytic atom is **B1** (a `W^{2,1}`/`H²_N` certificate for
  the smoothed chemotaxis flux), feeding the **already-proved**
  `duhamelSourceTimeC1_of_H2Neumann_timeC1` envelope and the **spectral** restart
  (τ=t/2>0, no `S(0)=id`).
- **Stage behind R4** (χ₀=0) to de-risk obstructions 1–2 and validate the
  spectral cocycle before adding flux.
- **The decisive de-risking instruction for B1:** target `Q ∈ W^{2,1}` (weak
  second derivative in `L¹`, which is what `IntervalWeakH2Neumann` actually
  requires) — **not** `C^{2,γ}` — so the route never needs a Schauder/Hölder
  semigroup bound the repo lacks. Get the `O(1/k²)` coefficient decay from
  weak-IBP + Riemann–Lebesgue, not from pointwise C².
- **No predicate introduced is unsatisfiable-by-construction**, on the explicit
  condition that Module C ships real data fields (never a `True`/`trivial`
  placeholder — that is the lesson of `S(0)=id`).
