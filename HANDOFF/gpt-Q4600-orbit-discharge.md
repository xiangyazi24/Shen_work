ANSWER Q4600 8db9bbe3

# Paper 3 sectorial keystone: the valid frontier is eventual, equilibrium-specific, full-mode, and mass-free

## Executive verdict

There are two separate conclusions.

1. **Among the proposed orbit frontiers, the mathematically correct analytic object is the equilibrium-specific eventual one without a mass hypothesis** — the shape called `...EventualEquilibriumWithoutMass` in the question.  It must use the actual linearized multiplier

   ```text
   exp (-d_k t),
   d_k = A + λ_k - κ λ_k/(λ_k+μ),
   ```

   for **every** mode `k`, including `k = 0`.  It must only assert the strong/C¹ estimate after a uniform positive delay `t₀ > 0`.

2. **That eventual estimate does not discharge the repository's current
   `MassConstrainedLocallyExponentiallyStableFromSup` definition.**  The current target concludes `ExponentialC1ConvergenceWith`, whose quantifier is `∀ t, 0 ≤ t`, with one constant `A` uniform over the whole sup-small datum class.  That conclusion is false for a genuine C¹ distance when the input is only sup-close.  The target must be changed to an eventual target, or the initial-data hypothesis must be strengthened to a strong/C¹ norm.

There is also a branch mismatch in the statement layer: `MassConstrainedLocallyExponentiallyStableFromSup` is documented in `Statements.lean` as the **minimal-model** stability package.  For the positive logistic equilibrium `a,b>0`, the natural target is `LocallyExponentiallyStableFromSup`; imposing the mass condition merely restricts the datum class and is analytically unnecessary.

On the connector-visible `chatgpt-scratch` branch, `IntervalDomainSectorial.lean` still wires the old
`IntervalDomainSpectralSemigroupOrbitBoundRaw`.  That definition uses
`unitIntervalNeumannHeatSemigroupP0Compl` and quantifies over all `t ≥ 0`.  I did not find the four later experimental names wired into that file, so the signatures below are the corrected interfaces to land, not a claim that those exact declarations already compile.

---

# 1. Audit of the proposed candidates

| Candidate | Verdict | Decisive reason |
|---|---|---|
| `IntervalDomainSpectralSemigroupOrbitBoundRaw` | **Refute** | It uses the pure Neumann heat multiplier with `P₀` removed.  The actual linearized operator has multiplier `e^{-d_k t}` and has a stable, dynamically relevant zero mode `d₀=A`. |
| `...Corrected` with `∀ t ≥ 0` | **Refute** | Sup-small data do not have a uniformly bounded strong/C¹ norm as `t ↓ 0`.  Replacing the multiplier does not repair the zero-time singularity. |
| `...AllTimeExistentialRate` | **Refute** | Making the decay rate existential does not repair the unbounded prefactor at small positive times.  The obstruction is spatial smoothing, not the choice of rate. |
| `...EventualWithoutEquilibrium` | **Insufficient as a public frontier** | The linear rates, nonlinear Taylor remainder, and zero-mode damping depend on the selected equilibrium.  A completely equilibrium-free statement cannot expose the hypotheses needed by the proof. |
| `...EventualEquilibriumWithoutMass` | **Correct analytic frontier** | It has a positive delay, uses the actual full-mode linearization, and proves a stronger result for all nearby data.  The outer theorem may then restrict to mass-constrained data if desired. |

## 1.1 The all-time C¹ obstruction is real even with the mass condition

Let

```text
u₀,N(x) = u* + η_N cos(Nπx),
η_N = N^{-1/2}.
```

For all sufficiently large `N`:

* `u₀,N > 0`;
* `‖u₀,N-u*‖∞ = η_N → 0`;
* `∫₀¹ u₀,N = u*`, so the repository mass constraint is satisfied exactly;
* the Neumann compatibility condition holds;
* the initial perturbation is a single nonzero cosine mode.

For the stable linearized flow, set `λ_N=(Nπ)²` and `t_N=1/λ_N`.  Then

```text
‖∂ₓ S_L(t_N)(u₀,N-u*)‖∞
  = η_N Nπ exp(-d_N/λ_N).
```

Since `d_N/λ_N → 1`, the right side is asymptotic to

```text
π e^{-1} √N → ∞.
```

But any estimate of the current form

```text
C1Distance(t) ≤ A exp(-ρ t)     for every t ≥ 0
```

with `A` uniform over a fixed sup ball gives a right side bounded by `A` at `t=t_N`.  This is impossible.  The same obstruction can be stated as the familiar operator fact

```text
‖S_L(t)‖_{L∞→C¹} ≍ t^{-1/2}
```

near `t=0`.

This is not fixed by the repository's weak `InitialTrace`: even if the value assigned to `u 0` is unconstrained, the contradiction occurs at the strictly positive times `t_N`.

Consequently, no eventual orbit estimate can be adapted to the current all-time `ExponentialC1ConvergenceWith` without an additional, false uniform finite-window C¹ bound.

---

# 2. The exact corrected eventual statement

## 2.1 Full linearized multiplier

For the positive equilibrium, define the decay rate for **all** cosine modes:

```lean
def positiveLinearDecayRate
    (p : CM2Params) (uStar vStar : ℝ) (k : ℕ) : ℝ :=
  -sigma p uStar vStar
    (unitIntervalNeumannSpectrum.eigenvalue k)

def actualLinearSemigroupCoeff
    (p : CM2Params) (uStar vStar t : ℝ)
    (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  Real.exp (-(positiveLinearDecayRate p uStar vStar k) * t) * a k
```

This replaces `unitIntervalNeumannHeatSemigroupP0Compl`.  There is no projection away from `k=0`.

## 2.2 Eventual C¹ convergence

```lean
def EventualExponentialC1ConvergenceWith
    (D : BoundedDomainData) (N : StabilityNorms D)
    (u v : ℝ → D.Point → ℝ)
    (uStar vStar t₀ C rate : ℝ) : Prop :=
  0 < t₀ ∧ 0 < C ∧ 0 < rate ∧
    ∀ t, t₀ ≤ t →
      N.c1Distance (u t) (fun _ => uStar) +
          N.c1Distance (v t) (fun _ => vStar) ≤
        C * Real.exp (-rate * (t - t₀))
```

For an orbit estimate that records continuous dependence on the datum, use the sharper version

```text
C · ‖u₀-u*‖∞ · exp(-rate·(t-t₀)).
```

That factor can be absorbed into `C·δ` when packaging a local-stability proposition.

## 2.3 Minimal fixed-strong-space frontier

Only one admissible strong space is needed to prove the headline.  Quantifying over every `sigma` and every `pNorm`, as the present raw frontier does, is stronger than necessary.

```lean
def IntervalDomainEventualEquilibriumOrbitBoundAt
    (p : CM2Params) (N : StabilityNorms intervalDomain)
    (sigma pNorm : ℝ) : Prop :=
  1 / 2 < sigma ∧ sigma < 1 ∧ 1 < pNorm ∧
  ∀ (ha : 0 < p.a) (hb : 0 < p.b),
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 →
      ∃ eps > 0, ∃ t₀ > 0, ∃ C > 0, ∃ rate > 0,
        ∀ u₀ : intervalDomain.Point → ℝ,
          PositiveInitialDatum intervalDomain u₀ →
          SupCloseToConstant intervalDomain u₀ eq.1 eps →
          ∀ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2GlobalClassicalSolution intervalDomain p u v →
            InitialTrace intervalDomain u₀ u →
            ∀ t, t₀ ≤ t →
              N.c1Distance (u t) (fun _ => eq.1) +
                  N.c1Distance (v t) (fun _ => eq.2) ≤
                C * intervalDomain.supNorm (fun x => u₀ x - eq.1) *
                  Real.exp (-rate * (t - t₀))
```

A repository-style reusable wrapper may quantify over all admissible `(sigma,pNorm)`, but this fixed-pair declaration is the minimal logical input.

The candidate name in the question can then be used as:

```lean
def IntervalDomainSpectralSemigroupOrbitBoundEventualEquilibriumWithoutMass
    (p : CM2Params) (N : StabilityNorms intervalDomain) : Prop :=
  ∃ sigma pNorm,
    IntervalDomainEventualEquilibriumOrbitBoundAt p N sigma pNorm
```

The word `SpectralSemigroup` is acceptable only if the implementation uses `actualLinearSemigroupCoeff`; it must not reuse the pure heat `P₀`-complement operator.

## 2.4 Correct target proposition

```lean
def EventuallyLocallyExponentiallyStableFromSup
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (uStar vStar : ℝ) : Prop :=
  ∃ delta > 0, ∃ t₀ > 0, ∃ A > 0, ∃ rate > 0,
    ∀ u₀ : D.Point → ℝ,
      PositiveInitialDatum D u₀ →
      SupCloseToConstant D u₀ uStar delta →
        ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2GlobalClassicalSolution D p u v ∧
          InitialTrace D u₀ u ∧
          EventualExponentialC1ConvergenceWith
            D N u v uStar vStar t₀ A rate

def MassConstrainedEventuallyLocallyExponentiallyStableFromSup
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (uStar vStar : ℝ) : Prop :=
  ∃ delta > 0, ∃ t₀ > 0, ∃ A > 0, ∃ rate > 0,
    ∀ u₀ : D.Point → ℝ,
      PositiveInitialDatum D u₀ →
      SupCloseToConstant D u₀ uStar delta →
      D.integral u₀ = D.volume * uStar →
        ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2GlobalClassicalSolution D p u v ∧
          InitialTrace D u₀ u ∧
          EventualExponentialC1ConvergenceWith
            D N u v uStar vStar t₀ A rate
```

The non-mass theorem immediately implies the mass-constrained one by ignoring the extra hypothesis.

---

# 3. Linear gap and the zero mode

Write

```text
A = a α > 0,
K = χ₀ γ ν u*^γ (1+v*)^{-β},
λ_k = (kπ)²,
d(λ) = A + λ - K λ/(λ+μ).
```

For `k=0`,

```text
d₀ = A.
```

This is already reflected by the committed lemmas

```lean
sigma_zero
sigma_zero_neg_of_a_pos
```

although the repository definition `LinearlyStable` only quantifies over `n ≠ 0`.  Any full semigroup theorem must combine `LinearlyStable` with `sigma_zero_neg_of_a_pos`.

## 3.1 Exact continuous spectral gap

For `λ ≥ 0`, put `y=λ+μ`.  Then

```text
d(λ) = A + y - μ - K + Kμ/y.
```

If `K ≤ μ`, the minimum is attained at `λ=0` and equals `A`.  If `K>μ`, the minimum is attained at

```text
λ* = √(Kμ)-μ
```

and equals

```text
A - (√K-√μ)².
```

Thus one may take

```text
δ_lin = A - (max (√K-√μ) 0)².
```

The condition

```text
K < (√μ+√A)²
```

is exactly what makes `δ_lin>0`.

## 3.2 Full-rate coercivity

The spectral gap alone controls low modes.  For smoothing one also needs growth with `λ`.
Since

```text
d(λ) ≥ A + λ - K,
```

let

```text
R = max 1 (2 * max (K-A) 0),
c_* = min (1/4) (δ_lin/(1+R)).
```

Then, for every `λ≥0`,

```text
d(λ) ≥ c_* (1+λ).
```

Indeed:

* if `λ≤R`, use `d(λ)≥δ_lin` and `1+λ≤1+R`;
* if `λ≥R`, use `d(λ)≥λ/2` and `λ/2≥(1+λ)/4` because `R≥1`.

This gives a particularly Lean-friendly explicit producer.

If the public theorem assumes only the repository predicate `LinearlyStable`, rather than the sufficient continuous threshold, the same existential conclusion still follows for the explicit cosine spectrum: high modes satisfy the preceding coercive estimate, while the finitely many low nonzero modes have a positive finite minimum.  The closed-form `δ_lin` route is simpler when the displayed threshold is available.

A suitable Lean statement is:

```lean
theorem positiveEquilibrium_fullRateGap
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b)
    (hstable :
      LinearlyStable unitIntervalNeumannSpectrum p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2) :
    ∃ delta > 0, ∃ cStar > 0,
      ∀ k : ℕ,
        delta ≤ positiveLinearDecayRate p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2 k ∧
        cStar * (1 + unitIntervalNeumannSpectrum.eigenvalue k) ≤
          positiveLinearDecayRate p
            (positiveEquilibrium p ⟨ha, hb⟩).1
            (positiveEquilibrium p ⟨ha, hb⟩).2 k
```

## 3.3 What the mass constraint actually does

The repository condition is only

```lean
D.integral u₀ = D.volume * uStar.
```

On `[0,1]`, it gives

```text
ŵ₀(0)=0.
```

It does **not** give `ŵ₀(t)=0` for later times.  Integrating the PDE and using Neumann boundary conditions removes diffusion and chemotactic divergence, but leaves the logistic reaction:

```text
d/dt ∫u = ∫ u(a-bu^α).
```

For `w=u-u*`, Taylor expansion at `u*` yields

```text
ŵ₀' = -A ŵ₀ + N₀(w),
A=aα,
N₀(w)=O(‖w‖²).
```

Hence

```text
ŵ₀(t)
 = e^{-At} ŵ₀(0)
   + ∫₀ᵗ e^{-A(t-s)} N₀(w(s)) ds.
```

Even when `ŵ₀(0)=0`, the nonlinear forcing generally creates a nonzero mean immediately.  The correct proof therefore does not project onto the zero-mean subspace.  It keeps the `k=0` multiplier `e^{-At}`.

If `‖w(t)‖≤Ce^{-ρt}`, then `N₀(w(t))=O(e^{-2ρt})`, so the convolution decays at rate `min(A,2ρ)`; at equality one obtains `t e^{-At}`, which is bounded by `C_ε e^{-(A-ε)t}`.  There is no zero-mode spectral-gap problem.

For the positive equilibrium, the mass hypothesis is therefore redundant.  In contrast, in the minimal model `a=b=0`, `A=0`; there the zero mode is neutral and a conserved-mass condition is genuinely needed.  This is why `Statements.lean` describes `MassConstrainedLocallyExponentiallyStableFromSup` as the minimal-model package.

---

# 4. Sup-small data to a strong space after a delay

## 4.1 The scalar smoothing estimate

Let `S_L(t)` denote the actual full-rate semigroup.  From

```text
d_k ≥ c_* (1+λ_k)
```

and

```text
x^r e^{-xt} ≤ (r/(e t))^r       (x,t,r>0),
```

one gets

```text
(1+λ_k)^sigma e^{-d_k t₀}
  ≤ c_*^{-sigma} d_k^sigma e^{-d_k t₀}
  ≤ c_*^{-sigma} (sigma/(e t₀))^sigma.
```

Thus, for the fractional-domain norm `X^sigma`,

```text
‖S_L(t₀)w₀‖_{X^sigma}
  ≤ M_sigma c_*^{-sigma}
      (sigma/(e t₀))^sigma ‖w₀‖_{L^p}.
```

On the unit interval,

```text
‖w₀‖_{L^p} ≤ ‖w₀‖∞.
```

Define

```text
C_lin(t₀)
  = M_sigma c_*^{-sigma} (sigma/(e t₀))^sigma.
```

Then the linear contribution is at most `C_lin(t₀) ε` for sup perturbation `ε`.

The repository already has the right abstract positive-delay interface:

```lean
InitialContinuityConclusion
```

It produces `T0>0` and strong smallness at time `T0` from sup smallness.  That is exactly the role this argument should fill.  The present concrete package, however, defines `intervalDomainSectorialXpSigmaDistance` to be the sup norm itself, so it does not yet realize a genuine fractional domain.  A real closure must replace that gauge by the coefficient/fractional norm and prove `InitialContinuityConclusion` rather than make it definitional.

The coefficient infrastructure already available in
`PDE/FractionalPowerSpace.lean` is relevant:

```lean
FractionalPowerSpace
fractionalPowerWeight
reciprocalFractionalPowerWeight_summable_of_sigma_gt_quarter
derivativeReciprocalFractionalPowerWeight_summable_of_sigma_gt_three_quarters
```

For a direct Hilbert coefficient embedding into `C¹`, take `sigma>3/4`.  If the contraction is run with only `1/2<sigma<1`, add a second fixed smoothing delay before claiming the `C¹` estimate; absorb that delay into `t₀`.

## 4.2 The nonlinear finite-window estimate

The genuine solution satisfies

```text
w(t₀)
 = S_L(t₀)w₀
   + ∫₀ᵗ⁰ S_L(t₀-s) R(w(s)) ds,
```

where `R(0)=0` and `DR(0)=0`.  The required finite-window lemma should produce

```text
‖w(t₀)‖_{X^sigma}
  ≤ C_lin(t₀) ε + C_quad(t₀) ε².                 (S)
```

This is the honest nonlinear version of `InitialContinuityConclusion`.  The scalar multiplier estimate alone proves only the first term.

Given a desired contraction radius `η>0`, choose

```text
ε ≤ min
  { ε_local,
    η/(2 C_lin(t₀)),
    sqrt(η/(2 C_quad(t₀))) }.
```

Then `(S)` gives `‖w(t₀)‖_{X^sigma}≤η`.

A Lean-shaped statement is:

```lean
theorem intervalDomain_sup_to_actualXpSigma_at_delay
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b)
    {sigma pNorm t₀ : ℝ}
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hp : 1 < pNorm) (ht₀ : 0 < t₀)
    (hgap : PositiveEquilibriumFullRateGap p ha hb)
    (hrem : PositiveEquilibriumRemainderEstimate p sigma pNorm ha hb) :
    ∃ Clinear > 0, ∃ Cquad ≥ 0, ∃ epsLocal > 0,
      ∀ u₀ u v,
        PositiveInitialDatum intervalDomain u₀ →
        IsPaper2GlobalClassicalSolution intervalDomain p u v →
        InitialTrace intervalDomain u₀ u →
        intervalDomain.supNorm
            (fun x => u₀ x - (positiveEquilibrium p ⟨ha, hb⟩).1) < epsLocal →
        actualXpSigmaDistance sigma pNorm (u t₀)
            (fun _ => (positiveEquilibrium p ⟨ha, hb⟩).1) ≤
          Clinear * intervalDomain.supNorm
              (fun x => u₀ x - (positiveEquilibrium p ⟨ha, hb⟩).1) +
          Cquad * intervalDomain.supNorm
              (fun x => u₀ x - (positiveEquilibrium p ⟨ha, hb⟩).1) ^ 2
```

---

# 5. Weighted Duhamel contraction after `t₀`

Let `X=X_p^sigma`, let `Y=L^p`, and assume

```text
‖S_L(t)‖_{X→X} ≤ M₀ e^{-δ_lin t},
‖S_L(t)‖_{Y→X} ≤ M_sigma t^{-sigma} e^{-δ_lin t},
```

with `0<sigma<1`.  Suppose the v-eliminated nonlinear remainder obeys, on the ball `‖z‖_X,‖y‖_X≤R`,

```text
‖R(z)-R(y)‖_Y
  ≤ K_R (‖z‖_X+‖y‖_X) ‖z-y‖_X.                 (N)
```

Choose `0<ρ<δ_lin` and use the weighted norm

```text
‖w‖_ρ = sup_{t≥t₀} e^{ρ(t-t₀)} ‖w(t)‖_X.
```

The convolution constant is finite because `sigma<1`:

```text
J_ρ
 = M_sigma ∫₀∞ r^{-sigma} e^{-(δ_lin-ρ)r} dr
 = M_sigma Γ(1-sigma) (δ_lin-ρ)^{sigma-1}.
```

On a radius-`R` weighted ball, `(N)` gives contraction constant at most

```text
2 K_R J_ρ R.
```

Choose

```text
2 K_R J_ρ R < 1,
M₀ ‖w(t₀)‖_X ≤ R/2.
```

Then the Duhamel map is a contraction and

```text
‖w(t)‖_X
  ≤ 2 M₀ ‖w(t₀)‖_X e^{-ρ(t-t₀)}.
```

The elliptic variable is recovered from `w` through

```text
-v_xx + μv = νu^γ.
```

The linear resolver multiplier is `(λ_k+μ)^{-1}`, hence it gains two spatial derivatives.  The nonlinear Nemytskii remainder is quadratic near `u*`.  Therefore

```text
‖v(t)-v*‖_{C¹} ≤ C_v ‖w(t)‖_X
```

for a sufficiently strong `X`, or after one additional fixed positive smoothing delay.

---

# 6. The single genuine hard core

The spectral estimates, the zero-mode calculation, the scalar smoothing inequality, and the weighted-convolution algebra are bounded Lean tasks.

The **single genuine hard core** is the v-eliminated nonlinear remainder estimate in the actual strong/base spaces:

```lean
def PositiveEquilibriumRemainderEstimate
    (p : CM2Params) (sigma pNorm : ℝ)
    (ha : 0 < p.a) (hb : 0 < p.b) : Prop :=
  let eq := positiveEquilibrium p ⟨ha, hb⟩
  ∃ R > 0, ∃ K > 0,
    ∀ w z,
      actualXpSigmaNorm sigma pNorm w ≤ R →
      actualXpSigmaNorm sigma pNorm z ≤ R →
      actualLpNorm pNorm
          (positiveEquilibriumRemainder p eq w -
            positiveEquilibriumRemainder p eq z) ≤
        K * (actualXpSigmaNorm sigma pNorm w +
              actualXpSigmaNorm sigma pNorm z) *
          actualXpSigmaNorm sigma pNorm (w-z)
```

Its proof must handle, without hiding the operator:

* the Neumann resolvent `(-∂xx+μ)⁻¹` and its derivative;
* the Nemytskii maps `u↦u^γ` and `v↦(1+v)^{-β}` near a positive constant;
* products and the divergence in the chemotactic term;
* the logistic Taylor remainder;
* the boundary/trace realization in the selected fractional space.

Once this estimate exists, the positive-delay smoothing and the weighted fixed point are standard analytic-semigroup assembly.

---

# 7. Dependency-ordered Lean lemma DAG

## Lemma 1 — all-mode rate, including zero

```lean
theorem positiveEquilibrium_decayRate_pos_all_modes
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b)
    (hstable : LinearlyStable unitIntervalNeumannSpectrum p
      (positiveEquilibrium p ⟨ha,hb⟩).1
      (positiveEquilibrium p ⟨ha,hb⟩).2) :
    ∀ k, 0 < positiveLinearDecayRate p
      (positiveEquilibrium p ⟨ha,hb⟩).1
      (positiveEquilibrium p ⟨ha,hb⟩).2 k
```

Reuse `sigma_zero_neg_of_a_pos` at `k=0`; use `hstable` at `k≠0`.

## Lemma 2 — uniform gap plus order-two growth

```lean
positiveEquilibrium_fullRateGap
```

as stated above.  This is finite-mode arithmetic plus the high-mode bound.

## Lemma 3 — actual semigroup decay and smoothing

```lean
theorem actualLinearSemigroup_decay
...
theorem actualLinearSemigroup_smoothing
...
```

The second theorem is the coefficientwise application of
`x^sigma e^{-xt}≤(sigma/(et))^sigma` and `d_k≥c_*(1+λ_k)`.

## Lemma 4 — nonlinear remainder estimate **[hardest]**

```lean
intervalDomain_positiveEquilibrium_remainderEstimate
```

This is the `PositiveEquilibriumRemainderEstimate` producer described in §6.

## Lemma 5 — sup-to-strong entrance at a positive delay

```lean
intervalDomain_sup_to_actualXpSigma_at_delay
```

Use Lemmas 3–4 to prove the quantitative
`C_lin(t₀) ε + C_quad(t₀) ε²` estimate.  This is the real producer for the existing abstract `InitialContinuityConclusion`.

## Lemma 6 — weighted Duhamel decay after restart

```lean
theorem actualXpSigma_weightedDuhamel_decay
```

Choose `ρ<δ_lin`, prove the Gamma-kernel convolution bound, and apply Banach's fixed-point theorem on `[t₀,∞)`.

## Lemma 7 — public eventual orbit and stability adapters

```lean
theorem intervalDomain_eventualEquilibriumOrbitBoundWithoutMass
...

theorem intervalDomain_eventuallyLocallyExponentiallyStableFromSup_of_orbit
...

theorem intervalDomain_massConstrainedEventuallyLocallyExponentiallyStableFromSup_of_nonmass
...
```

The last theorem simply ignores the mass hypothesis.

---

# 8. Final assembly theorem and proof skeleton

The valid positive-equilibrium theorem is:

```lean
theorem linearlyStable_implies_eventuallyLocallyExponentiallyStableFromSup
    (p : CM2Params) (N : StabilityNorms intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hstrong : ActualIntervalStrongNormData N)
    (hrem : PositiveEquilibriumRemainderEstimate p
      hstrong.sigma hstrong.pNorm ha hb)
    (hexist : ∀ delta > 0,
      SmallDataGlobalExistence intervalDomain p
        (positiveEquilibrium p ⟨ha,hb⟩).1 delta)
    (hstable : LinearlyStable unitIntervalNeumannSpectrum p
      (positiveEquilibrium p ⟨ha,hb⟩).1
      (positiveEquilibrium p ⟨ha,hb⟩).2) :
    EventuallyLocallyExponentiallyStableFromSup intervalDomain p N
      (positiveEquilibrium p ⟨ha,hb⟩).1
      (positiveEquilibrium p ⟨ha,hb⟩).2
```

Proof order:

1. Derive the all-mode uniform gap and `d_k≥c_*(1+λ_k)` from `hstable`, using `sigma_zero_neg_of_a_pos` for `k=0`.
2. Choose `ρ=δ_lin/2` and a Duhamel radius `R` satisfying `2K_RJ_ρR<1`.
3. Choose a restart threshold `η≤R/(2M₀)`.
4. Use the sup-to-strong delayed estimate to choose `δ_sup` so that every sup-`δ_sup` datum satisfies `‖w(t₀)‖_X≤η`.
5. Obtain a global classical solution from `hexist`.
6. Restart its mild equation at `t₀`; apply the weighted Duhamel contraction.
7. Use the strong-to-C¹ embedding and the elliptic resolver estimate for `v`.
8. Package the bound with `A=C δ_sup`.

The mass-constrained eventual version is an immediate corollary:

```lean
theorem linearlyStable_implies_massConstrainedEventuallyLocallyExponentiallyStableFromSup
    ... :
    MassConstrainedEventuallyLocallyExponentiallyStableFromSup ... :=
  (linearlyStable_implies_eventuallyLocallyExponentiallyStableFromSup ...).massConstrained
```

There is **no valid theorem with the current exact conclusion**

```lean
LinearlyStable →
  MassConstrainedLocallyExponentiallyStableFromSup
```

for the genuine interval `C¹` distance and only sup-small initial data.  To retain that theorem name, one of the following statement changes is mandatory:

1. replace `ExponentialC1ConvergenceWith` by its eventual version;
2. strengthen the datum hypothesis to `C¹`- or actual `X_p^sigma`-smallness;
3. weaken the conclusion near zero to the true smoothing form

   ```text
   C1Distance(t) ≤ C t^{-theta} e^{-ρt} ‖u₀-u*‖∞,   t>0.
   ```

The first option matches the proposed positive-delay route and is the minimal correction.
