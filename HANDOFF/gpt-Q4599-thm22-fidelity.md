ANSWER Q4599 6a16ca10

# Paper-fidelity verdict

The printed Theorem 2.2 is stronger than the argument actually proves. Its literal nonlinear clause is an all-time C^1 exponential estimate, for every t\ge 0, from an initial perturbation that is assumed small only in L^\infty and is merely continuous. Thus, among the four choices in the question, the printed nonlinear claim is (a)—not (b), (c), or (d)—although the theorem also contains the exact linear stability/instability dichotomy.

There are two important qualifications.

1. The paper does not put the factor \|u_0-u^*\| on the right side of (2.12). It states a basin estimate

1. Even without that factor, the printed t=0 assertion is not valid under the paper's initial-data hypothesis: u_0 is only required to lie in C(\bar\Omega), so its C^1 norm need not exist; even if one restricts to C^1 data, an L^\infty ball has no uniform C^1 bound.

The proof itself first waits until a positive time T_0, enters a fractional-power-space neighborhood, and then applies Henry's nonlinear stability theorem. It therefore genuinely proves eventual C^1 exponential decay for the paper's L^\infty-small data, and it proves instantaneous exponential decay for data initially small in the strong fractional-power norm.

Accordingly, a consistency-preserving formalization should separate three statements:

- the exact spectral dichotomy from Theorem 2.2;

- the correct strong-space, all-time nonlinear stability theorem;

- the correct L^\infty-small, positive-time/eventual basin-entry theorem.

It should not silently identify their conjunction with the literal printed (2.12) at t=0.

# 1. What Theorem 2.2 exactly states

The source checked is Chen–Ruau–Shen, Chemotaxis models with signal-dependent sensitivity and a logistic-type source, II: Persistence and stabilization, arXiv:2604.02599v1, April 3, 2026. Theorem 2.2 is titled “Linear stability and instability.”

For a positive constant equilibrium (u^*,v^*), let \{\lambda_n\}_{n\ge0} be the Neumann eigenvalues of -\Delta, with \lambda_0=0, and define

For a,b>0, u^*=(a/b)^{1/\alpha}. Theorem 2.2(1) says:

- if \chi_0<\chi^*_{a,b,\beta}(u^*), then (u^*,v^*) is linearly stable;

- if \chi_0>\chi^*_{a,b,\beta}(u^*), then it is unstable;

- moreover, in the stable regime there exist C,\delta,\lambda>0 such that every u_0 satisfying (1.8) and

Theorem 2.2(2) gives the corresponding minimal-model statement when a=b=0. In that case u^*>0 is free, v^*=(\nu/\mu)(u^*)^\gamma, and the nonlinear clause includes the mass constraint

Thus the exact classification is:

- not (d): the theorem is not spectral stability only; it explicitly appends a nonlinear exponential-decay conclusion;

- not (c): it does not merely assert convergence with no rate;

- not (b): the printed formula does not start at an eventual time;

- (a), literally: it states the C^1 estimate for all t\ge0.

The initial-data condition (1.8), however, is only

Proposition 1.1 supplies convergence to u_0 in L^\infty as t\downarrow0 and classical spatial regularity only for positive time. There is no C^1, Sobolev, or fractional-power smallness hypothesis in the statement of Theorem 2.2.

## An additional parameter-fidelity issue

The condition in the question,

is a clean sufficient condition, but it is generally not the full threshold in Theorem 2.2. With

the mode eigenvalues are

The exact stable condition is

The continuous minimization gives

Therefore \kappa<(\sqrt\mu+\sqrt{a\alpha})^2 proves stability in a possibly smaller parameter region. On [0,1], where \lambda_n=n^2\pi^2, the inequality can be strict unless the continuous minimizer \sqrt{a\alpha\mu} happens to coincide with a Neumann eigenvalue. To clear the actual stable half of Theorem 2.2, the formalization should use the discrete infimum—or equivalently prove \sigma_n<0 for every mode under \chi_0<\chi^*—rather than stopping at the continuous sufficient bound.

# 2. What the proof actually establishes

Section 5.1 has two distinct stages.

## Stage A: genuine strong-space nonlinear stability

The paper chooses

so that the fractional-power space X_p^\sigma embeds continuously into C^1(\bar\Omega). It rewrites the perturbation \widetilde u=u-u^* as

where

with Neumann domain W^{2,p}_N(\Omega), and where F(0)=0, DF(0)=0, and

Since the spectrum of A_* is \{\sigma_n\} and all \sigma_n<0 in the stable regime, Henry's theorem gives a radius \varepsilon>0 such that

for every 0<\omega<\min\{a\alpha,\inf_{n\ge1}(-\sigma_n)\}, after adjusting notation and constants. The paper's displayed (5.5) absorbs the small initial radius into the constant and writes Ce^{-\lambda t}, but Appendix Lemma A.1 has the standard multiplicative initial-norm factor.

This part is sound and gives an all-time C^1 estimate by the embedding X_p^\sigma\hookrightarrow C^1.

## Stage B: smoothing from the paper's weak initial topology

The paper then invokes Lemma 3.3. For the chosen \varepsilon, that lemma supplies T_0>0 and \delta>0 such that

It restarts the solution at T_0 and correctly obtains

Equivalently,

and the same kind of estimate follows for v-v^* through the elliptic resolvent.

The problematic sentence is the next one: after setting s=t+T_0, the paper says that “enlarging C if necessary” yields the same estimate for all s\ge0. The preceding estimate only covers s\ge T_0. Enlarging a uniform constant cannot fill the interval [0,T_0) when the initial family is controlled only in L^\infty and the output is measured in C^1.

## Decisive zero-time obstruction

On [0,1], take Neumann-compatible positive perturbations

with 0<\varepsilon<\min\{\delta,u^*/2\}. Then

for every n, but

Hence no constant C uniform over the L^\infty ball can make the printed C^1 estimate hold at t=0. The paper permits even merely continuous u_0, for which the C^1 quantity at t=0 may not be defined at all.

The version in the question with an extra factor \|u_0-u^*\|_\infty has the same obstruction, even more sharply.

Analytic-semigroup smoothing naturally produces a positive-time singular factor—for example, schematically,

for an appropriate \eta>0. Such a factor cannot be replaced by a uniform constant as t\downarrow0 unless the initial data are controlled in a stronger topology.

# 3. Is the obstruction only an artifact of using the sup norm?

Yes. The obstruction is not a failure of nonlinear spectral stability; it is a mismatch between the topology used for initial smallness and the topology placed on the solution at time zero.

For data small in X_p^\sigma, the standard all-time conclusion is true. Since X_p^\sigma\hookrightarrow C^1, the initial C^1 norm is controlled, positivity follows from sufficiently small perturbation of u^*>0, the nonlinear remainder is locally Lipschitz from X_p^\sigma to L^p, and the spectral gap closes the fixed-point/variation-of-constants estimate.

Therefore:

- strong-norm-small data: all-time exponential decay in X_p^\sigma, hence in C^1, is true and standard;

- only L^\infty-small continuous data: the unweighted C^1 estimate can start only after positive smoothing time, unless the statement is modified by a singular time weight.

But this does not mean that one may replace the paper's hypothesis by X_p^\sigma-smallness and claim to have proved Theorem 2.2 exactly. That replacement repairs the theorem but strengthens its hypothesis. It is a correct nearby theorem, not the literal printed one.

# 4. Bottom line for clearing the headline

## What matches the paper's stated hypothesis?

The paper assumes

with the additional mean constraint in the minimal model. Thus the hypothesis is sup-norm smallness, not X_p^\sigma, C^1, or high Sobolev smallness.

Consequently, the theorem that faithfully matches the argument under the paper's actual hypothesis is

For a fixed chosen basin radius, Lemma 3.3 actually allows T_0 and \delta to be chosen uniformly over the initial-data neighborhood; allowing T_0 to depend on the datum is a weaker statement.

## What matches a correct all-time stability theorem?

The correct all-time theorem is

and therefore

## What should be called “Theorem 2.2” in a faithful formalization?

There is no way to prove the literal printed nonlinear clause in a consistent system without changing either its time range, its output norm near t=0, or its initial-data hypothesis. The honest options are:

1. Formalize the literal statement and prove a counterexample/obstruction lemma, recording that its nonlinear t=0 clause is ill-posed or false under (1.8).

1. Use an explicit corrected theorem: exact spectral dichotomy plus eventual C^1 exponential decay for L^\infty-small continuous data.

1. Also formalize the standard strong version: exact spectral dichotomy plus all-time X_p^\sigma exponential decay for X_p^\sigma-small data.

1. If retaining L^\infty data and all positive times, use a smoothing-weighted estimate such as

Thus, between the two targets posed in the question:

- \forall t\ge0 with strong-norm-small data is mathematically correct, but it does not match the paper's printed smallness hypothesis;

- \forall t\ge T_0 with sup-small data matches the paper's proof and actual initial-data hypothesis, but is an explicit correction of the printed time range.

Do not label the first one as a verbatim proof of Theorem 2.2, and do not label the second one as exactly equation (2.12) without noting the correction.

# 5. Exact fractional-power space and sectorial theorem

On \Omega=(0,1), the paper uses

with

and defines

Choose

Then

The shift +\mu I does not alter the relevant regularity scale; it makes the Neumann operator invertible and aligns with the elliptic resolvent \mu I-\Delta_N.

A standard Henry-style theorem in the sign convention of the paper is:

```plain text
Let A be sectorial on a Banach space X and X^σ = D(A^σ), 0 < σ < 1.
Consider

    x_t + A x = f(x)

near an equilibrium x* ∈ D(A). Suppose

    f(x* + z) = f(x*) + B z + g(z),
    B : X^σ → X is bounded,
    ||g(z)||_X = o(||z||_{X^σ}),

and f is locally Lipschitz on X^σ. If

    spectrum(A - B) ⊂ {λ : Re λ > ρ}

for some ρ > 0, then there exist ε,M > 0 such that

    ||x0 - x*||_{X^σ} ≤ ε

implies global forward existence and

    ||x(t) - x*||_{X^σ}
      ≤ M exp(-ρ(t-t0)) ||x0 - x*||_{X^σ}

for every t ≥ t0.
```

For the paper's perturbation convention \widetilde u_t=A_*\widetilde u+F(\widetilde u), apply this to -A_*. If

then any 0<\omega<-s(A_*) below the available spectral margin is an admissible decay rate after the usual small-radius choice.

The elliptic component is recovered from

so local Lipschitzness of the Nemytskii map and resolvent regularity transfer the same exponential rate to \widetilde v in C^1.

# 6. Recommended dependency split for Lean

A paper-faithful implementation should expose separate theorems rather than one overloaded headline:

```javascript
-- Exact paper threshold, including the discrete Neumann spectrum.
theorem theorem22_linear_stable_of_lt_discrete_threshold : ...

theorem theorem22_linear_unstable_of_gt_discrete_threshold : ...

-- Correct Henry theorem at time zero.
theorem local_exp_stable_Xsigma_small :
  ‖u₀ - uStar‖_{Xσ} < ε →
  ∀ t ≥ 0, ‖u t - uStar‖_{Xσ} ≤ M * exp (-ω*t) * ‖u₀-uStar‖_{Xσ} := ...

-- Positive-time smoothing/basin entry from the paper's actual hypothesis.
theorem sup_small_enters_Xsigma_basin :
  ‖u₀-uStar‖∞ < δ →
  ‖u T₀ - uStar‖_{Xσ} < ε := ...

-- What Section 5.1 actually proves for (1.8) data.
theorem sup_small_eventual_C1_exp :
  ‖u₀-uStar‖∞ < δ →
  ∀ t ≥ T₀,
    ‖u t-uStar‖C1 + ‖v t-vStar‖C1 ≤ C * exp (-ω*(t-T₀)) := ...

-- Integrity guard against silently restoring the false t=0 clause.
theorem no_uniform_C1_at_zero_from_sup_ball : ...
```

The single most important fidelity guard is the last one: the oscillatory Neumann data u^*+\varepsilon\cos(n\pi x) prevent any future assembly from treating sup-smallness as if it controlled the strong norm at t=0.

# Sources checked

- Chen–Ruau–Shen, arXiv:2604.02599v1, Theorem 2.2 and equations (2.10)–(2.12), pp. 10–11.

- Initial-data condition (1.8) and Proposition 1.1, p. 4.

- Lemma 3.3, positive-time continuity/basin entry, p. 17.

- Proof of Theorem 2.2(1), especially equations (5.3)–(5.6), pp. 27–29.

- Appendix A.1, Lemma A.1 and the definition X_p^\sigma=D(A_p^\sigma), pp. 43–44.

# Final answer in one sentence

The paper literally claims all-time C^1 exponential decay from merely L^\infty-small continuous data, but its proof only establishes eventual C^1 decay after a uniform positive smoothing time; the all-time theorem is valid when the initial perturbation is small in X_p^\sigma, with 2\sigma-1/p>1 on [0,1], and these two corrected statements must be kept distinct to preserve paper fidelity.