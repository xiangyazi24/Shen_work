# Claude-Codex Sync: Half-Line Integral Estimate

Current pushed HEAD: `67b98b8 Lift paper exponential dominance to upper barrier`.

## Target: Exponential Region Sign Estimate

The remaining first target is proving the dominance hypothesis `hdom` of
`paperWaveOperator_exp_nonpos_of_kappa_speed_of_dominance`.

### Paper's argument (equations 4.3-4.4, page 24-25)

For χ ≤ 0, the key computation is:

```
-κm|χ|V_x + |χ|V
= |χ| · (1 + mγκ²)/(1 - γ²κ²) · exp(-γκx)     (equation 4.4)
```

where V = Ψ(x; u^γ, 1, 1) and 0 ≤ u ≤ exp(-κx).

### Proposed Lean lemma chain

**Lemma A**: Psi derivative left/right integral bound for trap-set elements.
When u is in WaveTrapSet κ M and γκ < 1:

```lean
theorem Psi_deriv_left_right_bound_of_inWaveTrapSet
    (p : CMParams) {κ : ℝ} {u : ℝ → ℝ}
    (hκ : 0 < κ) (hγκ : p.γ * κ < 1)
    (hu : InWaveTrapSet κ M u) (x : ℝ) :
    -κ * p.m * deriv (frozenElliptic p u) x +
      frozenElliptic p u x ≤
      (1 + p.m * p.γ * κ ^ 2) / (1 - p.γ ^ 2 * κ ^ 2) *
        Real.exp (-(p.γ * κ) * x) := sorry
```

**Proof dependencies**:
1. `Psi_derivative_formula_general` (proved) gives V'(x) as half-line integrals
2. u^γ ≤ exp(-γκy) in the trap set
3. Half-line integral of exp((1-γκ)y) on (-∞, x] and exp(-(1+γκ)y) on [x, ∞)
4. Algebra: combine with V = Ψ(u^γ) to get the explicit coefficient

**Lemma B**: From Lemma A, derive the dominance condition:

```lean
theorem exp_region_dominance_of_chi_nonpos
    (p : CMParams) {κ M : ℝ} {u : ℝ → ℝ}
    (hχ : p.χ ≤ 0) (hα : p.α ≤ p.m + p.γ - 1)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hγκ : p.γ * κ < 1)
    (hM : 1 ≤ M)
    (hMbound : |p.χ| * (1 + p.m * p.γ * κ ^ 2) / (1 - p.γ ^ 2 * κ ^ 2) * M ≤
      (1 + |p.χ| * M))
    (hu : InWaveTrapSet κ M u) (x : ℝ)
    (hx : Real.exp (-κ * x) ≤ M) :
    <the hdom condition> := sorry
```

The `hMbound` condition is equation (4.2) from the paper:
`κ < 1/√(γ² + γ²|χ| + mγ|χ|)` implies `(γ² + γ²|χ| + mγ|χ|)κ²M ≤ 1`,
which gives `|χ|(1+mγκ²)/(1-γ²κ²) · M ≤ 1 + |χ|M`.

### Key difficulty

The half-line integral bound (Lemma A) requires:
1. Substituting the explicit Psi derivative formula into `-κmV' + V`
2. Using `u^γ(y) ≤ exp(-γκy)` from the trap set
3. Computing the resulting exponential integrals explicitly
4. Simplifying the coefficient algebra

Steps 1-3 use `Psi_derivative_formula_general` and `Psi_le_min_const_exp_of_nonneg_le`
(both proved). Step 4 is rpow algebra.

### Who does what

- **Claude**: Write Lemma A with sorry, then try to prove it using
  `Psi_derivative_formula_general`. This is the core mathematical content.
- **Codex**: Write Lemma B assuming Lemma A, connecting to the dominance
  hypothesis. This is algebra/bookkeeping.
