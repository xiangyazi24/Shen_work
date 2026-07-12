# Oracle Synthesis R3 (2026-07-07) — Chi-negative Closure Route

## Converged route: ℓ¹ coefficient ladder (4 restart passes)

Both Fable (3 rounds) and ChatGPT (1 round + timeout) agree on the target:
close `CoupledFluxClassicalLocalExistenceResidual` directly. Mild solution
ALREADY EXISTS (conjugateMildExistenceCore_exists proved). The gap is
mild → classical (C^{2,1}) regularity.

### The four-pass ℓ¹ restart ladder (Fable R3, repo-grounded)

On restarted windows [t₀, T], each pass gains one power of k^{-1}:

| Pass | Input envelope | Mechanism | Output |
|------|---------------|-----------|--------|
| 1 | û bounded | Duhamel ∫₀^δ √λ e^{-λr} dr ≤ λ^{-1/2} | û ≲ k^{-1} |
| 2 | û ≲ k^{-1} | Product conv + Duhamel | û ≲ k^{-2}log k (Wiener, C^{0,θ}) |
| 3 | u ∈ C^{0,θ} | Hölder→decay → elliptic → Duhamel | û ≲ k^{-3+ε} (C^{1,θ}) |
| 4 | u ∈ C^{1,θ} | Same chain | û ≲ k^{-4+ε} → Σλ_k|û_k| < ∞ (C²) |

Then: per-mode ODE + M-test → time derivative. Spectral C² → spatial C².
Per-mode ODE replaces Schauder entirely.

### Three genuinely new atom families needed

1. **1D Neumann elliptic Green function** (~8-12 lemmas)
   - Explicit cosh kernel G_μ(x,y)
   - Kernel positivity (discharges hvnn without max principle)
   - L¹ bounds: ‖v‖_∞ ≤ (1/μ)‖f‖_∞, ‖∂ₓv‖_∞ ≤ C(μ)‖f‖_∞
   - Agreement with spectral resolverCoeff

2. **Hölder ⇒ coefficient-decay transfer** (~6-10 lemmas)
   - f ∈ C^{0,θ} ⇒ |cosineCoeffs f k| ≲ k^{-θ}
   - C^m + Neumann trace ⇒ k^{-m} by IBP (boundary terms vanish)

3. **Quantitative positivity floor** (~4-8 lemmas)
   - u ≥ c > 0 on [t₀,T]×[0,1] from restart bound
   - Needed for u^γ composition (γ ∈ [1,2) non-integer, C^{1,γ-1} at 0)

### Key corrections from oracle rounds

- hgradB: DEAD (endpoint obstruction, Task 314)
- No ∇u in the mild form (Fable R2) — B-kernel absorbs spatial derivative
- χ₀<0 CANNOT reduce to χ₀=0 (both oracles agree)
- conjugateMild_decomp_pos EXISTS at IntervalChiNegMildPackage:171 (Fable R3)
- DecompHyp blocker is Fubini, NOT parabolic representation theorem (audit-inherits-framing error)
- The ℓ² H^σ tower (SeamHyp σ < 3/2) is the WRONG norm for the classical consumer

### Codex dispatched (2026-07-07)

1. BForm field audit (high) — running
2. DecompHyp discharge (xhigh) — running
3. Green function (xhigh) — running

### Total estimated cost: ~55-85 lemmas
