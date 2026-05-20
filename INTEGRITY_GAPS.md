# Proof Integrity Gaps — 11-Point Audit (2026-05-19)

## Passing Points: 1, 2, 4 (partial), 9

- **Point 1 (0 sorry)**: PASS
- **Point 2 (0 custom axiom)**: PASS
- **Point 4 (0 trivially true)**: PARTIAL — main theorems pass, but
  `Preliminary.lean` has 4 placeholder theorems with `True` conclusion
  (semigroup_Lp_Lq_estimate, semigroup_grad_Lp_Lq_estimate,
   semigroup_div_Linfty_estimate, psi_weighted_gradient_estimate)
- **Point 9 (build passes)**: PASS

## Failing Points: 3, 5, 6, 7, 8

### Point 3: 假设结构体逃避

**Problem**: The main paper theorems are "proved" by projecting from assumption
structures that bundle the conclusions as fields.

| Structure | File | Fields that ARE the theorems being "proved" |
|-----------|------|---------------------------------------------|
| `Paper1AnalyticData` | Paper1/Statements.lean | 19 fields including Theorem_1_1, Theorem_1_2, Theorem_1_3, Proposition_1_1, Proposition_1_2, Lemma_4_1, Lemma_4_2, Lemma_5_1-5.3, etc. |
| `Paper2AnalyticData` | Paper2/Statements.lean | ~14 fields for Paper2 main theorems |
| `Paper3Constants` | Paper3/Statements.lean | Multiple fields for stability/threshold comparisons |
| `StabilityNorms` | Paper3/Statements.lean | Norm continuity, compactness fields |
| `CompactnessData` | Paper3/Statements.lean | Time-translate compactness fields |
| `SemigroupEstimateData` | Paper2/Statements.lean | Semigroup L^p estimates |
| `BoundedDomainData` | Paper2/Statements.lean | Abstract domain/boundary/integral |
| `SpectralData` | Paper3/Statements.lean | Abstract Neumann spectrum |

**Fix**: For each field, either:
(a) Prove it from lower-level lemmas and remove the field, or
(b) Keep it as an explicit axiom and mark the theorem as "conditional"

### Point 5: Prop 假设逃避

**Problem**: `_proved` theorems take assumption packages as parameters.
Example:
```
theorem Theorem_1_1_proved (A : Paper1AnalyticData) : Theorem_1_1 :=
  A.travelingWaveExistence
```
This is a projection, not a proof. The "proof" is `A` contains `Theorem_1_1`
as a field.

**Fix**: Prove each theorem from raw mathematical objects (CMParams, functions,
etc.) without assumption structure parameters, or honestly label as conditional.

### Point 6: End-to-end 定理不存在

**Problem**: No main theorem (Theorem 1.1-1.3, Propositions 1.1-1.2) takes
only raw math objects as input. They all require `Paper1AnalyticData` or
similar packages.

**Genuinely end-to-end theorems** (no assumption packages):
- `Psi_elliptic_ode`: v'' - λv + μf = 0
- `frozenElliptic_ode`: V'' - V + u^γ = 0
- `frozenElliptic_continuous`, `frozenElliptic_differentiable`
- `frozenElliptic_tendsto_atTop/atBot_of_U_tendsto`
- `chemotaxis_resolvent_bound`: paper eq (4.4)
- `paperWaveOperator_const_nonpos_neg/pos`: Lemma 4.1 constant region
- `paperWaveOperator_exp_nonpos_of_chi_nonpos`: Lemma 4.1 exp region (χ≤0)
- `Lemma_2_2_proved`, `Lemma_2_3_proved`, `Lemma_2_4_proved`
- `Lemma_2_5_proved` (Paper2)
- `Lemma_A_6_proved` (Paper3, partial — α≥1, γ≤1 branch)
- `FrozenStationaryWaveProfile.mk_auto_limits`
- `paperWaveOperator_eq_frozenWaveOperator_at_fixed_point`

**Fix**: Work toward proving assumption package fields from existing
infrastructure, converting projections into real proofs.

### Point 7: 接口最小化

**Problem**: `Paper1AnalyticData` bundles 19 fields. Many could potentially
be derived from a smaller set of fundamental assumptions.

**Fix**: Identify which fields follow from others and internalize the
derivations.

### Point 8: 反例检查

**Problem**: Not systematically done. The only known false statement
was `expDecay_mem_InWaveTrapSet` (attempted and caught — exp(-κx) > 1
for x < 0).

**Fix**: For each theorem that was difficult to prove, verify the
statement is not false before continuing.

## Priority Fix Order

1. **P0**: Delete Preliminary.lean trivially-true placeholders (replace with sorry or remove)
2. **P1**: Prove Paper1AnalyticData fields that already have infrastructure:
   - `upperBarrierSuperSolution` (Lemma_4_1) — constant region proved, exponential region partially proved
   - `lowerBarrierSubSolution` (Lemma_4_2) — constant subsolution proved for both χ branches
3. **P2**: Prove remaining Lemma_4_1/4_2 fields end-to-end
4. **P3**: Prove semigroup estimates (Lemma_2_1) from heat kernel
5. **P4**: Prove weighted gradient estimate (Lemma_2_5)
6. **P5**: Prove Section 5 estimates (Lemma_5_1-5.3) from wave ODE analysis
7. **P6**: Prove Schauder construction → Theorem_1_1
8. **P7**: Prove stability/uniqueness → Theorem_1_2, 1.3
9. **P8**: Instantiate bounded-domain API for Paper2/Paper3
