# Wiener Gap Closure: C³ Neumann → DatumWienerLifting

## Goal

Prove: for C³ Neumann positive initial data u₀, the cosine coefficients
satisfy |c_n| ≤ C/n³ (cubic decay), which implies MemW 1 (weighted ℓ¹
summability). Package into `DatumWienerLifting`.

## Mathematical Route (ORACLE SYNTHESIS — verified by both Fable and ChatGPT)

For f ∈ C³([0,1]) with f'(0) = f'(1) = 0 (Neumann BC):

1. **IBP chain** for cosine coefficients c_n = 2∫₀¹ f(x) cos(nπx) dx:
   - IBP 1: boundary sin terms vanish (sin(0) = sin(nπ) = 0)
   - IBP 2: boundary terms vanish (Neumann: f'(0) = f'(1) = 0)
   - Result: c_n(f) = c_n(f'') / (nπ)²
   - IBP 3 on c_n(f''): sin boundary vanishes again
   - Final: |c_n(f)| ≤ 2‖f'''‖_{L¹} / (nπ)³

2. **Weighted summability**: |c_n| ≤ C/n³ gives
   ∑ (1+k) |c_k| ≤ |c_0| + ∑_{k≥1} (1+k) C/k³ ≤ |c_0| + 2C ∑ 1/k² < ∞

3. **MemW 1 bridge**: use existing `memW_ofCosineCoeffs` theorem

## Files to create

### 1. `ShenWork/Wiener/EWA/CosineDecayC3.lean`

Prove the cubic decay estimate. Key dependencies:
- `Mathlib.Analysis.Calculus.ContDiff.Basic` (for ContDiffOn)
- `Mathlib.MeasureTheory.Integral.IntervalIntegral` (for IBP)
- `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` (for sin/cos)
- `ShenWork.PDE.IntervalNeumannFullKernel` (for `cosineCoeffs`)
- `ShenWork.PDE.HeatKernelGradientEstimates` (for `unitIntervalNeumannCosineCoeff`)

Target theorem shape:
```lean
theorem cosineCoeffs_cubic_decay_of_C3_neumann
    {f : ℝ → ℝ}
    (hfC3 : ContDiffOn ℝ 3 f (Set.Icc (0 : ℝ) 1))
    (hN0 : deriv f 0 = 0)
    (hN1 : deriv f 1 = 0)
    (n : ℕ) (hn : 1 ≤ n) :
    |cosineCoeffs f n| ≤ (2 * ∫ x in (0:ℝ)..1, |iteratedDeriv 3 f x|) / ((n : ℝ) * Real.pi) ^ 3
```

### 2. `ShenWork/Wiener/EWA/WienerLiftingC3.lean`

Package into DatumWienerLifting. Key dependencies:
- `ShenWork.Wiener.EWA.CosineDecayC3`
- `ShenWork.Wiener.EWA.SourceChiNegUniformBridge` (for `DatumWienerLifting`)
- `ShenWork.Wiener.WeightedL1CosineAdapter` (for `memW_ofCosineCoeffs`)

Target theorem shape:
```lean
theorem datumWienerLifting_of_C3_neumann
    {u₀p : intervalDomainPoint → ℝ}
    (hppid : PaperPositiveInitialDatum intervalDomain u₀p)
    (hC3 : C3NeumannDatum u₀p)  -- to be defined
    : DatumWienerLifting u₀p
```

## Existing infrastructure to use

1. `memW_ofCosineCoeffs` in `WeightedL1CosineAdapter.lean:105`
   Input: `Summable (fun k : ℕ => (1 + (k : ℝ)) ^ r * |c k|)`
   Output: `MemW r (ofCosineCoeffs c)`

2. `cosineCoeffs` in `IntervalNeumannFullKernel.lean:83`
   Definition: `fun n => unitIntervalNeumannCosineCoeff (fun x => (f x : ℂ)) n`

3. `unitIntervalNeumannCosineCoeff` in `HeatKernelGradientEstimates.lean:73`
   The normalized coefficient: if n=0 then real part of raw coeff, else 2× raw coeff

4. `Summable.of_nonneg_of_le` and comparison with `∑ 1/k²` (standard Mathlib)

## Key constraints

- No `sorry`, `admit`, `native_decide`, or custom `axiom`
- Max line length 100 chars
- All files must compile with `/Users/huangx/.elan/bin/lake build`
- EXCEPTION: `hrecon` field of `DatumWienerLifting` (cosine series pointwise
  convergence) may use `sorry` ONLY if the rest is complete. Document the sorry
  clearly with a comment explaining what it states.

## Verification

```bash
cd /Users/huangx/repos/Shen_work
/Users/huangx/.elan/bin/lake build ShenWork.Wiener.EWA.CosineDecayC3
/Users/huangx/.elan/bin/lake build ShenWork.Wiener.EWA.WienerLiftingC3
```

## Note on the unit interval

The repo uses [0,1] for the interval domain, NOT [0,π]. Cosine modes are
`cos(nπx)` on [0,1]. Eigenvalues λ_n = (nπ)². Integration by parts on [0,1]:
∫₀¹ f(x) cos(nπx) dx, not ∫₀^π.
