# Codex Spec: v2 Reduced Core (DuhamelSourceL1ContOn — no derivBound)

## Goal

Create v2 versions of synthesis, joint regularity, classical regularity,
and the reduced core wiring, using `DuhamelSourceL1ContOn` instead of
`DuhamelSourceTimeC1On`. This eliminates the `derivBound`/`hderivBound`
dependency, which is the hardest field to produce for the EWA Picard
fixed point.

## Key existing infrastructure to use

1. **`DuhamelSourceL1ContOn a T`** (IntervalPicardLimitRestartWeak.lean:127):
   ```
   structure DuhamelSourceL1ContOn (a : ℝ → ℕ → ℝ) (T : ℝ) where
     envelope : ℕ → ℝ
     henv_summable : Summable envelope
     henv_bound : ∀ s, 0 ≤ s → s ≤ T → ∀ n, |a s n| ≤ envelope n
     hcont : ∀ n, ContinuousOn (fun s : ℝ => a s n) (Set.Icc 0 T)
   ```

2. **`eigenvalue_mul_abs_duhamelSpectralCoeff_le_envelope`**
   (IntervalPicardLimitRestartWeak.lean:693):
   ```
   theorem eigenvalue_mul_abs_duhamelSpectralCoeff_le_envelope
       {a : ℝ → ℕ → ℝ} {T : ℝ} (src : DuhamelSourceL1ContOn a T)
       {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (k : ℕ) :
       unitIntervalCosineEigenvalue k * |duhamelSpectralCoeff a t k| ≤ src.envelope k
   ```

3. **`duhamelSpectralCoeff_hasDerivAt_of_on`**
   (PDE/IntervalDuhamelSpectralDerivOn.lean:19) — takes `DuhamelSourceTimeC1On`
   but only uses continuity. The v2 version replaces the continuity extraction.

4. **`parabolicGain_le_one`** (PDE/IntervalDuhamelRegularity.lean:104).

5. **`cosineMode_abs_le_one'`** — `|cosineMode n x| ≤ 1`.

6. **`hasDerivAt_tsum_of_isPreconnected`** — Mathlib's M-test for
   term-by-term differentiation.

7. **`continuousOn_tsum`** — Mathlib's Weierstrass M-test for uniform
   convergence on sets.

## File 1: `ShenWork/Wiener/EWA/SourceSynthesisL1.lean`

New file. All theorems against `DuhamelSourceL1ContOn` (no derivBound).

### Imports
```lean
import ShenWork.PDE.IntervalDuhamelSpectralDerivOn
import ShenWork.Paper2.IntervalPicardLimitRestartWeak
import ShenWork.Wiener.EWA.SourceReducedCoreWire
import ShenWork.Wiener.EWA.SourceJointRegularityOn
```

### 1a. HasDerivAt for Duhamel spectral coefficient (retype)

Mimic `duhamelSpectralCoeff_hasDerivAt_of_on` (IntervalDuhamelSpectralDerivOn.lean:19),
replacing `continuousOn_coeff_of_on src n` with `src.hcont n`:

```lean
theorem duhamelSpectralCoeff_hasDerivAt_of_L1ContOn {a : ℝ → ℕ → ℝ} {T : ℝ}
    (src : DuhamelSourceL1ContOn a T)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (n : ℕ) :
    HasDerivAt (fun r => duhamelSpectralCoeff a r n)
      (a t n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a t n) t
```

Proof: identical to `duhamelSpectralCoeff_hasDerivAt_of_on`, replacing line 25
(`continuousOn_coeff_of_on src n`) with `src.hcont n`.

### 1b. HasDerivAt for fullSourceCoeff (retype)

Mimic `fullSourceCoeff_hasDerivAt_on` (SourceReducedCoreWire.lean line ~138),
replacing `duhamelSpectralCoeff_hasDerivAt_of_on` calls with the L1ContOn version:

```lean
private theorem fullSourceCoeff_hasDerivAt_of_L1ContOn (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ)
    (hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (n : ℕ) :
    HasDerivAt (fun s => fullSourceCoeff p u u₀cos s n)
      (fullSourceCoeffDot p u u₀cos t n) t
```

### 1c. Direct semigroup bound on `|a(t,n) - λ_n * duhamelCoeff|`

```lean
private theorem duhamelDeriv_abs_le_two_env {a : ℝ → ℕ → ℝ} {T : ℝ}
    (src : DuhamelSourceL1ContOn a T)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (n : ℕ) :
    |a t n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a t n|
      ≤ 2 * src.envelope n
```

Proof: triangle inequality
```
|a - λ·d| ≤ |a| + λ·|d| ≤ env + env = 2·env
```
using `src.henv_bound` for `|a(t,n)| ≤ env(n)` and
`eigenvalue_mul_abs_duhamelSpectralCoeff_le_envelope` for `λ·|d| ≤ env(n)`.

### 1d. dotMajDirect definition

```lean
private noncomputable def dotMajDirect (p : CM2Params)
    (Mu0 c : ℝ)
    (chemEnv logEnv : ℕ → ℝ) (n : ℕ) : ℝ :=
  Mu0 * (unitIntervalCosineEigenvalue n *
      Real.exp (-c * unitIntervalCosineEigenvalue n))
    + 2 * |p.χ₀| * chemEnv n + 2 * logEnv n
```

### 1e. dotMajDirect summability

```lean
private theorem dotMajDirect_summable (p : CM2Params) (Mu0 : ℝ)
    {c : ℝ} (hc : 0 < c) (chemEnv logEnv : ℕ → ℝ)
    (hchemSum : Summable chemEnv) (hlogSum : Summable logEnv) :
    Summable (dotMajDirect p Mu0 c chemEnv logEnv)
```

Proof: sum of three summable sequences:
- Heat: `Mu0 * λ_n * e^{-c λ_n}` is summable by super-exponential decay
  (use `eigenvalueExp_summable` from SourceTimeRegularityMajorant or equivalent)
- Chem: `2 * |χ₀| * chemEnv(n)` summable from `hchemSum`
- Log: `2 * logEnv(n)` summable from `hlogSum`

### 1f. dotMajDirect bound

```lean
private theorem dotMajDirect_bound (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T)
    {c : ℝ} (hc : 0 < c) (hcT : c < T) (x : ℝ) (n : ℕ)
    (s : ℝ) (hs : s ∈ Set.Ioo c T) :
    ‖fullSourceCoeffDot p u u₀cos s n * cosineMode n x‖ ≤
      dotMajDirect p Mu0 c hchem.envelope hlog.envelope n
```

Proof sketch:
```
‖dot * cos‖ ≤ |dot| * 1
  = |-λ·e^{-sλ}·u₀(n) + (-χ₀)·(chemSrc-λ·duhamelChem) + (logSrc-λ·duhamelLog)| * 1
  ≤ Mu0·λ·e^{-sλ} + |χ₀|·2·chemEnv(n) + 2·logEnv(n)
  ≤ Mu0·λ·e^{-cλ} + 2|χ₀|·chemEnv(n) + 2·logEnv(n)   [since s ≥ c]
  = dotMajDirect(n)
```

Uses: `duhamelDeriv_abs_le_two_env` (1c), `cosineMode_abs_le_one'`, and
`e^{-sλ} ≤ e^{-cλ}` for s ≥ c.

### 1g. fsc_summable for L1ContOn

```lean
private theorem fsc_summable_of_L1ContOn (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : ℝ) :
    Summable (fun n => fullSourceCoeff p u u₀cos t n * cosineMode n x)
```

Uses summability of `Mu0 * e^{-tλ}` (heat) + `t * chemEnv(n)` (Duhamel value) +
`t * logEnv(n)` (Duhamel value). Mimic `fsc_summable_on` from SourceReducedCoreWire.lean
but use `abs_duhamelSpectralCoeff_le_on` adapted for DuhamelSourceL1ContOn.

NOTE: `abs_duhamelSpectralCoeff_le_weak` already exists
(IntervalPicardLimitRestartWeak.lean:150) against `DuhamelSourceL1ContOn`. Use that.

### 1h. Term-by-term differentiation (the v2 synthesis)

```lean
theorem synthesis_hasDerivAt_of_L1ContOn (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T) (x : ℝ) :
    HasDerivAt (fun s => ∑' n, fullSourceCoeff p u u₀cos s n * cosineMode n x)
      (∑' n, fullSourceCoeffDot p u u₀cos t₀ n * cosineMode n x) t₀
```

Proof: identical structure to `synthesis_hasDerivAt_on`:
```
exact hasDerivAt_tsum_of_isPreconnected
    (dotMajDirect_summable ...)  -- was dotMaj_summable
    isOpen_Ioo isPreconnected_Ioo
    (fun n s hs => (fullSourceCoeff_hasDerivAt_of_L1ContOn ... n).mul_const _)
    (fun n s hs => dotMajDirect_bound ... n s hs)
    ⟨..., ...⟩
    (fsc_summable_of_L1ContOn ...)
    ⟨..., ...⟩
```

### 1i. Duhamel derivative-series joint continuity

Mimic `duhamelDerivSeries_jointContinuousOn_of_on` (SourceJointRegularityOn.lean:396),
replacing the `env + derivBound * recipSquare` bound with `2 * env`:

```lean
theorem duhamelDerivSeries_jointContinuousOn_of_L1ContOn {a : ℝ → ℕ → ℝ} {T : ℝ}
    (src : DuhamelSourceL1ContOn a T) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          ∑' n, (a t n - unitIntervalCosineEigenvalue n *
            duhamelSpectralCoeff a t n) * cosineMode n x))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)
```

Proof: `continuousOn_tsum` with dominator `2 * src.envelope n` (summable from
`src.henv_summable.mul_left 2`). Per-mode continuity of the integrand
from `src.hcont n` (source coefficient continuous) and
`duhamelSpectralCoeff_continuous_of_L1ContOn` (Duhamel coefficient continuous,
analogous to `duhamelSpectralCoeff_continuous_of_on`).

NOTE: You may need to prove `duhamelSpectralCoeff_continuous_of_L1ContOn`:
```lean
theorem duhamelSpectralCoeff_continuous_of_L1ContOn {a : ℝ → ℕ → ℝ} {T : ℝ}
    (src : DuhamelSourceL1ContOn a T) (n : ℕ) :
    ContinuousOn (fun r => duhamelSpectralCoeff a r n) (Set.Ioo 0 T)
```
from HasDerivAt ⟹ ContinuousAt.

### 1j. Full three-leg joint continuity

```lean
theorem fullSourceCoeffDot_jointContinuousOn_of_L1ContOn (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T) :
    ContinuousOn
      (fun q : ℝ × ℝ => ∑' n, fullSourceCoeffDot p u u₀cos q.1 n * cosineMode n q.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)
```

Mimic `fullSourceCoeffDot_jointContinuousOn_on` (SourceJointRegularityOn.lean:577):
decompose into heat + chemDiv + logistic legs, use
`duhamelDerivSeries_jointContinuousOn_of_L1ContOn` for the two source legs.

Also the three-leg tsum split for L1ContOn:
```lean
theorem fullSourceCoeffDot_tsum_split_L1 (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T)
    {q : ℝ × ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) T ×ˢ Set.univ) :
    ∑' n, fullSourceCoeffDot p u u₀cos q.1 n * cosineMode n q.2 = ...
```

The tsum split decomposes `fullSourceCoeffDot` into three summable legs.
Mimic `fullSourceCoeffDot_tsum_split_on` from SourceJointRegularityOn.lean.
The summability of the Duhamel derivative legs uses `2 * env` bound instead
of `env + derivBound * recipSquare`.

### 1k. The two closed corollaries

```lean
theorem fullSourceCoeffDot_jointTimeDerivClosed_of_L1ContOn {T : ℝ} (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T) :
    ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        ∑' n, fullSourceCoeffDot p u u₀cos t n * cosineMode n x))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)

theorem fullSourceCoeffDot_jointTimeDerivInterior_of_L1ContOn {T : ℝ} (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T) :
    ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        ∑' n, fullSourceCoeffDot p u u₀cos t n * cosineMode n x))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Ioo (0 : ℝ) 1)
```

Both: `.mono (prod_mono (subset_refl _) ...)` from `fullSourceCoeffDot_jointContinuousOn_of_L1ContOn`.

### CRITICAL: also the value-field joint continuity

```lean
theorem fullSourceCoeff_jointSolutionClosed_of_L1ContOn {T : ℝ} (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T) :
    ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)
```

This uses the VALUE field majorant (env-based, not dot-based). The existing
`fullSourceCoeff_jointContinuousOn_on` uses `DuhamelSourceTimeC1On` only for
envelope fields. So this is a straightforward retype.

## Verification

After writing the file, run:
```bash
lake env lean ShenWork/Wiener/EWA/SourceSynthesisL1.lean
```

Must exit 0 with no `sorry`, no custom `axiom`, no `native_decide`, no `admit`.

## Hard rules

- NEW file only (`ShenWork/Wiener/EWA/SourceSynthesisL1.lean`)
- Do NOT modify any existing file
- No `sorry`, `axiom`, `native_decide`, `admit`
- Line length ≤ 100 chars
- Add `#print axioms` for the key theorems at the end

## Key imports you will likely need

```lean
import ShenWork.PDE.IntervalDuhamelSpectralDerivOn
import ShenWork.Paper2.IntervalPicardLimitRestartWeak
import ShenWork.Wiener.EWA.SourceReducedCoreWire
import ShenWork.Wiener.EWA.SourceJointRegularityOn
```

If you need `duhamelSpectralCoeff`, `fullSourceCoeff`, `fullSourceCoeffDot`,
`cosineMode`, `unitIntervalCosineEigenvalue`, `coupledChemDivSourceCoeffs`,
`coupledLogisticSourceCoeffs`, `reciprocalSquareTerm`, etc. — grep the tree to
find where they are defined and add the appropriate import.

## What NOT to do

- Do NOT try to also produce `DuhamelSourceL1ContOn` FROM the EWA fixed point — that's a separate task
- Do NOT try to also close the frontier — that's a separate task
- Do NOT modify `SourceReducedCoreWire.lean` or any other existing file
- Focus ONLY on producing the v2 synthesis/joint-regularity chain against `DuhamelSourceL1ContOn`
