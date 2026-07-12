ANSWER Q4441 ef4abec9

# Paper 3 Theorem 2.2 linear-stability dichotomy: executable Lean spec

## Verdict

The linear part is exactly the right “diagonal cosine-mode calc” target. For the bounded interval with Neumann boundary conditions, every nonzero cosine mode decouples. The elliptic `v` equation is diagonal in the same basis, so the linearized `u` equation reduces to a scalar growth rate per mode. Equivalently, one can package the same algebra as a `2 × 2` trace/determinant condition. No Krein–Rutman theorem is needed for this linear dichotomy.

Important: the repo already contains much of the threshold layer in `ShenWork/Paper3/CriticalSensitivityExactValue.lean`, including:

```lean
linearlyStable_of_chi_lt_mode_one_threshold
linearlyUnstable_of_mode_one_threshold_lt_chi
linearStability_dichotomy_at_mode_one_threshold
linearStability_dichotomy_unitInterval
positiveEquilibrium_linearStability_dichotomy_of_firstMode_dominant
minimalEquilibrium_linearStability_dichotomy_of_firstMode_dominant
```

So the “execution” should not rebuild the whole Paper 3 statement layer. It should add the explicit mode-matrix/scalar-growth algebra, then reuse the existing `sigmaCriticalChiPaperFormula` and `linearStability_dichotomy_*` theorems.

---

## 1. Constant equilibrium and per-mode linearization

For the positive logistic equilibrium, the repo already defines:

```lean
def positiveEquilibrium (p : CM2Params) (_hab : 0 < p.a ∧ 0 < p.b) : ℝ × ℝ :=
  ((p.a / p.b) ^ (1 / p.α),
    p.ν / p.μ * ((p.a / p.b) ^ (1 / p.α)) ^ p.γ)
```

So write:

```lean
uStar = (positiveEquilibrium p ⟨ha, hb⟩).1
vStar = (positiveEquilibrium p ⟨ha, hb⟩).2
```

For a Neumann mode `cos(kπx)` with eigenvalue

```lean
λ_k = S.eigenvalue k
-- unit interval: λ_k = (kπ)^2
```

linearize around the constant equilibrium `(uStar, vStar)`. Since `∇vStar = 0`, the only chemotaxis linear term comes from the perturbation of `∇v`:

```text
U_t = -(λ + a α) U + χ₀ · uStar^m · λ · V / (1+vStar)^β
0   = -(μ + λ) V + ν γ uStar^(γ-1) U
```

Eliminating `V` gives the scalar mode growth rate

```text
r(λ) = -(λ + a α)
       + χ₀ · ν · γ · uStar^(m+γ-1) · λ
           / ((1+vStar)^β · (μ+λ)).
```

The mode is linearly stable iff `r(λ) < 0`, i.e.

```text
χ₀ < (1+vStar)^β · (λ + a α) · (μ + λ)
        / (ν · γ · uStar^(m+γ-1) · λ).
```

This is exactly the repo formula:

```lean
sigmaCriticalChiPaperFormula p uStar vStar λ
```

---

## 2. Trace/determinant packaging

The equivalent `2 × 2` mode matrix is:

```text
A_k = [ -(λ + aα)                         χ₀ λ uStar^m / (1+vStar)^β ]
      [  νγ uStar^(γ-1)                  -(μ + λ)                    ]
```

Define the trace and determinant scalars instead of immediately using `Matrix`; this is easier to prove in Lean and can be bridged to a matrix determinant later if needed.

Paste-ready Lean skeleton:

```lean
import ShenWork.Paper3.CriticalSensitivityExactValue
import ShenWork.PDE.CosineSpectrum

namespace ShenWork.Paper3

noncomputable section

/-- Per-mode trace of the linearized two-variable mode system. -/
def paper3LinearModeTrace (p : CM2Params) (λ : ℝ) : ℝ :=
  -((λ + p.a * p.α) + (p.μ + λ))

/-- Per-mode determinant of the linearized two-variable mode system. -/
def paper3LinearModeDet (p : CM2Params) (uStar vStar λ : ℝ) : ℝ :=
  (λ + p.a * p.α) * (p.μ + λ)
    - p.χ₀ * p.ν * p.γ * uStar ^ (p.m + p.γ - 1) * λ /
        (1 + vStar) ^ p.β

/-- Scalar Schur-complement growth rate for the parabolic-elliptic mode. -/
def paper3LinearModeGrowth (p : CM2Params) (uStar vStar λ : ℝ) : ℝ :=
  -(λ + p.a * p.α)
    + p.χ₀ * p.ν * p.γ * uStar ^ (p.m + p.γ - 1) * λ /
        ((1 + vStar) ^ p.β * (p.μ + λ))

/-- Nonzero-mode stability in trace/determinant form. -/
def paper3LinearModeStable (p : CM2Params) (uStar vStar λ : ℝ) : Prop :=
  paper3LinearModeTrace p λ < 0 ∧
    0 < paper3LinearModeDet p uStar vStar λ

/-- Nonzero-mode stability in scalar-growth form. -/
def paper3LinearScalarModeStable (p : CM2Params) (uStar vStar λ : ℝ) : Prop :=
  paper3LinearModeGrowth p uStar vStar λ < 0
```

Core algebra lemmas:

```lean
theorem paper3LinearModeTrace_neg
    (p : CM2Params) {λ : ℝ} (hλ : 0 < λ) :
    paper3LinearModeTrace p λ < 0 := by
  unfold paper3LinearModeTrace
  have hμ : 0 < p.μ := p.hμ
  have haα_nonneg : 0 ≤ p.a * p.α :=
    mul_nonneg p.ha p.hα.le
  nlinarith

/-- Determinant positivity is exactly the per-mode critical-threshold condition. -/
theorem paper3LinearModeDet_pos_iff_chi_lt_sigma
    (p : CM2Params) {uStar vStar λ : ℝ}
    (hu : 0 < uStar) (hv : 0 ≤ vStar) (hλ : 0 < λ) :
    0 < paper3LinearModeDet p uStar vStar λ ↔
      p.χ₀ < sigmaCriticalChiPaperFormula p uStar vStar λ := by
  unfold paper3LinearModeDet sigmaCriticalChiPaperFormula
  have hden_pos :
      0 < p.ν * p.γ * uStar ^ (p.m + p.γ - 1) * λ := by
    positivity
  have hbase_pos : 0 < 1 + vStar := by linarith
  have hpow_pos : 0 < (1 + vStar) ^ p.β :=
    Real.rpow_pos_of_pos hbase_pos p.β
  -- Clear the positive denominators.  The final line is pure ordered-ring algebra.
  constructor
  · intro hdet
    -- Suggested proof path:
    --   1. move the chemotaxis term to the right;
    --   2. divide by the positive `ν γ uStar^(m+γ-1) λ`;
    --   3. multiply by `(1+vStar)^β`.
    field_simp [ne_of_gt hden_pos, ne_of_gt hpow_pos] at hdet ⊢
    nlinarith [hdet, hden_pos, hpow_pos]
  · intro hχ
    field_simp [ne_of_gt hden_pos, ne_of_gt hpow_pos] at hχ ⊢
    nlinarith [hχ, hden_pos, hpow_pos]

/-- Scalar Schur growth and determinant form agree because `μ+λ > 0`. -/
theorem paper3LinearScalarModeStable_iff_trace_det
    (p : CM2Params) {uStar vStar λ : ℝ}
    (hu : 0 < uStar) (hv : 0 ≤ vStar) (hλ : 0 < λ) :
    paper3LinearScalarModeStable p uStar vStar λ ↔
      paper3LinearModeStable p uStar vStar λ := by
  unfold paper3LinearScalarModeStable paper3LinearModeStable paper3LinearModeGrowth
  constructor
  · intro hgrowth
    refine ⟨paper3LinearModeTrace_neg p hλ, ?_⟩
    -- `paper3LinearModeGrowth = - det / (μ+λ)`.
    have hmul_pos : 0 < p.μ + λ := by positivity
    unfold paper3LinearModeDet
    field_simp [ne_of_gt hmul_pos] at hgrowth ⊢
    nlinarith [hgrowth, hmul_pos]
  · intro hstable
    rcases hstable with ⟨_, hdet⟩
    have hmul_pos : 0 < p.μ + λ := by positivity
    unfold paper3LinearModeDet at hdet
    field_simp [ne_of_gt hmul_pos] at hdet ⊢
    nlinarith [hdet, hmul_pos]

/-- Combined one-mode theorem: a nonzero mode is stable iff `χ₀` is below the mode threshold. -/
theorem paper3LinearModeStable_iff_chi_lt_sigma
    (p : CM2Params) {uStar vStar λ : ℝ}
    (hu : 0 < uStar) (hv : 0 ≤ vStar) (hλ : 0 < λ) :
    paper3LinearModeStable p uStar vStar λ ↔
      p.χ₀ < sigmaCriticalChiPaperFormula p uStar vStar λ := by
  constructor
  · intro h
    exact (paper3LinearModeDet_pos_iff_chi_lt_sigma p hu hv hλ).mp h.2
  · intro hχ
    exact ⟨paper3LinearModeTrace_neg p hλ,
      (paper3LinearModeDet_pos_iff_chi_lt_sigma p hu hv hλ).mpr hχ⟩
```

These lemmas are the concrete algebraic engine behind the existing threshold API.

---

## 3. Dichotomy theorem statement

For a general spectrum, the clean statement is: if the first nonzero mode is the critical/minimizing mode, then all nonzero modes are stable iff the first-mode threshold is satisfied.

Do **not** state an unconditional `∀ k, stable_mode k ↔ χ₀ < paperCriticalSensitivity` without care: since `paperCriticalSensitivity` is an infimum, `∀ k, χ₀ < threshold k` does not by itself imply `χ₀ < inf threshold` unless the infimum is attained or there is a uniform gap. The repo’s existing first-mode-dominant hypothesis is exactly the safe way to make the iff true.

Paste-ready target:

```lean
/-- All nonzero modes are stable iff `χ₀` is below the first-mode threshold,
provided the first nonzero mode realizes the critical threshold. -/
theorem paper3AllNonzeroModesStable_iff_chi_lt_mode_one
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    {uStar vStar : ℝ} (hu : 0 < uStar) (hv : 0 ≤ vStar)
    (hmode1 : S.eigenvalue 1 = S.firstNonzero)
    (hregime : p.a * p.α * p.μ ≤ S.firstNonzero ^ 2) :
    (∀ k : ℕ, k ≠ 0 → paper3LinearModeStable p uStar vStar (S.eigenvalue k)) ↔
      p.χ₀ < sigmaCriticalChiPaperFormula p uStar vStar (S.eigenvalue 1) := by
  constructor
  · intro hall
    have hstable1 := hall 1 one_ne_zero
    exact (paper3LinearModeStable_iff_chi_lt_sigma p hu hv
      (H.eigenvalue_pos_of_ne_zero 1 one_ne_zero)).mp hstable1
  · intro hχ k hk
    have hkpos : 0 < S.eigenvalue k := H.eigenvalue_pos_of_ne_zero k hk
    have h1pos : 0 < S.eigenvalue 1 := H.eigenvalue_pos_of_ne_zero 1 one_ne_zero
    have h1le : S.eigenvalue 1 ≤ S.eigenvalue k := by
      rw [hmode1]
      exact H.firstNonzero_le_eigenvalue k hk
    have hprod : p.a * p.α * p.μ ≤ S.eigenvalue 1 * S.eigenvalue k := by
      have hfn_le : S.firstNonzero ≤ S.eigenvalue k :=
        H.firstNonzero_le_eigenvalue k hk
      have hsq : S.firstNonzero ^ 2 ≤ S.eigenvalue 1 * S.eigenvalue k := by
        rw [hmode1, sq]
        exact mul_le_mul_of_nonneg_left hfn_le H.firstNonzero_pos.le
      linarith
    have hthreshold_le :
        sigmaCriticalChiPaperFormula p uStar vStar (S.eigenvalue 1) ≤
          sigmaCriticalChiPaperFormula p uStar vStar (S.eigenvalue k) :=
      sigmaCriticalChiPaperFormula_le_of_firstMode_dominant
        p hu hv h1pos hkpos h1le hprod
    exact (paper3LinearModeStable_iff_chi_lt_sigma p hu hv hkpos).mpr
      (lt_of_lt_of_le hχ hthreshold_le)
```

For the unit interval, specialize with `S = unitIntervalNeumannSpectrum`. The repo already has:

```lean
linearStability_dichotomy_unitInterval
```

A positive-equilibrium wrapper is essentially one line:

```lean
/-- Unit-interval positive-equilibrium linear stability dichotomy at the explicit first mode. -/
theorem positiveEquilibrium_linearStabilityDichotomy_unitInterval_exec
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b)
    (hregime : p.a * p.α * p.μ ≤ (Real.pi ^ 2) ^ 2) :
    (p.χ₀ < sigmaCriticalChiPaperFormula p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2
        (unitIntervalNeumannSpectrum.eigenvalue 1) →
        LinearlyStable unitIntervalNeumannSpectrum p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2) ∧
      (sigmaCriticalChiPaperFormula p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2
        (unitIntervalNeumannSpectrum.eigenvalue 1) < p.χ₀ →
        LinearlyUnstable unitIntervalNeumannSpectrum p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2) := by
  exact linearStability_dichotomy_unitInterval p
    (positiveEquilibrium_fst_pos p ⟨ha, hb⟩)
    (positiveEquilibrium_snd_pos p ⟨ha, hb⟩).le
    hregime
```

Or, if you want to expose the generic first-mode theorem instead of the unit-interval wrapper:

```lean
theorem positiveEquilibrium_linearStabilityDichotomy_firstMode_exec
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hmode1 : S.eigenvalue 1 = S.firstNonzero)
    (hregime : p.a * p.α * p.μ ≤ S.firstNonzero ^ 2) :
    (p.χ₀ < sigmaCriticalChiPaperFormula p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 (S.eigenvalue 1) →
        LinearlyStable S p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2) ∧
      (sigmaCriticalChiPaperFormula p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 (S.eigenvalue 1) < p.χ₀ →
        LinearlyUnstable S p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2) := by
  exact positiveEquilibrium_linearStability_dichotomy_of_firstMode_dominant
    S p H ha hb hmode1 hregime
```

---

## 4. Reused infrastructure

Use these existing components.

### From Paper 3 statements/formula layer

```lean
positiveEquilibrium
minimalEquilibrium
positiveEquilibrium_fst_pos
positiveEquilibrium_snd_pos
positiveEquilibrium_fst_rpow_alpha
positiveEquilibrium_logistic_zero
positiveEquilibrium_elliptic_relation
sigmaCriticalChiPaperFormula
sigmaCriticalChi_eq_paperFormula
paperCriticalSensitivity
LinearlyStable
LinearlyUnstable
BelowAllLinearCriticalThresholds_of_chi_lt_paperCriticalSensitivity
LinearlyUnstable_of_sigmaCriticalChi_lt_chi
```

### From the exact critical sensitivity file

```lean
sigmaCriticalChiPaperFormula_le_of_firstMode_dominant
paperCriticalSensitivity_eq_mode_one_of_firstMode_dominant
paperCriticalSensitivity_unitInterval_eq_mode_one
linearlyStable_of_chi_lt_mode_one_threshold
linearlyUnstable_of_mode_one_threshold_lt_chi
linearStability_dichotomy_at_mode_one_threshold
linearStability_dichotomy_unitInterval
positiveEquilibrium_linearStability_dichotomy_of_firstMode_dominant
minimalEquilibrium_linearStability_dichotomy_of_firstMode_dominant
```

### From cosine/spectrum infrastructure

```lean
ShenWork.CosineSpectrum.cosineMode
ShenWork.CosineSpectrum.cosineEigenvalue
ShenWork.IntervalNeumannFullKernel.cosineCoeffs
ShenWork.PDE.SpectralDecay.intervalNeumannSpectrum
ShenWork.PDE.SpectralDecay.intervalNeumannSpectrum_hasNeumannSpectrum
unitIntervalNeumannSpectrum
unitIntervalNeumannSpectrum_hasNeumannSpectrum
IntervalCosineInversion.intervalCosine_hasSum_pointwise
```

Only the first group is required for the algebraic dichotomy. The actual cosine reconstruction/inversion infrastructure is needed when connecting the linearized PDE operator to diagonal mode coefficients, not for the scalar threshold theorem itself.

---

## Proof skeleton summary

1. Establish the per-mode linearization:
   ```text
   V_k = νγ u*^(γ-1)/(μ+λ_k) · U_k.
   ```

2. Substitute into the `u` equation:
   ```text
   U_k' = r_k U_k
   r_k = -(λ_k+aα) + χ₀νγu*^(m+γ-1)λ_k/((1+v*)^β(μ+λ_k)).
   ```

3. Prove:
   ```lean
   r_k < 0 ↔ p.χ₀ < sigmaCriticalChiPaperFormula p uStar vStar λ_k
   ```
   by clearing positive denominators.

4. Prove trace/det version if desired:
   ```lean
   trace < 0 ∧ det > 0 ↔ p.χ₀ < sigmaCriticalChiPaperFormula ... λ_k
   ```

5. Use `HasNeumannSpectrum` to get `λ₁ ≤ λ_k` for `k ≠ 0`.

6. Use `sigmaCriticalChiPaperFormula_le_of_firstMode_dominant` under
   ```lean
   hregime : p.a * p.α * p.μ ≤ S.firstNonzero ^ 2
   ```
   to show the first-mode threshold is the minimum.

7. Conclude all nonzero modes are stable iff `χ₀` is below the first-mode threshold; instability above the first-mode threshold is immediate from mode `1`.

This is the exact low-PDE, high-reuse route. The nonlinear local exponential part of Theorem 2.2 remains a sectorial/Duhamel problem; this file should only claim the linear dichotomy.