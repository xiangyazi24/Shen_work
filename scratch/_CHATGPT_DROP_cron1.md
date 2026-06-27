# Q1280 / cron1 — `ha0_bound` for `level0ResolverRestartA0`

Repo: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target file updated by this drop:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Executive answer

The relevant definition is in

```text
ShenWork/Paper2/IntervalResolverLevel0SpectralC2Coeff.lean
```

and is:

```lean
/-- Level-0 trajectory used in the B-form Picard construction: the heat semigroup
iterate `conjugatePicardIter p u₀ 0`. -/
abbrev heatLevel0 (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) :
    ℝ → intervalDomainPoint → ℝ :=
  conjugatePicardIter p u₀ 0

/-- Restart offset for a positive interior time `t₀`: the positive half-time
`t₀ / 2`. -/
def halfOffset (t₀ : ℝ) : ℝ :=
  t₀ / 2

/-- Initial coefficients at the restart offset. -/
def level0ResolverRestartA0
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (t₀ : ℝ) : ℕ → ℝ :=
  fun k => resolverTimeCoeff p (heatLevel0 p u₀) k (halfOffset t₀)
```

So the target `ha0_bound` is just a uniform-in-`k` bound on

```lean
resolverTimeCoeff p (heatLevel0 p u₀) k (t₀ / 2)
```

at a fixed positive time `offset = t₀/2`.

The clean proof is: use the constant-weight factorization

```lean
resolverTimeCoeff p u k t
  = intervalNeumannResolverWeight p k * srcTimeCoeff p u k t
```

and the already-landed resolver weight bound

```lean
intervalNeumannResolverWeight p k ≤ 1 / p.μ.
```

Then bound the source cosine coefficient by a uniform source-slice sup bound:

```lean
|srcTimeCoeff p u k t| ≤ 2 * B
```

where `B` bounds `|srcSlice p u t x|` on `[0,1]`.  This gives

```lean
|level0ResolverRestartA0 p u₀ t₀ k| ≤ (1 / p.μ) * (2 * B)
```

for every `k`.

Important: the exponential heat diagonalization

```lean
cosineCoeffs (S(t) f) k = exp(-t * λ_k) * cosineCoeffs f k
```

applies directly to the **linear heat profile** `S(t)u₀`, not directly to the nonlinear source coefficient of `ν * (S(t)u₀)^γ`.  For `level0ResolverRestartA0`, the coefficient is an elliptic resolver coefficient of the source `ν * u^γ`, so the robust `ha0_bound` proof should use a bounded continuous source slice.  The exponential decay route is upstream evidence that the positive-time heat profile is smooth/bounded; it is not the final one-line rewrite for the nonlinear source.

Also, the current theorem

```lean
theorem resolverHasSpectralAgreementC2Coeff_heatLevel0
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {T : ℝ} (_hT : 0 < T) :
    ResolverHasSpectralAgreementC2Coeff T
      (coupledChemicalConcentration p (heatLevel0 p u₀)) := by
```

has no hypothesis that `u₀` is continuous/bounded/nonnegative, nor any packaged positive-time source-slice bound.  So `ha0_bound` should either consume an upstream positive-time source-slice continuity/boundedness lemma, or the theorem signature should be strengthened to carry such a lemma.  The minimal local hypothesis needed for this block is only source-slice continuity at positive time; boundedness then follows by compactness.

## Drop-in helper lemmas

Put these near the top of `IntervalResolverLevel0SpectralC2Coeff.lean`, after the definitions of `heatLevel0`, `halfOffset`, and `level0ResolverRestartA0`.

```lean
import ShenWork.Paper2.IntervalResolverLevel0SpectralC2Coeff
import ShenWork.PDE.IntervalPhysicalSourceTimeC2Concrete
import ShenWork.Paper2.IntervalMildPicardRegularity

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalResolverJointC2PhysicalConcrete (resolverTimeCoeff)
open ShenWork.IntervalPhysicalResolverDataConcrete (srcTimeCoeff)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete
  (srcSlice srcTimeCoeff_eq_cosineCoeffs)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_abs_le_of_continuous_bounded)

noncomputable section

namespace ShenWork.Paper2.ResolverLevel0SpectralC2Coeff

/-- A continuous source slice on `[0,1]` has a finite nonnegative absolute-value
bound there.  This is the compactness step needed by `ha0_bound`. -/
theorem sourceSlice_bound_exists_of_continuousOn
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {t : ℝ}
    (hcont : ContinuousOn (srcSlice p u t) (Icc (0 : ℝ) 1)) :
    ∃ B : ℝ, 0 ≤ B ∧
      ContinuousOn (srcSlice p u t) (Icc (0 : ℝ) 1) ∧
      ∀ x ∈ Icc (0 : ℝ) 1, |srcSlice p u t x| ≤ B := by
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hcont
  refine ⟨max B 0, le_max_right B 0, hcont, ?_⟩
  intro x hx
  have hxB := hB x hx
  rw [Real.norm_eq_abs] at hxB
  exact hxB.trans (le_max_left B 0)

/-- Uniform resolver-coefficient bound from a bounded continuous source slice.

If `|srcSlice p u t x| ≤ B` on `[0,1]`, then every resolver coefficient at time `t`
is bounded by `(1 / p.μ) * (2 * B)`: the source coefficient is bounded by
`2B`, and the elliptic resolver multiplier is bounded by `1 / p.μ`. -/
theorem resolverTimeCoeff_uniform_bound_of_sourceSlice_bound
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {t B : ℝ}
    (hB : 0 ≤ B)
    (hcont : ContinuousOn (srcSlice p u t) (Icc (0 : ℝ) 1))
    (hbd : ∀ x ∈ Icc (0 : ℝ) 1, |srcSlice p u t x| ≤ B) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
      |resolverTimeCoeff p u n t| ≤ M := by
  refine ⟨(1 / p.μ) * (2 * B), by positivity, ?_⟩
  intro n
  have hsrc : |srcTimeCoeff p u n t| ≤ 2 * B := by
    rw [srcTimeCoeff_eq_cosineCoeffs]
    exact cosineCoeffs_abs_le_of_continuous_bounded hcont hB hbd n
  calc
    |resolverTimeCoeff p u n t|
        = |ShenWork.PDE.intervalNeumannResolverWeight p n * srcTimeCoeff p u n t| := by
            rw [ShenWork.IntervalPhysicalResolverDataConcrete.resolverTimeCoeff_eq_weight_smul]
    _ = ShenWork.PDE.intervalNeumannResolverWeight p n * |srcTimeCoeff p u n t| := by
            rw [abs_mul,
              abs_of_nonneg
                (ShenWork.IntervalPhysicalResolverDataConcrete.resolverWeight_nonneg p n)]
    _ ≤ (1 / p.μ) * (2 * B) := by
            exact mul_le_mul
              (ShenWork.IntervalResolverJointC2PhysicalConcrete.resolverWeight_le_inv_mu p n)
              hsrc
              (abs_nonneg _)
              (by positivity)

end ShenWork.Paper2.ResolverLevel0SpectralC2Coeff
```

If the file already imports these dependencies indirectly, do not duplicate the imports; just add the missing `open` lines or use qualified names.

## Minimal theorem-signature patch

Since the current theorem has no usable initial-data or source-slice hypothesis, add the minimal positive-time source continuity producer:

```lean
(hlevel0_src_cont : ∀ t : ℝ, 0 < t →
  ContinuousOn
    (ShenWork.IntervalPhysicalSourceTimeC2Concrete.srcSlice
      p (heatLevel0 p u₀) t)
    (Icc (0 : ℝ) 1))
```

So the theorem header becomes:

```lean
theorem resolverHasSpectralAgreementC2Coeff_heatLevel0
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {T : ℝ} (_hT : 0 < T)
    (hlevel0_src_cont : ∀ t : ℝ, 0 < t →
      ContinuousOn
        (ShenWork.IntervalPhysicalSourceTimeC2Concrete.srcSlice
          p (heatLevel0 p u₀) t)
        (Icc (0 : ℝ) 1)) :
    ResolverHasSpectralAgreementC2Coeff T
      (coupledChemicalConcentration p (heatLevel0 p u₀)) := by
```

This hypothesis is exactly what the positive-time heat-level0 regularity/floor infrastructure should supply.  If you already have a stronger fact such as `FlooredSourceTimeData.d0` or a positive-time `srcSlice_continuousOn` theorem, use that instead of adding a new carried hypothesis.

## Replacement for the `ha0_bound` sorry block

Replace lines 139–145 with:

```lean
    obtain ⟨M, hM, ha₀⟩ :
        ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, |a₀ n| ≤ M := by
      have hsrc_cont : ContinuousOn
          (srcSlice p u offset) (Icc (0 : ℝ) 1) := by
        simpa [u, offset] using hlevel0_src_cont offset hoff_pos
      obtain ⟨B, hB, hcontB, hbdB⟩ :=
        sourceSlice_bound_exists_of_continuousOn
          (p := p) (u := u) (t := offset) hsrc_cont
      obtain ⟨M, hM, hMbound⟩ :=
        resolverTimeCoeff_uniform_bound_of_sourceSlice_bound
          (p := p) (u := u) (t := offset) (B := B) hB hcontB hbdB
      refine ⟨M, hM, ?_⟩
      intro n
      simpa [a₀, level0ResolverRestartA0, u, offset] using hMbound n
```

This is enough for the existential package expected by `hmake`:

```lean
∃ (a₀ : ℕ → ℝ) (M : ℝ) (_ : 0 ≤ M) (_ : ∀ n, |a₀ n| ≤ M) ...
```

## If you already have a source sup bound instead of continuity

If an upstream producer gives the stronger data directly,

```lean
hlevel0_src_bound : ∀ t : ℝ, 0 < t →
  ∃ B : ℝ, 0 ≤ B ∧
    ContinuousOn (srcSlice p (heatLevel0 p u₀) t) (Icc (0 : ℝ) 1) ∧
    ∀ x ∈ Icc (0 : ℝ) 1,
      |srcSlice p (heatLevel0 p u₀) t x| ≤ B
```

then the replacement is even shorter:

```lean
    obtain ⟨M, hM, ha₀⟩ :
        ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, |a₀ n| ≤ M := by
      obtain ⟨B, hB, hsrc_cont, hsrc_bd⟩ := hlevel0_src_bound offset hoff_pos
      obtain ⟨M, hM, hMbound⟩ :=
        resolverTimeCoeff_uniform_bound_of_sourceSlice_bound
          (p := p) (u := u) (t := offset) (B := B)
          hB
          (by simpa [u, offset] using hsrc_cont)
          (by simpa [u, offset] using hsrc_bd)
      refine ⟨M, hM, ?_⟩
      intro n
      simpa [a₀, level0ResolverRestartA0, u, offset] using hMbound n
```

## Why this is the right local proof

The target `ha0_bound` only needs a crude `ℓ∞` bound on the restart initial coefficient sequence.  It does **not** need summability or the full `λ²/λ³` spectral ladder.

For any bounded continuous source slice `F`, the normalized Neumann coefficient satisfies

```lean
|cosineCoeffs F n| ≤ 2 * sup_{x∈[0,1]} |F x|.
```

The elliptic resolver coefficient adds the multiplier

```lean
w_n = 1 / (p.μ + λ_n) ≤ 1 / p.μ.
```

Therefore

```lean
|resolverCoeff_n| ≤ (1 / p.μ) * (2 * sourceSup).
```

That is precisely the bound `ha0_bound` wants.

No local `lake build` was run; this drop was produced through the GitHub connector only.
