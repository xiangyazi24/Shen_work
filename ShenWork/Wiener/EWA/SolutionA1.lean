import ShenWork.Paper2.IntervalPicardLimitBddAdapter
import ShenWork.Paper2.IntervalPicardLimitRestartWeak

/-!
# Solution `A¹` regularity on a positive-time window — discharged from committed bricks

This file closes the `A¹` regularity gap of `ChemDivFinal.lean`.  The assembled
theorem `chemDiv_eigenvalueSummableOn_of_solution` is conditional on the `embedEWA`
inputs

* `hBv    : ∀ s k, |cosineCoeffs (intervalDomainLift (u s)) k| ≤ Bv k`,
* `hBvsum  : Summable (fun k => (1 + (k:ℝ)) * Bv k)`            (the `A¹` input).

The naive worst-case decay of the *source* is only `1/k²` (`A⁰`, NOT `A¹`):
`Σ (1+k)/k² ~ Σ 1/k` diverges (see
`IntervalMildSourceDecay.sourceCoeff_bound_from_parabolic`, which sets `C₀ = 0`
and keeps only the `B_R/(kπ)²` reaction term).

But that is **not** the regularity the committed development exposes for the
*solution* `u` on a *positive-time* window `[a', b'] ⊂ (0, τ]`.  The committed
σ-uniform eigenvalue-weighted bound

```
eigenvalue_mul_abs_limitCoeff_le_uniform_bdd :
  (λ_ k) * |limitCoeff p u₀ u σ k| ≤ windowEigEnv M₀ src.M a' (src.env (a'/2)) k
```

(`IntervalPicardLimitBddAdapter`, valid for every `σ ∈ [a', τ]`) keeps the full
positive-time heat-smoothing factor: `windowEigEnv` carries the
`λ_k · e^{-a' λ_k}` head — super-polynomial decay in `k` for fixed `a' > 0` — and
is **summable** (`windowEigEnv_summable`).  Since `λ_k = (kπ)²`, dividing by `λ_k`
gives an envelope `Bv k := windowEigEnv k / λ_k` (`k ≥ 1`) with

```
(1 + k) · Bv k = ((1+k) / λ_k) · windowEigEnv k ≤ windowEigEnv k     (since 1+k ≤ λ_k),
```

so `Σ_k (1+k) · Bv k ≤ Σ_k windowEigEnv k < ∞` — the `A¹` summability.

So `A¹` is **derivable** — it is the heat-semigroup positive-time smoothing already
formalized, not a new parabolic brick.  This file packages it: from the committed
`windowEigEnv` envelope we build the `A¹` envelope `Bv` (with `(1+k)·Bv k` summable)
that dominates `|cosineCoeffs (lift (u σ)) k|` uniformly on `[a', b']`, i.e. exactly
the `hBv`/`hBvsum` inputs of `embedEWA`.

NO `sorry`, `axiom`, `native_decide`, or `admit`.
-/

open scoped BigOperators
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalPicardLimitRestart (limitCoeff)
open ShenWork.IntervalPicardLimitRestartBdd
open ShenWork.IntervalPicardLimitBddAdapter

noncomputable section

namespace ShenWork.SolutionA1

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-- **`(1 + k) ≤ (kπ)² = λ_k`** for `k ≥ 1`.  The `A¹` weight is dominated by the
eigenvalue weight, so the committed `(kπ)²`-weighted ℓ¹ bound implies the `A¹`
(`(1+k)`-weighted) bound. -/
theorem one_add_le_eigenvalue {k : ℕ} (hk : 1 ≤ k) :
    (1 : ℝ) + (k : ℝ) ≤ (λ_ k) := by
  unfold unitIntervalCosineEigenvalue
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hπ : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hπ2 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_pos]
  -- (kπ)² = k²π² ≥ k²·9 ≥ k·9 ≥ k + k ≥ 1 + k
  calc (1 : ℝ) + (k : ℝ) ≤ (k : ℝ) + (k : ℝ) := by linarith
    _ = 2 * (k : ℝ) := by ring
    _ ≤ (k : ℝ) * (k : ℝ) * 9 := by nlinarith
    _ ≤ (k : ℝ) * (k : ℝ) * Real.pi ^ 2 := by
        nlinarith [mul_nonneg hkpos.le hkpos.le, hπ2]
    _ = ((k : ℝ) * Real.pi) ^ 2 := by ring

/-- `0 < λ_k` for `k ≥ 1`. -/
theorem eigenvalue_pos {k : ℕ} (hk : 1 ≤ k) : 0 < (λ_ k) := by
  unfold unitIntervalCosineEigenvalue
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  positivity

/-- The committed `A¹` envelope.

`Bv k := windowEigEnv M₀ M a' env k / λ_k` for `k ≥ 1`, with a fixed head value
`head` at `k = 0` (since `λ_0 = 0` carries no information about `|coeff 0|`, the
zero mode is dominated by the supplied head bound, not by the eigenvalue weight). -/
def a1Envelope (M₀ M a' : ℝ) (env : ℕ → ℝ) (head : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then head else windowEigEnv M₀ M a' env k / (λ_ k)

/-- `a1Envelope` is nonnegative when its ingredients are. -/
theorem a1Envelope_nonneg
    {M₀ M a' : ℝ} (hM₀ : 0 ≤ M₀) (hM : 0 ≤ M) (ha' : 0 < a')
    {env : ℕ → ℝ} (henv_nn : ∀ k, 0 ≤ env k) {head : ℝ} (hhead : 0 ≤ head)
    (k : ℕ) : 0 ≤ a1Envelope M₀ M a' env head k := by
  unfold a1Envelope
  split
  · exact hhead
  · rename_i hk0
    have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have hlam : 0 < (λ_ k) := eigenvalue_pos hk
    have hW : 0 ≤ windowEigEnv M₀ M a' env k := by
      unfold windowEigEnv
      have h1 : 0 ≤ (λ_ k) := by unfold unitIntervalCosineEigenvalue; positivity
      have hp1 : 0 ≤ M₀ * ((λ_ k) * Real.exp (-a' * (λ_ k))) :=
        mul_nonneg hM₀ (mul_nonneg h1 (Real.exp_pos _).le)
      have hp2 : 0 ≤ a' / 2 * M * ((λ_ k) * Real.exp (-(a' / 2) * (λ_ k))) :=
        mul_nonneg (mul_nonneg (by linarith) hM) (mul_nonneg h1 (Real.exp_pos _).le)
      have hp3 : 0 ≤ env k := henv_nn k
      linarith
    exact div_nonneg hW hlam.le

/-- **`A¹` summability of the envelope.**  `Σ_k (1+k) · a1Envelope … k < ∞`,
by comparison with the committed summable `windowEigEnv`:
`(1+k)·(windowEigEnv k / λ_k) ≤ windowEigEnv k` for `k ≥ 1` (since `1+k ≤ λ_k`),
plus the single head term at `k = 0`. -/
theorem a1Envelope_weighted_summable
    {M₀ M a' : ℝ} (hM₀ : 0 ≤ M₀) (hM : 0 ≤ M) (ha' : 0 < a')
    {env : ℕ → ℝ} (henv : Summable env) (henv_nn : ∀ k, 0 ≤ env k) {head : ℝ}
    (hhead : 0 ≤ head) :
    Summable (fun k : ℕ => (1 + (k : ℝ)) * a1Envelope M₀ M a' env head k) := by
  have hWsum : Summable (windowEigEnv M₀ M a' env) := windowEigEnv_summable ha' henv
  have hWnn : ∀ k, 0 ≤ windowEigEnv M₀ M a' env k := by
    intro k
    unfold windowEigEnv
    have h1 : 0 ≤ (λ_ k) := by unfold unitIntervalCosineEigenvalue; positivity
    have hp1 : 0 ≤ M₀ * ((λ_ k) * Real.exp (-a' * (λ_ k))) :=
      mul_nonneg hM₀ (mul_nonneg h1 (Real.exp_pos _).le)
    have hp2 : 0 ≤ a' / 2 * M * ((λ_ k) * Real.exp (-(a' / 2) * (λ_ k))) :=
      mul_nonneg (mul_nonneg (by linarith) hM) (mul_nonneg h1 (Real.exp_pos _).le)
    linarith [henv_nn k]
  -- Summable on the tail `k ≥ 1`; the single `k = 0` term is irrelevant.
  rw [← summable_nat_add_iff 1]
  -- Comparison: for `m`, the `(m+1)`-th term is `≤ windowEigEnv (m+1)`.
  refine Summable.of_nonneg_of_le
    (fun m => mul_nonneg (by positivity)
      (a1Envelope_nonneg hM₀ hM ha' henv_nn hhead (m + 1)))
    (fun m => ?_)
    ((summable_nat_add_iff 1).2 hWsum)
  -- `(1 + (m+1)) · (windowEigEnv (m+1) / λ_{m+1}) ≤ windowEigEnv (m+1)`.
  have hk : 1 ≤ m + 1 := Nat.le_add_left 1 m
  have hlam : 0 < (λ_ (m + 1)) := eigenvalue_pos hk
  have hwle : (1 : ℝ) + ((m + 1 : ℕ) : ℝ) ≤ (λ_ (m + 1)) := one_add_le_eigenvalue hk
  have hWk : 0 ≤ windowEigEnv M₀ M a' env (m + 1) := hWnn (m + 1)
  change (1 + ((m + 1 : ℕ) : ℝ)) * a1Envelope M₀ M a' env head (m + 1)
      ≤ windowEigEnv M₀ M a' env (m + 1)
  unfold a1Envelope
  rw [if_neg (Nat.succ_ne_zero m), mul_div_assoc', div_le_iff₀ hlam]
  calc (1 + ((m + 1 : ℕ) : ℝ)) * windowEigEnv M₀ M a' env (m + 1)
      ≤ (λ_ (m + 1)) * windowEigEnv M₀ M a' env (m + 1) :=
        mul_le_mul_of_nonneg_right hwle hWk
    _ = windowEigEnv M₀ M a' env (m + 1) * (λ_ (m + 1)) := by ring

/-- **`A¹` regularity of the solution on a positive-time window — discharged.**

This is the `hBv`/`hBvsum` pair of `embedEWA`, produced from the committed bricks.

Inputs (all committed / supplied as the same standard data the rest of the chain
already carries):
* `src`     — the bounded Duhamel source package `DuhamelSourceBddOn` on `[0, τ]`
  (its envelope `src.env (a'/2)` is summable, `src.henv_summable`);
* `hu₀_bound` — the uniform bound `|cosineCoeffs (lift u₀) k| ≤ M₀` on the initial data;
* `hbridge` — the committed half-step cosine identity
  `cosineCoeffs (lift (u σ)) k = limitCoeff p u₀ u σ k` on the window
  (`IntervalPicardLimitRestartWeak.cosineCoeffs_halfstep_eq_limitCoeff_weak`);
* `hzero`   — the zero-mode bound `|cosineCoeffs (lift (u σ)) 0| ≤ head` (the `k = 0`
  term the eigenvalue weight `λ_0 = 0` cannot see; available from the `L^∞` bound on
  `u`, since `cosineCoeffs · 0 = ∫₀¹ u`).

Output: the explicit `A¹` envelope `Bv := a1Envelope M₀ src.M a' (src.env (a'/2)) head`
with
* `∀ σ ∈ [a', b'], ∀ k, |cosineCoeffs (lift (u σ)) k| ≤ Bv k`   (the `hBv` shape), and
* `Summable (fun k => (1 + k) * Bv k)`                          (the `A¹` `hBvsum`).

The eigenvalue weight `λ_k = (kπ)²` exceeds the `A¹` weight `1 + k`, so the committed
`(kπ)²`-weighted positive-time bound dominates `A¹`. -/
theorem solution_A1_on_pos
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    {M₀ : ℝ} (hM₀ : 0 ≤ M₀)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {τ : ℝ}
    (src : DuhamelSourceBddOn
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k) τ)
    {a' b' : ℝ} (ha' : 0 < a') (hab : a' ≤ b') (hb'τ : b' ≤ τ)
    {head : ℝ} (hhead : 0 ≤ head)
    (hbridge : ∀ σ, σ ∈ Set.Icc a' b' → ∀ k,
      cosineCoeffs (intervalDomainLift (u σ)) k = limitCoeff p u₀ u σ k)
    (hzero : ∀ σ, σ ∈ Set.Icc a' b' →
      |cosineCoeffs (intervalDomainLift (u σ)) 0| ≤ head) :
    (∀ σ ∈ Set.Icc a' b', ∀ k,
        |cosineCoeffs (intervalDomainLift (u σ)) k|
          ≤ a1Envelope M₀ src.M a' (src.env (a' / 2)) head k)
      ∧ (∀ k, 0 ≤ a1Envelope M₀ src.M a' (src.env (a' / 2)) head k)
      ∧ Summable (fun k : ℕ =>
          (1 + (k : ℝ)) * a1Envelope M₀ src.M a' (src.env (a' / 2)) head k) := by
  set Bv : ℕ → ℝ := a1Envelope M₀ src.M a' (src.env (a' / 2)) head with hBv_def
  have henv_nn : ∀ k, 0 ≤ src.env (a' / 2) k := fun k =>
    le_trans (abs_nonneg _)
      (src.henv_bound (a' / 2) (by linarith) (a' / 2) le_rfl (by linarith) k)
  have henv_sum : Summable (src.env (a' / 2)) :=
    src.henv_summable (a' / 2) (by linarith) (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · -- domination: |coeff σ k| ≤ Bv k on the window.
    intro σ hσ k
    obtain ⟨hσa, hσb⟩ := hσ
    have hσpos : 0 < σ := lt_of_lt_of_le ha' hσa
    have hστ : σ ≤ τ := le_trans hσb hb'τ
    rw [hBv_def]
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simpa [a1Envelope] using hzero σ ⟨hσa, hσb⟩
    · have hk1 : 1 ≤ k := hkpos
      have hlam : 0 < (λ_ k) := eigenvalue_pos hk1
      -- committed eigenvalue-weighted bound on limitCoeff.
      have hcommit : (λ_ k) * |limitCoeff p u₀ u σ k|
          ≤ windowEigEnv M₀ src.M a' (src.env (a' / 2)) k :=
        eigenvalue_mul_abs_limitCoeff_le_uniform_bdd p u₀ u hM₀ hu₀_bound src
          ha' hσa hστ k
      have hbr : cosineCoeffs (intervalDomainLift (u σ)) k = limitCoeff p u₀ u σ k :=
        hbridge σ ⟨hσa, hσb⟩ k
      -- |coeff| = |limitCoeff| ≤ windowEigEnv / λ = Bv k.
      have : (λ_ k) * |cosineCoeffs (intervalDomainLift (u σ)) k|
          ≤ windowEigEnv M₀ src.M a' (src.env (a' / 2)) k := by rw [hbr]; exact hcommit
      have hBvk : a1Envelope M₀ src.M a' (src.env (a' / 2)) head k
          = windowEigEnv M₀ src.M a' (src.env (a' / 2)) k / (λ_ k) := by
        simp only [a1Envelope, if_neg (Nat.pos_iff_ne_zero.mp hkpos)]
      rw [hBvk, le_div_iff₀ hlam, mul_comm]
      exact this
  · intro k
    rw [hBv_def]
    exact a1Envelope_nonneg hM₀ src.hM_nonneg ha' henv_nn hhead k
  · rw [hBv_def]
    exact a1Envelope_weighted_summable hM₀ src.hM_nonneg ha' henv_sum henv_nn hhead

end ShenWork.SolutionA1

#print axioms ShenWork.SolutionA1.solution_A1_on_pos
