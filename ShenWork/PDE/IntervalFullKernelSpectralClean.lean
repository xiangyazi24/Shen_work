/-
  S1 — Hypothesis-free kernel↔spectral identities for the full Neumann
  propagator.

  `intervalNeumannFullKernel_eq_cosineKernel` (Poisson/theta content) and
  `intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional` (the
  `∫`↔`∑` interchange) are both proved upstream, but each still carries the
  pointwise kernel identity / summability side conditions as hypotheses.
  Every one of those side conditions is itself proved
  (`latticeGaussianSummable`, `latticeExpSummable`); this file assembles the
  zero-hypothesis versions:

  * `expCosSummable` — summability of the spectral cosine kernel terms;
  * `intervalNeumannFullKernel_eq_cosineKernel_clean` — pointwise kernel
    identity for all `t > 0`, `x y : ℝ`;
  * `intervalFullSemigroupOperator_eq_cosineHeatValue_clean` —
    `S(t)f(x) = ∑'ₙ e^{−tλₙ} f̂ₙ cos(nπx)` for continuous `f`, interior `x`;
  * `intervalFullSemigroupOperator_contDiff_two_clean` — spatial `C²` of the
    propagator for continuous `f` with bounded cosine coefficients.

  These are the S1 atoms of the χ₀ = 0 half-step restart construction
  (TASK_QUEUE 2026-06-06 roadmap).

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalFullKernelInterchange

open ShenWork.IntervalNeumannFullKernel

noncomputable section

namespace ShenWork.IntervalFullKernelSpectralClean

/-- Summability over `ℤ` of the spectral heat weights `e^{−t(mπ)²}`. -/
theorem expWeightSummable (t : ℝ) (ht : 0 < t) :
    Summable (fun m : ℤ => Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2)) := by
  have hc : (-(t * Real.pi ^ 2) : ℝ) < 0 :=
    neg_lt_zero.mpr (by positivity)
  have hbase : Summable (fun n : ℕ =>
      Real.exp (-(t * Real.pi ^ 2) * (n : ℝ) ^ 2)) := by
    refine Real.summable_exp_nat_mul_of_ge hc
      (f := fun n : ℕ => (n : ℝ) ^ 2) (fun i => ?_)
    have hnat : i ≤ i ^ 2 := by nlinarith [Nat.zero_le i]
    calc (i : ℝ) = ((i : ℕ) : ℝ) := rfl
      _ ≤ ((i ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (i : ℝ) ^ 2 := by push_cast; ring
  apply Summable.of_nat_of_neg
  · refine hbase.congr fun n => ?_
    congr 1
    push_cast
    ring
  · refine hbase.congr fun n => ?_
    congr 1
    push_cast
    ring

/-- Summability over `ℤ` of the spectral cosine kernel terms
`e^{−t(mπ)²} cos(mπθ)`. -/
theorem expCosSummable (t : ℝ) (ht : 0 < t) (θ : ℝ) :
    Summable (fun m : ℤ => Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
      Real.cos ((m : ℝ) * Real.pi * θ)) := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    (expWeightSummable t ht)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)

/-- **Pointwise kernel identity, hypothesis-free.**  For every `t > 0` and
`x y : ℝ`, the full periodised-image Neumann kernel equals the cosine
spectral kernel. -/
theorem intervalNeumannFullKernel_eq_cosineKernel_clean
    (t : ℝ) (ht : 0 < t) (x y : ℝ) :
    intervalNeumannFullKernel t x y =
      ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
        (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y)) :=
  intervalNeumannFullKernel_eq_cosineKernel t ht x y
    (latticeGaussianSummable ht (x - y)) (latticeGaussianSummable ht (x + y))
    ⟨expCosSummable t ht (x - y), expCosSummable t ht (x + y)⟩

/-- **Theorem 3, hypothesis-free.**  For `t > 0`, continuous `f`, and interior
`x ∈ (0,1)`, the full Neumann propagator equals the cosine spectral heat
value: `S(t)f(x) = ∑'ₙ e^{−tλₙ}·f̂ₙ·cos(nπx)`. -/
theorem intervalFullSemigroupOperator_eq_cosineHeatValue_clean
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    intervalFullSemigroupOperator t f x =
      unitIntervalCosineHeatValue t (cosineCoeffs f) x :=
  ShenWork.IntervalFullKernelInterchange.intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional
    t ht f hf x hx
    (fun y => intervalNeumannFullKernel_eq_cosineKernel_clean t ht x y)

/-- **Spatial `C²` of the propagator, hypothesis-free** (continuous `f` with
bounded cosine coefficients). -/
theorem intervalFullSemigroupOperator_contDiff_two_clean
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs f n| ≤ M) :
    ContDiff ℝ 2 (fun x => intervalFullSemigroupOperator t f x) :=
  ShenWork.IntervalFullKernelInterchange.intervalFullSemigroupOperator_contDiff_two_unconditional
    t ht f hf hM
    (fun x y => intervalNeumannFullKernel_eq_cosineKernel_clean t ht x y)

/-- **Closed-interval extension of Theorem 3.**  Both sides are continuous in
`x` (the propagator via the hypothesis-free `C²` corollary; the spectral heat
value via the smoothing engine), and they agree on the dense open `Ioo 0 1`,
hence on its closure `Icc 0 1`.  This is the form the restart-agreement
(`hagree : EqOn … (Set.Icc 0 1)`) obligations consume. -/
theorem intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs f n| ≤ M) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalFullSemigroupOperator t f x =
      unitIntervalCosineHeatValue t (cosineCoeffs f) x := by
  have hL : Continuous (fun x => intervalFullSemigroupOperator t f x) :=
    (intervalFullSemigroupOperator_contDiff_two_clean ht hf hM).continuous
  have hR : Continuous
      (fun x => unitIntervalCosineHeatValue t (cosineCoeffs f) x) :=
    (ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatValue_contDiff_two
      ht hM).continuous
  have heq : Set.EqOn (fun x => intervalFullSemigroupOperator t f x)
      (fun x => unitIntervalCosineHeatValue t (cosineCoeffs f) x)
      (Set.Ioo (0 : ℝ) 1) := fun y hy =>
    intervalFullSemigroupOperator_eq_cosineHeatValue_clean ht hf hy
  have hclos := heq.closure hL hR
  rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)] at hclos
  exact hclos hx

end ShenWork.IntervalFullKernelSpectralClean
