import ShenWork.Paper1.WaveFrozenEllipticValueDep
import ShenWork.Paper1.Lemma53Full

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Whole-line Cauchy local-existence atoms

This file starts the genuine general-sensitivity Cauchy construction.  The
older `PDE/MildSolution.lean` evolves only the logistic source and therefore
cannot produce the Paper 1 system.  Here the elliptic field is the canonical
`frozenElliptic` resolver and the nonlinear flux is the full divergence-form
chemotaxis flux used by the Duhamel map.
-/

/-- The spatial flux whose divergence appears in the population equation. -/
def wholeLineChemotaxisFlux
    (p : CMParams) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  (u x) ^ p.m * deriv (frozenElliptic p u) x

/-- Uniform continuous dependence of the resolver gradient on a nonnegative
bounded profile.  This is the global-sup specialization of the already proved
Green-kernel difference estimate. -/
theorem frozenElliptic_deriv_diff_uniform_abs_le
    (p : CMParams) {M D : ℝ} {u w : ℝ → ℝ}
    (hM : 0 ≤ M)
    (hu : IsCUnifBdd u) (hw : IsCUnifBdd w)
    (huM : ∀ x, u x ∈ Set.Icc (0 : ℝ) M)
    (hwM : ∀ x, w x ∈ Set.Icc (0 : ℝ) M)
    (hD : ∀ x, |u x - w x| ≤ D) (x : ℝ) :
    |deriv (frozenElliptic p u) x -
        deriv (frozenElliptic p w) x| ≤
      rpowLip p.γ M * D := by
  have hD0 : 0 ≤ D := (abs_nonneg (u 0 - w 0)).trans (hD 0)
  have hL0 : 0 ≤ rpowLip p.γ M := rpowLip_nonneg p.hγ hM
  have hpower : ∀ y,
      |(u y) ^ p.γ - (w y) ^ p.γ| ≤ rpowLip p.γ M * D := by
    intro y
    calc
      |(u y) ^ p.γ - (w y) ^ p.γ|
          ≤ rpowLip p.γ M * |u y - w y| := by
            simpa only [rpowLip] using
              abs_rpow_sub_rpow_le_of_mem_Icc p.hγ hM (huM y) (hwM y)
      _ ≤ rpowLip p.γ M * D :=
        mul_le_mul_of_nonneg_left (hD y) hL0
  have hkernel :
      (∫ y, Real.exp (-|x - y|) *
          |(u y) ^ p.γ - (w y) ^ p.γ|) ≤
        ∫ y, Real.exp (-|x - y|) * (rpowLip p.γ M * D) := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun y =>
        mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)
    · exact (exp_neg_abs_sub_integrable x).mul_const _
    · exact Filter.Eventually.of_forall fun y =>
        mul_le_mul_of_nonneg_left (hpower y) (Real.exp_nonneg _)
  have hbase := frozenElliptic_deriv_diff_abs_le p hu
    (fun y => (huM y).1) hw (fun y => (hwM y).1) x
  calc
    |deriv (frozenElliptic p u) x - deriv (frozenElliptic p w) x|
        ≤ 1 / 2 * ∫ y, Real.exp (-|x - y|) *
          |(u y) ^ p.γ - (w y) ^ p.γ| := hbase
    _ ≤ 1 / 2 * ∫ y,
          Real.exp (-|x - y|) * (rpowLip p.γ M * D) := by
        exact mul_le_mul_of_nonneg_left hkernel (by norm_num)
    _ = rpowLip p.γ M * D := by
        rw [integral_mul_const, exp_neg_abs_sub_integral_eq]
        ring

/-- A profile bounded by `M` generates a resolver gradient bounded by
`M^γ`. -/
theorem frozenElliptic_deriv_abs_le_rpow_of_Icc
    (p : CMParams) {M : ℝ} {u : ℝ → ℝ}
    (hM : 0 ≤ M) (hu : IsCUnifBdd u)
    (huM : ∀ x, u x ∈ Set.Icc (0 : ℝ) M) (x : ℝ) :
    |deriv (frozenElliptic p u) x| ≤ M ^ p.γ := by
  have hsource : ∀ y, (u y) ^ p.γ ≤ M ^ p.γ := by
    intro y
    exact Real.rpow_le_rpow (huM y).1 (huM y).2
      (zero_le_one.trans p.hγ)
  exact (frozenElliptic_deriv_abs_le p hu (fun y => (huM y).1) x).trans
    (frozenElliptic_le_of_rpow_le p (Real.rpow_nonneg hM _)
      hu.1 (fun y => (huM y).1) hsource x)

/-- The complete divergence-form chemotaxis flux is Lipschitz in the spatial
sup norm on the nonnegative strip `[0,M]`.  No derivative of the population
profile is used. -/
theorem wholeLineChemotaxisFlux_diff_abs_le
    (p : CMParams) {M D : ℝ} {u w : ℝ → ℝ}
    (hM : 0 ≤ M)
    (hu : IsCUnifBdd u) (hw : IsCUnifBdd w)
    (huM : ∀ x, u x ∈ Set.Icc (0 : ℝ) M)
    (hwM : ∀ x, w x ∈ Set.Icc (0 : ℝ) M)
    (hD : ∀ x, |u x - w x| ≤ D) (x : ℝ) :
    |wholeLineChemotaxisFlux p u x -
        wholeLineChemotaxisFlux p w x| ≤
      (rpowLip p.m M * M ^ p.γ +
          M ^ p.m * rpowLip p.γ M) * D := by
  have hD0 : 0 ≤ D := (abs_nonneg (u 0 - w 0)).trans (hD 0)
  have hLm0 : 0 ≤ rpowLip p.m M := rpowLip_nonneg p.hm hM
  have hLγ0 : 0 ≤ rpowLip p.γ M := rpowLip_nonneg p.hγ hM
  have hMγ : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM _
  have hMm : 0 ≤ M ^ p.m := Real.rpow_nonneg hM _
  have hpow : |(u x) ^ p.m - (w x) ^ p.m| ≤
      rpowLip p.m M * D := by
    calc
      |(u x) ^ p.m - (w x) ^ p.m|
          ≤ rpowLip p.m M * |u x - w x| := by
            simpa only [rpowLip] using
              abs_rpow_sub_rpow_le_of_mem_Icc p.hm hM (huM x) (hwM x)
      _ ≤ rpowLip p.m M * D :=
        mul_le_mul_of_nonneg_left (hD x) hLm0
  have hRu := frozenElliptic_deriv_abs_le_rpow_of_Icc p hM hu huM x
  have hRdiff := frozenElliptic_deriv_diff_uniform_abs_le p hM hu hw
    huM hwM hD x
  have hwpow : |(w x) ^ p.m| ≤ M ^ p.m := by
    rw [abs_of_nonneg (Real.rpow_nonneg (hwM x).1 _)]
    exact Real.rpow_le_rpow (hwM x).1 (hwM x).2
      (zero_le_one.trans p.hm)
  have hsplit : wholeLineChemotaxisFlux p u x -
      wholeLineChemotaxisFlux p w x =
        ((u x) ^ p.m - (w x) ^ p.m) *
            deriv (frozenElliptic p u) x +
          (w x) ^ p.m *
            (deriv (frozenElliptic p u) x -
              deriv (frozenElliptic p w) x) := by
    simp only [wholeLineChemotaxisFlux]
    ring
  rw [hsplit]
  calc
    |((u x) ^ p.m - (w x) ^ p.m) *
          deriv (frozenElliptic p u) x +
        (w x) ^ p.m *
          (deriv (frozenElliptic p u) x -
            deriv (frozenElliptic p w) x)|
        ≤ |(u x) ^ p.m - (w x) ^ p.m| *
              |deriv (frozenElliptic p u) x| +
            |(w x) ^ p.m| *
              |deriv (frozenElliptic p u) x -
                deriv (frozenElliptic p w) x| := by
          simpa only [abs_mul] using abs_add_le
            (((u x) ^ p.m - (w x) ^ p.m) *
              deriv (frozenElliptic p u) x)
            ((w x) ^ p.m *
              (deriv (frozenElliptic p u) x -
                deriv (frozenElliptic p w) x))
    _ ≤ (rpowLip p.m M * D) * M ^ p.γ +
          M ^ p.m * (rpowLip p.γ M * D) := by
        exact add_le_add
          (mul_le_mul hpow hRu (abs_nonneg _) (mul_nonneg hLm0 hD0))
          (mul_le_mul hwpow hRdiff (abs_nonneg _) hMm)
    _ = (rpowLip p.m M * M ^ p.γ +
          M ^ p.m * rpowLip p.γ M) * D := by ring

/-- The chemotaxis flux itself is uniformly bounded on a nonnegative strip. -/
theorem wholeLineChemotaxisFlux_abs_le
    (p : CMParams) {M : ℝ} {u : ℝ → ℝ}
    (hM : 0 ≤ M) (hu : IsCUnifBdd u)
    (huM : ∀ x, u x ∈ Set.Icc (0 : ℝ) M) (x : ℝ) :
    |wholeLineChemotaxisFlux p u x| ≤ M ^ p.m * M ^ p.γ := by
  have hupow : |(u x) ^ p.m| ≤ M ^ p.m := by
    rw [abs_of_nonneg (Real.rpow_nonneg (huM x).1 _)]
    exact Real.rpow_le_rpow (huM x).1 (huM x).2
      (zero_le_one.trans p.hm)
  have hR := frozenElliptic_deriv_abs_le_rpow_of_Icc p hM hu huM x
  simpa only [wholeLineChemotaxisFlux, abs_mul] using
    mul_le_mul hupow hR (abs_nonneg _) (Real.rpow_nonneg hM _)

/-- The scalar logistic source in the whole-line Cauchy problem. -/
def wholeLineLogisticSource
    (p : CMParams) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  reactionFun p.α (u x)

/-- The logistic source is uniformly bounded on a nonnegative strip. -/
theorem wholeLineLogisticSource_abs_le
    (p : CMParams) {M : ℝ} {u : ℝ → ℝ}
    (hM : 0 ≤ M) (huM : ∀ x, u x ∈ Set.Icc (0 : ℝ) M) (x : ℝ) :
    |wholeLineLogisticSource p u x| ≤ M * (1 + M ^ p.α) := by
  have hupow : (u x) ^ p.α ≤ M ^ p.α :=
    Real.rpow_le_rpow (huM x).1 (huM x).2 (zero_le_one.trans p.hα)
  have huabs : |u x| ≤ M := by
    rw [abs_of_nonneg (huM x).1]
    exact (huM x).2
  have hinner : |1 - (u x) ^ p.α| ≤ 1 + M ^ p.α := by
    calc
      |1 - (u x) ^ p.α| ≤ |(1 : ℝ)| + |(u x) ^ p.α| := abs_sub _ _
      _ = 1 + (u x) ^ p.α := by
        rw [abs_one, abs_of_nonneg (Real.rpow_nonneg (huM x).1 _)]
      _ ≤ 1 + M ^ p.α := by linarith
  simpa only [wholeLineLogisticSource, reactionFun, abs_mul] using
    mul_le_mul huabs hinner (abs_nonneg _) hM

/-- The logistic source is Lipschitz in the spatial sup norm on `[0,M]`. -/
theorem wholeLineLogisticSource_diff_abs_le
    (p : CMParams) {M D : ℝ} {u w : ℝ → ℝ}
    (hM : 0 ≤ M)
    (huM : ∀ x, u x ∈ Set.Icc (0 : ℝ) M)
    (hwM : ∀ x, w x ∈ Set.Icc (0 : ℝ) M)
    (hD : ∀ x, |u x - w x| ≤ D) (x : ℝ) :
    |wholeLineLogisticSource p u x -
        wholeLineLogisticSource p w x| ≤ reactionLip p.α M * D := by
  calc
    |wholeLineLogisticSource p u x - wholeLineLogisticSource p w x|
        ≤ reactionLip p.α M * |u x - w x| := by
          exact reaction_increment_abs_le p.hα hM (hwM x) (huM x)
    _ ≤ reactionLip p.α M * D :=
      mul_le_mul_of_nonneg_left (hD x) (reactionLip_nonneg p.hα hM)

section WholeLineCauchyLocalExistenceAxiomAudit

#print axioms frozenElliptic_deriv_diff_uniform_abs_le
#print axioms frozenElliptic_deriv_abs_le_rpow_of_Icc
#print axioms wholeLineChemotaxisFlux_diff_abs_le
#print axioms wholeLineChemotaxisFlux_abs_le
#print axioms wholeLineLogisticSource_abs_le
#print axioms wholeLineLogisticSource_diff_abs_le

end WholeLineCauchyLocalExistenceAxiomAudit

end ShenWork.Paper1
