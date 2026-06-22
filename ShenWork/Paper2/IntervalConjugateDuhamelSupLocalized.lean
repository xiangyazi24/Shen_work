/-
  Localized conjugate-kernel √T sup bound: the same estimate as
  `conjugateDuhamel_sup_bound`, but the per-slice integrability/sup hypotheses
  are required ONLY on `s ∈ Icc 0 t` (the actual integration window), not
  globally over all `s`.  This removes the spurious global-`∀ s` requirement that
  otherwise blocks the `hmapsTo` FIELD discharge (the Core field bounds the
  trajectory only on `(0,T]`, leaving `w s` unconstrained off-window).

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.Paper2.IntervalConjugateDuhamelMap

open MeasureTheory Set
open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant heatGradientLinftyLinftyConstant_nonneg)

noncomputable section

namespace ShenWork.IntervalConjugateDuhamelMap

/-- **Localized conjugate-kernel √T sup bound.**  Identical conclusion to
`conjugateDuhamel_sup_bound`, with per-slice integrability and sup hypotheses
restricted to the integration window `Icc 0 t`. -/
theorem conjugateDuhamel_sup_bound_localized
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) {q : ℝ → ℝ → ℝ}
    (hq_int : ∀ s ∈ Set.Icc (0 : ℝ) t, Integrable (q s) (intervalMeasure 1))
    {Cq : ℝ} (hCq : 0 ≤ Cq)
    (hq_sup : ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ y, |q s y| ≤ Cq) (x : ℝ)
    (hB_int : IntervalIntegrable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s) (q s) x) volume 0 t) :
    |∫ s in (0:ℝ)..t, intervalConjugateKernelOperator (t - s) (q s) x|
      ≤ heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * Cq := by
  set Cg := heatGradientLinftyLinftyConstant with hCgdef
  have hCgnn : 0 ≤ Cg := heatGradientLinftyLinftyConstant_nonneg
  have hptw : ∀ s, 0 ≤ s → s < t →
      |intervalConjugateKernelOperator (t - s) (q s) x|
        ≤ Cg * Cq * (t - s) ^ (-(1/2) : ℝ) := by
    intro s hs0 hst
    have hts : 0 < t - s := sub_pos.mpr hst
    have hmem : s ∈ Set.Icc (0 : ℝ) t := ⟨hs0, hst.le⟩
    have h := intervalConjugateKernelOperator_abs_le hts (hq_int s hmem)
      (hq_sup s hmem) x
    calc |intervalConjugateKernelOperator (t - s) (q s) x|
        ≤ Cg * (t - s) ^ (-(1 / 2) : ℝ) * Cq := by simpa [Cg] using h
      _ = Cg * Cq * (t - s) ^ (-(1 / 2) : ℝ) := by ring
  have hdom_int : IntervalIntegrable
      (fun s : ℝ => Cg * Cq * (t - s) ^ (-(1/2) : ℝ)) volume 0 t :=
    ((ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t).const_mul
      (Cg * Cq))
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  have hae : (fun s : ℝ => |intervalConjugateKernelOperator (t - s) (q s) x|)
      ≤ᵐ[volume.restrict (Set.Icc 0 t)]
      (fun s : ℝ => Cg * Cq * (t - s) ^ (-(1/2) : ℝ)) := by
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [hne] with s hs_ne hs_mem
    exact hptw s hs_mem.1 (lt_of_le_of_ne hs_mem.2 hs_ne)
  calc |∫ s in (0:ℝ)..t, intervalConjugateKernelOperator (t - s) (q s) x|
      ≤ ∫ s in (0:ℝ)..t, |intervalConjugateKernelOperator (t - s) (q s) x| :=
        intervalIntegral.abs_integral_le_integral_abs ht.le
    _ ≤ ∫ s in (0:ℝ)..t, Cg * Cq * (t - s) ^ (-(1/2) : ℝ) :=
        intervalIntegral.integral_mono_ae_restrict ht.le hB_int.abs hdom_int hae
    _ = Cg * Cq * (2 * Real.sqrt t) := by
        rw [intervalIntegral.integral_const_mul,
          ShenWork.IntervalGradDuhamelBound.integral_sub_rpow_neg_half ht.le]
    _ ≤ Cg * (2 * Real.sqrt T) * Cq := by
        have hsqrt : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt htT
        nlinarith [hCgnn, hCq, Real.sqrt_nonneg t, Real.sqrt_nonneg T, hsqrt,
          mul_nonneg hCgnn hCq]

#print axioms conjugateDuhamel_sup_bound_localized

end ShenWork.IntervalConjugateDuhamelMap
