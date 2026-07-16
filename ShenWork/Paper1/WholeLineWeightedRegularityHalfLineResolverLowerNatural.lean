import ShenWork.Paper1.WaveFrozenEllipticDep

open Filter MeasureTheory Set Topology Real

noncomputable section

namespace ShenWork.Paper1

/-!
# Frozen-resolver lower bound from a left half-line floor

The elliptic resolver does not need a global population floor.  If the
population is bounded below on a left half-line and the observation point is
at least `R` to the left of its endpoint, only the exponentially small right
kernel tail is lost.
-/

/-- A population floor on `(-∞, z₀]` gives an explicit lower bound for the
frozen elliptic resolver at points at least `R` to the left of `z₀`.

The factor tends to one as `R → ∞`; no population lower bound to the right of
`z₀` is assumed. -/
theorem frozenElliptic_lower_of_left_halfLine_floor
    (p : CMParams) {u : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ y, 0 ≤ u y)
    {a z₀ R x : ℝ} (ha : 0 ≤ a)
    (hfloor : ∀ y, y ≤ z₀ → a ≤ u y)
    (hR : 0 ≤ R) (hx : x ≤ z₀ - R) :
    (1 - Real.exp (-R) / 2) * a ^ p.γ ≤
      frozenElliptic p u x := by
  let K : ℝ → ℝ := fun y => Real.exp (-|x - y|)
  have hgamma0 : 0 ≤ p.γ := by linarith [p.hγ]
  have haPow0 : 0 ≤ a ^ p.γ := Real.rpow_nonneg ha p.γ
  have hxz₀ : x ≤ z₀ := by linarith
  have hKint : Integrable K := by
    simpa only [K] using exp_neg_abs_sub_integrable x
  have hsource : IsCUnifBdd (fun y => (u y) ^ p.γ) :=
    rpow_cunif_bdd_of_nonneg p hu hu_nonneg
  have hKsource : Integrable (fun y => K y * (u y) ^ p.γ) := by
    have hraw := Psi_kernel_integrable_of_isCUnifBdd
      (u := fun y => (u y) ^ p.γ) (l := 1) one_pos hsource x
    simpa only [K, Real.sqrt_one, neg_mul, one_mul] using hraw
  have htail0 := exp_neg_abs_sub_Ici_le (x := x) (R' := z₀) hxz₀
  have htailFactor : Real.exp x * Real.exp (-z₀) ≤ Real.exp (-R) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have htail :
      (∫ y in Set.Ici z₀, K y) ≤ Real.exp (-R) := by
    have htail0' :
        (∫ y in Set.Ici z₀, K y) ≤ Real.exp x * Real.exp (-z₀) := by
      simpa only [K] using htail0
    exact htail0'.trans htailFactor
  have hsplit := MeasureTheory.integral_add_compl
    (μ := volume) (s := Set.Iic z₀) measurableSet_Iic hKint
  have hmass : 2 - Real.exp (-R) ≤ ∫ y in Set.Iic z₀, K y := by
    rw [Set.compl_Iic, ← MeasureTheory.integral_Ici_eq_integral_Ioi,
      show (∫ y, K y) = 2 by
        simpa only [K] using exp_neg_abs_sub_integral_eq x] at hsplit
    linarith
  have hconstInt : Integrable (fun y => K y * a ^ p.γ) :=
    hKint.mul_const (a ^ p.γ)
  have hlocalMono :
      (∫ y in Set.Iic z₀, K y * a ^ p.γ) ≤
        ∫ y in Set.Iic z₀, K y * (u y) ^ p.γ := by
    exact MeasureTheory.setIntegral_mono_on
      hconstInt.integrableOn hKsource.integrableOn measurableSet_Iic
        (fun y hy => mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow ha (hfloor y hy) hgamma0)
          (Real.exp_nonneg _))
  have hlocalFull :
      (∫ y in Set.Iic z₀, K y * (u y) ^ p.γ) ≤
        ∫ y, K y * (u y) ^ p.γ := by
    exact MeasureTheory.integral_mono_measure
      MeasureTheory.Measure.restrict_le_self
      (Filter.Eventually.of_forall (fun y =>
        mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg (hu_nonneg y) p.γ)))
      hKsource
  calc
    (1 - Real.exp (-R) / 2) * a ^ p.γ =
        (1 / 2) * ((2 - Real.exp (-R)) * a ^ p.γ) := by ring
    _ ≤ (1 / 2) * ((∫ y in Set.Iic z₀, K y) * a ^ p.γ) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hmass haPow0) (by norm_num)
    _ = (1 / 2) * (∫ y in Set.Iic z₀, K y * a ^ p.γ) := by
      rw [MeasureTheory.integral_mul_const]
    _ ≤ (1 / 2) * (∫ y in Set.Iic z₀, K y * (u y) ^ p.γ) :=
      mul_le_mul_of_nonneg_left hlocalMono (by norm_num)
    _ ≤ (1 / 2) * (∫ y, K y * (u y) ^ p.γ) :=
      mul_le_mul_of_nonneg_left hlocalFull (by norm_num)
    _ = frozenElliptic p u x := by
      unfold frozenElliptic Psi
      dsimp only [K]
      simp only [Real.sqrt_one, neg_mul, one_mul]
      ring

section AxiomAudit

#print axioms frozenElliptic_lower_of_left_halfLine_floor

end AxiomAudit

end ShenWork.Paper1
