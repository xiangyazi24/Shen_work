import ShenWork.Paper1.WholeLineWeightedRegularityHalfLineResolverLowerNatural

open Filter MeasureTheory Set Topology Real

noncomputable section

namespace ShenWork.Paper1

/-!
# Frozen-resolver upper bound from a left half-line ceiling

The normalized elliptic kernel has mass `2`.  At a point at least `R` to the
left of a half-line endpoint, at most `exp (-R)` of that mass sees the global
ceiling instead of the sharper left-half-line ceiling.
-/

/-- A population ceiling on `(-∞, z₀]`, together with a global ceiling, gives
an explicit upper bound for the frozen elliptic resolver at points at least
`R` to the left of `z₀`. -/
theorem frozenElliptic_upper_of_left_halfLine_ceiling
    (p : CMParams) {u : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ y, 0 ≤ u y)
    {M G z₀ R x : ℝ} (hM : 0 ≤ M) (hMG : M ≤ G)
    (hglobal : ∀ y, u y ≤ G)
    (hceiling : ∀ y, y ≤ z₀ → u y ≤ M)
    (hR : 0 ≤ R) (hx : x ≤ z₀ - R) :
    frozenElliptic p u x ≤
      (1 - Real.exp (-R) / 2) * M ^ p.γ +
        (Real.exp (-R) / 2) * G ^ p.γ := by
  let K : ℝ → ℝ := fun y => Real.exp (-|x - y|)
  have hgamma0 : 0 ≤ p.γ := by linarith [p.hγ]
  have hG : 0 ≤ G := hM.trans hMG
  have hMpow0 : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM p.γ
  have hpowGap : 0 ≤ G ^ p.γ - M ^ p.γ := by
    exact sub_nonneg.mpr (Real.rpow_le_rpow hM hMG hgamma0)
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
  have htailIci :
      (∫ y in Set.Ici z₀, K y) ≤ Real.exp (-R) := by
    have htail0' :
        (∫ y in Set.Ici z₀, K y) ≤ Real.exp x * Real.exp (-z₀) := by
      simpa only [K] using htail0
    exact htail0'.trans htailFactor
  have htail :
      (∫ y in Set.Ioi z₀, K y) ≤ Real.exp (-R) := by
    rw [← MeasureTheory.integral_Ici_eq_integral_Ioi]
    exact htailIci
  have hsplitK := MeasureTheory.integral_add_compl
    (μ := volume) (s := Set.Iic z₀) measurableSet_Iic hKint
  rw [Set.compl_Iic,
    show (∫ y, K y) = 2 by
      simpa only [K] using exp_neg_abs_sub_integral_eq x] at hsplitK
  have hlocalMass :
      (∫ y in Set.Iic z₀, K y) = 2 - ∫ y in Set.Ioi z₀, K y := by
    linarith
  have hMconst : Integrable (fun y => K y * M ^ p.γ) :=
    hKint.mul_const (M ^ p.γ)
  have hGconst : Integrable (fun y => K y * G ^ p.γ) :=
    hKint.mul_const (G ^ p.γ)
  have hlocalMono :
      (∫ y in Set.Iic z₀, K y * (u y) ^ p.γ) ≤
        ∫ y in Set.Iic z₀, K y * M ^ p.γ := by
    exact MeasureTheory.setIntegral_mono_on
      hKsource.integrableOn hMconst.integrableOn measurableSet_Iic
        (fun y hy => mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (hu_nonneg y) (hceiling y hy) hgamma0)
          (Real.exp_nonneg _))
  have htailMono :
      (∫ y in Set.Ioi z₀, K y * (u y) ^ p.γ) ≤
        ∫ y in Set.Ioi z₀, K y * G ^ p.γ := by
    exact MeasureTheory.setIntegral_mono_on
      hKsource.integrableOn hGconst.integrableOn measurableSet_Ioi
        (fun y _hy => mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (hu_nonneg y) (hglobal y) hgamma0)
          (Real.exp_nonneg _))
  have hsplitSource := MeasureTheory.integral_add_compl
    (μ := volume) (s := Set.Iic z₀) measurableSet_Iic hKsource
  rw [Set.compl_Iic] at hsplitSource
  have hsourceBound :
      (∫ y, K y * (u y) ^ p.γ) ≤
        2 * M ^ p.γ + Real.exp (-R) * (G ^ p.γ - M ^ p.γ) := by
    calc
      (∫ y, K y * (u y) ^ p.γ) =
          (∫ y in Set.Iic z₀, K y * (u y) ^ p.γ) +
            ∫ y in Set.Ioi z₀, K y * (u y) ^ p.γ := hsplitSource.symm
      _ ≤ (∫ y in Set.Iic z₀, K y * M ^ p.γ) +
            ∫ y in Set.Ioi z₀, K y * G ^ p.γ := add_le_add hlocalMono htailMono
      _ = (∫ y in Set.Iic z₀, K y) * M ^ p.γ +
            (∫ y in Set.Ioi z₀, K y) * G ^ p.γ := by
              rw [MeasureTheory.integral_mul_const,
                MeasureTheory.integral_mul_const]
      _ = 2 * M ^ p.γ +
            (∫ y in Set.Ioi z₀, K y) * (G ^ p.γ - M ^ p.γ) := by
              rw [hlocalMass]
              ring
      _ ≤ 2 * M ^ p.γ +
            Real.exp (-R) * (G ^ p.γ - M ^ p.γ) := by
              exact add_le_add_right
                (mul_le_mul_of_nonneg_right htail hpowGap) _
  unfold frozenElliptic Psi
  dsimp only [K] at hsourceBound ⊢
  simp only [Real.sqrt_one, neg_mul, one_mul]
  nlinarith

/-- The lower and upper half-line resolver bounds packaged as one interval
pinching statement. -/
theorem frozenElliptic_pinched_of_left_halfLine_bounds
    (p : CMParams) {u : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ y, 0 ≤ u y)
    {ell M G z₀ R x : ℝ} (hell : 0 ≤ ell) (hM : 0 ≤ M) (hMG : M ≤ G)
    (hglobal : ∀ y, u y ≤ G)
    (hfloor : ∀ y, y ≤ z₀ → ell ≤ u y)
    (hceiling : ∀ y, y ≤ z₀ → u y ≤ M)
    (hR : 0 ≤ R) (hx : x ≤ z₀ - R) :
    frozenElliptic p u x ∈ Set.Icc
      ((1 - Real.exp (-R) / 2) * ell ^ p.γ)
      ((1 - Real.exp (-R) / 2) * M ^ p.γ +
        (Real.exp (-R) / 2) * G ^ p.γ) := by
  constructor
  · exact frozenElliptic_lower_of_left_halfLine_floor
      p hu hu_nonneg hell hfloor hR hx
  · exact frozenElliptic_upper_of_left_halfLine_ceiling
      p hu hu_nonneg hM hMG hglobal hceiling hR hx

section AxiomAudit

#print axioms frozenElliptic_upper_of_left_halfLine_ceiling
#print axioms frozenElliptic_pinched_of_left_halfLine_bounds

end AxiomAudit

end ShenWork.Paper1
