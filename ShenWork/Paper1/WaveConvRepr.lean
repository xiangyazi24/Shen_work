/-
  ShenWork/Paper1/WaveConvRepr.lean

  The convolution-representation bridge: the divergence-form auxiliary map
  `auxMap` equals the variation-of-parameters convolution `−greenConv(auxRHS)`.

  This is the last analytic brick discharging `GreenIdentity` end-to-end.

  Two pieces:

  * `kernelConv_eq_greenConv` (step 1) — the SMOOTH convolution against the
    Green kernel equals the explicit two-sided split:
        `∫ y, Kλ(x−y)·G(y) dy = greenConv c λ G x`.
    Proof: split `ℝ = Iic x ∪ Ioi x`; on `Iic x` (where `x−y ≥ 0`) the kernel
    is the `r₋` branch `(1/δ)e^{r₋(x−y)}`, on `Ioi x` (where `x−y < 0`) the
    `r₊` branch `(1/δ)e^{r₊(x−y)}`; factor `e^{r·x}` out of each set integral.

  * `auxMap_eq_negGreenConv` (step 1 + 2) — combine with the integration by
    parts of the chemotactic flux term, carried as the explicit hypothesis
    `hIBP` (`−χ∫ Kλ'(x−y)·flux = −χ∫ Kλ(x−y)·flux'`, boundary terms vanishing
    by decay and the kernel `C⁰` kink cancelling — a separate analytic brick).

  Then `greenIdentity_holds` is `greenIdentity_of_convRepr` applied to the
  representation plus the source decay hypotheses.
-/
import ShenWork.Paper1.WaveGreenIdentity

open Filter Topology MeasureTheory Real Set intervalIntegral

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## Step 1 — kernel convolution = explicit two-sided split

For a continuous source `G` with the two exponential-weighted tails
integrable, the smooth convolution `∫ y, Kλ(x−y)·G(y) dy` equals
`greenConv c λ G x`.  We carry the per-set integrability of the products
`y ↦ Kλ(x−y)·G(y)` (which on the trap follow from boundedness of `G`). -/

/-- On `Iic x` the kernel `Kλ(x−y)` is the `r₋` branch, so the integrand equals
`(1/δ)·e^{r₋ x}·(e^{−r₋ y}·G y)`. -/
theorem kernel_eqOn_Iic (G : ℝ → ℝ) (x : ℝ) :
    Set.EqOn (fun y => greenKernel c lam (x - y) * G y)
      (fun y => (greenDelta c lam)⁻¹ * Real.exp (greenRootMinus c lam * x)
        * gWeight (greenRootMinus c lam) G y) (Set.Iic x) := by
  intro y hy
  have hyx : y ≤ x := by simpa using hy
  -- Reduce both kernel branches to the `r₋(x−y)` exponential: at the kink
  -- `x−y = 0` both branch values coincide (`exp 0 = 1`), so we may pick `r₋`.
  have hkern : greenKernel c lam (x - y)
      = (greenDelta c lam)⁻¹ * Real.exp (greenRootMinus c lam * (x - y)) := by
    simp only [greenKernel]
    by_cases hz : x - y ≤ 0
    · have hz0 : x - y = 0 := le_antisymm hz (by linarith)
      rw [if_pos hz, hz0]; simp
    · rw [if_neg hz]
  simp only [gWeight]
  rw [hkern]
  rw [show greenRootMinus c lam * (x - y)
      = greenRootMinus c lam * x + (-greenRootMinus c lam) * y by ring,
    Real.exp_add]
  ring

/-- On `Ioi x` the kernel `Kλ(x−y)` is the `r₊` branch, so the integrand equals
`(1/δ)·e^{r₊ x}·(e^{−r₊ y}·G y)`. -/
theorem kernel_eqOn_Ioi (G : ℝ → ℝ) (x : ℝ) :
    Set.EqOn (fun y => greenKernel c lam (x - y) * G y)
      (fun y => (greenDelta c lam)⁻¹ * Real.exp (greenRootPlus c lam * x)
        * gWeight (greenRootPlus c lam) G y) (Set.Ioi x) := by
  intro y hy
  have hxy : x < y := by simpa using hy
  have hz : x - y ≤ 0 := by linarith
  simp only [greenKernel, gWeight]
  rw [if_pos hz]
  rw [show greenRootPlus c lam * (x - y)
      = greenRootPlus c lam * x + (-greenRootPlus c lam) * y by ring,
    Real.exp_add]
  ring

/-- **Step 1.** The kernel convolution equals the explicit two-sided split
`greenConv c λ G x`. -/
theorem kernelConv_eq_greenConv (G : ℝ → ℝ) (x : ℝ)
    (hIic : IntegrableOn (fun y => greenKernel c lam (x - y) * G y) (Set.Iic x))
    (hIoi : IntegrableOn (fun y => greenKernel c lam (x - y) * G y) (Set.Ioi x)) :
    (∫ y, greenKernel c lam (x - y) * G y) = greenConv c lam G x := by
  -- Split ℝ = Iic x ∪ Ioi x.
  have hfi : Integrable (fun y => greenKernel c lam (x - y) * G y) := by
    rw [← integrableOn_univ,
      show (Set.univ : Set ℝ) = Set.Iic x ∪ Set.Ioi x by
        ext y; constructor
        · intro _; rcases le_or_gt y x with h | h
          · exact Or.inl h
          · exact Or.inr h
        · intro _; trivial]
    exact hIic.union hIoi
  have hsplit := MeasureTheory.integral_add_compl
    (s := Set.Iic x) measurableSet_Iic hfi
  simp only [Set.compl_Iic] at hsplit
  -- Left branch (Iic x): factor e^{r₋ x}.
  have hLeft : ∫ y in Set.Iic x, greenKernel c lam (x - y) * G y
      = (greenDelta c lam)⁻¹ * Real.exp (greenRootMinus c lam * x)
          * tailLo (greenRootMinus c lam) G x := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Iic
      (kernel_eqOn_Iic (c := c) (lam := lam) G x)]
    rw [MeasureTheory.integral_const_mul]
    rfl
  -- Right branch (Ioi x): factor e^{r₊ x}.
  have hRight : ∫ y in Set.Ioi x, greenKernel c lam (x - y) * G y
      = (greenDelta c lam)⁻¹ * Real.exp (greenRootPlus c lam * x)
          * tailHi (greenRootPlus c lam) G x := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (kernel_eqOn_Ioi (c := c) (lam := lam) G x)]
    rw [MeasureTheory.integral_const_mul]
    rfl
  rw [← hsplit, hLeft, hRight, greenConv]
  ring

/-! ## Step 1 applied to the smooth (reaction + λu) source -/

/-- The smooth part of `auxMap` is `greenConv c λ (auxReaction+λu)`. -/
theorem auxMap_smooth_eq_greenConv (p : CMParams) (u : ℝ → ℝ) (x : ℝ)
    (hIic : IntegrableOn (fun y => greenKernel c lam (x - y)
      * (auxReaction p u y + lam * u y)) (Set.Iic x))
    (hIoi : IntegrableOn (fun y => greenKernel c lam (x - y)
      * (auxReaction p u y + lam * u y)) (Set.Ioi x)) :
    (∫ y, greenKernel c lam (x - y) * (auxReaction p u y + lam * u y))
      = greenConv c lam (fun y => auxReaction p u y + lam * u y) x :=
  kernelConv_eq_greenConv (fun y => auxReaction p u y + lam * u y) x hIic hIoi

/-! ## Step 1 + 2 — the full representation

We combine step 1 (the smooth term = `greenConv (F+λu)`) with the
integration-by-parts identity for the chemotactic flux term

    `−χ ∫ y, Kλ'(x−y)·flux y dy = greenConv c λ (fun y ↦ −χ·flux' y) x`

carried as `hIBP`.  Linearity of `greenConv` in its source then collapses
the two pieces into `greenConv c λ (fun y ↦ (F+λu) − χ·flux') = −greenConv(auxRHS)`,
because `−auxRHS = (F+λu) − χ·flux'`. -/

/-- `greenConv` is additive in the source. -/
theorem greenConv_add (G₁ G₂ : ℝ → ℝ) (x : ℝ)
    (h₁Hi : IntegrableOn (gWeight (greenRootPlus c lam) G₁) (Set.Ioi x))
    (h₂Hi : IntegrableOn (gWeight (greenRootPlus c lam) G₂) (Set.Ioi x))
    (h₁Lo : IntegrableOn (gWeight (greenRootMinus c lam) G₁) (Set.Iic x))
    (h₂Lo : IntegrableOn (gWeight (greenRootMinus c lam) G₂) (Set.Iic x)) :
    greenConv c lam (fun y => G₁ y + G₂ y) x
      = greenConv c lam G₁ x + greenConv c lam G₂ x := by
  simp only [greenConv, tailHi, tailLo]
  have hHi : (∫ y in Set.Ioi x, gWeight (greenRootPlus c lam) (fun y => G₁ y + G₂ y) y)
      = (∫ y in Set.Ioi x, gWeight (greenRootPlus c lam) G₁ y)
        + ∫ y in Set.Ioi x, gWeight (greenRootPlus c lam) G₂ y := by
    rw [← MeasureTheory.integral_add h₁Hi h₂Hi]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro y _; simp only [gWeight]; ring
  have hLo : (∫ y in Set.Iic x, gWeight (greenRootMinus c lam) (fun y => G₁ y + G₂ y) y)
      = (∫ y in Set.Iic x, gWeight (greenRootMinus c lam) G₁ y)
        + ∫ y in Set.Iic x, gWeight (greenRootMinus c lam) G₂ y := by
    rw [← MeasureTheory.integral_add h₁Lo h₂Lo]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
    intro y _; simp only [gWeight]; ring
  rw [hHi, hLo]; ring

/-- `greenConv (−H) = −greenConv H`. -/
theorem greenConv_neg (H : ℝ → ℝ) (x : ℝ) :
    greenConv c lam (fun y => -H y) x = -greenConv c lam H x := by
  simp only [greenConv, tailHi, tailLo]
  have hHi : (∫ y in Set.Ioi x, gWeight (greenRootPlus c lam) (fun y => -H y) y)
      = -∫ y in Set.Ioi x, gWeight (greenRootPlus c lam) H y := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro y _; simp only [gWeight]; ring
  have hLo : (∫ y in Set.Iic x, gWeight (greenRootMinus c lam) (fun y => -H y) y)
      = -∫ y in Set.Iic x, gWeight (greenRootMinus c lam) H y := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
    intro y _; simp only [gWeight]; ring
  rw [hHi, hLo]; ring

/-- `−auxRHS = (auxReaction + λu) + (−χ·flux')` pointwise. -/
theorem neg_auxRHS_eq (p : CMParams) (lam : ℝ) (u : ℝ → ℝ) (y : ℝ) :
    -auxRHS p lam u y
      = (auxReaction p u y + lam * u y) + (-p.χ * deriv (auxFlux p u) y) := by
  simp only [auxRHS]; ring

/-- **The convolution representation.**  Granting step 1's integrability for the
smooth term, and the IBP identity `hIBP` for the flux term (which represents
`−χ∫ Kλ'(x−y)·flux = greenConv c λ (−χ·flux')`), plus the per-tail
integrabilities used to split the combined source, we obtain
`auxMap = −greenConv(auxRHS)`. -/
theorem auxMap_eq_negGreenConv (p : CMParams) (u : ℝ → ℝ) (x : ℝ)
    (hIic : IntegrableOn (fun y => greenKernel c lam (x - y)
      * (auxReaction p u y + lam * u y)) (Set.Iic x))
    (hIoi : IntegrableOn (fun y => greenKernel c lam (x - y)
      * (auxReaction p u y + lam * u y)) (Set.Ioi x))
    (hIBP : -p.χ * ∫ y, greenKernelDeriv c lam (x - y) * auxFlux p u y
      = greenConv c lam (fun y => -p.χ * deriv (auxFlux p u) y) x)
    (hSmHi : IntegrableOn
      (gWeight (greenRootPlus c lam) (fun y => auxReaction p u y + lam * u y)) (Set.Ioi x))
    (hSmLo : IntegrableOn
      (gWeight (greenRootMinus c lam) (fun y => auxReaction p u y + lam * u y)) (Set.Iic x))
    (hFlHi : IntegrableOn
      (gWeight (greenRootPlus c lam) (fun y => -p.χ * deriv (auxFlux p u) y)) (Set.Ioi x))
    (hFlLo : IntegrableOn
      (gWeight (greenRootMinus c lam) (fun y => -p.χ * deriv (auxFlux p u) y)) (Set.Iic x)) :
    auxMap p c lam u x = - greenConv c lam (auxRHS p lam u) x := by
  -- auxMap = (smooth conv) − χ·(flux conv)
  simp only [auxMap]
  rw [auxMap_smooth_eq_greenConv (c := c) (lam := lam) p u x hIic hIoi]
  -- rewrite the flux term via the IBP hypothesis (note: A − χ·∫ = A + (−χ·∫))
  rw [show greenConv c lam (fun y => auxReaction p u y + lam * u y) x
        - p.χ * ∫ y, greenKernelDeriv c lam (x - y) * auxFlux p u y
      = greenConv c lam (fun y => auxReaction p u y + lam * u y) x
        + (-p.χ * ∫ y, greenKernelDeriv c lam (x - y) * auxFlux p u y) by ring,
    hIBP]
  -- combine via additivity, then collapse to −greenConv(auxRHS)
  rw [← greenConv_add (c := c) (lam := lam)
    (fun y => auxReaction p u y + lam * u y)
    (fun y => -p.χ * deriv (auxFlux p u) y) x hSmHi hFlHi hSmLo hFlLo]
  rw [show -greenConv c lam (auxRHS p lam u) x
      = greenConv c lam (fun y => -(auxRHS p lam u) y) x from
    (greenConv_neg (c := c) (lam := lam) (auxRHS p lam u) x).symm]
  congr 1
  funext y
  rw [neg_auxRHS_eq]

/-! ## End-to-end Green identity -/

/-- **GreenIdentity end-to-end.**  From the convolution representation
(`auxMap = −greenConv(auxRHS)`) plus the source continuity and the two-sided
decay tails, `GreenIdentity p c λ u` holds. -/
theorem greenIdentity_holds (hlam : 0 < lam) (p : CMParams) (u : ℝ → ℝ)
    (hH : Continuous (auxRHS p lam u))
    (hHi : ∀ t : ℝ,
      IntegrableOn (gWeight (greenRootPlus c lam) (auxRHS p lam u)) (Set.Ioi t))
    (hLo : ∀ t : ℝ,
      IntegrableOn (gWeight (greenRootMinus c lam) (auxRHS p lam u)) (Set.Iic t))
    (hrepr : auxMap p c lam u = fun x => -greenConv c lam (auxRHS p lam u) x) :
    GreenIdentity p c lam u :=
  greenIdentity_of_convRepr (c := c) (lam := lam) hlam p u hH hHi hLo hrepr

end ShenWork.Paper1
