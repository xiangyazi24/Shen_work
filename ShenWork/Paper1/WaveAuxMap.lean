/-
  ShenWork/Paper1/WaveAuxMap.lean

  Green-kernel auxiliary map for the traveling-wave Schauder construction
  (Shen, arXiv:2605.04401, §3 frozen fixed-point step).

  The positive constant-coefficient operator
      `Aλ = −∂² − c∂ + λ`        (λ > 0),
  with `δ = √(c²+4λ)`, roots `r₊ = (−c+δ)/2 > 0`, `r₋ = (−c−δ)/2 < 0`,
  has Green kernel
      `Kλ(z) = (1/δ)·exp(r₊ z)`  for z ≤ 0,
      `Kλ(z) = (1/δ)·exp(r₋ z)`  for z ≥ 0,
  satisfying `Aλ Kλ = δ₀` and `∫ Kλ = 1/λ`.  Equivalently the operator
      `Lλ = ∂² + c∂ − λ`         (Lλ = −Aλ)
  obeys `Lλ Kλ = −δ₀`, so `Lλ w = H ⟺ w = −Kλ ∗ H`.

  This file supplies the FOUNDATION (the explicit kernel and its analytic
  facts), the auxiliary map `T` in divergence form, and the L4 bridge
  (fixed point of `T` ⟹ stationarity of `frozenWaveOperator`), the Green
  inversion being carried as an explicit analytic interface predicate.
-/
import ShenWork.Paper1.Statements
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Filter Topology MeasureTheory Real

noncomputable section

namespace ShenWork.Paper1

/-! ## Green-kernel parameters

For `c : ℝ` and `λ > 0` we record the discriminant `δ = √(c²+4λ)` and the
two characteristic roots `r₊, r₋` of `s² + c s − λ = 0`. -/

/-- Discriminant `δ = √(c² + 4λ)` of the characteristic polynomial. -/
def greenDelta (c lam : ℝ) : ℝ := Real.sqrt (c ^ 2 + 4 * lam)

/-- Positive characteristic root `r₊ = (−c + δ)/2`. -/
def greenRootPlus (c lam : ℝ) : ℝ := (-c + greenDelta c lam) / 2

/-- Negative characteristic root `r₋ = (−c − δ)/2`. -/
def greenRootMinus (c lam : ℝ) : ℝ := (-c - greenDelta c lam) / 2

variable {c lam : ℝ}

theorem greenDelta_pos (hlam : 0 < lam) : 0 < greenDelta c lam := by
  unfold greenDelta
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg c]

theorem greenDelta_sq (hlam : 0 < lam) :
    greenDelta c lam ^ 2 = c ^ 2 + 4 * lam := by
  unfold greenDelta
  rw [Real.sq_sqrt]; nlinarith [sq_nonneg c]

/-- `δ > |c|`, hence `r₊ > 0`. -/
theorem greenDelta_gt_abs (hlam : 0 < lam) : |c| < greenDelta c lam := by
  have hδ := greenDelta_pos (c := c) hlam
  have hsq := greenDelta_sq (c := c) hlam
  have : c ^ 2 < greenDelta c lam ^ 2 := by nlinarith
  nlinarith [abs_nonneg c, sq_abs c, hδ, this]

theorem greenRootPlus_pos (hlam : 0 < lam) : 0 < greenRootPlus c lam := by
  have hgt := greenDelta_gt_abs (c := c) hlam
  have h := le_abs_self c
  have hpos : 0 < -c + greenDelta c lam := by linarith
  unfold greenRootPlus
  linarith

theorem greenRootMinus_neg (hlam : 0 < lam) : greenRootMinus c lam < 0 := by
  have hgt := greenDelta_gt_abs (c := c) hlam
  have h := neg_abs_le c
  have hneg : -c - greenDelta c lam < 0 := by linarith
  unfold greenRootMinus
  linarith

/-- Vieta: `r₊ + r₋ = −c`. -/
theorem greenRoots_add : greenRootPlus c lam + greenRootMinus c lam = -c := by
  unfold greenRootPlus greenRootMinus; ring

/-- Vieta: `r₊ · r₋ = −λ`. -/
theorem greenRoots_mul (hlam : 0 < lam) :
    greenRootPlus c lam * greenRootMinus c lam = -lam := by
  unfold greenRootPlus greenRootMinus
  have hsq := greenDelta_sq (c := c) hlam
  field_simp
  nlinarith [hsq]

/-- Each root solves the characteristic equation `s² + c s − λ = 0`,
in the `Lλ`-friendly form `s² + c s = λ`. -/
theorem greenRootPlus_char (hlam : 0 < lam) :
    greenRootPlus c lam ^ 2 + c * greenRootPlus c lam = lam := by
  have hadd := greenRoots_add (c := c) (lam := lam)
  have hmul := greenRoots_mul (c := c) hlam
  linear_combination greenRootPlus c lam * hadd - hmul

theorem greenRootMinus_char (hlam : 0 < lam) :
    greenRootMinus c lam ^ 2 + c * greenRootMinus c lam = lam := by
  have hadd := greenRoots_add (c := c) (lam := lam)
  have hmul := greenRoots_mul (c := c) hlam
  linear_combination greenRootMinus c lam * hadd - hmul

/-! ## The Green kernel `Kλ` -/

/-- Green kernel `Kλ(z) = (1/δ)·exp(r₊ z)` for `z ≤ 0`, `(1/δ)·exp(r₋ z)`
for `z ≥ 0`.  (At `z = 0` both branches agree, value `1/δ`.) -/
def greenKernel (c lam z : ℝ) : ℝ :=
  if z ≤ 0 then (greenDelta c lam)⁻¹ * Real.exp (greenRootPlus c lam * z)
  else (greenDelta c lam)⁻¹ * Real.exp (greenRootMinus c lam * z)

/-- Derivative of `Kλ` away from the kink: `(r±/δ)·exp(r± z)`. -/
def greenKernelDeriv (c lam z : ℝ) : ℝ :=
  if z ≤ 0 then
    (greenDelta c lam)⁻¹ * greenRootPlus c lam * Real.exp (greenRootPlus c lam * z)
  else
    (greenDelta c lam)⁻¹ * greenRootMinus c lam * Real.exp (greenRootMinus c lam * z)

/-- `Kλ` is strictly positive everywhere. -/
theorem greenKernel_pos (hlam : 0 < lam) (z : ℝ) : 0 < greenKernel c lam z := by
  unfold greenKernel
  have hδ : 0 < (greenDelta c lam)⁻¹ := inv_pos.mpr (greenDelta_pos (c := c) hlam)
  split
  · exact mul_pos hδ (Real.exp_pos _)
  · exact mul_pos hδ (Real.exp_pos _)

theorem greenKernel_nonneg (hlam : 0 < lam) (z : ℝ) : 0 ≤ greenKernel c lam z :=
  (greenKernel_pos hlam z).le

/-- Derivative of `Kλ` at any `z ≠ 0`. -/
theorem greenKernel_hasDerivAt (hlam : 0 < lam) {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (greenKernel c lam) (greenKernelDeriv c lam z) z := by
  rcases lt_or_gt_of_ne hz with hzneg | hzpos
  · -- z < 0 : on the left branch, locally `(1/δ)·exp(r₊·z)`.
    have hloc : greenKernel c lam =ᶠ[𝓝 z]
        fun w => (greenDelta c lam)⁻¹ * Real.exp (greenRootPlus c lam * w) := by
      filter_upwards [eventually_lt_nhds hzneg] with w hw
      simp only [greenKernel, if_pos hw.le]
    have hd : HasDerivAt
        (fun w => (greenDelta c lam)⁻¹ * Real.exp (greenRootPlus c lam * w))
        ((greenDelta c lam)⁻¹ *
          (Real.exp (greenRootPlus c lam * z) * greenRootPlus c lam)) z := by
      have hlin : HasDerivAt (fun w => greenRootPlus c lam * w)
          (greenRootPlus c lam) z := by
        simpa using (hasDerivAt_id z).const_mul (greenRootPlus c lam)
      have he : HasDerivAt (fun w => Real.exp (greenRootPlus c lam * w))
          (Real.exp (greenRootPlus c lam * z) * greenRootPlus c lam) z :=
        hlin.exp
      exact he.const_mul _
    have := hd.congr_of_eventuallyEq hloc
    convert this using 1
    simp only [greenKernelDeriv, if_pos hzneg.le]; ring
  · -- z > 0 : on the right branch, locally `(1/δ)·exp(r₋·z)`.
    have hloc : greenKernel c lam =ᶠ[𝓝 z]
        fun w => (greenDelta c lam)⁻¹ * Real.exp (greenRootMinus c lam * w) := by
      filter_upwards [eventually_gt_nhds hzpos] with w hw
      simp only [greenKernel, if_neg (not_le.mpr hw)]
    have hd : HasDerivAt
        (fun w => (greenDelta c lam)⁻¹ * Real.exp (greenRootMinus c lam * w))
        ((greenDelta c lam)⁻¹ *
          (Real.exp (greenRootMinus c lam * z) * greenRootMinus c lam)) z := by
      have hlin : HasDerivAt (fun w => greenRootMinus c lam * w)
          (greenRootMinus c lam) z := by
        simpa using (hasDerivAt_id z).const_mul (greenRootMinus c lam)
      have he : HasDerivAt (fun w => Real.exp (greenRootMinus c lam * w))
          (Real.exp (greenRootMinus c lam * z) * greenRootMinus c lam) z :=
        hlin.exp
      exact he.const_mul _
    have := hd.congr_of_eventuallyEq hloc
    convert this using 1
    simp only [greenKernelDeriv, if_neg (not_le.mpr hzpos)]; ring

/-! ### Integrability and total mass of `Kλ`

We use the two exponential tails:
`∫_{Iic 0} exp(r₊ z) dz = 1/r₊` and `∫_{Ioi 0} exp(r₋ z) dz = −1/r₋`,
giving `∫ Kλ = (1/δ)(1/r₊ − 1/r₋) = (1/δ)((r₊−r₋)/(−λ))·(−1)= 1/λ`
using `r₊r₋=−λ`, `r₊−r₋=δ`. -/

theorem greenKernel_integrableOn_Iic (hlam : 0 < lam) :
    IntegrableOn (greenKernel c lam) (Set.Iic 0) := by
  have hr := greenRootPlus_pos (c := c) hlam
  have hbase : IntegrableOn
      (fun z => (greenDelta c lam)⁻¹ * Real.exp (greenRootPlus c lam * z))
      (Set.Iic 0) :=
    (integrableOn_exp_mul_Iic (a := greenRootPlus c lam) hr 0).const_mul _
  refine IntegrableOn.congr_fun hbase ?_ measurableSet_Iic
  intro z hz
  rw [Set.mem_Iic] at hz
  simp only [greenKernel, if_pos hz]

theorem greenKernel_integrableOn_Ioi (hlam : 0 < lam) :
    IntegrableOn (greenKernel c lam) (Set.Ioi 0) := by
  have hr := greenRootMinus_neg (c := c) hlam
  have hbase : IntegrableOn
      (fun z => (greenDelta c lam)⁻¹ * Real.exp (greenRootMinus c lam * z))
      (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (a := greenRootMinus c lam) hr 0).const_mul _
  refine IntegrableOn.congr_fun hbase ?_ measurableSet_Ioi
  intro z hz
  rw [Set.mem_Ioi] at hz
  simp only [greenKernel, if_neg (not_le.mpr hz)]

/-- `Kλ` is integrable on the whole line. -/
theorem greenKernel_integrable (hlam : 0 < lam) :
    Integrable (greenKernel c lam) := by
  have hIic := greenKernel_integrableOn_Iic (c := c) hlam
  have hIoi := greenKernel_integrableOn_Ioi (c := c) hlam
  have hsplit : (Set.univ : Set ℝ) = Set.Iic 0 ∪ Set.Ioi 0 := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Set.mem_Iic, Set.mem_Ioi, true_iff]
    exact le_or_gt x 0
  rw [← integrableOn_univ, hsplit]
  exact hIic.union hIoi

/-! ## The auxiliary (Green) map `T`

In the integrated-by-parts / divergence form the chemotactic term is
written with the kernel's derivative, avoiding `u'` in the input:
`T p c λ u x = ∫ y, Kλ(x−y)·(F u y + λ·u y) − χ·∫ y, Kλ'(x−y)·Q u y`,
where `F u y = u y·(1 − (u y)^α)`, `Q u y = (u y)^m·(frozenElliptic p u)' y`. -/

/-- Reaction source `F u y = u y · (1 − (u y)^α)`. -/
def auxReaction (p : CMParams) (u : ℝ → ℝ) (y : ℝ) : ℝ :=
  u y * (1 - (u y) ^ p.α)

/-- Chemotactic flux `Q u y = (u y)^m · (frozenElliptic p u)' y`. -/
def auxFlux (p : CMParams) (u : ℝ → ℝ) (y : ℝ) : ℝ :=
  (u y) ^ p.m * deriv (frozenElliptic p u) y

/-- The auxiliary map, divergence form. -/
def auxMap (p : CMParams) (c lam : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun x =>
    (∫ y, greenKernel c lam (x - y) * (auxReaction p u y + lam * u y))
      - p.χ * ∫ y, greenKernelDeriv c lam (x - y) * auxFlux p u y

/-- Divergence-form right-hand side `H` of the wave ODE written for `Lλ`:
`Lλ U = U'' + cU' − λU = χ·∂ₓ(U^m V') − U(1−U^a) − λU = H`.
This is exactly the value the Green inversion must reproduce, since
`auxMap = −Kλ ∗ H` (the chemotactic term being integrated by parts into
`Kλ'`). -/
def auxRHS (p : CMParams) (lam : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  p.χ * deriv (auxFlux p u) x - auxReaction p u x - lam * u x

/-! ## Green inversion interface and the L4 bridge

The analytic core is the GREEN IDENTITY: the function `w = auxMap p c λ u`
solves `Lλ w = H`, i.e. `w'' + c w' − λ w = auxRHS`, pointwise.  This is the
genuine analytic statement `Lλ (−Kλ ∗ H) = H` obtained by differentiating the
explicit two-sided-exponential convolution (variation of parameters).  We
carry it as the predicate `GreenIdentity`; everything below is honest algebra
turning it into stationarity.  Discharging `GreenIdentity` from the kernel
representation is the remaining analytic obligation (see report). -/

/-- The Green identity for the auxiliary map at `u`: `auxMap p c λ u` solves
`Lλ w = auxRHS`, i.e. `w'' + c w' − λ w = auxRHS` pointwise. -/
def GreenIdentity (p : CMParams) (c lam : ℝ) (u : ℝ → ℝ) : Prop :=
  ∀ x,
    iteratedDeriv 2 (auxMap p c lam u) x + c * deriv (auxMap p c lam u) x
        - lam * auxMap p c lam u x
      = auxRHS p lam u x

/-- Pointwise expansion of `frozenWaveOperator p c u u` at a configuration `u`,
identifying the chemotactic term with `deriv (auxFlux p u)`.  Pure unfolding —
this is the algebraic skeleton the L4 bridge rides on. -/
theorem frozenWaveOperator_eq_aux (p : CMParams) (c : ℝ) (u : ℝ → ℝ) (x : ℝ) :
    frozenWaveOperator p c u u x =
      iteratedDeriv 2 u x + c * deriv u x
        - p.χ * deriv (auxFlux p u) x + auxReaction p u x := by
  unfold frozenWaveOperator auxFlux auxReaction
  rfl

/-- **L4 — fixed-point ⟹ stationarity bridge.**
If the Green identity holds at `u` (the analytic core) and `u` is a fixed
point of the auxiliary map, then `u` is a stationary profile of the frozen
wave operator.  This is the operator↔ODE bridge feeding the Schauder
construction; the proof is the algebra of substituting `auxMap = u` into the
Green identity and matching with `frozenWaveOperator`. -/
theorem fixedPoint_stationary
    (p : CMParams) (c lam : ℝ) (u : ℝ → ℝ)
    (hgreen : GreenIdentity p c lam u)
    (hfix : auxMap p c lam u = u) :
    ∀ x, frozenWaveOperator p c u u x = 0 := by
  intro x
  have hid := hgreen x
  rw [hfix] at hid
  -- hid : u'' x + c·u' x − lam·u x = χ·∂(auxFlux) x − reaction x − lam·u x
  rw [frozenWaveOperator_eq_aux]
  unfold auxRHS at hid
  linarith [hid]

/-- Conversely, at an auxiliary fixed point, frozen stationarity is exactly the
Green identity written for `auxMap`.  This is only algebraic: it does not produce
stationarity from the fixed-point equation. -/
theorem greenIdentity_of_stationary_fixedPoint
    (p : CMParams) (c lam : ℝ) (u : ℝ → ℝ)
    (hfix : auxMap p c lam u = u)
    (hstat : ∀ x, frozenWaveOperator p c u u x = 0) :
    GreenIdentity p c lam u := by
  intro x
  have hstatx := hstat x
  rw [frozenWaveOperator_eq_aux] at hstatx
  rw [hfix]
  unfold auxRHS at *
  linarith [hstatx]

/-- **L4′ — fixed-point ⟹ paper-form stationarity.**
Under the differentiability hypotheses that hold on the trap set, the
frozen stationarity from L4 transfers to the paper's expanded
`paperWaveOperator` form via the committed pointwise identity
`paperWaveOperator_eq_frozenWaveOperator_at_fixed_point`. -/
theorem fixedPoint_paper_stationary
    (p : CMParams) (c lam : ℝ) (u : ℝ → ℝ)
    (hgreen : GreenIdentity p c lam u)
    (hfix : auxMap p c lam u = u)
    (hU : IsCUnifBdd u) (hU_nonneg : ∀ x, 0 ≤ u x)
    (hU_diff : ∀ x, DifferentiableAt ℝ u x)
    (hV_diff : ∀ x, DifferentiableAt ℝ (deriv (frozenElliptic p u)) x)
    (hU_rpow_diff : ∀ x, DifferentiableAt ℝ (fun y => (u y) ^ p.m) x) :
    ∀ x, paperWaveOperator p c u u x = 0 := by
  intro x
  have hstat := fixedPoint_stationary p c lam u hgreen hfix x
  rw [paperWaveOperator_eq_frozenWaveOperator_at_fixed_point p x hU hU_nonneg
    (hU_diff x) (hV_diff x) (hU_rpow_diff x)]
  exact hstat

section AxiomAudit

#print axioms greenIdentity_of_stationary_fixedPoint

end AxiomAudit

end ShenWork.Paper1
