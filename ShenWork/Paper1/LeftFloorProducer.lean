/-
  Geometric producer for the left-floor maximum principle (Paper 1).

  Closes the remaining brick `hproduce` of
  `strictlyPositiveAtLeft_of_noSmallInteriorMin`:  from a floor violation
  (the failure of `StrictlyPositiveAtLeft U`) it manufactures a SMALL INTERIOR
  local minimum of the perturbed barrier `h = U + ε e^{-κ x}` staying in the
  small-density window `0 < U z ≤ η`, which the maximum principle
  `noSmallInteriorMin` then refutes.

  Mechanism (the dichotomy).  `¬ StrictlyPositiveAtLeft U` gives, for the test
  floor `η/2`, that `U` dips below `η/2` arbitrarily far to the left
  (`∃ᶠ x in atBot, U x < η/2`).  Fix any anchor `A` with `U A > η` and pick a
  violation point `z₀ < A` with `U z₀ < η/2`.  Choosing `ε := (η/2)·e^{κ z₀}`
  makes the barrier at `z₀` exactly `η/2`, so `h z₀ < η < U A ≤ h A`; and since
  `U ≥ 0` while `ε e^{-κ x} → +∞` as `x → -∞`, `h` is coercive at `-∞`.  The
  reusable `exists_interior_min_left` then attains the half-line infimum at an
  interior point `z < A` with `h z ≤ h z₀ < η`, whence `0 < U z ≤ η` (using the
  profile positivity `U_pos`).  That is exactly the interior minimum the maximum
  principle forbids.
-/
import ShenWork.Paper1.NoSmallLeftPocket

namespace ShenWork.Paper1

noncomputable section

open Filter Topology Set

/-- The perturbed barrier `h = U + ε e^{-κ x}` is coercive at `-∞`
(`→ +∞`) whenever `U ≥ 0`, `κ > 0`, `ε > 0`. -/
theorem barrier_tendsto_atBot_atTop
    {U : ℝ → ℝ} {κ ε : ℝ} (hUnonneg : ∀ x, 0 ≤ U x)
    (hκ : 0 < κ) (hε : 0 < ε) :
    Tendsto (fun x => U x + ε * Real.exp (-κ * x)) atBot atTop := by
  have hbar : Tendsto (fun x => ε * Real.exp (-κ * x)) atBot atTop := by
    have hlin : Tendsto (fun x : ℝ => -κ * x) atBot atTop :=
      Filter.Tendsto.const_mul_atBot_of_neg (r := -κ) (by linarith)
        (tendsto_id (α := ℝ) (x := atBot))
    have hexp : Tendsto (fun x : ℝ => Real.exp (-κ * x)) atBot atTop :=
      Real.tendsto_exp_atTop.comp hlin
    exact hexp.const_mul_atTop hε
  refine tendsto_atTop_mono (fun x => ?_) hbar
  have := hUnonneg x; linarith

/-- **Floor-violation extraction.**  The failure of `StrictlyPositiveAtLeft U`
forces `U` to dip below `η/2` arbitrarily far to the left: in particular, below
any anchor `A` there is a violation point `z₀ < A` with `U z₀ < η/2`. -/
theorem exists_left_floor_violation
    {U : ℝ → ℝ} {η : ℝ} (hη : 0 < η)
    (hviol : ¬ StrictlyPositiveAtLeft U) (A : ℝ) :
    ∃ z₀, z₀ < A ∧ U z₀ < η / 2 := by
  have hnot : ¬ ∀ᶠ x in atBot, η / 2 ≤ U x := by
    intro hev; exact hviol ⟨η / 2, by linarith, hev⟩
  rw [Filter.not_eventually] at hnot
  simp only [not_le] at hnot
  rw [frequently_atBot'] at hnot
  obtain ⟨z₀, hz₀A, hz₀⟩ := hnot A
  exact ⟨z₀, hz₀A, hz₀⟩

/-- **The geometric producer (`hproduce`).**  From a floor violation
(`¬ StrictlyPositiveAtLeft U`), an anchor `A` with `U A > η`, continuity of `U`
and nonnegativity, build a small interior local minimum of the perturbed barrier
`U + ε e^{-κ x}` whose value keeps `U` inside the small-density window
`0 < U z ≤ η`.  Discharges the remaining brick of
`strictlyPositiveAtLeft_of_noSmallInteriorMin`. -/
theorem produce_small_interior_min
    {U : ℝ → ℝ} {η b0 A : ℝ}
    (hUcont : Continuous U) (hUnonneg : ∀ x, 0 ≤ U x) (hUpos : ∀ x, 0 < U x)
    (hη : 0 < η) (hb0 : 0 < b0) (hanchor : η < U A)
    (hviol : ¬ StrictlyPositiveAtLeft U) :
    ∃ κ ε z : ℝ, 0 < κ ∧ κ < b0 ∧ 0 < ε ∧
      0 < U z ∧ U z ≤ η ∧
      IsLocalMin (fun x => U x + ε * Real.exp (-κ * x)) z := by
  -- choose the decay rate strictly inside the drift floor
  set κ : ℝ := b0 / 2 with hκdef
  have hκpos : 0 < κ := by positivity
  have hκb0 : κ < b0 := by rw [hκdef]; linarith
  -- a violation point strictly left of the anchor
  obtain ⟨z₀, hz₀A, hz₀⟩ := exists_left_floor_violation hη hviol A
  -- choose ε so that the barrier at z₀ is exactly η/2
  set ε : ℝ := (η / 2) * Real.exp (κ * z₀) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  set bar : ℝ → ℝ := fun x => ε * Real.exp (-κ * x) with hbardef
  set h : ℝ → ℝ := fun x => U x + bar x with hhdef
  have hbarcont : Continuous bar :=
    continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))
  have hhcont : Continuous h := hUcont.add hbarcont
  have hcoer : Tendsto h atBot atTop :=
    barrier_tendsto_atBot_atTop hUnonneg hκpos hεpos
  -- barrier value at z₀ is exactly η/2
  have hbar_z₀ : bar z₀ = η / 2 := by
    simp only [hbardef, hεdef]
    rw [mul_assoc, ← Real.exp_add]
    have : κ * z₀ + -κ * z₀ = 0 := by ring
    rw [this, Real.exp_zero, mul_one]
  have hbar_pos : ∀ x, 0 < bar x := fun x => by
    simp only [hbardef]; positivity
  -- h z₀ < η  (floor violation + tuned barrier)
  have hhz₀ : h z₀ < η := by
    have hval : h z₀ = U z₀ + bar z₀ := rfl
    rw [hval, hbar_z₀]; linarith
  -- h A > η  (anchor dominates)
  have hhA : η < h A := by
    have hval : h A = U A + bar A := rfl
    have hbarA : 0 < bar A := hbar_pos A
    rw [hval]; linarith
  have hz₀A_le : z₀ ≤ A := le_of_lt hz₀A
  have hlt : h z₀ < h A := lt_trans hhz₀ hhA
  -- interior minimiser of the half-line
  obtain ⟨z, hzA, hzmin, hzglob⟩ :=
    exists_interior_min_left hhcont hcoer hz₀A_le hlt
  -- window membership of U at the minimiser
  have hUz_pos : 0 < U z := hUpos z
  have hUz_le : U z ≤ η := by
    have hle : h z ≤ h z₀ := hzglob z₀ hz₀A_le
    have hbz : 0 < bar z := hbar_pos z
    have : U z + bar z ≤ η := le_of_lt (lt_of_le_of_lt hle hhz₀)
    linarith
  exact ⟨κ, ε, z, hκpos, hκb0, hεpos, hUz_pos, hUz_le, hzmin⟩

/-- **Left floor, fully discharged.**  Combining the geometric producer
`produce_small_interior_min` with the maximum-principle reduction
`strictlyPositiveAtLeft_of_noSmallInteriorMin`, a positive `C²` profile that is
small-density coercive and exceeds `η` at some anchor `A` stays uniformly
positive at the left end.  No remaining geometric brick. -/
theorem strictlyPositiveAtLeft_of_coercive_anchor
    {U B Q : ℝ → ℝ} {η b0 q0 A : ℝ}
    (hUcont : Continuous U)
    (hUdiff : Differentiable ℝ U)
    (hUdiff2 : Differentiable ℝ (deriv U))
    (hUpos : ∀ x, 0 < U x)
    (hcoer : SmallDensityCoercive U B Q η b0 q0)
    (hanchor : η < U A) :
    StrictlyPositiveAtLeft U := by
  have hUnonneg : ∀ x, 0 ≤ U x := fun x => (hUpos x).le
  refine strictlyPositiveAtLeft_of_noSmallInteriorMin hUdiff hUdiff2 hcoer ?_
  intro hviol
  exact produce_small_interior_min hUcont hUnonneg hUpos
    hcoer.hη hcoer.hb0 hanchor hviol

section LeftFloorProducerAxiomAudit
#print axioms barrier_tendsto_atBot_atTop
#print axioms exists_left_floor_violation
#print axioms produce_small_interior_min
#print axioms strictlyPositiveAtLeft_of_coercive_anchor
end LeftFloorProducerAxiomAudit

end

end ShenWork.Paper1


