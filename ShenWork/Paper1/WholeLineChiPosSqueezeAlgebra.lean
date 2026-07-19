import ShenWork.Paper3.IntervalDomainMRectangleGlobal

/-!
# Scalar contraction algebra for the positive-sensitivity rectangle squeeze

The whole-line χ>0 left-equilibrium argument alternates floor and ceiling
barrier steps whose targets satisfy the coupled equilibrium inequalities

  1 - ℓ'^α ≤ χ ℓ'^(m-1) (M^γ - ℓ'^γ) + δ,
  M'^α - 1 ≤ χ M'^(m-1) (M'^γ - ℓ'^γ) + δ.

At the critical exponent α = m + γ - 1 the straddling-gap absorption
`rpow_mul_gap_le_gap_add` turns their sum into the affine recurrence

  M'^α - ℓ'^α ≤ 2χ (M^α - ℓ^α) + 2δ,

geometric with ratio 2χ < 1 on the paper's Proposition 1.2(2) regime
χ < 1/2.  This file proves the recurrence step, its iterate bound, and the
endgame conversion |u - 1| ≤ M^α - ℓ^α.  Everything is stated for raw real
parameters: no PDE, no CMParams, no resolver.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- Floor-side absorption: the small-endpoint prefactor is dominated by the
large-endpoint one, then absorbed into the raised-exponent gap. -/
theorem chiPos_floor_prefactor_gap_le
    {L U s a : ℝ}
    (hL : 0 < L) (hL1 : L ≤ 1) (h1U : 1 ≤ U)
    (hs : 0 ≤ s) (ha : 0 ≤ a) :
    L ^ s * (U ^ a - L ^ a) ≤ U ^ (a + s) - L ^ (a + s) := by
  have hLU : L ≤ U := hL1.trans h1U
  have hgap : 0 ≤ U ^ a - L ^ a :=
    sub_nonneg.mpr (Real.rpow_le_rpow hL.le hLU ha)
  have hpre : L ^ s ≤ U ^ s := Real.rpow_le_rpow hL.le hLU hs
  calc
    L ^ s * (U ^ a - L ^ a) ≤ U ^ s * (U ^ a - L ^ a) :=
      mul_le_mul_of_nonneg_right hpre hgap
    _ ≤ U ^ (a + s) - L ^ (a + s) :=
      ShenWork.Paper3.rpow_mul_gap_le_gap_add hL hL1 h1U hs ha

/-- One full alternating step of the χ>0 rectangle squeeze contracts the
`α`-power gap by the factor `2χ`, up to twice the step defect.  `ℓ'`/`M'` are
the new floor/ceiling produced from the pair `(ℓ, M)`; the two hypotheses are
the barrier-target inequalities delivered by the floor and ceiling barriers. -/
theorem chiPos_squeeze_gap_step
    {m γ α χ ℓ ℓ' M M' δ : ℝ}
    (hm : 1 ≤ m) (hγ : 1 ≤ γ) (halpha : α = m + γ - 1)
    (hχ : 0 ≤ χ)
    (hℓ : 0 < ℓ) (hℓℓ' : ℓ ≤ ℓ') (hℓ'1 : ℓ' ≤ 1)
    (h1M' : 1 ≤ M') (hM'M : M' ≤ M)
    (hfloor : 1 - ℓ' ^ α ≤ χ * (ℓ' ^ (m - 1) * (M ^ γ - ℓ' ^ γ)) + δ)
    (hceil : M' ^ α - 1 ≤ χ * (M' ^ (m - 1) * (M' ^ γ - ℓ' ^ γ)) + δ) :
    M' ^ α - ℓ' ^ α ≤ 2 * χ * (M ^ α - ℓ ^ α) + 2 * δ := by
  have hℓ' : 0 < ℓ' := hℓ.trans_le hℓℓ'
  have h1M : (1 : ℝ) ≤ M := h1M'.trans hM'M
  have hs : (0 : ℝ) ≤ m - 1 := by linarith
  have ha : (0 : ℝ) ≤ γ := by linarith
  have hexp : γ + (m - 1) = α := by rw [halpha]; ring
  -- floor-side absorption against the OLD ceiling M
  have hbound1 : ℓ' ^ (m - 1) * (M ^ γ - ℓ' ^ γ) ≤ M ^ α - ℓ' ^ α := by
    have := chiPos_floor_prefactor_gap_le hℓ' hℓ'1 h1M hs ha
    rwa [hexp] at this
  -- ceiling-side absorption at the NEW ceiling M', then monotone in M' ≤ M
  have hbound2 : M' ^ (m - 1) * (M' ^ γ - ℓ' ^ γ) ≤ M ^ α - ℓ' ^ α := by
    have habs := ShenWork.Paper3.rpow_mul_gap_le_gap_add hℓ' hℓ'1 h1M' hs ha
    rw [hexp] at habs
    have hmono : M' ^ α ≤ M ^ α :=
      Real.rpow_le_rpow (by linarith) hM'M (by rw [halpha]; linarith)
    linarith
  -- old floor dominates through monotonicity
  have hfloorMono : ℓ ^ α ≤ ℓ' ^ α :=
    Real.rpow_le_rpow hℓ.le hℓℓ' (by rw [halpha]; linarith)
  have hgapMono : M ^ α - ℓ' ^ α ≤ M ^ α - ℓ ^ α := by linarith
  have hχb1 : χ * (ℓ' ^ (m - 1) * (M ^ γ - ℓ' ^ γ)) ≤
      χ * (M ^ α - ℓ ^ α) :=
    mul_le_mul_of_nonneg_left (hbound1.trans hgapMono) hχ
  have hχb2 : χ * (M' ^ (m - 1) * (M' ^ γ - ℓ' ^ γ)) ≤
      χ * (M ^ α - ℓ ^ α) :=
    mul_le_mul_of_nonneg_left (hbound2.trans hgapMono) hχ
  nlinarith [hfloor, hceil, hχb1, hχb2]

/-- Affine recurrence iterate: a sequence contracting by ratio `r < 1` with
additive defect `c` enters the `c/(1-r)`-neighborhood geometrically. -/
theorem affine_recurrence_iterate_le
    {g : ℕ → ℝ} {r c : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hc : 0 ≤ c)
    (hstep : ∀ k, g (k + 1) ≤ r * g k + c) (n : ℕ) :
    g n ≤ r ^ n * g 0 + c / (1 - r) := by
  have h1r : 0 < 1 - r := by linarith
  induction n with
  | zero =>
    have : 0 ≤ c / (1 - r) := div_nonneg hc h1r.le
    simpa using by linarith
  | succ k ih =>
    have hmul : r * g k ≤ r * (r ^ k * g 0 + c / (1 - r)) :=
      mul_le_mul_of_nonneg_left ih hr0
    have hkey : r * (c / (1 - r)) + c = c / (1 - r) := by
      field_simp
      ring
    calc
      g (k + 1) ≤ r * g k + c := hstep k
      _ ≤ r * (r ^ k * g 0 + c / (1 - r)) + c := by linarith
      _ = r ^ (k + 1) * g 0 + (r * (c / (1 - r)) + c) := by ring
      _ = r ^ (k + 1) * g 0 + c / (1 - r) := by rw [hkey]

/-- Endgame: a value squeezed between the rectangle endpoints is within the
`α`-power gap of the equilibrium `1`. -/
theorem abs_sub_one_le_rpow_gap
    {α ℓ M u : ℝ}
    (hα : 1 ≤ α) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (h1M : 1 ≤ M)
    (hℓu : ℓ ≤ u) (huM : u ≤ M) :
    |u - 1| ≤ M ^ α - ℓ ^ α := by
  have hMα : M ≤ M ^ α := by
    have := Real.rpow_le_rpow_of_exponent_le h1M hα
    simpa using this
  have hℓα : ℓ ^ α ≤ ℓ := by
    have := Real.rpow_le_rpow_of_exponent_ge hℓ hℓ1 hα
    simpa using this
  have h1Mα : (1 : ℝ) ≤ M ^ α := by
    calc (1 : ℝ) ≤ M := h1M
    _ ≤ M ^ α := hMα
  have hℓα1 : ℓ ^ α ≤ 1 := hℓα.trans hℓ1
  rw [abs_le]
  constructor <;> nlinarith

section AxiomAudit

#print axioms chiPos_floor_prefactor_gap_le
#print axioms chiPos_squeeze_gap_step
#print axioms affine_recurrence_iterate_le
#print axioms abs_sub_one_le_rpow_gap

end AxiomAudit

end ShenWork.Paper1
