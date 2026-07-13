import ShenWork.Paper1.WavePaperRotheProducer

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- The discriminant of the whole-line Green resolvent diverges as the
implicit-step parameter tends to infinity. -/
theorem greenDelta_tendsto_atTop (c : ℝ) :
    Tendsto (fun lam : ℝ => greenDelta c lam) atTop atTop := by
  unfold greenDelta
  refine Real.tendsto_sqrt_atTop.comp ?_
  apply Filter.tendsto_atTop_add_const_left
  exact Filter.tendsto_atTop_atTop.mpr fun b =>
    ⟨b / 4, fun a ha => by linarith⟩

/-- The positive characteristic root diverges with the resolvent parameter. -/
theorem greenRootPlus_tendsto_atTop (c : ℝ) :
    Tendsto (fun lam : ℝ => greenRootPlus c lam) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  rcases (Filter.tendsto_atTop_atTop.mp (greenDelta_tendsto_atTop c))
      (2 * b + c) with ⟨a, ha⟩
  exact ⟨a, fun lam hlam => by
    have := ha lam hlam
    unfold greenRootPlus
    linarith⟩

/-- The magnitude of the negative characteristic root also diverges. -/
theorem neg_greenRootMinus_tendsto_atTop (c : ℝ) :
    Tendsto (fun lam : ℝ => -greenRootMinus c lam) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  rcases (Filter.tendsto_atTop_atTop.mp (greenDelta_tendsto_atTop c))
      (2 * b - c) with ⟨a, ha⟩
  exact ⟨a, fun lam hlam => by
    have := ha lam hlam
    unfold greenRootMinus
    linarith⟩

private theorem root_ratio_tendsto_one
    {r : ℝ → ℝ} (hr : Tendsto r atTop atTop) (κ : ℝ) :
    Tendsto (fun lam => r lam * (r lam - κ)⁻¹) atTop (nhds 1) := by
  have hden : Tendsto (fun lam => r lam - κ) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    rcases (Filter.tendsto_atTop_atTop.mp hr) (b + κ) with ⟨a, ha⟩
    exact ⟨a, fun lam hlam => by linarith [ha lam hlam]⟩
  have hinv : Tendsto (fun lam => (r lam - κ)⁻¹) atTop (nhds 0) :=
    (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp hden
  have hsum : Tendsto (fun lam => 1 + κ * (r lam - κ)⁻¹)
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add (hinv.const_mul κ)
  have hpos : ∀ᶠ lam in atTop, 0 < r lam - κ := by
    rcases (Filter.tendsto_atTop_atTop.mp hden) 1 with ⟨a, ha⟩
    exact eventually_atTop.mpr ⟨a, fun lam hlam =>
      lt_of_lt_of_le zero_lt_one (ha lam hlam)⟩
  refine hsum.congr' ?_
  filter_upwards [hpos] with lam hlam
  field_simp [ne_of_gt hlam]
  <;> ring

/-- The exponentially weighted derivative-kernel mass used by the local
source box tends to zero for large implicit-step parameter. -/
theorem greenWeightedMass1_tendsto_zero (c κ : ℝ) :
    Tendsto (fun lam : ℝ => greenWeightedMass1 c lam κ) atTop (nhds 0) := by
  have hδinv : Tendsto (fun lam : ℝ => (greenDelta c lam)⁻¹) atTop (nhds 0) :=
    (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp (greenDelta_tendsto_atTop c)
  have hp : Tendsto
      (fun lam : ℝ => greenRootPlus c lam * (greenRootPlus c lam - κ)⁻¹)
      atTop (nhds 1) :=
    root_ratio_tendsto_one (greenRootPlus_tendsto_atTop c) κ
  have hm : Tendsto
      (fun lam : ℝ => (-greenRootMinus c lam) *
        ((-greenRootMinus c lam) - κ)⁻¹) atTop (nhds 1) :=
    root_ratio_tendsto_one (neg_greenRootMinus_tendsto_atTop c) κ
  have hprod := hδinv.mul (hp.add hm)
  simpa [greenWeightedMass1, sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc] using hprod

section AxiomAudit

#print axioms greenDelta_tendsto_atTop
#print axioms greenRootPlus_tendsto_atTop
#print axioms neg_greenRootMinus_tendsto_atTop
#print axioms greenWeightedMass1_tendsto_zero

end AxiomAudit

end ShenWork.Paper1
