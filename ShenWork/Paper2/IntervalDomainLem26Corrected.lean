import ShenWork.Paper2.IntervalDomainLem26ConcreteTerminal

/-!
# Lemma 2.6, corrected statement

The abstract `Lemma_2_6` is routed through `MoserDissipationDropBefore`, which
is UNSOUND: its premise quantifies over every quadruple `(A,B,K,L)` making the
energy inequality true, so a spatially constant decaying profile with
`A = B = K = L = 0` satisfies the premise while violating the conclusion
`0 ≤ (1/p) Y_p' + B Y_p`.  No PDE can supply it, and the pointwise route it
feeds is circular besides: extracting the gradient bound from the energy
inequality needs a lower bound on `Y_p'`, which needs the very upper bound on
the dissipation being derived.

This file records the corrected replacement interface and proves the
counterexample, so the defect is machine-checked rather than prose.  The
replacement drops the pointwise drop entirely and asks instead for the
TIME-INTEGRATED form, which is what an energy inequality actually gives after
integrating on `[t₁, t₂]`.
-/

open Set

noncomputable section

namespace ShenWork.Paper2

/-- The corrected, time-integrated dissipation interface: integrating the energy
inequality on a window is exactly what the FTC gives, with no pointwise sign
assertion about `Y_p'`. -/
def MoserIntegratedDissipationBefore
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ) (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∃ C, 0 ≤ C ∧
    ∀ t₁ ∈ Ioo (0 : ℝ) T, ∀ t₂ ∈ Ioo (0 : ℝ) T, t₁ ≤ t₂ →
      D.integral (fun x => (u t₂ x) ^ p) ≤
        D.integral (fun x => (u t₁ x) ^ p) + C * (t₂ - t₁)

/-- The unsound pointwise interface, in the abstract shape consumed by the
committed chain. -/
def PointwiseDropShape (Y G : ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ A B K L : ℝ,
    (∀ t ∈ Ioo (0 : ℝ) T, Y t + A * G t + B * (Y t) ≤ K * (Y t) + L) →
    ∀ t ∈ Ioo (0 : ℝ) T, 0 ≤ Y t + B * (Y t)

/-- The pointwise drop shape is unsatisfiable for a strictly decreasing
moment with vanishing dissipation: taking `A = B = K = L = 0` makes the
antecedent true (the derivative is negative) while the conclusion demands the
derivative be nonnegative.  This is the exact obstruction in
`MoserDissipationDropBefore`. -/
theorem pointwiseDropShape_false_of_negative
    {Y G : ℝ → ℝ} {T t : ℝ}
    (hT : 0 < T) (ht : t ∈ Ioo (0 : ℝ) T)
    (hY : ∀ s ∈ Ioo (0 : ℝ) T, Y s < 0)
    (hG : ∀ s ∈ Ioo (0 : ℝ) T, G s = 0) :
    ¬ PointwiseDropShape Y G T := by
  intro h
  have hprem : ∀ s ∈ Ioo (0 : ℝ) T,
      Y s + 0 * G s + 0 * (Y s) ≤ 0 * (Y s) + 0 := by
    intro s hs
    simpa using (hY s hs).le
  have hconc := h 0 0 0 0 hprem t ht
  have := hY t ht
  simp at hconc
  linarith

/-- On the corrected interface the moment growth over a window is linear in the
window length — the statement an energy inequality really supports. -/
theorem moserIntegratedDissipation_growth
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T p0 p : ℝ}
    (h : MoserIntegratedDissipationBefore D u T p0) (hp : p0 ≤ p) :
    ∃ C, 0 ≤ C ∧ ∀ t₁ ∈ Ioo (0 : ℝ) T, ∀ t₂ ∈ Ioo (0 : ℝ) T, t₁ ≤ t₂ →
      D.integral (fun x => (u t₂ x) ^ p) -
        D.integral (fun x => (u t₁ x) ^ p) ≤ C * (t₂ - t₁) := by
  obtain ⟨C, hC0, hC⟩ := h p hp
  refine ⟨C, hC0, ?_⟩
  intro t₁ h₁ t₂ h₂ hle
  have := hC t₁ h₁ t₂ h₂ hle
  linarith

section AxiomAudit

#print axioms pointwiseDropShape_false_of_negative
#print axioms moserIntegratedDissipation_growth

end AxiomAudit

end ShenWork.Paper2
