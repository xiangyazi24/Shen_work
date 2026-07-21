import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.Normed.Order.Lattice

/-!
# Sup-norm control of the spatial infimum / supremum

A pointwise `δ`-closeness of two bounded families forces their infima (and
suprema) to be `δ`-close:

`(∀ x, |f x − g x| ≤ δ) → |(⨅ x, f x) − (⨅ x, g x)| ≤ δ`.

This is the elementary bridge used by the `hstart` initial-confinement clause of
`parabolic_lower_barrier_direct_of_initial_interval`: the BUC semigroup is
strongly continuous, so `u(t,·) → u₀` in sup-norm as `t ↓ 0`, and this lemma
propagates that to `⨅_z u(t,z) → ⨅_z u₀(z)`, hence the spatial infimum is
right-continuous at `t = 0`.  It is completely independent of the PDE — pure
order/analysis — so it is proved and banked ahead of the design questions that
choose how the infimum is realized.
-/

noncomputable section

namespace ShenWork.Paper1

open Set

/-- **Sup-norm controls the infimum.**  If `f` and `g` are bounded below and
`|f x − g x| ≤ δ` for every `x`, then `|⨅ f − ⨅ g| ≤ δ`. -/
theorem ciInf_dist_le {ι : Type*} [Nonempty ι] {f g : ι → ℝ} {δ : ℝ}
    (hf : BddBelow (Set.range f)) (hg : BddBelow (Set.range g))
    (h : ∀ x, |f x - g x| ≤ δ) :
    |(⨅ x, f x) - (⨅ x, g x)| ≤ δ := by
  -- pointwise: f x ≤ g x + δ and g x ≤ f x + δ
  have hfg : ∀ x, f x ≤ g x + δ := by
    intro x; have := (abs_le.mp (h x)).2; linarith
  have hgf : ∀ x, g x ≤ f x + δ := by
    intro x
    have := (abs_le.mp (h x)).1; linarith
  -- ⨅ f ≤ ⨅ g + δ
  have h1 : (⨅ x, f x) ≤ (⨅ x, g x) + δ := by
    have hbound : ∀ x, (⨅ x, f x) - δ ≤ g x := by
      intro x
      have hle : (⨅ x, f x) ≤ f x := ciInf_le hf x
      have := hfg x
      linarith
    have := le_ciInf hbound
    linarith
  -- ⨅ g ≤ ⨅ f + δ
  have h2 : (⨅ x, g x) ≤ (⨅ x, f x) + δ := by
    have hbound : ∀ x, (⨅ x, g x) - δ ≤ f x := by
      intro x
      have hle : (⨅ x, g x) ≤ g x := ciInf_le hg x
      have := hgf x
      linarith
    have := le_ciInf hbound
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- **Sup-norm controls the supremum** (mirror form). -/
theorem ciSup_dist_le {ι : Type*} [Nonempty ι] {f g : ι → ℝ} {δ : ℝ}
    (hf : BddAbove (Set.range f)) (hg : BddAbove (Set.range g))
    (h : ∀ x, |f x - g x| ≤ δ) :
    |(⨆ x, f x) - (⨆ x, g x)| ≤ δ := by
  have hfg : ∀ x, f x ≤ g x + δ := by
    intro x; have := (abs_le.mp (h x)).2; linarith
  have hgf : ∀ x, g x ≤ f x + δ := by
    intro x; have := (abs_le.mp (h x)).1; linarith
  have h1 : (⨆ x, f x) ≤ (⨆ x, g x) + δ := by
    have hbound : ∀ x, f x ≤ (⨆ x, g x) + δ := by
      intro x
      have hle : g x ≤ (⨆ x, g x) := le_ciSup hg x
      have := hfg x
      linarith
    have := ciSup_le hbound
    linarith
  have h2 : (⨆ x, g x) ≤ (⨆ x, f x) + δ := by
    have hbound : ∀ x, g x ≤ (⨆ x, f x) + δ := by
      intro x
      have hle : f x ≤ (⨆ x, f x) := le_ciSup hf x
      have := hgf x
      linarith
    have := ciSup_le hbound
    linarith
  rw [abs_le]
  constructor <;> linarith

section AxiomAudit

#print axioms ciInf_dist_le
#print axioms ciSup_dist_le

end AxiomAudit

end ShenWork.Paper1
