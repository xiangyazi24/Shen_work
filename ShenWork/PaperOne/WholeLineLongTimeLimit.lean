import ShenWork.PaperOne.WholeLineTimeMonotonicity
import ShenWork.PaperOne.WholeLineExponentialBarriers
import ShenWork.Paper1.Statements
import Mathlib.Topology.Order.MonotoneConvergence

open Filter Set
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/-!
Long-time pointwise limit for a whole-line auxiliary orbit.

This file isolates the order-theoretic part of the argument: if every spatial
point sees an antitone-in-time real trajectory and the trajectory is bounded
below by the lower barrier, then it converges to its indexed infimum.  Spatial
regularity of the limit is kept as an explicit hypothesis in the final trap
membership theorem.
-/

/-- Pointwise long-time profile, defined as the infimum of the time orbit. -/
def wholeLineLongTimeLimit (w : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ⨅ t : ℝ, w t x

/-- The lower barrier gives a pointwise lower bound for each time orbit. -/
theorem wholeLine_longTime_bddBelow
    {κ κt D : ℝ} {w : ℝ → ℝ → ℝ}
    (hlower : ∀ t x, lowerBarrier κ κt D x ≤ w t x) (x : ℝ) :
    BddBelow (range fun t : ℝ => w t x) := by
  refine ⟨lowerBarrier κ κt D x, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact hlower t x

/-- Monotone convergence of the whole-line time orbit to its infimum. -/
theorem wholeLine_longTime_limit_tendsto
    {κ κt D : ℝ} {w : ℝ → ℝ → ℝ}
    (htime : ∀ x, Antitone fun t : ℝ => w t x)
    (hlower : ∀ t x, lowerBarrier κ κt D x ≤ w t x) (x : ℝ) :
    Tendsto (fun t : ℝ => w t x) atTop
      (𝓝 (wholeLineLongTimeLimit w x)) := by
  simpa [wholeLineLongTimeLimit] using
    tendsto_atTop_ciInf (htime x)
      (wholeLine_longTime_bddBelow (κ := κ) (κt := κt) (D := D)
        (w := w) hlower x)

/-- Existence of the pointwise long-time profile as the infimum limit. -/
theorem wholeLine_longTime_limit_exists
    {κ κt D : ℝ} {w : ℝ → ℝ → ℝ}
    (htime : ∀ x, Antitone fun t : ℝ => w t x)
    (hlower : ∀ t x, lowerBarrier κ κt D x ≤ w t x) :
    ∃ Uinf : ℝ → ℝ,
      Uinf = wholeLineLongTimeLimit w ∧
        ∀ x, Tendsto (fun t : ℝ => w t x) atTop (𝓝 (Uinf x)) := by
  refine ⟨wholeLineLongTimeLimit w, rfl, ?_⟩
  exact wholeLine_longTime_limit_tendsto htime hlower

/-- The lower barrier passes to the long-time infimum. -/
theorem wholeLine_longTime_limit_lowerBarrier
    {κ κt D : ℝ} {w : ℝ → ℝ → ℝ}
    (hlower : ∀ t x, lowerBarrier κ κt D x ≤ w t x) (x : ℝ) :
    lowerBarrier κ κt D x ≤ wholeLineLongTimeLimit w x := by
  simpa [wholeLineLongTimeLimit] using
    (le_ciInf fun t : ℝ => hlower t x)

/-- A uniform upper barrier passes to the long-time infimum. -/
theorem wholeLine_longTime_limit_upperBarrier
    {κ κt D : ℝ} {w : ℝ → ℝ → ℝ}
    (hlower : ∀ t x, lowerBarrier κ κt D x ≤ w t x)
    (hupper : ∀ t x, w t x ≤ upperBarrier κ x) (x : ℝ) :
    wholeLineLongTimeLimit w x ≤ upperBarrier κ x := by
  simpa [wholeLineLongTimeLimit] using
    (ciInf_le_of_le
      (wholeLine_longTime_bddBelow (κ := κ) (κt := κt) (D := D)
        (w := w) hlower x)
      (0 : ℝ) (hupper 0 x))

/-- The long-time profile is squeezed between the lower and upper barriers. -/
theorem wholeLine_longTime_limit_barrier_bounds
    {κ κt D : ℝ} {w : ℝ → ℝ → ℝ}
    (hlower : ∀ t x, lowerBarrier κ κt D x ≤ w t x)
    (hupper : ∀ t x, w t x ≤ upperBarrier κ x) :
    ∀ x,
      lowerBarrier κ κt D x ≤ wholeLineLongTimeLimit w x ∧
        wholeLineLongTimeLimit w x ≤ upperBarrier κ x := by
  intro x
  exact
    ⟨wholeLine_longTime_limit_lowerBarrier (κ := κ) (κt := κt)
        (D := D) (w := w) hlower x,
      wholeLine_longTime_limit_upperBarrier (κ := κ) (κt := κt)
        (D := D) (w := w) hlower hupper x⟩

/-- Spatial antitonicity passes to the long-time infimum. -/
theorem wholeLine_longTime_limit_antitone
    {κ κt D : ℝ} {w : ℝ → ℝ → ℝ}
    (hlower : ∀ t x, lowerBarrier κ κt D x ≤ w t x)
    (hspace : ∀ t, Antitone (w t)) :
    Antitone (wholeLineLongTimeLimit w) := by
  intro x y hxy
  simpa [wholeLineLongTimeLimit] using
    (ciInf_mono
      (wholeLine_longTime_bddBelow (κ := κ) (κt := κt) (D := D)
        (w := w) hlower y)
      (fun t : ℝ => hspace t hxy))

/-- The Paper 1 upper barrier with height `1` is the PaperOne upper barrier. -/
theorem wholeLine_paper1_upperBarrier_one_eq (κ x : ℝ) :
    ShenWork.Paper1.upperBarrier κ 1 x = upperBarrier κ x := by
  rfl

/--
Membership of the long-time profile in the old monotone wave trap with
height `1`.  Continuity of the pointwise infimum is the carried parabolic
regularity input.
-/
theorem wholeLine_longTime_limit_mem_InMonotoneWaveTrapSet
    {κ κt D : ℝ} {w : ℝ → ℝ → ℝ}
    (hlower : ∀ t x, lowerBarrier κ κt D x ≤ w t x)
    (hupper : ∀ t x, w t x ≤ upperBarrier κ x)
    (hspace : ∀ t, Antitone (w t))
    (hcont : Continuous (wholeLineLongTimeLimit w)) :
    ShenWork.Paper1.InMonotoneWaveTrapSet κ 1 (wholeLineLongTimeLimit w) := by
  have hlowerU :
      ∀ x, lowerBarrier κ κt D x ≤ wholeLineLongTimeLimit w x :=
    wholeLine_longTime_limit_lowerBarrier (κ := κ) (κt := κt) (D := D)
      (w := w) hlower
  have hupperU :
      ∀ x, wholeLineLongTimeLimit w x ≤ upperBarrier κ x :=
    wholeLine_longTime_limit_upperBarrier (κ := κ) (κt := κt) (D := D)
      (w := w) hlower hupper
  have hnonneg : ∀ x, 0 ≤ wholeLineLongTimeLimit w x := by
    intro x
    exact le_trans (lowerBarrier_nonneg κ κt D x) (hlowerU x)
  have hlePaperUpper :
      ∀ x, wholeLineLongTimeLimit w x ≤
        ShenWork.Paper1.upperBarrier κ 1 x := by
    intro x
    rw [wholeLine_paper1_upperBarrier_one_eq]
    exact hupperU x
  have hcunif : IsCUnifBdd (wholeLineLongTimeLimit w) := by
    refine ⟨hcont, ⟨1, ?_⟩⟩
    intro x
    rw [abs_of_nonneg (hnonneg x)]
    exact le_trans (hupperU x) (upperBarrier_le_one κ x)
  exact
    ⟨⟨hcunif, fun x => ⟨hnonneg x, hlePaperUpper x⟩⟩,
      wholeLine_longTime_limit_antitone (κ := κ) (κt := κt)
        (D := D) (w := w) hlower hspace⟩

#print axioms wholeLineLongTimeLimit
#print axioms wholeLine_longTime_bddBelow
#print axioms wholeLine_longTime_limit_tendsto
#print axioms wholeLine_longTime_limit_exists
#print axioms wholeLine_longTime_limit_lowerBarrier
#print axioms wholeLine_longTime_limit_upperBarrier
#print axioms wholeLine_longTime_limit_barrier_bounds
#print axioms wholeLine_longTime_limit_antitone
#print axioms wholeLine_paper1_upperBarrier_one_eq
#print axioms wholeLine_longTime_limit_mem_InMonotoneWaveTrapSet

end ShenWork.PaperOne
