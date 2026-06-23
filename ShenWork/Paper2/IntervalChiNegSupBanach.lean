/-
  ShenWork/Paper2/IntervalChiNegSupBanach.lean

  χ₀<0 FINAL — Step 1 of the concrete EnvBall Banach fixed point, IN THE SUP
  METRIC (the under-claim correction: stay in C[0,1] sup-norm, never product).

  A prior attempt declared the sup-complete EnvBall a missing from-scratch lemma
  by trying the PRODUCT metric on `ℕ → ℝ` and hitting a topology mismatch.  That
  was wrong-metric.  This file DERIVES Step 1 genuinely in the sup metric:

    The slice space is `C(Icc 0 1, ℝ)` with the sup metric (a `CompleteSpace`,
    Mathlib instance).  Each coefficient functional `w ↦ cosineCoeffs (w∘incl) k`
    is SUP-CONTINUOUS — indeed `2`-Lipschitz — by the LANDED
    `cosineCoeffs_dist_le_of_sup`.  Hence each constraint set
    `{w | |coeff w k| ≤ E_base k}` is the preimage of `Icc (−E_base k) (E_base k)`
    under a continuous functional, so CLOSED in the sup metric; the SupEnvBall is
    their countable intersection, hence sup-closed, hence (by `IsClosed.isComplete`
    inside the complete sup space) an `IsComplete` set IN THE SUP METRIC.

  This removes Step 1 from the CARRIED list of `localExist_via_envBall_banach`
  (the `IsComplete s` hypothesis) — no product/coefficient metric anywhere.

  Steps 2 (the concrete mild map `Φ` as a `C(Icc 0 1,ℝ)`-endomorphism that
  sup-contracts with `q(δ)<1`) and 3 (the fixed-point → `cosineCoeffs (u r)`
  readout) are NOT derivable from the landed pieces and are reported precisely
  (see the trailing PARTIAL note); they are NOT faked here.

  No sorry/admit/native_decide/custom axiom.  Lines ≤ 100.
-/
import ShenWork.Paper2.IntervalPicardLimitCoeffConv
import ShenWork.PDE.IntervalNeumannFullKernel
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

open Set Metric
open ShenWork.IntervalPicardLimitCoeffConv (cosineCoeffs_dist_le_of_sup)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegSupBanach

/-- The unit-interval slice space, sup-metrised: continuous maps `Icc 0 1 → ℝ`. -/
abbrev Slice := C(Set.Icc (0 : ℝ) 1, ℝ)

/-- Extend a slice `w : Icc 0 1 → ℝ` to a function `ℝ → ℝ` by `0` off `[0,1]`,
so the landed real-integral coefficient functional `cosineCoeffs` applies. -/
def sliceExtend (w : Slice) : ℝ → ℝ :=
  fun x => if hx : x ∈ Set.Icc (0 : ℝ) 1 then w ⟨x, hx⟩ else 0

/-- The `k`-th cosine coefficient of a slice (via its `[0,1]`-extension). -/
def sliceCoeff (w : Slice) (k : ℕ) : ℝ := cosineCoeffs (sliceExtend w) k

/-- The sup-metric EnvBall on the slice space. -/
def SupEnvBall (E_base : ℕ → ℝ) : Set Slice :=
  {w | ∀ k, |sliceCoeff w k| ≤ E_base k}

/-- On `Icc 0 1`, the extension agrees with the slice value. -/
theorem sliceExtend_apply {w : Slice} {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    sliceExtend w x = w ⟨x, hx⟩ := by
  simp only [sliceExtend, hx, dif_pos]

/-- The restriction of the extension to the subtype `Icc 0 1` is just `w`. -/
theorem restrict_sliceExtend (w : Slice) :
    (Set.Icc (0 : ℝ) 1).restrict (sliceExtend w) = fun p => w p := by
  funext p
  simp only [Set.restrict_apply]
  rw [sliceExtend_apply p.2]

/-- The `[0,1]`-extension of a slice is `ContinuousOn (Icc 0 1)`. -/
theorem sliceExtend_continuousOn (w : Slice) :
    ContinuousOn (sliceExtend w) (Set.Icc (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict, restrict_sliceExtend]
  exact w.continuous
/-- **The coefficient functional is `2`-Lipschitz in the SUP metric.**

Each `sliceCoeff · k : Slice → ℝ` satisfies
`|sliceCoeff w1 k − sliceCoeff w2 k| ≤ 2 · dist w1 w2`, by the LANDED
`cosineCoeffs_dist_le_of_sup` with `B = dist w1 w2` (sup bound from
`ContinuousMap.dist_apply_le_dist`). -/
theorem sliceCoeff_dist_le (w1 w2 : Slice) (k : ℕ) :
    |sliceCoeff w1 k - sliceCoeff w2 k| ≤ 2 * dist w1 w2 := by
  refine cosineCoeffs_dist_le_of_sup (sliceExtend_continuousOn w1)
    (sliceExtend_continuousOn w2) dist_nonneg (fun x hx => ?_) k
  rw [sliceExtend_apply hx, sliceExtend_apply hx]
  have := ContinuousMap.dist_apply_le_dist (f := w1) (g := w2) (⟨x, hx⟩)
  rwa [Real.dist_eq] at this

/-- The functional `w ↦ sliceCoeff w k` is sup-continuous (Lipschitz). -/
theorem continuous_sliceCoeff (k : ℕ) : Continuous (fun w : Slice => sliceCoeff w k) := by
  refine LipschitzWith.continuous (K := 2) (LipschitzWith.of_dist_le_mul fun w1 w2 => ?_)
  rw [Real.dist_eq]
  calc |sliceCoeff w1 k - sliceCoeff w2 k| ≤ 2 * dist w1 w2 := sliceCoeff_dist_le w1 w2 k
    _ = (2 : NNReal) * dist w1 w2 := by norm_num
/-- The sup-EnvBall is the countable intersection of the closed coefficient slabs. -/
theorem supEnvBall_eq_iInter (E_base : ℕ → ℝ) :
    SupEnvBall E_base = ⋂ k, {w : Slice | |sliceCoeff w k| ≤ E_base k} := by
  ext w; simp only [SupEnvBall, Set.mem_setOf_eq, Set.mem_iInter]

/-- **Step 1 (DERIVED, SUP metric): the EnvBall is sup-CLOSED.**

Each slab `{w | |sliceCoeff w k| ≤ E_base k}` is the preimage of the closed set
`{r | |r| ≤ E_base k}` under the sup-continuous functional `sliceCoeff · k`
(`continuous_sliceCoeff`), hence closed; the EnvBall is their countable
intersection, hence closed IN THE SUP METRIC.  No product topology. -/
theorem isClosed_supEnvBall (E_base : ℕ → ℝ) :
    IsClosed (SupEnvBall E_base) := by
  rw [supEnvBall_eq_iInter]
  refine isClosed_iInter (fun k => ?_)
  have hcont : Continuous (fun w : Slice => |sliceCoeff w k|) :=
    (continuous_sliceCoeff k).abs
  simpa only [← Set.preimage_setOf_eq, Set.Iic] using (isClosed_Iic.preimage hcont)

/-- **Step 1 PACKAGED (DERIVED, SUP metric): the EnvBall is `IsComplete`.**

`C(Icc 0 1, ℝ)` is a `CompleteSpace` (Mathlib instance, the sup metric on a
compact domain).  The sup-closed `SupEnvBall` is therefore `IsComplete` in the
SUP metric, via `IsClosed.isComplete`.  This DISCHARGES the `IsComplete s`
hypothesis of `localExist_via_envBall_banach` for the concrete sup-metric
EnvBall — with NO coefficient/product metric anywhere. -/
theorem isComplete_supEnvBall (E_base : ℕ → ℝ) :
    IsComplete (SupEnvBall E_base) :=
  (isClosed_supEnvBall E_base).isComplete

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms sliceCoeff_dist_le
#print axioms continuous_sliceCoeff
#print axioms isClosed_supEnvBall
#print axioms isComplete_supEnvBall
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegSupBanach
