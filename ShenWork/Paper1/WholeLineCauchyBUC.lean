import ShenWork.Paper1.WholeLineCauchyTruncation
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UniformSpace.UniformApproximation

open Filter Topology MeasureTheory Real Set
open scoped BoundedContinuousFunction

noncomputable section

namespace ShenWork.Paper1

/-!
# The paper-faithful BUC phase space

The paper defines `C_unif^b(R)` as the bounded uniformly continuous functions.
The historical repository predicate `IsCUnifBdd` only stores continuity and
boundedness, so it is retained for compatibility while the genuine Cauchy
construction uses the stronger predicate below.
-/

/-- The actual whole-line phase space used in the paper: bounded uniformly
continuous real functions. -/
def PaperCUnifBdd (f : ℝ → ℝ) : Prop :=
  UniformContinuous f ∧ IsBddFun f

/-- Paper-faithful nonnegative Cauchy data. -/
def PaperNonnegativeInitialDatum (u₀ : ℝ → ℝ) : Prop :=
  PaperCUnifBdd u₀ ∧ ∀ x, 0 ≤ u₀ x

theorem PaperCUnifBdd.to_isCUnifBdd
    {f : ℝ → ℝ} (h : PaperCUnifBdd f) :
    IsCUnifBdd f :=
  ⟨h.1.continuous, h.2⟩

theorem PaperNonnegativeInitialDatum.to_nonnegativeInitialDatum
    {u₀ : ℝ → ℝ} (h : PaperNonnegativeInitialDatum u₀) :
    NonnegativeInitialDatum u₀ :=
  ⟨h.1.to_isCUnifBdd, h.2⟩

/-- Bounded continuous functions whose underlying maps are uniformly
continuous.  The subtype inherits the ambient sup metric. -/
abbrev WholeLineBUC :=
  {f : BoundedContinuousFunction ℝ ℝ // UniformContinuous (f : ℝ → ℝ)}

/-- Uniformly continuous bounded functions form a closed subset of the
complete sup-norm space of bounded continuous functions. -/
theorem isClosed_wholeLineBUC :
    IsClosed {f : BoundedContinuousFunction ℝ ℝ |
      UniformContinuous (f : ℝ → ℝ)} := by
  apply IsSeqClosed.isClosed
  intro fs f hfs hlim
  have hunif : TendstoUniformly (fun n => (fs n : ℝ → ℝ))
      (f : ℝ → ℝ) atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim
  exact hunif.uniformContinuous (Frequently.of_forall hfs)

noncomputable instance wholeLineBUCCompleteSpace : CompleteSpace WholeLineBUC :=
  isClosed_wholeLineBUC.completeSpace_coe

theorem WholeLineBUC.isCUnifBdd (u : WholeLineBUC) :
    IsCUnifBdd (u.1 : ℝ → ℝ) := by
  refine ⟨u.2.continuous, ⟨‖u.1‖, ?_⟩⟩
  intro x
  simpa [Real.norm_eq_abs] using
    BoundedContinuousFunction.norm_coe_le_norm u.1 x

/-- Construct a BUC element from an explicit uniform bound. -/
def wholeLineBUCOfUniformBound
    (f : ℝ → ℝ) (hf : UniformContinuous f) (M : ℝ)
    (hM : ∀ x, |f x| ≤ M) : WholeLineBUC :=
  ⟨{
    toContinuousMap := ⟨f, hf.continuous⟩
    map_bounded' := ⟨2 * M, fun x y => by
      rw [Real.dist_eq]
      exact (abs_sub (f x) (f y)).trans
        (by linarith [hM x, hM y])⟩ }, hf⟩

@[simp] theorem wholeLineBUCOfUniformBound_apply
    (f : ℝ → ℝ) (hf : UniformContinuous f) (M : ℝ)
    (hM : ∀ x, |f x| ≤ M) (x : ℝ) :
    (wholeLineBUCOfUniformBound f hf M hM).1 x = f x :=
  rfl

/-- Build an element of the genuine BUC space from a paper-level function. -/
def wholeLineBUCOfPaperCUnifBdd
    (f : ℝ → ℝ) (hf : PaperCUnifBdd f) : WholeLineBUC := by
  let M : ℝ := Classical.choose hf.2
  have hM : ∀ x, |f x| ≤ M := Classical.choose_spec hf.2
  refine ⟨{
    toContinuousMap := ⟨f, hf.1.continuous⟩
    map_bounded' := ⟨2 * M, ?_⟩ }, hf.1⟩
  intro x y
  rw [Real.dist_eq]
  calc
    |f x - f y| ≤ |f x| + |f y| := abs_sub _ _
    _ ≤ M + M := add_le_add (hM x) (hM y)
    _ = 2 * M := by ring

@[simp] theorem wholeLineBUCOfPaperCUnifBdd_apply
    (f : ℝ → ℝ) (hf : PaperCUnifBdd f) (x : ℝ) :
    (wholeLineBUCOfPaperCUnifBdd f hf).1 x = f x :=
  rfl

/-- Continuous BUC-valued trajectories on a compact time interval. -/
abbrev WholeLineBUCTrajectory (T : ℝ) :=
  ContinuousMap (Set.Icc (0 : ℝ) T) WholeLineBUC

theorem wholeLineBUCTrajectory_completeSpace (T : ℝ) :
    CompleteSpace (WholeLineBUCTrajectory T) :=
  inferInstance

/-- Evaluation of a BUC trajectory is jointly continuous in time and space. -/
theorem wholeLineBUCTrajectory_jointContinuous
    {T : ℝ} (U : WholeLineBUCTrajectory T) :
    Continuous (fun z : Set.Icc (0 : ℝ) T × ℝ => (U z.1).1 z.2) := by
  fun_prop

/-- Pointwise clamping preserves the BUC phase space. -/
def wholeLineBUCClamp (M : ℝ) (u : WholeLineBUC) : WholeLineBUC :=
  ⟨u.1.comp (clampIcc M) (clampIcc_lipschitz M),
    (clampIcc_lipschitz M).uniformContinuous.comp u.2⟩

@[simp] theorem wholeLineBUCClamp_apply
    (M : ℝ) (u : WholeLineBUC) (x : ℝ) :
    (wholeLineBUCClamp M u).1 x = clampIcc M (u.1 x) :=
  rfl

theorem wholeLineBUCClamp_mem_Icc
    {M : ℝ} (hM : 0 ≤ M) (u : WholeLineBUC) (x : ℝ) :
    (wholeLineBUCClamp M u).1 x ∈ Set.Icc (0 : ℝ) M :=
  clampIcc_mem_Icc hM (u.1 x)

section WholeLineCauchyBUCAxiomAudit

#print axioms PaperCUnifBdd.to_isCUnifBdd
#print axioms PaperNonnegativeInitialDatum.to_nonnegativeInitialDatum
#print axioms isClosed_wholeLineBUC
#print axioms WholeLineBUC.isCUnifBdd
#print axioms wholeLineBUCOfUniformBound
#print axioms wholeLineBUCOfPaperCUnifBdd
#print axioms wholeLineBUCTrajectory_jointContinuous
#print axioms wholeLineBUCClamp_mem_Icc

end WholeLineCauchyBUCAxiomAudit

end ShenWork.Paper1
