import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.MetricSpace.ProperSpace.Real

noncomputable section

open Filter Set Topology

namespace ShenWork.PaperOne

/-- The compact sets used for compact convergence on `ℝ`. -/
def realCompactFamily : Set (Set ℝ) := {K | IsCompact K}

/-- The standard compact window `[-R,R]`. -/
def realWindow (R : ℕ) : Set ℝ := Icc (-(R : ℝ)) (R : ℝ)

theorem realWindow_isCompact (R : ℕ) : IsCompact (realWindow R) := by
  simpa [realWindow] using (isCompact_Icc : IsCompact (Icc (-(R : ℝ)) (R : ℝ)))

theorem realCompactFamily_covers : ⋃₀ realCompactFamily = univ := by
  ext x
  constructor
  · intro hx
    exact mem_univ x
  · intro hx
    exact mem_sUnion_of_mem (mem_singleton x) (by simp [realCompactFamily])

/-- Continuous functions, uniformly bounded and equicontinuous on every compact subset of `ℝ`. -/
structure LocallyUniformlyBoundedEquicont (u : ℕ → ℝ → ℝ) : Prop where
  continuous : ∀ n, Continuous (u n)
  locally_bounded :
    ∀ K : Set ℝ, IsCompact K → ∃ M : ℝ, ∀ n x, x ∈ K → u n x ∈ Icc (-M) M
  equicontinuous_on_compacts :
    ∀ K : Set ℝ, IsCompact K → EquicontinuousOn (fun n x => u n x) K

private theorem compact_closure_range_of_locallyUniformlyBoundedEquicont
    {u : ℕ → ℝ → ℝ} (hu : LocallyUniformlyBoundedEquicont u) :
    IsCompact (closure (range (fun n : ℕ => (⟨u n, hu.continuous n⟩ : C(ℝ, ℝ))))) := by
  haveI : T2Space (UniformOnFun ℝ ℝ realCompactFamily) :=
    UniformOnFun.t2Space_of_covering realCompactFamily_covers
  haveI : T2Space (UniformOnFun ℝ ℝ {K : Set ℝ | IsCompact K}) := by
    simpa [realCompactFamily] using
      (UniformOnFun.t2Space_of_covering realCompactFamily_covers :
        T2Space (UniformOnFun ℝ ℝ realCompactFamily))
  refine ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (X := ℝ) (α := ℝ) (ι := C(ℝ, ℝ))
    (F := fun g : C(ℝ, ℝ) => (g : ℝ → ℝ)) (𝔖 := realCompactFamily)
    (fun K hK => hK)
    ?_ ?_ ?_
  · simpa [realCompactFamily, ContinuousMap.toUniformOnFunIsCompact] using
      (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact
        : IsUniformEmbedding
            (ContinuousMap.toUniformOnFunIsCompact :
              C(ℝ, ℝ) → UniformOnFun ℝ ℝ realCompactFamily)).isClosedEmbedding
  · intro K hK x hx U hU
    filter_upwards [hu.equicontinuous_on_compacts K hK x hx U hU] with y hy
    intro g
    rcases g.2 with ⟨n, hn⟩
    change (g.1 x, g.1 y) ∈ U
    rw [← hn]
    exact hy n
  · intro K hK x hx
    rcases hu.locally_bounded K hK with ⟨M, hM⟩
    exact ⟨Icc (-M) M, isCompact_Icc, fun g hg => by
      rcases hg with ⟨n, hn⟩
      change g x ∈ Icc (-M) M
      rw [← hn]
      exact hM n x hx⟩

/-- Local-uniform compactness on `ℝ` for locally bounded equicontinuous sequences. -/
theorem exists_locallyUniform_convergent_subseq {u : ℕ → ℝ → ℝ}
    (hu : LocallyUniformlyBoundedEquicont u) :
    ∃ f : C(ℝ, ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformly (fun n x => u (φ n) x) f atTop := by
  have hcompact := compact_closure_range_of_locallyUniformlyBoundedEquicont hu
  obtain ⟨f, -, φ, hφ, hlim⟩ :=
    hcompact.tendsto_subseq
      (x := fun n : ℕ => (⟨u n, hu.continuous n⟩ : C(ℝ, ℝ)))
      fun n => subset_closure (mem_range_self n)
  refine ⟨f, φ, hφ, ?_⟩
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  simpa [Function.comp_def] using
    (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hlim K hK)

#print axioms compact_closure_range_of_locallyUniformlyBoundedEquicont
#print axioms exists_locallyUniform_convergent_subseq

end ShenWork.PaperOne
