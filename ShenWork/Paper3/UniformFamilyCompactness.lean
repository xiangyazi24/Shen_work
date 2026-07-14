import ShenWork.Paper3.IntervalDomainTailReactionCoercivity

/-!
# Sequential compactness for bounded uniformly equicontinuous families

This is the domain-agnostic Arzela--Ascoli wrapper used for translated orbit
rectangles.  It deliberately accepts the equicontinuity theorem as data; the
PDE-specific spatial and time moduli are proved separately.
-/

namespace ShenWork.Paper3

open Filter Set Topology

noncomputable section

/-- A bounded uniformly equicontinuous sequence on a compact metric domain has
a uniformly convergent subsequence. -/
theorem exists_uniform_convergent_subseq_of_uniformEquicontinuous
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : ℕ → C(X, ℝ)) {K : ℝ}
    (hbound : ∀ n x, |f n x| ≤ K)
    (hequi : UniformEquicontinuous (fun n x ↦ f n x)) :
    ∃ g : C(X, ℝ), ∃ phi : ℕ → ℕ, StrictMono phi ∧
      TendstoUniformly (fun n x ↦ f (phi n) x) g atTop := by
  let S : Set C(X, ℝ) := Set.range f
  have hcompact : IsCompact (closure S) := by
    have hcover : ⋃₀ {A : Set X | IsCompact A} = Set.univ := by
      ext x
      constructor
      · exact fun _ ↦ Set.mem_univ x
      · intro _
        exact Set.mem_sUnion_of_mem (Set.mem_singleton x) isCompact_singleton
    letI : T2Space (UniformOnFun X ℝ {A : Set X | IsCompact A}) :=
      UniformOnFun.t2Space_of_covering hcover
    refine ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (X := X) (α := ℝ) (ι := C(X, ℝ))
      (F := fun q : C(X, ℝ) ↦ (q : X → ℝ))
      (𝔖 := {A : Set X | IsCompact A})
      (fun A hA ↦ hA) ?_ ?_ ?_
    · simpa [ContinuousMap.toUniformOnFunIsCompact] using
        (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact :
          IsUniformEmbedding
            (ContinuousMap.toUniformOnFunIsCompact :
              C(X, ℝ) → UniformOnFun X ℝ {A : Set X | IsCompact A})).isClosedEmbedding
    · intro A hA x hx U hU
      have heq : Equicontinuous (fun n x ↦ f n x) := hequi.equicontinuous
      filter_upwards [(heq x U hU).filter_mono nhdsWithin_le_nhds] with y hy
      intro q
      rcases q.2 with ⟨n, hn⟩
      change (q.1 x, q.1 y) ∈ U
      rw [← hn]
      exact hy n
    · intro A hA x hx
      refine ⟨Set.Icc (-K) K, isCompact_Icc, ?_⟩
      intro q hq
      rcases hq with ⟨n, rfl⟩
      exact abs_le.mp (hbound n x)
  obtain ⟨g, _hg, phi, hphi, hlim⟩ :=
    hcompact.tendsto_subseq
      (x := f) (fun n ↦ subset_closure (Set.mem_range_self n))
  refine ⟨g, phi, hphi, ?_⟩
  have hcm : Tendsto (fun n ↦ f (phi n)) atTop (𝓝 g) := by
    simpa [Function.comp_def] using hlim
  have hall :=
    (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hcm)
      Set.univ isCompact_univ
  simpa [tendstoUniformlyOn_univ] using hall

end

end ShenWork.Paper3

#print axioms
  ShenWork.Paper3.exists_uniform_convergent_subseq_of_uniformEquicontinuous
