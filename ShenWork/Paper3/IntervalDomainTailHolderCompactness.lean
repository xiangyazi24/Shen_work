import ShenWork.Paper3.IntervalDomainTailReactionCoercivity

/-!
# Uniform compactness of interval profiles with a common Holder modulus

The time-translate argument in Paper 3 uses spatial compactness on the closed
interval.  The general-power mild restart naturally supplies a common Holder
modulus, rather than the Lipschitz modulus available in the linear-flux case.
This file records the corresponding concrete Arzela--Ascoli producer.
-/

namespace ShenWork.Paper3

open Filter Set Topology
open ShenWork.IntervalDomain

noncomputable section

local instance intervalDomainTailHolderMetricSpace : MetricSpace intervalDomainPoint :=
  inferInstanceAs (MetricSpace (Subtype (Set.Icc (0 : ℝ) 1)))

/-- A uniformly bounded sequence of continuous profiles with a common
positive-exponent Holder modulus has a uniformly convergent subsequence. -/
theorem intervalDomain_exists_uniform_convergent_subseq_of_holder
    (f : ℕ → C(intervalDomainPoint, ℝ)) {K G theta : ℝ}
    (hK : 0 ≤ K) (hG : 0 ≤ G) (htheta : 0 < theta)
    (hbound : ∀ n x, |f n x| ≤ K)
    (hholder : ∀ n x y,
      |f n x - f n y| ≤ G * |x.1 - y.1| ^ theta) :
    ∃ g : C(intervalDomainPoint, ℝ), ∃ phi : ℕ → ℕ, StrictMono phi ∧
      TendstoUniformly (fun n x ↦ f (phi n) x) g atTop := by
  have hequi : UniformEquicontinuous (fun n x ↦ f n x) := by
    let modulus : ℝ → ℝ := fun r ↦ G * |r| ^ theta
    have hmodulus : Tendsto modulus (𝓝 0) (𝓝 0) := by
      have hcont : ContinuousAt modulus 0 := by
        exact continuousAt_const.mul
          (continuous_abs.continuousAt.rpow_const (Or.inr htheta.le))
      have hzero : modulus 0 = 0 := by
        simp [modulus, htheta.ne']
      change Tendsto modulus (𝓝 0) (𝓝 (modulus 0)) at hcont
      simpa only [hzero] using hcont
    refine Metric.uniformEquicontinuous_of_continuity_modulus modulus hmodulus
      (fun n x ↦ f n x) ?_
    intro x y n
    have hxy := hholder n x y
    have hdist : dist x y = |x.1 - y.1| := by
      change |x.1 - y.1| = |x.1 - y.1|
      rfl
    have hvalue : dist (f n x) (f n y) = |f n x - f n y| := by
      simp [Real.dist_eq]
    simpa [modulus, hdist, hvalue] using hxy
  let S : Set C(intervalDomainPoint, ℝ) := Set.range f
  have hcompact : IsCompact (closure S) := by
    have hcover :
        ⋃₀ {A : Set intervalDomainPoint | IsCompact A} = Set.univ := by
      ext x
      constructor
      · exact fun _ ↦ Set.mem_univ x
      · intro _
        exact Set.mem_sUnion_of_mem (Set.mem_singleton x) isCompact_singleton
    letI : T2Space
        (UniformOnFun intervalDomainPoint ℝ
          {A : Set intervalDomainPoint | IsCompact A}) :=
      UniformOnFun.t2Space_of_covering hcover
    refine ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (X := intervalDomainPoint) (α := ℝ)
      (ι := C(intervalDomainPoint, ℝ))
      (F := fun q : C(intervalDomainPoint, ℝ) ↦
        (q : intervalDomainPoint → ℝ))
      (𝔖 := {A : Set intervalDomainPoint | IsCompact A})
      (fun A hA ↦ hA) ?_ ?_ ?_
    · simpa [ContinuousMap.toUniformOnFunIsCompact] using
        (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact :
          IsUniformEmbedding
            (ContinuousMap.toUniformOnFunIsCompact :
              C(intervalDomainPoint, ℝ) →
                UniformOnFun intervalDomainPoint ℝ
                  {A : Set intervalDomainPoint | IsCompact A})).isClosedEmbedding
    · intro A hA
      intro x hx U hU
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

#print axioms intervalDomain_exists_uniform_convergent_subseq_of_holder

end

end ShenWork.Paper3
