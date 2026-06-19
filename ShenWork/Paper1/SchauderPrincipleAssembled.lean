import ShenWork.Paper1.WaveG1Bridge
import ShenWork.Paper1.SchauderFixedPoint

namespace ShenWork.Paper1

open Set Finset Filter Topology
open ShenWork.Paper1.Freudenthal

noncomputable section

/-- Thin named wrapper for the committed compact finite-ε-net input used by the
Schauder projection route. -/
theorem finite_eps_net_of_compact {E : Type*} [PseudoMetricSpace E] {K : Set E}
    (hK_cpt : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ s ⊆ K, s.Finite ∧ K ⊆ ⋃ x ∈ s, Metric.ball x ε :=
  exists_finite_eps_net hK_cpt hε

namespace Freudenthal

/-- Exact fixed point on the finite cube, obtained from the committed finite-cube
Brouwer approximate theorem by compactness and continuity. -/
theorem brouwer_fixedPoint_unitCube {n : ℕ}
    {T : (Fin n → ℝ) → Fin n → ℝ}
    (hT : Set.MapsTo T (unitCube n) (unitCube n))
    (hTcont : ContinuousOn T (unitCube n)) :
    ∃ x ∈ unitCube n, T x = x := by
  classical
  let eps : ℕ → ℝ := fun m => (1 : ℝ) / (m + 1)
  have heps_pos : ∀ m, 0 < eps m := by
    intro m
    dsimp [eps]
    positivity
  let xseq : ℕ → Fin n → ℝ := fun m =>
    Classical.choose (brouwer_cube_approx hT hTcont (eps m) (heps_pos m))
  have hxseq_mem : ∀ m, xseq m ∈ unitCube n := by
    intro m
    exact (Classical.choose_spec
      (brouwer_cube_approx hT hTcont (eps m) (heps_pos m))).1
  have hxseq_close : ∀ m, ‖T (xseq m) - xseq m‖ ≤ eps m := by
    intro m
    exact (Classical.choose_spec
      (brouwer_cube_approx hT hTcont (eps m) (heps_pos m))).2
  obtain ⟨x, hx, φ, hφ, htend⟩ :=
    (isCompact_unitCube n).tendsto_subseq hxseq_mem
  refine ⟨x, hx, ?_⟩
  have htend' : Tendsto (fun j => xseq (φ j)) atTop (𝓝 x) := by
    simpa [Function.comp_def] using htend
  have hTtend : Tendsto (fun j => T (xseq (φ j))) atTop (𝓝 (T x)) := by
    apply (hTcont.continuousWithinAt hx).tendsto.comp
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      htend' (Eventually.of_forall (fun j => hxseq_mem (φ j)))
  have hdiff_tend :
      Tendsto (fun j => T (xseq (φ j)) - xseq (φ j)) atTop (𝓝 (T x - x)) :=
    hTtend.sub htend'
  have hgap0 : Tendsto (fun j => eps (φ j)) atTop (𝓝 0) := by
    have hmono : Tendsto (fun j => ((φ j : ℝ) + 1)) atTop atTop := by
      apply tendsto_atTop_add_const_right
      exact tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
    simpa [eps, Nat.cast_add, Nat.cast_one] using
      hmono.inv_tendsto_atTop.const_mul (1 : ℝ)
  have hdiff0 :
      Tendsto (fun j => T (xseq (φ j)) - xseq (φ j)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun j => eps (φ j))
    · intro j
      exact hxseq_close (φ j)
    · exact hgap0
  have hzero : T x - x = 0 := tendsto_nhds_unique hdiff_tend hdiff0
  exact sub_eq_zero.mp hzero

end Freudenthal

/-- Once the Schauder projection data have produced finite-dimensional cube
self-maps and local reconstruction estimates, exact finite-cube Brouwer gives
the locally-uniform approximate fixed sequence. -/
theorem localUniformApproxFixedPointSequence_of_cubeApproxData_brouwer
    {trap : (ℝ → ℝ) → Prop}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (D : LocalUniformCubeApproxData trap Tmap) :
    ∃ seq : ℕ → ℝ → ℝ,
      (∀ N, trap (seq N)) ∧ LocallyUniformApproxFixed Tmap seq := by
  let a : ∀ N, Fin (D.dim N) → ℝ := fun N =>
    Classical.choose
      (Freudenthal.brouwer_fixedPoint_unitCube (D.maps N) (D.cont N))
  have ha : ∀ N, a N ∈ unitCube (D.dim N) := by
    intro N
    exact (Classical.choose_spec
      (Freudenthal.brouwer_fixedPoint_unitCube (D.maps N) (D.cont N))).1
  have hfix : ∀ N, D.Tfin N (a N) = a N := by
    intro N
    exact (Classical.choose_spec
      (Freudenthal.brouwer_fixedPoint_unitCube (D.maps N) (D.cont N))).2
  have hclose : ∀ N, ‖D.Tfin N (a N) - a N‖ ≤ D.eps N := by
    intro N
    have hzero : ‖D.Tfin N (a N) - a N‖ = 0 := by
      simp [hfix N]
    rw [hzero]
    exact (D.eps_pos N).le
  refine ⟨fun N => D.lift N (a N), ?_, ?_⟩
  · intro N
    exact D.lift_trap N (a N) (ha N)
  · intro R hR η hη
    have hlim := D.localError_tendsto R hR
    obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp hlim η hη
    have hev : ∀ᶠ N in atTop, dist (D.localError N R) 0 < η :=
      Filter.eventually_atTop.mpr ⟨N0, hN0⟩
    filter_upwards [hev] with N hN x hx
    have hNabs : |D.localError N R - 0| < η := by
      simpa [Real.dist_eq] using hN
    have herr : D.localError N R < η := by
      simpa [sub_zero, abs_of_nonneg (D.localError_nonneg N R)] using hNabs
    exact lt_of_le_of_lt (D.residual_le N (a N) (ha N) (hclose N) R hR x hx)
      herr

/-- Projected Schauder data are the finite-dimensional projection package:
`proj ∘ Tmap ∘ lift` is the finite cube map, and the residual estimate turns its
finite fixed point into a local-uniform approximate fixed point. -/
theorem localUniformApproxFixedPointSequence_of_schauderProjectionData
    {trap : (ℝ → ℝ) → Prop}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (D : ProjectedCubeApproxData trap Tmap) :
    ∃ seq : ℕ → ℝ → ℝ,
      (∀ N, trap (seq N)) ∧ LocallyUniformApproxFixed Tmap seq :=
  localUniformApproxFixedPointSequence_of_cubeApproxData_brouwer
    D.toLocalUniformCubeApproxData

/-- Provider form of the Brouwer/Schauder-projection step.  The remaining
mathematical obligation is exactly to construct `ProjectedCubeApproxData` for
each admissible local-uniformly continuous compact self-map. -/
theorem localUniformApproxFixedPointSequences_of_brouwer
    {trap : (ℝ → ℝ) → Prop}
    (H : ∀ Tmap : (ℝ → ℝ) → ℝ → ℝ,
      (∀ u, trap u → trap (Tmap u)) →
      LocalUniformContinuousOn trap Tmap →
      LocalUniformSequentiallyCompactRange trap Tmap →
        ProjectedCubeApproxData trap Tmap) :
    LocalUniformApproxFixedPointSequences trap := by
  intro Tmap hmap hcont hcompact
  exact localUniformApproxFixedPointSequence_of_schauderProjectionData
    (H Tmap hmap hcont hcompact)

/-- The compactness-limit half of the Schauder proof, named as requested. -/
theorem localUniformSchauderFixedPointPrinciple_of_approx
    {trap : (ℝ → ℝ) → Prop}
    (happroxSeq : LocalUniformApproxFixedPointSequences trap) :
    LocalUniformSchauderFixedPointPrinciple trap :=
  localUniformSchauderFixedPointPrinciple_of_approx_fixed_sequences happroxSeq

/-- Concrete-map version: projection data plus the committed compactness-limit
lemma yield an actual fixed point. -/
theorem localUniformFixedPoint_of_schauderProjectionData
    {trap : (ℝ → ℝ) → Prop} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hcont : LocalUniformContinuousOn trap Tmap)
    (hcompact : LocalUniformSequentiallyCompactRange trap Tmap)
    (D : ProjectedCubeApproxData trap Tmap) :
    ∃ U : ℝ → ℝ, trap U ∧ Tmap U = U := by
  rcases localUniformApproxFixedPointSequence_of_schauderProjectionData D with
    ⟨seq, hseq, happrox⟩
  exact hcompact.exists_fixed_of_approx_fixed hcont hseq happrox

/-- The assembled conditional principle: finite-net/Schauder-projection data for
all admissible maps imply the local-uniform Schauder fixed-point principle. -/
theorem localUniformSchauderFixedPointPrinciple_of_brouwer
    {trap : (ℝ → ℝ) → Prop}
    (H : ∀ Tmap : (ℝ → ℝ) → ℝ → ℝ,
      (∀ u, trap u → trap (Tmap u)) →
      LocalUniformContinuousOn trap Tmap →
      LocalUniformSequentiallyCompactRange trap Tmap →
        ProjectedCubeApproxData trap Tmap) :
    LocalUniformSchauderFixedPointPrinciple trap :=
  localUniformSchauderFixedPointPrinciple_of_approx
    (localUniformApproxFixedPointSequences_of_brouwer H)

#print axioms finite_eps_net_of_compact
#print axioms Freudenthal.brouwer_fixedPoint_unitCube
#print axioms localUniformApproxFixedPointSequence_of_cubeApproxData_brouwer
#print axioms localUniformApproxFixedPointSequence_of_schauderProjectionData
#print axioms localUniformApproxFixedPointSequences_of_brouwer
#print axioms localUniformSchauderFixedPointPrinciple_of_approx
#print axioms localUniformFixedPoint_of_schauderProjectionData
#print axioms localUniformSchauderFixedPointPrinciple_of_brouwer

end

end ShenWork.Paper1
