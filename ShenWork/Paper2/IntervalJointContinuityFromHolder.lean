/-
  A small joint-continuity bridge used by the faithful positive-time bootstrap.

  Pointwise time continuity plus a spatial Holder modulus uniform in time gives
  joint space-time continuity.  This isolates the topology bookkeeping from the
  PDE estimates that provide the two inputs.
-/
import ShenWork.Paper2.IntervalPositiveRpowHolder

open Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

/-- Pointwise continuity in the first variable and a uniform positive-power
Holder modulus in the second variable imply joint continuity on a product set. -/
theorem jointContinuousOn_of_timeSlices_and_uniformHolder
    {f : ℝ → ℝ → ℝ} {I X : Set ℝ} {K theta : ℝ}
    (hK : 0 ≤ K) (htheta : 0 < theta)
    (htime : ∀ x ∈ X, ContinuousOn (fun t ↦ f t x) I)
    (hholder : ∀ t ∈ I, ∀ x ∈ X, ∀ y ∈ X,
      |f t x - f t y| ≤ K * |x - y| ^ theta) :
    ContinuousOn (Function.uncurry f) (I ×ˢ X) := by
  rw [Metric.continuousOn_iff]
  intro q hq eps heps
  obtain ⟨hqI, hqX⟩ := Set.mem_prod.mp hq
  have heps2 : 0 < eps / 2 := by linarith
  have htime_q := htime q.2 hqX
  rw [Metric.continuousOn_iff] at htime_q
  obtain ⟨delta_t, hdelta_t, htime_delta⟩ :=
    htime_q q.1 hqI (eps / 2) heps2
  let modulus : ℝ × ℝ → ℝ :=
    fun z ↦ K * |z.2 - q.2| ^ theta
  have hmodulus_cont : Continuous modulus := by
    dsimp [modulus]
    have habs_cont : Continuous (fun z : ℝ × ℝ ↦ |z.2 - q.2|) := by
      fun_prop
    exact continuous_const.mul
      (habs_cont.rpow_const (fun _ ↦ Or.inr htheta.le))
  have hmodulus_q : modulus q = 0 := by
    simp [modulus, htheta.ne']
  have hmodulus_cont_at : ContinuousAt modulus q :=
    hmodulus_cont.continuousAt
  rw [Metric.continuousAt_iff] at hmodulus_cont_at
  obtain ⟨delta_x, hdelta_x, hmodulus_delta⟩ :=
    hmodulus_cont_at (eps / 2) heps2
  refine ⟨min delta_t delta_x, lt_min hdelta_t hdelta_x, ?_⟩
  intro z hz hzdist
  obtain ⟨hzI, hzX⟩ := Set.mem_prod.mp hz
  have hzdist_t : dist z.1 q.1 < delta_t := by
    calc
      dist z.1 q.1 ≤ dist z q := by
        rw [Prod.dist_eq]
        exact le_max_left _ _
      _ < delta_t := lt_of_lt_of_le hzdist (min_le_left _ _)
  have hzdist_x : dist z q < delta_x :=
    lt_of_lt_of_le hzdist (min_le_right _ _)
  have htime_close := htime_delta z.1 hzI hzdist_t
  have hmodulus_close := hmodulus_delta hzdist_x
  have hmodulus_nonneg : 0 ≤ modulus z :=
    mul_nonneg hK (Real.rpow_nonneg (abs_nonneg _) _)
  have hspace_close : K * |z.2 - q.2| ^ theta < eps / 2 := by
    rw [hmodulus_q, Real.dist_eq, sub_zero,
      abs_of_nonneg hmodulus_nonneg] at hmodulus_close
    exact hmodulus_close
  rw [Function.uncurry_apply_pair, Function.uncurry_apply_pair, Real.dist_eq]
  calc
    |f z.1 z.2 - f q.1 q.2|
        ≤ |f z.1 z.2 - f z.1 q.2| +
            |f z.1 q.2 - f q.1 q.2| :=
          abs_sub_le _ _ _
    _ < eps / 2 + eps / 2 := by
      apply add_lt_add_of_le_of_lt
      · exact (hholder z.1 hzI z.2 hzX q.2 hqX).trans
          hspace_close.le
      · simpa [Real.dist_eq] using htime_close
    _ = eps := by ring

/-- A Holder modulus uniform on every positive-time strip is enough for joint
continuity on the open positive-time slab.  The modulus may deteriorate as the
lower time cutoff tends to zero. -/
theorem jointContinuousOn_Ioo_of_timeSlices_and_positiveStripHolder
    {f : ℝ → ℝ → ℝ} {T : ℝ} {X : Set ℝ} {theta : ℝ}
    (htheta : 0 < theta)
    (htime : ∀ x ∈ X,
      ContinuousOn (fun t ↦ f t x) (Set.Ioo (0 : ℝ) T))
    (hholder : ∀ tau : ℝ, 0 < tau →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc tau T, ∀ x ∈ X, ∀ y ∈ X,
        |f t x - f t y| ≤ K * |x - y| ^ theta) :
    ContinuousOn (Function.uncurry f)
      (Set.Ioo (0 : ℝ) T ×ˢ X) := by
  intro q hq
  obtain ⟨hq_time, hqX⟩ := Set.mem_prod.mp hq
  let tau : ℝ := q.1 / 2
  have htau_pos : 0 < tau := by
    dsimp [tau]
    linarith [hq_time.1]
  have htau_q : tau < q.1 := by
    dsimp [tau]
    linarith [hq_time.1]
  obtain ⟨K, hK, hKholder⟩ := hholder tau htau_pos
  have htime_local : ∀ x ∈ X,
      ContinuousOn (fun t ↦ f t x) (Set.Ioo tau T) := by
    intro x hx
    exact (htime x hx).mono (by
      intro t ht
      exact ⟨htau_pos.trans ht.1, ht.2⟩)
  have hholder_local : ∀ t ∈ Set.Ioo tau T, ∀ x ∈ X, ∀ y ∈ X,
      |f t x - f t y| ≤ K * |x - y| ^ theta := by
    intro t ht x hx y hy
    exact hKholder t ⟨ht.1.le, ht.2.le⟩ x hx y hy
  have hjoint_local :=
    jointContinuousOn_of_timeSlices_and_uniformHolder
      hK htheta htime_local hholder_local
  have hq_local : q ∈ Set.Ioo tau T ×ˢ X :=
    Set.mem_prod.mpr ⟨⟨htau_q, hq_time.2⟩, hqX⟩
  apply (hjoint_local q hq_local).mono_of_mem_nhdsWithin
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  refine ⟨Set.Ioi tau ×ˢ Set.univ,
    prod_mem_nhds (Ioi_mem_nhds htau_q) Filter.univ_mem, ?_⟩
  intro z hz
  obtain ⟨hz_open, hz_global⟩ := hz
  obtain ⟨hz_tau, _hz_univ⟩ := Set.mem_prod.mp hz_open
  obtain ⟨hz_time, hzX⟩ := Set.mem_prod.mp hz_global
  exact Set.mem_prod.mpr ⟨⟨hz_tau, hz_time.2⟩, hzX⟩

end ShenWork.Paper2

#print axioms ShenWork.Paper2.jointContinuousOn_of_timeSlices_and_uniformHolder
#print axioms ShenWork.Paper2.jointContinuousOn_Ioo_of_timeSlices_and_positiveStripHolder
