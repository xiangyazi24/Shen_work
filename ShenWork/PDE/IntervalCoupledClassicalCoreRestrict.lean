/-
  ShenWork/PDE/IntervalCoupledClassicalCoreRestrict.lean

  **Time-interval restriction for `CoupledDuhamelReducedClassicalCore`.**

  If `Core p T u₀ u` holds on `[0,T]` and `0 < δ ≤ T`, then `Core p δ u₀ u`
  holds on `[0,δ]`. Each Core field restricts trivially:
  - `u_pos`, `pde_u`: quantifier restriction (t < δ ≤ T → t < T)
  - `classicalRegularity`: restriction of open/product sets + ContinuousOn.mono
  - `initialTrace`: does not mention T at all (limit condition at t = 0)

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.PDE.IntervalCoupledClassicalCoreDischarge

open Set Filter

namespace ShenWork

theorem intervalDomainClassicalRegularity_restrict
    {T : ℝ} {u v : ℝ → IntervalDomain.intervalDomainPoint → ℝ}
    (hreg : IntervalDomain.intervalDomainClassicalRegularity T u v)
    {δ : ℝ} (_hδpos : 0 < δ) (hδT : δ ≤ T) :
    IntervalDomain.intervalDomainClassicalRegularity δ u v := by
  have hIoo : Set.Ioo (0 : ℝ) δ ⊆ Set.Ioo (0 : ℝ) T :=
    Set.Ioo_subset_Ioo_right hδT
  have hProdOO : Set.Ioo (0 : ℝ) δ ×ˢ Set.Ioo (0 : ℝ) 1 ⊆
      Set.Ioo (0 : ℝ) T ×ˢ Set.Ioo (0 : ℝ) 1 :=
    Set.prod_mono hIoo le_rfl
  have hProdOC : Set.Ioo (0 : ℝ) δ ×ˢ Set.Icc (0 : ℝ) 1 ⊆
      Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 :=
    Set.prod_mono hIoo le_rfl
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hreg
  exact ⟨
    fun t ht => h1 t (hIoo ht),
    fun x t ht => ⟨(h2 x t (hIoo ht)).1,
      ⟨(h2 x t (hIoo ht)).2.1.mono hIoo,
       (h2 x t (hIoo ht)).2.2.mono hIoo⟩⟩,
    ⟨h3.1.mono hProdOO, h3.2.mono hProdOO⟩,
    fun t ht => h4 t (hIoo ht),
    fun t ht => h5 t (hIoo ht),
    ⟨h6.1.mono hProdOC, h6.2.mono hProdOC⟩,
    ⟨h7.1.mono hProdOC, h7.2.mono hProdOC⟩⟩

theorem CoupledDuhamelReducedClassicalCore.restrict
    {p : CM2Params} {T : ℝ} {u₀ : IntervalDomain.intervalDomainPoint → ℝ}
    {u : ℝ → IntervalDomain.intervalDomainPoint → ℝ}
    (C : CoupledDuhamelReducedClassicalCore p T u₀ u)
    {δ : ℝ} (hδpos : 0 < δ) (hδT : δ ≤ T) :
    CoupledDuhamelReducedClassicalCore p δ u₀ u where
  u_pos t x ht htδ := C.u_pos t x ht (lt_of_lt_of_le htδ hδT)
  pde_u t x ht htδ hx := C.pde_u t x ht (lt_of_lt_of_le htδ hδT) hx
  classicalRegularity :=
    intervalDomainClassicalRegularity_restrict C.classicalRegularity hδpos hδT
  initialTrace := C.initialTrace

end ShenWork

#print axioms ShenWork.CoupledDuhamelReducedClassicalCore.restrict
