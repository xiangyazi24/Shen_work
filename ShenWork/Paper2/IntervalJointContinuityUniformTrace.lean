/-
  Uniform time traces from joint continuity on a positive-time compact spatial
  slab.  A compact time window around the target point converts ordinary joint
  continuity into uniform continuity, hence uniform convergence of the nearby
  spatial slices.
-/
import ShenWork.Paper2.IntervalJointContinuityFromHolder

open Filter Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

/-- Joint continuity on `(0,T) × [0,1]` gives a uniform-in-space time trace at
every strict positive target time. -/
theorem jointContinuousOn_Ioo_prod_Icc_tendstoUniformlyOn
    {F : ℝ → ℝ → ℝ} {T t : ℝ}
    (hF : ContinuousOn (Function.uncurry F)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1))
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    TendstoUniformlyOn F (F t) (𝓝 t) (Set.Icc (0 : ℝ) 1) := by
  let a : ℝ := t / 2
  let b : ℝ := (t + T) / 2
  have ha : 0 < a := by
    dsimp [a]
    linarith [ht.1]
  have hat : a < t := by
    dsimp [a]
    linarith [ht.1]
  have htb : t < b := by
    dsimp [b]
    linarith [ht.2]
  have hbT : b < T := by
    dsimp [b]
    linarith [ht.2]
  have hsub :
      Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1 ⊆
        Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro q hq
    obtain ⟨hs, hx⟩ := Set.mem_prod.mp hq
    exact Set.mem_prod.mpr
      ⟨⟨ha.trans_le hs.1, hs.2.trans_lt hbT⟩, hx⟩
  have hcompact : IsCompact
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have huc : UniformContinuousOn (Function.uncurry F)
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    hcompact.uniformContinuousOn_of_continuous (hF.mono hsub)
  have htrace : TendstoUniformlyOn F (F t)
      (𝓝[Set.Icc a b] t) (Set.Icc (0 : ℝ) 1) :=
    huc.tendstoUniformlyOn ⟨hat.le, htb.le⟩
  have hwindow : Set.Icc a b ∈ 𝓝 t := Icc_mem_nhds hat htb
  have hnhds : 𝓝[Set.Icc a b] t = 𝓝 t :=
    nhdsWithin_eq_nhds.mpr hwindow
  simpa [hnhds] using htrace

end ShenWork.Paper2

#print axioms ShenWork.Paper2.jointContinuousOn_Ioo_prod_Icc_tendstoUniformlyOn
