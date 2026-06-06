/-
  Phase C (MinPersistence): a cluster point of argmins is an argmin.

  The sequential-compactness core of the Hamilton/Dini argument: if `x_n` is a
  spatial argmin of `F(z_n, ·)` and `z_n → x`, then a subsequence of `x_n`
  converges to some `x*` that is a spatial argmin of `F(x, ·)`.  Used to pass
  the per-step slope bound (`sliceMin_diff_le_slope`) to the limit, where the
  min-point estimate applies.

  Abstract `F : ℝ → ℝ → ℝ`, `m t := sInf (F t '' [0,1])` (matches
  `sliceMin_isMinOn` / `sliceMin_continuousOn`).

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainMinPersistenceAtoms
import Mathlib.Topology.Sequences

open Set Filter Topology

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- **Cluster point of argmins is an argmin.**  With `m t := sInf (F t '' [0,1])`
continuous and `F` jointly continuous, a sequence of argmins `x_n` for times
`z_n → x` has a subsequence converging to a spatial argmin `x*` of `F x`. -/
theorem sliceMin_cluster_argmin
    {F : ℝ → ℝ → ℝ} {a b x : ℝ}
    (hx : x ∈ Set.Icc a b)
    (hF : ContinuousOn (Function.uncurry F)
      (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1))
    (hm_cont : ContinuousOn (fun t => sInf (F t '' Set.Icc (0:ℝ) 1))
      (Set.Icc a b))
    {zs : ℕ → ℝ} (hz_mem : ∀ n, zs n ∈ Set.Icc a b)
    (hz_lim : Tendsto zs atTop (nhds x))
    {xs : ℕ → ℝ} (hx_mem : ∀ n, xs n ∈ Set.Icc (0:ℝ) 1)
    (hx_argmin : ∀ n, F (zs n) (xs n) = sInf (F (zs n) '' Set.Icc (0:ℝ) 1)) :
    ∃ (xstar : ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ xstar ∈ Set.Icc (0:ℝ) 1 ∧
      F x xstar = sInf (F x '' Set.Icc (0:ℝ) 1) ∧
      Tendsto (fun k => xs (φ k)) atTop (nhds xstar) := by
  -- Subsequence of argmins converging in `[0,1]`.
  obtain ⟨xstar, hxstar_mem, φ, hφ_mono, hφ_lim⟩ :=
    isCompact_Icc.tendsto_subseq hx_mem
  refine ⟨xstar, φ, hφ_mono, hxstar_mem, ?_, hφ_lim⟩
  -- The paired sequence `(z_{φ k}, x_{φ k}) → (x, xstar)` in the slab.
  have hpair_lim : Tendsto (fun k => (zs (φ k), xs (φ k))) atTop
      (nhds (x, xstar)) :=
    (hz_lim.comp hφ_mono.tendsto_atTop).prodMk_nhds hφ_lim
  have hpair_mem : ∀ k, (zs (φ k), xs (φ k))
      ∈ Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1 :=
    fun k => ⟨hz_mem (φ k), hx_mem (φ k)⟩
  -- `F (z_{φk}) (x_{φk}) → F x xstar`  (joint continuity).
  have hF_lim : Tendsto (fun k => F (zs (φ k)) (xs (φ k))) atTop
      (nhds (F x xstar)) := by
    have hcwa : ContinuousWithinAt (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1) (x, xstar) := hF (x, xstar) ⟨hx, hxstar_mem⟩
    have := hcwa.tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hpair_lim, Filter.Eventually.of_forall hpair_mem⟩)
    exact this
  -- `m (z_{φk}) → m x`  (continuity of the minimum trajectory).
  have hm_lim : Tendsto (fun k => sInf (F (zs (φ k)) '' Set.Icc (0:ℝ) 1)) atTop
      (nhds (sInf (F x '' Set.Icc (0:ℝ) 1))) := by
    have hcwa : ContinuousWithinAt (fun t => sInf (F t '' Set.Icc (0:ℝ) 1))
        (Set.Icc a b) x := hm_cont x hx
    exact hcwa.tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hz_lim.comp hφ_mono.tendsto_atTop,
        Filter.Eventually.of_forall (fun k => hz_mem (φ k))⟩)
  -- The two limits agree termwise via the argmin identity.
  have heq : (fun k => F (zs (φ k)) (xs (φ k)))
      = fun k => sInf (F (zs (φ k)) '' Set.Icc (0:ℝ) 1) :=
    funext fun k => hx_argmin (φ k)
  rw [heq] at hF_lim
  exact tendsto_nhds_unique hF_lim hm_lim

end ShenWork.MinPersistenceAtoms
