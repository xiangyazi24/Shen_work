/-
  Phase C (MinPersistence): the packaged Hamilton lower bound.

  Composes the Dini hypothesis (`sliceMin_dini_of_argmin_bound`) with the
  Grönwall core (`hamilton_lower_bound`, B3) into the exponential lower bound
  on the spatial-minimum trajectory:

    `m(a)·e^{−Kp·(t−a)} ≤ m(t)`,   `m t := sInf (F t '' [0,1])`,

  for every classical-solution slice family `F` with time-differentiable
  slices and the min-point bound `−Kp·m ≤ ∂ₛF` at argmins.  This is the
  Hamilton trick — the analytic heart of `ClassicalMinPersistence`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainSliceMinDini

open Set Filter Topology

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- **Hamilton lower bound for the spatial minimum.**  Under the min-point
bound `hbound`, the minimum trajectory decays no faster than `e^{−Kp·t}`. -/
theorem sliceMin_hamilton_bound
    {F : ℝ → ℝ → ℝ} {a b Kp : ℝ}
    (hF : ContinuousOn (Function.uncurry F)
      (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1))
    (hslice_cont : ∀ y ∈ Set.Icc (0:ℝ) 1,
      ContinuousOn (fun r => F r y) (Set.Icc a b))
    (hslice_diff : ∀ y ∈ Set.Icc (0:ℝ) 1, ∀ s ∈ Set.Ioo a b,
      HasDerivAt (fun r => F r y) (deriv (fun r => F r y) s) s)
    (hm_cont : ContinuousOn (fun t => sInf (F t '' Set.Icc (0:ℝ) 1))
      (Set.Icc a b))
    (hdF_cont : ContinuousOn
      (Function.uncurry (fun s y => deriv (fun r => F r y) s))
      (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1))
    (hbound : ∀ s ∈ Set.Icc a b, ∀ xs ∈ Set.Icc (0:ℝ) 1,
      F s xs = sInf (F s '' Set.Icc (0:ℝ) 1) →
      -Kp * sInf (F s '' Set.Icc (0:ℝ) 1) ≤ deriv (fun r => F r xs) s) :
    ∀ t ∈ Set.Icc a b,
      sInf (F a '' Set.Icc (0:ℝ) 1) * Real.exp (-Kp * (t - a))
        ≤ sInf (F t '' Set.Icc (0:ℝ) 1) :=
  hamilton_lower_bound hm_cont
    (sliceMin_dini_of_argmin_bound hF hslice_cont hslice_diff hm_cont
      hdF_cont hbound)

end ShenWork.MinPersistenceAtoms
