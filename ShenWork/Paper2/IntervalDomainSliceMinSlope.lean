/-
  Phase C (MinPersistence): the slice-minimum slope step (time-MVT).

  The Hamilton/Dini argument needs a one-sided difference bound on the
  spatial-minimum trajectory `m(t) := sInf (F t '' [0,1])`.  Comparing the
  later minimum's value at the earlier argmin and applying Lagrange's MVT to
  the time-slice gives, for `x < z`,
    `m(x) − m(z) ≤ (x − z) · ∂ₛF(ξ, x_z)`
  for some `ξ ∈ (x,z)` and `x_z` the argmin at `z`.  This is the per-step
  inequality the Dini hypothesis of `hamilton_lower_bound` is built from
  (the min-point estimate then bounds `∂ₛF(ξ,x_z) = u_t ≥ −K·m`).

  Stated for an abstract jointly-continuous `F : ℝ → ℝ → ℝ` with
  time-differentiable slices, matching `sliceMin_isMinOn`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainMinPersistenceAtoms

open Set

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- **Slice-minimum slope step.**  With `m t := sInf (F t '' [0,1])`, the
later-argmin comparison + Lagrange MVT give `m x − m z ≤ (x − z)·∂ₛF(ξ,x_z)`
for some interior `ξ` and argmin `x_z` at `z`. -/
theorem sliceMin_diff_le_slope
    {F : ℝ → ℝ → ℝ} {a b x z : ℝ}
    (hz : z ∈ Set.Icc a b) (hxIcc : x ∈ Set.Icc a b) (hxz : x < z)
    (hF : ContinuousOn (Function.uncurry F)
      (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1))
    (hslice_cont : ∀ y ∈ Set.Icc (0:ℝ) 1,
      ContinuousOn (fun r => F r y) (Set.Icc x z))
    (hslice_diff : ∀ y ∈ Set.Icc (0:ℝ) 1, ∀ s ∈ Set.Ioo x z,
      HasDerivAt (fun r => F r y) (deriv (fun r => F r y) s) s) :
    ∃ ξ ∈ Set.Ioo x z, ∃ xz ∈ Set.Icc (0:ℝ) 1,
      sInf (F x '' Set.Icc (0:ℝ) 1) - sInf (F z '' Set.Icc (0:ℝ) 1)
        ≤ (x - z) * deriv (fun r => F r xz) ξ := by
  -- Argmin at `z`.
  obtain ⟨xz, hxz_mem, hFz_eq⟩ := sliceMin_isMinOn hz hF
  -- MVT for the time-slice at `xz` on `[x,z]`.
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ := exists_hasDerivAt_eq_slope
    (fun r => F r xz) (deriv (fun r => F r xz)) hxz
    (hslice_cont xz hxz_mem) (fun s hs => hslice_diff xz hxz_mem s hs)
  refine ⟨ξ, hξ_mem, xz, hxz_mem, ?_⟩
  -- `m z = F z xz`; `m x ≤ F x xz`.
  have hmz : sInf (F z '' Set.Icc (0:ℝ) 1) = F z xz := hFz_eq.symm
  -- `F x '' [0,1]` is compact ⇒ bdd below.
  have hslice_x : ContinuousOn (F x) (Set.Icc (0:ℝ) 1) := by
    intro y hy
    have := hF (x, y) ⟨hxIcc, hy⟩
    exact (this.comp (Continuous.continuousWithinAt (by fun_prop))
      (fun w hw => ⟨hxIcc, hw⟩) : ContinuousWithinAt (fun w => F x w) _ y)
  have hbdd : BddBelow (F x '' Set.Icc (0:ℝ) 1) :=
    (isCompact_Icc.image_of_continuousOn hslice_x).bddBelow
  have hmx_le : sInf (F x '' Set.Icc (0:ℝ) 1) ≤ F x xz :=
    csInf_le hbdd (Set.mem_image_of_mem _ hxz_mem)
  -- Convert the slope identity.
  have hslope : deriv (fun r => F r xz) ξ = (F z xz - F x xz) / (z - x) := hξ_eq
  have hzx_pos : 0 < z - x := by linarith
  have hdiff_eq : F x xz - F z xz = (x - z) * deriv (fun r => F r xz) ξ := by
    rw [hslope]
    field_simp
    ring
  calc sInf (F x '' Set.Icc (0:ℝ) 1) - sInf (F z '' Set.Icc (0:ℝ) 1)
      ≤ F x xz - F z xz := by rw [hmz]; linarith [hmx_le]
    _ = (x - z) * deriv (fun r => F r xz) ξ := hdiff_eq

end ShenWork.MinPersistenceAtoms
