/-
  B4 (MinPersistence): elliptic coefficient bounds.

  Combines the two proved one-dimensional elliptic black boxes
  (`elliptic_sup_bound`, `elliptic_deriv_bound`, both in
  `IntervalDomainMinPersistenceAtoms`) into the package of bounds the
  Hamilton min-point estimate needs for the chemical concentration `v`:
  for a nonnegative solution of `−v'' + μ v = Src` on `(0,1)` with
  homogeneous Neumann endpoints and `|Src| ≤ B`,

    v ≤ B/μ,    |v'| ≤ 2B,    |v''| ≤ 2B    on the open interior.

  Instantiated at `Src = ν·u^γ`, `B = ν·M'^γ` (the regime sup bound), these
  are exactly the `v`-field bounds needed by the MinPersistence argument.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainMinPersistenceAtoms

open Filter Topology

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- **Elliptic coefficient bounds (the B4 atom).**  A nonnegative interior
solution `w` of the 1-d elliptic identity `w'' = μ w − Src` with `|Src| ≤ B`
and homogeneous Neumann endpoints satisfies `w ≤ B/μ` and the slab-independent
derivative bounds `|w'| ≤ 2B`, `|w''| ≤ 2B` on `(0,1)`. -/
theorem elliptic_coeff_bounds
    {w Src : ℝ → ℝ} {μ B : ℝ} (hμ : 0 < μ) (hB : 0 ≤ B)
    (hcont : ContinuousOn w (Set.Icc (0:ℝ) 1))
    (hd1 : ∀ y ∈ Set.Ioo (0:ℝ) 1, DifferentiableAt ℝ w y)
    (hd2 : ∀ y ∈ Set.Ioo (0:ℝ) 1, DifferentiableAt ℝ (deriv w) y)
    (hd2c : ContinuousOn (deriv (deriv w)) (Set.Ioo (0:ℝ) 1))
    (hPDE : ∀ y ∈ Set.Ioo (0:ℝ) 1, deriv (deriv w) y = μ * w y - Src y)
    (hSrc : ∀ y ∈ Set.Ioo (0:ℝ) 1, |Src y| ≤ B)
    (hwnn : ∀ y ∈ Set.Ioo (0:ℝ) 1, 0 ≤ w y)
    (hNeu0 : Filter.Tendsto (deriv w) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hNeu1 : Filter.Tendsto (deriv w) (nhdsWithin 1 (Set.Iio 1)) (nhds 0)) :
    (∀ y ∈ Set.Ioo (0:ℝ) 1, w y ≤ B / μ) ∧
      (∀ y ∈ Set.Ioo (0:ℝ) 1, |deriv w y| ≤ 2 * B) ∧
      (∀ y ∈ Set.Ioo (0:ℝ) 1, |deriv (deriv w) y| ≤ 2 * B) := by
  -- Sup bound `w ≤ B/μ` on the closed interval, restricted to the interior.
  have hsup_Icc := elliptic_sup_bound hμ hcont hd1 hd2 hPDE hSrc hNeu0 hNeu1
  have hsup : ∀ y ∈ Set.Ioo (0:ℝ) 1, w y ≤ B / μ := fun y hy =>
    hsup_Icc y (Set.Ioo_subset_Icc_self hy)
  have hBμ_nonneg : 0 ≤ B / μ := div_nonneg hB hμ.le
  -- `|w| ≤ B/μ` on the interior (using `0 ≤ w`).
  have hw_bd : ∀ y ∈ Set.Ioo (0:ℝ) 1, |w y| ≤ B / μ := by
    intro y hy
    rw [abs_of_nonneg (hwnn y hy)]
    exact hsup y hy
  -- `μ·(B/μ) + B = 2B`.
  have hμcancel : μ * (B / μ) + B = 2 * B := by
    field_simp
    ring
  -- Derivative bound via `elliptic_deriv_bound` with `Mw := B/μ`.
  have hderiv := elliptic_deriv_bound hμ.le hB hBμ_nonneg hd2 hd2c hPDE hSrc
    hw_bd hNeu0
  have hd_bd : ∀ y ∈ Set.Ioo (0:ℝ) 1, |deriv w y| ≤ 2 * B := by
    intro y hy
    have := hderiv y hy
    rwa [hμcancel] at this
  -- Second-derivative bound straight from the identity.
  have hd2_bd : ∀ y ∈ Set.Ioo (0:ℝ) 1, |deriv (deriv w) y| ≤ 2 * B := by
    intro y hy
    rw [hPDE y hy]
    calc |μ * w y - Src y| ≤ |μ * w y| + |Src y| := by
          rw [sub_eq_add_neg]
          exact le_trans (abs_add_le _ _) (by rw [abs_neg])
      _ ≤ μ * (B / μ) + B := by
          refine add_le_add ?_ (hSrc y hy)
          rw [abs_mul, abs_of_pos hμ]
          exact mul_le_mul_of_nonneg_left (hw_bd y hy) hμ.le
      _ = 2 * B := hμcancel
  exact ⟨hsup, hd_bd, hd2_bd⟩

end ShenWork.MinPersistenceAtoms
