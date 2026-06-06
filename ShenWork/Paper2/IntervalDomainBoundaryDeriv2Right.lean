/-
  Phase C (MinPersistence): the boundary 2nd-derivative test at the RIGHT
  endpoint `x = 1` (mirror of `boundary_min_deriv2_rlimit_nonneg`).

  A left-boundary minimum at `1` with vanishing Neumann left-limit forces a
  nonnegative `w''` left-limit.  Same junk-value-free right-limit argument,
  reflected: `w'' < 0` ⇒ `w'` antitone ⇒ (with `w'(1⁻)→0`) `w' ≥ 0` ⇒ `w`
  monotone ⇒ `w(x) ≤ w(1)`, contradicting the minimum.

  No `sorry`/`admit`/custom `axiom`.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Set Filter Topology

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- **Boundary (right) second-derivative test.** -/
theorem boundary_min_deriv2_llimit_nonneg
    {w : ℝ → ℝ} {η V : ℝ} (hη : 0 < η)
    (hwcont : ContinuousWithinAt w (Set.Iic 1) 1)
    (hmin : ∀ x ∈ Set.Ioo (1 - η) 1, w 1 ≤ w x)
    (hd1 : ∀ x ∈ Set.Ioo (1 - η) 1, HasDerivAt w (deriv w x) x)
    (hd2 : ∀ x ∈ Set.Ioo (1 - η) 1, HasDerivAt (deriv w) (deriv (deriv w) x) x)
    (hw'lim : Tendsto (deriv w) (nhdsWithin 1 (Set.Iio 1)) (nhds 0))
    (hw''lim : Tendsto (deriv (deriv w)) (nhdsWithin 1 (Set.Iio 1)) (nhds V)) :
    0 ≤ V := by
  by_contra hV
  push_neg at hV
  have hVhalf : V / 2 < 0 := by linarith
  have hev : ∀ᶠ x in nhdsWithin 1 (Set.Iio 1), deriv (deriv w) x < V / 2 :=
    hw''lim.eventually_lt_const (by linarith)
  obtain ⟨δ, hδ_mem, hδ_sub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp
    (Filter.inter_mem hev (Ioo_mem_nhdsLT (by linarith : 1 - η < 1)))
  have hδ_lt : δ < 1 := hδ_mem
  have hw''neg : ∀ x ∈ Set.Ioo δ 1, deriv (deriv w) x < 0 := fun x hx =>
    lt_trans (hδ_sub hx).1 hVhalf
  have hsubη : Set.Ioo δ 1 ⊆ Set.Ioo (1 - η) 1 := fun x hx => (hδ_sub hx).2
  -- `w'` antitone on `(δ,1)`.
  have hw'_anti : AntitoneOn (deriv w) (Set.Ioo δ 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioo _ _) ?_ ?_ ?_
    · exact fun x hx => ((hd2 x (hsubη hx)).continuousAt).continuousWithinAt
    · intro x hx; rw [interior_Ioo] at hx
      exact (hd2 x (hsubη hx)).differentiableAt.differentiableWithinAt
    · intro x hx; rw [interior_Ioo] at hx
      rw [(hd2 x (hsubη hx)).deriv]; exact (hw''neg x hx).le
  -- `w' ≥ 0` on `(δ,1)` (antitone with left-limit `0` at the right end).
  have hw'_nonneg : ∀ x ∈ Set.Ioo δ 1, 0 ≤ deriv w x := by
    intro x hx
    refine le_of_tendsto hw'lim ?_
    filter_upwards [Ioo_mem_nhdsLT hx.2] with y hy
    exact hw'_anti hx ⟨lt_trans hx.1 hy.1, hy.2⟩ (le_of_lt hy.1)
  -- `w` monotone on `(δ,1)`.
  have hw_mono : MonotoneOn w (Set.Ioo δ 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioo _ _) ?_ ?_ ?_
    · exact fun x hx => ((hd1 x (hsubη hx)).continuousAt).continuousWithinAt
    · intro x hx; rw [interior_Ioo] at hx
      exact (hd1 x (hsubη hx)).differentiableAt.differentiableWithinAt
    · intro x hx; rw [interior_Ioo] at hx; exact hw'_nonneg x hx
  -- `w(x) ≤ w(1)` (monotone with left-limit `w(1)`); with `hmin`, `w(x)=w(1)`.
  have hw_le : ∀ x ∈ Set.Ioo δ 1, w x ≤ w 1 := by
    intro x hx
    have hcont1 : Tendsto w (nhdsWithin 1 (Set.Iio 1)) (nhds (w 1)) :=
      hwcont.mono_left (nhdsWithin_mono 1 Set.Iio_subset_Iic_self)
    refine ge_of_tendsto hcont1 ?_
    filter_upwards [Ioo_mem_nhdsLT hx.2] with y hy
    exact hw_mono hx ⟨lt_trans hx.1 hy.1, hy.2⟩ (le_of_lt hy.1)
  have hw_const : ∀ x ∈ Set.Ioo δ 1, w x = w 1 := fun x hx =>
    le_antisymm (hw_le x hx) (hmin x (hsubη hx))
  -- `w ≡ w 1` on the open `(δ,1)` ⇒ `w'' = 0` there ⇒ contradiction.
  set x₀ : ℝ := (δ + 1) / 2 with hx₀_def
  have hx₀_mem : x₀ ∈ Set.Ioo δ 1 := ⟨by simp only [hx₀_def]; linarith,
    by simp only [hx₀_def]; linarith⟩
  have hderiv0 : deriv w =ᶠ[nhds x₀] (fun _ => (0:ℝ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx₀_mem] with y hy
    have : w =ᶠ[nhds y] (fun _ => w 1) :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hy)
        (fun z hz => hw_const z hz)
    rw [this.deriv_eq]; exact deriv_const y (w 1)
  have hd2_zero : deriv (deriv w) x₀ = 0 := by
    rw [hderiv0.deriv_eq]; exact deriv_const x₀ 0
  exact absurd hd2_zero (ne_of_lt (hw''neg x₀ hx₀_mem))

end ShenWork.MinPersistenceAtoms
