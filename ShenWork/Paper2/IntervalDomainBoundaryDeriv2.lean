/-
  Phase B (MinPersistence): the boundary second-derivative test.

  At a left-boundary spatial argmin (`x* = 0`), the interior `u''` cannot have
  a negative right-limit.  Working entirely with the interior derivative and
  its `t→0⁺` right-limits (the zero-extension lift's two-sided derivative at the
  endpoint is junk; the genuine Neumann content is the right-limit), we prove:

    if `w` is right-continuous at `0`, `C²` on `(0,η)`, `w(0) ≤ w(x)` for
    `x∈(0,η)`, `w' → 0` and `w'' → V` along `0⁺`, then `0 ≤ V`.

  This is the boundary analog of `interior_argmin_deriv2_nonneg`; `V` is the
  right-limit of the interior Laplacian, the quantity the boundary PDE uses.

  No `sorry`/`admit`/custom `axiom`.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Set Filter Topology

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- **Boundary (left) second-derivative test.**  A right-boundary minimum with
vanishing Neumann right-limit forces a nonnegative `w''` right-limit. -/
theorem boundary_min_deriv2_rlimit_nonneg
    {w : ℝ → ℝ} {η V : ℝ} (hη : 0 < η)
    (hwcont : ContinuousWithinAt w (Set.Ici 0) 0)
    (hmin : ∀ x ∈ Set.Ioo (0:ℝ) η, w 0 ≤ w x)
    (hd1 : ∀ x ∈ Set.Ioo (0:ℝ) η, HasDerivAt w (deriv w x) x)
    (hd2 : ∀ x ∈ Set.Ioo (0:ℝ) η, HasDerivAt (deriv w) (deriv (deriv w) x) x)
    (hw'lim : Tendsto (deriv w) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hw''lim : Tendsto (deriv (deriv w)) (nhdsWithin 0 (Set.Ioi 0)) (nhds V)) :
    0 ≤ V := by
  by_contra hV
  push_neg at hV
  -- A right-neighbourhood `(0,δ)` where `w'' < V/2 < 0`.
  have hVhalf : V / 2 < 0 := by linarith
  have hev : ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0), deriv (deriv w) x < V / 2 :=
    hw''lim.eventually_lt_const (by linarith)
  obtain ⟨δ, hδ_mem, hδ_sub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (Filter.inter_mem hev (Ioo_mem_nhdsGT hη))
  have hδ_pos : 0 < δ := hδ_mem
  have hw''neg : ∀ x ∈ Set.Ioo (0:ℝ) δ, deriv (deriv w) x < 0 := fun x hx =>
    lt_trans (hδ_sub hx).1 hVhalf
  have hsubη : Set.Ioo (0:ℝ) δ ⊆ Set.Ioo (0:ℝ) η := fun x hx => (hδ_sub hx).2
  -- `w'` is antitone on `(0,δ)` (`w'' ≤ 0`).
  have hw'_anti : AntitoneOn (deriv w) (Set.Ioo (0:ℝ) δ) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioo _ _) ?_ ?_ ?_
    · exact fun x hx => ((hd2 x (hsubη hx)).continuousAt).continuousWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      exact (hd2 x (hsubη hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      rw [(hd2 x (hsubη hx)).deriv]
      exact (hw''neg x hx).le
  -- Hence `w' ≤ 0` on `(0,δ)` (antitone with right-limit `0`).
  have hw'_nonpos : ∀ x ∈ Set.Ioo (0:ℝ) δ, deriv w x ≤ 0 := by
    intro x hx
    refine ge_of_tendsto hw'lim ?_
    filter_upwards [Ioo_mem_nhdsGT hx.1] with y hy
    exact hw'_anti ⟨hy.1, lt_trans hy.2 hx.2⟩ hx (le_of_lt hy.2)
  -- Hence `w` is antitone on `(0,δ)`.
  have hw_anti : AntitoneOn w (Set.Ioo (0:ℝ) δ) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioo _ _) ?_ ?_ ?_
    · exact fun x hx => ((hd1 x (hsubη hx)).continuousAt).continuousWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      exact (hd1 x (hsubη hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      exact hw'_nonpos x hx
  -- `w(x) ≤ w(0)` (antitone with right-limit `w(0)`); with `hmin`, `w(x)=w(0)`.
  have hw_le : ∀ x ∈ Set.Ioo (0:ℝ) δ, w x ≤ w 0 := by
    intro x hx
    have hcont0 : Tendsto w (nhdsWithin 0 (Set.Ioi 0)) (nhds (w 0)) :=
      hwcont.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)
    refine ge_of_tendsto hcont0 ?_
    filter_upwards [Ioo_mem_nhdsGT hx.1] with y hy
    exact hw_anti ⟨hy.1, lt_trans hy.2 hx.2⟩ hx (le_of_lt hy.2)
  have hw_const : ∀ x ∈ Set.Ioo (0:ℝ) δ, w x = w 0 := fun x hx =>
    le_antisymm (hw_le x hx) (hmin x (hsubη hx))
  -- `w ≡ w 0` on the open `(0,δ)` ⇒ `w'' = 0` there ⇒ contradiction.
  set x₀ : ℝ := δ / 2 with hx₀_def
  have hx₀_mem : x₀ ∈ Set.Ioo (0:ℝ) δ := ⟨by positivity, by simp only [hx₀_def]; linarith⟩
  have hev_const : w =ᶠ[nhds x₀] (fun _ => w 0) :=
    Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx₀_mem)
      (fun y hy => hw_const y hy)
  have hderiv0 : deriv w =ᶠ[nhds x₀] (fun _ => (0:ℝ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx₀_mem] with y hy
    have : w =ᶠ[nhds y] (fun _ => w 0) :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hy)
        (fun z hz => hw_const z hz)
    rw [this.deriv_eq]; exact deriv_const y (w 0)
  have hd2_zero : deriv (deriv w) x₀ = 0 := by
    rw [hderiv0.deriv_eq]; exact deriv_const x₀ 0
  exact absurd hd2_zero (ne_of_lt (hw''neg x₀ hx₀_mem))

end ShenWork.MinPersistenceAtoms
