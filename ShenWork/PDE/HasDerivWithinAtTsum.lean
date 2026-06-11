import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# One-sided term-by-term differentiation for dominated real series

This file supplies a within-set version of `hasDerivAt_tsum` for the `ℕ`-indexed
case used by the interval cosine-mode tower.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace ShenWork.HasDerivWithinAtTsum

private lemma summable_of_summable_hasDerivWithinAt
    {F F' : ℕ → ℝ → ℝ} {s : Set ℝ} (hs : Convex ℝ s)
    {u : ℕ → ℝ} (hu : Summable u)
    (hF : ∀ n, ∀ x ∈ s, HasDerivWithinAt (F n) (F' n x) s x)
    (hbound : ∀ n, ∀ x ∈ s, |F' n x| ≤ u n)
    {x₀ : ℝ} (hx₀ : x₀ ∈ s) (hF0 : Summable fun n => F n x₀)
    {x : ℝ} (hx : x ∈ s) :
    Summable fun n => F n x := by
  have hdiff_bound :
      ∀ n, ‖F n x - F n x₀‖ ≤ u n * ‖x - x₀‖ := by
    intro n
    simpa [Real.norm_eq_abs, norm_sub_rev] using
      hs.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := F n) (f' := fun y => F' n y) (C := u n)
        (hF n) (fun y hy => by simpa [Real.norm_eq_abs] using hbound n y hy)
        hx₀ hx
  have hdiff : Summable fun n => F n x - F n x₀ := by
    refine (hu.mul_right ‖x - x₀‖).of_norm_bounded ?_
    intro n
    simpa [mul_comm] using hdiff_bound n
  simpa [sub_add_cancel] using hdiff.add hF0

theorem hasDerivWithinAt_tsum
    {F F' : ℕ → ℝ → ℝ} {s : Set ℝ} (hs : Convex ℝ s)
    {u : ℕ → ℝ} (hu : Summable u)
    (hF : ∀ n, ∀ x ∈ s, HasDerivWithinAt (F n) (F' n x) s x)
    (hbound : ∀ n, ∀ x ∈ s, |F' n x| ≤ u n)
    {xbase : ℝ} (hxbase : xbase ∈ s)
    (hF0 : Summable fun n => F n xbase)
    {x₀ : ℝ} (hx₀ : x₀ ∈ s) :
    HasDerivWithinAt (fun y => ∑' n, F n y) (∑' n, F' n x₀) s x₀ := by
  have hsumF : ∀ x ∈ s, Summable fun n => F n x := fun x hx =>
    summable_of_summable_hasDerivWithinAt hs hu hF hbound hxbase hF0 hx
  have hsumF' : ∀ x ∈ s, Summable fun n => F' n x := by
    intro x hx
    refine hu.of_norm_bounded ?_
    intro n
    simpa [Real.norm_eq_abs] using hbound n x hx
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hterm :
      ∀ n, Tendsto (fun y => slope (F n) x₀ y) (𝓝[s \ {x₀}] x₀) (𝓝 (F' n x₀)) := by
    intro n
    exact hasDerivWithinAt_iff_tendsto_slope.mp (hF n x₀ hx₀)
  have hbound_slope :
      ∀ᶠ y in 𝓝[s \ {x₀}] x₀, ∀ n, ‖slope (F n) x₀ y‖ ≤ u n := by
    filter_upwards [self_mem_nhdsWithin] with y hy n
    have hy_s : y ∈ s := hy.1
    have hy_ne : y ≠ x₀ := by simpa using hy.2
    have hmvt :
        ‖F n y - F n x₀‖ ≤ u n * ‖y - x₀‖ := by
      simpa [Real.norm_eq_abs, norm_sub_rev] using
        hs.norm_image_sub_le_of_norm_hasDerivWithin_le
          (f := F n) (f' := fun z => F' n z) (C := u n)
          (hF n) (fun z hz => by simpa [Real.norm_eq_abs] using hbound n z hz)
          hx₀ hy_s
    have hpos : 0 < ‖y - x₀‖ := by
      rw [norm_pos_iff]
      exact sub_ne_zero.mpr hy_ne
    have habspos : 0 < |y - x₀| := by
      exact abs_pos.mpr (sub_ne_zero.mpr hy_ne)
    rw [slope_def_module, norm_smul, Real.norm_eq_abs, abs_inv,
      inv_mul_le_iff₀ habspos]
    simpa [Real.norm_eq_abs, mul_comm] using hmvt
  have htend :
      Tendsto (fun y => ∑' n, slope (F n) x₀ y) (𝓝[s \ {x₀}] x₀)
        (𝓝 (∑' n, F' n x₀)) :=
    tendsto_tsum_of_dominated_convergence hu hterm hbound_slope
  refine htend.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy_s : y ∈ s := hy.1
  have hFy := hsumF y hy_s
  have hFx := hsumF x₀ hx₀
  simp_rw [slope_def_module]
  rw [← hFy.tsum_sub hFx]
  exact (hFy.sub hFx).tsum_const_smul (y - x₀)⁻¹

end ShenWork.HasDerivWithinAtTsum
