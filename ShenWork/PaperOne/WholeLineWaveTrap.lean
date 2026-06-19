import ShenWork.Defs
import ShenWork.PaperOne.LocalUniformCompactness
import ShenWork.PaperOne.WholeLineExponentialBarriers
import Mathlib.Analysis.Convex.Basic

noncomputable section

open Filter Set
open scoped Topology

namespace ShenWork.PaperOne

def WaveTrap (κ κt D : ℝ) : Set (ℝ → ℝ) :=
  {u | (∀ x, lowerBarrier κ κt D x ≤ u x ∧ u x ≤ upperBarrier κ x) ∧
    Antitone u}

theorem waveTrap_mem_nonneg {κ κt D : ℝ} {u : ℝ → ℝ}
    (hu : u ∈ WaveTrap κ κt D) (x : ℝ) :
    0 ≤ u x :=
  le_trans (lowerBarrier_nonneg κ κt D x) (hu.1 x).1

theorem waveTrap_mem_le_one {κ κt D : ℝ} {u : ℝ → ℝ}
    (hu : u ∈ WaveTrap κ κt D) (x : ℝ) :
    u x ≤ 1 :=
  le_trans (hu.1 x).2 (upperBarrier_le_one κ x)

theorem waveTrap_bounded {κ κt D : ℝ} {u : ℝ → ℝ}
    (hu : u ∈ WaveTrap κ κt D) :
    IsBddFun u := by
  refine ⟨1, fun x => ?_⟩
  rw [abs_of_nonneg (waveTrap_mem_nonneg hu x)]
  exact waveTrap_mem_le_one hu x

theorem waveTrap_convex (κ κt D : ℝ) :
    Convex ℝ (WaveTrap κ κt D) := by
  rw [convex_iff_add_mem]
  intro u hu v hv a b ha hb hab
  constructor
  · intro x
    rcases hu.1 x with ⟨hu_lo, hu_hi⟩
    rcases hv.1 x with ⟨hv_lo, hv_hi⟩
    constructor
    · calc
        lowerBarrier κ κt D x =
            a * lowerBarrier κ κt D x + b * lowerBarrier κ κt D x := by
              rw [← add_mul, hab, one_mul]
        _ ≤ a * u x + b * v x :=
              add_le_add
                (mul_le_mul_of_nonneg_left hu_lo ha)
                (mul_le_mul_of_nonneg_left hv_lo hb)
        _ = (a • u + b • v) x := by simp
    · calc
        (a • u + b • v) x = a * u x + b * v x := by simp
        _ ≤ a * upperBarrier κ x + b * upperBarrier κ x :=
              add_le_add
                (mul_le_mul_of_nonneg_left hu_hi ha)
                (mul_le_mul_of_nonneg_left hv_hi hb)
        _ = upperBarrier κ x := by rw [← add_mul, hab, one_mul]
  · intro x y hxy
    have hle :
        a * u y + b * v y ≤ a * u x + b * v x :=
      add_le_add
        (mul_le_mul_of_nonneg_left (hu.2 hxy) ha)
        (mul_le_mul_of_nonneg_left (hv.2 hxy) hb)
    simpa using hle

theorem waveTrap_closed_locUnif {κ κt D : ℝ}
    {u : ℕ → ℝ → ℝ} {f : C(ℝ, ℝ)}
    (hu : ∀ n, u n ∈ WaveTrap κ κt D)
    (hlim : TendstoLocallyUniformly u f atTop) :
    ((f : C(ℝ, ℝ)) : ℝ → ℝ) ∈ WaveTrap κ κt D := by
  have hpt : ∀ x, Tendsto (fun n : ℕ => u n x) atTop (𝓝 (f x)) := by
    intro x
    exact (hlim.tendstoLocallyUniformlyOn).tendsto_at (mem_univ x)
  constructor
  · intro x
    constructor
    · exact le_of_tendsto_of_tendsto' tendsto_const_nhds (hpt x)
        (fun n => ((hu n).1 x).1)
    · exact le_of_tendsto' (hpt x) (fun n => ((hu n).1 x).2)
  · intro x y hxy
    exact le_of_tendsto_of_tendsto' (hpt y) (hpt x)
      (fun n => (hu n).2 hxy)

#print axioms waveTrap_mem_nonneg
#print axioms waveTrap_mem_le_one
#print axioms waveTrap_bounded
#print axioms waveTrap_convex
#print axioms waveTrap_closed_locUnif

end ShenWork.PaperOne
