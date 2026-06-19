import ShenWork.PaperOne.WholeLineMildMap

open MeasureTheory Filter Topology Real Set

noncomputable section

namespace ShenWork.PaperOne

/-!
Explicit positive-time generator calculations for the whole-line Gaussian heat
kernel.  The file closes the pointwise Gaussian heat equation and isolates the
remaining convolution-level Mathlib frontier without adding axioms.
-/

lemma heatKernel_eq_rpow_of_pos {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatKernel t x =
      (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) *
        Real.exp (-x ^ 2 / (4 * t)) := by
  unfold heatKernel
  have hpos : 0 < 4 * Real.pi * t := by positivity
  rw [Real.rpow_neg hpos.le, ← Real.sqrt_eq_rpow]
  ring

lemma heatKernel_time_hasDerivAt {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s : ℝ => heatKernel s x)
      (heatKernel t x * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) t := by
  let coeff : ℝ → ℝ := fun s => (4 * Real.pi * s) ^ (-(1 / 2 : ℝ))
  let arg : ℝ → ℝ := fun s => -x ^ 2 / (4 * s)
  have hlin : HasDerivAt (fun s : ℝ => 4 * Real.pi * s) (4 * Real.pi) t := by
    simpa using (hasDerivAt_const t (4 * Real.pi)).mul (hasDerivAt_id t)
  have hbase_ne : 4 * Real.pi * t ≠ 0 := by positivity
  have hcoeff : HasDerivAt coeff
      ((-(1 / 2 : ℝ)) * (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
        (4 * Real.pi)) t := by
    dsimp [coeff]
    convert hlin.rpow_const (p := (-(1 / 2 : ℝ))) (Or.inl hbase_ne) using 1
    ring_nf
  have hden : 4 * t ≠ 0 := by positivity
  have hdenDeriv : HasDerivAt (fun s : ℝ => 4 * s) 4 t := by
    simpa using (hasDerivAt_const t (4 : ℝ)).mul (hasDerivAt_id t)
  have hnum : HasDerivAt (fun _s : ℝ => -x ^ 2) 0 t :=
    hasDerivAt_const t (-x ^ 2)
  have harg : HasDerivAt arg (x ^ 2 / (4 * t ^ 2)) t := by
    dsimp [arg]
    have h := hnum.div hdenDeriv hden
    convert h using 1
    field_simp [hden]
    ring
  have hprod : HasDerivAt (fun s : ℝ => coeff s * Real.exp (arg s))
      (heatKernel t x * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) t := by
    have hraw := hcoeff.mul harg.exp
    convert hraw using 1
    dsimp [coeff, arg]
    rw [heatKernel_eq_rpow_of_pos ht x]
    have ht_ne : t ≠ 0 := ne_of_gt ht
    have h4pi_ne : 4 * Real.pi ≠ 0 := by positivity
    have h4pit_pos : 0 < 4 * Real.pi * t := by positivity
    have h4pit_ne : 4 * Real.pi * t ≠ 0 := ne_of_gt h4pit_pos
    rw [show (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) =
        (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) / (4 * Real.pi * t) by
      rw [show (-(3 / 2 : ℝ)) = (-(1 / 2 : ℝ)) - 1 by norm_num]
      rw [Real.rpow_sub h4pit_pos]
      rw [Real.rpow_one]]
    field_simp [ht_ne, h4pi_ne, h4pit_ne]
    ring
  refine hprod.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
  dsimp [coeff, arg]
  exact heatKernel_eq_rpow_of_pos hs x

lemma heatKernel_time_deriv {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (fun s : ℝ => heatKernel s x) t =
      heatKernel t x * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) :=
  (heatKernel_time_hasDerivAt ht x).deriv

lemma heatKernel_spatial_deriv_hasDerivAt {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt
      (fun z : ℝ => -(z / (2 * t)) * heatKernel t z)
      (heatKernel t x * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) x := by
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hlin : HasDerivAt (fun z : ℝ => -(z / (2 * t))) (-(1 / (2 * t))) x := by
    have h := (hasDerivAt_id x).div_const (2 * t)
    convert h.neg using 1
  have hker := heatKernel_hasDerivAt ht x
  have hraw := hlin.mul hker
  convert hraw using 1
  field_simp [ht_ne]
  ring

lemma heatKernel_second_spatial_deriv {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (deriv (fun z : ℝ => heatKernel t z)) x =
      heatKernel t x * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) := by
  have hderiv_eq :
      (fun z : ℝ => deriv (fun w : ℝ => heatKernel t w) z) =
      fun z : ℝ => -(z / (2 * t)) * heatKernel t z := by
    funext z
    exact deriv_heatKernel ht z
  change deriv (fun z : ℝ => deriv (fun w : ℝ => heatKernel t w) z) x =
    heatKernel t x * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t))
  rw [hderiv_eq]
  exact (heatKernel_spatial_deriv_hasDerivAt ht x).deriv

theorem gaussian_heat_eq {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (fun s : ℝ => heatKernel s x) t =
      deriv (deriv (fun z : ℝ => heatKernel t z)) x := by
  rw [heatKernel_time_deriv ht x, heatKernel_second_spatial_deriv ht x]

/-- The remaining convolution-level frontier needed for the heat generator. -/
def HeatSemigroupGeneratorConvolutionFrontier (f : ℝ → ℝ) (t x : ℝ) : Prop :=
  HasDerivAt (fun s : ℝ => heatSemigroup s f x)
    (deriv (deriv (fun z : ℝ => heatSemigroup t f z)) x) t

theorem modifiedSemigroup_time_hasDerivAt_of_convolution_frontier
    {f : ℝ → ℝ} {t x : ℝ}
    (hfrontier : HeatSemigroupGeneratorConvolutionFrontier f t x) :
    HasDerivAt (fun s : ℝ => modifiedSemigroup s f x)
      (deriv (deriv (fun z : ℝ => modifiedSemigroup t f z)) x -
        modifiedSemigroup t f x) t := by
  unfold modifiedSemigroup
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_id t).neg.exp
  have hraw := hexp.mul hfrontier
  convert hraw using 1
  have hconst₁ :
      deriv (fun z : ℝ => Real.exp (-t) * heatSemigroup t f z) =
        fun z : ℝ => Real.exp (-t) * deriv (fun y : ℝ => heatSemigroup t f y) z := by
    funext z
    rw [deriv_const_mul_field]
  rw [hconst₁]
  have hconst₂ :
      deriv (fun z : ℝ =>
          Real.exp (-t) * deriv (fun y : ℝ => heatSemigroup t f y) z) x =
        Real.exp (-t) *
          deriv (fun z : ℝ => deriv (fun y : ℝ => heatSemigroup t f y) z) x := by
    rw [deriv_const_mul_field]
  rw [hconst₂]
  ring

theorem wholeLineHeatOp_time_hasDerivAt_of_convolution_frontier
    {f : ℝ → ℝ} {t x : ℝ}
    (hfrontier : HeatSemigroupGeneratorConvolutionFrontier f t x) :
    HasDerivAt (fun s : ℝ => wholeLineHeatOp s f x)
      (deriv (deriv (fun z : ℝ => wholeLineHeatOp t f z)) x -
        wholeLineHeatOp t f x) t := by
  simpa [wholeLineHeatOp] using
    modifiedSemigroup_time_hasDerivAt_of_convolution_frontier
      (f := f) (t := t) (x := x) hfrontier

#print axioms gaussian_heat_eq
#print axioms modifiedSemigroup_time_hasDerivAt_of_convolution_frontier
#print axioms wholeLineHeatOp_time_hasDerivAt_of_convolution_frontier

end ShenWork.PaperOne
