import ShenWork.Paper1.WholeLineWeightedRegularityDuhamel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Filter MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Interpolation across a strict exponential-weight gap

Uniform convergence in `BUC` together with a bound at the same exponential
weight does not imply convergence in the weighted `L2` norm: weighted mass
can drift to the right.  A strict reserve `eta < etaPlus` repairs this.  The
left half-line is controlled by the uniform norm and the right half-line by
the stronger exponential weight.
-/

/-- Split-at-`R` interpolation between a uniform bound and a strictly
stronger exponential `L2` weight. -/
theorem weightedL2_le_of_sup_and_stronger_weight
    {eta etaPlus R D : ℝ}
    (heta : 0 < eta) (hgap : eta < etaPlus) (hD : 0 ≤ D)
    {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f volume)
    (hfD : ∀ x, |f x| ≤ D)
    (hstrong : Integrable
      (fun x : ℝ => Real.exp (2 * etaPlus * x) * |f x| ^ 2)) :
    Integrable (fun x : ℝ => Real.exp (2 * eta * x) * |f x| ^ 2) ∧
      (∫ x : ℝ, Real.exp (2 * eta * x) * |f x| ^ 2) ≤
        D ^ 2 * Real.exp (2 * eta * R) / (2 * eta) +
          Real.exp (-2 * (etaPlus - eta) * R) *
            (∫ x : ℝ, Real.exp (2 * etaPlus * x) * |f x| ^ 2) := by
  let weak : ℝ → ℝ := fun x => Real.exp (2 * eta * x) * |f x| ^ 2
  let strong : ℝ → ℝ := fun x =>
    Real.exp (2 * etaPlus * x) * |f x| ^ 2
  let leftMajor : ℝ → ℝ := fun x => D ^ 2 * Real.exp (2 * eta * x)
  let rightMajor : ℝ → ℝ := fun x =>
    Real.exp (-2 * (etaPlus - eta) * R) * strong x
  have hweak_meas : AEStronglyMeasurable weak volume := by
    have hsq : AEStronglyMeasurable (fun x => |f x| ^ 2) volume := by
      simpa only [Real.norm_eq_abs] using hf_meas.norm.pow 2
    exact ((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable.mul hsq)
  have hleftMajor : IntegrableOn leftMajor (Iic R) := by
    exact (integrableOn_exp_mul_Iic
      (by linarith : (0 : ℝ) < 2 * eta) R).const_mul (D ^ 2)
  have hleft_point : ∀ x ∈ Iic R, weak x ≤ leftMajor x := by
    intro x _hx
    have hsquare : |f x| ^ 2 ≤ D ^ 2 := by
      have hs := (sq_le_sq₀ (abs_nonneg (f x)) hD).2 (hfD x)
      simpa only [sq_abs] using hs
    dsimp only [weak, leftMajor]
    have hm : Real.exp (2 * eta * x) * |f x| ^ 2 ≤
        Real.exp (2 * eta * x) * D ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare (Real.exp_nonneg _)
    nlinarith
  have hleft : IntegrableOn weak (Iic R) := by
    refine hleftMajor.mono'
      (hweak_meas.mono_measure Measure.restrict_le_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    have hweak0 : 0 ≤ weak x := by dsimp only [weak]; positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hweak0] using
      hleft_point x hx
  have hrightMajorGlobal : Integrable rightMajor := by
    exact hstrong.const_mul (Real.exp (-2 * (etaPlus - eta) * R))
  have hrightMajor : IntegrableOn rightMajor (Ioi R) := by
    exact hrightMajorGlobal.mono_measure Measure.restrict_le_self
  have hright_point : ∀ x ∈ Ioi R, weak x ≤ rightMajor x := by
    intro x hx
    have hcoef : -2 * (etaPlus - eta) * x ≤
        -2 * (etaPlus - eta) * R := by
      have hneg : -2 * (etaPlus - eta) < 0 := by linarith
      exact mul_le_mul_of_nonpos_left hx.le hneg.le
    have hexp := Real.exp_le_exp.mpr hcoef
    have hsplit : Real.exp (2 * eta * x) =
        Real.exp (-2 * (etaPlus - eta) * x) *
          Real.exp (2 * etaPlus * x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp only [weak, rightMajor, strong]
    rw [hsplit]
    have htail0 : 0 ≤ Real.exp (2 * etaPlus * x) * |f x| ^ 2 := by
      positivity
    have hm :
        Real.exp (-2 * (etaPlus - eta) * x) *
            (Real.exp (2 * etaPlus * x) * |f x| ^ 2) ≤
          Real.exp (-2 * (etaPlus - eta) * R) *
            (Real.exp (2 * etaPlus * x) * |f x| ^ 2) :=
      mul_le_mul_of_nonneg_right hexp htail0
    simpa only [mul_assoc] using hm
  have hright : IntegrableOn weak (Ioi R) := by
    refine hrightMajor.mono'
      (hweak_meas.mono_measure Measure.restrict_le_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hweak0 : 0 ≤ weak x := by dsimp only [weak]; positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hweak0] using
      hright_point x hx
  have hcover : Iic R ∪ Ioi R = (Set.univ : Set ℝ) := Iic_union_Ioi
  have hweak : Integrable weak := by
    rw [← integrableOn_univ, ← hcover]
    exact hleft.union hright
  refine ⟨by simpa only [weak] using hweak, ?_⟩
  have hleft_bound : (∫ x in Iic R, weak x) ≤
      D ^ 2 * Real.exp (2 * eta * R) / (2 * eta) := by
    calc
      (∫ x in Iic R, weak x) ≤ ∫ x in Iic R, leftMajor x :=
        setIntegral_mono_on hleft hleftMajor measurableSet_Iic hleft_point
      _ = D ^ 2 * (Real.exp (2 * eta * R) / (2 * eta)) := by
        dsimp only [leftMajor]
        rw [integral_const_mul,
          integral_exp_mul_Iic (by linarith : (0 : ℝ) < 2 * eta) R]
      _ = D ^ 2 * Real.exp (2 * eta * R) / (2 * eta) := by ring
  have hright_bound : (∫ x in Ioi R, weak x) ≤
      Real.exp (-2 * (etaPlus - eta) * R) *
        (∫ x : ℝ, strong x) := by
    calc
      (∫ x in Ioi R, weak x) ≤ ∫ x in Ioi R, rightMajor x :=
        setIntegral_mono_on hright hrightMajor measurableSet_Ioi hright_point
      _ ≤ ∫ x : ℝ, rightMajor x := by
        exact integral_mono_measure
          (Measure.restrict_le_self)
          (Eventually.of_forall fun x => by
            dsimp only [rightMajor, strong]
            positivity)
          hrightMajorGlobal
      _ = Real.exp (-2 * (etaPlus - eta) * R) *
          (∫ x : ℝ, strong x) := by
        dsimp only [rightMajor]
        rw [integral_const_mul]
  have hsplitIntegral := intervalIntegral.integral_Iic_add_Ioi hleft hright
  change (∫ x : ℝ, weak x) ≤ _
  rw [← hsplitIntegral]
  change (∫ x in Iic R, weak x) + (∫ x in Ioi R, weak x) ≤ _
  exact add_le_add hleft_bound hright_bound

private theorem weightGap_right_factor_identity
    {eta etaPlus alpha delta : ℝ}
    (heta : 0 < eta) (hgap : eta < etaPlus)
    (halpha : 0 < alpha) (hdelta : 0 < delta) :
    Real.exp (-2 * (etaPlus - eta) *
        (-(alpha / etaPlus) * Real.log delta)) =
      delta ^ (2 * (alpha * (etaPlus - eta) / etaPlus)) := by
  have hetaPlus : etaPlus ≠ 0 := ne_of_gt (heta.trans hgap)
  rw [Real.rpow_def_of_pos hdelta]
  congr 1
  field_simp [hetaPlus]

private theorem weightGap_left_factor_identity
    {eta etaPlus alpha delta H : ℝ}
    (heta : 0 < eta) (hgap : eta < etaPlus)
    (halpha : 0 < alpha) (hdelta : 0 < delta) :
    (H * delta ^ alpha) ^ 2 *
        Real.exp (2 * eta *
          (-(alpha / etaPlus) * Real.log delta)) /
          (2 * eta) =
      (H ^ 2 / (2 * eta)) *
        delta ^ (2 * (alpha * (etaPlus - eta) / etaPlus)) := by
  have heta_ne : eta ≠ 0 := ne_of_gt heta
  have hetaPlus : etaPlus ≠ 0 := ne_of_gt (heta.trans hgap)
  rw [Real.rpow_def_of_pos hdelta,
    Real.rpow_def_of_pos hdelta]
  rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
  have hexp :
      Real.log delta * alpha + Real.log delta * alpha +
          2 * eta * (-(alpha / etaPlus) * Real.log delta) =
        Real.log delta * (2 * (alpha * (etaPlus - eta) / etaPlus)) := by
    field_simp [hetaPlus]
    ring
  rw [mul_assoc, ← Real.exp_add, hexp]
  field_simp [heta_ne]

/-- A quantitative `L∞`-to-weighted-`L2` interpolation estimate across a
strict exponential-weight gap.  The stronger weighted bound prevents mass
from escaping to the right, while the uniform Hölder modulus controls the
left half-line. -/
theorem weightedL2_holder_of_sup_holder_and_stronger_bound
    {eta etaPlus alpha H K : ℝ}
    (heta : 0 < eta) (hgap : eta < etaPlus)
    (halpha : 0 < alpha) (hH : 0 ≤ H)
    {F : ℝ → ℝ → ℝ}
    (hF_meas : ∀ s, AEStronglyMeasurable (F s) volume)
    (hstrong : ∀ s,
      Integrable
          (fun x : ℝ => Real.exp (2 * etaPlus * x) * |F s x| ^ 2) ∧
        (∫ x : ℝ, Real.exp (2 * etaPlus * x) * |F s x| ^ 2) ≤ K)
    (hsup : ∀ s t x, |F s x - F t x| ≤ H * |s - t| ^ alpha) :
    ∀ s t, 0 < |s - t| → |s - t| ≤ 1 →
      Integrable
          (fun x : ℝ =>
            Real.exp (2 * eta * x) * |F s x - F t x| ^ 2) ∧
        (∫ x : ℝ,
            Real.exp (2 * eta * x) * |F s x - F t x| ^ 2) ≤
          (H ^ 2 / (2 * eta) + 4 * K) *
            |s - t| ^
              (2 * (alpha * (etaPlus - eta) / etaPlus)) := by
  intro s t hdelta _hdelta_one
  let delta : ℝ := |s - t|
  let f : ℝ → ℝ := fun x => F s x - F t x
  let strongS : ℝ → ℝ := fun x =>
    Real.exp (2 * etaPlus * x) * |F s x| ^ 2
  let strongT : ℝ → ℝ := fun x =>
    Real.exp (2 * etaPlus * x) * |F t x| ^ 2
  let strongDiff : ℝ → ℝ := fun x =>
    Real.exp (2 * etaPlus * x) * |f x| ^ 2
  let strongMajor : ℝ → ℝ := fun x =>
    2 * strongS x + 2 * strongT x
  have hf_meas : AEStronglyMeasurable f volume :=
    (hF_meas s).sub (hF_meas t)
  have hstrongDiff_meas : AEStronglyMeasurable strongDiff volume := by
    have hsq : AEStronglyMeasurable (fun x => |f x| ^ 2) volume := by
      simpa only [Real.norm_eq_abs] using hf_meas.norm.pow 2
    exact ((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable.mul hsq)
  have hstrongMajor_int : Integrable strongMajor := by
    exact ((hstrong s).1.const_mul 2).add ((hstrong t).1.const_mul 2)
  have hstrongDiff_point : ∀ x, strongDiff x ≤ strongMajor x := by
    intro x
    have hsquare : |F s x - F t x| ^ 2 ≤
        2 * |F s x| ^ 2 + 2 * |F t x| ^ 2 := by
      rw [sq_abs, sq_abs, sq_abs]
      nlinarith [sq_nonneg (F s x + F t x)]
    have hm := mul_le_mul_of_nonneg_left hsquare
      (Real.exp_nonneg (2 * etaPlus * x))
    calc
      strongDiff x ≤
          Real.exp (2 * etaPlus * x) *
            (2 * |F s x| ^ 2 + 2 * |F t x| ^ 2) := by
        simpa only [strongDiff, f] using hm
      _ = strongMajor x := by
        dsimp only [strongMajor, strongS, strongT]
        ring
  have hstrongDiff_int : Integrable strongDiff := by
    refine hstrongMajor_int.mono' hstrongDiff_meas ?_
    filter_upwards with x
    have hnonneg : 0 ≤ strongDiff x := by
      dsimp only [strongDiff]
      positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using
      hstrongDiff_point x
  have hstrongDiff_bound : (∫ x : ℝ, strongDiff x) ≤ 4 * K := by
    calc
      (∫ x : ℝ, strongDiff x) ≤ ∫ x : ℝ, strongMajor x :=
        integral_mono hstrongDiff_int hstrongMajor_int
          hstrongDiff_point
      _ = 2 * (∫ x : ℝ, strongS x) +
          2 * (∫ x : ℝ, strongT x) := by
        dsimp only [strongMajor]
        rw [integral_add ((hstrong s).1.const_mul 2)
            ((hstrong t).1.const_mul 2),
          integral_const_mul, integral_const_mul]
      _ ≤ 2 * K + 2 * K := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hstrong s).2 (by positivity))
          (mul_le_mul_of_nonneg_left (hstrong t).2 (by positivity))
      _ = 4 * K := by ring
  have hD : 0 ≤ H * delta ^ alpha :=
    mul_nonneg hH (Real.rpow_nonneg (by
      dsimp only [delta]
      exact abs_nonneg _) _)
  have hsplit := weightedL2_le_of_sup_and_stronger_weight
    heta hgap hD hf_meas
    (fun x => by simpa only [f, delta] using hsup s t x)
    hstrongDiff_int
    (R := -(alpha / etaPlus) * Real.log delta)
  refine ⟨by simpa only [f] using hsplit.1, ?_⟩
  have hcoef : 0 ≤
      Real.exp (-2 * (etaPlus - eta) *
        (-(alpha / etaPlus) * Real.log delta)) := Real.exp_nonneg _
  calc
    (∫ x : ℝ,
        Real.exp (2 * eta * x) * |F s x - F t x| ^ 2) ≤
        (H * delta ^ alpha) ^ 2 *
              Real.exp (2 * eta *
                (-(alpha / etaPlus) * Real.log delta)) /
              (2 * eta) +
          Real.exp (-2 * (etaPlus - eta) *
              (-(alpha / etaPlus) * Real.log delta)) *
            (∫ x : ℝ, strongDiff x) := by
      simpa only [f] using hsplit.2
    _ ≤ (H * delta ^ alpha) ^ 2 *
              Real.exp (2 * eta *
                (-(alpha / etaPlus) * Real.log delta)) /
              (2 * eta) +
          Real.exp (-2 * (etaPlus - eta) *
              (-(alpha / etaPlus) * Real.log delta)) * (4 * K) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hstrongDiff_bound hcoef)
    _ = (H ^ 2 / (2 * eta) + 4 * K) *
          delta ^ (2 * (alpha * (etaPlus - eta) / etaPlus)) := by
      rw [weightGap_left_factor_identity heta hgap halpha hdelta,
        weightGap_right_factor_identity heta hgap halpha hdelta]
      ring
    _ = (H ^ 2 / (2 * eta) + 4 * K) *
          |s - t| ^ (2 * (alpha * (etaPlus - eta) / etaPlus)) := rfl

section AxiomAudit

#print axioms weightedL2_le_of_sup_and_stronger_weight
#print axioms weightedL2_holder_of_sup_holder_and_stronger_bound

end AxiomAudit

end ShenWork.Paper1
