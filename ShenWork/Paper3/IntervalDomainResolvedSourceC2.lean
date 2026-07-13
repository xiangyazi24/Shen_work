/- C1 gradient / elliptic-laplacian bridge for an arbitrary resolved source. -/
import ShenWork.Paper3.IntervalDomainResolvedSourceBounds
import ShenWork.PDE.IntervalResolverGradientBridge

namespace ShenWork.Paper3

open Real
open ShenWork.PDE
open ShenWork.IntervalResolverGradientBridge

noncomputable section

structure ResolvedSourceCoeffQuadraticDecay (a : ℕ → ℝ) where
  C : ℝ
  C_nonneg : 0 ≤ C
  decay : ∀ k : ℕ, 1 ≤ k →
    |a k| ≤ C / ((k : ℝ) * Real.pi) ^ 2

theorem ResolvedSourceCoeffQuadraticDecay.abs_summable
    {a : ℕ → ℝ} (H : ResolvedSourceCoeffQuadraticDecay a) :
    Summable fun k => |a k| := by
  rw [← summable_nat_add_iff 1]
  have hp : Summable fun k : ℕ =>
      (H.C / Real.pi ^ 2) * (1 / ((k : ℝ) + 1) ^ 2) := by
    have hs : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
      have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      simpa using
        (summable_nat_add_iff (f := fun k : ℕ => 1 / (k : ℝ) ^ 2) 1).2 h
    exact hs.mul_left _
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) ?_ hp
  intro k
  have hk : 1 ≤ k + 1 := Nat.le_add_left 1 k
  have hd := H.decay (k + 1) hk
  have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by norm_num
  rw [hcast] at hd
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  calc
    |a (k + 1)| ≤ H.C / (((k : ℝ) + 1) * Real.pi) ^ 2 := hd
    _ = (H.C / Real.pi ^ 2) * (1 / ((k : ℝ) + 1) ^ 2) := by
      field_simp
      <;> ring

def paper3ResolvedSourceCoeff
    (p : CM2Params) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  a k / (p.μ + unitIntervalNeumannSpectrum.eigenvalue k)

def paper3ResolvedSourceSourceValue (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, a k * Real.cos ((k : ℝ) * Real.pi * x)

def paper3ResolvedSourceLaplacian
    (p : CM2Params) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, paper3ResolvedSourceCoeff p a k *
    (-(((k : ℝ) * Real.pi) ^ 2) *
      Real.cos ((k : ℝ) * Real.pi * x))

theorem paper3ResolvedSourceCoeff_grad2_summable
    (p : CM2Params) {a : ℕ → ℝ}
    (H : ResolvedSourceCoeffQuadraticDecay a) :
    Summable fun k : ℕ =>
      |paper3ResolvedSourceCoeff p a k| * ((k : ℝ) * Real.pi) ^ 2 := by
  have ha := H.abs_summable
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    ?_ ha
  intro k
  have hden : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue k :=
    ShenWork.PDE.intervalNeumannResolver_denom_pos p k
  have hlam : unitIntervalNeumannSpectrum.eigenvalue k =
      ((k : ℝ) * Real.pi) ^ 2 := by
    simp [unitIntervalNeumannSpectrum]
    ring
  have hlambda : ((k : ℝ) * Real.pi) ^ 2 ≤
      p.μ + unitIntervalNeumannSpectrum.eigenvalue k := by
    rw [hlam]
    linarith [p.hμ.le]
  rw [paper3ResolvedSourceCoeff, abs_div, abs_of_pos hden]
  calc
    |a k| / (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) *
        ((k : ℝ) * Real.pi) ^ 2 ≤
      |a k| / (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) *
        (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) :=
      mul_le_mul_of_nonneg_left hlambda (div_nonneg (abs_nonneg _) hden.le)
    _ = |a k| := by field_simp [hden.ne']

theorem paper3ResolvedSourceGradient_hasDerivAt_laplacian
    (p : CM2Params) {a : ℕ → ℝ}
    (H : ResolvedSourceCoeffQuadraticDecay a) (x : ℝ) :
    HasDerivAt (paper3ResolvedSourceGradient p a)
      (paper3ResolvedSourceLaplacian p a x) x := by
  have hder := sineSeries_hasDerivAt_of_grad2Summable
    (c := paper3ResolvedSourceCoeff p a)
    (paper3ResolvedSourceCoeff_grad2_summable p H) x
  convert hder using 1
  · funext y
    unfold paper3ResolvedSourceGradient
    apply tsum_congr
    intro k
    rw [paper3ResolvedSourceCoeff,
      ShenWork.PDE.intervalNeumannResolverGradWeight]
    ring

theorem paper3ResolvedSourceLaplacian_eq_elliptic
    (p : CM2Params) {a : ℕ → ℝ}
    (H : ResolvedSourceCoeffQuadraticDecay a) (x : ℝ) :
    paper3ResolvedSourceLaplacian p a x =
      p.μ * paper3ResolvedSourceValue p a x -
        paper3ResolvedSourceSourceValue a x := by
  have ha := H.abs_summable
  have hsource : Summable fun k : ℕ =>
      a k * Real.cos ((k : ℝ) * Real.pi * x) := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) ?_ ha
    intro k
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have hlapAbs := paper3ResolvedSourceCoeff_grad2_summable p H
  have hlap : Summable fun k : ℕ =>
      paper3ResolvedSourceCoeff p a k *
        (-(((k : ℝ) * Real.pi) ^ 2) *
          Real.cos ((k : ℝ) * Real.pi * x)) := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) ?_ hlapAbs
    intro k
    have hsabs : |((k : ℝ) * Real.pi) ^ 2| =
        ((k : ℝ) * Real.pi) ^ 2 := abs_of_nonneg (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, hsabs]
    have hc := Real.abs_cos_le_one ((k : ℝ) * Real.pi * x)
    calc
      |paper3ResolvedSourceCoeff p a k| *
          (((k : ℝ) * Real.pi) ^ 2 *
            |Real.cos ((k : ℝ) * Real.pi * x)|) ≤
        |paper3ResolvedSourceCoeff p a k| *
          (((k : ℝ) * Real.pi) ^ 2 * 1) := by gcongr
      _ = _ := by ring
  have hvalue : Summable fun k : ℕ =>
      a k * ShenWork.PDE.intervalNeumannResolverWeight p k *
        unitIntervalCosineMode k x := by
    apply Summable.of_norm
    have hmajor := ha.mul_left (1 / p.μ)
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) ?_ hmajor
    intro k
    have hden : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue k :=
      ShenWork.PDE.intervalNeumannResolver_denom_pos p k
    have hmuDen : p.μ ≤ p.μ + unitIntervalNeumannSpectrum.eigenvalue k := by
      linarith [unitIntervalNeumannSpectrum_hasNeumannSpectrum.eigenvalue_nonneg k]
    have hw : ShenWork.PDE.intervalNeumannResolverWeight p k ≤ 1 / p.μ := by
      unfold ShenWork.PDE.intervalNeumannResolverWeight
      exact one_div_le_one_div_of_le p.hμ hmuDen
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (ShenWork.PDE.intervalNeumannResolverWeight_nonneg p k)]
    unfold unitIntervalCosineMode
    have hcoef0 : 0 ≤ |a k| * (1 / p.μ) :=
      mul_nonneg (abs_nonneg _) (one_div_nonneg.mpr p.hμ.le)
    calc
      |a k| * ShenWork.PDE.intervalNeumannResolverWeight p k *
          |unitIntervalCosineMode k x| ≤
        |a k| * (1 / p.μ) * |Real.cos ((k : ℝ) * Real.pi * x)| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hw (abs_nonneg _)) (abs_nonneg _)
      _ ≤ |a k| * (1 / p.μ) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hcoef0
      _ = (1 / p.μ) * |a k| := by ring
  have hterm : ∀ k : ℕ,
      paper3ResolvedSourceCoeff p a k *
          (-(((k : ℝ) * Real.pi) ^ 2) *
            Real.cos ((k : ℝ) * Real.pi * x)) =
        p.μ * (a k * ShenWork.PDE.intervalNeumannResolverWeight p k *
          unitIntervalCosineMode k x) -
          a k * Real.cos ((k : ℝ) * Real.pi * x) := by
    intro k
    have hden : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue k :=
      ShenWork.PDE.intervalNeumannResolver_denom_pos p k
    have hlam : unitIntervalNeumannSpectrum.eigenvalue k =
        ((k : ℝ) * Real.pi) ^ 2 := by
      simp [unitIntervalNeumannSpectrum]
      ring
    unfold paper3ResolvedSourceCoeff
      ShenWork.PDE.intervalNeumannResolverWeight unitIntervalCosineMode
    rw [← hlam]
    field_simp [hden.ne']
    ring
  unfold paper3ResolvedSourceLaplacian paper3ResolvedSourceValue
    paper3ResolvedSourceSourceValue
  rw [tsum_congr hterm]
  have hmuValue := hvalue.mul_left p.μ
  rw [hmuValue.tsum_sub hsource, tsum_mul_left]

theorem paper3ResolvedSourceGradient_hasDerivAt_elliptic
    (p : CM2Params) {a : ℕ → ℝ}
    (H : ResolvedSourceCoeffQuadraticDecay a)
    {f : ℝ → ℝ}
    (hreconstruct : ∀ x, paper3ResolvedSourceSourceValue a x = f x)
    (x : ℝ) :
    HasDerivAt (paper3ResolvedSourceGradient p a)
      (p.μ * paper3ResolvedSourceValue p a x - f x) x := by
  rw [← hreconstruct x, ← paper3ResolvedSourceLaplacian_eq_elliptic p H x]
  exact paper3ResolvedSourceGradient_hasDerivAt_laplacian p H x

#print axioms ResolvedSourceCoeffQuadraticDecay.abs_summable
#print axioms paper3ResolvedSourceGradient_hasDerivAt_laplacian
#print axioms paper3ResolvedSourceLaplacian_eq_elliptic
#print axioms paper3ResolvedSourceGradient_hasDerivAt_elliptic

end

end ShenWork.Paper3
