/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import ShenWork.Liang.ScalarPersistence
import ShenWork.Liang.MovingCorridor
import Mathlib.Analysis.Convolution

/-!
# Finite-block lower spreading certificates

A one-generation box argument sees at most half of a probability kernel at
one of the two expanding endpoints.  That is why the fixed-floor certificate
in `ScalarPersistence` forces an artificial growth threshold.

This file supplies the correct reusable interface for a multigeneration
argument.  On a sufficiently small density range, the nonlinear corrected
response dominates a linear growth-and-dispersal recursion.  A
`FiniteBlockCertificate` is then a statement only about a finite iterate of
that linear recursion.  It can collect contributions from all dispersal paths
inside the block, rather than retaining a single endpoint window at each
generation.

The construction below is fully nonlinear once a finite linear certificate
has been supplied.  Proving such certificates from convolution powers, and
ultimately from the variational speed formula, is kept as a separate analytic
problem.
-/

open Filter MeasureTheory Set Topology
open scoped Convolution

namespace ShenWork.Liang

noncomputable section

/-! ## Low-density linear lower bound -/

/-- Uniform low-density slope in a favorable environment with competitor
bounded by `δ`, evaluated at the top `η` of the linearization range. -/
def favorableLowerSlope (ρ α δ η : ℝ) : ℝ :=
  (1 + ρ) / (1 + ρ * (η + α * δ))

theorem favorableLowerSlope_pos
    {ρ α δ η : ℝ}
    (hρ : 0 ≤ ρ) (hα : 0 ≤ α)
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) :
    0 < favorableLowerSlope ρ α δ η := by
  unfold favorableLowerSlope
  positivity

/-- The low-density slope is supercritical precisely below the perturbed
nullcline. -/
theorem one_lt_favorableLowerSlope
    {ρ α δ η : ℝ}
    (hρ : 0 < ρ) (hα : 0 ≤ α)
    (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hsmall : η + α * δ < 1) :
    1 < favorableLowerSlope ρ α δ η := by
  have hden : 0 < 1 + ρ * (η + α * δ) := by positivity
  unfold favorableLowerSlope
  apply (lt_div_iff₀ hden).2
  have hmul :=
    mul_lt_mul_of_pos_left hsmall hρ
  nlinarith

/-- On `[0,η]`, the favorable corrected response dominates every linear
slope below `favorableLowerSlope`. -/
theorem linear_mul_le_correctedResponse
    {ρ α δ η slope z : ℝ}
    (hρ : 0 < ρ) (hα : 0 ≤ α)
    (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hslope : 0 ≤ slope)
    (hslope_le : slope ≤ favorableLowerSlope ρ α δ η)
    (hz : 0 ≤ z) (hzη : z ≤ η) :
    slope * z ≤ correctedResponse ρ α z δ := by
  have hdenη : 0 < 1 + ρ * (η + α * δ) := by positivity
  have hdenz : 0 < 1 + ρ * (z + α * δ) := by positivity
  have hdenle :
      1 + ρ * (z + α * δ) ≤
        1 + ρ * (η + α * δ) := by
    gcongr
  have hslope_cross :
      slope * (1 + ρ * (η + α * δ)) ≤ 1 + ρ := by
    exact (le_div_iff₀ hdenη).mp hslope_le
  rw [correctedResponse_eq_localResponse_of_nonneg hρ.le]
  unfold localResponse
  apply (le_div_iff₀ hdenz).2
  have hscaledDen :
      (slope * z) * (1 + ρ * (z + α * δ)) ≤
        (slope * z) * (1 + ρ * (η + α * δ)) :=
    mul_le_mul_of_nonneg_left hdenle (mul_nonneg hslope hz)
  have hscaledSlope :
      z * (slope * (1 + ρ * (η + α * δ))) ≤
        z * (1 + ρ) :=
    mul_le_mul_of_nonneg_left hslope_cross hz
  nlinarith

/-! ## Linear block dynamics -/

/-- A constant floor on a compact interval, extended by zero. -/
def intervalFloor (seed L R x : ℝ) : ℝ :=
  if x ∈ Set.Icc L R then seed else 0

theorem intervalFloor_nonneg
    {seed L R x : ℝ} (hseed : 0 ≤ seed) :
    0 ≤ intervalFloor seed L R x := by
  unfold intervalFloor
  split_ifs <;> positivity

theorem intervalFloor_le_seed
    {seed L R x : ℝ} (hseed : 0 ≤ seed) :
    intervalFloor seed L R x ≤ seed := by
  unfold intervalFloor
  split_ifs <;> simp [hseed]

/-- Linear growth-and-dispersal orbit from an arbitrary initial profile. -/
def finiteLinearOrbit
    (K : ℝ → ℝ) (slope : ℝ) (f : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => f
  | n + 1 =>
      ShenWork.Analysis.linearDispersalStep K slope
        (finiteLinearOrbit K slope f n)

@[simp]
theorem finiteLinearOrbit_zero
    (K : ℝ → ℝ) (slope : ℝ) (f : ℝ → ℝ) :
    finiteLinearOrbit K slope f 0 = f :=
  rfl

@[simp]
theorem finiteLinearOrbit_succ
    (K : ℝ → ℝ) (slope : ℝ) (f : ℝ → ℝ) (n : ℕ) :
    finiteLinearOrbit K slope f (n + 1) =
      ShenWork.Analysis.linearDispersalStep K slope
        (finiteLinearOrbit K slope f n) :=
  rfl

/-- A finite, purely linear certificate.  The last field is the substantive
convolution-power estimate.  The other fields record the bounds and
integrability needed to insert that estimate below the nonlinear IDE. -/
structure FiniteBlockCertificate
    (K : ℝ → ℝ) (slope η seed : ℝ) (block : ℕ)
    (leftAdvance rightAdvance minWidth : ℝ) : Prop where
  seed_pos : 0 < seed
  seed_le_eta : seed ≤ η
  linear_nonneg :
    ∀ L R, minWidth ≤ R - L →
      ∀ t, t ≤ block → ∀ x,
        0 ≤ finiteLinearOrbit K slope
          (intervalFloor seed L R) t x
  linear_le_eta :
    ∀ L R, minWidth ≤ R - L →
      ∀ t, t ≤ block → ∀ x,
        finiteLinearOrbit K slope
          (intervalFloor seed L R) t x ≤ η
  linear_integrable :
    ∀ L R, minWidth ≤ R - L →
      ∀ t, t < block → ∀ x,
        Integrable
          (fun y =>
            K (x - y) *
              (slope * finiteLinearOrbit K slope
                (intervalFloor seed L R) t y))
  expands_floor :
    ∀ L R, minWidth ≤ R - L →
      ∀ x ∈ Set.Icc
        (L + leftAdvance) (R + rightAdvance),
        seed ≤ finiteLinearOrbit K slope
          (intervalFloor seed L R) block x

/-! ## Reducing the expansion check to one reference interval -/

theorem intervalFloor_mono_of_Icc_subset
    {seed L₁ R₁ L₂ R₂ x : ℝ}
    (hseed : 0 ≤ seed)
    (hsubset : Set.Icc L₁ R₁ ⊆ Set.Icc L₂ R₂) :
    intervalFloor seed L₁ R₁ x ≤
      intervalFloor seed L₂ R₂ x := by
  by_cases hx : x ∈ Set.Icc L₁ R₁
  · rw [intervalFloor, if_pos hx, intervalFloor, if_pos (hsubset hx)]
  · rw [intervalFloor, if_neg hx]
    exact intervalFloor_nonneg hseed

theorem intervalFloor_translate
    (seed W h x : ℝ) :
    intervalFloor seed h (h + W) (x + h) =
      intervalFloor seed 0 W x := by
  have hmem :
      x + h ∈ Set.Icc h (h + W) ↔ x ∈ Set.Icc 0 W := by
    simp only [Set.mem_Icc]
    constructor
    · intro hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · intro hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  unfold intervalFloor
  by_cases hx : x ∈ Set.Icc 0 W
  · rw [if_pos hx, if_pos (hmem.mpr hx)]
  · rw [if_neg hx, if_neg (fun h => hx (hmem.mp h))]

/-- Linear dispersal commutes with spatial translation. -/
theorem finiteLinearOrbit_translate
    (K : ℝ → ℝ) (slope : ℝ) (f : ℝ → ℝ) (h : ℝ) :
    ∀ n x,
      finiteLinearOrbit K slope (fun y => f (y - h)) n (x + h) =
        finiteLinearOrbit K slope f n x := by
  intro n
  induction n with
  | zero =>
      intro x
      simp
  | succ n ih =>
      intro x
      rw [finiteLinearOrbit_succ, finiteLinearOrbit_succ]
      unfold ShenWork.Analysis.linearDispersalStep
      apply congrArg (fun q => slope * q)
      rw [ShenWork.Analysis.dispersal_eq_shift,
        ShenWork.Analysis.dispersal_eq_shift]
      apply integral_congr_ae
      filter_upwards [] with z
      apply congrArg (fun q => K z * q)
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        ih (x - z)

theorem finiteLinearOrbit_interval_translate
    (K : ℝ → ℝ) (slope seed W h : ℝ) (n : ℕ) (x : ℝ) :
    finiteLinearOrbit K slope
        (intervalFloor seed h (h + W)) n (x + h) =
      finiteLinearOrbit K slope
        (intervalFloor seed 0 W) n x := by
  have hprofile :
      intervalFloor seed h (h + W) =
        fun y => intervalFloor seed 0 W (y - h) := by
    funext y
    simpa using intervalFloor_translate seed W h (y - h)
  rw [hprofile]
  exact finiteLinearOrbit_translate K slope
    (intervalFloor seed 0 W) h n x

theorem intervalFloor_integrable
    (seed L R : ℝ) :
    Integrable (intervalFloor seed L R) := by
  have hconst :
      IntegrableOn (fun _ : ℝ => seed) (Set.Icc L R) :=
    continuousOn_const.integrableOn_Icc
  have hindicator :=
    hconst.integrable_indicator measurableSet_Icc
  apply hindicator.congr
  filter_upwards [] with x
  simp only [Set.indicator, intervalFloor]

/-- The total mass of an interval floor is its height times its width. -/
theorem integral_intervalFloor
    {seed L R : ℝ} (hLR : L ≤ R) :
    ∫ x, intervalFloor seed L R x = seed * (R - L) := by
  have hprofile :
      intervalFloor seed L R =
        (Set.Icc L R).indicator (fun _ : ℝ => seed) := by
    funext x
    simp [intervalFloor, Set.indicator]
  rw [hprofile,
    MeasureTheory.integral_indicator_const seed measurableSet_Icc]
  simp [MeasureTheory.measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hLR), smul_eq_mul]
  ring

/-- `dispersal K f` is the ordinary scalar convolution `f ⋆ K`. -/
theorem dispersal_eq_convolution_mul
    (K f : ℝ → ℝ) :
    ShenWork.Analysis.dispersal K f =
      f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] K := by
  funext x
  unfold ShenWork.Analysis.dispersal
  rw [MeasureTheory.convolution_def]
  apply integral_congr_ae
  filter_upwards [] with y
  simp [mul_comm]

/-- Integrability of the kernel and initial profile propagates through every
finite linear iterate. -/
theorem finiteLinearOrbit_integrable
    {K f : ℝ → ℝ} {slope : ℝ}
    (hKint : Integrable K) (hfint : Integrable f) :
    ∀ n, Integrable (finiteLinearOrbit K slope f n) := by
  intro n
  induction n with
  | zero =>
      simpa using hfint
  | succ n ih =>
      rw [finiteLinearOrbit_succ]
      unfold ShenWork.Analysis.linearDispersalStep
      rw [dispersal_eq_convolution_mul]
      exact (ih.integrable_convolution
        (ContinuousLinearMap.mul ℝ ℝ) hKint).const_mul slope

/-- A unit-mass kernel preserves total mass under dispersal, so the total
mass of the linear orbit grows by the exact scalar factor `slope ^ n`. -/
theorem integral_finiteLinearOrbit
    {K f : ℝ → ℝ} {slope : ℝ}
    (hKint : Integrable K) (hKmass : ∫ z, K z = 1)
    (hfint : Integrable f) :
    ∀ n,
      ∫ x, finiteLinearOrbit K slope f n x =
        slope ^ n * ∫ x, f x := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [finiteLinearOrbit_succ]
      unfold ShenWork.Analysis.linearDispersalStep
      rw [integral_const_mul, dispersal_eq_convolution_mul,
        MeasureTheory.integral_convolution
          (ContinuousLinearMap.mul ℝ ℝ)
          (finiteLinearOrbit_integrable hKint hfint n) hKint,
        hKmass, ih]
      simp
      ring

/-- For interval data, the exact total mass of the linear orbit is the
initial height times the interval width, multiplied by `slope ^ n`. -/
theorem integral_finiteLinearOrbit_intervalFloor
    {K : ℝ → ℝ} {slope seed L R : ℝ}
    (hKint : Integrable K) (hKmass : ∫ z, K z = 1)
    (hLR : L ≤ R) :
    ∀ n,
      ∫ x, finiteLinearOrbit K slope (intervalFloor seed L R) n x =
        slope ^ n * seed * (R - L) := by
  intro n
  rw [integral_finiteLinearOrbit hKint hKmass
    (intervalFloor_integrable seed L R) n,
    integral_intervalFloor hLR]
  ring

/-- The linear orbit is homogeneous in its initial profile. -/
theorem finiteLinearOrbit_const_mul
    (K : ℝ → ℝ) (slope a : ℝ) (f : ℝ → ℝ) :
    ∀ n x,
      finiteLinearOrbit K slope (fun y => a * f y) n x =
        a * finiteLinearOrbit K slope f n x := by
  intro n
  induction n with
  | zero =>
      intro x
      rfl
  | succ n ih =>
      intro x
      rw [finiteLinearOrbit_succ, finiteLinearOrbit_succ]
      unfold ShenWork.Analysis.linearDispersalStep
      rw [show finiteLinearOrbit K slope
          (fun y => a * f y) n =
            fun y => a * finiteLinearOrbit K slope f n y by
        funext y
        exact ih y]
      rw [ShenWork.Analysis.dispersal_const_mul]
      ring

theorem intervalFloor_eq_seed_mul_unit
    (seed L R : ℝ) :
    intervalFloor seed L R =
      fun x => seed * intervalFloor 1 L R x := by
  funext x
  by_cases hx : x ∈ Set.Icc L R <;>
    simp [intervalFloor, hx]

/-- Scaling the height of an interval seed scales every later linear
iterate by exactly the same factor. -/
theorem finiteLinearOrbit_interval_scale
    (K : ℝ → ℝ) (slope seed L R : ℝ) :
    ∀ n x,
      finiteLinearOrbit K slope
          (intervalFloor seed L R) n x =
        seed * finiteLinearOrbit K slope
          (intervalFloor 1 L R) n x := by
  rw [intervalFloor_eq_seed_mul_unit]
  exact finiteLinearOrbit_const_mul K slope seed
    (intervalFloor 1 L R)

/-- Pointwise order of initial profiles propagates through a finite linear
orbit.  The integrability assumptions match the exact form stored in
`FiniteBlockCertificate`. -/
theorem finiteLinearOrbit_mono_of_integrable
    {K f g : ℝ → ℝ} {slope : ℝ}
    (hK : ∀ z, 0 ≤ K z) (hslope : 0 ≤ slope)
    (hfg : ∀ x, f x ≤ g x) :
    ∀ n,
      (∀ t, t < n → ∀ x,
        Integrable
          (fun y =>
            K (x - y) *
              (slope * finiteLinearOrbit K slope f t y))) →
      (∀ t, t < n → ∀ x,
        Integrable
          (fun y =>
            K (x - y) *
              (slope * finiteLinearOrbit K slope g t y))) →
      ∀ x,
        finiteLinearOrbit K slope f n x ≤
          finiteLinearOrbit K slope g n x := by
  intro n
  induction n with
  | zero =>
      intro _hfint _hgint x
      simpa using hfg x
  | succ n ih =>
      intro hfint hgint x
      rw [finiteLinearOrbit_succ, finiteLinearOrbit_succ]
      unfold ShenWork.Analysis.linearDispersalStep
      rw [← ShenWork.Analysis.dispersal_const_mul,
        ← ShenWork.Analysis.dispersal_const_mul]
      unfold ShenWork.Analysis.dispersal
      apply integral_mono (hfint n (by omega) x) (hgint n (by omega) x)
      intro y
      apply mul_le_mul_of_nonneg_left _ (hK (x - y))
      exact mul_le_mul_of_nonneg_left
        (ih
          (fun t ht => hfint t (by omega))
          (fun t ht => hgint t (by omega)) y)
        hslope

/-- Nonnegative kernels and slopes preserve nonnegativity throughout the
finite linear recursion. -/
theorem finiteLinearOrbit_nonneg
    {K f : ℝ → ℝ} {slope : ℝ}
    (hK : ∀ z, 0 ≤ K z) (hslope : 0 ≤ slope)
    (hf : ∀ x, 0 ≤ f x) :
    ∀ n x, 0 ≤ finiteLinearOrbit K slope f n x := by
  intro n
  induction n with
  | zero =>
      intro x
      simpa using hf x
  | succ n ih =>
      intro x
      rw [finiteLinearOrbit_succ]
      unfold ShenWork.Analysis.linearDispersalStep
      exact mul_nonneg hslope <|
        integral_nonneg fun y =>
          mul_nonneg (hK (x - y)) (ih y)

/-- With unit kernel mass, a finite linear orbit is bounded above by the
corresponding scalar geometric orbit. -/
theorem finiteLinearOrbit_le_pow_mul
    {K f : ℝ → ℝ} {slope seed : ℝ}
    (hKint : Integrable K)
    (hKmass : ∫ z, K z = 1)
    (hK : ∀ z, 0 ≤ K z)
    (hslope : 0 ≤ slope)
    (hf : ∀ x, f x ≤ seed) :
    ∀ n,
      (∀ t, t < n → ∀ x,
        Integrable
          (fun y =>
            K (x - y) *
              (slope * finiteLinearOrbit K slope f t y))) →
      ∀ x,
        finiteLinearOrbit K slope f n x ≤ slope ^ n * seed := by
  intro n
  induction n with
  | zero =>
      intro _hint x
      simpa using hf x
  | succ n ih =>
      intro hint x
      rw [finiteLinearOrbit_succ]
      unfold ShenWork.Analysis.linearDispersalStep
      rw [← ShenWork.Analysis.dispersal_const_mul]
      unfold ShenWork.Analysis.dispersal
      calc
        (∫ y,
            K (x - y) *
              (slope * finiteLinearOrbit K slope f n y)) ≤
            ∫ y,
              K (x - y) *
                (slope * (slope ^ n * seed)) := by
          apply integral_mono
            (hint n (by omega) x)
            ((hKint.comp_sub_left x).mul_const
              (slope * (slope ^ n * seed)))
          intro y
          apply mul_le_mul_of_nonneg_left _ (hK (x - y))
          exact mul_le_mul_of_nonneg_left
            (ih (fun t ht => hint t (by omega)) y) hslope
        _ = slope ^ (n + 1) * seed := by
          rw [integral_mul_const,
            integral_sub_left_eq_self K (volume : Measure ℝ) x,
            hKmass]
          ring

/-- For an interval seed, integrability of every comparison integrand and the
scalar power upper bound are automatic from an integrable nonnegative
unit-mass kernel. -/
theorem finiteLinearOrbit_interval_bound_and_integrable
    {K : ℝ → ℝ} {slope seed L R : ℝ}
    (hKint : Integrable K)
    (hKmass : ∫ z, K z = 1)
    (hK : ∀ z, 0 ≤ K z)
    (hslope : 0 ≤ slope)
    (hseed : 0 ≤ seed) :
    ∀ t,
      (∀ x,
        finiteLinearOrbit K slope
          (intervalFloor seed L R) t x ≤
            slope ^ t * seed) ∧
      ∀ x,
        Integrable
          (fun y =>
            K (x - y) *
              (slope * finiteLinearOrbit K slope
                (intervalFloor seed L R) t y)) := by
  have horbit_nonneg :
      ∀ t x,
        0 ≤ finiteLinearOrbit K slope
          (intervalFloor seed L R) t x :=
    finiteLinearOrbit_nonneg hK hslope
      (fun x => intervalFloor_nonneg hseed)
  have horbit_integrable :
      ∀ t,
        Integrable
          (finiteLinearOrbit K slope
            (intervalFloor seed L R) t) :=
    finiteLinearOrbit_integrable hKint
      (intervalFloor_integrable seed L R)
  intro t
  induction t with
  | zero =>
      constructor
      · intro x
        simpa using intervalFloor_le_seed (x := x) hseed
      · intro x
        apply (hKint.comp_sub_left x).mul_bdd
          ((horbit_integrable 0).const_mul slope).aestronglyMeasurable
        filter_upwards [] with y
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg hslope (horbit_nonneg 0 y))]
        have hupper :=
          intervalFloor_le_seed
            (L := L) (R := R) (x := y) hseed
        simpa using mul_le_mul_of_nonneg_left hupper hslope
  | succ t ih =>
      have hupper :
          ∀ x,
            finiteLinearOrbit K slope
              (intervalFloor seed L R) (t + 1) x ≤
                slope ^ (t + 1) * seed := by
        intro x
        rw [finiteLinearOrbit_succ]
        unfold ShenWork.Analysis.linearDispersalStep
        rw [← ShenWork.Analysis.dispersal_const_mul]
        unfold ShenWork.Analysis.dispersal
        calc
          (∫ y,
              K (x - y) *
                (slope * finiteLinearOrbit K slope
                  (intervalFloor seed L R) t y)) ≤
              ∫ y,
                K (x - y) *
                  (slope * (slope ^ t * seed)) := by
            apply integral_mono (ih.2 x)
              ((hKint.comp_sub_left x).mul_const
                (slope * (slope ^ t * seed)))
            intro y
            apply mul_le_mul_of_nonneg_left _ (hK (x - y))
            exact mul_le_mul_of_nonneg_left (ih.1 y) hslope
          _ = slope ^ (t + 1) * seed := by
            rw [integral_mul_const,
              integral_sub_left_eq_self K (volume : Measure ℝ) x,
              hKmass]
            ring
      refine ⟨hupper, ?_⟩
      intro x
      apply (hKint.comp_sub_left x).mul_bdd
        ((horbit_integrable (t + 1)).const_mul slope).aestronglyMeasurable
      filter_upwards [] with y
      rw [Real.norm_eq_abs,
        abs_of_nonneg
          (mul_nonneg hslope (horbit_nonneg (t + 1) y))]
      exact mul_le_mul_of_nonneg_left (hupper y) hslope

/-- To verify the substantive expansion field of a finite block certificate,
it suffices to check the single reference interval `[0,minWidth]`.
Translation invariance and sliding that interval inside any wider seed
interval give the universal statement. -/
theorem finiteBlockCertificate_of_reference_interval
    {K : ℝ → ℝ}
    {slope η seed leftAdvance rightAdvance minWidth : ℝ}
    {block : ℕ}
    (hseed_pos : 0 < seed)
    (hseed_le_eta : seed ≤ η)
    (hK : ∀ z, 0 ≤ K z)
    (hslope : 0 ≤ slope)
    (hminWidth : 0 ≤ minWidth)
    (hadvance : leftAdvance ≤ rightAdvance)
    (hlinear_nonneg :
      ∀ L R, minWidth ≤ R - L →
        ∀ t, t ≤ block → ∀ x,
          0 ≤ finiteLinearOrbit K slope
            (intervalFloor seed L R) t x)
    (hlinear_le_eta :
      ∀ L R, minWidth ≤ R - L →
        ∀ t, t ≤ block → ∀ x,
          finiteLinearOrbit K slope
            (intervalFloor seed L R) t x ≤ η)
    (hlinear_integrable :
      ∀ L R, minWidth ≤ R - L →
        ∀ t, t < block → ∀ x,
          Integrable
            (fun y =>
              K (x - y) *
                (slope * finiteLinearOrbit K slope
                  (intervalFloor seed L R) t y)))
    (href :
      ∀ x ∈ Set.Icc leftAdvance (minWidth + rightAdvance),
        seed ≤ finiteLinearOrbit K slope
          (intervalFloor seed 0 minWidth) block x) :
    FiniteBlockCertificate K slope η seed block
      leftAdvance rightAdvance minWidth := by
  refine
    { seed_pos := hseed_pos
      seed_le_eta := hseed_le_eta
      linear_nonneg := hlinear_nonneg
      linear_le_eta := hlinear_le_eta
      linear_integrable := hlinear_integrable
      expands_floor := ?_ }
  intro L R hwidth x hx
  let A : ℝ := max L (x - (minWidth + rightAdvance))
  have hAL : L ≤ A := le_max_left _ _
  have hAxleft : A ≤ x - leftAdvance := by
    apply max_le
    · linarith [hx.1]
    · linarith [hminWidth, hadvance]
  have hAR : A + minWidth ≤ R := by
    have hxright : x - (minWidth + rightAdvance) ≤
        R - minWidth := by
      linarith [hx.2]
    have hLright : L ≤ R - minWidth := by
      linarith
    have hmax :
        max L (x - (minWidth + rightAdvance)) ≤
          R - minWidth :=
      max_le hLright hxright
    dsimp [A]
    linarith
  have hsub :
      Set.Icc A (A + minWidth) ⊆ Set.Icc L R := by
    intro y hy
    exact ⟨hAL.trans hy.1, hy.2.trans hAR⟩
  have hxsub :
      x ∈ Set.Icc
        (A + leftAdvance) (A + minWidth + rightAdvance) := by
    have hxA :
        x - (minWidth + rightAdvance) ≤ A :=
      le_max_right _ _
    constructor <;> linarith
  have href_shift :
      seed ≤ finiteLinearOrbit K slope
        (intervalFloor seed A (A + minWidth)) block x := by
    have hreference := href (x - A) (by
      constructor <;> linarith [hxsub.1, hxsub.2])
    have htranslate :=
      finiteLinearOrbit_interval_translate
        K slope seed minWidth A block (x - A)
    rw [show x - A + A = x by ring] at htranslate
    rw [htranslate]
    exact hreference
  apply href_shift.trans
  apply finiteLinearOrbit_mono_of_integrable hK hslope
  · intro y
    exact intervalFloor_mono_of_Icc_subset hseed_pos.le hsub
  · intro t ht y
    exact hlinear_integrable A (A + minWidth) (by linarith) t ht y
  · intro t ht y
    exact hlinear_integrable L R hwidth t ht y

/-- A more economical reference-interval constructor.  Nonnegativity is
automatic, all finite-step integrability conditions follow from convolution
of integrable functions and the scalar bounds, and the universal upper bound
is reduced to `slope ^ t * seed ≤ η`.  Thus only finite scalar inequalities
and one reference expansion estimate remain to be checked. -/
theorem finiteBlockCertificate_of_reference_interval_and_power_bound
    {K : ℝ → ℝ}
    {slope η seed leftAdvance rightAdvance minWidth : ℝ}
    {block : ℕ}
    (hseed_pos : 0 < seed)
    (hseed_le_eta : seed ≤ η)
    (hKint : Integrable K)
    (hKmass : ∫ z, K z = 1)
    (hK : ∀ z, 0 ≤ K z)
    (hslope : 0 ≤ slope)
    (hminWidth : 0 ≤ minWidth)
    (hadvance : leftAdvance ≤ rightAdvance)
    (hpower :
      ∀ t, t ≤ block → slope ^ t * seed ≤ η)
    (href :
      ∀ x ∈ Set.Icc leftAdvance (minWidth + rightAdvance),
        seed ≤ finiteLinearOrbit K slope
          (intervalFloor seed 0 minWidth) block x) :
    FiniteBlockCertificate K slope η seed block
      leftAdvance rightAdvance minWidth := by
  apply finiteBlockCertificate_of_reference_interval
    hseed_pos hseed_le_eta hK hslope hminWidth hadvance
  · intro L R _hwidth t _ht x
    exact finiteLinearOrbit_nonneg hK hslope
      (fun y => intervalFloor_nonneg hseed_pos.le) t x
  · intro L R hwidth t ht x
    apply
      (finiteLinearOrbit_interval_bound_and_integrable
        hKint hKmass hK hslope hseed_pos.le t).1 x |>.trans
    exact hpower t ht
  · intro L R _hwidth t _ht x
    exact
      (finiteLinearOrbit_interval_bound_and_integrable
        hKint hKmass hK hslope hseed_pos.le t).2 x
  · exact href

/-- Dimensionless finite-block constructor.  When the slope is at least one,
the scalar upper bounds follow from the single terminal inequality.  Linear
homogeneity removes the seed height from the reference expansion estimate.
Thus the analytic content is precisely the unit-height reference inequality
`1 ≤ finiteLinearOrbit ... block`. -/
theorem finiteBlockCertificate_of_unit_reference
    {K : ℝ → ℝ}
    {slope η seed leftAdvance rightAdvance minWidth : ℝ}
    {block : ℕ}
    (hseed_pos : 0 < seed)
    (hKint : Integrable K)
    (hKmass : ∫ z, K z = 1)
    (hK : ∀ z, 0 ≤ K z)
    (hslope : 1 ≤ slope)
    (hminWidth : 0 ≤ minWidth)
    (hadvance : leftAdvance ≤ rightAdvance)
    (hseed_terminal : slope ^ block * seed ≤ η)
    (href :
      ∀ x ∈ Set.Icc leftAdvance (minWidth + rightAdvance),
        1 ≤ finiteLinearOrbit K slope
          (intervalFloor 1 0 minWidth) block x) :
    FiniteBlockCertificate K slope η seed block
      leftAdvance rightAdvance minWidth := by
  have hseed_le_eta : seed ≤ η := by
    calc
      seed = 1 * seed := by ring
      _ ≤ slope ^ block * seed :=
        mul_le_mul_of_nonneg_right
          (one_le_pow₀ hslope) hseed_pos.le
      _ ≤ η := hseed_terminal
  apply finiteBlockCertificate_of_reference_interval_and_power_bound
    hseed_pos hseed_le_eta hKint hKmass hK
    (zero_le_one.trans hslope)
    hminWidth hadvance
  · intro t ht
    exact
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hslope ht) hseed_pos.le).trans
        hseed_terminal
  · intro x hx
    rw [finiteLinearOrbit_interval_scale]
    simpa using
      mul_le_mul_of_nonneg_left (href x hx) hseed_pos.le

/-! ## One nonlinear block -/

/-- A finite linear block stays below the corrected nonlinear orbit whenever
the environment and competitor bounds hold on the positive support of the
linear subsolution. -/
theorem finiteLinearOrbit_le_correctedOrbit
    {focal competitor : ℕ → ℝ → ℝ}
    {Kfun ρfun initial : ℝ → ℝ}
    {α c ρ₀ δ η slope : ℝ} {N block : ℕ}
    (hstep :
      ∀ t x,
        focal (N + t + 1) x =
          heterogeneousCorrectedStep Kfun ρfun α c (N + t)
            (focal (N + t)) (competitor (N + t)) x)
    (hKint : Integrable Kfun) (hKcont : Continuous Kfun)
    (hKnonneg : ∀ s, 0 ≤ Kfun s)
    (hρcont : Continuous ρfun) (hρlow : ∀ s, -1 < ρfun s)
    (hα : 0 ≤ α)
    (hfocal_cont : ∀ n, Continuous (focal n))
    (hfocal_nonneg : ∀ n y, 0 ≤ focal n y)
    (hfocal_le_one : ∀ n y, focal n y ≤ 1)
    (hcompetitor_cont : ∀ n, Continuous (competitor n))
    (hcompetitor_nonneg : ∀ n y, 0 ≤ competitor n y)
    (hρ₀ : 0 < ρ₀) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hsmall : η + α * δ ≤ 1)
    (hslope : 0 ≤ slope)
    (hslope_le : slope ≤ favorableLowerSlope ρ₀ α δ η)
    (hlinear_nonneg :
      ∀ t, t ≤ block → ∀ x,
        0 ≤ finiteLinearOrbit Kfun slope initial t x)
    (hlinear_le_eta :
      ∀ t, t ≤ block → ∀ x,
        finiteLinearOrbit Kfun slope initial t x ≤ η)
    (hlinear_integrable :
      ∀ t, t < block → ∀ x,
        Integrable
          (fun y =>
            Kfun (x - y) *
              (slope * finiteLinearOrbit Kfun slope initial t y)))
    (hinitial : ∀ x, initial x ≤ focal N x)
    (hfavorable :
      ∀ t, t < block → ∀ y,
        0 < finiteLinearOrbit Kfun slope initial t y →
          competitor (N + t) y ≤ δ ∧
          ρ₀ ≤ ρfun (y - c * ((N + t : ℕ) : ℝ))) :
    ∀ t, t ≤ block → ∀ x,
      finiteLinearOrbit Kfun slope initial t x ≤
        focal (N + t) x := by
  intro t
  induction t with
  | zero =>
      intro _ht x
      simpa using hinitial x
  | succ t ih =>
      intro ht x
      have htblock : t < block := by omega
      have htle : t ≤ block := by omega
      rw [finiteLinearOrbit_succ]
      rw [show N + (t + 1) = N + t + 1 by omega, hstep t x]
      unfold ShenWork.Analysis.linearDispersalStep
      rw [← ShenWork.Analysis.dispersal_const_mul]
      unfold ShenWork.Analysis.dispersal heterogeneousCorrectedStep
      have hright :
          Integrable
            (fun y =>
              Kfun (x - y) *
                correctedResponse
                  (ρfun (y - c * ((N + t : ℕ) : ℝ))) α
                  (focal (N + t) y) (competitor (N + t) y)) :=
        heterogeneousCorrectedIntegrable
          hKint hKcont hρcont hρlow hα
          (hfocal_cont _) (hfocal_nonneg _) (hfocal_le_one _)
          (hcompetitor_cont _) (hcompetitor_nonneg _)
      apply integral_mono (hlinear_integrable t htblock x) hright
      intro y
      apply mul_le_mul_of_nonneg_left _ (hKnonneg _)
      let w : ℝ := finiteLinearOrbit Kfun slope initial t y
      have hw0 : 0 ≤ w := hlinear_nonneg t htle y
      have hwη : w ≤ η := hlinear_le_eta t htle y
      have hwfocal : w ≤ focal (N + t) y :=
        ih htle y
      by_cases hwpos : 0 < w
      · have hfav := hfavorable t htblock y hwpos
        have hlinear :
            slope * w ≤ correctedResponse ρ₀ α w δ :=
          linear_mul_le_correctedResponse
            hρ₀ hα hδ hη hslope hslope_le hw0 hwη
        have hsubunit : w + α * δ ≤ 1 := by
          linarith
        exact hlinear.trans <|
          correctedResponse_ge_perturbed_floor
            hρ₀.le hfav.2 hα hw0 hwfocal
            (hcompetitor_nonneg _ y) hfav.1 hsubunit
      · have hwzero : w = 0 := le_antisymm (le_of_not_gt hwpos) hw0
        change slope * w ≤ _
        rw [hwzero, mul_zero]
        exact correctedResponse_nonneg
          (hρlow _) hα (hfocal_nonneg _ y)
          (hcompetitor_nonneg _ y)

/-! ## Iteration of certified blocks -/

/-- Interval reached after `k` certified linear blocks. -/
def blockSeedInterval
    (L R leftAdvance rightAdvance : ℝ) (k : ℕ) : Set ℝ :=
  Set.Icc
    (L + leftAdvance * (k : ℝ))
    (R + rightAdvance * (k : ℝ))

@[simp]
theorem blockSeedInterval_zero
    (L R leftAdvance rightAdvance : ℝ) :
    blockSeedInterval L R leftAdvance rightAdvance 0 =
      Set.Icc L R := by
  simp [blockSeedInterval]

/-- A finite linear block certificate iterates to a genuine fixed positive
floor for the nonlinear corrected IDE at all block times. -/
theorem finiteBlockCertificate_positive_floor
    {focal competitor : ℕ → ℝ → ℝ}
    {Kfun ρfun : ℝ → ℝ}
    {α c ρ₀ δ η slope seed L R leftAdvance rightAdvance minWidth : ℝ}
    {N block : ℕ}
    (cert :
      FiniteBlockCertificate Kfun slope η seed block
        leftAdvance rightAdvance minWidth)
    (hadvance : leftAdvance ≤ rightAdvance)
    (hwidth : minWidth ≤ R - L)
    (hstep :
      ∀ n x,
        focal (n + 1) x =
          heterogeneousCorrectedStep Kfun ρfun α c n
            (focal n) (competitor n) x)
    (hKint : Integrable Kfun) (hKcont : Continuous Kfun)
    (hKnonneg : ∀ s, 0 ≤ Kfun s)
    (hρcont : Continuous ρfun) (hρlow : ∀ s, -1 < ρfun s)
    (hα : 0 ≤ α)
    (hfocal_cont : ∀ n, Continuous (focal n))
    (hfocal_nonneg : ∀ n y, 0 ≤ focal n y)
    (hfocal_le_one : ∀ n y, focal n y ≤ 1)
    (hcompetitor_cont : ∀ n, Continuous (competitor n))
    (hcompetitor_nonneg : ∀ n y, 0 ≤ competitor n y)
    (hρ₀ : 0 < ρ₀) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hsmall : η + α * δ ≤ 1)
    (hslope : 0 ≤ slope)
    (hslope_le : slope ≤ favorableLowerSlope ρ₀ α δ η)
    (hinitial : ∀ y ∈ Set.Icc L R, seed ≤ focal N y)
    (hfavorable :
      ∀ (k t : ℕ), t < block → ∀ y,
        0 < finiteLinearOrbit Kfun slope
          (intervalFloor seed
            (L + leftAdvance * (k : ℝ))
            (R + rightAdvance * (k : ℝ))) t y →
        competitor (N + block * k + t) y ≤ δ ∧
        ρ₀ ≤ ρfun
          (y - c * ((N + block * k + t : ℕ) : ℝ))) :
    ∀ (k : ℕ) (y : ℝ),
      y ∈ blockSeedInterval L R leftAdvance rightAdvance k →
        seed ≤ focal (N + block * k) y := by
  intro k
  induction k with
  | zero =>
      intro y hy
      rw [blockSeedInterval_zero] at hy
      simpa using hinitial y hy
  | succ k ih =>
      intro x hx
      let Lk : ℝ := L + leftAdvance * (k : ℝ)
      let Rk : ℝ := R + rightAdvance * (k : ℝ)
      have hwidthk : minWidth ≤ Rk - Lk := by
        have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
        have hgrow :
            0 ≤ (rightAdvance - leftAdvance) * (k : ℝ) :=
          mul_nonneg (sub_nonneg.mpr hadvance) hk0
        dsimp [Lk, Rk]
        nlinarith
      have hinit :
          ∀ y,
            intervalFloor seed Lk Rk y ≤
              focal (N + block * k) y := by
        intro y
        by_cases hy : y ∈ Set.Icc Lk Rk
        · rw [intervalFloor, if_pos hy]
          apply ih y
          simpa [blockSeedInterval, Lk, Rk] using hy
        · rw [intervalFloor, if_neg hy]
          exact hfocal_nonneg _ y
      have hcompare :=
        finiteLinearOrbit_le_correctedOrbit
          (focal := focal) (competitor := competitor)
          (Kfun := Kfun) (ρfun := ρfun)
          (initial := intervalFloor seed Lk Rk)
          (α := α) (c := c) (ρ₀ := ρ₀) (δ := δ)
          (η := η) (slope := slope)
          (N := N + block * k) (block := block)
          (fun t y => by
            simpa [Nat.add_assoc] using hstep (N + block * k + t) y)
          hKint hKcont hKnonneg hρcont hρlow hα
          hfocal_cont hfocal_nonneg hfocal_le_one
          hcompetitor_cont hcompetitor_nonneg
          hρ₀ hδ hη hsmall hslope hslope_le
          (cert.linear_nonneg Lk Rk hwidthk)
          (cert.linear_le_eta Lk Rk hwidthk)
          (cert.linear_integrable Lk Rk hwidthk)
          hinit
          (fun t ht y hy =>
            hfavorable k t ht y <| by
              simpa [Lk, Rk] using hy)
      have hx' :
          x ∈ Set.Icc
            (Lk + leftAdvance) (Rk + rightAdvance) := by
        dsimp [blockSeedInterval, Lk, Rk] at hx ⊢
        push_cast at hx
        constructor <;> nlinarith [hx.1, hx.2]
      have hlinearFloor :=
        cert.expands_floor Lk Rk hwidthk x hx'
      have hfinal :=
        hlinearFloor.trans (hcompare block le_rfl x)
      simpa [Nat.mul_add, Nat.add_assoc] using hfinal

/-! ## Moving-corridor form -/

/-- At block times, every corridor whose two boundary speeds lie strictly
inside the certified advances is eventually contained in the propagated
block interval. -/
theorem eventually_blockTimeCorridor_subset_blockSeedInterval
    {L R leftAdvance rightAdvance c front ε : ℝ}
    {N block : ℕ}
    (hleft : (c + ε) * (block : ℝ) > leftAdvance)
    (hright : (front - ε) * (block : ℝ) < rightAdvance) :
    ∀ᶠ k : ℕ in atTop,
      favorableCorridor c front ε (N + block * k) ⊆
        blockSeedInterval L R leftAdvance rightAdvance k := by
  have hleftgap :
      0 < (c + ε) * (block : ℝ) - leftAdvance := by linarith
  have hrightgap :
      0 < rightAdvance - (front - ε) * (block : ℝ) := by linarith
  have hleftTend :
      Tendsto
        (fun k : ℕ =>
          ((c + ε) * (block : ℝ) - leftAdvance) * (k : ℝ))
        atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hleftgap).2
      tendsto_natCast_atTop_atTop
  have hrightTend :
      Tendsto
        (fun k : ℕ =>
          (rightAdvance - (front - ε) * (block : ℝ)) * (k : ℝ))
        atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hrightgap).2
      tendsto_natCast_atTop_atTop
  have hleftEventually :
      ∀ᶠ k : ℕ in atTop,
        L - (c + ε) * (N : ℝ) ≤
          ((c + ε) * (block : ℝ) - leftAdvance) * (k : ℝ) :=
    hleftTend.eventually (eventually_ge_atTop _)
  have hrightEventually :
      ∀ᶠ k : ℕ in atTop,
        (front - ε) * (N : ℝ) - R ≤
          (rightAdvance - (front - ε) * (block : ℝ)) * (k : ℝ) :=
    hrightTend.eventually (eventually_ge_atTop _)
  filter_upwards [hleftEventually, hrightEventually] with
    k hkleft hkright
  intro x hx
  constructor
  · dsimp [favorableCorridor, blockSeedInterval] at hx ⊢
    push_cast at hx
    nlinarith [hx.1]
  · dsimp [favorableCorridor, blockSeedInterval] at hx ⊢
    push_cast at hx
    nlinarith [hx.2]

/-- A finite block certificate supplies a positive floor on every strictly
interior moving corridor at all sufficiently large block times. -/
theorem finiteBlockCertificate_blockCorridor_floor
    {focal competitor : ℕ → ℝ → ℝ}
    {Kfun ρfun : ℝ → ℝ}
    {α c ρ₀ δ η slope seed L R leftAdvance rightAdvance minWidth
      front ε : ℝ}
    {N block : ℕ}
    (cert :
      FiniteBlockCertificate Kfun slope η seed block
        leftAdvance rightAdvance minWidth)
    (hadvance : leftAdvance ≤ rightAdvance)
    (hwidth : minWidth ≤ R - L)
    (hstep :
      ∀ n x,
        focal (n + 1) x =
          heterogeneousCorrectedStep Kfun ρfun α c n
            (focal n) (competitor n) x)
    (hKint : Integrable Kfun) (hKcont : Continuous Kfun)
    (hKnonneg : ∀ s, 0 ≤ Kfun s)
    (hρcont : Continuous ρfun) (hρlow : ∀ s, -1 < ρfun s)
    (hα : 0 ≤ α)
    (hfocal_cont : ∀ n, Continuous (focal n))
    (hfocal_nonneg : ∀ n y, 0 ≤ focal n y)
    (hfocal_le_one : ∀ n y, focal n y ≤ 1)
    (hcompetitor_cont : ∀ n, Continuous (competitor n))
    (hcompetitor_nonneg : ∀ n y, 0 ≤ competitor n y)
    (hρ₀ : 0 < ρ₀) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hsmall : η + α * δ ≤ 1)
    (hslope : 0 ≤ slope)
    (hslope_le : slope ≤ favorableLowerSlope ρ₀ α δ η)
    (hinitial : ∀ y ∈ Set.Icc L R, seed ≤ focal N y)
    (hfavorable :
      ∀ (k t : ℕ), t < block → ∀ y,
        0 < finiteLinearOrbit Kfun slope
          (intervalFloor seed
            (L + leftAdvance * (k : ℝ))
            (R + rightAdvance * (k : ℝ))) t y →
        competitor (N + block * k + t) y ≤ δ ∧
        ρ₀ ≤ ρfun
          (y - c * ((N + block * k + t : ℕ) : ℝ)))
    (hleft : (c + ε) * (block : ℝ) > leftAdvance)
    (hright : (front - ε) * (block : ℝ) < rightAdvance) :
    ∃ K, ∀ (k : ℕ), K ≤ k →
      ∀ y ∈ favorableCorridor c front ε (N + block * k),
        seed ≤ focal (N + block * k) y := by
  have hfloor :=
    finiteBlockCertificate_positive_floor
      cert hadvance hwidth hstep hKint hKcont hKnonneg
      hρcont hρlow hα
      hfocal_cont hfocal_nonneg hfocal_le_one
      hcompetitor_cont hcompetitor_nonneg
      hρ₀ hδ hη hsmall hslope hslope_le hinitial hfavorable
  have hgeom :=
    eventually_blockTimeCorridor_subset_blockSeedInterval
      (L := L) (R := R)
      (leftAdvance := leftAdvance) (rightAdvance := rightAdvance)
      (c := c) (front := front) (ε := ε)
      (N := N) (block := block) hleft hright
  rcases eventually_atTop.1 hgeom with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk y hy
  exact hfloor k y (hK k hk hy)

section AxiomAudit

#print axioms linear_mul_le_correctedResponse
#print axioms integral_intervalFloor
#print axioms integral_finiteLinearOrbit
#print axioms integral_finiteLinearOrbit_intervalFloor
#print axioms finiteBlockCertificate_of_reference_interval
#print axioms finiteBlockCertificate_of_reference_interval_and_power_bound
#print axioms finiteBlockCertificate_of_unit_reference
#print axioms finiteLinearOrbit_le_correctedOrbit
#print axioms finiteBlockCertificate_positive_floor
#print axioms finiteBlockCertificate_blockCorridor_floor

end AxiomAudit

end

end ShenWork.Liang
