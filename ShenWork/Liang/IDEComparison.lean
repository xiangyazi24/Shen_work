/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import ShenWork.Analysis.DispersalKernel
import ShenWork.Liang.CorrectedModel

/-!
# Scalar comparison for the corrected integrodifference model

The corrected two-species update is dominated componentwise by the
single-species linearization in the far-right environment.  Combined with the
exponential convolution identity, this gives a reusable exponential-barrier
induction for discrete-time orbits.
-/

open Filter MeasureTheory Topology

namespace ShenWork.Liang

noncomputable section

/-- One component of the corrected heterogeneous IDE update. -/
def heterogeneousCorrectedStep
    (K ρ : ℝ → ℝ) (α c : ℝ) (n : ℕ)
    (u v : ℝ → ℝ) (x : ℝ) : ℝ :=
  ShenWork.Analysis.dispersal K
    (fun y =>
      correctedResponse (ρ (y - c * (n : ℝ))) α (u y) (v y)) x

/-- A species absent at one generation remains absent at the next. -/
@[simp]
theorem heterogeneousCorrectedStep_zero_focal
    (K ρ v : ℝ → ℝ) (α c x : ℝ) (n : ℕ) :
    heterogeneousCorrectedStep K ρ α c n (fun _ => 0) v x = 0 := by
  simp [heterogeneousCorrectedStep, ShenWork.Analysis.dispersal]

/-- Under the natural continuity and unit-interval hypotheses, every
heterogeneous corrected component integrand is integrable by domination by a
translate of the kernel. -/
theorem heterogeneousCorrectedIntegrable
    {K ρ u v : ℝ → ℝ} {α c x : ℝ} {n : ℕ}
    (hKint : Integrable K) (hKcont : Continuous K)
    (hρcont : Continuous ρ) (hρlow : ∀ s, -1 < ρ s)
    (hα : 0 ≤ α)
    (hucont : Continuous u) (hu : ∀ y, 0 ≤ u y) (hu1 : ∀ y, u y ≤ 1)
    (hvcont : Continuous v) (hv : ∀ y, 0 ≤ v y) :
    Integrable
      (fun y =>
        K (x - y) *
          correctedResponse (ρ (y - c * (n : ℝ))) α (u y) (v y)) := by
  have hshift : Continuous (fun y : ℝ => y - c * (n : ℝ)) :=
    continuous_id.sub continuous_const
  have hρshift :
      Continuous (fun y : ℝ => ρ (y - c * (n : ℝ))) :=
    hρcont.comp hshift
  have hrespcont :
      Continuous
        (fun y =>
          correctedResponse (ρ (y - c * (n : ℝ))) α (u y) (v y)) :=
    correctedResponse_comp_continuous hρshift hucont hvcont hα hu hv
  have hintcont :
      Continuous
        (fun y =>
          K (x - y) *
            correctedResponse (ρ (y - c * (n : ℝ))) α (u y) (v y)) :=
    (hKcont.comp (continuous_const.sub continuous_id)).mul hrespcont
  have hKshift : Integrable (fun y => K (x - y)) :=
    hKint.comp_sub_left x
  apply hKshift.mono hintcont.aestronglyMeasurable
  filter_upwards with y
  have hresp0 :
      0 ≤ correctedResponse (ρ (y - c * (n : ℝ))) α (u y) (v y) :=
    correctedResponse_nonneg (hρlow _) hα (hu y) (hv y)
  have hresp1 :
      correctedResponse (ρ (y - c * (n : ℝ))) α (u y) (v y) ≤ 1 :=
    correctedResponse_le_one (hρlow _) hα (hu y) (hu1 y) (hv y)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hresp0]
  simpa using mul_le_mul_of_nonneg_left hresp1 (abs_nonneg (K (x - y)))

/-- A probability kernel lifts the corrected local unit-interval bound to one
full heterogeneous IDE component step. -/
theorem heterogeneousCorrectedStep_mem_unitInterval
    {K ρ u v : ℝ → ℝ} {α c x : ℝ} {n : ℕ}
    (hKint : Integrable K) (hK : ∀ z, 0 ≤ K z)
    (hKmass : ∫ z, K z = 1)
    (hρlow : ∀ s, -1 < ρ s)
    (hα : 0 ≤ α)
    (hu : ∀ y, 0 ≤ u y) (hu1 : ∀ y, u y ≤ 1)
    (hv : ∀ y, 0 ≤ v y)
    (hresp :
      Integrable
        (fun y =>
          K (x - y) *
            correctedResponse (ρ (y - c * (n : ℝ))) α (u y) (v y))) :
    heterogeneousCorrectedStep K ρ α c n u v x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · unfold heterogeneousCorrectedStep ShenWork.Analysis.dispersal
    apply integral_nonneg
    intro y
    exact mul_nonneg (hK (x - y))
      (correctedResponse_nonneg (hρlow _) hα (hu y) (hv y))
  · have hKshift : Integrable (fun y => K (x - y)) :=
      hKint.comp_sub_left x
    unfold heterogeneousCorrectedStep ShenWork.Analysis.dispersal
    calc
      (∫ y,
          K (x - y) *
            correctedResponse (ρ (y - c * (n : ℝ))) α (u y) (v y)) ≤
          (∫ y, K (x - y)) := by
        apply integral_mono hresp hKshift
        intro y
        calc
          K (x - y) *
              correctedResponse (ρ (y - c * (n : ℝ))) α (u y) (v y) ≤
              K (x - y) * 1 :=
            mul_le_mul_of_nonneg_left
              (correctedResponse_le_one
                (hρlow _) hα (hu y) (hu1 y) (hv y))
              (hK (x - y))
          _ = K (x - y) := mul_one _
      _ = ∫ z, K z :=
        integral_sub_left_eq_self K (volume : Measure ℝ) x
      _ = 1 := hKmass

/-- Continuous unit-square states therefore remain in the unit interval after
one full corrected IDE component step, with integrability discharged. -/
theorem heterogeneousCorrectedStep_mem_unitInterval_of_continuous
    {K ρ u v : ℝ → ℝ} {α c x : ℝ} {n : ℕ}
    (hKint : Integrable K) (hKcont : Continuous K)
    (hK : ∀ z, 0 ≤ K z) (hKmass : ∫ z, K z = 1)
    (hρcont : Continuous ρ) (hρlow : ∀ s, -1 < ρ s)
    (hα : 0 ≤ α)
    (hucont : Continuous u) (hu : ∀ y, 0 ≤ u y) (hu1 : ∀ y, u y ≤ 1)
    (hvcont : Continuous v) (hv : ∀ y, 0 ≤ v y) :
    heterogeneousCorrectedStep K ρ α c n u v x ∈ Set.Icc (0 : ℝ) 1 := by
  apply heterogeneousCorrectedStep_mem_unitInterval
    hKint hK hKmass hρlow hα hu hu1 hv
  exact heterogeneousCorrectedIntegrable
    hKint hKcont hρcont hρlow hα hucont hu hu1 hvcont hv

/-- The corrected heterogeneous component step preserves the competitive
order: increasing the focal profile and decreasing the competitor profile
increases the next focal profile. -/
theorem heterogeneousCorrectedStep_competitive_mono
    {K ρ u₁ u₂ v₁ v₂ : ℝ → ℝ} {α c x : ℝ} {n : ℕ}
    (hK : ∀ z, 0 ≤ K z) (hρlow : ∀ s, -1 < ρ s)
    (hα : 0 ≤ α)
    (hu₁ : ∀ y, 0 ≤ u₁ y) (hv₂ : ∀ y, 0 ≤ v₂ y)
    (hu₁₂ : ∀ y, u₁ y ≤ u₂ y) (hv₂₁ : ∀ y, v₂ y ≤ v₁ y)
    (hint₁ :
      Integrable
        (fun y =>
          K (x - y) *
            correctedResponse (ρ (y - c * (n : ℝ))) α (u₁ y) (v₁ y)))
    (hint₂ :
      Integrable
        (fun y =>
          K (x - y) *
            correctedResponse (ρ (y - c * (n : ℝ))) α (u₂ y) (v₂ y))) :
    heterogeneousCorrectedStep K ρ α c n u₁ v₁ x ≤
      heterogeneousCorrectedStep K ρ α c n u₂ v₂ x := by
  unfold heterogeneousCorrectedStep ShenWork.Analysis.dispersal
  apply integral_mono hint₁ hint₂
  intro y
  apply mul_le_mul_of_nonneg_left _ (hK (x - y))
  calc
    correctedResponse (ρ (y - c * (n : ℝ))) α (u₁ y) (v₁ y) ≤
        correctedResponse (ρ (y - c * (n : ℝ))) α (u₁ y) (v₂ y) :=
      correctedResponse_antitone_competitor
        (hρlow _) hα (hu₁ y) (hv₂ y) (hv₂₁ y)
    _ ≤ correctedResponse
        (ρ (y - c * (n : ℝ))) α (u₂ y) (v₂ y) :=
      correctedResponse_monotone_focal
        (hρlow _) hα (hu₁ y) (hu₁₂ y) (hv₂ y)

/-- Each component of the corrected IDE is bounded by the linear dispersal
step at the maximal environmental growth rate. -/
theorem heterogeneousCorrectedStep_le_linear
    {K ρ u v : ℝ → ℝ} {α c ρplus x : ℝ} {n : ℕ}
    (hK : ∀ z, 0 ≤ K z)
    (hρlow : ∀ s, -1 < ρ s) (hρup : ∀ s, ρ s ≤ ρplus)
    (hα : 0 ≤ α) (hu : ∀ y, 0 ≤ u y) (hv : ∀ y, 0 ≤ v y)
    (hleft :
      Integrable
        (fun y =>
          K (x - y) *
            correctedResponse (ρ (y - c * (n : ℝ))) α (u y) (v y)))
    (hright :
      Integrable
        (fun y => K (x - y) * ((1 + ρplus) * u y))) :
    heterogeneousCorrectedStep K ρ α c n u v x ≤
      ShenWork.Analysis.linearDispersalStep K (1 + ρplus) u x := by
  unfold heterogeneousCorrectedStep ShenWork.Analysis.linearDispersalStep
  rw [← ShenWork.Analysis.dispersal_const_mul]
  unfold ShenWork.Analysis.dispersal
  apply integral_mono hleft hright
  intro y
  apply mul_le_mul_of_nonneg_left _ (hK (x - y))
  calc
    correctedResponse (ρ (y - c * (n : ℝ))) α (u y) (v y) ≤
        (1 + ρ (y - c * (n : ℝ))) * u y :=
      correctedResponse_le_linear
        (hρlow _) hα (hu y) (hv y)
    _ ≤ (1 + ρplus) * u y :=
      mul_le_mul_of_nonneg_right (by linarith [hρup (y - c * (n : ℝ))])
        (hu y)

/-- Nonnegative-kernel linear dispersal preserves pointwise order, subject to
the explicit integrability hypotheses required by the Bochner integral. -/
theorem linearDispersalStep_mono
    {K f g : ℝ → ℝ} {growth x : ℝ}
    (hK : ∀ z, 0 ≤ K z) (hgrowth : 0 ≤ growth)
    (hfg : ∀ y, f y ≤ g y)
    (hf : Integrable (fun y => K (x - y) * f y))
    (hg : Integrable (fun y => K (x - y) * g y)) :
    ShenWork.Analysis.linearDispersalStep K growth f x ≤
      ShenWork.Analysis.linearDispersalStep K growth g x := by
  unfold ShenWork.Analysis.linearDispersalStep
  apply mul_le_mul_of_nonneg_left _ hgrowth
  unfold ShenWork.Analysis.dispersal
  apply integral_mono hf hg
  intro y
  exact mul_le_mul_of_nonneg_left (hfg y) (hK (x - y))

/-- A sublinear discrete orbit starting below an exponential tail remains
below the exact exponential orbit at every generation. -/
theorem sublinear_orbit_le_exponentialOrbit
    (K : ℝ → ℝ) (u : ℕ → ℝ → ℝ)
    (amplitude growth μ : ℝ)
    (hK : ∀ z, 0 ≤ K z) (hgrowth : 0 ≤ growth)
    (hinit :
      ∀ x, u 0 x ≤ amplitude * ShenWork.Analysis.exponentialTail μ x)
    (hstep :
      ∀ n x, u (n + 1) x ≤
        ShenWork.Analysis.linearDispersalStep K growth (u n) x)
    (hleft :
      ∀ n x, Integrable (fun y => K (x - y) * u n y))
    (hright :
      ∀ n x,
        Integrable
          (fun y =>
            K (x - y) *
              ShenWork.Analysis.exponentialOrbit amplitude growth
                (ShenWork.Analysis.kernelMoment K μ) μ n y)) :
    ∀ n x,
      u n x ≤
        ShenWork.Analysis.exponentialOrbit amplitude growth
          (ShenWork.Analysis.kernelMoment K μ) μ n x := by
  intro n
  induction n with
  | zero =>
      intro x
      simpa using hinit x
  | succ n ih =>
      intro x
      calc
        u (n + 1) x ≤
            ShenWork.Analysis.linearDispersalStep K growth (u n) x :=
          hstep n x
        _ ≤
            ShenWork.Analysis.linearDispersalStep K growth
              (ShenWork.Analysis.exponentialOrbit amplitude growth
                (ShenWork.Analysis.kernelMoment K μ) μ n) x :=
          linearDispersalStep_mono hK hgrowth ih (hleft n x) (hright n x)
        _ =
            ShenWork.Analysis.exponentialOrbit amplitude growth
              (ShenWork.Analysis.kernelMoment K μ) μ (n + 1) x :=
          (ShenWork.Analysis.exponentialOrbit_succ
            K amplitude growth μ n x).symm

/-- Consequently, every nonnegative sublinear orbit vanishes along a frame
whose speed exceeds the exponential speed selected by `μ`. -/
theorem sublinear_orbit_movingFrame_tendsto_zero
    (K : ℝ → ℝ) (u : ℕ → ℝ → ℝ)
    (amplitude growth μ c : ℝ)
    (hK : ∀ z, 0 ≤ K z) (hgrowth : 0 ≤ growth)
    (hnonneg : ∀ n x, 0 ≤ u n x)
    (hinit :
      ∀ x, u 0 x ≤ amplitude * ShenWork.Analysis.exponentialTail μ x)
    (hstep :
      ∀ n x, u (n + 1) x ≤
        ShenWork.Analysis.linearDispersalStep K growth (u n) x)
    (hleft :
      ∀ n x, Integrable (fun y => K (x - y) * u n y))
    (hright :
      ∀ n x,
        Integrable
          (fun y =>
            K (x - y) *
              ShenWork.Analysis.exponentialOrbit amplitude growth
                (ShenWork.Analysis.kernelMoment K μ) μ n y))
    (hR : 0 < growth * ShenWork.Analysis.kernelMoment K μ)
    (hμ : 0 < μ)
    (hc :
      Real.log (growth * ShenWork.Analysis.kernelMoment K μ) / μ < c) :
    Tendsto (fun n : ℕ => u n (c * (n : ℝ))) atTop (𝓝 0) := by
  have hupper :=
    sublinear_orbit_le_exponentialOrbit
      K u amplitude growth μ hK hgrowth hinit hstep hleft hright
  apply squeeze_zero
  · exact fun n => hnonneg n (c * (n : ℝ))
  · exact fun n => hupper n (c * (n : ℝ))
  · exact ShenWork.Analysis.exponentialOrbit_tendsto_zero_of_speed_gt
      hR hμ hc

section AxiomAudit

#print axioms heterogeneousCorrectedStep_le_linear
#print axioms heterogeneousCorrectedStep_zero_focal
#print axioms heterogeneousCorrectedStep_mem_unitInterval
#print axioms heterogeneousCorrectedStep_mem_unitInterval_of_continuous
#print axioms heterogeneousCorrectedStep_competitive_mono
#print axioms linearDispersalStep_mono
#print axioms sublinear_orbit_le_exponentialOrbit
#print axioms sublinear_orbit_movingFrame_tendsto_zero

end AxiomAudit

end

end ShenWork.Liang
