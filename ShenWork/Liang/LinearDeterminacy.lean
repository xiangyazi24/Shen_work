/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import ShenWork.Analysis.DispersalKernel
import ShenWork.Liang.ModelAudit
import ShenWork.Paper1.WaveRotheTrap

/-!
# Linear determinacy for the Liang shifting-habitat proposal

The two-species global dynamics require a corrected nonlinear model.  The
linear speed calculation, however, is already rigorous: convolution maps an
exponential tail to the kernel moment times the same tail, and the tail decays
in every moving frame faster than `log (growth * moment) / μ`.

This file also records that the generic dispersal operator is definitionally
the same convolution convention already used in ShenWork's traveling-wave
infrastructure.
-/

open Filter Topology
open scoped BoundedContinuousFunction

namespace ShenWork.Liang

noncomputable section

/-- The speed selected by one exponential weight. -/
def exponentialSpeed (growth moment μ : ℝ) : ℝ :=
  Real.log (growth * moment) / μ

/-- The speed selected by one kernel and one exponential weight. -/
def kernelSpeedAt (K : ℝ → ℝ) (growth μ : ℝ) : ℝ :=
  exponentialSpeed growth (ShenWork.Analysis.kernelMoment K μ) μ

/-- The raw dispersal operator agrees exactly with the bounded-continuous
convolution convention used by the ShenWork traveling-wave engine. -/
theorem dispersal_eq_kernelConvVal
    (K : ℝ → ℝ) (g : ℝ →ᵇ ℝ) (x : ℝ) :
    ShenWork.Analysis.dispersal K (fun y => g y) x =
      ShenWork.Paper1.kernelConvVal K g x :=
  rfl

/-- A faster frame kills the exponential comparison orbit. -/
theorem exponential_comparison_decay
    {K : ℝ → ℝ} {amplitude growth μ c : ℝ}
    (hR : 0 < growth * ShenWork.Analysis.kernelMoment K μ)
    (hμ : 0 < μ) (hc : kernelSpeedAt K growth μ < c) :
    Tendsto
      (fun n : ℕ =>
        ShenWork.Analysis.exponentialOrbit amplitude growth
          (ShenWork.Analysis.kernelMoment K μ) μ n (c * (n : ℝ)))
      atTop (𝓝 0) := by
  exact ShenWork.Analysis.exponentialOrbit_tendsto_zero_of_speed_gt
    hR hμ hc

/-- The same exponential comparison orbit satisfies the exact
growth-and-dispersal recurrence. -/
theorem exponential_comparison_recurrence
    (K : ℝ → ℝ) (amplitude growth μ : ℝ) (n : ℕ) (x : ℝ) :
    ShenWork.Analysis.exponentialOrbit amplitude growth
        (ShenWork.Analysis.kernelMoment K μ) μ (n + 1) x =
      ShenWork.Analysis.linearDispersalStep K growth
        (ShenWork.Analysis.exponentialOrbit amplitude growth
          (ShenWork.Analysis.kernelMoment K μ) μ n) x :=
  ShenWork.Analysis.exponentialOrbit_succ K amplitude growth μ n x

section AxiomAudit

#print axioms dispersal_eq_kernelConvVal
#print axioms exponential_comparison_decay
#print axioms exponential_comparison_recurrence

end AxiomAudit

end

end ShenWork.Liang
