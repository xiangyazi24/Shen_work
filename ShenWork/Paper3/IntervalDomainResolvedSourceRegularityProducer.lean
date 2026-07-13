/- Produce the qualitative resolved-source package from closed C2 Neumann data. -/
import ShenWork.Paper3.IntervalDomainSignalC2Bridge
import ShenWork.Paper2.IntervalDomainL2StaticVDifference

namespace ShenWork.Paper3

open MeasureTheory Set
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalCosineInversion
open ShenWork.PDE.IntervalMildSourceDecayHelper
open ShenWork.Paper2

noncomputable section

/-- A closed `C²` Neumann profile has exactly the qualitative package needed
to differentiate its resolved gradient.  The global representative is the
clamped profile; no global regularity of the zero extension is asserted. -/
noncomputable def resolvedSourceProfileRegularity_of_contDiffOn
    {f : ℝ → ℝ}
    (hC2 : ContDiffOn ℝ 2 f (Set.Icc (0 : ℝ) 1))
    (htend0 : Filter.Tendsto (deriv f)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htend1 : Filter.Tendsto (deriv f)
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    (hbc0 : deriv f 0 = 0) (hbc1 : deriv f 1 = 0) :
    ResolvedSourceProfileRegularity f := by
  let F : ℝ → ℝ := fun x => f (clamp01 x)
  have hFcont : Continuous F := by
    refine continuousOn_univ.mp ?_
    exact hC2.continuousOn.comp clamp01_continuous.continuousOn
      (fun x _ => clamp01_mem x)
  have hFeq : ∀ x ∈ Set.Icc (0 : ℝ) 1, F x = f x := by
    intro x hx
    dsimp [F]
    rw [clamp01_eq_self hx]
  have hFsum : Summable (fun n : ℤ => fourierCoeff (reflCircle F) n) :=
    fourierCoeff_reflCircle_summable_of_repr
      hFcont hC2 hFeq htend0 htend1 hbc0 hbc1
  exact
    { weakH2 := intervalWeakH2Neumann_of_contDiffOn
        hC2 htend0 htend1 hbc0 hbc1
      representative := F
      representative_continuous := hFcont
      representative_fourier_summable := hFsum
      representative_eq := hFeq
      coeff_eq := fun k =>
        cosineCoeffs_congr_on_Icc (fun x hx => (hFeq x hx).symm) k }

#print axioms resolvedSourceProfileRegularity_of_contDiffOn

end

end ShenWork.Paper3
