import ShenWork.PaperOne.WaveTrapSchauderViaRetraction
import ShenWork.PaperOne.WholeLineLongTimeMap

/-!
# Wave fixed point from the continuous-image Schauder principle (our own Brouwer)

`wholeLine_wave_fixedPoint_exists_of_continuousImage` is the drop-in replacement for the brick-12
`wholeLine_wave_fixedPoint_exists` that carried the *abstract* `LocalUniformSchauderFixedPointPrinciple` as a
hypothesis.  Here that abstract principle is DISCHARGED (proved from our own `brouwer_fixedPoint` via the
antitone-majorant retraction, `waveTrap_fixedPoint_of_continuousImage`), at the cost of the extra hypothesis
`hTimg : ∀ u ∈ WaveTrap, Continuous (T u)` — which is exactly `LongTimeMapImageContinuity`, already carried by
the wave assembly.  So the wave headline no longer needs the Schauder principle as a residual: it reuses the
image-continuity field it already has.
-/

open Set

namespace ShenWork.PaperOne

/-- Wave fixed point, with the Schauder principle DISCHARGED via our own Brouwer + the continuous-image
hypothesis (`= LongTimeMapImageContinuity`). -/
theorem wholeLine_wave_fixedPoint_exists_of_continuousImage {κ κt D : ℝ}
    (hκ : 0 < κ) (hκt : κ < κt) (hD : 1 ≤ D)
    {T : (ℝ → ℝ) → ℝ → ℝ}
    (hmapsTo : MapsTo T (WaveTrap κ κt D) (WaveTrap κ κt D))
    (hcont :
      ShenWork.Paper1.LocalUniformContinuousOn
        (fun U : ℝ → ℝ => U ∈ WaveTrap κ κt D) T)
    (hcompact :
      ShenWork.Paper1.LocalUniformSequentiallyCompactRange
        (fun U : ℝ → ℝ => U ∈ WaveTrap κ κt D) T)
    (hTimg : ∀ u, u ∈ WaveTrap κ κt D → Continuous (T u)) :
    ∃ Ustar : ℝ → ℝ, Ustar ∈ WaveTrap κ κt D ∧ T Ustar = Ustar :=
  waveTrap_fixedPoint_of_continuousImage hκ hκt hD
    (fun u hu => hmapsTo hu) hcont hcompact hTimg

end ShenWork.PaperOne
