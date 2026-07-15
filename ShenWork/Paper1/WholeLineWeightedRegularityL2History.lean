import ShenWork.Paper1.WholeLineWeightedRegularityDuhamel

open Filter MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-!
# Canonical weighted `L²` history sections

Pointwise existence of an `L²` representative does not provide a measurable
time history.  This file starts the history bridge with the canonical
square-integrable representative, leaving the genuinely separate measurable
section and Bochner/Fubini lemmas explicit.
-/

def wholeLineRealL2Section
    {ι : Type*}
    (g : ι → ℝ → ℝ)
    (hg_meas : ∀ s, AEStronglyMeasurable (g s) volume)
    (hg2 : ∀ s, Integrable (fun x : ℝ => g s x ^ 2) volume) :
    ι → WholeLineRealL2 :=
  fun s => wholeLineRealL2OfSqIntegrable
    (g s) (hg_meas s) (hg2 s)

theorem wholeLineRealL2Section_coe_ae
    {ι : Type*} (g : ι → ℝ → ℝ)
    (hg_meas : ∀ s, AEStronglyMeasurable (g s) volume)
    (hg2 : ∀ s, Integrable (fun x : ℝ => g s x ^ 2) volume)
    (s : ι) :
    (((wholeLineRealL2Section g hg_meas hg2 s : WholeLineRealL2) : ℝ → ℝ)
      =ᵐ[volume] g s) := by
  exact wholeLineRealL2OfSqIntegrable_coe_ae
    (g s) (hg_meas s) (hg2 s)

theorem wholeLineRealL2Section_norm_sq
    {ι : Type*} (g : ι → ℝ → ℝ)
    (hg_meas : ∀ s, AEStronglyMeasurable (g s) volume)
    (hg2 : ∀ s, Integrable (fun x : ℝ => g s x ^ 2) volume)
    (s : ι) :
    ‖wholeLineRealL2Section g hg_meas hg2 s‖ ^ 2 = ∫ x : ℝ, g s x ^ 2 := by
  exact wholeLineRealL2OfSqIntegrable_norm_sq
    (g s) (hg_meas s) (hg2 s)

end ShenWork.Paper1

#print axioms ShenWork.Paper1.wholeLineRealL2Section_coe_ae
#print axioms ShenWork.Paper1.wholeLineRealL2Section_norm_sq
