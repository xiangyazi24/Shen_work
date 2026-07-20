import ShenWork.Paper1.WholeLineChiPosStabilityNatural
import ShenWork.Paper1.Theorem13ChiPosNatural
import ShenWork.Paper1.WavePositiveConstruction

/-!
# The positive-sensitivity stability capstones are not vacuous

An axiom-clean theorem whose hypotheses cannot all hold proves nothing.  The
χ>0 Step-4 capstone carries a substantial package — a stable parameter regime,
a traveling wave with regularity, a STRICT upper tail bound, a right-tail
asymptotic at some `κ₁`, a weight inside the perturbed-root window, and a datum
that is nonnegative, strictly positive at the left and weighted-`L²`-close to
the wave.  This file exhibits a concrete point of parameter space where all of
them hold simultaneously, with the wave produced by the genuine Schauder
construction of Theorem 1.1 rather than assumed.

Model point: `m = α = γ = 1`, `χ = 1/4` (so `0 < χ < 1/2` and the exponent is
critical), and the speed chosen ABOVE the corrected stability threshold without
computing it: `c := max 3 (paper5CorrectedCStarStar p p.χ + 1)`.  This works
because Theorem 1.1's positive branch produces a wave for EVERY `c > 2`.

The weight `eta` is taken STRICTLY INSIDE the perturbed-root window, via the
budget's own `cap_between` (`paper531RootMinus < stabilityWeightCap`) and
`exists_between` — an earlier version of this file instantiated `eta := 0` and
silently omitted the two window hypotheses, which made the docstring's claim
("every hypothesis") false.  Caught by an adversarial audit; fixed here.
-/

open Filter Topology MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-- The model parameter point of the positive branch. -/
def chiPosNonvacuityParams : CMParams :=
  { m := 1, α := 1, γ := 1, χ := 1 / 4
    hm := by norm_num, hα := by norm_num, hγ := by norm_num }

theorem chiPosNonvacuityParams_regime :
    StableWaveParameterRegime chiPosNonvacuityParams := by
  refine Or.inr ⟨by norm_num [chiPosNonvacuityParams], ?_, ?_⟩
  · norm_num [chiPosNonvacuityParams, chiStar]
  · norm_num [chiPosNonvacuityParams]

/-- Every hypothesis of the χ>0 Step-4 capstone is simultaneously satisfiable,
with the wave coming from the Theorem 1.1 construction.  The conclusion is the
capstone's own conclusion, so this exhibits a genuine instance. -/
theorem chiPos_stability_nonvacuous :
    ∃ (p : CMParams) (hregime : StableWaveParameterRegime p)
      (c eta κ₁ : ℝ) (U V : ℝ → ℝ) (u₀ : WholeLineBUC),
      0 < p.χ ∧ p.χ < 1 / 2 ∧ p.α = p.m + p.γ - 1 ∧
      paper5CorrectedCStarStar p p.χ < c ∧
      IsTravelingWave p c U V ∧
      TravelingWaveRegularity p c U V ∧
      HasStrictWaveUpperTailBound p c U ∧
      kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U ∧
      -- the weight window, the part the first version omitted
      paper531RootMinus c
          (paper531ConcreteStabilityBudget p hregime).A
          (paper531ConcreteStabilityBudget p hregime).B < eta ∧
      eta < stabilityWeightCap p ∧
      (∀ x, 0 ≤ u₀.1 x) ∧
      StrictlyPositiveAtLeft u₀.1 ∧
      WeightedL2InitialCloseness eta u₀.1 U := by
  let p : CMParams := chiPosNonvacuityParams
  have hregime : StableWaveParameterRegime p := chiPosNonvacuityParams_regime
  have hα : p.α = p.m + p.γ - 1 := by norm_num [p, chiPosNonvacuityParams]
  have hχ0 : 0 ≤ p.χ := by norm_num [p, chiPosNonvacuityParams]
  have hχpos : 0 < p.χ := by norm_num [p, chiPosNonvacuityParams]
  have hχhalf : p.χ < 1 / 2 := by norm_num [p, chiPosNonvacuityParams]
  have hχ1 : p.χ < 1 := by norm_num [p, chiPosNonvacuityParams]
  have hχsmall : p.χ < min (1 / 2 : ℝ) (chiStar p) := by
    refine lt_min hχhalf ?_
    norm_num [p, chiPosNonvacuityParams, chiStar]
  -- pick the speed above BOTH the construction threshold and the stability one
  set c : ℝ := max 3 (paper5CorrectedCStarStar p p.χ + 1) with hcdef
  have hc2 : (2 : ℝ) < c := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hcStar : paper5CorrectedCStarStar p p.χ < c :=
    lt_of_lt_of_le (by linarith) (le_max_right _ _)
  -- the genuine Schauder construction supplies the wave and its regularity
  obtain ⟨U, hprofile, _hU2, _hV2, hreg, hupper, htail⟩ :=
    paper1_positiveConstruction_selfStep p hα hχ0 hχsmall c hc2
  let V : ℝ → ℝ := frozenElliptic p U
  have hTW : IsTravelingWave p c U V := by
    simpa [V] using hprofile.to_travelingWave
  have hstrict : HasStrictWaveUpperTailBound p c U :=
    hupper.hasStrictWaveUpperTailBound hχ0 hχ1
  -- a right-tail exponent strictly inside the admissible cap
  have hkappa_one : kappa c < 1 := kappa_lt_one_of_two_lt hc2
  have hkappa_cap :
      kappa c < min ((1 + p.α) * kappa c)
        (min (p.m * kappa c + 1 / 2) 1) := by
    have hkpos : 0 < kappa c := kappa_pos_of_two_lt hc2
    refine lt_min ?_ (lt_min ?_ hkappa_one)
    · have : p.α = 1 := by norm_num [p, chiPosNonvacuityParams]
      rw [this]; linarith
    · have : p.m = 1 := by norm_num [p, chiPosNonvacuityParams]
      rw [this]; linarith
  obtain ⟨κ₁, hκ₁_lo, hκ₁_cap⟩ := exists_between hkappa_cap
  have hκ₁_one : κ₁ < 1 :=
    lt_of_lt_of_le hκ₁_cap
      (le_trans (min_le_right _ _) (min_le_right _ _))
  -- the wave itself is an admissible datum
  have hU_nonneg : ∀ x, 0 ≤ U x := fun x => (hTW.U_pos x).le
  have hU_paper : PaperNonnegativeInitialDatum U :=
    ⟨⟨travelingWave_U_uniformContinuous hTW hreg.U_cont, hstrict.isBddFun⟩,
      hU_nonneg⟩
  let w : WholeLineBUC := wholeLineBUCOfPaperCUnifBdd U hU_paper.1
  -- a genuine weight inside the perturbed-root window
  let budget := paper531ConcreteStabilityBudget p hregime
  obtain ⟨eta, hroot_eta, heta_cap⟩ :=
    exists_between (budget.cap_between c hcStar).1
  refine ⟨p, hregime, c, eta, κ₁, U, V, w, hχpos, hχhalf, hα, hcStar, hTW,
    hreg, hstrict, hκ₁_lo, hκ₁_one, htail κ₁ hκ₁_lo hκ₁_cap,
    hroot_eta, heta_cap,
    (by intro x; simpa [w] using hU_nonneg x),
    (by simpa [w] using IsTravelingWave.strictlyPositiveAtLeft hTW),
    (by simpa [w] using WeightedL2InitialCloseness.refl eta U)⟩

section AxiomAudit

#print axioms chiPosNonvacuityParams_regime
#print axioms chiPos_stability_nonvacuous

end AxiomAudit

end ShenWork.Paper1
