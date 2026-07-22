import ShenWork.Paper1.WholeLineChiLargeResidualClosure

/-!
# Reduction of the large-critical Stage 1 to one weighted energy inequality

This file removes the scalar ODE closure from the residual.  Once the
translated energy

`E(t,x₀) = (1/P) ∫ u(t,x)^P ψκ(x-x₀) dx`

is continuous up to time zero and satisfies `E' + E ≤ R` at positive times,
the existing positive-time damping lemma gives a bound uniform in the
terminal time and in `x₀`.  Thus the remaining Stage-1 issue is precisely the
whole-line integration-by-parts/dominated-differentiation estimate encoded
below, not a Grönwall or semigroup estimate.
-/

open Filter MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-- Exact differential-energy statement needed on maximal BUC orbits.  It is
formulated on every finite subhorizon, but its right-hand side is independent
of that horizon and of the translated spatial centre. -/
def WholeLineLargeChiMaximalEnergyDamping
    (p : CMParams) (P κ : ℝ) : Prop :=
  ∀ (u₀ : ℝ → ℝ), PaperNonnegativeInitialDatum u₀ →
    ∀ (Tmax : WithTop ℝ) (U : ℝ → WholeLineBUC),
      IsWholeLineMaximalBUCOrbit p u₀ Tmax U →
      ∀ T : ℝ, 0 < T → (T : WithTop ℝ) < Tmax → ∀ x₀ : ℝ,
        let u : ℝ → ℝ → ℝ := fun t x => (U t).1 x
        let E : ℝ → ℝ := fun t => wholeLineLocalLpEnergy P κ u t x₀
        ContinuousOn E (Icc 0 T) ∧
          ∀ t ∈ Ioo (0 : ℝ) T,
            HasDerivAt E (deriv E t) t ∧
              deriv E t + E t ≤ wholeLineLocalMomentDampingRhs p P κ

/-- The differential-energy statement implies the final time- and
translation-uniform local moment bound. -/
theorem wholeLineLargeChiMaximalLocalMomentBound_of_energyDamping
    (p : CMParams) {P κ : ℝ}
    (hP : 1 < P) (hκ : 0 < κ)
    (habsorption : 0 < wholeLineLocalMomentAbsorption p P κ)
    (Hdamping : WholeLineLargeChiMaximalEnergyDamping p P κ) :
    WholeLineLargeChiMaximalLocalMomentBound p P κ := by
  intro u₀ hu₀ Tmax U horbit
  let w : WholeLineBUC := wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1
  let A : ℝ := (‖w‖ ^ P * (2 / κ)) / P
  let R : ℝ := wholeLineLocalMomentDampingRhs p P κ
  let K : ℝ := P * max A R
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hR : 0 < R := by
    have hrem := wholeLineLocalMomentYoungRemainder_pos
      p hP hκ habsorption
    dsimp [R, wholeLineLocalMomentDampingRhs]
    exact mul_pos hrem (div_pos (by norm_num) hκ)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg hP0.le
      (hA.trans (le_max_left A R))
  refine ⟨K, hK, ?_⟩
  intro T hT hTmax x₀
  let u : ℝ → ℝ → ℝ := fun t x => (U t).1 x
  let E : ℝ → ℝ := fun t => wholeLineLocalLpEnergy P κ u t x₀
  have hdata := Hdamping u₀ hu₀ Tmax U horbit T hT hTmax x₀
  change ContinuousOn E (Icc 0 T) ∧
    (∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt E (deriv E t) t ∧
        deriv E t + E t ≤ wholeLineLocalMomentDampingRhs p P κ) at hdata
  obtain ⟨hcont, hdamping⟩ := hdata
  have hscalar : E T ≤ max (E 0) R := by
    have hraw := scalarEnergy_uniform_bound_of_positive_time_damping
      (E := E) (T := T) (lam := 1)
      (K := wholeLineLocalMomentDampingRhs p P κ)
      hT.le one_pos hcont
      (fun t ht => (hdamping t ht).1)
      (fun t ht => by simpa only [one_mul] using (hdamping t ht).2)
      T ⟨hT.le, le_rfl⟩
    simpa [R] using hraw
  obtain ⟨_hTmaxPos, hdatum, _htrace, _hcontOrbit, _hclass,
    _hmild, _hnonnegative, _hblowup⟩ := horbit
  have hUzero : U 0 = w := by
    apply Subtype.ext
    apply BoundedContinuousFunction.ext
    intro x
    simpa [w] using hdatum x
  have hmoment0 : wholeLineLocalLpMoment P κ u 0 x₀ ≤
      ‖w‖ ^ P * (2 / κ) := by
    apply wholeLineLocalLpMoment_le_two_mul_div
      hP0.le hκ (norm_nonneg w)
    · simpa [u, hUzero] using (WholeLineBUC.isCUnifBdd w).1
    · intro x
      simpa [u, hUzero] using hu₀.2 x
    · intro x
      simpa [u, hUzero] using WholeLineBUC.apply_le_norm w x
  have hEzero : E 0 ≤ A := by
    change (1 / P) * wholeLineLocalLpMoment P κ u 0 x₀ ≤
      (‖w‖ ^ P * (2 / κ)) / P
    have hscaled := mul_le_mul_of_nonneg_left hmoment0
      (one_div_nonneg.mpr hP0.le)
    convert hscaled using 1
    all_goals field_simp [hP0.ne']
  have hE : E T ≤ max A R :=
    hscalar.trans (max_le_max hEzero le_rfl)
  have hscaled := mul_le_mul_of_nonneg_left hE hP0.le
  have hmomentEq : wholeLineLocalLpMoment P κ u T x₀ = P * E T := by
    dsimp [E, wholeLineLocalLpEnergy]
    field_simp [hP0.ne']
  change wholeLineLocalLpMoment P κ u T x₀ ≤ K
  rw [hmomentEq]
  simpa [K] using hscaled

/-- Uniform producer form of the sole Stage-1 analytic estimate. -/
def WholeLineLargeChiCriticalEnergyDampingProducer (p : CMParams) : Prop :=
  ∀ P κ : ℝ,
    max (2 * p.m) p.γ < P →
    P < p.m + p.γ →
    p.χ * (P - 1) < P + p.m - 1 →
    0 < κ → κ < 1 / 2 →
    0 < wholeLineLocalMomentAbsorption p P κ →
    WholeLineLargeChiMaximalEnergyDamping p P κ

/-- The energy-damping producer supplies the Stage-1 producer used by the
continuation closure. -/
theorem wholeLineLargeChiCriticalStage1Producer_of_energyDamping
    (p : CMParams)
    (H : WholeLineLargeChiCriticalEnergyDampingProducer p) :
    WholeLineLargeChiCriticalStage1Producer p := by
  intro P κ hP hPupper hadmissible hκ hκhalf habsorption
  have hPone : 1 < P := by
    have hm2 : 1 ≤ 2 * p.m := by linarith [p.hm]
    exact lt_of_le_of_lt
      (hm2.trans (le_max_left (2 * p.m) p.γ)) hP
  exact wholeLineLargeChiMaximalLocalMomentBound_of_energyDamping
    p hPone hκ habsorption
      (H P κ hP hPupper hadmissible hκ hκhalf habsorption)

/-- Full Proposition 1.1 reduced to maximal-orbit construction and the exact
whole-line differential local-moment estimate. -/
theorem paper1_Proposition_1_1_of_largeChi_maximal_and_energyDamping
    (H : ∀ p : CMParams,
      p.χ < min ((p.m + p.γ - 1) / (2 * p.m - 1))
        ((p.m + p.γ - 1) / (p.γ - 1)) →
      1 ≤ p.χ →
      p.α = p.m + p.γ - 1 →
      WholeLineMaximalBUCImport p ∧
        WholeLineLargeChiCriticalEnergyDampingProducer p) :
    Proposition_1_1 := by
  apply paper1_Proposition_1_1_of_largeChi_continuationBootstrap
  intro p hwindow hχ hcritical
  obtain ⟨himport, hdamping⟩ := H p hwindow hχ hcritical
  exact ⟨himport,
    wholeLineLargeChiCriticalStage1Producer_of_energyDamping p hdamping⟩

section AxiomAudit

#print axioms wholeLineLargeChiMaximalLocalMomentBound_of_energyDamping
#print axioms wholeLineLargeChiCriticalStage1Producer_of_energyDamping
#print axioms paper1_Proposition_1_1_of_largeChi_maximal_and_energyDamping

end AxiomAudit

end ShenWork.Paper1
