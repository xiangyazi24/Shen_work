import ShenWork.Paper1.WholeLineWeightedRegularityMild

open Filter MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

/-- Gradient counterpart of the shifted-reaction Duhamel slice.  The value
producer in `WholeLineWeightedRegularityMild` is insufficient for the Henry
`hWx2` input; this theorem applies the already-proved cap Schur gradient
estimate to the same truncated reaction source. -/
theorem exists_capWeightedMovingHeatGradient_truncatedReactionL2
    (p : CMParams) {M eta R c s tau B : ℝ}
    (hM : 0 ≤ M) (heta : 0 ≤ eta) (heta_one : eta < 1)
    (htau : 0 < tau) (hB : 0 ≤ B) (u₂ u₁ : WholeLineBUC)
    (hclose : Integrable (fun x => capWeight eta R x *
      |u₂.1 (x + c * s) - u₁.1 (x + c * s)| ^ 2))
    (henergy : (∫ x : ℝ, capWeight eta R x *
      |u₂.1 (x + c * s) - u₁.1 (x + c * s)| ^ 2) ≤ B ^ 2) :
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x => capWeightSqrt eta R x *
        paper5MovingFrameHeatGradOp c tau
          (coMovingTruncatedReactionDifference
            p M c s u₂.1 u₁.1) x) ∧
      ‖Z‖ ≤ Real.exp (-tau) * capHeatGradientSchurMass eta c tau *
        (1 + reactionLip p.α M) * B := by
  let L : ℝ := 1 + reactionLip p.α M
  have hL : 0 ≤ L := by
    dsimp [L]
    exact add_nonneg zero_le_one (reactionLip_nonneg p.hα hM)
  have hsource := capWeighted_coMovingTruncatedReaction_l2_bounded
    p hM (WholeLineBUC.isCUnifBdd u₂)
      (WholeLineBUC.isCUnifBdd u₁) hclose
  have hcap : Integrable (fun x => capWeight eta R x *
      |coMovingTruncatedReactionDifference p M c s u₂.1 u₁.1 x| ^ 2) := by
    refine hsource.1.congr (Eventually.of_forall fun x => ?_)
    change (capWeightSqrt eta R x *
      (wholeLineCauchyTruncatedReaction p M u₂.1 (x + c * s) -
        wholeLineCauchyTruncatedReaction p M u₁.1 (x + c * s))) ^ 2 = _
    dsimp only
    rw [mul_pow, capWeightSqrt_sq, sq_abs]
    rfl
  have hsource_energy : (∫ x : ℝ, capWeight eta R x *
      |coMovingTruncatedReactionDifference p M c s u₂.1 u₁.1 x| ^ 2) ≤
      (L * B) ^ 2 := by
    have heq : (∫ x : ℝ, capWeight eta R x *
        |coMovingTruncatedReactionDifference p M c s u₂.1 u₁.1 x| ^ 2) =
        ∫ x : ℝ, capWeightedCoMovingTruncatedReactionDifference
          p M eta R c s u₂.1 u₁.1 x ^ 2 := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change capWeight eta R x *
            |coMovingTruncatedReactionDifference p M c s u₂.1 u₁.1 x| ^ 2 =
          (capWeightSqrt eta R x *
            (wholeLineCauchyTruncatedReaction p M u₂.1 (x + c * s) -
              wholeLineCauchyTruncatedReaction p M u₁.1 (x + c * s))) ^ 2
        rw [mul_pow, capWeightSqrt_sq, sq_abs]
        rfl
    rw [heq]
    calc
      (∫ x : ℝ, capWeightedCoMovingTruncatedReactionDifference
          p M eta R c s u₂.1 u₁.1 x ^ 2) ≤ L ^ 2 * B ^ 2 :=
        hsource.2.trans (mul_le_mul_of_nonneg_left henergy (sq_nonneg L))
      _ = (L * B) ^ 2 := by rw [mul_pow]
  rcases exists_capWeightedMovingHeatGradientL2
    heta htau (mul_nonneg hL hB) R c
      (coMovingTruncatedReactionDifference_measurable p hM c s u₂ u₁)
      hcap hsource_energy with ⟨Z, hrep, hZ⟩
  refine ⟨Z, hrep, hZ.trans_eq ?_⟩
  dsimp only [L]
  ring

/-- Generic three-leg assembly for a cap-weighted gradient Duhamel map.  The
homogeneous, chemotactic, and reaction gradient representatives are kept
separate so each can be supplied by its own Schur estimate. -/
theorem exists_capWeightedGradientDuhamelSumL2
    {t A : ℝ} (ht : 0 ≤ t)
    (Z₀ : WholeLineRealL2) (ZG ZR : ℝ → WholeLineRealL2)
    (f₀ fG fR gG gR : ℝ → ℝ)
    (hZG_int : IntervalIntegrable ZG volume 0 t)
    (hZR_int : IntervalIntegrable ZR volume 0 t)
    (hgG_int : IntervalIntegrable gG volume 0 t)
    (hgR_int : IntervalIntegrable gR volume 0 t)
    (hZ₀ : ‖Z₀‖ ≤ A)
    (hZG : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖ZG s‖ ≤ gG s)
    (hZR : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖ZR s‖ ≤ gR s)
    (hZ₀_rep : ((Z₀ : ℝ → ℝ) =ᵐ[volume] f₀))
    (hZG_rep : (((∫ s in (0 : ℝ)..t, ZG s) : WholeLineRealL2) : ℝ → ℝ)
      =ᵐ[volume] fG)
    (hZR_rep : (((∫ s in (0 : ℝ)..t, ZR s) : WholeLineRealL2) : ℝ → ℝ)
      =ᵐ[volume] fR) :
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x => f₀ x + fG x + fR x) ∧
      ‖Z‖ ≤ A + ∫ s in (0 : ℝ)..t, (gG s + gR s) := by
  exact capWeightedMild_oneStep_l2_of_history ht Z₀ ZG ZR
    f₀ fG fR gG gR hZG_int hZR_int hgG_int hgR_int hZ₀ hZG hZR
    hZ₀_rep hZG_rep hZR_rep

theorem exists_capWeightedMovingHeatGradient_truncatedReactionL2_le_kernel
    (p : CMParams) {M eta R c s tau T B : ℝ}
    (hM : 0 ≤ M) (heta : 0 ≤ eta) (heta_one : eta < 1)
    (htau : 0 < tau)
    (htauT : tau ≤ T) (hB : 0 ≤ B) (u₂ u₁ : WholeLineBUC)
    (hclose : Integrable (fun x => capWeight eta R x *
      |u₂.1 (x + c * s) - u₁.1 (x + c * s)| ^ 2))
    (henergy : (∫ x : ℝ, capWeight eta R x *
      |u₂.1 (x + c * s) - u₁.1 (x + c * s)| ^ 2) ≤ B ^ 2) :
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x => capWeightSqrt eta R x *
        paper5MovingFrameHeatGradOp c tau
          (coMovingTruncatedReactionDifference
            p M c s u₂.1 u₁.1) x) ∧
      ‖Z‖ ≤
      (2 * capMildGrowthBound eta c T *
            (1 + reactionLip p.α M) * eta +
          (2 * capMildGrowthBound eta c T *
            (1 + reactionLip p.α M) *
            (2 / Real.sqrt (4 * Real.pi))) *
              tau ^ (-(1 / 2 : ℝ))) * B := by
  let L : ℝ := 1 + reactionLip p.α M
  have hL : 0 ≤ L := by
    dsimp [L]
    exact add_nonneg zero_le_one (reactionLip_nonneg p.hα hM)
  rcases exists_capWeightedMovingHeatGradient_truncatedReactionL2
      p hM heta heta_one htau hB u₂ u₁ hclose henergy with
    ⟨Z, hrep, hZ⟩
  have hmass := capHeatGradientSchurMass_le_capMildKernel
    (c := c) heta htau htauT
  have hexp : Real.exp (-tau) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr htau.le)
  have hfactor : Real.exp (-tau) * capHeatGradientSchurMass eta c tau ≤
      2 * capMildGrowthBound eta c T * eta +
        (2 * capMildGrowthBound eta c T *
          (2 / Real.sqrt (4 * Real.pi))) *
            tau ^ (-(1 / 2 : ℝ)) := by
    exact (mul_le_mul_of_nonneg_right hexp
      (capHeatGradientSchurMass_pos htau heta c).le).trans (by simpa using hmass)
  refine ⟨Z, hrep, hZ.trans ?_⟩
  calc
    Real.exp (-tau) * capHeatGradientSchurMass eta c tau * L * B =
        (Real.exp (-tau) * capHeatGradientSchurMass eta c tau) * (L * B) := by ring
    _ ≤ (2 * capMildGrowthBound eta c T * eta +
        (2 * capMildGrowthBound eta c T *
          (2 / Real.sqrt (4 * Real.pi))) *
            tau ^ (-(1 / 2 : ℝ))) * (L * B) :=
      mul_le_mul_of_nonneg_right hfactor (mul_nonneg hL hB)
    _ = (2 * capMildGrowthBound eta c T * L * eta +
        (2 * capMildGrowthBound eta c T *
          (2 / Real.sqrt (4 * Real.pi))) * L *
          tau ^ (-(1 / 2 : ℝ))) * B := by ring
    _ = (2 * capMildGrowthBound eta c T *
            (1 + reactionLip p.α M) * eta +
          (2 * capMildGrowthBound eta c T *
            (1 + reactionLip p.α M) *
            (2 / Real.sqrt (4 * Real.pi))) *
              tau ^ (-(1 / 2 : ℝ))) * B := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      dsimp [L]
      ring

/-- Once the differentiated fixed-point identity identifies the three-leg
sum with the weighted population gradient, its L² representative immediately
gives the desired `hWx2` integrability. -/
theorem paper5WeightedPopulationX_sq_integrable_of_gradientDuhamelSum
    {eta c t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {f₀ fG fR : ℝ → ℝ}
    (hsum : ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x => f₀ x + fG x + fR x))
    (hgrad_eq : ∀ x,
      paper5WeightedPopulationX eta (coMovingPath c u) U t x =
        f₀ x + fG x + fR x) :
    Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2) volume := by
  rcases hsum with ⟨Z, hrep⟩
  have hZmeas : Measurable (Z : ℝ → ℝ) :=
    (Lp.stronglyMeasurable Z).measurable
  have hZsq : Integrable (fun x => (Z x) ^ 2) :=
    (memLp_two_iff_integrable_sq (Lp.memLp Z).1).1 (Lp.memLp Z)
  refine hZsq.congr ?_
  filter_upwards [hrep] with x hx
  rw [hx, hgrad_eq x]

/-- Algebraic pointwise bridge for the differentiated fixed-point identity.
The three scalar legs can be instantiated with the homogeneous, chemotactic,
and reaction gradient Duhamel terms supplied by the C² bootstrap. -/
theorem capWeightedPopulationX_eq_three_gradient_legs
    {eta R c t x : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {q₀ qG qR : ℝ}
    (hderiv : eta * (coMovingPath c u t x - U x) +
      deriv (coMovingPath c u t) x - deriv U x = q₀ + qG + qR) :
    capWeightSqrt eta R x *
        paper5WeightedPopulationX eta (coMovingPath c u) U t x =
      capWeightSqrt eta R x * Real.exp (eta * x) * q₀ +
      capWeightSqrt eta R x * Real.exp (eta * x) * qG +
      capWeightSqrt eta R x * Real.exp (eta * x) * qR := by
  unfold paper5WeightedPopulationX paper5WeightedPopulation
  calc
    capWeightSqrt eta R x *
        (eta * (Real.exp (eta * x) *
          (coMovingPath c u t x - U x)) +
          Real.exp (eta * x) *
            (deriv (coMovingPath c u t) x - deriv U x)) =
      capWeightSqrt eta R x * Real.exp (eta * x) *
        (eta * (coMovingPath c u t x - U x) +
          deriv (coMovingPath c u t) x - deriv U x) := by ring
    _ = capWeightSqrt eta R x * Real.exp (eta * x) *
        (q₀ + qG + qR) := by rw [hderiv]
    _ = capWeightSqrt eta R x * Real.exp (eta * x) * q₀ +
        capWeightSqrt eta R x * Real.exp (eta * x) * qG +
      capWeightSqrt eta R x * Real.exp (eta * x) * qR := by ring

/-! The C² bootstrap exposes spatial derivatives as `HasDerivAt` facts.  This
lemma is the small interface which turns those facts into the scalar identity
consumed by the cap-weighted three-leg assembly above.  Keeping this bridge
separate is useful: the fixed-point/Duhamel producers can provide the three
source terms independently, while the coordinate change and the reference
profile only enter through the two derivative witnesses. -/
theorem capWeightedPopulationX_eq_three_gradient_legs_of_hasDerivAt
    {eta R c t x : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {qU qRef q₀ qG qR : ℝ}
    (hu : HasDerivAt (coMovingPath c u t) qU x)
    (hU : HasDerivAt U qRef x)
    (hlegs : eta * (coMovingPath c u t x - U x) +
      qU - qRef = q₀ + qG + qR) :
    capWeightSqrt eta R x *
        paper5WeightedPopulationX eta (coMovingPath c u) U t x =
      capWeightSqrt eta R x * Real.exp (eta * x) * q₀ +
      capWeightSqrt eta R x * Real.exp (eta * x) * qG +
      capWeightSqrt eta R x * Real.exp (eta * x) * qR := by
  have hderiv : deriv (coMovingPath c u t) x = qU := hu.deriv
  have hUderiv : deriv U x = qRef := hU.deriv
  apply capWeightedPopulationX_eq_three_gradient_legs
  rw [hderiv, hUderiv]
  exact hlegs

/-! A source-level version of the `hWx2` producer.  The three weighted
Duhamel legs are deliberately hypotheses here; their concrete Schur
producers above (and the C² bootstrap bridge immediately above) can be
plugged in without reproving the Hilbert-space addition argument. -/
theorem paper5WeightedPopulationX_sq_integrable_of_three_gradient_representatives
    {eta R c t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {f₀ fG fR : ℝ → ℝ}
    (h₀ : ∃ Z₀ : WholeLineRealL2, ((Z₀ : ℝ → ℝ) =ᵐ[volume] f₀))
    (hG : ∃ ZG : WholeLineRealL2, ((ZG : ℝ → ℝ) =ᵐ[volume] fG))
    (hR : ∃ ZR : WholeLineRealL2, ((ZR : ℝ → ℝ) =ᵐ[volume] fR))
    (hpoint : ∀ x,
      paper5WeightedPopulationX eta (coMovingPath c u) U t x =
        f₀ x + fG x + fR x) :
    Integrable
      (fun x => paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2)
      volume := by
  rcases h₀ with ⟨Z₀, h₀⟩
  rcases hG with ⟨ZG, hG⟩
  rcases hR with ⟨ZR, hR⟩
  let Z : WholeLineRealL2 := Z₀ + ZG + ZR
  have hZ : ((Z : ℝ → ℝ) =ᵐ[volume] fun x => f₀ x + fG x + fR x) := by
    filter_upwards [h₀, hG, hR] with x hx₀ hxG hxR
    change Z₀ x + ZG x + ZR x = f₀ x + fG x + fR x
    rw [hx₀, hxG, hxR]
  exact paper5WeightedPopulationX_sq_integrable_of_gradientDuhamelSum
    ⟨Z, hZ⟩ hpoint


section AxiomAudit
#print axioms exists_capWeightedMovingHeatGradient_truncatedReactionL2
#print axioms exists_capWeightedGradientDuhamelSumL2
#print axioms exists_capWeightedMovingHeatGradient_truncatedReactionL2_le_kernel
#print axioms paper5WeightedPopulationX_sq_integrable_of_gradientDuhamelSum
#print axioms capWeightedPopulationX_eq_three_gradient_legs
end AxiomAudit

end ShenWork.Paper1
