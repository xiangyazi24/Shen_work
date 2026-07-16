import ShenWork.Paper1.WholeLineWeightedRegularityPointwiseEnvelopeNatural
import ShenWork.Paper1.WholeLineWeightedRegularityLeftTailBarrierNatural
import ShenWork.Paper1.WholeLineWeightedRegularityGlobalSliceH0Natural
import ShenWork.Paper1.WholeLineWeightedRegularityGlobalStrictPositivityNatural
import ShenWork.Paper1.WholeLineWeightedRegularitySlice
import ShenWork.Paper1.WholeLineWeightedRegularityWaveStaticNatural
import ShenWork.Paper1.WholeLineWeightedRegularitySecondDeriv

open Filter MeasureTheory Set Topology Real

noncomputable section

namespace ShenWork.Paper1

/-!
# A positive-time lower-plateau seed

This file supplies the initial ordering needed by the dynamic lower-barrier
comparison.  It combines the one-sided initial floor, the uniform initial
trace, the positive-time weighted `H¹` envelope, and the wave's sharp right
tail.  No global positive floor is assumed.
-/

/-- A one-sided initial floor survives on some positive co-moving slice by
the uniform initial trace. -/
theorem exists_positive_time_strictlyPositiveAtLeft_of_uniformInitialTrace
    {c : ℝ} {u : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ}
    (hleft : StrictlyPositiveAtLeft u₀)
    (htrace : HasUniformInitialTrace u u₀) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ StrictlyPositiveAtLeft (coMovingPath c u t₀) := by
  rcases hleft with ⟨δ, hδ, hδle⟩
  obtain ⟨d, hd, hclose⟩ := htrace (δ / 2) (half_pos hδ)
  let t₀ : ℝ := d / 2
  have ht₀ : 0 < t₀ := half_pos hd
  have ht₀d : t₀ < d := by dsimp [t₀]; linarith
  have hshift : ∀ᶠ x in atBot, δ ≤ u₀ (x + c * t₀) :=
    (tendsto_atBot_add_const_right atBot (c * t₀) tendsto_id).eventually hδle
  refine ⟨t₀, ht₀, δ / 2, half_pos hδ, ?_⟩
  filter_upwards [hshift] with x hx
  have hdist := hclose t₀ (x + c * t₀) ht₀.le ht₀d
  rw [abs_lt] at hdist
  unfold coMovingPath
  linarith

/-- The sharp wave tail and a faster weighted-error envelope give a fixed
fraction of the leading exponential as an eventual lower bound. -/
theorem eventually_half_exp_le_of_wave_tail_and_weighted_envelope
    {c κ₁ eta C : ℝ} {w U : ℝ → ℝ}
    (hκ₁ : kappa c < κ₁) (heta : kappa c < eta)
    (henv : ∀ x, |w x - U x| ≤ C * Real.exp (-eta * x))
    (htail : HasWaveRightTailAsymptotic c κ₁ U) :
    ∀ᶠ x in atTop,
      (1 / 2 : ℝ) * Real.exp (-(kappa c) * x) ≤ w x := by
  have hgap₁ : 0 < κ₁ - kappa c := sub_pos.mpr hκ₁
  have hgapeta : 0 < eta - kappa c := sub_pos.mpr heta
  have hlin₁ : Tendsto (fun x : ℝ => -(κ₁ - kappa c) * x) atTop atBot := by
    have h := tendsto_neg_atTop_atBot.comp
      (tendsto_id.atTop_mul_const hgap₁)
    exact h.congr' (Filter.Eventually.of_forall fun x => by
      simp only [Function.comp_apply, id_eq]
      ring)
  have hlineta : Tendsto (fun x : ℝ => -(eta - kappa c) * x) atTop atBot := by
    have h := tendsto_neg_atTop_atBot.comp
      (tendsto_id.atTop_mul_const hgapeta)
    exact h.congr' (Filter.Eventually.of_forall fun x => by
      simp only [Function.comp_apply, id_eq]
      ring)
  have hexp₁ : Tendsto
      (fun x : ℝ => Real.exp (-(κ₁ - kappa c) * x))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp hlin₁
  have hexpeta : Tendsto
      (fun x : ℝ => C * Real.exp (-(eta - kappa c) * x))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp hlineta)
  have hsmall₁ : ∀ᶠ x in atTop,
      Real.exp (-(κ₁ - kappa c) * x) < (1 / 4 : ℝ) :=
    (tendsto_order.1 hexp₁).2 _ (by norm_num)
  have hsmalleta : ∀ᶠ x in atTop,
      C * Real.exp (-(eta - kappa c) * x) < (1 / 4 : ℝ) :=
    (tendsto_order.1 hexpeta).2 _ (by norm_num)
  filter_upwards [htail.eventually_abs_sub_exp_le, hsmall₁, hsmalleta]
      with x htailx hsmall₁x hsmalletax
  have htailquarter :
      Real.exp (-κ₁ * x) ≤
        (1 / 4 : ℝ) * Real.exp (-(kappa c) * x) := by
    calc
      Real.exp (-κ₁ * x) =
          Real.exp (-(kappa c) * x) *
            Real.exp (-(κ₁ - kappa c) * x) := by
              rw [← Real.exp_add]
              congr 1
              ring
      _ ≤ Real.exp (-(kappa c) * x) * (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left (le_of_lt hsmall₁x) (Real.exp_nonneg _)
      _ = (1 / 4 : ℝ) * Real.exp (-(kappa c) * x) := by ring
  have henvquarter :
      C * Real.exp (-eta * x) ≤
        (1 / 4 : ℝ) * Real.exp (-(kappa c) * x) := by
    calc
      C * Real.exp (-eta * x) =
          C * (Real.exp (-(kappa c) * x) *
            Real.exp (-(eta - kappa c) * x)) := by
              rw [← Real.exp_add]
              congr 2
              ring
      _ = Real.exp (-(kappa c) * x) *
            (C * Real.exp (-(eta - kappa c) * x)) := by ring
      _ ≤ Real.exp (-(kappa c) * x) * (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left (le_of_lt hsmalletax) (Real.exp_nonneg _)
      _ = (1 / 4 : ℝ) * Real.exp (-(kappa c) * x) := by ring
  have hUlower :
      Real.exp (-(kappa c) * x) - Real.exp (-κ₁ * x) ≤ U x := by
    linarith [neg_le_of_abs_le htailx]
  have hwlower : U x - C * Real.exp (-eta * x) ≤ w x := by
    linarith [neg_le_of_abs_le (henv x)]
  linarith

/-- If the second exponent is below twice the leading exponent, the height
of the patched plateau is at most half of the leading exponential evaluated
at its splice point. -/
theorem lowerBarrierRaw_xplus_le_half_exp_of_lt_two
    {kappa kappaTilde D : ℝ}
    (hkappa : 0 < kappa) (hgap : 0 < kappaTilde - kappa)
    (hcap : kappaTilde < 2 * kappa) (hD : 0 < D) :
    lowerBarrierRaw kappa kappaTilde D
        (lowerBarrierXPlus kappa kappaTilde D) ≤
      (1 / 2 : ℝ) *
        Real.exp (-kappa * lowerBarrierXPlus kappa kappaTilde D) := by
  have hkappaTilde : 0 < kappaTilde := by linarith
  have hcrit := lowerBarrierRaw_deriv_eq_zero_at_xplus
    hkappa hgap hD
  rw [lowerBarrierRaw_deriv] at hcrit
  have hBpos :
      0 < D * Real.exp (-kappaTilde *
        lowerBarrierXPlus kappa kappaTilde D) := by positivity
  have hscale :
      kappaTilde *
          (D * Real.exp (-kappaTilde *
            lowerBarrierXPlus kappa kappaTilde D)) <
        2 * kappa *
          (D * Real.exp (-kappaTilde *
            lowerBarrierXPlus kappa kappaTilde D)) :=
    mul_lt_mul_of_pos_right hcap hBpos
  unfold lowerBarrierRaw
  nlinarith [Real.exp_pos (-kappa *
    lowerBarrierXPlus kappa kappaTilde D)]

/-- A positive continuous slice with the paper's one-sided floor, weighted
`H¹` pointwise envelope, and sharp wave tail lies above a suitable patched
two-exponential plateau.  The second exponent is chosen strictly below every
rate needed later: the wave-tail rate, the weighted-error rate, an external
admissible cap, and `2 * kappa c`. -/
theorem exists_lowerBarrierPlateau_seed_of_profile_bounds
    {c κ₁ eta cap B C : ℝ} {w U : ℝ → ℝ}
    (hκ : 0 < kappa c)
    (hκ₁ : kappa c < κ₁) (heta : kappa c < eta)
    (hcap : kappa c < cap)
    (hwcont : Continuous w) (hwpos : ∀ x, 0 < w x)
    (hwleft : StrictlyPositiveAtLeft w)
    (hC : 0 ≤ C)
    (henv : ∀ x, |w x - U x| ≤ C * Real.exp (-eta * x))
    (htail : HasWaveRightTailAsymptotic c κ₁ U) :
    ∃ kappaTilde : ℝ,
      kappa c < kappaTilde ∧
      kappaTilde < κ₁ ∧
      kappaTilde < eta ∧
      kappaTilde < cap ∧
      kappaTilde < 2 * kappa c ∧
      ∃ D : ℝ, 1 ≤ D ∧ B < D ∧
        ∀ x, lowerBarrierPlateau (kappa c) kappaTilde D x ≤ w x := by
  have hkappaTop :
      kappa c < min κ₁ (min eta (min cap (2 * kappa c))) := by
    exact lt_min hκ₁ (lt_min heta (lt_min hcap (by linarith)))
  obtain ⟨kappaTilde, hkappaTilde, hkappaTildeTop⟩ :=
    exists_between hkappaTop
  have hkappaTildeκ₁ : kappaTilde < κ₁ :=
    hkappaTildeTop.trans_le (min_le_left _ _)
  have hkappaTildeEta : kappaTilde < eta :=
    hkappaTildeTop.trans_le
      ((min_le_right κ₁ _).trans (min_le_left _ _))
  have hkappaTildeCap : kappaTilde < cap :=
    hkappaTildeTop.trans_le
      ((min_le_right κ₁ _).trans
        ((min_le_right eta _).trans (min_le_left _ _)))
  have hkappaTildeTwo : kappaTilde < 2 * kappa c :=
    hkappaTildeTop.trans_le
      ((min_le_right κ₁ _).trans
        ((min_le_right eta _).trans
          ((min_le_right cap _).trans le_rfl)))
  rcases hwleft with ⟨delta, hdelta, hdeltaEventually⟩
  obtain ⟨L, hL⟩ := eventually_atBot.1 hdeltaEventually
  have hhalfEventually :=
    eventually_half_exp_le_of_wave_tail_and_weighted_envelope
      hκ₁ heta henv htail
  have hrightEventually :=
    hhalfEventually.and htail.eventually_abs_sub_exp_le
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 hrightEventually
  let R : ℝ := max L (max 0 R₀)
  have hLR : L ≤ R := le_max_left _ _
  have hRzero : 0 ≤ R :=
    (le_max_left (0 : ℝ) R₀).trans (le_max_right L _)
  have hR₀R : R₀ ≤ R :=
    (le_max_right (0 : ℝ) R₀).trans (le_max_right L _)
  obtain ⟨middleFloor, hmiddleFloor, hmiddle⟩ :=
    isCompact_Icc.exists_forall_le' hwcont.continuousOn
      (fun x _hx => hwpos x)
  let smallHeight : ℝ := min delta
    (min middleFloor (Real.exp (-(kappa c) * R)))
  have hsmallHeight : 0 < smallHeight := by
    dsimp [smallHeight]
    exact lt_min hdelta (lt_min hmiddleFloor (Real.exp_pos _))
  let Dbase : ℝ := max B (1 + C)
  obtain ⟨D, hDbase, hspliceSmall⟩ :=
    exists_D_gt_with_exp_xplus_le
      (B := Dbase) hκ (sub_pos.mpr hkappaTilde) hsmallHeight
  have hBD : B < D := (le_max_left B (1 + C)).trans_lt hDbase
  have honeCD : 1 + C < D :=
    (le_max_right B (1 + C)).trans_lt hDbase
  have hDone : 1 ≤ D := by linarith
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one hDone
  let X : ℝ := lowerBarrierXPlus (kappa c) kappaTilde D
  have hspliceDelta : Real.exp (-(kappa c) * X) ≤ delta := by
    exact hspliceSmall.trans (min_le_left _ _)
  have hspliceMiddle : Real.exp (-(kappa c) * X) ≤ middleFloor := by
    exact hspliceSmall.trans
      ((min_le_right delta _).trans (min_le_left _ _))
  have hspliceR : Real.exp (-(kappa c) * X) ≤
      Real.exp (-(kappa c) * R) := by
    exact hspliceSmall.trans
      ((min_le_right delta _).trans (min_le_right _ _))
  have hRX : R ≤ X := by
    have hlog := Real.exp_le_exp.mp hspliceR
    dsimp [X] at hlog ⊢
    nlinarith
  have hplateauSplice : ∀ x,
      lowerBarrierPlateau (kappa c) kappaTilde D x ≤
        Real.exp (-(kappa c) * X) := by
    intro x
    dsimp [X]
    exact lowerBarrierPlateau_le_exp_xplus hκ.le hD.le x
  have hplateauHalf :
      lowerBarrierRaw (kappa c) kappaTilde D X ≤
        (1 / 2 : ℝ) * Real.exp (-(kappa c) * X) := by
    dsimp [X]
    exact lowerBarrierRaw_xplus_le_half_exp_of_lt_two
      hκ (sub_pos.mpr hkappaTilde) hkappaTildeTwo hD
  refine ⟨kappaTilde, hkappaTilde, hkappaTildeκ₁,
    hkappaTildeEta, hkappaTildeCap, hkappaTildeTwo,
    D, hDone, hBD, ?_⟩
  intro x
  by_cases hxL : x ≤ L
  · exact (hplateauSplice x).trans (hspliceDelta.trans (hL x hxL))
  · have hLx : L ≤ x := le_of_not_ge hxL
    by_cases hxR : x ≤ R
    · exact (hplateauSplice x).trans
        (hspliceMiddle.trans (hmiddle x ⟨hLx, hxR⟩))
    · have hRx : R ≤ x := le_of_not_ge hxR
      have hright := hR₀ x (hR₀R.trans hRx)
      by_cases hxX : x ≤ X
      · have hplateauEq :
            lowerBarrierPlateau (kappa c) kappaTilde D x =
              lowerBarrierRaw (kappa c) kappaTilde D X := by
          dsimp [X] at hxX ⊢
          exact lowerBarrierPlateau_eq_const_of_le hxX
        have hexpMono : Real.exp (-(kappa c) * X) ≤
            Real.exp (-(kappa c) * x) := by
          exact Real.exp_le_exp.mpr (by nlinarith)
        rw [hplateauEq]
        exact hplateauHalf.trans
          ((mul_le_mul_of_nonneg_left hexpMono (by norm_num)).trans hright.1)
      · have hXx : X < x := lt_of_not_ge hxX
        have hxzero : 0 ≤ x := hRzero.trans hRx
        have hexpκ₁ : Real.exp (-κ₁ * x) ≤
            Real.exp (-kappaTilde * x) := by
          exact Real.exp_le_exp.mpr (by nlinarith)
        have hexpEta : Real.exp (-eta * x) ≤
            Real.exp (-kappaTilde * x) := by
          exact Real.exp_le_exp.mpr (by nlinarith)
        have herrors : Real.exp (-κ₁ * x) +
              C * Real.exp (-eta * x) ≤
            D * Real.exp (-kappaTilde * x) := by
          have hCexp := mul_le_mul_of_nonneg_left hexpEta hC
          have hcoef := mul_le_mul_of_nonneg_right
            (le_of_lt honeCD) (Real.exp_nonneg (-kappaTilde * x))
          nlinarith
        have hUlower : Real.exp (-(kappa c) * x) -
              Real.exp (-κ₁ * x) ≤ U x := by
          linarith [neg_le_of_abs_le hright.2]
        have hwlower : U x - C * Real.exp (-eta * x) ≤ w x := by
          linarith [neg_le_of_abs_le (henv x)]
        rw [lowerBarrierPlateau_eq_raw_of_xplus_lt hXx]
        unfold lowerBarrierRaw
        linarith

/-- Positive-time seed in the canonical moving coordinate.  All analytic
inputs are the natural positive-time slice facts already produced by the
weighted-regularity chain; the conclusion chooses both the restart time and
the lower barrier. -/
theorem exists_positive_time_lowerBarrierPlateau_seed_of_H1
    {c κ₁ eta cap B : ℝ}
    {u : ℝ → ℝ → ℝ} {u₀ U : ℝ → ℝ}
    (hκ : 0 < kappa c)
    (hκ₁ : kappa c < κ₁) (heta : kappa c < eta)
    (hcap : kappa c < cap)
    (htrace : HasUniformInitialTrace u u₀)
    (hu₀left : StrictlyPositiveAtLeft u₀)
    (hpositive : ∀ t x, 0 < t → 0 < u t x)
    (hu2 : ∀ t, 0 < t → ContDiff ℝ 2 (coMovingPath c u t))
    (hU2 : ContDiff ℝ 2 U)
    (hW2 : ∀ t, 0 < t → Integrable (fun x =>
      paper5WeightedPopulation eta (coMovingPath c u) U t x ^ 2))
    (hWx2 : ∀ t, 0 < t → Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2))
    (htail : HasWaveRightTailAsymptotic c κ₁ U) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∃ kappaTilde : ℝ,
        kappa c < kappaTilde ∧
        kappaTilde < κ₁ ∧
        kappaTilde < eta ∧
        kappaTilde < cap ∧
        kappaTilde < 2 * kappa c ∧
        ∃ D : ℝ, 1 ≤ D ∧ B < D ∧
          ∀ x, lowerBarrierPlateau (kappa c) kappaTilde D x ≤
            coMovingPath c u t₀ x := by
  obtain ⟨t₀, ht₀, ht₀left⟩ :=
    exists_positive_time_strictlyPositiveAtLeft_of_uniformInitialTrace
      (c := c) hu₀left htrace
  obtain ⟨C, hC, henv⟩ :=
    exists_weightedDifference_pointwise_envelope_of_H1
      (hu2 t₀ ht₀) hU2 (hW2 t₀ ht₀) (hWx2 t₀ ht₀)
  have hwpos : ∀ x, 0 < coMovingPath c u t₀ x := by
    intro x
    exact hpositive t₀ (x + c * t₀) ht₀
  obtain ⟨kappaTilde, hkappaTilde, hkappaTildeκ₁,
      hkappaTildeEta, hkappaTildeCap, hkappaTildeTwo,
      D, hDone, hBD, hseed⟩ :=
    exists_lowerBarrierPlateau_seed_of_profile_bounds
      hκ hκ₁ heta hcap (hu2 t₀ ht₀).continuous hwpos ht₀left
        hC henv htail
  exact ⟨t₀, ht₀, kappaTilde, hkappaTilde,
    hkappaTildeκ₁, hkappaTildeEta, hkappaTildeCap,
    hkappaTildeTwo, D, hDone, hBD, hseed⟩

/-- Canonical negative-sensitivity seed.  Exact weighted initial closeness is
propagated to a positive global slice by the natural `H⁰` and `H¹` producers;
the one-sided initial floor supplies strict positivity without a whole-line
uniform lower bound. -/
theorem
    wholeLineCauchyGlobal_exists_positive_time_lowerBarrierPlateau_seed_chi_neg_natural
    (p : CMParams) (hchi : p.χ < 0)
    {c κ₁ eta cap B : ℝ} {U V : ℝ → ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hκ₁ : kappa c < κ₁) (heta : kappa c < eta)
    (heta_one : eta < 1) (hcap : kappa c < cap)
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (htail : HasWaveRightTailAsymptotic c κ₁ U)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hu₀left : StrictlyPositiveAtLeft u₀.1)
    (hinitial : WeightedL2InitialCloseness eta u₀.1 U) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∃ kappaTilde : ℝ,
        kappa c < kappaTilde ∧
        kappaTilde < κ₁ ∧
        kappaTilde < eta ∧
        kappaTilde < cap ∧
        kappaTilde < 2 * kappa c ∧
        ∃ D : ℝ, 1 ≤ D ∧ B < D ∧
          ∀ x, lowerBarrierPlateau (kappa c) kappaTilde D x ≤
            coMovingPath c (wholeLineCauchyGlobalU p u₀) t₀ x := by
  have hregime : WholeLineCauchyCeilingRegime p :=
    WholeLineCauchyCeilingRegime.of_nonpositive hchi.le
  have hκ : 0 < kappa c :=
    kappa_pos_of_stabilitySpeedBaseline_lt
      (paper5CorrectedCStarStar_baseline_le p) hc
  have heta_pos : 0 < eta := hκ.trans heta
  have hs : Paper5WaveStaticNaturalData p c U V :=
    paper5WaveStaticNaturalData_of_wave
      p (ne_of_lt hchi) hc hTW hbound hreg
  apply exists_positive_time_lowerBarrierPlateau_seed_of_H1
    (u := wholeLineCauchyGlobalU p u₀) (u₀ := u₀.1)
    (U := U) hκ hκ₁ heta hcap
  · exact wholeLineCauchyGlobal_hasUniformInitialTrace p u₀
  · exact hu₀left
  · intro t x ht
    exact wholeLineCauchyGlobal_pos_of_posAtBot
      p hregime u₀ hu₀ hu₀left ht x
  · intro t ht
    exact wholeLineCauchyGlobalU_coMoving_contDiff_two_positive
      p hregime u₀ hu₀ ht
  · exact hreg.U_contDiff_two hTW
  · intro t ht
    apply paper5WeightedPopulation_sq_integrable_of_weighted_difference
    exact
      wholeLineCauchyGlobal_fullWeightedL2_integrable_wave_chi_nonpos_of_initialCloseness
        (D := paper5ConcreteLu p)
        (E := paper5WaveSecondDerivativeBound p c)
        (Kflux := paper5WaveFluxBound p)
        (FD := paper5WaveFluxDerivativeBound p)
        (B := paper5WaveShiftedReactionBound p)
        p hchi.le u₀ ht heta_pos heta_one hTW hbound hreg hs.hD hs.hFD
          hs.hB hs.hUd hs.hUdd hs.hUddcont hs.hflux hs.hfluxd
          hs.hflux_has hs.hfluxd_cont hs.hreact hs.hreact_cont
          hs.hgrad_int hinitial
  · intro t ht
    exact
      paper5WeightedPopulationX_sq_integrable_global_chi_nonpos_of_initialCloseness
        (Blog := 1) (D := paper5ConcreteLu p)
        (E := paper5WaveSecondDerivativeBound p c)
        (Kflux := paper5WaveFluxBound p)
        (FD := paper5WaveFluxDerivativeBound p)
        (B := paper5WaveShiftedReactionBound p)
        p hchi.le u₀ hu₀ ht hs.hBlog heta_pos heta_one hTW hbound
          hreg hs.hlog hs.hD hs.hFD hs.hB hs.hUd hs.hUdd hs.hUddcont
          hs.hflux hs.hfluxd hs.hflux_has hs.hfluxd_cont hs.hreact
          hs.hreact_cont hs.hgrad_int hinitial
  · exact htail

section AxiomAudit

#print axioms
  exists_positive_time_strictlyPositiveAtLeft_of_uniformInitialTrace
#print axioms eventually_half_exp_le_of_wave_tail_and_weighted_envelope
#print axioms lowerBarrierRaw_xplus_le_half_exp_of_lt_two
#print axioms exists_lowerBarrierPlateau_seed_of_profile_bounds
#print axioms exists_positive_time_lowerBarrierPlateau_seed_of_H1
#print axioms
  wholeLineCauchyGlobal_exists_positive_time_lowerBarrierPlateau_seed_chi_neg_natural

end AxiomAudit

end ShenWork.Paper1
