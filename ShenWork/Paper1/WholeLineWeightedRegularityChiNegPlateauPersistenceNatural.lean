import ShenWork.Paper1.WholeLineWeightedRegularityChiNegFixedTimePlateauSeedNatural
import ShenWork.Paper1.WholeLineWeightedRegularityChiNegPlateauPropagationNatural
import ShenWork.Paper1.WholeLineWeightedRegularityWeightedConvergenceNatural

open Filter MeasureTheory Set Topology Real

noncomputable section

namespace ShenWork.Paper1

/-!
# Canonical persistence of a negative-sensitivity lower plateau

The exact weighted convergence supplies one common scaled upper trap on all
late canonical restart windows.  At the first such seam, positive-time
regularity and the preserved one-sided floor produce a lower plateau.  Its
coefficient is chosen above the genuinely scaled Lemma-4.2 threshold, and
the closed-window comparison then propagates the same plateau forever.
-/

/-- The canonical strictly negative-sensitivity orbit admits one stationary
positive lower plateau on every sufficiently late closed restart window.

The coefficient-one conditions used by the subsolution operator and the
amplitude-`Q` trap are kept separate.  In particular, the seed is asked to
dominate `paperScaledDMin p Q ...`, not merely the normalized `paperDMin`.
-/
theorem
    wholeLineCauchyGlobal_exists_persistent_lowerBarrierPlateau_chi_neg_natural
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : p.χ < 0)
    {c eta kappaOne : ℝ} {U V : ℝ → ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hstrict : HasStrictWaveUpperTailBound p c U)
    (hkappaOne : kappa c < kappaOne)
    (hkappaOne_one : kappaOne < 1)
    (htail : HasWaveRightTailAsymptotic c kappaOne U)
    (hroot : paper531RootMinus c
      (paper531ConcreteStabilityBudget p hregime).A
      (paper531ConcreteStabilityBudget p hregime).B < eta)
    (hetaCap : eta < stabilityWeightCap p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hu₀left : StrictlyPositiveAtLeft u₀.1)
    (hinitial : WeightedL2InitialCloseness eta u₀.1 U) :
    ∃ N : ℕ, ∃ kappaTilde D Q : ℝ,
      1 ≤ Q ∧
      kappa c < kappaTilde ∧
      kappaTilde < kappaOne ∧
      kappaTilde < eta ∧
      PaperLemma42ExactConditions p c (kappa c) kappaTilde 1 ∧
      1 ≤ D ∧
      paperScaledDMin p Q (kappa c) kappaTilde c < D ∧
      (∀ x, lowerBarrierPlateau (kappa c) kappaTilde D x ≤
        constantSubsolutionThreshold p.χ (kappa c) kappaTilde D) ∧
      ∀ n : ℕ, N ≤ n →
        ∀ r ∈ Set.Icc (0 : ℝ) (wholeLineCauchyGlobalStep p u₀), ∀ x,
          lowerBarrierPlateau (kappa c) kappaTilde D x ≤
            wholeLineCauchyGlobalU p u₀
              (((n : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀ + r)
              (x + c * (((n : ℝ) + 1) *
                wholeLineCauchyGlobalStep p u₀ + r)) := by
  have hbaseline : stabilitySpeedBaseline p ≤
      paper5CorrectedCStarStar p p.χ :=
    paper5CorrectedCStarStar_baseline_le p
  have hc_two : 2 < c :=
    two_lt_of_stabilitySpeedBaseline_lt hbaseline hc
  have hkappa : 0 < kappa c := kappa_pos_of_two_lt hc_two
  have hkappa_one : kappa c < 1 := kappa_lt_one_of_two_lt hc_two
  have hkappa_eta : kappa c < eta :=
    ((paper531ConcreteStabilityBudget p hregime).kappa_le_rootMinus hc).trans_lt
      hroot
  have heta : 0 < eta := hkappa.trans hkappa_eta
  have heta_one : eta < 1 := by
    have hcap_one : stabilityWeightCap p ≤ 1 := by
      unfold stabilityWeightCap
      rw [div_le_one (by positivity)]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)
    exact hetaCap.trans_le hcap_one
  have hbound : HasWaveUpperTailBound p c U :=
    hstrict.hasWaveUpperTailBound
  have hs : Paper5WaveStaticNaturalData p c U V :=
    paper5WaveStaticNaturalData_of_wave p (ne_of_lt hchi) hc hTW hbound hreg
  have hconv : CoMovingWeightedL2Convergence eta c
      (wholeLineCauchyGlobalU p u₀) U :=
    wholeLineCauchyGlobal_coMovingWeightedL2Convergence_chi_neg_natural
      p hregime hchi hc hTW hbound hreg hroot hetaCap u₀ hu₀ hinitial
  obtain ⟨N, Q, hQ, htrap⟩ :=
    exists_eventual_common_global_inTimeWaveTrapSet_chi_nonpos
      (Blog := 1) (D := paper5ConcreteLu p)
      (E := paper5WaveSecondDerivativeBound p c)
      (Kflux := paper5WaveFluxBound p)
      (FD := paper5WaveFluxDerivativeBound p)
      (B := paper5WaveShiftedReactionBound p)
      p hchi.le u₀ hu₀ hs.hBlog heta heta_one hkappa hkappa_eta.le
        hTW hbound hreg hs.hlog hs.hD hs.hFD hs.hB hs.hUd hs.hUdd
        hs.hUddcont hs.hflux hs.hfluxd hs.hflux_has hs.hfluxd_cont
        hs.hreact hs.hreact_cont hs.hgrad_int hconv
  let cap : ℝ := min ((1 + p.α) * kappa c)
    (min (p.m * kappa c + 1 / 2) 1)
  have hkappa_cap : kappa c < cap := by
    dsimp only [cap]
    apply lt_min
    · nlinarith [p.hα]
    · apply lt_min
      · nlinarith [p.hm, hkappa]
      · exact hkappa_one
  have hcapRange :
      cap ≤ min ((1 + p.α) * kappa c)
        (min (p.m * kappa c + 1 / 2) 1) := le_rfl
  let step := wholeLineCauchyGlobalStep p u₀
  have hstep : 0 < step := by
    simpa only [step] using wholeLineCauchyGlobalStep_pos p u₀
  let t₀ : ℝ := ((N : ℝ) + 1) * step
  have ht₀ : 0 < t₀ := by
    dsimp only [t₀]
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    positivity
  obtain ⟨kappaTilde, D, hkappaTilde, hkappaTildeOne,
      hkappaTildeEta, _hkappaTildeCap, _hkappaTildeTwo,
      hcondQ, hD1, _hDnormalized, hDscaled, hplateau, hseed⟩ :=
    wholeLineCauchyGlobal_exists_compatible_lowerBarrierPlateau_seed_at_time_chi_neg
      p hchi
      (fun kappaTilde =>
        paperScaledDMin p Q (kappa c) kappaTilde c)
      hc hQ hkappaOne hkappa_eta heta_one hkappa_cap hcapRange
        hregime.alpha_le ht₀ hTW hbound hreg htail u₀ hu₀ hu₀left hinitial
  have hcondOne : PaperLemma42ExactConditions
      p c (kappa c) kappaTilde 1 :=
    { hκ0 := hcondQ.hκ0
      hκ1 := hcondQ.hκ1
      hgap := hcondQ.hgap
      hrange := hcondQ.hrange
      hM := le_rfl
      hc := hcondQ.hc
      hχ := hcondQ.hχ
      hα_le := hcondQ.hα_le }
  have hseed' : ∀ x,
      lowerBarrierPlateau (kappa c) kappaTilde D x ≤
        wholeLineCauchyGlobalU p u₀
          (((N : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀)
          (x + c * (((N : ℝ) + 1) *
            wholeLineCauchyGlobalStep p u₀)) := by
    simpa only [coMovingPath, t₀, step] using hseed
  have hpersist :=
    wholeLineCauchyGlobal_ge_lowerBarrierPlateau_on_all_late_windows_chiNonpos
      p hchi.le u₀ hu₀ hcondOne hQ hDscaled hD1 hplateau htrap hseed'
  exact ⟨N, kappaTilde, D, Q, hQ, hkappaTilde, hkappaTildeOne,
    hkappaTildeEta, hcondOne, hD1, hDscaled, hplateau, hpersist⟩

/-- Every time after the first late seam belongs to one of the canonical
closed windows used by the plateau induction. -/
theorem exists_canonical_closed_window_coordinates
    {delta t : ℝ} (hdelta : 0 < delta) (N : ℕ)
    (ht : ((N : ℝ) + 1) * delta ≤ t) :
    ∃ n : ℕ, N ≤ n ∧ ∃ r ∈ Set.Icc (0 : ℝ) delta,
      t = ((n : ℝ) + 1) * delta + r := by
  let k : ℕ := Nat.floor (t / delta)
  have ht0 : 0 ≤ t := by
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    exact (mul_nonneg (by linarith) hdelta.le).trans ht
  have hratio0 : 0 ≤ t / delta := div_nonneg ht0 hdelta.le
  have hklo : (k : ℝ) ≤ t / delta := by
    simpa only [k] using Nat.floor_le hratio0
  have hkhi : t / delta < (k : ℝ) + 1 := by
    simpa only [k] using Nat.lt_floor_add_one (t / delta)
  have hkNat : N + 1 ≤ k := by
    apply Nat.le_floor
    exact (le_div_iff₀ hdelta).2 (by
      simpa only [Nat.cast_add, Nat.cast_one] using ht)
  have hkpos : 0 < k :=
    lt_of_lt_of_le Nat.zero_lt_one (le_trans (Nat.succ_le_succ (Nat.zero_le N)) hkNat)
  let n : ℕ := k.pred
  have hn : N ≤ n := by
    apply Nat.le_pred_of_lt
    exact (Nat.lt_succ_self N).trans_le hkNat
  have hnk : n + 1 = k := by
    dsimp only [n]
    simpa only [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hkpos
  let r : ℝ := t - (k : ℝ) * delta
  have hr0 : 0 ≤ r := by
    dsimp only [r]
    exact sub_nonneg.mpr ((le_div_iff₀ hdelta).1 hklo)
  have hrlt : r < delta := by
    dsimp only [r]
    have := (div_lt_iff₀ hdelta).1 hkhi
    nlinarith
  refine ⟨n, hn, r, ⟨hr0, hrlt.le⟩, ?_⟩
  have hnkReal : (n : ℝ) + 1 = (k : ℝ) := by
    exact_mod_cast hnk
  rw [hnkReal]
  dsimp only [r]
  ring

/-- A windowwise lower comparison is automatically an all-real-time lower
comparison after the first late seam. -/
theorem wholeLineCauchyGlobal_ge_lowerBarrierPlateau_of_late_time
    (p : CMParams) (u₀ : WholeLineBUC)
    {N : ℕ} {c kappa kappaTilde D t : ℝ}
    (hpersist : ∀ n : ℕ, N ≤ n →
      ∀ r ∈ Set.Icc (0 : ℝ) (wholeLineCauchyGlobalStep p u₀), ∀ x,
        lowerBarrierPlateau kappa kappaTilde D x ≤
          wholeLineCauchyGlobalU p u₀
            (((n : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀ + r)
            (x + c * (((n : ℝ) + 1) *
              wholeLineCauchyGlobalStep p u₀ + r)))
    (ht : ((N : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀ ≤ t) (x : ℝ) :
    lowerBarrierPlateau kappa kappaTilde D x ≤
      wholeLineCauchyGlobalU p u₀ t (x + c * t) := by
  obtain ⟨n, hn, r, hr, htime⟩ :=
    exists_canonical_closed_window_coordinates
      (wholeLineCauchyGlobalStep_pos p u₀) N ht
  rw [htime]
  exact hpersist n hn r hr x

/-- A persistent positive plateau gives a fixed positive spatial floor on a
fixed left half-line at every sufficiently late real time. -/
theorem wholeLineCauchyGlobal_eventual_coMoving_left_floor_of_persistent_plateau
    (p : CMParams) (u₀ : WholeLineBUC)
    {N : ℕ} {c kappa kappaTilde D : ℝ}
    (hkappa : 0 < kappa) (hgap : kappa < kappaTilde) (hD : 1 ≤ D)
    (hpersist : ∀ n : ℕ, N ≤ n →
      ∀ r ∈ Set.Icc (0 : ℝ) (wholeLineCauchyGlobalStep p u₀), ∀ x,
        lowerBarrierPlateau kappa kappaTilde D x ≤
          wholeLineCauchyGlobalU p u₀
            (((n : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀ + r)
            (x + c * (((n : ℝ) + 1) *
              wholeLineCauchyGlobalStep p u₀ + r))) :
    ∃ T R d : ℝ, 0 < d ∧
      ∀ t, T ≤ t → ∀ x, x ≤ R →
        d ≤ wholeLineCauchyGlobalU p u₀ t (x + c * t) := by
  let T : ℝ := ((N : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀
  let R : ℝ := lowerBarrierXPlus kappa kappaTilde D
  let d : ℝ := lowerBarrierRaw kappa kappaTilde D R
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hdpos : 0 < d := by
    simpa only [d, R] using
      lowerBarrierRaw_pos_at_xplus hkappa (sub_pos.mpr hgap) hDpos
  refine ⟨T, R, d, hdpos, ?_⟩
  intro t ht x hx
  have hlate := wholeLineCauchyGlobal_ge_lowerBarrierPlateau_of_late_time
    p u₀ hpersist (by simpa only [T] using ht) x
  rw [lowerBarrierPlateau_eq_const_of_le (by simpa only [R] using hx)] at hlate
  simpa only [d, R] using hlate

#print axioms
  wholeLineCauchyGlobal_exists_persistent_lowerBarrierPlateau_chi_neg_natural
#print axioms exists_canonical_closed_window_coordinates
#print axioms wholeLineCauchyGlobal_ge_lowerBarrierPlateau_of_late_time
#print axioms
  wholeLineCauchyGlobal_eventual_coMoving_left_floor_of_persistent_plateau

end ShenWork.Paper1
