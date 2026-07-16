import ShenWork.Paper1.WholeLineWeightedRegularityScaledTrapWindowNatural
import ShenWork.Paper1.WholeLineWeightedRegularityLateH1WindowNatural

open Filter MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# One scaled trap constant for a family of positive-time windows

The single-window producer returns an existential scale after the trajectory
has been fixed.  That statement cannot by itself exchange `forall` and
`exists` over an infinite family.  Here the Agmon constant and trap scale are
chosen explicitly from the common `H0/H1` budgets before the family index is
introduced.
-/

/-- Common exact-weight `H0/H1` budgets and a common physical height bound
give one scaled paper-trap constant for every member of an arbitrary family
of compact positive-time windows. -/
theorem exists_common_shifted_inTimeWaveTrapSet_of_uniform_weighted_H1_family
    {ι : Type*} {a b kappa eta S F G : ℝ}
    {q : ι → ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hkappa : 0 < kappa) (hkappaEta : kappa ≤ eta)
    (hF : 0 ≤ F) (hG : 0 ≤ G)
    (_hab : a ≤ b)
    (hqC : ∀ i, ∀ t ∈ Set.Icc a b, IsCUnifBdd (q i t))
    (hq0 : ∀ i, ∀ t ∈ Set.Icc a b, ∀ x, 0 ≤ q i t x)
    (hqS : ∀ i, ∀ t ∈ Set.Icc a b, ∀ x, q i t x ≤ S)
    (hq2 : ∀ i, ∀ t ∈ Set.Icc a b, ContDiff ℝ 2 (q i t))
    (hU2 : ContDiff ℝ 2 U)
    (hUexp : ∀ x, U x ≤ Real.exp (-kappa * x))
    (hW : ∀ i, ∀ t ∈ Set.Icc a b,
      Integrable (fun x => paper5WeightedPopulation eta (q i) U t x ^ 2) ∧
      (∫ x, paper5WeightedPopulation eta (q i) U t x ^ 2) ≤ F ^ 2)
    (hWx : ∀ i, ∀ t ∈ Set.Icc a b,
      Integrable (fun x => paper5WeightedPopulationX eta (q i) U t x ^ 2) ∧
      (∫ x, paper5WeightedPopulationX eta (q i) U t x ^ 2) ≤ G ^ 2) :
    ∃ Q : ℝ, 1 ≤ Q ∧ ∀ i,
      InTimeWaveTrapSet kappa Q (b - a) (fun s => q i (a + s)) := by
  let C := Real.sqrt (2 * F ^ 2 + 2 * F * G)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  let Q : ℝ := max S (1 + C)
  have hQ : max S (1 + C) ≤ Q := le_rfl
  have hQone : 1 ≤ Q :=
    le_trans (by linarith : (1 : ℝ) ≤ 1 + C)
      (le_max_right S (1 + C))
  refine ⟨Q, hQone, ?_⟩
  intro i
  apply inTimeWaveTrapSet_of_uniform_bound_and_weighted_envelope
    hkappa hkappaEta hC hQ
  · intro s hs
    apply hqC i (a + s)
    constructor <;> linarith [hs.1, hs.2]
  · intro s hs x
    apply hq0 i (a + s)
    constructor <;> linarith [hs.1, hs.2]
  · intro s hs x
    apply hqS i (a + s)
    constructor <;> linarith [hs.1, hs.2]
  · exact hUexp
  · intro s hs x
    have ht : a + s ∈ Set.Icc a b := by
      constructor <;> linarith [hs.1, hs.2]
    exact weightedDifference_pointwise_envelope_of_H1_budgets
      hF hG (hq2 i (a + s) ht) hU2
        (hW i (a + s) ht).1 (hW i (a + s) ht).2
        (hWx i (a + s) ht).1 (hWx i (a + s) ht).2 x

/-- A nonpositive-sensitivity orbit converging in the exact moving-frame
weight has one scaled paper-trap constant on every sufficiently late
canonical restart window.  Both numerical Sobolev budgets and the resulting
trap scale are selected before the restart index is introduced. -/
theorem exists_eventual_common_shifted_inTimeWaveTrapSet_chi_nonpos
    (p : CMParams) (hchi : p.χ ≤ 0)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {Blog eta c D E Kflux FD B : ℝ}
    (hBlog : 0 ≤ Blog) (heta : 0 < eta) (heta_one : eta < 1)
    (hkappa : 0 < kappa c) (hkappaEta : kappa c ≤ eta)
    {Uw Vw : ℝ → ℝ}
    (hTW : IsTravelingWave p c Uw Vw)
    (hbound : HasWaveUpperTailBound p c Uw)
    (hreg : TravelingWaveRegularity p c Uw Vw)
    (hlog : ∀ y, |deriv Uw y / Uw y| ≤ Blog)
    (hD : 0 ≤ D) (hFD : 0 ≤ FD) (hB : 0 ≤ B)
    (hUd : ∀ y, |deriv Uw y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv Uw) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv Uw)))
    (hflux : ∀ y, |wholeLineTravelingWaveFlux p Uw Vw y| ≤ Kflux)
    (hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p Uw Vw) y| ≤ FD)
    (hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p Uw Vw)
      (deriv (wholeLineTravelingWaveFlux p Uw Vw) y) y)
    (hfluxd_cont : Continuous
      (deriv (wholeLineTravelingWaveFlux p Uw Vw)))
    (hreact : ∀ y, |wholeLineCauchyShiftedReaction p Uw y| ≤ B)
    (hreact_cont : Continuous (wholeLineCauchyShiftedReaction p Uw))
    (hgrad_int : ∀ q, 0 < q → ∀ x, IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p Uw Vw) x) volume 0 q)
    (hconv : CoMovingWeightedL2Convergence eta c
      (wholeLineCauchyGlobalU p u₀) Uw) :
    ∃ N : ℕ, ∃ Q : ℝ, 1 ≤ Q ∧
      ∀ n : ℕ, N ≤ n →
        let datum := wholeLineCauchyGlobalTranslatedDatumIndex p u₀ c n
        let Traj := wholeLineCauchyBUCMildFixedPoint p
          (wholeLineCauchyGlobalClamp_pos p u₀).le
          (wholeLineCauchyGlobalSegmentTime_pos p u₀).le datum
          (wholeLineCauchyGlobalSegmentTime_rate p u₀)
        let q : ℝ → ℝ → ℝ := fun s x =>
          (wholeLineBUCTrajectoryExtend
            (wholeLineCauchyGlobalSegmentTime_pos p u₀).le Traj s).1
              (x + c * s)
        InTimeWaveTrapSet (kappa c) Q
          (wholeLineCauchyGlobalStep p u₀)
          (fun s => q (wholeLineCauchyGlobalStep p u₀ + s)) := by
  let M := wholeLineCauchyGlobalClamp p u₀
  let T := wholeLineCauchyGlobalSegmentTime p u₀
  let a := wholeLineCauchyGlobalStep p u₀
  have hM : 0 ≤ M := by
    simpa only [M] using (wholeLineCauchyGlobalClamp_pos p u₀).le
  have hT : 0 ≤ T := by
    simpa only [T] using (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
  have ha : 0 < a := by
    simpa only [a] using wholeLineCauchyGlobalStep_pos p u₀
  have haT : a ≤ T := by
    dsimp only [a, T]
    rw [wholeLineCauchyGlobalSegmentTime_eq_two_step]
    linarith [wholeLineCauchyGlobalStep_pos p u₀]
  have hregime : WholeLineCauchyCeilingRegime p :=
    WholeLineCauchyCeilingRegime.of_nonpositive hchi
  obtain ⟨N, F, G, hF, hG, hbudget⟩ :=
    exists_eventual_common_weighted_H1_restart_window_chi_nonpos
      p hchi u₀ hu₀ hBlog heta heta_one hTW hbound hreg hlog
        hD hFD hB hUd hUdd hUddcont hflux hfluxd hflux_has hfluxd_cont
        hreact hreact_cont hgrad_int hconv
  let ι := {n : ℕ // N ≤ n}
  let datum : ι → WholeLineBUC := fun i =>
    wholeLineCauchyGlobalTranslatedDatumIndex p u₀ c i.1
  let Traj : ι → WholeLineBUCTrajectory T := fun i =>
    wholeLineCauchyBUCMildFixedPoint p hM hT (datum i)
      (wholeLineCauchyGlobalSegmentTime_rate p u₀)
  let u : ι → ℝ → ℝ → ℝ := fun i s x =>
    (wholeLineBUCTrajectoryExtend hT (Traj i) s).1 x
  let q : ι → ℝ → ℝ → ℝ := fun i s x => u i s (x + c * s)
  have hstrip : ∀ i : ι, ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (Traj i z).1 x ∈ Set.Icc (0 : ℝ) M := by
    intro i z x
    let d : ℝ := c * ((i.1 : ℝ) * a)
    have htranslate : datum i = wholeLineBUCTranslate d
        (wholeLineCauchyGlobalDatum p u₀ i.1) := by
      rfl
    have hfp := wholeLineCauchyBUCMildFixedPoint_spatialTranslate
      (d := d) p hM hT (wholeLineCauchyGlobalDatum p u₀ i.1)
        (wholeLineCauchyGlobalSegmentTime_rate p u₀)
    have heq : Traj i = wholeLineBUCTrajectorySpatialTranslate hT d
        (wholeLineCauchyGlobalSegment p u₀ i.1) := by
      dsimp only [Traj]
      rw [htranslate]
      simpa only [wholeLineCauchyGlobalSegment, M, T] using hfp
    rw [heq]
    simpa only [wholeLineBUCTrajectorySpatialTranslate_apply, M, T] using
      (wholeLineCauchyGlobalDatum_segment_bounds
        p hregime u₀ hu₀ i.1).2.1 z (x + d)
  have hsMem : ∀ s ∈ Set.Icc a T, s ∈ Set.Icc (0 : ℝ) T := by
    intro s hs
    exact ⟨ha.le.trans hs.1, hs.2⟩
  have hqC : ∀ i : ι, ∀ s ∈ Set.Icc a T, IsCUnifBdd (q i s) := by
    intro i s _hs
    dsimp only [q, coMovingPath, u]
    exact IsCUnifBdd.shift
      (WholeLineBUC.isCUnifBdd (wholeLineBUCTrajectoryExtend hT (Traj i) s))
      (c * s)
  have hq0 : ∀ i : ι, ∀ s ∈ Set.Icc a T, ∀ x, 0 ≤ q i s x := by
    intro i s hs x
    have hext : wholeLineBUCTrajectoryExtend hT (Traj i) s =
        Traj i ⟨s, hsMem s hs⟩ :=
      wholeLineBUCTrajectoryExtend_eq hT (Traj i) (hsMem s hs)
    simpa only [q, coMovingPath, u, hext] using
      (hstrip i ⟨s, hsMem s hs⟩ (x + c * s)).1
  have hqM : ∀ i : ι, ∀ s ∈ Set.Icc a T, ∀ x, q i s x ≤ M := by
    intro i s hs x
    have hext : wholeLineBUCTrajectoryExtend hT (Traj i) s =
        Traj i ⟨s, hsMem s hs⟩ :=
      wholeLineBUCTrajectoryExtend_eq hT (Traj i) (hsMem s hs)
    simpa only [q, coMovingPath, u, hext] using
      (hstrip i ⟨s, hsMem s hs⟩ (x + c * s)).2
  have hq2 : ∀ i : ι, ∀ s ∈ Set.Icc a T, ContDiff ℝ 2 (q i s) := by
    intro i s hs
    have hs0 : 0 < s := ha.trans_le hs.1
    let zs : Set.Icc (0 : ℝ) T := ⟨s, hs0.le, hs.2⟩
    have hwindow : ∀ r ∈ Set.Icc (s / 2) s, ∀ x,
        (wholeLineBUCTrajectoryExtend hT (Traj i) r).1 x ∈
          Set.Icc (0 : ℝ) M := by
      intro r hr x
      have hrT : r ∈ Set.Icc (0 : ℝ) T :=
        ⟨(half_pos hs0).le.trans hr.1, hr.2.trans hs.2⟩
      rw [wholeLineBUCTrajectoryExtend_eq hT (Traj i) hrT]
      exact hstrip i ⟨r, hrT⟩ x
    have hslice : ContDiff ℝ 2 (fun x => (Traj i zs).1 x) := by
      simpa only [Traj] using
        (wholeLineCauchyBUCMildFixedPoint_slice_contDiff_two_positive
          (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
          p hM hT (datum i)
            (wholeLineCauchyGlobalSegmentTime_rate p u₀) zs hs0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) hwindow)
    have hext : wholeLineBUCTrajectoryExtend hT (Traj i) s = Traj i zs :=
      wholeLineBUCTrajectoryExtend_eq hT (Traj i) zs.2
    dsimp only [q, coMovingPath, u]
    rw [hext]
    exact ContDiff.two_shift hslice (c * s)
  have hW : ∀ i : ι, ∀ s ∈ Set.Icc a T,
      Integrable (fun x => paper5WeightedPopulation eta (q i) Uw s x ^ 2) ∧
      (∫ x, paper5WeightedPopulation eta (q i) Uw s x ^ 2) ≤ F ^ 2 := by
    intro i s hs
    have hbase := (hbudget i.1 i.2).1 s (hsMem s hs)
    constructor
    · exact hbase.1.congr (Eventually.of_forall fun x =>
        (paper5WeightedPopulation_sq_eq_weighted_difference
          (eta := eta) (t := s) (x := x) (u := q i) (U := Uw)).symm)
    · calc
        (∫ x, paper5WeightedPopulation eta (q i) Uw s x ^ 2) =
            ∫ x, Real.exp (2 * eta * x) * |q i s x - Uw x| ^ 2 := by
              apply integral_congr_ae
              filter_upwards with x
              exact paper5WeightedPopulation_sq_eq_weighted_difference
        _ ≤ F ^ 2 := by
          simpa only [q, coMovingPath, u, Traj, datum, M, T] using hbase.2
  have hWx : ∀ i : ι, ∀ s ∈ Set.Icc a T,
      Integrable (fun x => paper5WeightedPopulationX eta (q i) Uw s x ^ 2) ∧
      (∫ x, paper5WeightedPopulationX eta (q i) Uw s x ^ 2) ≤ G ^ 2 := by
    intro i s hs
    have hbase := (hbudget i.1 i.2).2 s hs
    simpa only [q, u, Traj, datum, M, T, a] using hbase
  obtain ⟨Q, hQ, htrap⟩ :=
    exists_common_shifted_inTimeWaveTrapSet_of_uniform_weighted_H1_family
      hkappa hkappaEta hF hG haT hqC hq0 hqM hq2
        (hreg.U_contDiff_two hTW) hbound.le_exp hW hWx
  refine ⟨N, Q, hQ, ?_⟩
  intro n hn
  let i : ι := ⟨n, hn⟩
  have hi := htrap i
  have hTa : T - a = a := by
    dsimp only [T, a]
    rw [wholeLineCauchyGlobalSegmentTime_eq_two_step]
    ring
  rw [hTa] at hi
  simpa only [q, u, Traj, datum, i, M, T, a, coMovingPath] using hi

section AxiomAudit

#print axioms
  exists_common_shifted_inTimeWaveTrapSet_of_uniform_weighted_H1_family
#print axioms exists_eventual_common_shifted_inTimeWaveTrapSet_chi_nonpos

end AxiomAudit

end ShenWork.Paper1
