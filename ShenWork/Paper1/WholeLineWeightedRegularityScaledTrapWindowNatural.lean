import ShenWork.Paper1.WholeLineWeightedRegularityScaledTrapNatural
import ShenWork.Paper1.WholeLineWeightedRegularityPointwiseEnvelopeNatural
import ShenWork.Paper1.WholeLineWeightedRegularityForcingWindowNatural

open Filter MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Common scaled traps on compact positive-time windows

The exact-weight `H0` and `H1` producers already choose numerical square
budgets uniformly on a compact positive-time window.  This file keeps those
budgets quantitative through the one-dimensional Agmon estimate.  The result
is one exponentially decaying pointwise envelope, hence one scaled paper trap,
for every slice in the window.  No coefficient-one trap or left-tail
convergence is assumed.
-/

/-- Pointwise identification of the weighted population square with the
physical exponentially weighted error density. -/
theorem paper5WeightedPopulation_sq_eq_weighted_difference
    {eta t x : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ} :
    paper5WeightedPopulation eta u U t x ^ 2 =
      Real.exp (2 * eta * x) * |u t x - U x| ^ 2 := by
  unfold paper5WeightedPopulation
  rw [mul_pow, sq_abs]
  congr 1
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- Quantitative whole-line Agmon estimate for one exact-weight slice.  The
two numerical square budgets remain visible in the conclusion, so the same
constant can later be used on a whole time window. -/
theorem weightedDifference_pointwise_envelope_of_H1_budgets
    {eta t F G : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hu2 : ContDiff ℝ 2 (u t)) (hU2 : ContDiff ℝ 2 U)
    (hW2 : Integrable (fun x =>
      paper5WeightedPopulation eta u U t x ^ 2))
    (hW2le : (∫ x, paper5WeightedPopulation eta u U t x ^ 2) ≤ F ^ 2)
    (hWx2 : Integrable (fun x =>
      paper5WeightedPopulationX eta u U t x ^ 2))
    (hWx2le : (∫ x, paper5WeightedPopulationX eta u U t x ^ 2) ≤ G ^ 2) :
    ∀ x, |u t x - U x| ≤
      Real.sqrt (2 * F ^ 2 + 2 * F * G) * Real.exp (-eta * x) := by
  let W : ℝ → ℝ := paper5WeightedPopulation eta u U t
  let Wx : ℝ → ℝ := paper5WeightedPopulationX eta u U t
  have hWcont : Continuous W := by
    dsimp only [W]
    unfold paper5WeightedPopulation
    fun_prop
  have hWxcont : Continuous Wx := by
    dsimp only [Wx]
    exact paper5WeightedPopulationX_continuous hu2 hU2
  have hderiv : ∀ x, HasDerivAt W (Wx x) x := by
    intro x
    dsimp only [W, Wx]
    exact paper5WeightedPopulation_space_hasDerivAt
      (hu2.differentiable (by norm_num) x)
      (hU2.differentiable (by norm_num) x)
  have hW2' : Integrable (fun x => W x ^ 2) := by
    simpa only [W] using hW2
  have hWx2' : Integrable (fun x => Wx x ^ 2) := by
    simpa only [Wx] using hWx2
  have hIW0 : 0 ≤ ∫ x, W x ^ 2 :=
    integral_nonneg (fun x => sq_nonneg (W x))
  have hIWx0 : 0 ≤ ∫ x, Wx x ^ 2 :=
    integral_nonneg (fun x => sq_nonneg (Wx x))
  have hsqrtW : Real.sqrt (∫ x, W x ^ 2) ≤ F := by
    calc
      Real.sqrt (∫ x, W x ^ 2) ≤ Real.sqrt (F ^ 2) :=
        Real.sqrt_le_sqrt (by simpa only [W] using hW2le)
      _ = F := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hF]
  have hsqrtWx : Real.sqrt (∫ x, Wx x ^ 2) ≤ G := by
    calc
      Real.sqrt (∫ x, Wx x ^ 2) ≤ Real.sqrt (G ^ 2) :=
        Real.sqrt_le_sqrt (by simpa only [Wx] using hWx2le)
      _ = G := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hG]
  have hK0 : 0 ≤ 2 * F ^ 2 + 2 * F * G := by positivity
  intro x
  have hraw := wholeLine_H1_sq_pointwise_le
    hWcont hWxcont hderiv hW2' hWx2' x
  have hprod :
      2 * Real.sqrt (∫ y, W y ^ 2) * Real.sqrt (∫ y, Wx y ^ 2) ≤
        2 * F * G := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hsqrtW (by norm_num)) hsqrtWx
      (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) hF)
  have hWsq : W x ^ 2 ≤ 2 * F ^ 2 + 2 * F * G := by
    calc
      W x ^ 2 ≤ 2 * (∫ y, W y ^ 2) +
          2 * Real.sqrt (∫ y, W y ^ 2) *
            Real.sqrt (∫ y, Wx y ^ 2) := hraw
      _ ≤ 2 * F ^ 2 + 2 * F * G :=
        add_le_add
          (mul_le_mul_of_nonneg_left
            (by simpa only [W] using hW2le) (by norm_num)) hprod
  have hWabs : |W x| ≤ Real.sqrt (2 * F ^ 2 + 2 * F * G) := by
    have hsqrtSq :
        Real.sqrt (2 * F ^ 2 + 2 * F * G) ^ 2 =
          2 * F ^ 2 + 2 * F * G := Real.sq_sqrt hK0
    nlinarith [sq_abs (W x), abs_nonneg (W x),
      Real.sqrt_nonneg (2 * F ^ 2 + 2 * F * G)]
  dsimp only [W] at hWabs
  rw [paper5WeightedPopulation, abs_mul,
    abs_of_pos (Real.exp_pos _)] at hWabs
  have hexp : Real.exp (-eta * x) * Real.exp (eta * x) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    |u t x - U x| = Real.exp (-eta * x) *
        (Real.exp (eta * x) * |u t x - U x|) := by
          rw [← mul_assoc, hexp, one_mul]
    _ ≤ Real.exp (-eta * x) *
        Real.sqrt (2 * F ^ 2 + 2 * F * G) :=
      mul_le_mul_of_nonneg_left hWabs (Real.exp_pos _).le
    _ = Real.sqrt (2 * F ^ 2 + 2 * F * G) *
        Real.exp (-eta * x) := by ring

/-- One pair of exact-weight square budgets on a compact positive-time window
gives one pointwise exponential envelope on every slice of that window. -/
theorem exists_common_weightedDifference_pointwise_envelope_of_H1_window
    {a b eta F G : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hu2 : ∀ t ∈ Set.Icc a b, ContDiff ℝ 2 (u t))
    (hU2 : ContDiff ℝ 2 U)
    (hW : ∀ t ∈ Set.Icc a b,
      Integrable (fun x => paper5WeightedPopulation eta u U t x ^ 2) ∧
      (∫ x, paper5WeightedPopulation eta u U t x ^ 2) ≤ F ^ 2)
    (hWx : ∀ t ∈ Set.Icc a b,
      Integrable (fun x => paper5WeightedPopulationX eta u U t x ^ 2) ∧
      (∫ x, paper5WeightedPopulationX eta u U t x ^ 2) ≤ G ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc a b, ∀ x,
      |u t x - U x| ≤ C * Real.exp (-eta * x) := by
  let C := Real.sqrt (2 * F ^ 2 + 2 * F * G)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  refine ⟨C, hC, ?_⟩
  intro t ht x
  exact weightedDifference_pointwise_envelope_of_H1_budgets
    hF hG (hu2 t ht) hU2 (hW t ht).1 (hW t ht).2
      (hWx t ht).1 (hWx t ht).2 x

/-- A common exact-weight `H1` window, together with the physical height
strip and wave exponential bound, produces a genuine scaled paper trap after
shifting the time window to start at zero. -/
theorem exists_shifted_inTimeWaveTrapSet_of_uniform_weighted_H1
    {a b kappa eta S F G : ℝ}
    {q : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (_hab : a ≤ b) (hkappa : 0 < kappa) (hkappaEta : kappa ≤ eta)
    (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hqC : ∀ t ∈ Set.Icc a b, IsCUnifBdd (q t))
    (hq0 : ∀ t ∈ Set.Icc a b, ∀ x, 0 ≤ q t x)
    (hqS : ∀ t ∈ Set.Icc a b, ∀ x, q t x ≤ S)
    (hq2 : ∀ t ∈ Set.Icc a b, ContDiff ℝ 2 (q t))
    (hU2 : ContDiff ℝ 2 U)
    (hUexp : ∀ x, U x ≤ Real.exp (-kappa * x))
    (hW : ∀ t ∈ Set.Icc a b,
      Integrable (fun x => paper5WeightedPopulation eta q U t x ^ 2) ∧
      (∫ x, paper5WeightedPopulation eta q U t x ^ 2) ≤ F ^ 2)
    (hWx : ∀ t ∈ Set.Icc a b,
      Integrable (fun x => paper5WeightedPopulationX eta q U t x ^ 2) ∧
      (∫ x, paper5WeightedPopulationX eta q U t x ^ 2) ≤ G ^ 2) :
    ∃ Q : ℝ, 0 < Q ∧
      InTimeWaveTrapSet kappa Q (b - a) (fun s => q (a + s)) := by
  obtain ⟨C, hC, henv⟩ :=
    exists_common_weightedDifference_pointwise_envelope_of_H1_window
      hF hG hq2 hU2 hW hWx
  let Q : ℝ := max S (1 + C)
  have hQ : max S (1 + C) ≤ Q := le_rfl
  have hQpos : 0 < Q := by
    have : 1 ≤ Q := by
      exact le_trans (by linarith : (1 : ℝ) ≤ 1 + C)
        (le_max_right S (1 + C))
    linarith
  refine ⟨Q, hQpos, ?_⟩
  apply inTimeWaveTrapSet_of_uniform_bound_and_weighted_envelope
    hkappa hkappaEta hC hQ
  · intro s hs
    apply hqC (a + s)
    constructor <;> linarith [hs.1, hs.2]
  · intro s hs x
    apply hq0 (a + s)
    constructor <;> linarith [hs.1, hs.2]
  · intro s hs x
    apply hqS (a + s)
    constructor <;> linarith [hs.1, hs.2]
  · exact hUexp
  · intro s hs x
    apply henv (a + s)
    constructor <;> linarith [hs.1, hs.2]

/-- Canonical finite-horizon producer.  Exact-weight initial closeness first
selects a common `H0` radius; the positive-window Henry estimate then selects
a common `H1` radius.  The quantitative window lemma above turns those two
radii into one scaled trap for the time-shifted canonical mild fixed point.

This is a finite-slab theorem: its scale may depend on the chosen contraction
horizon and positive window, but it assumes neither the target trap nor any
left-tail convergence. -/
theorem exists_shifted_inTimeWaveTrapSet_mildFixedPoint_wave_natural
    (p : CMParams)
    {M T a b Blog eta c D E Kflux FD B : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b ≤ T)
    (hBlog : 0 ≤ Blog) (heta : 0 < eta) (heta_one : eta < 1)
    (hkappa : 0 < kappa c) (hkappaEta : kappa c ≤ eta)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    {Uw Vw : ℝ → ℝ}
    (hTW : IsTravelingWave p c Uw Vw)
    (hbound : HasWaveUpperTailBound p c Uw)
    (hreg : TravelingWaveRegularity p c Uw Vw)
    (hMChi : MChi p ≤ M)
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
    (hdata_full : Integrable (fun y : ℝ => Real.exp (2 * eta * y) *
      |u₀.1 y - Uw y| ^ 2)) :
    let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let q : ℝ → ℝ → ℝ := fun s x =>
      (wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s)
    ∃ Q : ℝ, 0 < Q ∧
      InTimeWaveTrapSet (kappa c) Q (b - a) (fun s => q (a + s)) := by
  dsimp only
  let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let u : ℝ → ℝ → ℝ := fun s x =>
    (wholeLineBUCTrajectoryExtend hT Traj s).1 x
  let q : ℝ → ℝ → ℝ := fun s x => u s (x + c * s)
  let E₀ : ℝ := ∫ y : ℝ,
    Real.exp (2 * eta * y) * |u₀.1 y - Uw y| ^ 2
  let B₀ : ℝ := Real.sqrt E₀
  have hE₀ : 0 ≤ E₀ := by
    dsimp only [E₀]
    exact integral_nonneg fun y =>
      mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)
  have hB₀ : 0 ≤ B₀ := Real.sqrt_nonneg _
  have hdata_energy :
      (∫ y : ℝ, Real.exp (2 * eta * y) * |u₀.1 y - Uw y| ^ 2) ≤
        B₀ ^ 2 := by
    dsimp only [B₀, E₀]
    rw [Real.sq_sqrt hE₀]
  obtain ⟨F, hF, hfullAuto⟩ :=
    exists_uniform_fullWeighted_mildFixedPoint_wave_value_inputs_finiteHorizon
      p hT heta heta_one hB₀ u₀ hsmall hTW hbound hreg hMChi
        hD hFD hB hUd hUdd hUddcont hflux hfluxd hflux_has hfluxd_cont
        hreact hreact_cont hgrad_int hdata_full hdata_energy
  have hfull : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
        |q s x - Uw x| ^ 2) ∧
      (∫ x : ℝ, Real.exp (2 * eta * x) *
        |q s x - Uw x| ^ 2) ≤ F ^ 2 := by
    intro s hs
    simpa only [q, u, Traj] using hfullAuto s hs
  obtain ⟨G, hG, hgradAuto⟩ :=
    exists_uniform_window_weightedPopulationX_data_mildFixedPoint_wave
      p hM hT ha hab hbT hBlog heta heta_one hF u₀ hsmall hstrip
        hTW hbound hreg hMChi hlog hD hFD hB hUd hUdd hUddcont
        hflux hfluxd hflux_has hfluxd_cont hreact hreact_cont hgrad_int
        (by simpa only [q, u, Traj, coMovingPath] using hfull)
  have hgrad : ∀ s ∈ Set.Icc a b,
      Integrable (fun x => paper5WeightedPopulationX eta q Uw s x ^ 2) ∧
      (∫ x, paper5WeightedPopulationX eta q Uw s x ^ 2) ≤ G ^ 2 := by
    simpa only [q, u, Traj, coMovingPath] using hgradAuto
  have hqC : ∀ s ∈ Set.Icc a b, IsCUnifBdd (q s) := by
    intro s _hs
    dsimp only [q, u]
    exact IsCUnifBdd.shift (WholeLineBUC.isCUnifBdd
      (wholeLineBUCTrajectoryExtend hT Traj s)) (c * s)
  have hsMem : ∀ s ∈ Set.Icc a b, s ∈ Set.Icc (0 : ℝ) T := by
    intro s hs
    exact ⟨ha.le.trans hs.1, hs.2.trans hbT⟩
  have hq0 : ∀ s ∈ Set.Icc a b, ∀ x, 0 ≤ q s x := by
    intro s hs x
    have hext : wholeLineBUCTrajectoryExtend hT Traj s =
        Traj ⟨s, hsMem s hs⟩ :=
      wholeLineBUCTrajectoryExtend_eq hT Traj (hsMem s hs)
    simpa only [q, u, hext] using
      (hstrip ⟨s, hsMem s hs⟩ (x + c * s)).1
  have hqM : ∀ s ∈ Set.Icc a b, ∀ x, q s x ≤ M := by
    intro s hs x
    have hext : wholeLineBUCTrajectoryExtend hT Traj s =
        Traj ⟨s, hsMem s hs⟩ :=
      wholeLineBUCTrajectoryExtend_eq hT Traj (hsMem s hs)
    simpa only [q, u, hext] using
      (hstrip ⟨s, hsMem s hs⟩ (x + c * s)).2
  have hq2 : ∀ s ∈ Set.Icc a b, ContDiff ℝ 2 (q s) := by
    intro s hs
    have hs0 : 0 < s := ha.trans_le hs.1
    have hsT : s ≤ T := (hsMem s hs).2
    let zs : Set.Icc (0 : ℝ) T := ⟨s, hs0.le, hsT⟩
    have hwindow : ∀ r ∈ Set.Icc (s / 2) s, ∀ x,
        (wholeLineBUCTrajectoryExtend hT Traj r).1 x ∈
          Set.Icc (0 : ℝ) M := by
      intro r hr x
      have hrT : r ∈ Set.Icc (0 : ℝ) T :=
        ⟨(half_pos hs0).le.trans hr.1, hr.2.trans hsT⟩
      rw [wholeLineBUCTrajectoryExtend_eq hT Traj hrT]
      exact hstrip ⟨r, hrT⟩ x
    have hslice : ContDiff ℝ 2 (fun x => (Traj zs).1 x) := by
      simpa only [Traj] using
        (wholeLineCauchyBUCMildFixedPoint_slice_contDiff_two_positive
          (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
          p hM hT u₀ hsmall zs hs0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) hwindow)
    have hext : wholeLineBUCTrajectoryExtend hT Traj s = Traj zs :=
      wholeLineBUCTrajectoryExtend_eq hT Traj zs.2
    dsimp only [q, u]
    rw [hext]
    exact ContDiff.two_shift hslice (c * s)
  have hW : ∀ s ∈ Set.Icc a b,
      Integrable (fun x => paper5WeightedPopulation eta q Uw s x ^ 2) ∧
      (∫ x, paper5WeightedPopulation eta q Uw s x ^ 2) ≤ F ^ 2 := by
    intro s hs
    have hbase := hfull s (hsMem s hs)
    constructor
    · exact hbase.1.congr (Eventually.of_forall fun x =>
        (paper5WeightedPopulation_sq_eq_weighted_difference
          (eta := eta) (t := s) (x := x) (u := q) (U := Uw)).symm)
    · calc
        (∫ x, paper5WeightedPopulation eta q Uw s x ^ 2) =
            ∫ x, Real.exp (2 * eta * x) * |q s x - Uw x| ^ 2 := by
              apply integral_congr_ae
              filter_upwards with x
              exact paper5WeightedPopulation_sq_eq_weighted_difference
        _ ≤ F ^ 2 := hbase.2
  exact exists_shifted_inTimeWaveTrapSet_of_uniform_weighted_H1
    hab hkappa hkappaEta hF hG hqC hq0 hqM hq2
      (hreg.U_contDiff_two hTW) hbound.le_exp hW hgrad

section AxiomAudit

#print axioms paper5WeightedPopulation_sq_eq_weighted_difference
#print axioms weightedDifference_pointwise_envelope_of_H1_budgets
#print axioms exists_common_weightedDifference_pointwise_envelope_of_H1_window
#print axioms exists_shifted_inTimeWaveTrapSet_of_uniform_weighted_H1
#print axioms exists_shifted_inTimeWaveTrapSet_mildFixedPoint_wave_natural

end AxiomAudit

end ShenWork.Paper1
