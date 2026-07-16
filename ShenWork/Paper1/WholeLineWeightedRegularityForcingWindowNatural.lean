import ShenWork.Paper1.WholeLineWeightedRegularityGradientWindowBudget
import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorForcingNatural
import ShenWork.Paper1.WavePositiveLeftEndpoint

open Filter MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Natural uniform generator-forcing budget on positive windows

The canonical mild fixed point already carries uniform exact-weight `H0`
and `H1` budgets on every compact positive-time window.  This file combines
those two producers with the static generator-forcing estimate.  Spatial
regularity of the dynamic signal, its resolver identity, and the physical
strip are derived from the canonical construction rather than exposed as
weighted assumptions.
-/

/-- The whole-line frozen elliptic resolver is `C²` for every nonnegative
bounded uniformly continuous source.  The second derivative is continuous
by the resolver ODE. -/
theorem frozenElliptic_contDiff_two_of_cunifBdd_nonneg
    (p : CMParams) {f : ℝ → ℝ}
    (hf : IsCUnifBdd f) (hf0 : ∀ x, 0 ≤ f x) :
    ContDiff ℝ 2 (frozenElliptic p f) := by
  have hdiff : Differentiable ℝ (frozenElliptic p f) :=
    frozenElliptic_differentiable p hf hf0
  have hderivDiff : Differentiable ℝ (deriv (frozenElliptic p f)) :=
    fun x => frozenElliptic_deriv_differentiableAt p hf hf0 x
  have hsecondCont : Continuous (deriv (deriv (frozenElliptic p f))) := by
    have hsecondEq :
        deriv (deriv (frozenElliptic p f)) =
          fun x => frozenElliptic p f x - (f x) ^ p.γ := by
      funext x
      exact frozenElliptic_deriv_deriv_eq p hf hf0 x
    rw [hsecondEq]
    exact
      (frozenElliptic_continuous p hf hf0).sub
        (hf.1.rpow_const
          (fun _ => Or.inr (by linarith [p.hγ] : 0 ≤ p.γ)))
  have hderivC1 : ContDiff ℝ 1 (deriv (frozenElliptic p f)) := by
    rw [contDiff_one_iff_deriv]
    exact ⟨hderivDiff, hsecondCont⟩
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  exact ⟨hdiff, by simp, hderivC1⟩

/-- The signal component of a regular traveling wave is `C²`; continuity
of its second derivative follows directly from the elliptic wave ODE. -/
theorem TravelingWaveRegularity.V_contDiff_two
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hreg : TravelingWaveRegularity p c U V)
    (hTW : IsTravelingWave p c U V) :
    ContDiff ℝ 2 V := by
  have hVdiff : Differentiable ℝ V := hreg.V_diff
  have hVderivDiff : Differentiable ℝ (deriv V) := hreg.V_deriv_diff
  have hsecondEq : deriv (deriv V) = fun x => V x - (U x) ^ p.γ := by
    funext x
    have hiD2 : iteratedDeriv 2 V x = deriv (deriv V) x := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
        iteratedDeriv_one]
    have hode := hTW.ode_V x
    rw [hiD2] at hode
    linarith
  have hsecondCont : Continuous (deriv (deriv V)) := by
    rw [hsecondEq]
    exact hVdiff.continuous.sub
      (hreg.U_cont.rpow_const
        (fun _ => Or.inr (by linarith [p.hγ] : 0 ≤ p.γ)))
  have hderivC1 : ContDiff ℝ 1 (deriv V) := by
    rw [contDiff_one_iff_deriv]
    exact ⟨hVderivDiff, hsecondCont⟩
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  exact ⟨hVdiff, by simp, hderivC1⟩

/-- The population component of a regular traveling wave is `C²`; the
wave equation realizes its second derivative as a continuous lower-order
expression. -/
theorem TravelingWaveRegularity.U_contDiff_two
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hreg : TravelingWaveRegularity p c U V)
    (hTW : IsTravelingWave p c U V) :
    ContDiff ℝ 2 U := by
  have hUdiff : Differentiable ℝ U := hreg.U_diff
  have hVdiff : Differentiable ℝ V := hreg.V_diff
  have hVderivDiff : Differentiable ℝ (deriv V) := hreg.V_deriv_diff
  have hVxcont : Continuous (deriv V) := hVderivDiff.continuous
  have hU0 : ∀ x, 0 ≤ U x := fun x => (hTW.U_pos x).le
  have hsecondEq : deriv (deriv U) = fun x =>
      -(c - p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x) * deriv U x +
        (p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ) -
          U x * (1 - (U x) ^ p.α)) := by
    funext x
    have hchem := wave_chemotaxis_deriv_expand p (hreg.U_diff x)
      (hreg.V_deriv_diff x) (hU0 x)
      (by have := hTW.ode_V x; linarith)
    have hiD2 : iteratedDeriv 2 U x = deriv (deriv U) x := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
        iteratedDeriv_one]
    have hode := hTW.ode_U x
    rw [hchem, hiD2] at hode
    linarith
  have hpowm1 : Continuous (fun x => (U x) ^ (p.m - 1)) :=
    hreg.U_cont.rpow_const
      (fun _ => Or.inr (by linarith [p.hm] : 0 ≤ p.m - 1))
  have hpowm : Continuous (fun x => (U x) ^ p.m) :=
    hreg.U_cont.rpow_const
      (fun _ => Or.inr (by linarith [p.hm] : 0 ≤ p.m))
  have hpowgamma : Continuous (fun x => (U x) ^ p.γ) :=
    hreg.U_cont.rpow_const
      (fun _ => Or.inr (by linarith [p.hγ] : 0 ≤ p.γ))
  have hpowalpha : Continuous (fun x => (U x) ^ p.α) :=
    hreg.U_cont.rpow_const
      (fun _ => Or.inr (by linarith [p.hα] : 0 ≤ p.α))
  have hsecondCont : Continuous (deriv (deriv U)) := by
    rw [hsecondEq]
    have hchemCoeff : Continuous (fun x =>
        p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x) :=
      (((continuous_const.mul continuous_const).mul hpowm1).mul hVxcont)
    have hdrift : Continuous (fun x =>
        c - p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x) :=
      continuous_const.sub hchemCoeff
    have hfirst : Continuous (fun x =>
        -(c - p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x) *
          deriv U x) :=
      hdrift.neg.mul hreg.deriv_U_cont
    have hsignal : Continuous (fun x => V x - (U x) ^ p.γ) :=
      hVdiff.continuous.sub hpowgamma
    have hchem : Continuous (fun x =>
        p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ)) :=
      (continuous_const.mul hpowm).mul hsignal
    have honeMinus : Continuous (fun x => 1 - (U x) ^ p.α) :=
      continuous_const.sub hpowalpha
    have hreaction : Continuous (fun x => U x * (1 - (U x) ^ p.α)) :=
      hreg.U_cont.mul honeMinus
    exact hfirst.add (hchem.sub hreaction)
  have hderivC1 : ContDiff ℝ 1 (deriv U) := by
    rw [contDiff_one_iff_deriv]
    exact ⟨hreg.deriv_U_diff, hsecondCont⟩
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  exact ⟨hUdiff, by simp, hderivC1⟩

/-- On a compact positive-time window, the canonical mild fixed point has
one exact-weight `L²` square budget for its complete generator forcing.
The numerical `H0` and `H1` bounds are selected internally. -/
theorem exists_uniform_weightedGeneratorForcing_square_bound_mildFixedPoint_wave
    (p : CMParams)
    {M T a b Blog eta c D E Kflux FD B : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (hBlog : 0 ≤ Blog) (heta : 0 < eta)
    (heta_one : eta < 1) (hetaCap : eta < stabilityWeightCap p)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    {Uw Vw : ℝ → ℝ}
    (hchi : p.χ ≠ 0)
    (hc : paper5CorrectedCStarStar p p.χ < c)
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
    let Uc := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let u : ℝ → ℝ → ℝ := fun s x =>
      (wholeLineBUCTrajectoryExtend hT Uc s).1 x
    let v : ℝ → ℝ → ℝ := fun s => frozenElliptic p (u s)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc a b,
      Integrable (fun x : ℝ =>
        paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) Uw Vw s x ^ 2) ∧
      (∫ x : ℝ,
        paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) Uw Vw s x ^ 2) ≤ C := by
  dsimp only
  let Uc := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let u : ℝ → ℝ → ℝ := fun s x =>
    (wholeLineBUCTrajectoryExtend hT Uc s).1 x
  let v : ℝ → ℝ → ℝ := fun s => frozenElliptic p (u s)
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
        |u s (x + c * s) - Uw x| ^ 2) ∧
      (∫ x : ℝ, Real.exp (2 * eta * x) *
        |u s (x + c * s) - Uw x| ^ 2) ≤ F ^ 2 := by
    intro s hs
    simpa only [u, Uc] using hfullAuto s hs
  obtain ⟨G, hG, hgrad⟩ :=
    exists_uniform_window_weightedPopulationX_data_mildFixedPoint_wave
      p hM hT ha hab hbT.le hBlog heta heta_one hF u₀ hsmall hstrip
        hTW hbound hreg hMChi hlog hD hFD hB hUd hUdd hUddcont hflux
        hfluxd hflux_has hfluxd_cont hreact hreact_cont hgrad_int
        (by simpa only [u, Uc] using hfull)
  have hTpos : 0 < T := ha.trans_le (hab.trans hbT.le)
  have hU2 : ContDiff ℝ 2 Uw := hreg.U_contDiff_two hTW
  have hV2 : ContDiff ℝ 2 Vw := hreg.V_contDiff_two hTW
  have hsol : IsClassicalSolution p T u v := by
    simpa only [u, v, Uc] using
      (wholeLineCauchyBUCMildFixedPoint_isClassicalSolution
        p (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
          hM hTpos u₀ hsmall
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) hstrip)
  have huM : ∀ s ∈ Set.Icc a b, ∀ x,
      coMovingPath c u s x ∈ Set.Icc (0 : ℝ) M := by
    intro s hs x
    let zs : Set.Icc (0 : ℝ) T :=
      ⟨s, ha.le.trans hs.1, hs.2.trans hbT.le⟩
    have hext : wholeLineBUCTrajectoryExtend hT Uc s = Uc zs :=
      wholeLineBUCTrajectoryExtend_eq hT Uc zs.2
    simpa only [coMovingPath, u, hext] using hstrip zs (x + c * s)
  have hu2 : ∀ s ∈ Set.Icc a b,
      ContDiff ℝ 2 (coMovingPath c u s) := by
    intro s hs
    have hs0 : 0 < s := ha.trans_le hs.1
    have hsT : s ≤ T := hs.2.trans hbT.le
    let zs : Set.Icc (0 : ℝ) T := ⟨s, hs0.le, hsT⟩
    have hwindow : ∀ r ∈ Set.Icc (s / 2) s, ∀ x,
        (wholeLineBUCTrajectoryExtend hT Uc r).1 x ∈
          Set.Icc (0 : ℝ) M := by
      intro r hr x
      have hrT : r ∈ Set.Icc (0 : ℝ) T :=
        ⟨(half_pos hs0).le.trans hr.1, hr.2.trans hsT⟩
      rw [wholeLineBUCTrajectoryExtend_eq hT Uc hrT]
      exact hstrip ⟨r, hrT⟩ x
    have hslice : ContDiff ℝ 2 (fun x => (Uc zs).1 x) := by
      simpa only [Uc] using
        (wholeLineCauchyBUCMildFixedPoint_slice_contDiff_two_positive
          (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
          p hM hT u₀ hsmall zs hs0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) hwindow)
    have hext : wholeLineBUCTrajectoryExtend hT Uc s = Uc zs :=
      wholeLineBUCTrajectoryExtend_eq hT Uc zs.2
    change ContDiff ℝ 2
      (fun x => (wholeLineBUCTrajectoryExtend hT Uc s).1 (x + c * s))
    rw [hext]
    exact ContDiff.two_shift hslice (c * s)
  have hvEq : ∀ s ∈ Set.Icc a b,
      coMovingPath c v s = frozenElliptic p (coMovingPath c u s) := by
    intro s hs
    have hs0 : 0 ≤ s := (ha.trans_le hs.1).le
    let zs : Set.Icc (0 : ℝ) T :=
      ⟨s, hs0, hs.2.trans hbT.le⟩
    have hext : wholeLineBUCTrajectoryExtend hT Uc s = Uc zs :=
      wholeLineBUCTrajectoryExtend_eq hT Uc zs.2
    have huC : IsCUnifBdd (u s) := by
      simpa only [u, hext] using WholeLineBUC.isCUnifBdd (Uc zs)
    have hu0 : ∀ x, 0 ≤ u s x := by
      intro x
      simpa only [u, hext] using (hstrip zs x).1
    change
      (fun x => frozenElliptic p (u s) (x + c * s)) =
        frozenElliptic p (fun x => u s (x + c * s))
    exact (frozenElliptic_comp_add_const_fun p huC hu0 (c * s)).symm
  have hv2 : ∀ s ∈ Set.Icc a b,
      ContDiff ℝ 2 (coMovingPath c v s) := by
    intro s hs
    rw [hvEq s hs]
    have huCphys : IsCUnifBdd (u s) := by
      dsimp only [u]
      exact WholeLineBUC.isCUnifBdd
        (wholeLineBUCTrajectoryExtend hT Uc s)
    have huC : IsCUnifBdd (coMovingPath c u s) := by
      simpa only [coMovingPath] using
        isCUnifBdd_comp_add_const huCphys (c * s)
    exact frozenElliptic_contDiff_two_of_cunifBdd_nonneg
      p huC (fun x => (huM s hs x).1)
  have hclose : ∀ s ∈ Set.Icc a b, Integrable (fun x : ℝ =>
      Real.exp (2 * eta * x) * |coMovingPath c u s x - Uw x| ^ 2) := by
    intro s hs
    simpa only [coMovingPath] using
      (hfull s ⟨ha.le.trans hs.1, hs.2.trans hbT.le⟩).1
  have hclose_le : ∀ s ∈ Set.Icc a b, (∫ x : ℝ,
      Real.exp (2 * eta * x) * |coMovingPath c u s x - Uw x| ^ 2) ≤
        F ^ 2 := by
    intro s hs
    simpa only [coMovingPath] using
      (hfull s ⟨ha.le.trans hs.1, hs.2.trans hbT.le⟩).2
  have hgrad' : ∀ s ∈ Set.Icc a b,
      Integrable (fun x =>
        paper5WeightedPopulationX eta (coMovingPath c u) Uw s x ^ 2) ∧
      (∫ x : ℝ,
        paper5WeightedPopulationX eta (coMovingPath c u) Uw s x ^ 2) ≤
          G ^ 2 := by
    simpa only [u, Uc] using hgrad
  let C : ℝ := max 0
    (paper5WeightedGeneratorForcingH1SquareBound
      p M eta (F ^ 2) (G ^ 2))
  refine ⟨C, le_max_left _ _, ?_⟩
  have hforcing :=
    paper5WeightedGeneratorForcing_uniform_square_bound_on_Icc_of_population_H1_natural
      p hchi hc heta hetaCap hsol ha hbT hTW hreg hbound hMChi
        hu2 hv2 hU2 hV2 huM hvEq hclose (fun s hs => (hgrad' s hs).1)
        hclose_le (fun s hs => (hgrad' s hs).2)
  intro s hs
  refine ⟨(hforcing s hs).1, (hforcing s hs).2.trans ?_⟩
  exact le_max_right _ _

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.frozenElliptic_contDiff_two_of_cunifBdd_nonneg
#print axioms ShenWork.Paper1.TravelingWaveRegularity.V_contDiff_two
#print axioms ShenWork.Paper1.TravelingWaveRegularity.U_contDiff_two
#print axioms
  ShenWork.Paper1.exists_uniform_weightedGeneratorForcing_square_bound_mildFixedPoint_wave
