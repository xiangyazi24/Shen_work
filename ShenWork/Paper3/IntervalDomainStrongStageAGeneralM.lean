/- Faithful general-`m` Stage-A strong spectral stability. -/
import ShenWork.Paper2.IntervalDomainMEllipticResolverAgreementIcc
import ShenWork.Paper3.IntervalDomainStrongBootstrapGeneralM
import ShenWork.Paper3.IntervalDomainSignalRegularityProducerGeneralM
import ShenWork.Paper3.IntervalDomainStrongStageA

namespace ShenWork.Paper3

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.PDE
open ShenWork.PDE.SectorialOperator

noncomputable section

/-- The uniform elliptic value/gradient estimates specialized to a realized
faithful general-`m` `X_2^sigma` slice. -/
theorem paper3SignalComponents_strong_bounds_of_X2Sigma_ball_generalM
    {p : CM2Params} {T t sigma uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (Hreal : IntervalDomainX2SigmaRealizationBounds sigma uStar (u t))
    (hsmall : intervalDomainX2SigmaDistance sigma uStar (u t) ≤
      intervalDomainX2SigmaLocalNemytskiiRadiusGeneralM p sigma uStar) :
    let C := paper3UniformSignalStrongConstant p uStar heq.u_pos
    let M := intervalDomainX2SigmaC1Envelope sigma *
      intervalDomainX2SigmaDistance sigma uStar (u t)
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3LinearSignalValue p uStar (u t) x| ≤ C * M ∧
      |paper3LinearSignalGradient p uStar (u t) x| ≤ C * M ∧
      |paper3LinearSignalLaplacian p uStar (u t) x| ≤ C * M ∧
      |paper3QuadraticSignalValue p uStar (u t) x| ≤ C * M ^ 2 ∧
      |paper3QuadraticSignalGradient p uStar (u t) x| ≤ C * M ^ 2 ∧
      |paper3QuadraticSignalLaplacian p uStar (u t) x| ≤ C * M ^ 2 := by
  let d := intervalDomainX2SigmaDistance sigma uStar (u t)
  let M := intervalDomainX2SigmaC1Envelope sigma * d
  have hsmallOld : d ≤ intervalDomainX2SigmaLocalNemytskiiRadius
      sigma uStar := hsmall.trans (min_le_left _ _)
  have henv := Hreal.local_envelope_bounds hsmallOld
  have hM0 : 0 ≤ M := by simpa [M, d] using henv.1
  have hvalue : ∀ x : intervalDomainPoint, |u t x - uStar| ≤ M := by
    simpa [M, d] using henv.2.2.1
  have hdistPos : d ≤ intervalDomainX2SigmaPositivityRadius sigma uStar :=
    hsmallOld.trans (min_le_left _ _)
  have hnearAbs : ∀ x : intervalDomainPoint, |u t x - uStar| ≤ uStar / 2 := by
    intro x
    let Cinf := intervalDomainX2SigmaValueTrace sigma
    have hCinf : 0 ≤ Cinf := intervalDomainX2SigmaValueTrace_nonneg sigma
    have hden : 0 < 1 + Cinf := by linarith
    calc
      |u t x - uStar| ≤ Cinf * d := Hreal.value_bound x
      _ ≤ Cinf * intervalDomainX2SigmaPositivityRadius sigma uStar :=
        mul_le_mul_of_nonneg_left hdistPos hCinf
      _ = (uStar / 2) * (Cinf / (1 + Cinf)) := by
        dsimp [Cinf, intervalDomainX2SigmaPositivityRadius]
        field_simp [hden.ne']
      _ ≤ uStar / 2 := by
        have hfrac : Cinf / (1 + Cinf) ≤ 1 := by
          rw [div_le_one hden]
          linarith
        simpa using mul_le_mul_of_nonneg_left hfrac (by linarith [heq.u_pos])
  have hu_near : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u t) x ∈ Set.Icc (uStar / 2) (3 * uStar / 2) := by
    intro x hx
    let xp : intervalDomainPoint := ⟨x, hx⟩
    have ha := hnearAbs xp
    have hlift : intervalDomainLift (u t) x = u t xp := by
      simp [intervalDomainLift, xp, hx]
    rw [hlift]
    exact ⟨by linarith [neg_le_of_abs_le ha], by linarith [le_of_abs_le ha]⟩
  have hphi_sup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalPerturbationProfile uStar (u t) x| ≤ M := by
    intro x hx
    let xp : intervalDomainPoint := ⟨x, hx⟩
    simpa [paper3IntervalPerturbationProfile, intervalDomainLift, xp, hx]
      using hvalue xp
  have hphiCont : ContinuousOn
      (paper3IntervalPerturbationProfile uStar (u t))
      (Set.Icc (0 : ℝ) 1) := by
    have huCont : ContinuousOn (intervalDomainLift (u t))
        (Set.Icc (0 : ℝ) 1) :=
      ((hsol.regularity.2.2.2.2.1 t ht).1.1).continuousOn
    exact huCont.sub continuousOn_const
  have hphi : MemLp (paper3IntervalPerturbationProfile uStar (u t)) 2
      (intervalMeasure 1) :=
    BFormPositiveDatumNegPart.memLp_two_of_continuousOn_Icc hphiCont
  have hphi_l2 : intervalL2Size
      (paper3IntervalPerturbationProfile uStar (u t)) ≤ M :=
    intervalL2Size_le_of_pointwise_abs_bound hM0 hphi
      (fun x hx => hphi_sup x (Set.Ioo_subset_Icc_self hx))
  rcases paper3SignalSourceRegularity_of_classical_slice_generalM hsol ht heq with
    ⟨⟨Hlin, Hquad⟩⟩
  simpa [M, d] using
    paper3SignalComponents_strong_bounds_uniform
      p heq.u_pos hM0 (u t) hu_near hphi
        Hlin.profile_aestronglyMeasurable
        Hquad.profile_aestronglyMeasurable hphi_sup hphi_l2

/-- On the faithful local strong ball, the elliptically resolved signal is
controlled in the concrete `C¹` gauge by the strong population distance. -/
theorem intervalDomainMSignal_c1Distance_le_X2Sigma
    {p : CM2Params} {T t sigma uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (Hreal : IntervalDomainX2SigmaRealizationBounds sigma uStar (u t))
    (hsmall : intervalDomainX2SigmaDistance sigma uStar (u t) ≤
      intervalDomainX2SigmaLocalNemytskiiRadiusGeneralM p sigma uStar) :
    intervalDomainSectorialC1Distance (v t) (fun _ => vStar) ≤
      4 * paper3UniformSignalStrongConstant p uStar heq.u_pos *
        intervalDomainX2SigmaC1Envelope sigma *
          intervalDomainX2SigmaDistance sigma uStar (u t) := by
  let d := intervalDomainX2SigmaDistance sigma uStar (u t)
  let E := intervalDomainX2SigmaC1Envelope sigma
  let M := E * d
  let C := paper3UniformSignalStrongConstant p uStar heq.u_pos
  have hsmallOld : d ≤ intervalDomainX2SigmaLocalNemytskiiRadius
      sigma uStar := hsmall.trans (min_le_left _ _)
  have henv := Hreal.local_envelope_bounds hsmallOld
  have hM0 : 0 ≤ M := by simpa [M, E, d] using henv.1
  have hM1 : M ≤ 1 := by simpa [M, E, d] using henv.2.1
  have hC : 0 < C := by
    simpa [C] using paper3UniformSignalStrongConstant_pos p uStar heq.u_pos
  have hsignal := paper3SignalComponents_strong_bounds_of_X2Sigma_ball_generalM
    hsol ht heq Hreal hsmall
  let Hsplit := intervalSolutionSignalSplitData_of_classical_slice_generalM
    (p := p) (uStar := uStar) hsol ht
  have hvalue : ∀ x : intervalDomainPoint,
      |v t x - vStar| ≤ 2 * C * M := by
    intro x
    have hphys := solution_v_eq_resolver_pointwise_IccM hsol ht x.2
    have hlift : intervalDomainLift (v t) x.1 = v t x := by
      simp [intervalDomainLift]
    rw [hlift] at hphys
    have hphys' : intervalNeumannResolverR p (u t) x = v t x := by
      simpa using hphys
    have hsplit := paper3IntervalResolver_value_sub_eq_signalComponents
      p uStar (u t) Hsplit.linear_integrable Hsplit.remainder_integrable
      Hsplit.source_sq_summable Hsplit.equilibrium_source_sq_summable
      Hsplit.linear_source_sq_summable Hsplit.remainder_source_sq_summable x
    have hconst := intervalNeumannResolverR_const_eq_vStar p heq x
    have heqValue : v t x - vStar =
        paper3LinearSignalValue p uStar (u t) x.1 +
          paper3QuadraticSignalValue p uStar (u t) x.1 := by
      linarith [hphys']
    rw [heqValue]
    calc
      |paper3LinearSignalValue p uStar (u t) x.1 +
          paper3QuadraticSignalValue p uStar (u t) x.1| ≤
        |paper3LinearSignalValue p uStar (u t) x.1| +
          |paper3QuadraticSignalValue p uStar (u t) x.1| := abs_add_le _ _
      _ ≤ C * M + C * M ^ 2 :=
        add_le_add (hsignal x.1 x.2).1
          (hsignal x.1 x.2).2.2.2.1
      _ ≤ 2 * C * M := by
        nlinarith [mul_nonneg hC.le hM0]
  have hgrad : ∀ x : intervalDomainPoint,
      intervalDomain.gradNorm (fun y => v t y - vStar) x ≤ 2 * C * M := by
    intro x
    rw [intervalDomain_gradNorm_sub_const_eq]
    have hphys := solution_lift_v_deriv_eq_resolverGrad_IccM hsol ht x.2
    rw [resolverGradReal_eq p (u t) x] at hphys
    have hsplit := paper3IntervalResolver_gradient_sub_eq_signalComponents
      p uStar (u t) Hsplit.linear_integrable Hsplit.remainder_integrable
      Hsplit.source_sq_summable Hsplit.equilibrium_source_sq_summable
      Hsplit.linear_source_sq_summable Hsplit.remainder_source_sq_summable x
    have hconst := intervalNeumannResolverRGrad_const p uStar x
    have heqGrad : deriv (intervalDomainLift (v t)) x.1 =
        paper3LinearSignalGradient p uStar (u t) x.1 +
          paper3QuadraticSignalGradient p uStar (u t) x.1 := by
      linarith
    rw [heqGrad]
    calc
      |paper3LinearSignalGradient p uStar (u t) x.1 +
          paper3QuadraticSignalGradient p uStar (u t) x.1| ≤
        |paper3LinearSignalGradient p uStar (u t) x.1| +
          |paper3QuadraticSignalGradient p uStar (u t) x.1| := abs_add_le _ _
      _ ≤ C * M + C * M ^ 2 :=
        add_le_add (hsignal x.1 x.2).2.1
          (hsignal x.1 x.2).2.2.2.2.1
      _ ≤ 2 * C * M := by
        nlinarith [mul_nonneg hC.le hM0]
  have hvalueSup : intervalDomain.supNorm (fun x => v t x - vStar) ≤
      2 * C * M := intervalDomainSupNorm_le_of_pointwise_abs hvalue
  have hgradSup : intervalDomain.supNorm
      (fun x => intervalDomain.gradNorm (fun y => v t y - vStar) x) ≤
      2 * C * M := by
    apply intervalDomainSupNorm_le_of_pointwise_abs
    intro x
    have hx0 : 0 ≤ intervalDomain.gradNorm (fun y => v t y - vStar) x := by
      change 0 ≤ |deriv (intervalDomainLift (fun y => v t y - vStar)) x.1|
      exact abs_nonneg _
    simpa [abs_of_nonneg hx0] using hgrad x
  unfold intervalDomainSectorialC1Distance
  calc
    intervalDomain.supNorm (fun x => v t x - vStar) +
        intervalDomain.supNorm
          (fun x => intervalDomain.gradNorm (fun y => v t y - vStar) x) ≤
      2 * C * M + 2 * C * M := add_le_add hvalueSup hgradSup
    _ = 4 * C * E * d := by simp [M]; ring

/-- Faithful Stage A in the strong phase norm.  Positive-time restarted
estimates are uniform as the restart tends to zero, and the strong initial
trace identifies the limiting datum. -/
theorem intervalDomainMX2SigmaDistance_allTime_exponential_bound
    {p : CM2Params} {sigma uStar vStar gap : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar gap)
    (hsigmaStrong : 3 / 4 < sigma) (hsigma1 : sigma < 1)
    (hmem₀ : IntervalDomainX2SigmaPerturbation sigma uStar u₀)
    (hstate : IntervalDomainStrongInitialState p u₀ u v)
    (htrace : IntervalDomainStrongInitialTrace sigma uStar u₀ u)
    (hsmall₀ : intervalDomainX2SigmaDistance sigma uStar u₀ ≤
      intervalDomainStrongBootstrapRadiusGeneralM
        p sigma uStar vStar gap heq / 4) :
    ∀ t, 0 ≤ t →
      IntervalDomainX2SigmaPerturbation sigma uStar (u t) ∧
      intervalDomainX2SigmaDistance sigma uStar (u t) ≤
        2 * intervalDomainX2SigmaDistance sigma uStar u₀ *
          Real.exp (-(gap / 4) * t) := by
  intro t ht
  let size : ℝ → ℝ := fun s =>
    intervalDomainX2SigmaDistance sigma uStar (u s)
  let datum : ℝ := intervalDomainX2SigmaDistance sigma uStar u₀
  let R : ℝ := intervalDomainStrongBootstrapRadiusGeneralM
    p sigma uStar vStar gap heq
  have hR : 0 < R := by
    simpa [R] using intervalDomainStrongBootstrapRadiusGeneralM_pos
      p heq hgap.1 (by linarith) hsigma1
  have hdatum0 : 0 ≤ datum := by
    dsimp [datum]
    exact Real.sqrt_nonneg _
  by_cases htzero : t = 0
  · subst t
    constructor
    · simpa [hstate.1] using hmem₀
    · dsimp [size, datum]
      rw [hstate.1]
      simp only [mul_one, Real.exp_zero, mul_zero]
      linarith
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm htzero)
    constructor
    · let T : ℝ := t + 1
      have hT : 0 < T := by dsimp [T]; linarith
      apply intervalDomainMX2SigmaPerturbation_of_classical_positive
        (hglobal T hT) ⟨htpos, by dsimp [T]; linarith⟩ hsigma1.le
    · let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
      have hsizeTend : Tendsto size l (nhds datum) := by
        simpa [size, datum, l] using htrace
      have hidTend : Tendsto (fun a : ℝ => a) l (nhds 0) :=
        tendsto_id.mono_left inf_le_left
      have hsumTend : Tendsto (fun a => size a + a) l (nhds (datum + 0)) :=
        hsizeTend.add hidTend
      have hscaledTend : Tendsto (fun a => 2 * (size a + a)) l
          (nhds (2 * (datum + 0))) := by
        simpa only [mul_comm] using hsumTend.const_mul 2
      have hlinearLimit : 2 * (datum + 0) < R := by
        have hsmall : datum ≤ R / 4 := by simpa [datum, R] using hsmall₀
        linarith
      have hradiusEventually : ∀ᶠ a in l, 2 * (size a + a) ≤ R :=
        (hscaledTend.eventually (Iio_mem_nhds hlinearLimit)).mono
          (fun _a ha => ha.le)
      have hpositiveEventually : ∀ᶠ a in l, 0 < a := by
        exact self_mem_nhdsWithin
      have hterminalEventually : ∀ᶠ a in l, a < t := by
        exact (show ∀ᶠ a in nhds (0 : ℝ), a < t from
          Iio_mem_nhds htpos).filter_mono inf_le_left
      have hexpTend : Tendsto
          (fun a : ℝ => Real.exp (-(gap / 4) * (t - a))) l
          (nhds (Real.exp (-(gap / 4) * (t - 0)))) := by
        have hcont : Continuous
            (fun a : ℝ => Real.exp (-(gap / 4) * (t - a))) := by
          fun_prop
        exact hcont.continuousAt.mono_left inf_le_left
      have hrhsTend : Tendsto
          (fun a : ℝ =>
            2 * (size a + a) * Real.exp (-(gap / 4) * (t - a))) l
          (nhds
            (2 * datum * Real.exp (-(gap / 4) * t))) := by
        simpa only [add_zero, sub_zero] using hscaledTend.mul hexpTend
      change size t ≤ 2 * datum * Real.exp (-(gap / 4) * t)
      apply le_of_tendsto_of_tendsto tendsto_const_nhds hrhsTend
      filter_upwards [hpositiveEventually, hterminalEventually,
        hradiusEventually] with a ha hat hrad
      let radius : ℝ := 2 * (size a + a)
      have hsizea0 : 0 ≤ size a := by
        dsimp [size]
        exact Real.sqrt_nonneg _
      have hradiusPos : 0 < radius := by
        dsimp [radius]
        linarith
      have hrestart : size a ≤ radius / 2 := by
        dsimp [radius]
        linarith
      have hdecay :=
        intervalDomainX2SigmaDistance_restart_exponential_bound_of_radius_le_generalM
          hglobal ha heq hgap hsigmaStrong hsigma1 hradiusPos
          (by simpa [radius] using hrad) hrestart (t - a) (by linarith)
      simpa [size, radius, add_sub_cancel_left] using hdecay

/-- Faithful general-`m` Stage-A orbit interface.  Unlike the legacy bundle,
every datum, trace, and classical-solution predicate uses `intervalDomainM`,
and no equation `p.m = 1` is carried. -/
def IntervalDomainMStrongSpectralSemigroupOrbitBound
    (p : CM2Params) : Prop :=
  ∀ sigma uStar vStar,
    3 / 4 < sigma → sigma < 1 →
    0 < p.a →
    Paper3ConstantEquilibrium p uStar vStar →
    LinearlyStable unitIntervalNeumannSpectrum p uStar vStar →
      ∃ eps > 0, ∃ C > 0, ∃ rate > 0,
        ∀ u₀ : intervalDomainPoint → ℝ,
          PositiveInitialDatum intervalDomainM u₀ →
          IntervalDomainX2SigmaPerturbation sigma uStar u₀ →
          intervalDomainX2SigmaDistance sigma uStar u₀ ≤ eps →
          ∀ u v : ℝ → intervalDomainPoint → ℝ,
            IsPaper2GlobalClassicalSolution intervalDomainM p u v →
            InitialTrace intervalDomainM u₀ u →
            IntervalDomainStrongInitialState p u₀ u v →
            IntervalDomainStrongInitialTrace sigma uStar u₀ u →
              ∀ t, 0 ≤ t →
                IntervalDomainX2SigmaPerturbation sigma uStar (u t) ∧
                intervalDomainX2SigmaDistance sigma uStar (u t) ≤
                  C * Real.exp (-rate * t) *
                    intervalDomainX2SigmaDistance sigma uStar u₀ ∧
                (0 < t →
                  intervalDomainSectorialC1Distance (u t) (fun _ => uStar) +
                    intervalDomainSectorialC1Distance (v t) (fun _ => vStar) ≤
                      C * Real.exp (-rate * t) *
                        intervalDomainX2SigmaDistance sigma uStar u₀)

/-- The faithful general-`m` closed Stage-A orbit theorem. -/
theorem intervalDomainM_strongSpectralSemigroupOrbitBound
    (p : CM2Params) :
    IntervalDomainMStrongSpectralSemigroupOrbitBound p := by
  intro sigma uStar vStar hsigmaStrong hsigma1 ha heq hstable
  rcases unitIntervalLinearSpectralGap_of_linearlyStable_of_a_pos
      p heq hstable ha with ⟨gap, hgap0, hgap⟩
  let R := intervalDomainStrongBootstrapRadiusGeneralM
    p sigma uStar vStar gap heq
  let eps := R / 4
  let Cu := intervalDomainX2SigmaValueTrace sigma +
    intervalDomainX2SigmaDerivativeTrace sigma
  let Cv := 4 * paper3UniformSignalStrongConstant p uStar heq.u_pos *
    intervalDomainX2SigmaC1Envelope sigma
  let C := 2 + 2 * (Cu + Cv)
  have hR : 0 < R := by
    simpa [R] using intervalDomainStrongBootstrapRadiusGeneralM_pos
      p heq hgap0 (by linarith) hsigma1
  have heps : 0 < eps := by dsimp [eps]; linarith
  have hCu : 0 ≤ Cu := by
    dsimp [Cu]
    exact add_nonneg (intervalDomainX2SigmaValueTrace_nonneg sigma)
      (intervalDomainX2SigmaDerivativeTrace_nonneg sigma)
  have hCv : 0 ≤ Cv := by
    dsimp [Cv]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (paper3UniformSignalStrongConstant_pos p uStar heq.u_pos).le)
      (intervalDomainX2SigmaC1Envelope_pos sigma).le
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨eps, heps, C, hC, gap / 4, by linarith, ?_⟩
  intro u₀ _hu₀ hmem₀ hsmall₀ u v hglobal _hweak hstate hstrongTrace
  have hsmall₀' : intervalDomainX2SigmaDistance sigma uStar u₀ ≤
      intervalDomainStrongBootstrapRadiusGeneralM
        p sigma uStar vStar gap heq / 4 := by
    simpa [eps, R] using hsmall₀
  have hall := intervalDomainMX2SigmaDistance_allTime_exponential_bound
    hglobal heq hgap hsigmaStrong hsigma1 hmem₀ hstate
      hstrongTrace hsmall₀'
  intro t ht
  rcases hall t ht with ⟨hmemt, hdist⟩
  have hdatum0 : 0 ≤ intervalDomainX2SigmaDistance sigma uStar u₀ :=
    Real.sqrt_nonneg _
  have hexp0 : 0 ≤ Real.exp (-(gap / 4) * t) := Real.exp_nonneg _
  refine ⟨hmemt, ?_, ?_⟩
  · calc
      intervalDomainX2SigmaDistance sigma uStar (u t) ≤
          2 * intervalDomainX2SigmaDistance sigma uStar u₀ *
            Real.exp (-(gap / 4) * t) := hdist
      _ ≤ C * Real.exp (-(gap / 4) * t) *
          intervalDomainX2SigmaDistance sigma uStar u₀ := by
        have hC2 : 2 ≤ C := by dsimp [C]; linarith
        nlinarith [mul_nonneg hdatum0 hexp0]
  · intro htpos
    let T : ℝ := t + 1
    have hT : 0 < T := by dsimp [T]; linarith
    have htT : t < T := by dsimp [T]; linarith
    let hsol := hglobal T hT
    have htmem : t ∈ Set.Ioo (0 : ℝ) T := ⟨htpos, htT⟩
    have hcont : Continuous (u t) :=
      ShenWork.Paper2.IntervalDomainM.solutionSlice_continuous hsol htmem
    have Hreal : IntervalDomainX2SigmaRealizationBounds sigma uStar (u t) :=
      intervalDomainX2SigmaRealizationBounds_of_continuous
        hsigmaStrong hcont hmemt
    have hexple : Real.exp (-(gap / 4) * t) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have : 0 ≤ gap / 4 := by linarith
      nlinarith
    have hdistR : intervalDomainX2SigmaDistance sigma uStar (u t) ≤ R := by
      calc
        intervalDomainX2SigmaDistance sigma uStar (u t) ≤
            2 * intervalDomainX2SigmaDistance sigma uStar u₀ *
              Real.exp (-(gap / 4) * t) := hdist
        _ ≤ 2 * (R / 4) * 1 := by
          gcongr
        _ ≤ R := by linarith
    have hlocal : intervalDomainX2SigmaDistance sigma uStar (u t) ≤
        intervalDomainX2SigmaLocalNemytskiiRadiusGeneralM p sigma uStar :=
      hdistR.trans (intervalDomainStrongBootstrapRadiusGeneralM_le_positivity
        p sigma uStar vStar gap heq)
    have huC1 := Hreal.c1Distance_le
    have hvC1 := intervalDomainMSignal_c1Distance_le_X2Sigma
      hsol htmem heq Hreal hlocal
    have hsumC1 :
        intervalDomainSectorialC1Distance (u t) (fun _ => uStar) +
            intervalDomainSectorialC1Distance (v t) (fun _ => vStar) ≤
          (Cu + Cv) * intervalDomainX2SigmaDistance sigma uStar (u t) := by
      calc
        _ ≤ Cu * intervalDomainX2SigmaDistance sigma uStar (u t) +
            Cv * intervalDomainX2SigmaDistance sigma uStar (u t) := by
          exact add_le_add (by simpa [Cu] using huC1)
            (by simpa [Cv] using hvC1)
        _ = _ := by ring
    calc
      intervalDomainSectorialC1Distance (u t) (fun _ => uStar) +
          intervalDomainSectorialC1Distance (v t) (fun _ => vStar) ≤
        (Cu + Cv) * intervalDomainX2SigmaDistance sigma uStar (u t) := hsumC1
      _ ≤ (Cu + Cv) *
          (2 * intervalDomainX2SigmaDistance sigma uStar u₀ *
            Real.exp (-(gap / 4) * t)) :=
        mul_le_mul_of_nonneg_left hdist (add_nonneg hCu hCv)
      _ ≤ C * Real.exp (-(gap / 4) * t) *
          intervalDomainX2SigmaDistance sigma uStar u₀ := by
        dsimp [C]
        nlinarith [mul_nonneg hdatum0 hexp0,
          mul_nonneg (add_nonneg hCu hCv) (mul_nonneg hdatum0 hexp0)]

#print axioms paper3SignalComponents_strong_bounds_of_X2Sigma_ball_generalM
#print axioms intervalDomainMSignal_c1Distance_le_X2Sigma
#print axioms intervalDomainMX2SigmaDistance_allTime_exponential_bound
#print axioms IntervalDomainMStrongSpectralSemigroupOrbitBound
#print axioms intervalDomainM_strongSpectralSemigroupOrbitBound

end

end ShenWork.Paper3
