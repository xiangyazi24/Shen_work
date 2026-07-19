import ShenWork.Paper1.WholeLineLocalMomentEnergyProducer
import ShenWork.Paper1.WholeLineLocalMomentBound
import ShenWork.Paper1.WholeLineWeightedRegularityGlobalStrictPositivityNatural

/-!
# Canonical global producer for whole-line local-moment energy data

This file transports the segment-level local-moment package through the
canonical restart construction, proves continuity of the glued local energy,
and closes the uniformly local `Lᴾ` estimate.
-/

open Filter Function MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-! ## Transport through a restart -/

/-- Transport local-moment time data through a time translation and a germ
identity at the target time. -/
private theorem localMomentTimeData_transport
    {P κ t x₀ a : ℝ} {u w : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentTimeData P κ (t - a) x₀ w
      (fun s x => deriv (fun r : ℝ => w r x) s))
    (heq : (fun s => u s) =ᶠ[nhds t] fun s => w (s - a)) :
    ∃ _H' : WholeLineLocalMomentTimeData P κ t x₀ u
      (fun s x => deriv (fun r : ℝ => u r x) s), True := by
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp heq
  let δ : ℝ := min ε H.δ
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min hε H.hδ
  have hball_eq : ∀ {s : ℝ}, s ∈ Metric.ball t δ →
      s ∈ Metric.ball t ε := by
    intro s hs
    exact Metric.ball_subset_ball (min_le_left ε H.δ) hs
  have hball_shift : ∀ {s : ℝ}, s ∈ Metric.ball t δ →
      s - a ∈ Metric.ball (t - a) H.δ := by
    intro s hs
    have hslt : dist s t < δ := hs
    have hlt : dist s t < H.δ :=
      hslt.trans_le (min_le_right ε H.δ)
    rw [Metric.mem_ball]
    calc
      dist (s - a) (t - a) = dist s t := by
        simp only [Real.dist_eq]
        congr 1
        ring
      _ < H.δ := hlt
  have heq_at : ∀ {s : ℝ}, s ∈ Metric.ball t ε →
      (fun r => u r) =ᶠ[nhds s] fun r => w (r - a) := by
    intro s hs
    filter_upwards [Metric.isOpen_ball.mem_nhds hs] with r hr
    exact hεsub hr
  have hderiv_eq : ∀ {s : ℝ}, s ∈ Metric.ball t ε → ∀ x,
      deriv (fun r : ℝ => u r x) s =
        deriv (fun r : ℝ => w r x) (s - a) := by
    intro s hs x
    have hscalar : (fun r : ℝ => u r x) =ᶠ[nhds s]
        fun r => w (r - a) x := by
      filter_upwards [heq_at hs] with r hr
      exact congrFun hr x
    rw [hscalar.deriv_eq]
    exact deriv_comp_sub_const (fun r : ℝ => w r x) a s
  have hshift : Tendsto (fun s : ℝ => s - a) (nhds t) (nhds (t - a)) :=
    (continuous_id.sub continuous_const).continuousAt
  have hut : u t = w (t - a) := heq.self_of_nhds
  refine ⟨
    { δ := δ
      bound := H.bound
      hδ := hδ
      integrand_aeStronglyMeasurable := ?_
      integrand_integrable := ?_
      derivative_aeStronglyMeasurable := ?_
      derivative_bound := ?_
      bound_integrable := H.bound_integrable
      hasDerivAt_u := ?_ }, trivial⟩
  · filter_upwards [heq,
      hshift.eventually H.integrand_aeStronglyMeasurable] with s hus hs
    simpa only [hus] using hs
  · simpa only [hut] using H.integrand_integrable
  · have htε : t ∈ Metric.ball t ε := Metric.mem_ball_self hε
    have hdt : ∀ x,
        deriv (fun r : ℝ => u r x) t =
          deriv (fun r : ℝ => w r x) (t - a) := hderiv_eq htε
    simpa only [hut, hdt] using H.derivative_aeStronglyMeasurable
  · filter_upwards [H.derivative_bound] with x hx
    intro s hs
    have hsε : s ∈ Metric.ball t ε := hball_eq hs
    have hus : u s = w (s - a) := hεsub hsε
    have hds := hderiv_eq hsε x
    simpa only [hus, hds] using hx (s - a) (hball_shift hs)
  · filter_upwards [H.hasDerivAt_u] with x hx
    intro s hs
    have hsε : s ∈ Metric.ball t ε := hball_eq hs
    have hscalar : (fun r : ℝ => u r x) =ᶠ[nhds s]
        fun r => w (r - a) x := by
      filter_upwards [heq_at hsε] with r hr
      exact congrFun hr x
    have hw := hx (s - a) (hball_shift hs)
    have hcomp := hw.comp s ((hasDerivAt_id s).sub_const a)
    have htranslated : HasDerivAt (fun r : ℝ => w (r - a) x)
        (deriv (fun r : ℝ => w r x) (s - a)) s := by
      simpa only [Function.comp_apply, id_eq, mul_one] using hcomp
    have hu := htranslated.congr_of_eventuallyEq hscalar
    rw [hderiv_eq hsε x]
    exact hu

/-- Static energy data transport across equal time slices, with the time
field supplied separately because it depends on a full time germ. -/
private noncomputable def localMomentEnergyData_of_slice_eq
    {p : CMParams} {P κ T T' t q x₀ : ℝ}
    {u v w z : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentEnergyData p P κ T' q x₀ w z)
    (hsol : IsClassicalSolution p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (htime : WholeLineLocalMomentTimeData P κ t x₀ u
      (fun s x => deriv (fun r : ℝ => u r x) s))
    (hu : u t = w q) (hv : v t = z q) :
    WholeLineLocalMomentEnergyData p P κ T t x₀ u v := by
  have htest : wholeLineLocalLpTest P κ u t x₀ =
      wholeLineLocalLpTest P κ w q x₀ := by
    funext x
    simp only [wholeLineLocalLpTest, hu]
  have htestDeriv : wholeLineLocalLpTestDeriv P κ u t x₀ =
      wholeLineLocalLpTestDeriv P κ w q x₀ := by
    funext x
    simp only [wholeLineLocalLpTestDeriv, hu]
  have hflux : wholeLineLocalChemotaxisFlux p u v t =
      wholeLineLocalChemotaxisFlux p w z q := by
    funext x
    simp only [wholeLineLocalChemotaxisFlux, hu, hv]
  refine
    { hP := H.hP
      hκ := H.hκ
      ht0 := ht0
      htT := htT
      solution := hsol
      u_pos := ?_
      time := htime
      diffusion := ?_
      diffusionWeight := ?_
      chemotaxisFirst := ?_
      chemotaxisSecond := ?_
      diffusion_dissipation_integrable := ?_
      diffusion_weightCross_integrable := ?_
      weightSecond_integrable := ?_
      chemotaxis_firstCross_integrable := ?_
      moment_integrable := ?_
      logistic_integrable := ?_
      chemotaxis_high_integrable := ?_
      signal_integrable := ?_
      signal_secondDerivative_integrable := ?_
      signal_weightCross_integrable := ?_
      signal_gradient_abs_integrable := ?_ }
  · simpa only [hu] using H.u_pos
  · simpa only [htest, htestDeriv, hu] using H.diffusion
  · simpa only [hu] using H.diffusionWeight
  · simpa only [htest, htestDeriv, hflux] using H.chemotaxisFirst
  · simpa only [hu, hv] using H.chemotaxisSecond
  · simpa only [hu] using H.diffusion_dissipation_integrable
  · simpa only [hu] using H.diffusion_weightCross_integrable
  · simpa only [hu] using H.weightSecond_integrable
  · simpa only [hu, hv] using H.chemotaxis_firstCross_integrable
  · simpa only [hu] using H.moment_integrable
  · simpa only [hu] using H.logistic_integrable
  · simpa only [hu] using H.chemotaxis_high_integrable
  · simpa only [hu, hv] using H.signal_integrable
  · simpa only [hu, hv] using H.signal_secondDerivative_integrable
  · simpa only [hu, hv] using H.signal_weightCross_integrable
  · simpa only [hu, hv] using H.signal_gradient_abs_integrable

/-! ## Global energy-data producer -/

/-- The canonical global orbit supplies the complete local-moment energy
package at every positive time by reducing to its preferred restart segment. -/
noncomputable def wholeLineCauchyGlobal_localMomentEnergyData
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hleft : StrictlyPositiveAtLeft u₀.1)
    {T P κ t : ℝ} (hT : 0 < T) (hP : 1 < P) (hκ : 0 < κ)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) (x₀ : ℝ) :
    WholeLineLocalMomentEnergyData p P κ T t x₀
      (wholeLineCauchyGlobalU p u₀)
      (wholeLineCauchyGlobalV p u₀) := by
  let n := wholeLineCauchyGlobalIndex p u₀ t
  let a := (n : ℝ) * wholeLineCauchyGlobalStep p u₀
  let q := t - a
  have hq0 : 0 < q := by
    simpa [q, a, n, wholeLineCauchyGlobalLocalTime] using
      (wholeLineCauchyGlobalLocalTime_pos p u₀ ht.1)
  have hqH : q < wholeLineCauchyGlobalSegmentTime p u₀ := by
    simpa [q, a, n, wholeLineCauchyGlobalLocalTime] using
      (wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht.1.le)
  have hstrip : ∀ z : Set.Icc (0 : ℝ)
      (wholeLineCauchyGlobalSegmentTime p u₀), ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p
        (wholeLineCauchyGlobalClamp_pos p u₀).le
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
        (wholeLineCauchyGlobalDatum p u₀ n)
        (wholeLineCauchyGlobalSegmentTime_rate p u₀) z).1 x ∈
          Set.Icc (0 : ℝ) (wholeLineCauchyGlobalClamp p u₀) := by
    simpa [wholeLineCauchyGlobalSegment] using
      (wholeLineCauchyGlobalDatum_segment_bounds
        p hregime u₀ hu₀ n).2.1
  have hpos : ∀ z : Set.Icc (0 : ℝ)
      (wholeLineCauchyGlobalSegmentTime p u₀), 0 < z.1 → ∀ x,
      0 < (wholeLineCauchyBUCMildFixedPoint p
        (wholeLineCauchyGlobalClamp_pos p u₀).le
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
        (wholeLineCauchyGlobalDatum p u₀ n)
        (wholeLineCauchyGlobalSegmentTime_rate p u₀) z).1 x := by
    simpa [wholeLineCauchyGlobalSegment] using
      (wholeLineCauchyGlobalDatum_segment_pos_and_left_of_posAtBot
        p hregime u₀ hu₀ hleft n).2.1
  let Hlocal :=
    wholeLineCauchyBUCMildFixedPoint_localMomentEnergyData
      p (M := wholeLineCauchyGlobalClamp p u₀)
      (T := wholeLineCauchyGlobalSegmentTime p u₀)
      (P := P) (κ := κ) (t := q) (x₀ := x₀)
      (wholeLineCauchyGlobalClamp_pos p u₀).le
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
      hP hκ hq0 hqH (wholeLineCauchyGlobalDatum p u₀ n)
      (wholeLineCauchyGlobalSegmentTime_rate p u₀) hstrip hpos
  have Hlocal' : WholeLineLocalMomentEnergyData p P κ
      (wholeLineCauchyGlobalSegmentTime p u₀) q x₀
      (wholeLineCauchyGlobalSegmentU p u₀ n)
      (wholeLineCauchyGlobalSegmentV p u₀ n) := by
    simpa [wholeLineCauchyGlobalSegmentU, wholeLineCauchyGlobalSegmentV,
      wholeLineCauchyGlobalSegment] using Hlocal
  have heqU :
      (fun s => wholeLineCauchyGlobalU p u₀ s) =ᶠ[nhds t]
        fun s => wholeLineCauchyGlobalSegmentU p u₀ n (s - a) := by
    filter_upwards [wholeLineCauchyGlobalBUC_eventuallyEq_preferred
      p hregime u₀ hu₀ ht.1] with s hs
    funext x
    have hx := congrArg (fun w : WholeLineBUC => w.1 x) hs
    simpa [wholeLineCauchyGlobalU, wholeLineCauchyGlobalSegmentU, n, a] using hx
  have htimeExists := localMomentTimeData_transport Hlocal'.time heqU
  let htime := Classical.choose htimeExists
  have hu : wholeLineCauchyGlobalU p u₀ t =
      wholeLineCauchyGlobalSegmentU p u₀ n q := by
    funext y
    have hy := (wholeLineCauchyGlobalU_eventuallyEq_segment
      p hregime u₀ hu₀ ht.1 y).eq_of_nhds
    simpa [n, a, q] using hy
  have hv : wholeLineCauchyGlobalV p u₀ t =
      wholeLineCauchyGlobalSegmentV p u₀ n q := by
    funext y
    have hy := (wholeLineCauchyGlobalV_eventuallyEq_segment
      p hregime u₀ hu₀ ht.1 y).eq_of_nhds
    simpa [n, a, q] using hy
  exact localMomentEnergyData_of_slice_eq Hlocal'
    (wholeLineCauchyGlobal_isGlobalClassicalSolution
      p hregime u₀ hu₀ T hT)
    ht.1 ht.2 htime hu hv

/-! ## Continuity of the glued local energy -/

private theorem wholeLineCauchyGlobalBUC_continuousAt_positive_localMoment
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {t : ℝ} (ht : 0 < t) :
    ContinuousAt (wholeLineCauchyGlobalBUC p u₀) t := by
  let n := wholeLineCauchyGlobalIndex p u₀ t
  let a := (n : ℝ) * wholeLineCauchyGlobalStep p u₀
  have hev := wholeLineCauchyGlobalBUC_eventuallyEq_preferred
    p hregime u₀ hu₀ ht
  have hlocal : ContinuousAt (fun s =>
      wholeLineBUCTrajectoryExtend
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
        (wholeLineCauchyGlobalSegment p u₀ n) (s - a)) t :=
    ((wholeLineBUCTrajectoryExtend_continuous
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
      (wholeLineCauchyGlobalSegment p u₀ n)).comp
        (continuous_id.sub continuous_const)).continuousAt
  exact hlocal.congr_of_eventuallyEq (by simpa [n, a] using hev)

private theorem wholeLineCauchyGlobalBUC_continuousWithinAt_zero_localMoment
    (p : CMParams) (u₀ : WholeLineBUC) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousWithinAt (wholeLineCauchyGlobalBUC p u₀) (Icc 0 T) 0 := by
  let U := wholeLineCauchyGlobalSegment p u₀ 0
  let f : ℝ → WholeLineBUC := fun s =>
    wholeLineBUCTrajectoryExtend
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le U s
  have hf : ContinuousAt f 0 :=
    (wholeLineBUCTrajectoryExtend_continuous
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le U).continuousAt
  have hev : wholeLineCauchyGlobalBUC p u₀ =ᶠ[nhdsWithin 0 (Icc 0 T)] f := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds
        (Iio_mem_nhds (wholeLineCauchyGlobalStep_pos p u₀))]
      with s hs hsstep
    have hcell : s ∈ Ico ((0 : ℕ) * wholeLineCauchyGlobalStep p u₀)
        (((0 : ℕ) + 1) * wholeLineCauchyGlobalStep p u₀) := by
      simpa using ⟨hs.1, hsstep⟩
    have heq := wholeLineCauchyGlobalBUC_eq_preferred_on_cell
      p u₀ 0 hcell
    simpa [f, U] using heq
  exact hf.continuousWithinAt.congr_of_eventuallyEq hev
    (hev.eq_of_nhdsWithin ⟨le_rfl, hT⟩)

private theorem wholeLineCauchyGlobalBUC_continuousOn_localMoment
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (wholeLineCauchyGlobalBUC p u₀) (Icc 0 T) := by
  intro t ht
  by_cases htz : t = 0
  · simpa [htz] using
      wholeLineCauchyGlobalBUC_continuousWithinAt_zero_localMoment
        p u₀ (T := T) hT
  · exact (wholeLineCauchyGlobalBUC_continuousAt_positive_localMoment
      p hregime u₀ hu₀
        (lt_of_le_of_ne ht.1 (Ne.symm htz))).continuousWithinAt

/-- The local `Lᴾ` energy of the canonical glued orbit is continuous up to
time zero. -/
theorem wholeLineCauchyGlobal_localLpEnergy_continuousOn
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {P κ T : ℝ} (hT : 0 ≤ T) (hP : 1 < P) (hκ : 0 < κ) (x₀ : ℝ) :
    ContinuousOn
      (fun t : ℝ => wholeLineLocalLpEnergy P κ
        (wholeLineCauchyGlobalU p u₀) t x₀) (Icc 0 T) := by
  let M := wholeLineCauchyStableCeiling p u₀
  have hM : 0 ≤ M :=
    zero_le_one.trans (wholeLineCauchyStableCeiling_one_le hregime u₀)
  have hP0 : 0 ≤ P := by linarith
  have hBUC := wholeLineCauchyGlobalBUC_continuousOn_localMoment
    p hregime u₀ hu₀ (T := T) hT
  intro t ht
  let F : ℝ → ℝ → ℝ := fun s x =>
    (wholeLineCauchyGlobalU p u₀ s x) ^ P *
      localizingWeightAt κ x₀ x
  let bound : ℝ → ℝ := fun x => M ^ P * localizingWeightAt κ x₀ x
  have hmeas : ∀ᶠ s in nhdsWithin t (Icc 0 T),
      AEStronglyMeasurable (F s) volume := by
    filter_upwards [] with s
    exact (((Real.continuous_rpow_const hP0).comp
      (WholeLineBUC.isCUnifBdd
        (wholeLineCauchyGlobalBUC p u₀ s)).1).mul
          continuous_localizingWeightAt).aestronglyMeasurable
  have hbound : ∀ᶠ s in nhdsWithin t (Icc 0 T),
      ∀ᵐ x ∂volume, ‖F s x‖ ≤ bound x := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards [] with x
    have hu0 := wholeLineCauchyGlobal_nonnegative
      p hregime u₀ hu₀ hs.1 x
    have huM := wholeLineCauchyGlobal_le_stableCeiling
      p hregime u₀ hu₀ hs.1 x
    have hpow := Real.rpow_le_rpow hu0 huM hP0
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hu0 P),
      abs_of_pos (localizingWeightAt_pos κ x₀ x)]
    exact mul_le_mul_of_nonneg_right hpow
      (localizingWeightAt_pos κ x₀ x).le
  have hboundInt : Integrable bound volume :=
    (localizingWeightAt_integrable hκ x₀).const_mul (M ^ P)
  have hlim : ∀ᵐ x ∂volume,
      Tendsto (fun s => F s x) (nhdsWithin t (Icc 0 T)) (nhds (F t x)) := by
    filter_upwards [] with x
    have heval : Continuous (fun w : WholeLineBUC => w.1 x) := by fun_prop
    have hu := heval.continuousAt.tendsto.comp (hBUC t ht)
    exact (((Real.continuous_rpow_const hP0).tendsto
      (wholeLineCauchyGlobalU p u₀ t x)).comp hu).mul_const _
  have hint := tendsto_integral_filter_of_dominated_convergence
    bound hmeas hbound hboundInt hlim
  change Tendsto
    (fun s => (1 / P) * ∫ x, F s x)
    (nhdsWithin t (Icc 0 T)) (nhds ((1 / P) * ∫ x, F t x))
  exact hint.const_mul (1 / P)

/-! ## Uniform local-moment closure -/

/-- Assemble the abstract local-moment bound package from a supplied
positive-time energy-data producer. -/
private noncomputable def
    wholeLineCauchyGlobal_localMomentBoundData_of_energyData
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {P κ T : ℝ}
    (hT : 0 ≤ T) (hP : max 1 (max p.m p.γ) < P)
    (hκ : 0 < κ) (hκhalf : κ < 1 / 2)
    (hχ : 0 ≤ p.χ) (hcritical : p.α = p.m + p.γ - 1)
    (hadmissible : p.χ * (P - 1) < P + p.m - 1)
    (habsorption : 0 < wholeLineLocalMomentAbsorption p P κ)
    (henergyData : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x₀ : ℝ,
      WholeLineLocalMomentEnergyData p P κ T t x₀
        (wholeLineCauchyGlobalU p u₀)
        (wholeLineCauchyGlobalV p u₀)) :
    WholeLineLocalMomentBoundData p P κ T
      (wholeLineCauchyStableCeiling p u₀)
      (wholeLineCauchyGlobalU p u₀)
      (wholeLineCauchyGlobalV p u₀) := by
  have hPone : 1 < P :=
    lt_of_le_of_lt (le_max_left 1 (max p.m p.γ)) hP
  refine
    { hT := hT
      hP := hP
      hκ := hκ
      hκhalf := hκhalf
      hχ := hχ
      hcritical := hcritical
      admissible := hadmissible
      absorption_pos := habsorption
      energyData := henergyData
      u_nonnegative := ?_
      u_slice_isCUnifBdd := ?_
      resolver := ?_
      energy_continuous := ?_
      hU₀ := ?_
      initial_isCUnifBdd := ?_
      initial_upper := ?_ }
  · intro t ht x
    exact wholeLineCauchyGlobal_nonnegative p hregime u₀ hu₀ ht.1 x
  · intro t _ht
    exact WholeLineBUC.isCUnifBdd (wholeLineCauchyGlobalBUC p u₀ t)
  · intro t _ht
    rfl
  · intro x₀
    exact wholeLineCauchyGlobal_localLpEnergy_continuousOn
      p hregime u₀ hu₀ hT hPone hκ x₀
  · exact zero_le_one.trans
      (wholeLineCauchyStableCeiling_one_le hregime u₀)
  · have hzero : wholeLineCauchyGlobalU p u₀ 0 = fun x => u₀.1 x := by
      funext x
      change (wholeLineCauchyGlobalBUC p u₀ 0).1 x = u₀.1 x
      rw [wholeLineCauchyGlobalBUC_zero]
    rw [hzero]
    exact WholeLineBUC.isCUnifBdd u₀
  · intro x
    simpa only [wholeLineCauchyGlobalU,
      wholeLineCauchyGlobalBUC_zero] using
        (wholeLineCauchyStableCeiling_initial_lt p u₀ x).le

/-- The canonical global orbit supplies every field required by the
time-uniform local-moment estimate. -/
noncomputable def wholeLineCauchyGlobal_localMomentBoundData
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hleft : StrictlyPositiveAtLeft u₀.1)
    {P κ T : ℝ}
    (hT : 0 ≤ T) (hP : max 1 (max p.m p.γ) < P)
    (hκ : 0 < κ) (hκhalf : κ < 1 / 2)
    (hχ : 0 ≤ p.χ) (hcritical : p.α = p.m + p.γ - 1)
    (hadmissible : p.χ * (P - 1) < P + p.m - 1)
    (habsorption : 0 < wholeLineLocalMomentAbsorption p P κ) :
    WholeLineLocalMomentBoundData p P κ T
      (wholeLineCauchyStableCeiling p u₀)
      (wholeLineCauchyGlobalU p u₀)
      (wholeLineCauchyGlobalV p u₀) := by
  have hPone : 1 < P :=
    lt_of_le_of_lt (le_max_left 1 (max p.m p.γ)) hP
  apply wholeLineCauchyGlobal_localMomentBoundData_of_energyData
    p hregime u₀ hu₀ hT hP hκ hκhalf hχ hcritical
      hadmissible habsorption
  intro t ht x₀
  exact wholeLineCauchyGlobal_localMomentEnergyData
    p hregime u₀ hu₀ hleft (ht.1.trans ht.2) hPone hκ ht x₀

/-- Uniformly local `Lᴾ` bound for the canonical global orbit. -/
theorem wholeLineCauchyGlobal_uniformlyLocalLpBounded
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hleft : StrictlyPositiveAtLeft u₀.1)
    {P κ T : ℝ}
    (hT : 0 ≤ T) (hP : max 1 (max p.m p.γ) < P)
    (hκ : 0 < κ) (hκhalf : κ < 1 / 2)
    (hχ : 0 ≤ p.χ) (hcritical : p.α = p.m + p.γ - 1)
    (hadmissible : p.χ * (P - 1) < P + p.m - 1)
    (habsorption : 0 < wholeLineLocalMomentAbsorption p P κ) :
    UniformlyLocalLpBounded P κ (wholeLineCauchyGlobalU p u₀) T
      (wholeLineLocalMomentUniformBound p P κ
        (wholeLineCauchyStableCeiling p u₀)) :=
  (wholeLineCauchyGlobal_localMomentBoundData
    p hregime u₀ hu₀ hleft hT hP hκ hκhalf hχ hcritical
      hadmissible habsorption).uniformlyLocalLpBounded

section AxiomAudit

#print axioms wholeLineCauchyGlobal_localMomentEnergyData
#print axioms wholeLineCauchyGlobal_localMomentBoundData
#print axioms wholeLineCauchyGlobal_uniformlyLocalLpBounded

end AxiomAudit

end ShenWork.Paper1
