/-
  Joint measurability for the windowed source used by the positive-time
  truncated Picard gradient bootstrap.

  The key point is that joint measurability of a parametrized function does
  not by itself make its spatial derivative jointly measurable.  On the
  active region below, the derivative is represented by the measurable
  sequential difference-quotient surrogate `ParamDeriv.diffQuotLimsup`; on
  the inactive region it is assumed (and in the concrete truncated flux is
  proved) to vanish.
-/

import ShenWork.Paper2.IntervalBFormCron2TruncatedPicard
import ShenWork.Paper2.IntervalCompactSliceGradientBounds
import ShenWork.PDE.IntervalParamDerivMeasurable

open MeasureTheory Set Filter
open scoped BigOperators Topology Real

noncomputable section

namespace ShenWork.Paper2.TruncatedPositiveTimeBootstrap

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.Paper2.BFormPositiveDatumNegPart
  (truncatedChemFluxLifted truncatedLogisticLifted truncatedLogisticLocal)

/-- Time-window truncation of a source at one Picard index. -/
def truncatedWindowedSource
    (Src : ℕ → ℝ → ℝ → ℝ) (n : ℕ) (a hi : ℝ) : ℝ → ℝ → ℝ :=
  fun s y => if a ≤ s ∧ s ≤ hi then Src n s y else 0

/-- Windowing preserves joint measurability. -/
theorem truncatedWindowedSource_measurable_of_source_joint
    {Src : ℕ → ℝ → ℝ → ℝ} {n : ℕ} {a hi : ℝ}
    (hSrc : Measurable (Function.uncurry (Src n))) :
    Measurable (Function.uncurry (truncatedWindowedSource Src n a hi)) := by
  change Measurable (fun q : ℝ × ℝ =>
    if a ≤ q.1 ∧ q.1 ≤ hi then Src n q.1 q.2 else 0)
  exact Measurable.ite
    ((measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const))
    hSrc measurable_const

/-- A jointly measurable family has a jointly measurable spatial derivative
on a measurable active region, provided it is differentiable there and its
`deriv` is zero off that region.  Only the requested time window is used. -/
theorem windowed_spatialDeriv_measurable_of_active
    {f : ℝ → ℝ → ℝ} {active : Set (ℝ × ℝ)} {a hi : ℝ}
    (hf : Measurable (Function.uncurry f))
    (hactive : MeasurableSet active)
    (hderiv : ∀ s, a ≤ s → s ≤ hi → ∀ y, (s, y) ∈ active →
      HasDerivAt (f s) (deriv (f s) y) y)
    (hzero : ∀ s, a ≤ s → s ≤ hi → ∀ y, (s, y) ∉ active →
      deriv (f s) y = 0) :
    Measurable (fun q : ℝ × ℝ =>
      if a ≤ q.1 ∧ q.1 ≤ hi then deriv (f q.1) q.2 else 0) := by
  classical
  let g : ℝ × ℝ → ℝ := Function.uncurry f
  have hsurrogate : Measurable (ShenWork.ParamDeriv.diffQuotLimsup g) :=
    ShenWork.ParamDeriv.measurable_diffQuotLimsup hf
  have hrepr :
      (fun q : ℝ × ℝ =>
        if a ≤ q.1 ∧ q.1 ≤ hi then deriv (f q.1) q.2 else 0)
        = fun q : ℝ × ℝ =>
          if (a ≤ q.1 ∧ q.1 ≤ hi) ∧ q ∈ active then
            ShenWork.ParamDeriv.diffQuotLimsup g q
          else 0 := by
    funext q
    by_cases hq : a ≤ q.1 ∧ q.1 ≤ hi
    · by_cases hmem : q ∈ active
      · simp only [hq, hmem, and_self, if_true]
        have hhas : HasDerivAt (fun y' : ℝ => g (q.1, y'))
            (deriv (f q.1) q.2) q.2 := by
          simpa [g, Function.uncurry] using
            hderiv q.1 hq.1 hq.2 q.2 hmem
        exact
          (ShenWork.ParamDeriv.diffQuotLimsup_eq_of_hasDerivAt
            (g := g) hhas).symm
      · simp only [hq, hmem, and_false, if_false]
        exact hzero q.1 hq.1 hq.2 q.2 hmem
    · simp only [hq, false_and, if_false]
  rw [hrepr]
  exact Measurable.ite
    (((measurableSet_le measurable_const measurable_fst).inter
        (measurableSet_le measurable_fst measurable_const)).inter
      hactive)
    hsurrogate measurable_const

private theorem measurable_tsum_nat {X : Type*} [MeasurableSpace X]
    {f : ℕ → X → ℝ} (hf : ∀ n, Measurable (f n)) :
    Measurable (fun x : X => ∑' n : ℕ, f n x) := by
  classical
  let L := SummationFilter.unconditional ℕ
  set S : Finset ℕ → X → ℝ := fun s x => ∑ n ∈ s, f n x with hSdef
  have hS_meas : ∀ s, StronglyMeasurable (S s) := by
    intro s
    exact (Finset.measurable_sum _ (fun n _ => hf n)).stronglyMeasurable
  set C : Set X :=
    {x | ∃ c : ℝ, Tendsto (fun s : Finset ℕ => S s x) L.filter (nhds c)} with hCdef
  have hC_meas : MeasurableSet C := by
    simpa [C] using MeasureTheory.StronglyMeasurable.measurableSet_exists_tendsto
      (l := L.filter) (f := S) hS_meas
  have hlim_meas : Measurable (fun x : X =>
      L.filter.limUnder (fun s : Finset ℕ => S s x)) :=
    (MeasureTheory.StronglyMeasurable.limUnder (l := L.filter) hS_meas).measurable
  have h_eq : (fun x : X => ∑' n : ℕ, f n x) =
      fun x : X => if x ∈ C then L.filter.limUnder (fun s : Finset ℕ => S s x) else 0 := by
    funext x
    by_cases hx : x ∈ C
    · simp only [hx, if_true]
      rcases hx with ⟨c, hc⟩
      have hsum : Summable (fun n : ℕ => f n x) := ⟨c, hc⟩
      exact hsum.hasSum.limUnder_eq.symm
    · simp only [hx, if_false]
      have hnot : ¬ Summable (fun n : ℕ => f n x) := by
        intro hs
        exact hx ⟨∑' n : ℕ, f n x, hs.hasSum⟩
      exact tsum_eq_zero_of_not_summable hnot
  rw [h_eq]
  exact Measurable.ite hC_meas hlim_meas measurable_const

private theorem resolverSourceCoeff_time_measurable_of_lift_joint
    {p : CM2Params} {w : ℝ → intervalDomainPoint → ℝ}
    (hw : Measurable (fun q : ℝ × ℝ => intervalDomainLift (w q.1) q.2))
    (k : ℕ) :
    Measurable (fun s : ℝ =>
      ShenWork.PDE.intervalNeumannResolverSourceCoeff p (w s) k) := by
  set src : ℝ → ℝ → ℂ :=
    fun s x => ((p.ν * intervalDomainLift (w s) x ^ p.γ : ℝ) : ℂ) with hsrc_def
  have hsrc_meas : Measurable (fun q : ℝ × ℝ => src q.1 q.2) := by
    have h_rpow : Measurable (fun x : ℝ => x ^ p.γ) := by fun_prop
    have hpow : Measurable (fun q : ℝ × ℝ =>
        intervalDomainLift (w q.1) q.2 ^ p.γ) := h_rpow.comp hw
    have hreal : Measurable (fun q : ℝ × ℝ =>
        p.ν * intervalDomainLift (w q.1) q.2 ^ p.γ) :=
      measurable_const.mul hpow
    exact Complex.continuous_ofReal.measurable.comp hreal
  have hraw : ∀ n : ℕ, Measurable (fun s : ℝ =>
      ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff
        (fun x : ℝ => src s x) n) := by
    intro n
    set F : ℝ × ℝ → ℂ :=
      fun q => (Real.cos ((n : ℝ) * Real.pi * q.2) : ℂ) * src q.1 q.2 with hF_def
    have hF : Measurable F := by
      have hcos : Measurable (fun q : ℝ × ℝ =>
          (Real.cos ((n : ℝ) * Real.pi * q.2) : ℂ)) := by
        fun_prop
      exact hcos.mul hsrc_meas
    have hI : StronglyMeasurable (fun s : ℝ =>
        ∫ x : ℝ, F (s, x) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
      MeasureTheory.StronglyMeasurable.integral_prod_right'
        (ν := volume.restrict (Set.Ioc (0 : ℝ) 1)) hF.stronglyMeasurable
    have hfun : (fun s : ℝ =>
        ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff
          (fun x : ℝ => src s x) n) =
        fun s : ℝ => ∫ x : ℝ, F (s, x) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      funext s
      rw [ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff,
        intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    rw [hfun]
    exact hI.measurable
  have hcoeff_real : Measurable (fun s : ℝ =>
      ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff
        (fun x : ℝ => src s x) k) := by
    by_cases hk : k = 0
    · subst k
      have hre : Measurable (fun s : ℝ =>
          (ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff
            (fun x : ℝ => src s x) 0).re) :=
        Complex.continuous_re.measurable.comp (hraw 0)
      simpa [ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff] using hre
    · have hre : Measurable (fun s : ℝ =>
          (ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff
            (fun x : ℝ => src s x) k).re) :=
        Complex.continuous_re.measurable.comp (hraw k)
      simpa [ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff, hk] using
        (measurable_const.mul hre)
  have hcomplex : Measurable (fun s : ℝ =>
      ((ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff
        (fun x : ℝ => src s x) k : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hcoeff_real
  simpa [ShenWork.PDE.intervalNeumannResolverSourceCoeff, hsrc_def] using hcomplex

private theorem resolverCoeff_re_time_measurable_of_lift_joint
    {p : CM2Params} {w : ℝ → intervalDomainPoint → ℝ}
    (hw : Measurable (fun q : ℝ × ℝ => intervalDomainLift (w q.1) q.2))
    (k : ℕ) :
    Measurable (fun s : ℝ =>
      (ShenWork.PDE.intervalNeumannResolverCoeff p (w s) k).re) := by
  have hsource := resolverSourceCoeff_time_measurable_of_lift_joint
    (p := p) (w := w) hw k
  have hcoeff : Measurable (fun s : ℝ =>
      ShenWork.PDE.intervalNeumannResolverCoeff p (w s) k) := by
    unfold ShenWork.PDE.intervalNeumannResolverCoeff
    unfold ShenWork.PDE.ResolventEstimate.shiftedNeumannResolventCoeff
    exact measurable_const.mul hsource
  exact Complex.continuous_re.measurable.comp hcoeff

private theorem resolver_lift_joint_measurable_of_lift_joint
    {p : CM2Params} {w : ℝ → intervalDomainPoint → ℝ}
    (hw : Measurable (fun q : ℝ × ℝ => intervalDomainLift (w q.1) q.2)) :
    Measurable (fun q : ℝ × ℝ =>
      intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p (w q.1)) q.2) := by
  have hseries : Measurable (fun q : ℝ × ℝ =>
      ∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverCoeff p (w q.1) k).re *
          unitIntervalCosineMode k q.2) := by
    refine measurable_tsum_nat ?_
    intro k
    have hcoeff : Measurable (fun q : ℝ × ℝ =>
        (ShenWork.PDE.intervalNeumannResolverCoeff p (w q.1) k).re) :=
      (resolverCoeff_re_time_measurable_of_lift_joint (p := p) (w := w) hw k).comp
        measurable_fst
    have hmode : Measurable (fun q : ℝ × ℝ => unitIntervalCosineMode k q.2) := by
      unfold unitIntervalCosineMode
      fun_prop
    exact hcoeff.mul hmode
  have hfun : (fun q : ℝ × ℝ =>
      intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p (w q.1)) q.2) =
      fun q : ℝ × ℝ =>
        if q.2 ∈ Set.Icc (0 : ℝ) 1 then
          ∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverCoeff p (w q.1) k).re *
              unitIntervalCosineMode k q.2
        else 0 := by
    funext q
    by_cases hy : q.2 ∈ Set.Icc (0 : ℝ) 1
    · simp [intervalDomainLift, ShenWork.PDE.intervalNeumannResolverR, hy]
    · simp [intervalDomainLift, hy]
  rw [hfun]
  exact Measurable.ite (measurableSet_Icc.preimage measurable_snd) hseries measurable_const

private theorem resolverGrad_joint_measurable_of_lift_joint
    {p : CM2Params} {w : ℝ → intervalDomainPoint → ℝ}
    (hw : Measurable (fun q : ℝ × ℝ => intervalDomainLift (w q.1) q.2)) :
    Measurable (fun q : ℝ × ℝ => ShenWork.Paper2.resolverGradReal p (w q.1) q.2) := by
  unfold ShenWork.Paper2.resolverGradReal
  refine measurable_tsum_nat ?_
  intro k
  have hcoeff : Measurable (fun q : ℝ × ℝ =>
      (ShenWork.PDE.intervalNeumannResolverCoeff p (w q.1) k).re) :=
    (resolverCoeff_re_time_measurable_of_lift_joint (p := p) (w := w) hw k).comp
      measurable_fst
  have hmode : Measurable (fun q : ℝ × ℝ =>
      -((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * q.2)) := by
    fun_prop
  exact hcoeff.mul hmode

/-- The truncated chemotaxis flux is jointly measurable whenever the lifted
trajectory is jointly measurable. -/
theorem truncatedChemFluxLifted_joint_measurable_of_lift_joint
    {p : CM2Params} {w : ℝ → intervalDomainPoint → ℝ}
    (hw : Measurable (fun q : ℝ × ℝ => intervalDomainLift (w q.1) q.2)) :
    Measurable (Function.uncurry (fun s => truncatedChemFluxLifted p (w s))) := by
  have hR := resolver_lift_joint_measurable_of_lift_joint (p := p) (w := w) hw
  have hG := resolverGrad_joint_measurable_of_lift_joint (p := p) (w := w) hw
  have hpos : Measurable (fun q : ℝ × ℝ =>
      positivePart (intervalDomainLift (w q.1) q.2)) := by
    simpa [positivePart] using hw.max measurable_const
  have hden_base : Measurable (fun q : ℝ × ℝ =>
      1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p (w q.1)) q.2) :=
    measurable_const.add hR
  have h_rpow : Measurable (fun x : ℝ => x ^ p.β) := by fun_prop
  have hden : Measurable (fun q : ℝ × ℝ =>
      (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p (w q.1)) q.2) ^ p.β) :=
    h_rpow.comp hden_base
  have hnum : Measurable (fun q : ℝ × ℝ =>
      positivePart (intervalDomainLift (w q.1) q.2) *
        ShenWork.Paper2.resolverGradReal p (w q.1) q.2) :=
    hpos.mul hG
  simpa [Function.uncurry, truncatedChemFluxLifted] using hnum.div hden

/-- The lifted truncated flux has zero `deriv` outside the open spatial
interior, including at the two endpoints. -/
theorem truncatedChemFluxLifted_deriv_eq_zero_outside_Ioo
    (p : CM2Params) (w : intervalDomainPoint → ℝ) {y : ℝ}
    (hy : y ∉ Set.Ioo (0 : ℝ) 1) :
    deriv (truncatedChemFluxLifted p w) y = 0 := by
  let F : intervalDomainPoint → ℝ := fun x =>
    positivePart (w x) * ShenWork.Paper2.resolverGradReal p w x.1 /
      (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) x.1) ^ p.β
  have hflux_eq : truncatedChemFluxLifted p w = intervalDomainLift F := by
    funext z
    by_cases hz : z ∈ Set.Icc (0 : ℝ) 1
    · simp [truncatedChemFluxLifted, F, intervalDomainLift, hz]
    · simp [truncatedChemFluxLifted, intervalDomainLift, hz, positivePart]
  let W : ℝ → intervalDomainPoint → ℝ := fun _ => F
  rcases lt_or_ge y 0 with hy0 | hy0
  · have hzero : deriv (intervalDomainLift (W 0)) y = 0 := by
      simpa [W] using
        (ShenWork.Paper2.CompactSliceGradientBounds.deriv_lift_eq_zero_on_Iio
          W 0 hy0)
    simpa [hflux_eq, W] using hzero
  rcases lt_or_ge 1 y with hy1 | hy1
  · have hzero : deriv (intervalDomainLift (W 0)) y = 0 := by
      simpa [W] using
        (ShenWork.Paper2.CompactSliceGradientBounds.deriv_lift_eq_zero_on_Ioi
          W 0 hy1)
    simpa [hflux_eq, W] using hzero
  rcases eq_or_lt_of_le hy0 with hy_eq | hy_pos
  · subst y
    have hzero : deriv (intervalDomainLift (W 0)) 0 = 0 := by
      simpa [W] using
        (ShenWork.Paper2.CompactSliceGradientBounds.deriv_lift_eq_zero_at_left
          W 0)
    simpa [hflux_eq, W] using hzero
  rcases eq_or_lt_of_le hy1 with hy_eq | hy_lt_one
  · subst y
    have hzero : deriv (intervalDomainLift (W 0)) 1 = 0 := by
      simpa [W] using
        (ShenWork.Paper2.CompactSliceGradientBounds.deriv_lift_eq_zero_at_right
          W 0)
    simpa [hflux_eq, W] using hzero
  · exact False.elim (hy ⟨hy_pos, hy_lt_one⟩)

/-- The truncated logistic term is jointly measurable whenever the lifted
trajectory is jointly measurable. -/
theorem truncatedLogisticLifted_joint_measurable_of_lift_joint
    {p : CM2Params} {w : ℝ → intervalDomainPoint → ℝ}
    (hw : Measurable (fun q : ℝ × ℝ => intervalDomainLift (w q.1) q.2)) :
    Measurable (Function.uncurry (fun s => truncatedLogisticLifted p (w s))) := by
  have hpos : Measurable (fun q : ℝ × ℝ =>
      positivePart (intervalDomainLift (w q.1) q.2)) := by
    simpa [positivePart] using hw.max measurable_const
  have hpow : Measurable (fun q : ℝ × ℝ =>
      (positivePart (intervalDomainLift (w q.1) q.2)) ^ p.α) := by
    have hrpow : Measurable (fun r : ℝ => r ^ p.α) := by fun_prop
    exact hrpow.comp hpos
  simpa [Function.uncurry, truncatedLogisticLifted, truncatedLogisticLocal] using
    hw.mul (measurable_const.sub (measurable_const.mul hpow))

/-- Global raw-source producer from an explicit jointly measurable flux
derivative field. -/
theorem source_joint_measurable_of_truncated_formula
    {p : CM2Params} {w : ℝ → intervalDomainPoint → ℝ}
    {Src : ℝ → ℝ → ℝ}
    (hw : Measurable (fun q : ℝ × ℝ => intervalDomainLift (w q.1) q.2))
    (hfluxDeriv : Measurable (fun q : ℝ × ℝ =>
      deriv (truncatedChemFluxLifted p (w q.1)) q.2))
    (hSrc : ∀ s y,
      Src s y = truncatedLogisticLifted p (w s) y -
        p.χ₀ * deriv (truncatedChemFluxLifted p (w s)) y) :
    Measurable (Function.uncurry Src) := by
  have hlog := truncatedLogisticLifted_joint_measurable_of_lift_joint (p := p) hw
  have hrepr : Function.uncurry Src = fun q : ℝ × ℝ =>
      truncatedLogisticLifted p (w q.1) q.2 -
        p.χ₀ * deriv (truncatedChemFluxLifted p (w q.1)) q.2 := by
    funext q
    exact hSrc q.1 q.2
  rw [hrepr]
  exact hlog.sub (measurable_const.mul hfluxDeriv)

/-- Local, non-circular producer for the windowed Picard source.

The two flux hypotheses are needed only on `[a,hi]`.  In the concrete
truncated bootstrap they follow respectively from the positive-region product
rule and from the zero derivative lemma on the nonpositive region. -/
theorem truncatedWindowedSource_measurable_of_truncated_formula
    {p : CM2Params} {w : ℝ → intervalDomainPoint → ℝ}
    {Src : ℕ → ℝ → ℝ → ℝ} {n : ℕ} {a hi : ℝ}
    (hw : Measurable (fun q : ℝ × ℝ => intervalDomainLift (w q.1) q.2))
    (hfluxDeriv_pos : ∀ s, a ≤ s → s ≤ hi → ∀ y,
      y ∈ Set.Ioo (0 : ℝ) 1 →
      0 < intervalDomainLift (w s) y →
        HasDerivAt (truncatedChemFluxLifted p (w s))
          (deriv (truncatedChemFluxLifted p (w s)) y) y)
    (hfluxDeriv_zero : ∀ s, a ≤ s → s ≤ hi → ∀ y,
      y ∈ Set.Ioo (0 : ℝ) 1 →
      intervalDomainLift (w s) y ≤ 0 →
        deriv (truncatedChemFluxLifted p (w s)) y = 0)
    (hSrc : ∀ s y,
      Src n s y = truncatedLogisticLifted p (w s) y -
        p.χ₀ * deriv (truncatedChemFluxLifted p (w s)) y) :
    Measurable (Function.uncurry (truncatedWindowedSource Src n a hi)) := by
  have hflux := truncatedChemFluxLifted_joint_measurable_of_lift_joint (p := p) hw
  let active : Set (ℝ × ℝ) :=
    {q | q.2 ∈ Set.Ioo (0 : ℝ) 1 ∧ 0 < intervalDomainLift (w q.1) q.2}
  have hactive : MeasurableSet active := by
    exact (measurableSet_Ioo.preimage measurable_snd).inter
      (measurableSet_lt measurable_const hw)
  have hD : Measurable (fun q : ℝ × ℝ =>
      if a ≤ q.1 ∧ q.1 ≤ hi then
        deriv (truncatedChemFluxLifted p (w q.1)) q.2
      else 0) :=
    windowed_spatialDeriv_measurable_of_active
      hflux hactive
        (fun s has hshi y hy =>
          hfluxDeriv_pos s has hshi y hy.1 hy.2)
        (fun s has hshi y hy => by
          by_cases hyIoo : y ∈ Set.Ioo (0 : ℝ) 1
          · apply hfluxDeriv_zero s has hshi y hyIoo
            apply le_of_not_gt
            intro hpos
            exact hy ⟨hyIoo, hpos⟩
          · exact truncatedChemFluxLifted_deriv_eq_zero_outside_Ioo
              p (w s) hyIoo)
  have hlog := truncatedLogisticLifted_joint_measurable_of_lift_joint (p := p) hw
  have hwin : MeasurableSet {q : ℝ × ℝ | a ≤ q.1 ∧ q.1 ≤ hi} :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const)
  have hlogWin : Measurable (fun q : ℝ × ℝ =>
      if a ≤ q.1 ∧ q.1 ≤ hi then
        truncatedLogisticLifted p (w q.1) q.2
      else 0) :=
    Measurable.ite hwin hlog measurable_const
  have hrepr : Function.uncurry (truncatedWindowedSource Src n a hi) =
      fun q : ℝ × ℝ =>
        (if a ≤ q.1 ∧ q.1 ≤ hi then
          truncatedLogisticLifted p (w q.1) q.2
        else 0) - p.χ₀ *
          (if a ≤ q.1 ∧ q.1 ≤ hi then
            deriv (truncatedChemFluxLifted p (w q.1)) q.2
          else 0) := by
    funext q
    by_cases hq : a ≤ q.1 ∧ q.1 ≤ hi
    · simp [truncatedWindowedSource, Function.uncurry, hq, hSrc]
    · simp [truncatedWindowedSource, Function.uncurry, hq]
  rw [hrepr]
  exact hlogWin.sub (measurable_const.mul hD)

end ShenWork.Paper2.TruncatedPositiveTimeBootstrap
