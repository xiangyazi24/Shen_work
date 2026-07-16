import ShenWork.Paper3.LyapunovFunction
import ShenWork.Paper2.IntervalDomainMLpTimeLeibniz
import ShenWork.Paper2.IntervalDomainMass

/-!
# Time differentiation of the Paper 3 entropy for the faithful general-`m` equation

For a positive classical solution of the paper-faithful `u^m`-flux system on
the unit interval this file proves, directly from the shared classical
regularity fields, the chain rule

`d/dt ∫ h_m(u) = ∫ (1 - (uStar/u)^(2m-1)) u_t`.

This is the general-`m` counterpart of
`ShenWork/Paper3/IntervalDomainEntropyTimeDerivative.lean`, which hardcodes
`chemotaxisEntropyDensity 1` and the legacy `intervalDomain` equation.  The
Leibniz argument is kinematic: it uses only regularity, positivity, and the
general-`m` scalar entropy FTC layer from `LyapunovFunction.lean`, so no `m`
hypothesis at all is needed here.
-/

open ShenWork.IntervalDomain MeasureTheory
open ShenWork.IntervalUnderIntegralLeibniz
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open scoped Topology Interval

namespace ShenWork.Paper3

noncomputable section

/-- Lifted general-`m` entropy density used by the interval Leibniz argument. -/
def intervalDomainMEntropyLiftIntegrand
    (m : ℝ) (u : ℝ → intervalDomain.Point → ℝ) (uStar s y : ℝ) : ℝ :=
  chemotaxisEntropyDensity m uStar (intervalDomainLift (u s) y)

/-- Lifted derivative field for the general-`m` entropy. -/
def intervalDomainMEntropyTimeDerivIntegrand
    (m : ℝ) (u : ℝ → intervalDomain.Point → ℝ) (uStar s y : ℝ) : ℝ :=
  chemotaxisEntropyIntegrand m uStar (intervalDomainLift (u s) y) *
    ShenWork.Paper2.intervalDomainMassTimeDerivIntegrand u s y

/-- Pointwise scalar chain rule at an interior spatial point. -/
theorem intervalDomainMEntropyLiftIntegrand_hasDerivAt_interior
    {p : CM2Params} {T m uStar : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution intervalDomainM p T u v)
    {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1)
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (huStar : 0 < uStar) :
    HasDerivAt
      (fun r => intervalDomainMEntropyLiftIntegrand m u uStar r y)
      (intervalDomainMEntropyTimeDerivIntegrand m u uStar s y) s := by
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
  let x : intervalDomain.Point := ⟨y, hyIcc⟩
  have hlift : ∀ r : ℝ, intervalDomainLift (u r) y = u r x := by
    intro r
    simp [intervalDomainLift, hyIcc, x]
  have huDeriv : HasDerivAt (fun r : ℝ => u r x)
      (intervalDomain.timeDeriv u s x) s :=
    ShenWork.Paper2.IntervalDomainM.timeDeriv_isGenuine hsol (x := x) hy hs
  have huPos : 0 < u s x := hsol.u_pos' hs.1 hs.2
  have hchain := chemotaxisEntropyDensity_comp_hasDerivAt
    (m := m) huStar huPos huDeriv
  have hfun : (fun r => intervalDomainMEntropyLiftIntegrand m u uStar r y) =
      fun r => chemotaxisEntropyDensity m uStar (u r x) := by
    funext r
    simp [intervalDomainMEntropyLiftIntegrand, hlift]
  have htime :
      ShenWork.Paper2.intervalDomainMassTimeDerivIntegrand u s y =
        intervalDomain.timeDeriv u s x := by
    unfold ShenWork.Paper2.intervalDomainMassTimeDerivIntegrand
    rw [show (fun r : ℝ => intervalDomainLift (u r) y) =
      fun r => u r x from funext hlift]
    rfl
  rw [hfun]
  simpa [intervalDomainMEntropyTimeDerivIntegrand, hlift, htime] using hchain

/-- The concrete entropy functional is the interval integral of the lifted
entropy density.  This holds for any exponent `m` and any slice. -/
theorem intervalDomainM_entropyFunctional_eq_lift_integral
    (m : ℝ) (u : ℝ → intervalDomain.Point → ℝ) (uStar t : ℝ) :
    chemotaxisEntropyFunctional intervalDomain m uStar u t =
      ∫ y in (0 : ℝ)..1,
        intervalDomainMEntropyLiftIntegrand m u uStar t y := by
  change intervalDomainIntegral
      (fun x => chemotaxisEntropyDensity m uStar (u t x)) = _
  unfold intervalDomainIntegral
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le zero_le_one] at hy
  simp [intervalDomainMEntropyLiftIntegrand, intervalDomainLift, hy]

/-- Localized Leibniz theorem for the general-`m` entropy functional. -/
theorem intervalDomainM_entropy_hasDerivAt_of_slabContinuous
    {p : CM2Params} {T m uStar t delta : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution intervalDomainM p T u v)
    (huStar : 0 < uStar) (hdelta : 0 < delta)
    (hball : Metric.ball t delta ⊆ Set.Ioo (0 : ℝ) T)
    (hFmeas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (intervalDomainMEntropyLiftIntegrand m u uStar s)
        intervalDomainInteriorMeasure)
    (hFint : IntervalIntegrable
      (intervalDomainMEntropyLiftIntegrand m u uStar t) volume 0 1)
    (hF'meas : AEStronglyMeasurable
      (intervalDomainMEntropyTimeDerivIntegrand m u uStar t)
        intervalDomainInteriorMeasure)
    (hslab : ContinuousOn
      (Function.uncurry (intervalDomainMEntropyTimeDerivIntegrand m u uStar))
      (Set.Icc (t - delta) (t + delta) ×ˢ Set.Icc (0 : ℝ) 1)) :
    HasDerivAt
      (fun s => chemotaxisEntropyFunctional intervalDomain m uStar u s)
      (∫ y in (0 : ℝ)..1,
        intervalDomainMEntropyTimeDerivIntegrand m u uStar t y) t := by
  obtain ⟨bound, hboundInt, hbound⟩ :=
    exists_bound_of_continuousOn_slab hdelta hslab
  have hdiff : ∀ᵐ y ∂intervalDomainInteriorMeasure,
      ∀ s ∈ Metric.ball t delta,
        HasDerivAt
          (fun r => intervalDomainMEntropyLiftIntegrand m u uStar r y)
          (intervalDomainMEntropyTimeDerivIntegrand m u uStar s y) s := by
    refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
    exact Filter.Eventually.of_forall fun y hy s hs =>
      intervalDomainMEntropyLiftIntegrand_hasDerivAt_interior
        hsol hy (hball hs) huStar
  have hderiv := intervalIntegral_hasDerivAt_time_of_local
    hdelta hFmeas hFint hF'meas hbound hboundInt hdiff
  have hfun :
      (fun s => chemotaxisEntropyFunctional intervalDomain m uStar u s) =
        fun s => ∫ y in (0 : ℝ)..1,
          intervalDomainMEntropyLiftIntegrand m u uStar s y := by
    funext s
    exact intervalDomainM_entropyFunctional_eq_lift_integral m u uStar s
  rw [hfun]
  exact hderiv

/-- Exact integral form of the general-`m` entropy derivative field. -/
theorem intervalDomainMEntropyTimeDerivIntegrand_integral_eq
    (m : ℝ) (u : ℝ → intervalDomain.Point → ℝ) (uStar t : ℝ) :
    (∫ y in (0 : ℝ)..1,
      intervalDomainMEntropyTimeDerivIntegrand m u uStar t y) =
      intervalDomain.integral (fun x =>
        chemotaxisEntropyIntegrand m uStar (u t x) *
          intervalDomain.timeDeriv u t x) := by
  change _ = intervalDomainIntegral (fun x =>
    chemotaxisEntropyIntegrand m uStar (u t x) *
      intervalDomain.timeDeriv u t x)
  unfold intervalDomainIntegral
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le zero_le_one] at hy
  have hlift : ∀ r : ℝ, intervalDomainLift (u r) y = u r ⟨y, hy⟩ := by
    intro r
    simp [intervalDomainLift, hy]
  unfold intervalDomainMEntropyTimeDerivIntegrand
    ShenWork.Paper2.intervalDomainMassTimeDerivIntegrand
  rw [show (fun r : ℝ => intervalDomainLift (u r) y) =
    fun r => u r ⟨y, hy⟩ from funext hlift]
  have hright : intervalDomainLift (fun x =>
      chemotaxisEntropyIntegrand m uStar (u t x) *
        intervalDomain.timeDeriv u t x) y =
      chemotaxisEntropyIntegrand m uStar (u t ⟨y, hy⟩) *
        intervalDomain.timeDeriv u t ⟨y, hy⟩ := by
    simp [intervalDomainLift, hy]
  rw [hright, hlift t]
  rfl

/-- Unconditional general-`m` entropy time derivative for every positive
classical slice of the faithful equation. -/
theorem intervalDomainM_entropy_hasDerivAt
    {p : CM2Params} {T m uStar t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution intervalDomainM p T u v)
    (huStar : 0 < uStar) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun s => chemotaxisEntropyFunctional intervalDomain m uStar u s)
      (intervalDomain.integral (fun x =>
        chemotaxisEntropyIntegrand m uStar (u t x) *
          intervalDomain.timeDeriv u t x)) t := by
  obtain ⟨delta, hdelta, hball, hIcc⟩ :=
    ShenWork.Paper2.exists_closedSlab_subset ht
  have hreg : intervalDomainClassicalRegularity T u v := hsol.regularity
  have htimeJoint : ContinuousOn
      (Function.uncurry (ShenWork.Paper2.intervalDomainMassTimeDerivIntegrand u))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hreg.2.2.2.2.2.1.1
  have huJoint : ContinuousOn
      (Function.uncurry (fun (s : ℝ) (y : ℝ) => intervalDomainLift (u s) y))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hreg.2.2.2.2.2.2.1
  have hslabSet :
      Set.Icc (t - delta) (t + delta) ×ˢ Set.Icc (0 : ℝ) 1 ⊆
        Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 :=
    Set.prod_mono hIcc (le_refl _)
  have huSlab := huJoint.mono hslabSet
  have htimeSlab := htimeJoint.mono hslabSet
  have hpos : ∀ z ∈ Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1,
      0 < Function.uncurry
        (fun (s : ℝ) (y : ℝ) => intervalDomainLift (u s) y) z := by
    intro z hz
    have hlift : intervalDomainLift (u z.1) z.2 = u z.1 ⟨z.2, hz.2⟩ := by
      simp [intervalDomainLift, hz.2]
    change 0 < intervalDomainLift (u z.1) z.2
    rw [hlift]
    exact hsol.u_pos' hz.1.1 hz.1.2
  have hIntegrandCont : ContinuousOn
      (chemotaxisEntropyIntegrand m uStar) ({0}ᶜ : Set ℝ) := by
    intro z hz
    exact (chemotaxisEntropyIntegrand_continuousAt_of_ne
      (m := m) (uStar := uStar) huStar.ne' (by simpa using hz)).continuousWithinAt
  have hcompJoint : ContinuousOn
      (fun z : ℝ × ℝ =>
        chemotaxisEntropyIntegrand m uStar (intervalDomainLift (u z.1) z.2))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
    have hmaps : Set.MapsTo
        (Function.uncurry (fun (s : ℝ) (y : ℝ) => intervalDomainLift (u s) y))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) ({0}ᶜ : Set ℝ) := by
      intro z hz
      exact ne_of_gt (hpos z hz)
    exact ContinuousOn.comp (g := chemotaxisEntropyIntegrand m uStar)
      hIntegrandCont huJoint hmaps
  have hderivJoint : ContinuousOn
      (Function.uncurry (intervalDomainMEntropyTimeDerivIntegrand m u uStar))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
    have := hcompJoint.mul htimeJoint
    refine this.congr ?_
    intro z _hz
    rfl
  have hslab : ContinuousOn
      (Function.uncurry (intervalDomainMEntropyTimeDerivIntegrand m u uStar))
      (Set.Icc (t - delta) (t + delta) ×ˢ Set.Icc (0 : ℝ) 1) :=
    hderivJoint.mono hslabSet
  have huSlice : ContinuousOn (fun y => intervalDomainLift (u t) y)
      (Set.Icc (0 : ℝ) 1) :=
    ShenWork.Paper2.intervalDomain_continuousOn_timeSlice huJoint ht
  have huSlicePos : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (u t) y := by
    intro y hy
    simpa [intervalDomainLift, hy] using
      hsol.u_pos' (x := (⟨y, hy⟩ : intervalDomain.Point)) ht.1 ht.2
  have hdensityContinuous : ContinuousOn
      (fun z => chemotaxisEntropyDensity m uStar z) (Set.Ioi (0 : ℝ)) := by
    intro z hz
    exact (chemotaxisEntropyDensity_hasDerivAt
      huStar hz).continuousAt.continuousWithinAt
  have hFcont : ContinuousOn (intervalDomainMEntropyLiftIntegrand m u uStar t)
      (Set.Icc (0 : ℝ) 1) := by
    unfold intervalDomainMEntropyLiftIntegrand
    exact hdensityContinuous.comp huSlice (fun y hy => huSlicePos y hy)
  have hFint : IntervalIntegrable
      (intervalDomainMEntropyLiftIntegrand m u uStar t) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hFcont
  have hFmeas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (intervalDomainMEntropyLiftIntegrand m u uStar s)
        intervalDomainInteriorMeasure := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    have huslice := ShenWork.Paper2.intervalDomain_continuousOn_timeSlice huJoint hs
    have hposSlice : ∀ y ∈ Set.Icc (0 : ℝ) 1,
        0 < intervalDomainLift (u s) y := by
      intro y hy
      simpa [intervalDomainLift, hy] using
        hsol.u_pos' (x := (⟨y, hy⟩ : intervalDomain.Point)) hs.1 hs.2
    exact ((hdensityContinuous.comp huslice (fun y hy => hposSlice y hy)).mono
      Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hF'cont : ContinuousOn
      (intervalDomainMEntropyTimeDerivIntegrand m u uStar t)
      (Set.Icc (0 : ℝ) 1) :=
    ShenWork.Paper2.intervalDomain_continuousOn_timeSlice hderivJoint ht
  have hF'meas : AEStronglyMeasurable
      (intervalDomainMEntropyTimeDerivIntegrand m u uStar t)
      intervalDomainInteriorMeasure :=
    (hF'cont.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hderiv := intervalDomainM_entropy_hasDerivAt_of_slabContinuous
    hsol huStar hdelta hball hFmeas hFint hF'meas hslab
  rw [intervalDomainMEntropyTimeDerivIntegrand_integral_eq] at hderiv
  exact hderiv

#print axioms intervalDomainMEntropyLiftIntegrand_hasDerivAt_interior
#print axioms intervalDomainM_entropyFunctional_eq_lift_integral
#print axioms intervalDomainM_entropy_hasDerivAt

end

end ShenWork.Paper3
