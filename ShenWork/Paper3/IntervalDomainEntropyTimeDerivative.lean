import ShenWork.Paper3.IntervalDomainEntropyEllipticGradient
import ShenWork.Paper2.IntervalDomainMass

/-!
# Time differentiation of the Paper 3 entropy on the interval

For the implemented `m = 1` equation this file proves, directly from the
classical-solution regularity, the chain rule

`d/dt ∫ h₁(u) = ∫ (1 - uStar/u) u_t`.

The proof uses the same localized under-the-integral Leibniz theorem as the
mass and `L²` identities.  Positivity on a closed time slab supplies both the
`rpow`/division side conditions and the uniform integrable envelope.
-/

open ShenWork.IntervalDomain MeasureTheory
open ShenWork.IntervalUnderIntegralLeibniz
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open scoped Topology Interval

namespace ShenWork.Paper3

noncomputable section

/-- Lifted entropy density used by the interval Leibniz argument. -/
def intervalDomainEntropyLiftIntegrand
    (u : ℝ → intervalDomain.Point → ℝ) (uStar s y : ℝ) : ℝ :=
  chemotaxisEntropyDensity 1 uStar (intervalDomainLift (u s) y)

/-- Lifted derivative field for the `m = 1` entropy. -/
def intervalDomainEntropyTimeDerivIntegrand
    (u : ℝ → intervalDomain.Point → ℝ) (uStar s y : ℝ) : ℝ :=
  (1 - uStar / intervalDomainLift (u s) y) *
    ShenWork.Paper2.intervalDomainMassTimeDerivIntegrand u s y

theorem chemotaxisEntropyIntegrand_one
    {uStar s : ℝ} (_hs : 0 < s) :
    chemotaxisEntropyIntegrand 1 uStar s = 1 - uStar / s := by
  norm_num [chemotaxisEntropyIntegrand, Real.rpow_one]

/-- Pointwise scalar chain rule at an interior spatial point. -/
theorem intervalDomainEntropyLiftIntegrand_hasDerivAt_interior
    {p : CM2Params} {T uStar : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution intervalDomain p T u v)
    {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1)
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (huStar : 0 < uStar) :
    HasDerivAt
      (fun r => intervalDomainEntropyLiftIntegrand u uStar r y)
      (intervalDomainEntropyTimeDerivIntegrand u uStar s y) s := by
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
  let x : intervalDomain.Point := ⟨y, hyIcc⟩
  have hlift : ∀ r : ℝ, intervalDomainLift (u r) y = u r x := by
    intro r
    simp [intervalDomainLift, hyIcc, x]
  have huDeriv : HasDerivAt (fun r : ℝ => u r x)
      (intervalDomain.timeDeriv u s x) s :=
    ShenWork.Paper2.intervalDomain_timeDeriv_isGenuine hsol hy hs
  have huPos : 0 < u s x := hsol.u_pos' hs.1 hs.2
  have hchain := chemotaxisEntropyDensity_comp_hasDerivAt
    (m := (1 : ℝ)) huStar huPos huDeriv
  have hfun : (fun r => intervalDomainEntropyLiftIntegrand u uStar r y) =
      fun r => chemotaxisEntropyDensity 1 uStar (u r x) := by
    funext r
    simp [intervalDomainEntropyLiftIntegrand, hlift]
  have htime :
      ShenWork.Paper2.intervalDomainMassTimeDerivIntegrand u s y =
        intervalDomain.timeDeriv u s x := by
    unfold ShenWork.Paper2.intervalDomainMassTimeDerivIntegrand
    rw [show (fun r : ℝ => intervalDomainLift (u r) y) =
      fun r => u r x from funext hlift]
    rfl
  rw [hfun]
  simpa [intervalDomainEntropyTimeDerivIntegrand, hlift, htime,
    chemotaxisEntropyIntegrand_one huPos] using hchain

/-- The concrete entropy functional is the interval integral of the lifted
entropy density. -/
theorem intervalDomain_entropyFunctional_eq_lift_integral
    (u : ℝ → intervalDomain.Point → ℝ) (uStar t : ℝ) :
    chemotaxisEntropyFunctional intervalDomain 1 uStar u t =
      ∫ y in (0 : ℝ)..1, intervalDomainEntropyLiftIntegrand u uStar t y := by
  change intervalDomainIntegral
      (fun x => chemotaxisEntropyDensity 1 uStar (u t x)) = _
  unfold intervalDomainIntegral
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le zero_le_one] at hy
  simp [intervalDomainEntropyLiftIntegrand, intervalDomainLift, hy]

/-- Localized Leibniz theorem for the entropy functional. -/
theorem intervalDomain_entropy_hasDerivAt_of_slabContinuous
    {p : CM2Params} {T uStar t delta : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution intervalDomain p T u v)
    (huStar : 0 < uStar) (hdelta : 0 < delta)
    (hball : Metric.ball t delta ⊆ Set.Ioo (0 : ℝ) T)
    (hFmeas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (intervalDomainEntropyLiftIntegrand u uStar s)
        intervalDomainInteriorMeasure)
    (hFint : IntervalIntegrable
      (intervalDomainEntropyLiftIntegrand u uStar t) volume 0 1)
    (hF'meas : AEStronglyMeasurable
      (intervalDomainEntropyTimeDerivIntegrand u uStar t)
        intervalDomainInteriorMeasure)
    (hslab : ContinuousOn
      (Function.uncurry (intervalDomainEntropyTimeDerivIntegrand u uStar))
      (Set.Icc (t - delta) (t + delta) ×ˢ Set.Icc (0 : ℝ) 1)) :
    HasDerivAt
      (fun s => chemotaxisEntropyFunctional intervalDomain 1 uStar u s)
      (∫ y in (0 : ℝ)..1,
        intervalDomainEntropyTimeDerivIntegrand u uStar t y) t := by
  obtain ⟨bound, hboundInt, hbound⟩ :=
    exists_bound_of_continuousOn_slab hdelta hslab
  have hdiff : ∀ᵐ y ∂intervalDomainInteriorMeasure,
      ∀ s ∈ Metric.ball t delta,
        HasDerivAt
          (fun r => intervalDomainEntropyLiftIntegrand u uStar r y)
          (intervalDomainEntropyTimeDerivIntegrand u uStar s y) s := by
    refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
    exact Filter.Eventually.of_forall fun y hy s hs =>
      intervalDomainEntropyLiftIntegrand_hasDerivAt_interior
        hsol hy (hball hs) huStar
  have hderiv := intervalIntegral_hasDerivAt_time_of_local
    hdelta hFmeas hFint hF'meas hbound hboundInt hdiff
  have hfun :
      (fun s => chemotaxisEntropyFunctional intervalDomain 1 uStar u s) =
        fun s => ∫ y in (0 : ℝ)..1,
          intervalDomainEntropyLiftIntegrand u uStar s y := by
    funext s
    exact intervalDomain_entropyFunctional_eq_lift_integral u uStar s
  rw [hfun]
  exact hderiv

/-- Exact integral form of the entropy derivative field. -/
theorem intervalDomainEntropyTimeDerivIntegrand_integral_eq
    (u : ℝ → intervalDomain.Point → ℝ) (uStar t : ℝ) :
    (∫ y in (0 : ℝ)..1,
      intervalDomainEntropyTimeDerivIntegrand u uStar t y) =
      intervalDomain.integral (fun x =>
        (1 - uStar / u t x) * intervalDomain.timeDeriv u t x) := by
  change _ = intervalDomainIntegral (fun x =>
    (1 - uStar / u t x) * intervalDomain.timeDeriv u t x)
  unfold intervalDomainIntegral
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le zero_le_one] at hy
  have hlift : ∀ r : ℝ, intervalDomainLift (u r) y = u r ⟨y, hy⟩ := by
    intro r
    simp [intervalDomainLift, hy]
  unfold intervalDomainEntropyTimeDerivIntegrand
    ShenWork.Paper2.intervalDomainMassTimeDerivIntegrand
  rw [show (fun r : ℝ => intervalDomainLift (u r) y) =
    fun r => u r ⟨y, hy⟩ from funext hlift]
  have hright : intervalDomainLift (fun x =>
      (1 - uStar / u t x) * intervalDomain.timeDeriv u t x) y =
      (1 - uStar / u t ⟨y, hy⟩) *
        intervalDomain.timeDeriv u t ⟨y, hy⟩ := by
    simp [intervalDomainLift, hy]
  rw [hright, hlift t]
  rfl

/-- Unconditional entropy time derivative for every positive classical slice. -/
theorem intervalDomain_entropy_hasDerivAt
    {p : CM2Params} {T uStar t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution intervalDomain p T u v)
    (huStar : 0 < uStar) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun s => chemotaxisEntropyFunctional intervalDomain 1 uStar u s)
      (intervalDomain.integral (fun x =>
        (1 - uStar / u t x) * intervalDomain.timeDeriv u t x)) t := by
  obtain ⟨delta, hdelta, hball, hIcc⟩ :=
    ShenWork.Paper2.exists_closedSlab_subset ht
  have htimeJoint : ContinuousOn
      (Function.uncurry (ShenWork.Paper2.intervalDomainMassTimeDerivIntegrand u))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hsol.regularity.2.2.2.2.2.1.1
  have huJoint : ContinuousOn
      (Function.uncurry (fun (s : ℝ) (y : ℝ) => intervalDomainLift (u s) y))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hsol.regularity.2.2.2.2.2.2.1
  have hslabSet :
      Set.Icc (t - delta) (t + delta) ×ˢ Set.Icc (0 : ℝ) 1 ⊆
        Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 :=
    Set.prod_mono hIcc (le_refl _)
  have huSlab := huJoint.mono hslabSet
  have htimeSlab := htimeJoint.mono hslabSet
  have huSlabPos : ∀ z ∈
      Set.Icc (t - delta) (t + delta) ×ˢ Set.Icc (0 : ℝ) 1,
      0 < Function.uncurry
        (fun (s : ℝ) (y : ℝ) => intervalDomainLift (u s) y) z := by
    intro z hz
    have hzOpen := hslabSet hz
    have hlift : intervalDomainLift (u z.1) z.2 = u z.1 ⟨z.2, hz.2⟩ := by
      simp [intervalDomainLift, hz.2]
    change 0 < intervalDomainLift (u z.1) z.2
    rw [hlift]
    exact hsol.u_pos' hzOpen.1.1 hzOpen.1.2
  have hslab : ContinuousOn
      (Function.uncurry (intervalDomainEntropyTimeDerivIntegrand u uStar))
      (Set.Icc (t - delta) (t + delta) ×ˢ Set.Icc (0 : ℝ) 1) := by
    unfold intervalDomainEntropyTimeDerivIntegrand
    exact (continuousOn_const.sub
      (continuousOn_const.div huSlab
        (fun z hz => ne_of_gt (huSlabPos z hz)))).mul htimeSlab
  have huSlice : ContinuousOn (fun y => intervalDomainLift (u t) y)
      (Set.Icc (0 : ℝ) 1) :=
    ShenWork.Paper2.intervalDomain_continuousOn_timeSlice huJoint ht
  have huSlicePos : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (u t) y := by
    intro y hy
    simpa [intervalDomainLift, hy] using
      hsol.u_pos' (x := (⟨y, hy⟩ : intervalDomain.Point)) ht.1 ht.2
  have hdensityContinuous : ContinuousOn
      (fun z => chemotaxisEntropyDensity 1 uStar z) (Set.Ioi (0 : ℝ)) := by
    intro z hz
    exact (chemotaxisEntropyDensity_hasDerivAt huStar hz).continuousAt.continuousWithinAt
  have hFcont : ContinuousOn (intervalDomainEntropyLiftIntegrand u uStar t)
      (Set.Icc (0 : ℝ) 1) := by
    unfold intervalDomainEntropyLiftIntegrand
    exact hdensityContinuous.comp huSlice (fun y hy => huSlicePos y hy)
  have hFint : IntervalIntegrable
      (intervalDomainEntropyLiftIntegrand u uStar t) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hFcont
  have hFmeas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (intervalDomainEntropyLiftIntegrand u uStar s)
        intervalDomainInteriorMeasure := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    have huslice := ShenWork.Paper2.intervalDomain_continuousOn_timeSlice huJoint hs
    have hpos : ∀ y ∈ Set.Icc (0 : ℝ) 1,
        0 < intervalDomainLift (u s) y := by
      intro y hy
      simpa [intervalDomainLift, hy] using
        hsol.u_pos' (x := (⟨y, hy⟩ : intervalDomain.Point)) hs.1 hs.2
    exact ((hdensityContinuous.comp huslice (fun y hy => hpos y hy)).mono
      Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hF'cont : ContinuousOn
      (intervalDomainEntropyTimeDerivIntegrand u uStar t)
      (Set.Icc (0 : ℝ) 1) :=
    ShenWork.Paper2.intervalDomain_continuousOn_timeSlice
      (by
        unfold intervalDomainEntropyTimeDerivIntegrand
        exact (continuousOn_const.sub
          (continuousOn_const.div huJoint
            (fun z hz => by
              have hlift : intervalDomainLift (u z.1) z.2 =
                  u z.1 ⟨z.2, hz.2⟩ := by
                simp [intervalDomainLift, hz.2]
              change intervalDomainLift (u z.1) z.2 ≠ 0
              rw [hlift]
              exact ne_of_gt (hsol.u_pos' hz.1.1 hz.1.2)))).mul htimeJoint)
      ht
  have hF'meas : AEStronglyMeasurable
      (intervalDomainEntropyTimeDerivIntegrand u uStar t)
      intervalDomainInteriorMeasure :=
    (hF'cont.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hderiv := intervalDomain_entropy_hasDerivAt_of_slabContinuous
    hsol huStar hdelta hball hFmeas hFint hF'meas hslab
  rw [intervalDomainEntropyTimeDerivIntegrand_integral_eq] at hderiv
  exact hderiv

#print axioms chemotaxisEntropyIntegrand_one
#print axioms intervalDomainEntropyLiftIntegrand_hasDerivAt_interior
#print axioms intervalDomain_entropyFunctional_eq_lift_integral
#print axioms intervalDomain_entropy_hasDerivAt

end

end ShenWork.Paper3
