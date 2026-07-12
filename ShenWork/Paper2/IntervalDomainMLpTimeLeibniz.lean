import ShenWork.Paper2.IntervalDomainLpTimeLeibniz

/-!
# Lp time Leibniz rule for the paper-faithful interval model

The time-chain-rule argument is kinematic: it uses only positive classical
regularity and is independent of the chemotaxis flux.  The legacy theorem is
typed at `intervalDomain`; this file transports the same proved argument to
`intervalDomainM`, whose flux contains the actual power `u ^ m`.
-/

open ShenWork.IntervalDomain MeasureTheory
open ShenWork.IntervalUnderIntegralLeibniz
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open scoped Topology

namespace ShenWork.Paper2.IntervalDomainM

noncomputable section

open ShenWork.Paper2.IntervalDomainEnergyStep

theorem u_pos
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (x : intervalDomain.Point) :
    0 < u t x :=
  hsol.2.2.1 t x ht0 htT

theorem timeDeriv_isGenuine
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    {x : intervalDomain.Point} (_hx : (x.1 : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun s : ℝ => u s x) (intervalDomain.timeDeriv u t x) t := by
  have hreg : intervalDomainClassicalRegularity T u v := hsol.regularity
  have hdiff : DifferentiableAt ℝ (fun s : ℝ => u s x) t :=
    (hreg.2.1 x t ht).1.1
  simpa [intervalDomain, intervalDomainClassicalRegularity] using hdiff.hasDerivAt

theorem power_hasDerivAt_interior
    {p : CM2Params} {T q : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1)
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun r => (intervalDomainLift (u r) y) ^ q)
      (intervalDomainPowerDeriv q u s y) s := by
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
  set x : intervalDomain.Point := ⟨y, hyIcc⟩ with hx
  have hlift : ∀ r : ℝ, intervalDomainLift (u r) y = u r x := by
    intro r
    simp [intervalDomainLift, hyIcc, hx]
  have hslice := timeDeriv_isGenuine hsol (x := x) hy hs
  have hpow := hslice.rpow_const (p := q)
    (Or.inl (ne_of_gt (u_pos hsol hs.1 hs.2 x)))
  have hfun : (fun r : ℝ => (intervalDomainLift (u r) y) ^ q) =
      fun r : ℝ => (u r x) ^ q := by
    funext r
    rw [hlift r]
  rw [hfun]
  unfold intervalDomainPowerDeriv
  rw [hlift s, show (fun r : ℝ => intervalDomainLift (u r) y) =
      (fun r : ℝ => u r x) from funext hlift]
  refine hpow.congr_deriv ?_
  change deriv (fun r : ℝ => u r x) s * q * u s x ^ (q - 1) =
    q * u s x ^ (q - 1) * deriv (fun r : ℝ => u r x) s
  ring

theorem powerDeriv_continuousOn
    {p : CM2Params} {T q : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v) :
    ContinuousOn (Function.uncurry (intervalDomainPowerDeriv q u))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hU := hsol.regularity.2.2.2.2.2.2.1
  have hUt := hsol.regularity.2.2.2.2.2.1.1
  have hne : ∀ z ∈ Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u z.1) z.2 ≠ 0 := by
    intro z hz
    rcases Set.mem_prod.mp hz with ⟨ht, hx⟩
    let x : intervalDomain.Point := ⟨z.2, hx⟩
    have hpos : 0 < u z.1 x := u_pos hsol ht.1 ht.2 x
    exact ne_of_gt (by simpa [intervalDomainLift, hx] using hpos)
  have hpow := hU.rpow_const (p := q - 1) (fun z hz => Or.inl (hne z hz))
  have hconst : ContinuousOn (fun _ : ℝ × ℝ => q)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := continuousOn_const
  have hprod := hconst.mul (hpow.mul hUt)
  refine hprod.congr ?_
  intro z hz
  simp [intervalDomainPowerDeriv, Function.uncurry]
  ring

theorem power_continuousOn_timeSlice
    {p : CM2Params} {T q t : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ContinuousOn (fun y => (intervalDomainLift (u t) y) ^ q)
      (Set.Icc (0 : ℝ) 1) := by
  have hU := intervalDomain_continuousOn_timeSlice
    hsol.regularity.2.2.2.2.2.2.1 ht
  exact hU.rpow_const (fun y hy => Or.inl (ne_of_gt (by
    let x : intervalDomain.Point := ⟨y, hy⟩
    have hpos : 0 < u t x := u_pos hsol ht.1 ht.2 x
    simpa [intervalDomainLift, hy] using hpos)))

theorem powerEnergy_hasDerivAt
    {p : CM2Params} {T q : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun s => intervalDomainPowerEnergy q u s)
      (∫ y in (0 : ℝ)..1, intervalDomainPowerDeriv q u t y) t := by
  obtain ⟨δ, hδ, hball, hIcc⟩ := exists_closedSlab_subset ht
  have hjoint := powerDeriv_continuousOn (q := q) hsol
  have hslab := hjoint.mono (Set.prod_mono hIcc (le_refl _))
  have hslice := intervalDomain_continuousOn_timeSlice hjoint ht
  have hF'_meas : AEStronglyMeasurable
      (intervalDomainPowerDeriv q u t) intervalDomainInteriorMeasure :=
    (hslice.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hF_int : IntervalIntegrable
      (fun y => (intervalDomainLift (u t) y) ^ q) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact power_continuousOn_timeSlice (q := q) hsol ht
  have hF_meas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (fun y => (intervalDomainLift (u s) y) ^ q)
        intervalDomainInteriorMeasure := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact ((power_continuousOn_timeSlice (q := q) hsol hs).mono
      Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  obtain ⟨bound, hbound_int, h_bound⟩ :=
    exists_bound_of_continuousOn_slab hδ hslab
  have h_diff : ∀ᵐ y ∂intervalDomainInteriorMeasure,
      ∀ s ∈ Metric.ball t δ,
        HasDerivAt (fun r => (intervalDomainLift (u r) y) ^ q)
          (intervalDomainPowerDeriv q u s y) s := by
    refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
    exact Filter.Eventually.of_forall (fun y hy s hs =>
      power_hasDerivAt_interior hsol hy (hball hs))
  exact intervalIntegral_hasDerivAt_time_of_local hδ hF_meas hF_int
    hF'_meas h_bound hbound_int h_diff

/-- The Lp time chain rule for a faithful `u ^ m` classical solution. -/
theorem lp_energy_hLpTime
    {p : CM2Params} {T q t : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    deriv (fun τ => intervalDomainLpEnergy q u τ) t =
      q * intervalDomain.integral
        (intervalDomainLpEnergyWeightedTimeTerm q u t) := by
  have hplain0 := powerEnergy_hasDerivAt (q := q) hsol ⟨ht0, htT⟩
  have hplain : HasDerivAt (fun s => intervalDomainPowerEnergy q u s)
      (intervalDomain.integral
        (fun x => q * (u t x) ^ (q - 1) * intervalDomain.timeDeriv u t x)) t :=
    hplain0.congr_deriv (intervalDomainPowerDeriv_integral_eq_timeTerm q u t)
  have heq : (fun s => intervalDomainLpEnergy q u s) =ᶠ[𝓝 t]
      fun s => intervalDomainPowerEnergy q u s := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨ht0, htT⟩] with s hs
    exact intervalDomainLpEnergy_eq_powerEnergy_of_pos
      (q := q) (u := u) (t := s)
      (fun x => u_pos hsol hs.1 hs.2 x)
  have habs := heq.hasDerivAt_iff.mpr hplain
  rw [habs.deriv]
  exact intervalDomainPowerTimeTerm_eq_scaled_weighted q t u
    (fun x => u_pos hsol ht0 htT x)

theorem lp_energy_hLpTime_frontier
    {p : CM2Params} {T q : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v) :
    ∀ s, 0 < s → s < T →
      deriv (fun τ => intervalDomainLpEnergy q u τ) s =
        q * intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm q u s) := by
  intro s hs0 hsT
  exact lp_energy_hLpTime (q := q) hsol hs0 hsT

end

end ShenWork.Paper2.IntervalDomainM
