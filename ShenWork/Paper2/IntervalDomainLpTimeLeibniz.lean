import ShenWork.Paper2.IntervalDomainL2HalfEnergyTimeLeibniz

open ShenWork.IntervalDomain MeasureTheory
open ShenWork.IntervalUnderIntegralLeibniz
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open scoped Topology

namespace ShenWork.Paper2

noncomputable section

open ShenWork.Paper2.IntervalDomainEnergyStep

def intervalDomainPowerEnergy
    (q : ℝ) (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1, (intervalDomainLift (u t) y) ^ q

def intervalDomainPowerDeriv
    (q : ℝ) (u : ℝ → intervalDomain.Point → ℝ) (t y : ℝ) : ℝ :=
  q * (intervalDomainLift (u t) y) ^ (q - 1) *
    deriv (fun r : ℝ => intervalDomainLift (u r) y) t

theorem intervalDomainPower_hasDerivAt_interior
    {p : CM2Params} {T q : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1)
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun r => (intervalDomainLift (u r) y) ^ q)
      (intervalDomainPowerDeriv q u s y) s := by
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
  set x : intervalDomain.Point := ⟨y, hyIcc⟩ with hx
  have hlift : ∀ r : ℝ, intervalDomainLift (u r) y = u r x := by
    intro r; simp [intervalDomainLift, hyIcc, hx]
  have hslice := intervalDomain_timeDeriv_isGenuine hsol (x := x) hy hs
  have hpow := hslice.rpow_const (p := q)
    (Or.inl (ne_of_gt (hsol.u_pos' hs.1 hs.2)))
  have hfun : (fun r : ℝ => (intervalDomainLift (u r) y) ^ q) =
      fun r : ℝ => (u r x) ^ q := by
    funext r; rw [hlift r]
  rw [hfun]
  unfold intervalDomainPowerDeriv
  rw [hlift s, show (fun r : ℝ => intervalDomainLift (u r) y) =
      (fun r : ℝ => u r x) from funext hlift]
  refine hpow.congr_deriv ?_
  change deriv (fun r : ℝ => u r x) s * q * u s x ^ (q - 1) =
    q * u s x ^ (q - 1) * deriv (fun r : ℝ => u r x) s
  ring

theorem intervalDomainPowerDeriv_continuousOn
    {p : CM2Params} {T q : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v) :
    ContinuousOn (Function.uncurry (intervalDomainPowerDeriv q u))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hU := hsol.regularity.2.2.2.2.2.2.1
  have hUt := hsol.regularity.2.2.2.2.2.1.1
  have hne : ∀ z ∈ Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u z.1) z.2 ≠ 0 := by
    intro z hz
    rcases Set.mem_prod.mp hz with ⟨ht, hx⟩
    let x : intervalDomain.Point := ⟨z.2, hx⟩
    have hpos : 0 < u z.1 x :=
      hsol.u_pos' (x := x) ht.1 ht.2
    exact ne_of_gt (by simpa [intervalDomainLift, hx] using hpos)
  have hpow := hU.rpow_const (p := q - 1) (fun z hz => Or.inl (hne z hz))
  have hconst : ContinuousOn (fun _ : ℝ × ℝ => q)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := continuousOn_const
  have hprod := hconst.mul (hpow.mul hUt)
  refine hprod.congr ?_
  intro z hz
  simp [intervalDomainPowerDeriv, Function.uncurry]
  ring

theorem intervalDomainPower_continuousOn_timeSlice
    {p : CM2Params} {T q t : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ContinuousOn (fun y => (intervalDomainLift (u t) y) ^ q)
      (Set.Icc (0 : ℝ) 1) := by
  have hU := intervalDomain_continuousOn_timeSlice
    hsol.regularity.2.2.2.2.2.2.1 ht
  exact hU.rpow_const (fun y hy => Or.inl (ne_of_gt (by
    let x : intervalDomain.Point := ⟨y, hy⟩
    have hpos : 0 < u t x := hsol.u_pos' (x := x) ht.1 ht.2
    simpa [intervalDomainLift, hy] using hpos)))

theorem intervalDomainPowerEnergy_hasDerivAt
    {p : CM2Params} {T q : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun s => intervalDomainPowerEnergy q u s)
      (∫ y in (0 : ℝ)..1, intervalDomainPowerDeriv q u t y) t := by
  obtain ⟨δ, hδ, hball, hIcc⟩ := exists_closedSlab_subset ht
  have hjoint := intervalDomainPowerDeriv_continuousOn (q := q) hsol
  have hslab := hjoint.mono (Set.prod_mono hIcc (le_refl _))
  have hslice := intervalDomain_continuousOn_timeSlice hjoint ht
  have hF'_meas : AEStronglyMeasurable
      (intervalDomainPowerDeriv q u t) intervalDomainInteriorMeasure :=
    (hslice.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hF_int : IntervalIntegrable
      (fun y => (intervalDomainLift (u t) y) ^ q) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (zero_le_one)]
    exact intervalDomainPower_continuousOn_timeSlice (q := q) hsol ht
  have hF_meas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (fun y => (intervalDomainLift (u s) y) ^ q)
        intervalDomainInteriorMeasure := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact ((intervalDomainPower_continuousOn_timeSlice (q := q) hsol hs).mono
      Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  obtain ⟨bound, hbound_int, h_bound⟩ :=
    exists_bound_of_continuousOn_slab hδ hslab
  have h_diff : ∀ᵐ y ∂intervalDomainInteriorMeasure,
      ∀ s ∈ Metric.ball t δ,
        HasDerivAt (fun r => (intervalDomainLift (u r) y) ^ q)
          (intervalDomainPowerDeriv q u s y) s := by
    refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
    exact Filter.Eventually.of_forall (fun y hy s hs =>
      intervalDomainPower_hasDerivAt_interior hsol hy (hball hs))
  exact intervalIntegral_hasDerivAt_time_of_local hδ hF_meas hF_int
    hF'_meas h_bound hbound_int h_diff

theorem intervalDomainPowerDeriv_integral_eq_timeTerm
    (q : ℝ) (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) :
    (∫ y in (0 : ℝ)..1, intervalDomainPowerDeriv q u t y) =
      intervalDomain.integral
        (fun x => q * (u t x) ^ (q - 1) * intervalDomain.timeDeriv u t x) := by
  change _ = intervalDomainIntegral _
  unfold intervalDomainIntegral
  refine intervalIntegral.integral_congr (fun y hy => ?_)
  rw [Set.uIcc_of_le (zero_le_one)] at hy
  have hlift : ∀ r : ℝ, intervalDomainLift (u r) y = u r ⟨y, hy⟩ := by
    intro r; simp [intervalDomainLift, hy]
  unfold intervalDomainPowerDeriv
  rw [hlift t, show (fun r : ℝ => intervalDomainLift (u r) y) =
      (fun r : ℝ => u r ⟨y, hy⟩) from funext hlift]
  simp [intervalDomain, intervalDomainLift, hy]

theorem intervalDomainPowerTimeTerm_interval_eq_domain
    (q : ℝ) (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) :
    (∫ y in (0 : ℝ)..1,
      q * (intervalDomainLift (u t) y) ^ (q - 1) *
        intervalDomainLift (intervalDomain.timeDeriv u t) y) =
      intervalDomain.integral
        (fun x => q * (u t x) ^ (q - 1) * intervalDomain.timeDeriv u t x) := by
  change _ = intervalDomainIntegral _
  unfold intervalDomainIntegral
  refine intervalIntegral.integral_congr (fun y hy => ?_)
  rw [Set.uIcc_of_le (zero_le_one)] at hy
  simp [intervalDomainLift, hy]

theorem intervalDomain_lp_timeLeibniz
    {p : CM2Params} {T q t : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    HasDerivAt (fun s => ∫ y in (0 : ℝ)..1,
        (intervalDomainLift (u s) y) ^ q)
      (intervalDomain.integral
        (fun x => q * (u t x) ^ (q - 1) * intervalDomain.timeDeriv u t x)) t := by
  simpa [intervalDomainPowerEnergy, intervalDomainPowerDeriv_integral_eq_timeTerm]
    using intervalDomainPowerEnergy_hasDerivAt (q := q) hsol ⟨ht0, htT⟩

theorem intervalDomain_lp_timeLeibniz_intervalIntegral
    {p : CM2Params} {T q t : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    HasDerivAt (fun s => ∫ y in (0 : ℝ)..1,
        (intervalDomainLift (u s) y) ^ q)
      (∫ y in (0 : ℝ)..1,
        q * (intervalDomainLift (u t) y) ^ (q - 1) *
          intervalDomainLift (intervalDomain.timeDeriv u t) y) t := by
  have h := intervalDomain_lp_timeLeibniz (q := q) hsol ht0 htT
  exact h.congr_deriv
    (intervalDomainPowerTimeTerm_interval_eq_domain q u t).symm

theorem intervalDomainLpEnergy_eq_powerEnergy_of_pos
    {q t : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hpos : ∀ x : intervalDomain.Point, 0 < u t x) :
    intervalDomainLpEnergy q u t = intervalDomainPowerEnergy q u t := by
  unfold intervalDomainLpEnergy intervalDomainPowerEnergy
  change intervalDomainIntegral (fun x => |u t x| ^ q) = _
  unfold intervalDomainIntegral
  refine intervalIntegral.integral_congr (fun y hy => ?_)
  rw [Set.uIcc_of_le (zero_le_one)] at hy
  simp [intervalDomainLift, hy, abs_of_pos (hpos ⟨y, hy⟩)]

theorem intervalDomainPowerTimeTerm_eq_scaled_weighted
    (q t : ℝ) (u : ℝ → intervalDomain.Point → ℝ)
    (hpos : ∀ x : intervalDomain.Point, 0 < u t x) :
    intervalDomain.integral
        (fun x => q * (u t x) ^ (q - 1) * intervalDomain.timeDeriv u t x) =
      q * intervalDomain.integral (intervalDomainLpEnergyWeightedTimeTerm q u t) := by
  change intervalDomainIntegral _ = q * intervalDomainIntegral _
  unfold intervalDomainIntegral
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun y hy => ?_)
  rw [Set.uIcc_of_le (zero_le_one)] at hy
  let x : intervalDomain.Point := ⟨y, hy⟩
  have hL : intervalDomainLift
      (fun z => q * (u t z) ^ (q - 1) * intervalDomain.timeDeriv u t z) y =
      q * (u t x) ^ (q - 1) * intervalDomain.timeDeriv u t x := by
    simp [intervalDomainLift, hy, x]
  have hR : intervalDomainLift (intervalDomainLpEnergyWeightedTimeTerm q u t) y =
      intervalDomainLpEnergyWeightedTimeTerm q u t x := by
    simp [intervalDomainLift, hy, x]
  have hpow : (u t x) ^ (q - 2) * u t x = (u t x) ^ (q - 1) := by
    calc
      (u t x) ^ (q - 2) * u t x
          = (u t x) ^ (q - 2) * (u t x) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
      _ = (u t x) ^ ((q - 2) + 1) := by
            rw [← Real.rpow_add (hpos x)]
      _ = (u t x) ^ (q - 1) := by ring_nf
  calc
    intervalDomainLift
        (fun z => q * (u t z) ^ (q - 1) * intervalDomain.timeDeriv u t z) y
        = q * (u t x) ^ (q - 1) * intervalDomain.timeDeriv u t x := hL
    _ = q * intervalDomainLpEnergyWeightedTimeTerm q u t x := by
        unfold intervalDomainLpEnergyWeightedTimeTerm
        rw [abs_of_pos (hpos x), ← hpow]
        ring
    _ = q * intervalDomainLift (intervalDomainLpEnergyWeightedTimeTerm q u t) y := by
        rw [hR]

theorem intervalDomain_lp_energy_hLpTime
    {p : CM2Params} {T q t : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    deriv (fun τ => intervalDomainLpEnergy q u τ) t =
      q * intervalDomain.integral (intervalDomainLpEnergyWeightedTimeTerm q u t) := by
  have hplain0 := intervalDomainPowerEnergy_hasDerivAt (q := q) hsol ⟨ht0, htT⟩
  have hplain : HasDerivAt (fun s => intervalDomainPowerEnergy q u s)
      (intervalDomain.integral
        (fun x => q * (u t x) ^ (q - 1) * intervalDomain.timeDeriv u t x)) t :=
    hplain0.congr_deriv (intervalDomainPowerDeriv_integral_eq_timeTerm q u t)
  have heq : (fun s => intervalDomainLpEnergy q u s) =ᶠ[𝓝 t]
      fun s => intervalDomainPowerEnergy q u s := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨ht0, htT⟩] with s hs
    exact intervalDomainLpEnergy_eq_powerEnergy_of_pos
      (q := q) (u := u) (t := s)
      (fun x => hsol.u_pos' (x := x) hs.1 hs.2)
  have habs := heq.hasDerivAt_iff.mpr hplain
  rw [habs.deriv]
  exact intervalDomainPowerTimeTerm_eq_scaled_weighted q t u
    (fun x => hsol.u_pos' (x := x) ht0 htT)

theorem intervalDomain_lp_energy_hLpTime_frontier
    {p : CM2Params} {T q : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v) :
    ∀ s, 0 < s → s < T →
      deriv (fun τ => intervalDomainLpEnergy q u τ) s =
        q * intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm q u s) := by
  intro s hs0 hsT
  exact intervalDomain_lp_energy_hLpTime (q := q) hsol hs0 hsT

end

end ShenWork.Paper2
