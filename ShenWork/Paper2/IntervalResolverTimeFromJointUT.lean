/-
  Direct time regularity of the elliptic resolver from a genuine jointly
  continuous time derivative of the parabolic component.

  This file deliberately avoids `DuhamelSourceTimeC1`, restart data, and any
  spectral-agreement hypothesis.  The only time-regularity input is an honest
  closed-space representative `ut` for the time derivative of `u`.
-/
import ShenWork.Paper2.IntervalResolverWeightedTimeSeries
import ShenWork.Paper2.IntervalDomainPositiveWindowK1OnEndpoint
import ShenWork.PDE.IntervalCoupledRegularityBootstrap

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.PDE
  (intervalNeumannResolverSourceCoeff intervalNeumannResolverCoeff
    intervalNeumannResolverWeight)
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemicalConcentration)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_abs_le_of_continuous_bounded
    cosineCoeffs_hasDerivAt_of_smooth_param)
open ShenWork.IntervalDomainPositiveWindowK1OnEndpoint
  (cosineCoeffs_continuousOn_of_jointContinuousOn_Icc)

noncomputable section

namespace ShenWork.Paper2

/-- The exact input needed to pass time regularity from `u` to its elliptic
resolver.  In particular, `hasTimeDeriv` is required at the two spatial
endpoints as well as in the interior. -/
structure ResolverTimeFromJointUTData
    (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) (ut : ℝ → ℝ → ℝ) : Prop where
  jointValue :
    ContinuousOn
      (Function.uncurry (fun t x => intervalDomainLift (u t) x))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)
  jointTimeDeriv :
    ContinuousOn (Function.uncurry ut)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)
  positive :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (u t) x
  hasTimeDeriv :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => intervalDomainLift (u s) x) (ut t x) t

/-- The physical power source of the elliptic equation. -/
def resolverPowerSource (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  p.ν * intervalDomainLift (u t) x ^ p.γ

/-- Its genuine chain-rule time derivative. -/
def resolverPowerSourceTimeDeriv (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (ut : ℝ → ℝ → ℝ)
    (t x : ℝ) : ℝ :=
  p.ν * p.γ * intervalDomainLift (u t) x ^ (p.γ - 1) * ut t x

/-- Cosine coefficients of the physical power source. -/
def resolverPowerSourceCoeff (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) (k : ℕ) : ℝ :=
  cosineCoeffs (resolverPowerSource p u t) k

/-- Cosine coefficients of the physical source time derivative. -/
def resolverPowerSourceTimeDerivCoeff (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (ut : ℝ → ℝ → ℝ)
    (t : ℝ) (k : ℕ) : ℝ :=
  cosineCoeffs (resolverPowerSourceTimeDeriv p u ut t) k

/-- The candidate time derivative of the elliptic resolver. -/
def resolverTimeDerivFromJointUT (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (ut : ℝ → ℝ → ℝ)
    (t x : ℝ) : ℝ :=
  ∑' k : ℕ, resolverPowerSourceTimeDerivCoeff p u ut t k *
    intervalNeumannResolverWeight p k * cosineMode k x

/-- The source coefficients stored by the concrete resolver are exactly the
cosine coefficients of `ν u^γ`. -/
theorem resolverSourceCoeff_re_eq_resolverPowerSourceCoeff
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) (k : ℕ) :
    (intervalNeumannResolverSourceCoeff p (u t) k).re =
      resolverPowerSourceCoeff p u t k := by
  simp [resolverPowerSourceCoeff, resolverPowerSource,
    intervalNeumannResolverSourceCoeff, cosineCoeffs]

/-- Closed-space series identity for the actual elliptic resolver. -/
theorem coupledChemicalConcentration_lift_eq_resolverPowerSeries
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (t : ℝ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalDomainLift (coupledChemicalConcentration p u t) x =
      ∑' k : ℕ, resolverPowerSourceCoeff p u t k *
        intervalNeumannResolverWeight p k * cosineMode k x := by
  let X : intervalDomainPoint := ⟨x, hx⟩
  have hR := ShenWork.IntervalResolverSpatialC2.resolverR_eq_cosineSeries
    (p := p) (u := u t) X
  simp only [coupledChemicalConcentration, intervalDomainLift, hx, dif_pos]
  rw [hR]
  apply tsum_congr
  intro k
  rw [ShenWork.IntervalResolverGradientBridge.resolverCoeff_re_eq]
  rw [resolverSourceCoeff_re_eq_resolverPowerSourceCoeff]
  simp [intervalNeumannResolverWeight, div_eq_mul_inv, X, mul_assoc]

/-- Joint continuity of the power source on the positive-time closed slab. -/
theorem ResolverTimeFromJointUTData.powerSource_jointContinuousOn
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    {ut : ℝ → ℝ → ℝ} (H : ResolverTimeFromJointUTData T u ut) :
    ContinuousOn (Function.uncurry (resolverPowerSource p u))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hpow : ContinuousOn
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2 ^ p.γ)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    H.jointValue.rpow_const (fun q hq => by
      obtain ⟨ht, hx⟩ := Set.mem_prod.mp hq
      exact Or.inl (ne_of_gt (H.positive q.1 ht q.2 hx)))
  simpa [resolverPowerSource, Function.uncurry] using
    continuousOn_const.mul hpow

/-- Joint continuity of the physical source derivative on the same slab. -/
theorem ResolverTimeFromJointUTData.powerSourceTimeDeriv_jointContinuousOn
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    {ut : ℝ → ℝ → ℝ} (H : ResolverTimeFromJointUTData T u ut) :
    ContinuousOn
      (Function.uncurry (resolverPowerSourceTimeDeriv p u ut))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hpow : ContinuousOn
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2 ^ (p.γ - 1))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    H.jointValue.rpow_const (fun q hq => by
      obtain ⟨ht, hx⟩ := Set.mem_prod.mp hq
      exact Or.inl (ne_of_gt (H.positive q.1 ht q.2 hx)))
  have hc : ContinuousOn (fun _ : ℝ × ℝ => p.ν * p.γ)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := continuousOn_const
  exact ((hc.mul hpow).mul H.jointTimeDeriv).congr (by
    intro q _hq
    rfl)

/-- Pointwise chain rule for the power source, including the two spatial
endpoints. -/
theorem ResolverTimeFromJointUTData.powerSource_hasDerivAt
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    {ut : ℝ → ℝ → ℝ} (H : ResolverTimeFromJointUTData T u ut)
    {t x : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun s : ℝ => resolverPowerSource p u s x)
      (resolverPowerSourceTimeDeriv p u ut t x) t := by
  have hpow := (H.hasTimeDeriv t ht x hx).rpow_const (p := p.γ)
    (Or.inl (ne_of_gt (H.positive t ht x hx)))
  have hmul := hpow.const_mul p.ν
  refine hmul.congr_deriv ?_
  simp [resolverPowerSourceTimeDeriv]
  ring

/-- A jointly continuous family on a compact time-space box has cosine
coefficients bounded uniformly in both time and mode. -/
private theorem exists_uniform_cosineCoeff_bound_on_timeIcc
    {f : ℝ → ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn (Function.uncurry f)
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)) :
    ∃ C, ∀ t ∈ Set.Icc a b, ∀ k : ℕ, |cosineCoeffs (f t) k| ≤ C := by
  classical
  let K : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1
  have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hfK : ContinuousOn (Function.uncurry f) K := hf
  obtain ⟨B, hB⟩ := hKcompact.bddAbove_image hfK.norm
  let B' : ℝ := max B 0
  have hB'nn : 0 ≤ B' := le_max_right B 0
  have hfb : ∀ t ∈ Set.Icc a b, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |f t x| ≤ B' := by
    intro t ht x hx
    have hmem : (t, x) ∈ K := Set.mem_prod.mpr ⟨ht, hx⟩
    have hraw : ‖Function.uncurry f (t, x)‖ ≤ B :=
      hB (Set.mem_image_of_mem _ hmem)
    simpa [K, B', Function.uncurry, Real.norm_eq_abs] using
      hraw.trans (le_max_left B 0)
  refine ⟨2 * B', ?_⟩
  intro t ht k
  have hsec : ContinuousOn (f t) (Set.Icc (0 : ℝ) 1) := by
    exact hfK.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x hx => Set.mem_prod.mpr ⟨ht, hx⟩)
  exact cosineCoeffs_abs_le_of_continuous_bounded hsec hB'nn
    (fun x hx => hfb t ht x hx) k

set_option maxHeartbeats 800000 in
/-- Local time differentiation of every power-source cosine coefficient. -/
theorem ResolverTimeFromJointUTData.powerSourceCoeff_hasDerivAt
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    {ut : ℝ → ℝ → ℝ} (H : ResolverTimeFromJointUTData T u ut)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) (k : ℕ) :
    HasDerivAt (fun s : ℝ => resolverPowerSourceCoeff p u s k)
      (resolverPowerSourceTimeDerivCoeff p u ut t k) t := by
  let δ : ℝ := min t (T - t) / 2
  have ht0 : 0 < t := ht.1
  have htT : 0 < T - t := sub_pos.mpr ht.2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδt : δ ≤ t / 2 := by
    dsimp [δ]
    gcongr
    exact min_le_left _ _
  have hδT : δ ≤ (T - t) / 2 := by
    dsimp [δ]
    gcongr
    exact min_le_right _ _
  have hball : Metric.ball t δ ⊆ Set.Ioo (0 : ℝ) T := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    constructor <;> linarith
  have hslab : Set.Icc (t - δ) (t + δ) ⊆ Set.Ioo (0 : ℝ) T := by
    intro s hs
    have hlo : 0 < t - δ := by linarith [hδt, ht0]
    have hhi : t + δ < T := by linarith [hδT, ht.2]
    exact ⟨hlo.trans_le hs.1, hs.2.trans_lt hhi⟩
  have hf_int : ∀ᶠ s in 𝓝 t,
      IntervalIntegrable (resolverPowerSource p u s) volume (0 : ℝ) 1 := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    have hsec : ContinuousOn (resolverPowerSource p u s)
        (Set.Icc (0 : ℝ) 1) := by
      exact H.powerSource_jointContinuousOn.comp
        (continuousOn_const.prodMk continuousOn_id)
        (fun x hx => Set.mem_prod.mpr ⟨hs, hx⟩)
    exact (hsec.mono (by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)])).intervalIntegrable
  have hdiff : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball t δ,
      HasDerivAt (fun r : ℝ => resolverPowerSource p u r x)
        (resolverPowerSourceTimeDeriv p u ut s x) s := by
    intro x hx s hs
    exact H.powerSource_hasDerivAt (hball hs) (Set.Ioo_subset_Icc_self hx)
  have hcont : ContinuousOn
      (Function.uncurry (resolverPowerSourceTimeDeriv p u ut))
      (Set.Icc (t - δ) (t + δ) ×ˢ Set.Icc (0 : ℝ) 1) :=
    H.powerSourceTimeDeriv_jointContinuousOn.mono (fun q hq =>
      Set.mem_prod.mpr ⟨hslab (Set.mem_prod.mp hq).1, (Set.mem_prod.mp hq).2⟩)
  exact cosineCoeffs_hasDerivAt_of_smooth_param
    (f := resolverPowerSource p u)
    (f' := resolverPowerSourceTimeDeriv p u ut)
    (τ := t) (δ := δ) (n := k) hδ hf_int hdiff hcont

/-- Each derivative coefficient is continuous on the whole positive-time
interval.  The proof is local on compact positive windows. -/
theorem ResolverTimeFromJointUTData.powerSourceTimeDerivCoeff_continuousOn
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    {ut : ℝ → ℝ → ℝ} (H : ResolverTimeFromJointUTData T u ut)
    (k : ℕ) :
    ContinuousOn (fun t : ℝ => resolverPowerSourceTimeDerivCoeff p u ut t k)
      (Set.Ioo (0 : ℝ) T) := by
  rw [isOpen_Ioo.continuousOn_iff]
  intro t ht
  let a : ℝ := t / 2
  let b : ℝ := (t + T) / 2
  have ha : 0 < a := by dsimp [a]; linarith [ht.1]
  have hat : a < t := by dsimp [a]; linarith [ht.1]
  have htb : t < b := by dsimp [b]; linarith [ht.2]
  have hbT : b < T := by dsimp [b]; linarith [ht.2]
  have hsub : Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1 ⊆
      Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 := by
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    exact ⟨⟨lt_of_lt_of_le ha hs.1, lt_of_le_of_lt hs.2 hbT⟩, hx⟩
  have hclosed := cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
    (f := resolverPowerSourceTimeDeriv p u ut) (c := a) (T := b) k
    (H.powerSourceTimeDeriv_jointContinuousOn.mono hsub)
  have hnhds : Set.Icc a b ∈ 𝓝 t := Icc_mem_nhds hat htb
  exact hclosed.continuousAt hnhds

/-- Uniform coefficient bounds on any compact positive time window. -/
theorem ResolverTimeFromJointUTData.exists_powerSourceCoeff_bounds_on_Icc
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    {ut : ℝ → ℝ → ℝ} (H : ResolverTimeFromJointUTData T u ut)
    {a b : ℝ} (ha : 0 < a) (hb : b < T) :
    ∃ A D,
      (∀ t ∈ Set.Icc a b, ∀ k : ℕ,
        |resolverPowerSourceCoeff p u t k| ≤ A) ∧
      (∀ t ∈ Set.Icc a b, ∀ k : ℕ,
        |resolverPowerSourceTimeDerivCoeff p u ut t k| ≤ D) := by
  have hsub : Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1 ⊆
      Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    exact ⟨⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩, hx⟩
  obtain ⟨A, hA⟩ := exists_uniform_cosineCoeff_bound_on_timeIcc
    (f := resolverPowerSource p u)
    (H.powerSource_jointContinuousOn.mono hsub)
  obtain ⟨D, hD⟩ := exists_uniform_cosineCoeff_bound_on_timeIcc
    (f := resolverPowerSourceTimeDeriv p u ut)
    (H.powerSourceTimeDeriv_jointContinuousOn.mono hsub)
  exact ⟨A, D, hA, hD⟩

set_option maxHeartbeats 800000 in
/-- The actual lifted elliptic resolver has the derivative represented by the
weighted cosine series of `ν γ u^(γ-1) ut`, at every closed-space point. -/
theorem ResolverTimeFromJointUTData.coupledChemical_lift_hasDerivAt
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    {ut : ℝ → ℝ → ℝ} (H : ResolverTimeFromJointUTData T u ut)
    {t x : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun s : ℝ => intervalDomainLift (coupledChemicalConcentration p u s) x)
      (resolverTimeDerivFromJointUT p u ut t x) t := by
  let a : ℝ := t / 2
  let b : ℝ := (t + T) / 2
  let I : Set ℝ := Set.Ioo a b
  have ha : 0 < a := by dsimp [a]; linarith [ht.1]
  have hat : a < t := by dsimp [a]; linarith [ht.1]
  have htb : t < b := by dsimp [b]; linarith [ht.2]
  have hbT : b < T := by dsimp [b]; linarith [ht.2]
  have htI : t ∈ I := ⟨hat, htb⟩
  obtain ⟨A, D, hA, hD⟩ :=
    H.exists_powerSourceCoeff_bounds_on_Icc (p := p) ha hbT
  have hcoeff : ∀ k s, s ∈ I →
      HasDerivAt (fun r : ℝ => resolverPowerSourceCoeff p u r k)
        (resolverPowerSourceTimeDerivCoeff p u ut s k) s := by
    intro k s hs
    have hsGlobal : s ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_of_lt_of_le ha hs.1.le, lt_of_le_of_lt hs.2.le hbT⟩
    exact H.powerSourceCoeff_hasDerivAt hsGlobal k
  have hseries : HasDerivAt
      (fun s : ℝ => ∑' k : ℕ, resolverPowerSourceCoeff p u s k *
        intervalNeumannResolverWeight p k * cosineMode k x)
      (resolverTimeDerivFromJointUT p u ut t x) t := by
    simpa [resolverTimeDerivFromJointUT] using
      (resolverWeightedCosineSeries_hasDerivAt_of_local_uniform
        p (I := I) (a := resolverPowerSourceCoeff p u)
        (adot := resolverPowerSourceTimeDerivCoeff p u ut)
        (A := A) (D := D)
        (by simpa [I] using isOpen_Ioo)
        (by simpa [I] using isPreconnected_Ioo)
        hcoeff
        (fun s hs k => hA s ⟨hs.1.le, hs.2.le⟩ k)
        (fun s hs k => hD s ⟨hs.1.le, hs.2.le⟩ k)
        htI x)
  have hfun :
      (fun s : ℝ => intervalDomainLift (coupledChemicalConcentration p u s) x) =
      (fun s : ℝ => ∑' k : ℕ, resolverPowerSourceCoeff p u s k *
        intervalNeumannResolverWeight p k * cosineMode k x) := by
    funext s
    exact coupledChemicalConcentration_lift_eq_resolverPowerSeries p u s hx
  rw [hfun]
  exact hseries

/-- On each compact positive time window, the resolver time-derivative
representative is jointly continuous up to the spatial endpoints. -/
theorem ResolverTimeFromJointUTData.resolverTimeDeriv_continuousOn_timeIcc
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    {ut : ℝ → ℝ → ℝ} (H : ResolverTimeFromJointUTData T u ut)
    {a b : ℝ} (ha : 0 < a) (hb : b < T) :
    ContinuousOn (Function.uncurry (resolverTimeDerivFromJointUT p u ut))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
  obtain ⟨A, D, hA, hD⟩ :=
    H.exists_powerSourceCoeff_bounds_on_Icc (p := p) ha hb
  have htimeSub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hcont : ∀ k, ContinuousOn
      (fun t : ℝ => resolverPowerSourceTimeDerivCoeff p u ut t k)
      (Set.Icc a b) := fun k =>
    (H.powerSourceTimeDerivCoeff_continuousOn (p := p) k).mono htimeSub
  simpa [resolverTimeDerivFromJointUT, Function.uncurry] using
    (resolverWeightedCosineSeries_continuousOn_prod_Icc
      p (I := Set.Icc a b)
      (a := resolverPowerSourceTimeDerivCoeff p u ut) (A := D)
      hcont hD)

/-- Global positive-time joint continuity of the explicit resolver derivative.
Only local compact bounds are used; no bound near time zero or the horizon is
assumed. -/
theorem ResolverTimeFromJointUTData.resolverTimeDeriv_jointContinuousOn
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    {ut : ℝ → ℝ → ℝ} (H : ResolverTimeFromJointUTData T u ut) :
    ContinuousOn (Function.uncurry (resolverTimeDerivFromJointUT p u ut))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  let S : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1
  change ContinuousOn (Function.uncurry (resolverTimeDerivFromJointUT p u ut)) S
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  let a : ℝ := t / 2
  let b : ℝ := (t + T) / 2
  let N : Set (ℝ × ℝ) := Set.Ioo a b ×ˢ Set.univ
  have ha : 0 < a := by dsimp [a]; linarith [ht.1]
  have hat : a < t := by dsimp [a]; linarith [ht.1]
  have htb : t < b := by dsimp [b]; linarith [ht.2]
  have hbT : b < T := by dsimp [b]; linarith [ht.2]
  have hlocal := H.resolverTimeDeriv_continuousOn_timeIcc
    (p := p) ha hbT
  have hqLocal : (t, x) ∈ Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1 :=
    ⟨⟨hat.le, htb.le⟩, hx⟩
  have hNnhds : N ∈ 𝓝 (t, x) := by
    exact (isOpen_Ioo.prod isOpen_univ).mem_nhds
      ⟨⟨hat, htb⟩, Set.mem_univ x⟩
  have hmem : S ∩ N ∈ nhdsWithin (t, x) S :=
    Filter.inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds hNnhds)
  refine ContinuousWithinAt.mono_of_mem_nhdsWithin ?_ hmem
  have hsub : S ∩ N ⊆ Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1 := by
    rintro ⟨s, y⟩ ⟨⟨hs, hy⟩, ⟨hsN, _⟩⟩
    exact ⟨⟨hsN.1.le, hsN.2.le⟩, hy⟩
  exact (hlocal (t, x) hqLocal).mono hsub

/-- Derivative-value form of the closed-space resolver differentiation
theorem. -/
theorem ResolverTimeFromJointUTData.coupledChemical_lift_timeDeriv_eq
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    {ut : ℝ → ℝ → ℝ} (H : ResolverTimeFromJointUTData T u ut)
    {t x : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    deriv
        (fun s : ℝ => intervalDomainLift (coupledChemicalConcentration p u s) x) t =
      resolverTimeDerivFromJointUT p u ut t x :=
  (H.coupledChemical_lift_hasDerivAt (p := p) ht hx).deriv

/-- Joint continuity of the literal `deriv` field of the actual elliptic
resolver on `Ioo 0 T × Icc 0 1`. -/
theorem ResolverTimeFromJointUTData.coupledChemical_timeDeriv_jointContinuousOn_closed
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    {ut : ℝ → ℝ → ℝ} (H : ResolverTimeFromJointUTData T u ut) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv
            (fun s : ℝ =>
              intervalDomainLift (coupledChemicalConcentration p u s) x) t))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  refine H.resolverTimeDeriv_jointContinuousOn (p := p) |>.congr ?_
  intro q hq
  obtain ⟨ht, hx⟩ := Set.mem_prod.mp hq
  simpa [Function.uncurry] using
    (H.coupledChemical_lift_timeDeriv_eq (p := p) ht hx)

/-- Open-space restriction of the preceding closed-slab theorem. -/
theorem ResolverTimeFromJointUTData.coupledChemical_timeDeriv_jointContinuousOn_interior
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    {ut : ℝ → ℝ → ℝ} (H : ResolverTimeFromJointUTData T u ut) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv
            (fun s : ℝ =>
              intervalDomainLift (coupledChemicalConcentration p u s) x) t))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Ioo (0 : ℝ) 1) :=
  (H.coupledChemical_timeDeriv_jointContinuousOn_closed (p := p)).mono
    (Set.prod_mono_right Set.Ioo_subset_Icc_self)

/-- Genuine time derivative of the subtype-valued resolver slice at every
closed-space point. -/
theorem ResolverTimeFromJointUTData.coupledChemical_hasDerivAt_time
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    {ut : ℝ → ℝ → ℝ} (H : ResolverTimeFromJointUTData T u ut)
    (X : intervalDomainPoint) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun s : ℝ => coupledChemicalConcentration p u s X)
      (resolverTimeDerivFromJointUT p u ut t X.1) t := by
  have h := H.coupledChemical_lift_hasDerivAt (p := p) ht X.2
  have hfun :
      (fun s : ℝ => intervalDomainLift (coupledChemicalConcentration p u s) X.1) =
      (fun s : ℝ => coupledChemicalConcentration p u s X) := by
    funext s
    simp [intervalDomainLift]
  rw [hfun] at h
  exact h

/-- Time differentiability of the actual resolver at every closed-space
point. -/
theorem ResolverTimeFromJointUTData.coupledChemical_differentiableAt_time
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    {ut : ℝ → ℝ → ℝ} (H : ResolverTimeFromJointUTData T u ut)
    (X : intervalDomainPoint) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    DifferentiableAt ℝ (fun s : ℝ => coupledChemicalConcentration p u s X) t :=
  (H.coupledChemical_hasDerivAt_time (p := p) X ht).differentiableAt

/-- For every fixed closed-space point, the actual resolver time derivative is
continuous on the full positive-time interval. -/
theorem ResolverTimeFromJointUTData.coupledChemical_timeDeriv_continuousOn_fixed_x
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    {ut : ℝ → ℝ → ℝ} (H : ResolverTimeFromJointUTData T u ut)
    (X : intervalDomainPoint) :
    ContinuousOn
      (fun t : ℝ => deriv
        (fun s : ℝ => coupledChemicalConcentration p u s X) t)
      (Set.Ioo (0 : ℝ) T) := by
  have hline : ContinuousOn
      (fun t : ℝ => deriv
        (fun s : ℝ =>
          intervalDomainLift (coupledChemicalConcentration p u s) X.1) t)
      (Set.Ioo (0 : ℝ) T) := by
    exact (H.coupledChemical_timeDeriv_jointContinuousOn_closed (p := p)).comp
      (continuousOn_id.prodMk continuousOn_const)
      (fun t ht => Set.mem_prod.mpr ⟨ht, X.2⟩)
  have hfun :
      (fun s : ℝ => intervalDomainLift (coupledChemicalConcentration p u s) X.1) =
      (fun s : ℝ => coupledChemicalConcentration p u s X) := by
    funext s
    simp [intervalDomainLift]
  rw [hfun] at hline
  exact hline

/-- The complete `v`-side time-slice field consumed by classical regularity. -/
theorem ResolverTimeFromJointUTData.coupledChemical_timeSlices
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    {ut : ℝ → ℝ → ℝ} (H : ResolverTimeFromJointUTData T u ut)
    (X : intervalDomainPoint) :
    (∀ t ∈ Set.Ioo (0 : ℝ) T,
      DifferentiableAt ℝ (fun s : ℝ => coupledChemicalConcentration p u s X) t) ∧
    ContinuousOn
      (fun t : ℝ => deriv
        (fun s : ℝ => coupledChemicalConcentration p u s X) t)
      (Set.Ioo (0 : ℝ) T) :=
  ⟨fun _ ht => H.coupledChemical_differentiableAt_time (p := p) X ht,
    H.coupledChemical_timeDeriv_continuousOn_fixed_x (p := p) X⟩

/-- One-shot package of exactly the three `v`-side time-regularity outputs:
time slices at every closed-space point, open-slab joint continuity, and
closed-slab joint continuity. -/
theorem ResolverTimeFromJointUTData.coupledChemical_timeRegularity
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    {ut : ℝ → ℝ → ℝ} (H : ResolverTimeFromJointUTData T u ut) :
    (∀ X : intervalDomainPoint,
      (∀ t ∈ Set.Ioo (0 : ℝ) T,
        DifferentiableAt ℝ
          (fun s : ℝ => coupledChemicalConcentration p u s X) t) ∧
      ContinuousOn
        (fun t : ℝ => deriv
          (fun s : ℝ => coupledChemicalConcentration p u s X) t)
        (Set.Ioo (0 : ℝ) T)) ∧
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv
            (fun s : ℝ =>
              intervalDomainLift (coupledChemicalConcentration p u s) x) t))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Ioo (0 : ℝ) 1) ∧
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv
            (fun s : ℝ =>
              intervalDomainLift (coupledChemicalConcentration p u s) x) t))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
  ⟨fun X => H.coupledChemical_timeSlices (p := p) X,
    H.coupledChemical_timeDeriv_jointContinuousOn_interior (p := p),
    H.coupledChemical_timeDeriv_jointContinuousOn_closed (p := p)⟩

section AxiomAudit

#print axioms ResolverTimeFromJointUTData.coupledChemical_lift_hasDerivAt
#print axioms ResolverTimeFromJointUTData.coupledChemical_timeDeriv_jointContinuousOn_closed
#print axioms ResolverTimeFromJointUTData.coupledChemical_timeSlices
#print axioms ResolverTimeFromJointUTData.coupledChemical_timeRegularity

end AxiomAudit

end ShenWork.Paper2
