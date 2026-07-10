/-
  The genuinely decoupled zero-reaction branch of Paper 2 on the interval.

  The hypotheses `a = b = 0` alone do not make the equation a heat equation:
  the chemotaxis term remains when `chi_0 < 0`.  This file therefore treats the
  exact heat branch `chi_0 = a = b = 0` and keeps that restriction visible in
  every public theorem.

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.Paper2.IntervalHsupNormHeat
import ShenWork.Paper2.IntervalHeatLevel0SourceDecay
import ShenWork.Paper2.IntervalResolverSourceClampedWitness
import ShenWork.Paper2.IntervalPicardWindowAdot
import ShenWork.Paper2.IntervalPicardIterateInitialApproach
import ShenWork.Paper2.IntervalMildRegularityFrontierAssembly
import ShenWork.PDE.IntervalMildFrontierFromSpectral
import ShenWork.Paper2.IntervalResolverDirectTimeRegularity
import ShenWork.PDE.IntervalCoupledClassicalCorePAR
import ShenWork.PDE.IntervalCosineSliceRegularity

open Filter Topology Set MeasureTheory
open ShenWork.IntervalDomain
  (intervalDomain intervalDomainPoint intervalDomainLift intervalDomainSupNorm
   intervalDomainClassicalRegularity)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete (srcSlice srcSlice1)
open ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData (heatDu heatSemigroup_d0)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalResolverDirectTimeRegularity
  (HasResolverDirectSpectralData)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration)
open ShenWork.PDE (intervalNeumannResolverR intervalNeumannResolverSourceCoeff)

noncomputable section

namespace ShenWork.Paper2.ChiZeroZeroReactionHeat

/-- The heat trajectory, using the maintained level-zero Picard representation. -/
abbrev heatU (p : CM2Params) (u0 : intervalDomainPoint -> Real) :
    Real -> intervalDomainPoint -> Real :=
  conjugatePicardIter p u0 0

/-- The elliptic concentration attached to the heat trajectory. -/
abbrev heatV (p : CM2Params) (u0 : intervalDomainPoint -> Real) :
    Real -> intervalDomainPoint -> Real :=
  coupledChemicalConcentration p (heatU p u0)

/-- A bounded continuous interval datum has uniformly bounded cosine coefficients. -/
theorem exists_heatCoeff_bound
    {u0 : intervalDomainPoint -> Real}
    (hu0_adm : intervalDomain.initialAdmissible u0) :
    exists M : Real, 0 <= M /\
      forall k, |cosineCoeffs (intervalDomainLift u0) k| <= M := by
  obtain ⟨B, hB⟩ := hu0_adm.1
  let M := 2 * max B 0
  refine ⟨M, mul_nonneg (by norm_num) (le_max_right B 0), ?_⟩
  apply ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
  · have hu0_cont : Continuous u0 := hu0_adm.2
    rw [continuousOn_iff_continuous_restrict]
    have hrestrict :
        Set.restrict (Set.Icc (0 : Real) 1) (intervalDomainLift u0) = u0 := by
      ext ⟨x, hx⟩
      simp [Set.restrict, intervalDomainLift, hx]
    rw [hrestrict]
    exact hu0_cont
  · exact le_max_right B 0
  · intro x hx
    simp only [intervalDomainLift, hx, dif_pos]
    exact (hB (Set.mem_range_self (⟨x, hx⟩ : intervalDomainPoint))).trans
      (le_max_left B 0)

/-- The heat trajectory has the local restart spectral data used by the
time-regularity layer.  The restart source is identically zero. -/
theorem heatU_timeNeighborhoodSpectralAgreement
    (p : CM2Params) {u0 : intervalDomainPoint -> Real}
    (hu0_cont : Continuous u0) {M : Real} (hM : 0 <= M)
    (hu0_coeff : forall k, |cosineCoeffs (intervalDomainLift u0) k| <= M)
    (T : Real) :
    HasTimeNeighborhoodSpectralAgreement T (heatU p u0) := by
  refine ⟨?_⟩
  intro t0 ht0 _ht0T
  refine ⟨cosineCoeffs (intervalDomainLift u0), M, hM, hu0_coeff,
    (fun _ _ => (0 : Real)),
    ShenWork.IntervalPicardWindowAdot.zeroDuhamelSource, 0, by simpa, ?_⟩
  filter_upwards [Ioi_mem_nhds ht0] with s hs x
  have hagree := ShenWork.IntervalPicardIterateRepresentation.hagree_zero
    p u0 hs hu0_cont hu0_coeff x.2
  change heatU p u0 s x = _
  rw [show heatU p u0 s x = picardIter p u0 0 s x by rfl]
  rw [← show intervalDomainLift (picardIter p u0 0 s) x.1 =
      picardIter p u0 0 s x by simp [intervalDomainLift, x.2]]
  rw [hagree]
  congr 1
  funext n
  simp [localRestartCoeff,
    ShenWork.IntervalPicardIterateRepresentation.iterateReprCoeff,
    ShenWork.IntervalDuhamelClosedC2.duhamelSpectralCoeff]

private theorem heatDu_eq_secondValue
    {u0 : intervalDomainPoint -> Real} {t x : Real} (ht : 0 < t) :
    heatDu u0 t x =
      ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondValue
        t (cosineCoeffs (intervalDomainLift u0)) x := by
  simp only [heatDu, if_pos ht]
  simp only [ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianValue,
    ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondValue]
  congr 1
  funext n
  simp only [
    ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight,
    ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondPointWeight,
    ShenWork.IntervalDuhamelClosedC2.unitIntervalCosineHeatPointWeight,
    ShenWork.IntervalDuhamelClosedC2.unitIntervalCosineMode,
    ShenWork.IntervalDuhamelClosedC2.unitIntervalCosineEigenvalue]
  ring

/-- The elliptic concentration attached to the heat trajectory has the direct
resolver spectral package on every positive time horizon. -/
theorem heatV_resolverDirectSpectralData
    (p : CM2Params) {u0 : intervalDomainPoint -> Real}
    (hu0_cont : Continuous u0) (hu0_pos : forall x, 0 < u0 x)
    {M0 : Real} (hu0_coeff : forall k,
      |cosineCoeffs (intervalDomainLift u0) k| <= M0)
    (T : Real) :
    HasResolverDirectSpectralData T (heatV p u0) p := by
  have hfloor : forall t : Real, 0 < t -> forall x ∈ Set.Icc (0 : Real) 1,
      0 < intervalDomainLift (heatU p u0 t) x := by
    intro t ht x hx
    exact ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
      (p := p) hu0_cont hu0_pos ht hx
  apply ShenWork.Paper2.RegularityFrontierAssembly.hasResolverDirectSpectralData_of_clamped_perT0
    (T := T) (p := p) (heatU p u0)
  intro t0 ht0 _ht0T
  let c' : Real := t0 / 4
  let c : Real := t0 / 2
  let d : Real := 3 * t0 / 2
  let d' : Real := 2 * t0
  have hc'c : c' < c := by dsimp [c', c]; linarith
  have hcd : c <= d := by dsimp [c, d]; linarith
  have hdd' : d < d' := by dsimp [d, d']; linarith
  have hc'pos : 0 < c' := by dsimp [c']; linarith
  have ht0cd : t0 ∈ Set.Ioo c d := by
    dsimp [c, d]
    constructor <;> linarith
  let bc : Real -> Nat -> Real := fun s k =>
    ShenWork.IntervalPicardIterateRepresentation.iterateReprCoeff p u0 0 s k
  have hbsum : forall s ∈ Set.Icc c' d',
      Summable (fun n =>
        ShenWork.IntervalDuhamelClosedC2.unitIntervalCosineEigenvalue n * |bc s n|) := by
    intro s hs
    exact ShenWork.IntervalPicardIterateRepresentation.hbsum_zero
      p u0 (lt_of_lt_of_le hc'pos hs.1) hu0_coeff
  have hagree : forall s ∈ Set.Icc c' d',
      Set.EqOn (intervalDomainLift (heatU p u0 s))
        (fun x => ∑' n, bc s n * cosineMode n x) (Set.Icc (0 : Real) 1) := by
    intro s hs
    exact ShenWork.IntervalPicardIterateRepresentation.hagree_zero
      p u0 (lt_of_lt_of_le hc'pos hs.1) hu0_cont hu0_coeff
  have hpos : forall s ∈ Set.Icc c' d', forall x ∈ Set.Icc (0 : Real) 1,
      0 < intervalDomainLift (heatU p u0 s) x := by
    intro s hs x hx
    exact hfloor s (lt_of_lt_of_le hc'pos hs.1) x hx
  have hprofile : ContinuousOn
      (fun q : Real × Real => intervalDomainLift (heatU p u0 q.1) q.2)
      (Set.Icc c' d' ×ˢ Set.Icc (0 : Real) 1) := by
    simpa [heatU, Function.uncurry] using
      ShenWork.IntervalPicardLevel0SourceTimeC1On.heatSlice_profile_jointContinuousOn
        p hc'pos hu0_cont hu0_coeff
  have hsourceJoint : ContinuousOn
      (Function.uncurry (srcSlice p (heatU p u0)))
      (Set.Icc c' d' ×ˢ Set.Icc (0 : Real) 1) := by
    have hpow : ContinuousOn
        (fun q : Real × Real =>
          intervalDomainLift (heatU p u0 q.1) q.2 ^ p.γ)
        (Set.Icc c' d' ×ˢ Set.Icc (0 : Real) 1) := by
      refine hprofile.rpow_const ?_
      intro q hq
      obtain ⟨hs, hx⟩ := Set.mem_prod.mp hq
      exact Or.inl (ne_of_gt (hpos q.1 hs q.2 hx))
    simpa [srcSlice, Function.uncurry] using continuousOn_const.mul hpow
  let K : Set (Real × Real) := Set.Icc c' d' ×ˢ Set.Icc (0 : Real) 1
  have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hsourceK : ContinuousOn (Function.uncurry (srcSlice p (heatU p u0))) K :=
    hsourceJoint
  obtain ⟨B0, hB0⟩ := hKcompact.bddAbove_image hsourceK.norm
  let B0' : Real := max B0 0
  have hB0'nn : 0 <= B0' := le_max_right _ _
  have hsourceBound : forall s ∈ Set.Icc c' d', forall x ∈ Set.Icc (0 : Real) 1,
      |srcSlice p (heatU p u0) s x| <= B0' := by
    intro s hs x hx
    have hmem : (s, x) ∈ K := Set.mem_prod.mpr ⟨hs, hx⟩
    have hle : norm (Function.uncurry (srcSlice p (heatU p u0)) (s, x)) <= B0 :=
      hB0 (Set.mem_image_of_mem _ hmem)
    exact (by simpa [Function.uncurry, Real.norm_eq_abs] using hle).trans
      (le_max_left _ _)
  obtain ⟨C4, hC4nn, hC4⟩ :=
    ShenWork.Paper2.HeatLevel0SourceDecay.heatLevel0_srcSlice_quartic_decay_tail
      (p := p) (u₀ := u0) (M₀ := M0) hc'pos hu0_coeff hu0_cont hu0_pos
  let C : Real := max C4 (2 * B0')
  have hCnn : 0 <= C := hC4nn.trans (le_max_left _ _)
  have hdecay : forall s ∈ Set.Icc c' d', forall k : Nat, 1 <= k ->
      |cosineCoeffs (fun x => p.ν * intervalDomainLift (heatU p u0 s) x ^ p.γ) k|
        <= C / ((k : Real) * Real.pi) ^ 2 := by
    intro s hs k hk
    let z : Real := (k : Real) * Real.pi
    have hkReal : (1 : Real) <= k := by exact_mod_cast hk
    have hpi : (1 : Real) <= Real.pi := by linarith [Real.pi_gt_three]
    have hz : 1 <= z := one_le_mul_of_one_le_of_one_le hkReal hpi
    have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz
    have hpows : z ^ 2 <= z ^ 4 := by
      nlinarith [sq_nonneg z, sq_nonneg (z ^ 2 - 1)]
    calc
      |cosineCoeffs
          (fun x => p.ν * intervalDomainLift (heatU p u0 s) x ^ p.γ) k|
          <= C4 / z ^ 4 := by
            simpa [srcSlice, z] using hC4 s hs.1 k hk
      _ <= C / z ^ 4 := by gcongr; exact le_max_left _ _
      _ <= C / z ^ 2 := div_le_div_of_nonneg_left hCnn (pow_pos hzpos 2) hpows
  have ha0 : forall s ∈ Set.Icc c' d',
      |cosineCoeffs (fun x => p.ν * intervalDomainLift (heatU p u0 s) x ^ p.γ) 0|
        <= C := by
    intro s hs
    have hslice : ContinuousOn (srcSlice p (heatU p u0) s) (Set.Icc (0 : Real) 1) :=
      hsourceJoint.comp (continuousOn_const.prodMk continuousOn_id)
        (fun x hx => Set.mem_prod.mpr ⟨hs, hx⟩)
    have hcoeff :=
      ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
        hslice hB0'nn (hsourceBound s hs) 0
    exact (by simpa [srcSlice] using hcoeff).trans (le_max_right _ _)
  let adot : Real -> Nat -> Real := fun s k =>
    cosineCoeffs (srcSlice1 p (heatU p u0) (heatDu u0) s) k
  have hderiv : forall s ∈ Set.Icc c' d', forall n,
      HasDerivAt
        (fun r => cosineCoeffs
          (fun x => p.ν * intervalDomainLift (heatU p u0 r) x ^ p.γ) n)
        (adot s n) s := by
    intro s hs n
    have hspos : 0 < s := lt_of_lt_of_le hc'pos hs.1
    obtain ⟨delta, hdelta, hcont, hdiff, hjoint⟩ :=
      heatSemigroup_d0 hu0_coeff hu0_cont hfloor s hspos
    have hint : ∀ᶠ r in nhds s,
        IntervalIntegrable (srcSlice p (heatU p u0) r) volume (0 : Real) 1 :=
      hcont.mono fun r hr =>
        (Set.uIcc_of_le (by norm_num : (0 : Real) <= 1) ▸ hr).intervalIntegrable
    have hcoeff :=
      ShenWork.IntervalMildPicardRegularity.cosineCoeffs_hasDerivAt_of_smooth_param
        (f := srcSlice p (heatU p u0))
        (f' := srcSlice1 p (heatU p u0) (heatDu u0))
        (τ := s) (δ := delta) (n := n) hdelta hint hdiff hjoint
    simpa [srcSlice, adot] using hcoeff
  have hduJoint : ContinuousOn
      (fun q : Real × Real => heatDu u0 q.1 q.2)
      (Set.Icc c' d' ×ˢ Set.Icc (0 : Real) 1) := by
    have hsecond :=
      ShenWork.IntervalPicardLevel0SourceTimeC1On.heatSlice_secondValue_jointContinuousOn
        (u₀ := u0) hc'pos hu0_coeff
    exact hsecond.congr (fun q hq => by
      obtain ⟨hs, _hx⟩ := Set.mem_prod.mp hq
      simpa using heatDu_eq_secondValue (u0 := u0) (x := q.2)
        (lt_of_lt_of_le hc'pos hs.1))
  have hsrc1Joint : ContinuousOn
      (Function.uncurry (srcSlice1 p (heatU p u0) (heatDu u0)))
      (Set.Icc c' d' ×ˢ Set.Icc (0 : Real) 1) := by
    have hpow : ContinuousOn
        (fun q : Real × Real =>
          intervalDomainLift (heatU p u0 q.1) q.2 ^ (p.γ - 1))
        (Set.Icc c' d' ×ˢ Set.Icc (0 : Real) 1) := by
      refine hprofile.rpow_const ?_
      intro q hq
      obtain ⟨hs, hx⟩ := Set.mem_prod.mp hq
      exact Or.inl (ne_of_gt (hpos q.1 hs q.2 hx))
    simpa [srcSlice1, Function.uncurry] using
      ((continuousOn_const.mul continuousOn_const).mul hpow).mul hduJoint
  have hadotcont : forall n, ContinuousOn (fun s => adot s n) (Set.Icc c' d') := by
    intro n
    exact ShenWork.IntervalDomainPositiveWindowK1OnEndpoint.cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
      (f := srcSlice1 p (heatU p u0) (heatDu u0)) (c := c') (T := d') n hsrc1Joint
  have hsrc1K : ContinuousOn
      (Function.uncurry (srcSlice1 p (heatU p u0) (heatDu u0))) K := hsrc1Joint
  obtain ⟨B1, hB1⟩ := hKcompact.bddAbove_image hsrc1K.norm
  let B1' : Real := max B1 0
  have hB1'nn : 0 <= B1' := le_max_right _ _
  have hsrc1Bound : forall s ∈ Set.Icc c' d', forall x ∈ Set.Icc (0 : Real) 1,
      |srcSlice1 p (heatU p u0) (heatDu u0) s x| <= B1' := by
    intro s hs x hx
    have hmem : (s, x) ∈ K := Set.mem_prod.mpr ⟨hs, hx⟩
    have hle : norm (Function.uncurry
        (srcSlice1 p (heatU p u0) (heatDu u0)) (s, x)) <= B1 :=
      hB1 (Set.mem_image_of_mem _ hmem)
    exact (by simpa [Function.uncurry, Real.norm_eq_abs] using hle).trans
      (le_max_left _ _)
  have hMdot : forall s ∈ Set.Icc c' d', forall n, |adot s n| <= 2 * B1' := by
    intro s hs n
    have hslice : ContinuousOn
        (srcSlice1 p (heatU p u0) (heatDu u0) s) (Set.Icc (0 : Real) 1) :=
      hsrc1Joint.comp (continuousOn_const.prodMk continuousOn_id)
        (fun x hx => Set.mem_prod.mpr ⟨hs, hx⟩)
    exact ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
      hslice hB1'nn (hsrc1Bound s hs) n
  let aC : Real -> Nat -> Real := fun s k =>
    (intervalNeumannResolverSourceCoeff p
      (heatU p u0 (ShenWork.IntervalTimeSoftClamp.φ c' c d d' ((0 : Real) + s))) k).re
  let src : DuhamelSourceTimeC1 aC :=
    ShenWork.Paper2.ResolverSourceClampedWitness.clampedResolverSource_duhamelSourceTimeC1
      p (heatU p u0) (τ := 0) hc'c hcd hdd' bc hbsum hagree hpos
        hCnn hdecay ha0 adot hderiv hadotcont hMdot
  refine ⟨aC, src, Set.Ioo c d, isOpen_Ioo.mem_nhds ht0cd, ?_⟩
  intro s hs k
  have hsIcc : (0 : Real) + s ∈ Set.Icc c d :=
    ⟨by simpa using le_of_lt hs.1, by simpa using le_of_lt hs.2⟩
  simpa [aC] using
    ShenWork.Paper2.ResolverSourceClampedWitness.clampedResolverFamily_eq_on
      p (heatU p u0) (τ := 0) hc'c hdd' hsIcc k

#print axioms exists_heatCoeff_bound
#print axioms heatU_timeNeighborhoodSpectralAgreement
#print axioms heatV_resolverDirectSpectralData

end ShenWork.Paper2.ChiZeroZeroReactionHeat
