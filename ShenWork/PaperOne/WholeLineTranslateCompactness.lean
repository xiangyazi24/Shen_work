import ShenWork.PaperOne.LocalUniformCompactness
import ShenWork.PaperOne.WholeLineWaveTrap
import ShenWork.PaperOne.WholeLineLongTimeStationary
import ShenWork.PaperOne.WholeLineLeftTail
import ShenWork.Paper1.WaveTrapProps

open Filter Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/-- Translates of a trapped profile are locally bounded once `0 ≤ U ≤ 1`, and
locally equicontinuous under the supplied parabolic modulus. -/
theorem translateFamily_locallyUniformlyBoundedEquicont
    {κ κt D : ℝ} {U : ℝ → ℝ} (shifts : ℕ → ℝ)
    (hU : U ∈ WaveTrap κ κt D) (hcont : Continuous U)
    (hequi : ∀ K : Set ℝ, IsCompact K →
      EquicontinuousOn (fun n x => U (x + shifts n)) K) :
    LocallyUniformlyBoundedEquicont (fun n x => U (x + shifts n)) where
  continuous := by
    intro n
    exact hcont.comp (continuous_id.add continuous_const)
  locally_bounded := by
    intro _K _hK
    refine ⟨1, ?_⟩
    intro n x _hx
    constructor
    · exact le_trans (by norm_num : (-1 : ℝ) ≤ 0)
        (waveTrap_mem_nonneg hU (x + shifts n))
    · exact waveTrap_mem_le_one hU (x + shifts n)
  equicontinuous_on_compacts := hequi

/-- Ascoli compactness for an arbitrary translated sequence of a fixed profile. -/
theorem translate_precompactness_of_equicontinuity
    {κ κt D : ℝ} {U : ℝ → ℝ} (shifts : ℕ → ℝ)
    (hU : U ∈ WaveTrap κ κt D) (hcont : Continuous U)
    (hequi : ∀ K : Set ℝ, IsCompact K →
      EquicontinuousOn (fun n x => U (x + shifts n)) K) :
    ∃ Ulim : C(ℝ, ℝ), ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      TendstoLocallyUniformly
        (fun n x => U (x + shifts (subseq n))) Ulim atTop :=
  exists_locallyUniform_convergent_subseq
    (translateFamily_locallyUniformlyBoundedEquicont
      shifts hU hcont hequi)

/-- A profile with the PaperOne lower barrier has a strictly positive finite
left limit. -/
theorem waveTrap_left_limit_pos
    {κ κt D L : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < κ) (hκt : κ < κt) (hD : 1 ≤ D)
    (hU : U ∈ WaveTrap κ κt D)
    (hlim : Tendsto U atBot (𝓝 L)) :
    0 < L := by
  let x0 : ℝ := ShenWork.Paper1.lowerBarrierXPlus κ κt D
  have hgap : 0 < κt - κ := sub_pos.mpr hκt
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hraw_pos :
      0 < ShenWork.Paper1.lowerBarrierRaw κ κt D x0 :=
    ShenWork.Paper1.lowerBarrierRaw_pos_at_xplus hκ hgap hDpos
  have hlower_pos : 0 < lowerBarrier κ κt D x0 := by
    exact lt_of_lt_of_le hraw_pos (le_max_right (0 : ℝ)
      (Real.exp (-κ * x0) - D * Real.exp (-κt * x0)))
  have hUx0 : 0 < U x0 := lt_of_lt_of_le hlower_pos ((hU.1 x0).1)
  have htail : ∀ᶠ x in atBot, U x0 ≤ U x := by
    refine eventually_atBot.2 ⟨x0, ?_⟩
    intro x hx
    exact hU.2 hx
  exact lt_of_lt_of_le hUx0 (ge_of_tendsto hlim htail)

/-- A constant self-frozen profile evaluates to the logistic reaction. -/
theorem frozenWaveOperator_const_self_eq_reaction
    (p : CMParams) (c : ℝ) {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    ShenWork.Paper1.frozenWaveOperator p c (fun _ : ℝ => L) (fun _ : ℝ => L) x =
      ShenWork.Paper1.reactionFun p.α L := by
  have hconst : IsCUnifBdd (fun _ : ℝ => L) :=
    ⟨continuous_const, ⟨|L|, by intro y; simp⟩⟩
  rw [ShenWork.Paper1.frozenWaveOperator_const_eq p hconst (fun _ => hL) x]
  rw [ShenWork.Paper1.frozenElliptic_const_eq p hL x]
  simp [ShenWork.Paper1.reactionFun]

/-- Left-shifts going to `-∞` inherit the left endpoint value pointwise. -/
theorem translated_pointwise_of_left_limit
    {U : ℝ → ℝ} {L : ℝ} {shifts : ℕ → ℝ}
    (hlim : Tendsto U atBot (𝓝 L))
    (hshifts : Tendsto shifts atTop atBot) :
    ∀ x : ℝ, Tendsto (fun n : ℕ => U (x + shifts n)) atTop (𝓝 L) := by
  intro x
  have hxshift : Tendsto (fun n : ℕ => x + shifts n) atTop atBot := by
    have hright := Filter.tendsto_atBot_add_const_right atTop x hshifts
    simpa [add_comm] using hright
  exact hlim.comp hxshift

/-- Passing a stationary frozen equation to a flat left endpoint leaves the
logistic reaction root.  This local copy avoids depending on older carried
frontier wrappers. -/
theorem reactionFun_root_of_stationary_flat_limit_clean
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ} {L : ℝ}
    (hlim : Tendsto U atBot (𝓝 L))
    (hstat : ∀ x, ShenWork.Paper1.frozenWaveOperator p c U U x = 0)
    (hflat : ShenWork.Paper1.FrozenStationaryFlatAtLeft p U) :
    ShenWork.Paper1.reactionFun p.α L = 0 := by
  have hα_nonneg : 0 ≤ p.α := le_trans zero_le_one p.hα
  have hpow :
      Tendsto (fun x => (U x) ^ p.α) atBot (𝓝 (L ^ p.α)) :=
    hlim.rpow_const (Or.inr hα_nonneg)
  have hreact :
      Tendsto (fun x => ShenWork.Paper1.reactionFun p.α (U x)) atBot
        (𝓝 (ShenWork.Paper1.reactionFun p.α L)) := by
    unfold ShenWork.Paper1.reactionFun
    exact hlim.mul (tendsto_const_nhds.sub hpow)
  have hsum :
      Tendsto
        (fun x =>
          iteratedDeriv 2 U x + c * deriv U x -
            p.χ *
              deriv
                (fun y => (U y) ^ p.m *
                  deriv (ShenWork.Paper1.frozenElliptic p U) y) x +
            ShenWork.Paper1.reactionFun p.α (U x))
        atBot (𝓝 (ShenWork.Paper1.reactionFun p.α L)) := by
    simpa using
      (((hflat.1.add (hflat.2.1.const_mul c)).add
        (hflat.2.2.const_mul (-p.χ))).add hreact)
  have hop :
      Tendsto (fun x => ShenWork.Paper1.frozenWaveOperator p c U U x) atBot
        (𝓝 (ShenWork.Paper1.reactionFun p.α L)) := by
    simpa [ShenWork.Paper1.frozenWaveOperator, ShenWork.Paper1.reactionFun,
      sub_eq_add_neg, mul_assoc] using hsum
  have hzero :
      Tendsto (fun x => ShenWork.Paper1.frozenWaveOperator p c U U x) atBot
        (𝓝 0) := by
    simp [hstat]
  exact tendsto_nhds_unique hop hzero

/--
The translate-compactness data consumed by the left-tail brick.  The Ascoli
subsequence is extracted from the derivative-bound equicontinuity; stationarity
of the constant limit is obtained from the existing stationary-flat endpoint
root lemma.
-/
def translate_compactness_of_equicontinuity
    {p : CMParams} {c κ κt D L : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < κ) (hκt : κ < κt) (hD : 1 ≤ D)
    (hU : U ∈ WaveTrap κ κt D) (hcont : Continuous U)
    (hequi : ∀ K : Set ℝ, IsCompact K →
      EquicontinuousOn (fun (n : ℕ) (x : ℝ) => U (x + (-(n : ℝ)))) K)
    (hlim : Tendsto U atBot (𝓝 L))
    (hstat : ∀ x, ShenWork.Paper1.frozenWaveOperator p c U U x = 0)
    (hflat : ShenWork.Paper1.FrozenStationaryFlatAtLeft p U) :
    ShenWork.Paper1.WholeLineLeftTail.TranslateCompactnessStationaryLimit
      p c U L := by
  let rawShifts : ℕ → ℝ := fun n => -((n : ℕ) : ℝ)
  have hcompact :
      ∃ Ulim : C(ℝ, ℝ), ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
        TendstoLocallyUniformly
          (fun n x => U (x + rawShifts (subseq n))) Ulim atTop :=
    translate_precompactness_of_equicontinuity
      (κ := κ) (κt := κt) (D := D) (U := U)
      rawShifts hU hcont (by
        intro K hK
        simpa [rawShifts] using hequi K hK)
  let UlimAA : C(ℝ, ℝ) := Classical.choose hcompact
  have hcompact_tail :
      ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
        TendstoLocallyUniformly
          (fun n x => U (x + rawShifts (subseq n))) UlimAA atTop :=
    Classical.choose_spec hcompact
  let subseq : ℕ → ℕ := Classical.choose hcompact_tail
  have hsubseq_and_AA :
      StrictMono subseq ∧
        TendstoLocallyUniformly
          (fun n x => U (x + rawShifts (subseq n))) UlimAA atTop :=
    Classical.choose_spec hcompact_tail
  have hsubseq : StrictMono subseq := hsubseq_and_AA.1
  let shifts : ℕ → ℝ := fun n => -((subseq n : ℕ) : ℝ)
  have hsubseq_atTop : Tendsto (fun n : ℕ => (subseq n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsubseq.tendsto_atTop
  have hshifts : Tendsto shifts atTop atBot := by
    change Tendsto (fun n : ℕ => -((subseq n : ℕ) : ℝ)) atTop atBot
    exact tendsto_neg_atTop_atBot.comp hsubseq_atTop
  have hLpos : 0 < L := waveTrap_left_limit_pos hκ hκt hD hU hlim
  have hroot : ShenWork.Paper1.reactionFun p.α L = 0 :=
    reactionFun_root_of_stationary_flat_limit_clean hlim hstat hflat
  refine
    { Ulim := fun _ => L
      shifts := shifts
      shifts_atBot := hshifts
      translated_pointwise := ?_
      constant_profile := ?_
      positive_profile := ?_
      stationary_profile := ?_ }
  · exact translated_pointwise_of_left_limit hlim hshifts
  · intro x
    rfl
  · intro x
    exact hLpos
  · intro x
    rw [frozenWaveOperator_const_self_eq_reaction p c hLpos.le x]
    exact hroot

/-- Named parabolic derivative convergence data used to turn a long-time
monotone limit into stationarity. -/
structure WholeLineParabolicDerivativeConvergence
    (w wt wx wxx : ℝ → ℝ → ℝ) (U : ℝ → ℝ) : Prop where
  time_derivative_tendsto_zero :
    ∀ x, Tendsto (fun t : ℝ => wt t x) atTop (𝓝 0)
  spatial_derivative_tendsto :
    ∀ x, Tendsto (fun t : ℝ => wx t x) atTop (𝓝 (deriv U x))
  spatial_second_derivative_tendsto :
    ∀ x, Tendsto (fun t : ℝ => wxx t x) atTop
      (𝓝 (iteratedDeriv 2 U x))

/-- Long-time stationarity data from monotone convergence plus the named
parabolic derivative-convergence package. -/
theorem longTime_stationarity_of_convergence
    {p : CMParams} {c κ κt D : ℝ}
    {w wt wx wxx : ℝ → ℝ → ℝ} {V Vx : ℝ → ℝ}
    (htime : ∀ x, Antitone fun t : ℝ => w t x)
    (hlower : ∀ t x, lowerBarrier κ κt D x ≤ w t x)
    (hderivConv :
      WholeLineParabolicDerivativeConvergence
        w wt wx wxx (wholeLineLongTimeLimit w))
    (hevolution :
      ∀ t x,
        wt t x =
          wxx t x + c * wx t x +
            auxiliaryFrozenNonlinearity p (w t) (wx t) V Vx x) :
    WholeLineLongTimeStationarityData p c w wt wx wxx
      (wholeLineLongTimeLimit w) V Vx where
  orbit_tendsto := wholeLine_longTime_limit_tendsto htime hlower
  time_derivative_tendsto_zero := hderivConv.time_derivative_tendsto_zero
  spatial_derivative_tendsto := hderivConv.spatial_derivative_tendsto
  spatial_second_derivative_tendsto :=
    hderivConv.spatial_second_derivative_tendsto
  evolution_eq := hevolution

#print axioms translateFamily_locallyUniformlyBoundedEquicont
#print axioms translate_precompactness_of_equicontinuity
#print axioms waveTrap_left_limit_pos
#print axioms frozenWaveOperator_const_self_eq_reaction
#print axioms translated_pointwise_of_left_limit
#print axioms translate_compactness_of_equicontinuity
#print axioms WholeLineParabolicDerivativeConvergence
#print axioms longTime_stationarity_of_convergence

end ShenWork.PaperOne
