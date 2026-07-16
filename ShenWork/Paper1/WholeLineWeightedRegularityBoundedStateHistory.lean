import ShenWork.Paper1.WholeLineWeightedRegularitySemigroupHistoryNatural

open Filter MeasureTheory Set Topology
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Measurable bounded-state heat histories

The terminal weighted-heat history does not require continuity of its
`L²` datum trajectory.  Almost-everywhere strong measurability is enough:
simple datum histories give measurable heat histories by linearity, and the
general case follows by pointwise simple-function approximation.
-/

/-- A strongly measurable `L²` datum trajectory has a strongly measurable
terminal weighted-heat history on every compact time interval. -/
theorem weightedMovingHeatL2Semigroup_terminal_history_aestronglyMeasurable_of_stronglyMeasurable
    {eta c tau a r : ℝ} {G : ℝ → WholeLineRealL2}
    (hG : StronglyMeasurable G) :
    AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Semigroup eta c (tau - q) (G q))
      (volume.restrict (Set.Icc a r)) := by
  induction G, hG using StronglyMeasurable.induction with
  | ind Z hs =>
      have hbase : AEStronglyMeasurable
          (fun q => weightedMovingHeatL2Semigroup eta c (tau - q) Z)
          (volume.restrict (Set.Icc a r)) :=
        (weightedMovingHeatL2Semigroup_terminal_history_aestronglyMeasurable
          (eta := eta) (c := c) (tau := tau)
          (F := fun _ : ℝ => Z) continuous_const).mono_measure
            Measure.restrict_le_self
      have hind := hbase.indicator hs
      exact hind.congr (Eventually.of_forall fun q => by
        simp only [Set.indicator]
        split
        · rfl
        · exact (map_zero
            (weightedMovingHeatL2Semigroup eta c (tau - q))).symm)
  | add hF hG hFG hdis ihF ihG =>
      exact (ihF.add ihG).congr (Eventually.of_forall fun q => by
        simp only [Pi.add_apply, map_add])
  | lim hF hG ih hlim =>
      apply aestronglyMeasurable_of_tendsto_ae atTop ih
      exact Eventually.of_forall fun q => by
        simpa only [Function.comp_apply] using
          Filter.Tendsto.comp
            ((weightedMovingHeatL2Semigroup eta c (tau - q)).continuous.tendsto
              _) (hlim q)

/-- An almost-everywhere strongly measurable `L²` datum trajectory has a
measurable terminal weighted-heat history.  This is the continuity-free
history interface used by bounded restart arguments. -/
theorem weightedMovingHeatL2Semigroup_terminal_history_aestronglyMeasurable_of_aestronglyMeasurable
    {eta c tau a r : ℝ} {G : ℝ → WholeLineRealL2}
    (hG : AEStronglyMeasurable G volume) :
    AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Semigroup eta c (tau - q) (G q))
      (volume.restrict (Set.Icc a r)) := by
  let Gm : ℝ → WholeLineRealL2 := hG.mk G
  have hm : AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Semigroup eta c (tau - q) (Gm q))
      (volume.restrict (Set.Icc a r)) :=
    weightedMovingHeatL2Semigroup_terminal_history_aestronglyMeasurable_of_stronglyMeasurable
      (eta := eta) (c := c) (tau := tau) (a := a) (r := r)
      hG.stronglyMeasurable_mk
  apply hm.congr
  filter_upwards [hG.ae_eq_mk.filter_mono ae_restrict_le]
    with q hq
  rw [show Gm q = G q by simpa only [Gm] using hq.symm]

/-- Joint measurability of a scalar source gives strong measurability of its
weighted-heat history.  This is the scalar product-space companion to the
preceding Hilbert-valued history theorem. -/
theorem weightedMovingHeatEta_history_stronglyMeasurable_of_joint_measurable_bounded
    {eta c tau : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) :
    StronglyMeasurable
      (fun z : ℝ × ℝ =>
        weightedMovingHeatEta eta c (tau - z.1) (f z.1) z.2) := by
  let raw : (ℝ × ℝ) × ℝ → ℝ := fun z =>
    weightedMovingHeatMarkovKernel eta c (tau - z.1.1) z.1.2 z.2 *
      f z.1.1 z.2
  have hraw : StronglyMeasurable raw := by
    apply Measurable.stronglyMeasurable
    dsimp only [raw, weightedMovingHeatMarkovKernel, heatKernel]
    fun_prop
  have hint : StronglyMeasurable
      (fun z : ℝ × ℝ => ∫ y : ℝ, raw (z, y)) :=
    hraw.integral_prod_right'
  have hgrowth : Continuous (fun z : ℝ × ℝ =>
      weightedMovingHeatGrowth eta c (tau - z.1)) := by
    dsimp only [weightedMovingHeatGrowth]
    fun_prop
  have hprod := hgrowth.stronglyMeasurable.mul hint
  simpa only [raw, weightedMovingHeatEta] using hprod

/-- Bounded jointly measurable scalar representatives provide all history
data needed by a compact-window restart.  The only Hilbert-valued hypothesis
is almost-everywhere strong measurability of the two datum trajectories; no
time continuity is required.

Besides the terminal Hilbert history and its damped interval integrability,
the result records the local scalar product-integrability supplied by the
uniform-square restart-data theorem. -/
theorem weightedMovingHeat_boundedState_history_data
    {eta c a r Cz Cf : ℝ} (_har : a ≤ r)
    (hCz : 0 ≤ Cz) (hCf : 0 ≤ Cf)
    {z f : ℝ → ℝ → ℝ} {Z F : ℝ → WholeLineRealL2}
    (hz_joint : Measurable (Function.uncurry z))
    (hf_joint : Measurable (Function.uncurry f))
    (hz_sq : ∀ q ∈ Set.Icc a r,
      Integrable (fun x : ℝ => z q x ^ 2) volume)
    (hf_sq : ∀ q ∈ Set.Icc a r,
      Integrable (fun x : ℝ => f q x ^ 2) volume)
    (hz_le : ∀ q ∈ Set.Icc a r,
      (∫ x : ℝ, z q x ^ 2) ≤ Cz)
    (hf_le : ∀ q ∈ Set.Icc a r,
      (∫ x : ℝ, f q x ^ 2) ≤ Cf)
    (hZrep : ∀ q ∈ Set.Icc a r,
      (((Z q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] z q))
    (hFrep : ∀ q ∈ Set.Icc a r,
      (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] f q))
    (hZtime : AEStronglyMeasurable Z volume)
    (hFtime : AEStronglyMeasurable F volume) :
    ∀ t ∈ Set.Icc a r,
      AEStronglyMeasurable
          (fun q => weightedMovingHeatL2Semigroup eta c (t - q)
            (Z q + F q))
          (volume.restrict (Set.Icc a t)) ∧
        IntervalIntegrable
          (fun q => Real.exp (-(t - q)) •
            weightedMovingHeatL2Semigroup eta c (t - q) (Z q + F q))
          volume a t ∧
        ∀ A : Set ℝ, MeasurableSet A →
          (volume : Measure ℝ) A < ⊤ →
          Integrable
            (fun w : ℝ × ℝ => A.indicator
              (weightedMovingHeatEta eta c (t - w.1)
                (fun x => z w.1 x + f w.1 x)) w.2)
            ((volume.restrict (Set.Ioc a t)).prod volume) := by
  have hz_meas : ∀ q : ℝ, AEStronglyMeasurable (z q) volume := by
    intro q
    exact hz_joint.of_uncurry_left.aestronglyMeasurable
  have hf_meas : ∀ q : ℝ, AEStronglyMeasurable (f q) volume := by
    intro q
    exact hf_joint.of_uncurry_left.aestronglyMeasurable
  have hZeq : ∀ q ∈ Set.Icc a r,
      Z q = wholeLineRealL2Total (z q) := by
    intro q hq
    apply Lp.ext
    filter_upwards [hZrep q hq,
        wholeLineRealL2Total_coe_ae (z q) (hz_meas q) (hz_sq q hq)]
      with x hZx htx
    rw [hZx, htx]
  have hFeq : ∀ q ∈ Set.Icc a r,
      F q = wholeLineRealL2Total (f q) := by
    intro q hq
    apply Lp.ext
    filter_upwards [hFrep q hq,
        wholeLineRealL2Total_coe_ae (f q) (hf_meas q) (hf_sq q hq)]
      with x hFx htx
    rw [hFx, htx]
  let K : ℝ := Real.sqrt Cz + Real.sqrt Cf
  have hK : 0 ≤ K := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hGbound : ∀ q ∈ Set.Icc a r, ‖Z q + F q‖ ≤ K := by
    intro q hq
    calc
      ‖Z q + F q‖ ≤ ‖Z q‖ + ‖F q‖ := norm_add_le _ _
      _ ≤ Real.sqrt Cz + Real.sqrt Cf := by
        gcongr
        · rw [hZeq q hq]
          exact wholeLineRealL2Total_norm_le_sqrt_of_integral_sq_le
            hCz (hz_meas q) (hz_sq q hq) (hz_le q hq)
        · rw [hFeq q hq]
          exact wholeLineRealL2Total_norm_le_sqrt_of_integral_sq_le
            hCf (hf_meas q) (hf_sq q hq) (hf_le q hq)
      _ = K := rfl
  let g : ℝ → ℝ → ℝ := fun q x => z q x + f q x
  have hg_joint : Measurable (Function.uncurry g) := by
    exact hz_joint.add hf_joint
  have hg_meas : ∀ q ∈ Set.Icc a r,
      AEStronglyMeasurable (g q) volume := by
    intro q hq
    exact (hz_meas q).add (hf_meas q)
  have hg_sq : ∀ q ∈ Set.Icc a r,
      Integrable (fun x : ℝ => g q x ^ 2) volume := by
    intro q hq
    have hzLp : MemLp (z q) 2 volume :=
      (memLp_two_iff_integrable_sq (hz_meas q)).2 (hz_sq q hq)
    have hfLp : MemLp (f q) 2 volume :=
      (memLp_two_iff_integrable_sq (hf_meas q)).2 (hf_sq q hq)
    exact (memLp_two_iff_integrable_sq (hg_meas q hq)).1 (hzLp.add hfLp)
  have htotal : ∀ q ∈ Set.Icc a r,
      wholeLineRealL2Total (g q) = Z q + F q := by
    intro q hq
    apply Lp.ext
    filter_upwards [wholeLineRealL2Total_coe_ae _ (hg_meas q hq)
        (hg_sq q hq), Lp.coeFn_add (Z q) (F q), hZrep q hq, hFrep q hq]
      with x htx hadd hzx hfx
    rw [htx, hadd]
    simp only [g, Pi.add_apply]
    rw [hzx, hfx]
  have hGtime : AEStronglyMeasurable (fun q => Z q + F q) volume :=
    hZtime.add hFtime
  intro t ht
  have hhist : AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Semigroup eta c (t - q) (Z q + F q))
      (volume.restrict (Set.Icc a t)) :=
    weightedMovingHeatL2Semigroup_terminal_history_aestronglyMeasurable_of_aestronglyMeasurable
      (eta := eta) (c := c) (tau := t) (a := a) (r := t) hGtime
  have hg_le : ∀ q ∈ Set.Icc a t,
      (∫ x : ℝ, g q x ^ 2) ≤ K ^ 2 := by
    intro q hq
    have hqR : q ∈ Set.Icc a r := ⟨hq.1, hq.2.trans ht.2⟩
    rw [← wholeLineRealL2Total_norm_sq_eq_integral
      (hg_meas q hqR) (hg_sq q hqR), htotal q hqR]
    exact (sq_le_sq₀ (norm_nonneg _) hK).2 (hGbound q hqR)
  have hhistTotal : AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Semigroup eta c (t - q)
        (wholeLineRealL2Total (g q)))
      (volume.restrict (Set.Icc a t)) := by
    apply hhist.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with q hq
    rw [htotal q ⟨hq.1, hq.2.trans ht.2⟩]
  have hjointHeat : AEStronglyMeasurable
      (fun w : ℝ × ℝ =>
        weightedMovingHeatEta eta c (t - w.1) (g w.1) w.2)
      ((volume.restrict (Set.Ioc a t)).prod volume) :=
    (weightedMovingHeatEta_history_stronglyMeasurable_of_joint_measurable_bounded
      (eta := eta) (c := c) (tau := t) hg_joint).aestronglyMeasurable
  have hdata := weightedMovingHeat_generatorRestart_data_of_uniform_square_bound
    (eta := eta) (c := c) ht.1 (sq_nonneg K)
      (fun q hq => hg_meas q ⟨hq.1, hq.2.trans ht.2⟩)
      (fun q hq => hg_sq q ⟨hq.1, hq.2.trans ht.2⟩)
      hg_le hhistTotal hjointHeat
  have hdamped :=
    (weightedMovingHeat_damped_histories_intervalIntegrable_of_uniform_norm_bound
      (eta := eta) (c := c) ht.1 hK
      (fun q hq => hGbound q ⟨hq.1, hq.2.trans ht.2⟩) hhist).1
  exact ⟨hhist, hdamped, hdata.2⟩

/-- Final bounded-state history interface: jointly measurable scalar
representatives, uniform exact-weight square budgets, and measurable `L²`
realizations give the damped restart history on every terminal slice. -/
theorem weightedMovingHeat_boundedState_damped_history_intervalIntegrable
    {eta c a r Cz Cf : ℝ} (har : a ≤ r)
    (hCz : 0 ≤ Cz) (hCf : 0 ≤ Cf)
    {z f : ℝ → ℝ → ℝ} {Z F : ℝ → WholeLineRealL2}
    (hz_joint : Measurable (Function.uncurry z))
    (hf_joint : Measurable (Function.uncurry f))
    (hz_sq : ∀ q ∈ Set.Icc a r,
      Integrable (fun x : ℝ => z q x ^ 2) volume)
    (hf_sq : ∀ q ∈ Set.Icc a r,
      Integrable (fun x : ℝ => f q x ^ 2) volume)
    (hz_le : ∀ q ∈ Set.Icc a r,
      (∫ x : ℝ, z q x ^ 2) ≤ Cz)
    (hf_le : ∀ q ∈ Set.Icc a r,
      (∫ x : ℝ, f q x ^ 2) ≤ Cf)
    (hZrep : ∀ q ∈ Set.Icc a r,
      (((Z q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] z q))
    (hFrep : ∀ q ∈ Set.Icc a r,
      (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] f q))
    (hZtime : AEStronglyMeasurable Z volume)
    (hFtime : AEStronglyMeasurable F volume) :
    ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q) (Z q + F q))
      volume a t := by
  intro t ht
  exact (weightedMovingHeat_boundedState_history_data
    (eta := eta) (c := c) har hCz hCf hz_joint hf_joint hz_sq hf_sq
      hz_le hf_le hZrep hFrep hZtime hFtime t ht).2.1

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.weightedMovingHeatL2Semigroup_terminal_history_aestronglyMeasurable_of_stronglyMeasurable
#print axioms
  ShenWork.Paper1.weightedMovingHeatL2Semigroup_terminal_history_aestronglyMeasurable_of_aestronglyMeasurable
#print axioms
  ShenWork.Paper1.weightedMovingHeatEta_history_stronglyMeasurable_of_joint_measurable_bounded
#print axioms ShenWork.Paper1.weightedMovingHeat_boundedState_history_data
#print axioms
  ShenWork.Paper1.weightedMovingHeat_boundedState_damped_history_intervalIntegrable
