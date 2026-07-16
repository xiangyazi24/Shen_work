import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorShift
import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorDomainNatural

open Filter MeasureTheory Set Topology
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Convergence of shifted positive generator regularizations

This file closes the endpoint-generator limit for one exact-weight mild
restart.  The proof uses the native truncated cancellation, the exact
shift decomposition, the Holder translation bound, and the short upper
tail estimate.  No generator-domain or spatial second-derivative premise is
used.
-/

/-- A strongly measurable, uniformly bounded Banach-valued section on a
compact interval is interval integrable. -/
theorem intervalIntegrable_of_aestronglyMeasurable_Icc_of_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b M : ℝ} (hab : a ≤ b)
    (hmeas : AEStronglyMeasurable f (volume.restrict (Set.Icc a b)))
    (hbound : ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  apply IntegrableOn.of_bound measure_Icc_lt_top hmeas M
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hbound x hx

/-- The explicit full-generator value of a positive-time mild restart. -/
def weightedMovingHeatFullGeneratorValue
    (eta c a t : ℝ) (Z₀ : WholeLineRealL2)
    (F : ℝ → WholeLineRealL2) : WholeLineRealL2 :=
  weightedMovingHeatL2Generator eta c (t - a) Z₀ +
    ((∫ r in (0 : ℝ)..t - a,
        weightedMovingHeatL2Generator eta c r (F (t - r) - F t)) +
      (weightedMovingHeatL2Semigroup eta c (t - a) - 1) (F t))

/-- Along an arbitrary positive sequence tending to zero, applying the
positive generator regularization to a full mild candidate converges to the
canonical endpoint-cancellation expression.

The only measure-theoretic assumptions are measurability of the native
generator history and of each translated history.  All interval
integrability fields used by the cancellation and shift lemmas are produced
inside the proof from these assumptions and the uniform forcing bound. -/
theorem weightedMovingHeatL2Generator_fullGeneratorCandidate_tendsto_sequence
    {eta c a t theta H K : ℝ}
    (hat : a < t) (htheta : 0 < theta)
    (hH : 0 ≤ H) (hK : 0 ≤ K)
    {F : ℝ → WholeLineRealL2} {Z₀ : WholeLineRealL2}
    (hFbound : ∀ s ∈ Set.Icc a t, ‖F s‖ ≤ K)
    (hFholder : ∀ s ∈ Set.Icc a t, ∀ q ∈ Set.Icc a t,
      ‖F s - F q‖ ≤ H * |s - q| ^ theta)
    (hhist : IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      volume a t)
    (hbase_meas : AEStronglyMeasurable
      (fun r => weightedMovingHeatL2Generator eta c r (F (t - r)))
      (volume.restrict (Set.Ioc (0 : ℝ) (t - a))))
    {eps : ℕ → ℝ}
    (heps_pos : ∀ n, 0 < eps n)
    (hepsh : ∀ n, eps n ≤ t - a)
    (heps : Tendsto eps atTop (nhds 0))
    (hshift_meas : ∀ n, AEStronglyMeasurable
      (fun r => weightedMovingHeatL2Generator eta c r
        (F (t + eps n - r)))
      (volume.restrict (Set.Icc (eps n) (t - a + eps n)))) :
    Tendsto
      (fun n => weightedMovingHeatL2Generator eta c (eps n)
        (weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F t))
      atTop
      (nhds (weightedMovingHeatFullGeneratorValue eta c a t Z₀ F)) := by
  let h : ℝ := t - a
  let C : ℝ := weightedMovingHeatGeneratorHorizonConst eta c (2 * h)
  let L : WholeLineRealL2 :=
    (∫ r in (0 : ℝ)..h,
        weightedMovingHeatL2Generator eta c r (F (t - r) - F t)) +
      (weightedMovingHeatL2Semigroup eta c h - 1) (F t)
  let Hom : ℕ → WholeLineRealL2 := fun n =>
    weightedMovingHeatL2Generator eta c (eps n + h) Z₀
  let Base : ℕ → WholeLineRealL2 := fun n =>
    ∫ r in eps n..h,
      weightedMovingHeatL2Generator eta c r (F (t - r))
  let Err : ℕ → WholeLineRealL2 := fun n =>
    ∫ r in eps n..h,
      weightedMovingHeatL2Generator eta c r
        (F (t + eps n - r) - F (t - r))
  let Tail : ℕ → WholeLineRealL2 := fun n =>
    ∫ r in h..h + eps n,
      weightedMovingHeatL2Generator eta c r (F (t + eps n - r))
  have hh : 0 < h := by
    dsimp only [h]
    linarith
  have hh0 : 0 ≤ h := hh.le
  have h2h0 : 0 ≤ 2 * h := by positivity
  have hC : 0 ≤ C := by
    exact weightedMovingHeatGeneratorHorizonConst_nonneg h2h0
  have hA : ∀ r ∈ Set.Ioc (0 : ℝ) (2 * h),
      ‖weightedMovingHeatL2Generator eta c r‖ ≤ C * r⁻¹ := by
    intro r hr
    have hraw := weightedMovingHeatL2Generator_norm_le_horizon
      eta c (2 * h) r hr
    simpa only [C, Real.rpow_neg_one] using hraw
  have hbase_int : ∀ n, IntervalIntegrable
      (fun r => weightedMovingHeatL2Generator eta c r (F (t - r)))
      volume (eps n) h := by
    intro n
    have henh : eps n ≤ h := by simpa only [h] using hepsh n
    have hmeas : AEStronglyMeasurable
        (fun r => weightedMovingHeatL2Generator eta c r (F (t - r)))
        (volume.restrict (Set.Icc (eps n) h)) := by
      apply hbase_meas.mono_measure
      apply Measure.restrict_mono
      · intro r hr
        exact ⟨(heps_pos n).trans_le hr.1, hr.2⟩
      · exact le_rfl
    apply intervalIntegrable_of_aestronglyMeasurable_Icc_of_norm_le
      henh hmeas
    intro r hr
    have hrpos : 0 < r := (heps_pos n).trans_le hr.1
    have hr2h : r ≤ 2 * h := hr.2.trans (by linarith [hh])
    have htime : t - r ∈ Set.Icc a t := by
      constructor <;> dsimp only [h] at hr ⊢ <;> linarith [hr.1, hr.2]
    have hopen := (weightedMovingHeatL2Generator eta c r).le_opNorm
      (F (t - r))
    calc
      ‖weightedMovingHeatL2Generator eta c r (F (t - r))‖ ≤
          ‖weightedMovingHeatL2Generator eta c r‖ * ‖F (t - r)‖ := hopen
      _ ≤ (C * r⁻¹) * K := by
        exact mul_le_mul (hA r ⟨hrpos, hr2h⟩)
          (hFbound (t - r) htime) (norm_nonneg _)
          (mul_nonneg hC (inv_nonneg.mpr hrpos.le))
      _ ≤ (C * (eps n)⁻¹) * K := by
        have hinv : r⁻¹ ≤ (eps n)⁻¹ := by
          simpa only [one_div] using
            one_div_le_one_div_of_le (heps_pos n) hr.1
        gcongr
  have hshift_int : ∀ n, IntervalIntegrable
      (fun r => weightedMovingHeatL2Generator eta c r
        (F (t + eps n - r)))
      volume (eps n) (h + eps n) := by
    intro n
    have henh : eps n ≤ h := by simpa only [h] using hepsh n
    have horder : eps n ≤ h + eps n := by linarith [hh]
    apply intervalIntegrable_of_aestronglyMeasurable_Icc_of_norm_le
      horder (hshift_meas n)
    intro r hr
    have hrpos : 0 < r := (heps_pos n).trans_le hr.1
    have hr2h : r ≤ 2 * h := by linarith [hr.2, henh]
    have htime : t + eps n - r ∈ Set.Icc a t := by
      constructor
      · dsimp only [h] at hr henh ⊢
        linarith [hr.2]
      · linarith [hr.1]
    calc
      ‖weightedMovingHeatL2Generator eta c r (F (t + eps n - r))‖ ≤
          ‖weightedMovingHeatL2Generator eta c r‖ *
            ‖F (t + eps n - r)‖ :=
        (weightedMovingHeatL2Generator eta c r).le_opNorm _
      _ ≤ (C * r⁻¹) * K := by
        exact mul_le_mul (hA r ⟨hrpos, hr2h⟩)
          (hFbound (t + eps n - r) htime) (norm_nonneg _)
          (mul_nonneg hC (inv_nonneg.mpr hrpos.le))
      _ ≤ (C * (eps n)⁻¹) * K := by
        have hinv : r⁻¹ ≤ (eps n)⁻¹ := by
          simpa only [one_div] using
            one_div_le_one_div_of_le (heps_pos n) hr.1
        gcongr
  have hconst_cont : ContinuousOn
      (fun r => weightedMovingHeatL2Generator eta c r (F t))
      (Set.Ioc (0 : ℝ) h) := by
    intro r hr
    exact (weightedMovingHeatL2Generator_orbit_continuousAt_of_pos
      hr.1 (F t)).continuousWithinAt
  have hconst_meas : AEStronglyMeasurable
      (fun r => weightedMovingHeatL2Generator eta c r (F t))
      (volume.restrict (Set.Ioc (0 : ℝ) h)) :=
    hconst_cont.aestronglyMeasurable measurableSet_Ioc
  have hrem_meas : AEStronglyMeasurable
      (fun r => weightedMovingHeatL2Generator eta c r
        (F (t - r) - F t))
      (volume.restrict (Set.uIoc (0 : ℝ) h)) := by
    rw [Set.uIoc_of_le hh0]
    have hsub := hbase_meas.sub hconst_meas
    apply hsub.congr
    exact Eventually.of_forall fun r => by
      simp only [Pi.sub_apply, map_sub]
  have hconst_int : ∀ n, IntervalIntegrable
      (fun r => weightedMovingHeatL2Generator eta c r (F t))
      volume (eps n) h := by
    intro n
    have henh : eps n ≤ h := by simpa only [h] using hepsh n
    apply ContinuousOn.intervalIntegrable_of_Icc henh
    intro r hr
    exact (weightedMovingHeatL2Generator_orbit_continuousAt_of_pos
      ((heps_pos n).trans_le hr.1) (F t)).continuousWithinAt
  have horbit : ∀ n, ∀ r ∈ Set.Icc (eps n) h,
      HasDerivAt
        (fun q => weightedMovingHeatL2Semigroup eta c q (F t))
        (weightedMovingHeatL2Generator eta c r (F t)) r := by
    intro n r hr
    exact weightedMovingHeatL2Semigroup_orbit_hasDerivAt
      ((heps_pos n).trans_le hr.1) (F t)
  have hepsWithin : Tendsto eps atTop
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨heps, ?_⟩
    exact Eventually.of_forall fun n => heps_pos n
  have hSzero : Tendsto
      (fun n => weightedMovingHeatL2Semigroup eta c (eps n) (F t))
      atTop (nhds (F t)) :=
    (weightedMovingHeatL2Semigroup_tendsto_zero eta c (F t)).comp hepsWithin
  have hFnative : ∀ r ∈ Set.Icc (0 : ℝ) h,
      ‖F (t - r) - F t‖ ≤ H * r ^ theta := by
    intro r hr
    have htime : t - r ∈ Set.Icc a t := by
      constructor <;> dsimp only [h] at hr ⊢ <;> linarith [hr.1, hr.2]
    have htmem : t ∈ Set.Icc a t := ⟨hat.le, le_rfl⟩
    simpa only [sub_sub_cancel_left, abs_neg, abs_of_nonneg hr.1] using
      hFholder (t - r) htime t htmem
  have hBase : Tendsto Base atTop (nhds L) := by
    exact weightedMovingHeatL2_generatorDuhamel_truncated_tendsto
      htheta hh0 hC hH heps_pos
      (fun n => by simpa only [h] using hepsh n) heps
      (fun r hr => by
        have hr2h : r ≤ 2 * h := hr.2.trans (by linarith [hh])
        simpa only [Real.rpow_neg_one] using hA r ⟨hr.1, hr2h⟩)
      hFnative hrem_meas hbase_int hconst_int horbit hSzero
  have hHom : Tendsto Hom atTop
      (nhds (weightedMovingHeatL2Generator eta c h Z₀)) := by
    have harg : Tendsto (fun n => eps n + h) atTop (nhds h) := by
      simpa only [zero_add] using heps.add tendsto_const_nhds
    exact (weightedMovingHeatL2Generator_orbit_continuousAt_of_pos
      hh Z₀).tendsto.comp harg
  have hErr : Tendsto Err atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    let B : ℕ → ℝ := fun n =>
      (C * H * ((2 / theta) * h ^ (theta / 2))) *
        (eps n) ^ (theta / 2)
    have hB : Tendsto B atTop (nhds 0) := by
      have hp : 0 < theta / 2 := by linarith
      have hrpow : Tendsto (fun n => (eps n) ^ (theta / 2))
          atTop (nhds 0) := by
        have := heps.rpow_const (Or.inr hp.le)
        simpa only [Real.zero_rpow (ne_of_gt hp)] using this
      simpa only [B, mul_zero] using
        (hrpow.const_mul (C * H * ((2 / theta) * h ^ (theta / 2))))
    apply squeeze_zero (fun n => norm_nonneg (Err n)) _ hB
    intro n
    have henh : eps n ≤ h := by simpa only [h] using hepsh n
    have htrans : ∀ r ∈ Set.Icc (eps n) h,
        ‖F (t + eps n - r) - F (t - r)‖ ≤
          H * (eps n) ^ theta := by
      intro r hr
      have hs : t + eps n - r ∈ Set.Icc a t := by
        constructor
        · dsimp only [h] at hr henh ⊢
          linarith [hr.2, heps_pos n]
        · linarith [hr.1]
      have hq : t - r ∈ Set.Icc a t := by
        constructor
        · dsimp only [h] at hr ⊢
          linarith [hr.2]
        · linarith [hr.1, heps_pos n]
      have hraw := hFholder (t + eps n - r) hs (t - r) hq
      have habs : |(t + eps n - r) - (t - r)| = eps n := by
        rw [show (t + eps n - r) - (t - r) = eps n by ring,
          abs_of_pos (heps_pos n)]
      simpa only [habs] using hraw
    have herr_int : IntervalIntegrable
        (fun r => weightedMovingHeatL2Generator eta c r
          (F (t + eps n - r) - F (t - r))) volume (eps n) h := by
      have horder : eps n ≤ h + eps n := by linarith [hh]
      have hsubset : Set.uIcc (eps n) h ⊆
          Set.uIcc (eps n) (h + eps n) := by
        intro r hr
        rw [Set.uIcc_of_le henh] at hr
        rw [Set.uIcc_of_le horder]
        exact ⟨hr.1, hr.2.trans (le_add_of_nonneg_right (heps_pos n).le)⟩
      have hsub := ((hshift_int n).mono_set hsubset).sub (hbase_int n)
      apply hsub.congr
      intro r _hr
      change
        weightedMovingHeatL2Generator eta c r (F (t + eps n - r)) -
            weightedMovingHeatL2Generator eta c r (F (t - r)) =
          weightedMovingHeatL2Generator eta c r
            (F (t + eps n - r) - F (t - r))
      rw [map_sub]
    have hlog := intervalIntegral_weightedMovingHeatL2Generator_translation_error_norm_le
      hh (heps_pos n) henh hC hH
      (F := F) (t := t)
      (fun r hr => by
        have hr2h : r ≤ 2 * h := hr.2.trans (by linarith [hh])
        simpa only [Real.rpow_neg_one] using hA r ⟨hr.1, hr2h⟩)
      htrans herr_int
    have hp := rpow_mul_log_div_le_half_power
      hh (heps_pos n) htheta
    dsimp only [Err, B]
    calc
      ‖∫ r in eps n..h,
          weightedMovingHeatL2Generator eta c r
            (F (t + eps n - r) - F (t - r))‖ ≤
          C * H * (eps n) ^ theta * Real.log (h / eps n) := hlog
      _ = C * H * ((eps n) ^ theta * Real.log (h / eps n)) := by ring
      _ ≤ C * H *
          ((2 / theta) * h ^ (theta / 2) * (eps n) ^ (theta / 2)) := by
        exact mul_le_mul_of_nonneg_left hp (mul_nonneg hC hH)
      _ = (C * H * ((2 / theta) * h ^ (theta / 2))) *
          (eps n) ^ (theta / 2) := by ring
  have hTail : Tendsto Tail atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    let B : ℕ → ℝ := fun n => C * h⁻¹ * K * eps n
    have hB : Tendsto B atTop (nhds 0) := by
      simpa only [B, mul_zero] using
        heps.const_mul (C * h⁻¹ * K)
    apply squeeze_zero (fun n => norm_nonneg (Tail n)) _ hB
    intro n
    have henh : eps n ≤ h := by simpa only [h] using hepsh n
    have htailF : ∀ r ∈ Set.Icc h (h + eps n),
        ‖F (t + eps n - r)‖ ≤ K := by
      intro r hr
      apply hFbound
      constructor
      · dsimp only [h] at hr ⊢
        linarith [hr.2]
      · linarith [hr.1]
    dsimp only [Tail, B]
    exact intervalIntegral_weightedMovingHeatL2Generator_upper_tail_norm_le
      hh (heps_pos n).le (by linarith [henh]) hC
      (T := 2 * h) (F := F) (t := t) hA htailF
  have hEq : ∀ n,
      weightedMovingHeatL2Generator eta c (eps n)
          (weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F t) =
        Hom n + (Base n + Err n + Tail n) := by
    intro n
    have henh : eps n ≤ h := by simpa only [h] using hepsh n
    have happ := weightedMovingHeatL2Generator_apply_fullGeneratorCandidate_lag
      (Z₀ := Z₀) (F := F) hat.le (heps_pos n) hhist
    have hlag := intervalIntegral_weightedMovingHeatL2Generator_add_lag_eq_shift
      (eta := eta) (c := c) (h := h) (t := t) (eps := eps n) (F := F)
    have hdecomp := intervalIntegral_weightedMovingHeatL2Generator_shift_decomposition
      (eta := eta) (c := c) (h := h) (t := t) (eps := eps n)
      (heps_pos n).le henh (hshift_int n) (hbase_int n)
    dsimp only [Hom, Base, Err, Tail]
    simpa only [h] using happ.trans (by rw [hlag, hdecomp])
  have hsum := hHom.add ((hBase.add hErr).add hTail)
  have hsum' : Tendsto
      (fun n => Hom n + (Base n + Err n + Tail n)) atTop
      (nhds (weightedMovingHeatFullGeneratorValue eta c a t Z₀ F)) := by
    simpa only [h, L, add_zero, weightedMovingHeatFullGeneratorValue]
      using hsum
  refine hsum'.congr' ?_
  exact Eventually.of_forall fun n => (hEq n).symm

/-- Filter form of the positive-generator convergence.  The proof applies
the sequence theorem after discarding a finite prefix of an arbitrary
sequence converging within the positive half-line. -/
theorem weightedMovingHeatL2Generator_fullGeneratorCandidate_tendsto
    {eta c a t theta H K : ℝ}
    (hat : a < t) (htheta : 0 < theta)
    (hH : 0 ≤ H) (hK : 0 ≤ K)
    {F : ℝ → WholeLineRealL2} {Z₀ : WholeLineRealL2}
    (hFbound : ∀ s ∈ Set.Icc a t, ‖F s‖ ≤ K)
    (hFholder : ∀ s ∈ Set.Icc a t, ∀ q ∈ Set.Icc a t,
      ‖F s - F q‖ ≤ H * |s - q| ^ theta)
    (hhist : IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      volume a t)
    (hbase_meas : AEStronglyMeasurable
      (fun r => weightedMovingHeatL2Generator eta c r (F (t - r)))
      (volume.restrict (Set.Ioc (0 : ℝ) (t - a))))
    (hshift_meas : ∀ e, 0 < e → e ≤ t - a →
      AEStronglyMeasurable
        (fun r => weightedMovingHeatL2Generator eta c r
          (F (t + e - r)))
        (volume.restrict (Set.Icc e (t - a + e)))) :
    Tendsto
      (fun e : ℝ => weightedMovingHeatL2Generator eta c e
        (weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F t))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (weightedMovingHeatFullGeneratorValue eta c a t Z₀ F)) := by
  rw [tendsto_iff_seq_tendsto]
  intro e he
  have heparts := tendsto_nhdsWithin_iff.mp he
  have he0 : Tendsto e atTop (nhds 0) := heparts.1
  have hepos : ∀ᶠ n in atTop, 0 < e n := by
    simpa only [Set.mem_Ioi] using heparts.2
  have heh : ∀ᶠ n in atTop, e n ≤ t - a := by
    have hnhds : Set.Iio (t - a) ∈ nhds (0 : ℝ) :=
      Iio_mem_nhds (sub_pos.mpr hat)
    exact (he0.eventually hnhds).mono fun n hn => hn.le
  rcases (eventually_atTop.1 (hepos.and heh)) with ⟨N, hN⟩
  let eN : ℕ → ℝ := fun n => e (n + N)
  have heNpos : ∀ n, 0 < eN n := by
    intro n
    exact (hN (n + N) (Nat.le_add_left N n)).1
  have heNh : ∀ n, eN n ≤ t - a := by
    intro n
    exact (hN (n + N) (Nat.le_add_left N n)).2
  have heN0 : Tendsto eN atTop (nhds 0) := by
    exact he0.comp (tendsto_add_atTop_nat N)
  have hseq :=
    weightedMovingHeatL2Generator_fullGeneratorCandidate_tendsto_sequence
      (F := F) (Z₀ := Z₀) (eps := eN)
      hat htheta hH hK hFbound hFholder hhist hbase_meas
      heNpos heNh heN0 (fun n => hshift_meas (eN n) (heNpos n) (heNh n))
  let g : ℕ → WholeLineRealL2 := fun n =>
    weightedMovingHeatL2Generator eta c (e n)
      (weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F t)
  have hgN : Tendsto (fun n => g (n + N)) atTop
      (nhds (weightedMovingHeatFullGeneratorValue eta c a t Z₀ F)) := by
    simpa only [g, eN] using hseq
  have hg : Tendsto g atTop
      (nhds (weightedMovingHeatFullGeneratorValue eta c a t Z₀ F)) :=
    (tendsto_add_atTop_iff_nat N).mp hgN
  simpa only [Function.comp_apply, g] using hg

/-- The full mild candidate belongs to the right generator domain, with the
explicit generator value above. -/
theorem weightedMovingHeatL2Semigroup_fullGeneratorCandidate_hasDerivWithinAt_zero
    {eta c a t theta H K : ℝ}
    (hat : a < t) (htheta : 0 < theta)
    (hH : 0 ≤ H) (hK : 0 ≤ K)
    {F : ℝ → WholeLineRealL2} {Z₀ : WholeLineRealL2}
    (hFbound : ∀ s ∈ Set.Icc a t, ‖F s‖ ≤ K)
    (hFholder : ∀ s ∈ Set.Icc a t, ∀ q ∈ Set.Icc a t,
      ‖F s - F q‖ ≤ H * |s - q| ^ theta)
    (hhist : IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      volume a t)
    (hbase_meas : AEStronglyMeasurable
      (fun r => weightedMovingHeatL2Generator eta c r (F (t - r)))
      (volume.restrict (Set.Ioc (0 : ℝ) (t - a))))
    (hshift_meas : ∀ e, 0 < e → e ≤ t - a →
      AEStronglyMeasurable
        (fun r => weightedMovingHeatL2Generator eta c r
          (F (t + e - r)))
        (volume.restrict (Set.Icc e (t - a + e)))) :
    HasDerivWithinAt
      (fun e : ℝ => weightedMovingHeatL2Semigroup eta c e
        (weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F t))
      (weightedMovingHeatFullGeneratorValue eta c a t Z₀ F)
      (Set.Ici 0) 0 := by
  apply weightedMovingHeatL2Semigroup_hasDerivWithinAt_zero_of_generator_tendsto
  exact weightedMovingHeatL2Generator_fullGeneratorCandidate_tendsto
    hat htheta hH hK hFbound hFholder hhist hbase_meas hshift_meas

section AxiomAudit

#print axioms intervalIntegrable_of_aestronglyMeasurable_Icc_of_norm_le
#print axioms weightedMovingHeatFullGeneratorValue
#print axioms
  weightedMovingHeatL2Generator_fullGeneratorCandidate_tendsto_sequence
#print axioms
  weightedMovingHeatL2Generator_fullGeneratorCandidate_tendsto
#print axioms
  weightedMovingHeatL2Semigroup_fullGeneratorCandidate_hasDerivWithinAt_zero

end AxiomAudit

end ShenWork.Paper1
