import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorRestartNatural
import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorClosure
import ShenWork.Paper1.WholeLineWeightedRegularityDuhamelHolder

open Filter MeasureTheory Set Topology
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Positive generator regularization of a full mild restart

This file records the exact algebra needed before the endpoint-generator
limit.  Applying a positive generator regularization to the full mild state
shifts every heat lag by the same positive amount.  No endpoint generator
domain or time derivative is assumed.
-/

/-- A positive generator regularization commutes through the full mild
candidate.  The only analytic premise is Bochner integrability of the
original heat history; boundedness of the regularizing continuous linear map
then supplies integrability after applying it. -/
theorem weightedMovingHeatL2Generator_apply_fullGeneratorCandidate
    {eta c a t eps : ℝ} (hat : a ≤ t) (heps : 0 < eps)
    {F : ℝ → WholeLineRealL2} {Z₀ : WholeLineRealL2}
    (hhist : IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      volume a t) :
    weightedMovingHeatL2Generator eta c eps
        (weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F t) =
      weightedMovingHeatL2Generator eta c (eps + (t - a)) Z₀ +
        ∫ q in a..t,
          weightedMovingHeatL2Generator eta c (eps + (t - q)) (F q) := by
  let Aeps : WholeLineRealL2 →L[ℝ] WholeLineRealL2 :=
    weightedMovingHeatL2Generator eta c eps
  have hhom :
      Aeps (weightedMovingHeatL2Semigroup eta c (t - a) Z₀) =
        weightedMovingHeatL2Generator eta c (eps + (t - a)) Z₀ := by
    have hcomp := weightedMovingHeatL2Generator_comp_semigroup_add
      (eta := eta) (c := c) heps (sub_nonneg.mpr hat)
    exact DFunLike.congr_fun hcomp Z₀
  have hcommute := Aeps.intervalIntegral_comp_comm hhist
  have hint :
      Aeps (∫ q in a..t,
          weightedMovingHeatL2Semigroup eta c (t - q) (F q)) =
        ∫ q in a..t,
          weightedMovingHeatL2Generator eta c (eps + (t - q)) (F q) := by
    rw [← hcommute]
    apply intervalIntegral.integral_congr
    intro q hq
    have hqt : q ≤ t := by
      rw [uIcc_of_le hat] at hq
      exact hq.2
    have hcomp := weightedMovingHeatL2Generator_comp_semigroup_add
      (eta := eta) (c := c) heps (sub_nonneg.mpr hqt)
    exact DFunLike.congr_fun hcomp (F q)
  unfold weightedMovingHeatFullGeneratorCandidate
  rw [map_add, hhom, hint]

/-- Time reversal rewrites the shifted generator history in its native lag
coordinate.  This is the coordinate used by the endpoint cancellation
theorem. -/
theorem intervalIntegral_weightedMovingHeatL2Generator_shift_eq_lag
    {eta c a t eps : ℝ} {F : ℝ → WholeLineRealL2} :
    (∫ q in a..t,
        weightedMovingHeatL2Generator eta c (eps + (t - q)) (F q)) =
      ∫ r in (0 : ℝ)..t - a,
        weightedMovingHeatL2Generator eta c (eps + r) (F (t - r)) := by
  let G : ℝ → WholeLineRealL2 := fun r =>
    weightedMovingHeatL2Generator eta c (eps + r) (F (t - r))
  have hchange := intervalIntegral.integral_comp_sub_left
    (f := G) (a := a) (b := t) t
  simpa only [G, sub_sub_cancel, sub_self] using hchange

/-- Lag-coordinate form of positive generator regularization of the full
mild candidate. -/
theorem weightedMovingHeatL2Generator_apply_fullGeneratorCandidate_lag
    {eta c a t eps : ℝ} (hat : a ≤ t) (heps : 0 < eps)
    {F : ℝ → WholeLineRealL2} {Z₀ : WholeLineRealL2}
    (hhist : IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      volume a t) :
    weightedMovingHeatL2Generator eta c eps
        (weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F t) =
      weightedMovingHeatL2Generator eta c (eps + (t - a)) Z₀ +
        ∫ r in (0 : ℝ)..t - a,
          weightedMovingHeatL2Generator eta c (eps + r) (F (t - r)) := by
  rw [weightedMovingHeatL2Generator_apply_fullGeneratorCandidate
    hat heps hhist]
  rw [intervalIntegral_weightedMovingHeatL2Generator_shift_eq_lag]

/-- Translating the positive generator regularization from the lag variable
to the generator-time variable.  The forcing acquires the matching forward
time shift `eps`. -/
theorem intervalIntegral_weightedMovingHeatL2Generator_add_lag_eq_shift
    {eta c h t eps : ℝ} {F : ℝ → WholeLineRealL2} :
    (∫ r in (0 : ℝ)..h,
        weightedMovingHeatL2Generator eta c (eps + r) (F (t - r))) =
      ∫ q in eps..h + eps,
        weightedMovingHeatL2Generator eta c q (F (t + eps - q)) := by
  let G : ℝ → WholeLineRealL2 := fun q =>
    weightedMovingHeatL2Generator eta c q (F (t + eps - q))
  have hchange := intervalIntegral.integral_comp_add_right
    (f := G) (a := (0 : ℝ)) (b := h) eps
  have hleft : (fun r : ℝ => G (r + eps)) = fun r =>
      weightedMovingHeatL2Generator eta c (eps + r) (F (t - r)) := by
    funext r
    dsimp only [G]
    congr 2 <;> ring
  rw [hleft] at hchange
  simpa only [G, zero_add] using hchange

/-- Exact decomposition of a shifted generator history into the native
truncated history, the forcing-translation error, and the short upper tail.
This is the algebraic bridge missing from the unshifted endpoint-cancellation
theorem. -/
theorem intervalIntegral_weightedMovingHeatL2Generator_shift_decomposition
    {eta c h t eps : ℝ} (heps : 0 ≤ eps) (hepsh : eps ≤ h)
    {F : ℝ → WholeLineRealL2}
    (hfull : IntervalIntegrable
      (fun q => weightedMovingHeatL2Generator eta c q
        (F (t + eps - q))) volume eps (h + eps))
    (hbase : IntervalIntegrable
      (fun q => weightedMovingHeatL2Generator eta c q
        (F (t - q))) volume eps h) :
    (∫ q in eps..h + eps,
        weightedMovingHeatL2Generator eta c q (F (t + eps - q))) =
      (∫ q in eps..h,
          weightedMovingHeatL2Generator eta c q (F (t - q))) +
        (∫ q in eps..h,
          weightedMovingHeatL2Generator eta c q
            (F (t + eps - q) - F (t - q))) +
        ∫ q in h..h + eps,
          weightedMovingHeatL2Generator eta c q (F (t + eps - q)) := by
  let Full : ℝ → WholeLineRealL2 := fun q =>
    weightedMovingHeatL2Generator eta c q (F (t + eps - q))
  let Base : ℝ → WholeLineRealL2 := fun q =>
    weightedMovingHeatL2Generator eta c q (F (t - q))
  let Err : ℝ → WholeLineRealL2 := fun q =>
    weightedMovingHeatL2Generator eta c q
      (F (t + eps - q) - F (t - q))
  have hepsTop : eps ≤ h + eps := by linarith
  have hhTop : h ≤ h + eps := by linarith
  have hfullHead : IntervalIntegrable Full volume eps h := by
    apply hfull.mono_set
    rw [Set.uIcc_of_le hepsTop, Set.uIcc_of_le hepsh]
    exact Set.Icc_subset_Icc_right hhTop
  have hfullTail : IntervalIntegrable Full volume h (h + eps) := by
    apply hfull.mono_set
    rw [Set.uIcc_of_le hepsTop, Set.uIcc_of_le hhTop]
    exact Set.Icc_subset_Icc_left hepsh
  have herr : IntervalIntegrable Err volume eps h := by
    have hsub : IntervalIntegrable (fun q => Full q - Base q)
        volume eps h := hfullHead.sub hbase
    apply hsub.congr
    intro q _hq
    dsimp only [Err, Full, Base]
    rw [map_sub]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hfullHead hfullTail
  have hhead : (∫ q in eps..h, Full q) =
      (∫ q in eps..h, Base q) + ∫ q in eps..h, Err q := by
    have hadd := intervalIntegral.integral_add hbase herr
    rw [← hadd]
    apply intervalIntegral.integral_congr
    intro q _hq
    dsimp only [Full, Base, Err]
    rw [map_sub]
    abel
  dsimp only [Full, Base, Err] at hsplit hhead ⊢
  rw [← hsplit, hhead]

/-- The forcing-translation error in the shifted generator history has the
expected `eps^theta * log (h/eps)` bound. -/
theorem intervalIntegral_weightedMovingHeatL2Generator_translation_error_norm_le
    {eta c h t eps theta C H : ℝ}
    (hh : 0 < h) (heps : 0 < eps) (hepsh : eps ≤ h)
    (hC : 0 ≤ C) (hH : 0 ≤ H)
    {F : ℝ → WholeLineRealL2}
    (hA : ∀ q ∈ Set.Ioc (0 : ℝ) h,
      ‖weightedMovingHeatL2Generator eta c q‖ ≤ C * q⁻¹)
    (hF : ∀ q ∈ Set.Icc eps h,
      ‖F (t + eps - q) - F (t - q)‖ ≤ H * eps ^ theta)
    (herr : IntervalIntegrable
      (fun q => weightedMovingHeatL2Generator eta c q
        (F (t + eps - q) - F (t - q))) volume eps h) :
    ‖∫ q in eps..h,
        weightedMovingHeatL2Generator eta c q
          (F (t + eps - q) - F (t - q))‖ ≤
      C * H * eps ^ theta * Real.log (h / eps) := by
  let M : ℝ := C * H * eps ^ theta
  have hM : 0 ≤ M := by
    dsimp only [M]
    positivity
  have hinv : IntervalIntegrable (fun q : ℝ => q⁻¹) volume eps h := by
    apply intervalIntegral.intervalIntegrable_inv
    · intro q hq
      rw [Set.uIcc_of_le hepsh] at hq
      exact ne_of_gt (heps.trans_le hq.1)
    · exact continuous_id.continuousOn
  have hmajor : IntervalIntegrable (fun q : ℝ => M * q⁻¹)
      volume eps h := hinv.const_mul M
  have hpoint : ∀ q ∈ Set.Icc eps h,
      ‖weightedMovingHeatL2Generator eta c q
        (F (t + eps - q) - F (t - q))‖ ≤ M * q⁻¹ := by
    intro q hq
    have hqpos : 0 < q := heps.trans_le hq.1
    have hAnorm := hA q ⟨hqpos, hq.2⟩
    have happly := (weightedMovingHeatL2Generator eta c q).le_opNorm
      (F (t + eps - q) - F (t - q))
    calc
      ‖weightedMovingHeatL2Generator eta c q
          (F (t + eps - q) - F (t - q))‖ ≤
          ‖weightedMovingHeatL2Generator eta c q‖ *
            ‖F (t + eps - q) - F (t - q)‖ := happly
      _ ≤ (C * q⁻¹) * (H * eps ^ theta) := by
        exact mul_le_mul hAnorm (hF q hq) (norm_nonneg _)
          (mul_nonneg hC (inv_nonneg.mpr hqpos.le))
      _ = M * q⁻¹ := by
        dsimp only [M]
        ring
  calc
    ‖∫ q in eps..h,
        weightedMovingHeatL2Generator eta c q
          (F (t + eps - q) - F (t - q))‖ ≤
        ∫ q in eps..h,
          ‖weightedMovingHeatL2Generator eta c q
            (F (t + eps - q) - F (t - q))‖ :=
      intervalIntegral.norm_integral_le_integral_norm hepsh
    _ ≤ ∫ q in eps..h, M * q⁻¹ :=
      intervalIntegral.integral_mono_on hepsh herr.norm hmajor hpoint
    _ = M * ∫ q in eps..h, q⁻¹ := by
      rw [intervalIntegral.integral_const_mul]
    _ = C * H * eps ^ theta * Real.log (h / eps) := by
      rw [integral_inv_of_pos heps hh]

/-- A positive Hölder power absorbs the logarithmic loss produced by the
shifted generator history. -/
theorem rpow_mul_log_div_le_half_power
    {h eps theta : ℝ} (hh : 0 < h) (heps : 0 < eps)
    (htheta : 0 < theta) :
    eps ^ theta * Real.log (h / eps) ≤
      (2 / theta) * h ^ (theta / 2) * eps ^ (theta / 2) := by
  let d : ℝ := theta / 2
  have hd : 0 < d := by dsimp only [d]; linarith
  have hratio : 0 ≤ h / eps := div_nonneg hh.le heps.le
  have hlog := Real.log_le_rpow_div hratio hd
  have hepspow : 0 ≤ eps ^ theta := Real.rpow_nonneg heps.le _
  calc
    eps ^ theta * Real.log (h / eps) ≤
        eps ^ theta * ((h / eps) ^ d / d) :=
      mul_le_mul_of_nonneg_left hlog hepspow
    _ = (2 / theta) * h ^ (theta / 2) * eps ^ (theta / 2) := by
      have hepsd : eps ^ d ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos heps d)
      have hdne : d ≠ 0 := ne_of_gt hd
      rw [Real.div_rpow hh.le heps.le]
      dsimp only [d]
      field_simp [hdne, hepsd]
      rw [show theta = theta / 2 + theta / 2 by ring,
        Real.rpow_add heps]
      ring

/-- The short upper tail created by translating the regularized generator
history is linear in the translation length. -/
theorem intervalIntegral_weightedMovingHeatL2Generator_upper_tail_norm_le
    {eta c h eps T C K : ℝ}
    (hh : 0 < h) (heps : 0 ≤ eps) (hhT : h + eps ≤ T)
    (hC : 0 ≤ C)
    {F : ℝ → WholeLineRealL2} {t : ℝ}
    (hA : ∀ q ∈ Set.Ioc (0 : ℝ) T,
      ‖weightedMovingHeatL2Generator eta c q‖ ≤ C * q⁻¹)
    (hF : ∀ q ∈ Set.Icc h (h + eps), ‖F (t + eps - q)‖ ≤ K) :
    ‖∫ q in h..h + eps,
        weightedMovingHeatL2Generator eta c q (F (t + eps - q))‖ ≤
      C * h⁻¹ * K * eps := by
  have hpoint : ∀ q ∈ Set.Icc h (h + eps),
      ‖weightedMovingHeatL2Generator eta c q (F (t + eps - q))‖ ≤
        C * h⁻¹ * K := by
    intro q hq
    have hqpos : 0 < q := hh.trans_le hq.1
    have hqT : q ≤ T := hq.2.trans hhT
    have hAnorm := hA q ⟨hqpos, hqT⟩
    have hinv : q⁻¹ ≤ h⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hh hq.1
    have hAcoarse :
        ‖weightedMovingHeatL2Generator eta c q‖ ≤ C * h⁻¹ :=
      hAnorm.trans (mul_le_mul_of_nonneg_left hinv hC)
    calc
      ‖weightedMovingHeatL2Generator eta c q (F (t + eps - q))‖ ≤
          ‖weightedMovingHeatL2Generator eta c q‖ *
            ‖F (t + eps - q)‖ :=
        (weightedMovingHeatL2Generator eta c q).le_opNorm _
      _ ≤ (C * h⁻¹) * K := by
        exact mul_le_mul hAcoarse (hF q hq) (norm_nonneg _)
          (mul_nonneg hC (inv_nonneg.mpr hh.le))
      _ = C * h⁻¹ * K := rfl
  have hbound := intervalIntegral_norm_le_const_mul_sub
    (a := h) (b := h + eps) (C := C * h⁻¹ * K)
    (le_add_of_nonneg_right heps) hpoint
  simpa only [add_sub_cancel_left] using hbound

/-- Positive-time generator regularizations form a strongly continuous
orbit.  The proof factors a neighborhood of `h` through one fixed positive
generator step and the strongly continuous heat orbit. -/
theorem weightedMovingHeatL2Generator_orbit_continuousAt_of_pos
    {eta c h : ℝ} (hh : 0 < h) (Z : WholeLineRealL2) :
    ContinuousAt (fun q => weightedMovingHeatL2Generator eta c q Z) h := by
  let r : ℝ := h / 2
  let A : WholeLineRealL2 →L[ℝ] WholeLineRealL2 :=
    weightedMovingHeatL2Generator eta c r
  have hr : 0 < r := by dsimp only [r]; linarith
  have hshift : ContinuousAt (fun q : ℝ => q - r) h :=
    continuousAt_id.sub continuousAt_const
  have hlag : h - r = r := by dsimp only [r]; ring
  have hS : ContinuousAt
      (fun q => weightedMovingHeatL2Semigroup eta c (q - r) Z) h := by
    have horbit :=
      (weightedMovingHeatL2Semigroup_orbit_hasDerivAt
        (eta := eta) (c := c) hr Z).continuousAt
    have hshift' := hshift
    change Tendsto (fun q : ℝ => q - r) (𝓝 h) (𝓝 (h - r)) at hshift'
    rw [hlag] at hshift'
    have hc := Filter.Tendsto.comp horbit hshift'
    change Tendsto
      (fun q => weightedMovingHeatL2Semigroup eta c (q - r) Z)
      (𝓝 h) (𝓝 (weightedMovingHeatL2Semigroup eta c r Z)) at hc
    change Tendsto
      (fun q => weightedMovingHeatL2Semigroup eta c (q - r) Z)
      (𝓝 h) (𝓝 (weightedMovingHeatL2Semigroup eta c (h - r) Z))
    rw [hlag]
    exact hc
  have hfixed : ContinuousAt
      (fun q => A (weightedMovingHeatL2Semigroup eta c (q - r) Z)) h :=
    A.continuous.continuousAt.comp hS
  have hevent : ∀ᶠ q : ℝ in 𝓝 h, r < q := Ioi_mem_nhds (by
    dsimp only [r]
    linarith)
  have heq : (fun q => A
      (weightedMovingHeatL2Semigroup eta c (q - r) Z)) =ᶠ[𝓝 h]
      fun q => weightedMovingHeatL2Generator eta c q Z := by
    filter_upwards [hevent] with q hq
    have hqr : 0 ≤ q - r := sub_nonneg.mpr hq.le
    have hcomp := weightedMovingHeatL2Generator_comp_semigroup_add
      (eta := eta) (c := c) hr hqr
    have happ := DFunLike.congr_fun hcomp Z
    dsimp only [A]
    simpa only [ContinuousLinearMap.comp_apply,
      show r + (q - r) = q by ring] using happ
  exact hfixed.congr_of_eventuallyEq heq.symm

section AxiomAudit

#print axioms
  weightedMovingHeatL2Generator_apply_fullGeneratorCandidate
#print axioms
  intervalIntegral_weightedMovingHeatL2Generator_shift_eq_lag
#print axioms
  weightedMovingHeatL2Generator_apply_fullGeneratorCandidate_lag
#print axioms
  intervalIntegral_weightedMovingHeatL2Generator_add_lag_eq_shift
#print axioms
  intervalIntegral_weightedMovingHeatL2Generator_shift_decomposition
#print axioms
  intervalIntegral_weightedMovingHeatL2Generator_translation_error_norm_le
#print axioms rpow_mul_log_div_le_half_power
#print axioms
  intervalIntegral_weightedMovingHeatL2Generator_upper_tail_norm_le
#print axioms weightedMovingHeatL2Generator_orbit_continuousAt_of_pos

end AxiomAudit

end ShenWork.Paper1
