import ShenWork.Paper1.WholeLineCauchyCanonicalSegments

open Filter Topology MeasureTheory Real Set Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section

namespace ShenWork.Paper1

/-!
# Global gluing of the canonical whole-line Cauchy segments

The canonical segments have length `H` and are restarted after the half-step
`delta = H / 2`.  We use segment `floor(t / delta).pred`; this makes every
strictly positive time an interior point of its preferred segment, including
the restart seams.
-/

theorem wholeLineCauchyGlobalSegmentTime_eq_two_step
    (p : CMParams) (u₀ : WholeLineBUC) :
    wholeLineCauchyGlobalSegmentTime p u₀ =
      2 * wholeLineCauchyGlobalStep p u₀ := by
  unfold wholeLineCauchyGlobalStep
  ring

/-- Preferred segment index.  The predecessor is what puts restart seams in
the interior of the preferred segment rather than at local time zero. -/
def wholeLineCauchyGlobalIndex
    (p : CMParams) (u₀ : WholeLineBUC) (t : ℝ) : ℕ :=
  if 0 ≤ t then (Nat.floor (t / wholeLineCauchyGlobalStep p u₀)).pred else 0

def wholeLineCauchyGlobalLocalTime
    (p : CMParams) (u₀ : WholeLineBUC) (t : ℝ) : ℝ :=
  t - (wholeLineCauchyGlobalIndex p u₀ t : ℝ) *
    wholeLineCauchyGlobalStep p u₀

theorem wholeLineCauchyGlobalLocalTime_nonneg
    (p : CMParams) (u₀ : WholeLineBUC) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ wholeLineCauchyGlobalLocalTime p u₀ t := by
  let δ := wholeLineCauchyGlobalStep p u₀
  have hδ : 0 < δ := wholeLineCauchyGlobalStep_pos p u₀
  have ha0 : 0 ≤ t / δ := div_nonneg ht hδ.le
  have hklo : ((Nat.floor (t / δ) : ℕ) : ℝ) ≤ t / δ :=
    Nat.floor_le ha0
  have hklo' : ((Nat.floor (t / δ) : ℕ) : ℝ) * δ ≤ t :=
    (le_div_iff₀ hδ).mp hklo
  have hpred :
      (((Nat.floor (t / δ)).pred : ℕ) : ℝ) ≤
        ((Nat.floor (t / δ) : ℕ) : ℝ) := by
    exact_mod_cast Nat.pred_le (Nat.floor (t / δ))
  have hpred' : (((Nat.floor (t / δ)).pred : ℕ) : ℝ) * δ ≤ t :=
    (mul_le_mul_of_nonneg_right hpred hδ.le).trans hklo'
  simpa [wholeLineCauchyGlobalLocalTime, wholeLineCauchyGlobalIndex, ht,
    δ] using sub_nonneg.mpr hpred'

theorem wholeLineCauchyGlobalLocalTime_lt_segmentTime
    (p : CMParams) (u₀ : WholeLineBUC) {t : ℝ} (ht : 0 ≤ t) :
    wholeLineCauchyGlobalLocalTime p u₀ t <
      wholeLineCauchyGlobalSegmentTime p u₀ := by
  let δ := wholeLineCauchyGlobalStep p u₀
  have hδ : 0 < δ := wholeLineCauchyGlobalStep_pos p u₀
  generalize hk : Nat.floor (t / δ) = k
  have hkhi0 : t / δ < ((Nat.floor (t / δ) : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one (t / δ)
  rw [hk] at hkhi0
  have hkhi' : t < ((k : ℝ) + 1) * δ := (div_lt_iff₀ hδ).mp hkhi0
  cases k with
  | zero =>
      have hcalc : t < 2 * δ := by
        norm_num at hkhi'
        linarith
      simpa [wholeLineCauchyGlobalLocalTime, wholeLineCauchyGlobalIndex, ht,
        δ, hk, wholeLineCauchyGlobalSegmentTime_eq_two_step] using hcalc
  | succ n =>
      have hcalc :
          t - (n : ℝ) * δ < 2 * δ := by
        norm_num [Nat.cast_add, Nat.cast_one] at hkhi'
        linarith
      simpa [wholeLineCauchyGlobalLocalTime, wholeLineCauchyGlobalIndex, ht,
        δ, hk, Nat.succ_eq_add_one,
        wholeLineCauchyGlobalSegmentTime_eq_two_step] using hcalc

theorem wholeLineCauchyGlobalLocalTime_pos
    (p : CMParams) (u₀ : WholeLineBUC) {t : ℝ} (ht : 0 < t) :
    0 < wholeLineCauchyGlobalLocalTime p u₀ t := by
  let δ := wholeLineCauchyGlobalStep p u₀
  have hδ : 0 < δ := wholeLineCauchyGlobalStep_pos p u₀
  have ha0 : 0 ≤ t / δ := div_nonneg ht.le hδ.le
  generalize hk : Nat.floor (t / δ) = k
  have hklo0 : ((Nat.floor (t / δ) : ℕ) : ℝ) ≤ t / δ := Nat.floor_le ha0
  rw [hk] at hklo0
  cases k with
  | zero =>
      simpa [wholeLineCauchyGlobalLocalTime, wholeLineCauchyGlobalIndex,
        ht.le, δ, hk] using ht
  | succ n =>
      have hklo' : ((n + 1 : ℕ) : ℝ) * δ ≤ t :=
        (le_div_iff₀ hδ).mp (by simpa [Nat.succ_eq_add_one] using hklo0)
      have hcalc : 0 < t - (n : ℝ) * δ := by
        norm_num [Nat.cast_add, Nat.cast_one] at hklo'
        linarith
      simpa [wholeLineCauchyGlobalLocalTime, wholeLineCauchyGlobalIndex,
        ht.le, δ, hk, Nat.succ_eq_add_one] using hcalc

/-- The total BUC-valued orbit obtained by evaluating the preferred segment.
Negative times are filled by the datum; the Cauchy interface only uses
nonnegative time. -/
def wholeLineCauchyGlobalBUC
    (p : CMParams) (u₀ : WholeLineBUC) (t : ℝ) : WholeLineBUC :=
  if 0 ≤ t then
    wholeLineBUCTrajectoryExtend
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
      (wholeLineCauchyGlobalSegment p u₀
        (wholeLineCauchyGlobalIndex p u₀ t))
      (wholeLineCauchyGlobalLocalTime p u₀ t)
  else u₀

def wholeLineCauchyGlobalU
    (p : CMParams) (u₀ : WholeLineBUC) (t x : ℝ) : ℝ :=
  (wholeLineCauchyGlobalBUC p u₀ t).1 x

def wholeLineCauchyGlobalV
    (p : CMParams) (u₀ : WholeLineBUC) (t : ℝ) : ℝ → ℝ :=
  frozenElliptic p (wholeLineCauchyGlobalU p u₀ t)

def wholeLineCauchyGlobalSegmentU
    (p : CMParams) (u₀ : WholeLineBUC) (n : ℕ) (t x : ℝ) : ℝ :=
  (wholeLineBUCTrajectoryExtend
    (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
    (wholeLineCauchyGlobalSegment p u₀ n) t).1 x

def wholeLineCauchyGlobalSegmentV
    (p : CMParams) (u₀ : WholeLineBUC) (n : ℕ) (t : ℝ) : ℝ → ℝ :=
  frozenElliptic p (wholeLineCauchyGlobalSegmentU p u₀ n t)

theorem wholeLineCauchyGlobalBUC_eq_segment
    (p : CMParams) (u₀ : WholeLineBUC) {t : ℝ} (ht : 0 ≤ t) :
    wholeLineCauchyGlobalBUC p u₀ t =
      wholeLineCauchyGlobalSegment p u₀
        (wholeLineCauchyGlobalIndex p u₀ t)
        ⟨wholeLineCauchyGlobalLocalTime p u₀ t,
          wholeLineCauchyGlobalLocalTime_nonneg p u₀ ht,
          (wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht).le⟩ := by
  rw [wholeLineCauchyGlobalBUC, if_pos ht]
  exact wholeLineBUCTrajectoryExtend_eq
    (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
    (wholeLineCauchyGlobalSegment p u₀
      (wholeLineCauchyGlobalIndex p u₀ t))
    ⟨wholeLineCauchyGlobalLocalTime_nonneg p u₀ ht,
      (wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht).le⟩

theorem wholeLineCauchyGlobalIndex_eq_pred_of_mem_cell
    (p : CMParams) (u₀ : WholeLineBUC) (k : ℕ) {t : ℝ}
    (ht : t ∈ Set.Ico ((k : ℝ) * wholeLineCauchyGlobalStep p u₀)
      (((k : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀)) :
    wholeLineCauchyGlobalIndex p u₀ t = k.pred := by
  let δ := wholeLineCauchyGlobalStep p u₀
  have hδ : 0 < δ := wholeLineCauchyGlobalStep_pos p u₀
  have ht0 : 0 ≤ t :=
    (mul_nonneg (Nat.cast_nonneg k) hδ.le).trans ht.1
  have hratio : t / δ ∈ Set.Ico (k : ℝ) ((k : ℝ) + 1) := by
    constructor
    · exact (le_div_iff₀ hδ).2 (by simpa [δ] using ht.1)
    · exact (div_lt_iff₀ hδ).2 (by simpa [δ] using ht.2)
  have hfloor : Nat.floor (t / δ) = k :=
    Nat.floor_eq_on_Ico k (t / δ) hratio
  simp [wholeLineCauchyGlobalIndex, ht0, δ, hfloor]

/-- Pointwise form of the half-window overlap between consecutive segments. -/
theorem wholeLineCauchyGlobalSegment_overlap_apply
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x) (n : ℕ)
    {r : ℝ} (hr0 : 0 ≤ r)
    (hrδ : r ≤ wholeLineCauchyGlobalStep p u₀) :
    wholeLineCauchyGlobalSegment p u₀ n
        ⟨wholeLineCauchyGlobalStep p u₀ + r,
          add_nonneg (wholeLineCauchyGlobalStep_pos p u₀).le hr0,
          by rw [wholeLineCauchyGlobalSegmentTime_eq_two_step]; linarith⟩ =
      wholeLineCauchyGlobalSegment p u₀ (n + 1)
        ⟨r, hr0,
          hrδ.trans (by
            rw [wholeLineCauchyGlobalSegmentTime_eq_two_step]
            linarith [wholeLineCauchyGlobalStep_pos p u₀])⟩ := by
  let δ := wholeLineCauchyGlobalStep p u₀
  let H := wholeLineCauchyGlobalSegmentTime p u₀
  have hov := congrArg
    (fun U : WholeLineBUCTrajectory δ => U ⟨r, hr0, hrδ⟩)
    (wholeLineCauchyGlobalSegment_overlap p hregime u₀ hu₀ n)
  simpa [δ, H] using hov

theorem wholeLineCauchyGlobalBUC_eq_preferred_on_cell
    (p : CMParams) (u₀ : WholeLineBUC) (k : ℕ) {t : ℝ}
    (ht : t ∈ Set.Ico ((k : ℝ) * wholeLineCauchyGlobalStep p u₀)
      (((k : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀)) :
    wholeLineCauchyGlobalBUC p u₀ t =
      wholeLineBUCTrajectoryExtend
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
        (wholeLineCauchyGlobalSegment p u₀ k.pred)
        (t - (k.pred : ℝ) * wholeLineCauchyGlobalStep p u₀) := by
  let δ := wholeLineCauchyGlobalStep p u₀
  have hδ : 0 < δ := wholeLineCauchyGlobalStep_pos p u₀
  have ht0 : 0 ≤ t :=
    (mul_nonneg (Nat.cast_nonneg k) hδ.le).trans (by simpa [δ] using ht.1)
  have hidx := wholeLineCauchyGlobalIndex_eq_pred_of_mem_cell p u₀ k ht
  simp [wholeLineCauchyGlobalBUC, ht0, wholeLineCauchyGlobalLocalTime,
    hidx, δ]

/-- On cell `n`, the globally selected predecessor segment can equally be
read in the next segment.  This is the left-hand chart at the following
restart seam. -/
theorem wholeLineCauchyGlobalBUC_eq_next_on_cell
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x) (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Ico ((n : ℝ) * wholeLineCauchyGlobalStep p u₀)
      (((n : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀)) :
    wholeLineCauchyGlobalBUC p u₀ t =
      wholeLineBUCTrajectoryExtend
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
        (wholeLineCauchyGlobalSegment p u₀ n)
        (t - (n : ℝ) * wholeLineCauchyGlobalStep p u₀) := by
  let δ := wholeLineCauchyGlobalStep p u₀
  have hδ : 0 < δ := wholeLineCauchyGlobalStep_pos p u₀
  have hr0 : 0 ≤ t - (n : ℝ) * δ := sub_nonneg.mpr (by simpa [δ] using ht.1)
  have hrδ : t - (n : ℝ) * δ ≤ δ := by
    have := ht.2.le
    dsimp [δ] at this ⊢
    linarith
  cases n with
  | zero =>
      simpa [δ] using
        (wholeLineCauchyGlobalBUC_eq_preferred_on_cell p u₀ 0 ht)
  | succ m =>
      have hdirect :=
        wholeLineCauchyGlobalBUC_eq_preferred_on_cell p u₀ (m + 1) ht
      have hleftmem : t - (m : ℝ) * δ ∈
          Set.Icc (0 : ℝ) (wholeLineCauchyGlobalSegmentTime p u₀) := by
        constructor
        · push_cast at hr0
          linarith
        · rw [wholeLineCauchyGlobalSegmentTime_eq_two_step]
          push_cast at hrδ
          dsimp [δ]
          linarith
      have hrightmem : t - ((m + 1 : ℕ) : ℝ) * δ ∈
          Set.Icc (0 : ℝ) (wholeLineCauchyGlobalSegmentTime p u₀) := by
        exact ⟨hr0, hrδ.trans (by
          rw [wholeLineCauchyGlobalSegmentTime_eq_two_step]
          dsimp [δ]
          linarith [wholeLineCauchyGlobalStep_pos p u₀])⟩
      have hleft :
          wholeLineBUCTrajectoryExtend
              (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
              (wholeLineCauchyGlobalSegment p u₀ m)
              (t - (m : ℝ) * δ) =
            wholeLineCauchyGlobalSegment p u₀ m
              ⟨δ + (t - ((m + 1 : ℕ) : ℝ) * δ),
                add_nonneg hδ.le hr0,
                by rw [wholeLineCauchyGlobalSegmentTime_eq_two_step];
                   linarith⟩ := by
        rw [wholeLineBUCTrajectoryExtend_eq _ _ hleftmem]
        congr 1
        push_cast
        ring
      have hright :
          wholeLineBUCTrajectoryExtend
              (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
              (wholeLineCauchyGlobalSegment p u₀ (m + 1))
              (t - ((m + 1 : ℕ) : ℝ) * δ) =
            wholeLineCauchyGlobalSegment p u₀ (m + 1)
              ⟨t - ((m + 1 : ℕ) : ℝ) * δ, hr0,
                hrightmem.2⟩ := by
        rw [wholeLineBUCTrajectoryExtend_eq _ _ hrightmem]
      calc
        wholeLineCauchyGlobalBUC p u₀ t =
            wholeLineBUCTrajectoryExtend
              (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
              (wholeLineCauchyGlobalSegment p u₀ m)
              (t - (m : ℝ) * δ) := by
                simpa [δ] using hdirect
        _ = wholeLineCauchyGlobalSegment p u₀ m
              ⟨δ + (t - ((m + 1 : ℕ) : ℝ) * δ),
                add_nonneg hδ.le hr0,
                by rw [wholeLineCauchyGlobalSegmentTime_eq_two_step];
                   linarith⟩ := hleft
        _ = wholeLineCauchyGlobalSegment p u₀ (m + 1)
              ⟨t - ((m + 1 : ℕ) : ℝ) * δ, hr0, hrightmem.2⟩ := by
                simpa [δ] using
                  (wholeLineCauchyGlobalSegment_overlap_apply
                    p hregime u₀ hu₀ m hr0 hrδ)
        _ = wholeLineBUCTrajectoryExtend
              (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
              (wholeLineCauchyGlobalSegment p u₀ (m + 1))
              (t - ((m + 1 : ℕ) : ℝ) * δ) := hright.symm
        _ = _ := by simp [δ]

/-- Every strictly positive global time has an open time neighborhood on
which the glued BUC orbit is a translate of one preferred canonical segment.
At a restart seam the left half is rewritten with the overlap theorem. -/
theorem wholeLineCauchyGlobalBUC_eventuallyEq_preferred
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {t : ℝ} (ht : 0 < t) :
    (fun s => wholeLineCauchyGlobalBUC p u₀ s) =ᶠ[nhds t]
      fun s =>
        wholeLineBUCTrajectoryExtend
          (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
          (wholeLineCauchyGlobalSegment p u₀
            (wholeLineCauchyGlobalIndex p u₀ t))
          (s - (wholeLineCauchyGlobalIndex p u₀ t : ℝ) *
            wholeLineCauchyGlobalStep p u₀) := by
  let δ := wholeLineCauchyGlobalStep p u₀
  have hδ : 0 < δ := wholeLineCauchyGlobalStep_pos p u₀
  let k := Nat.floor (t / δ)
  have ha0 : 0 ≤ t / δ := div_nonneg ht.le hδ.le
  have hklo : (k : ℝ) ≤ t / δ := Nat.floor_le ha0
  have hkhi : t / δ < (k : ℝ) + 1 := Nat.lt_floor_add_one (t / δ)
  have hklo' : (k : ℝ) * δ ≤ t := (le_div_iff₀ hδ).mp hklo
  have hkhi' : t < ((k : ℝ) + 1) * δ := (div_lt_iff₀ hδ).mp hkhi
  have htcell : t ∈ Set.Ico ((k : ℝ) * δ) (((k : ℝ) + 1) * δ) :=
    ⟨hklo', hkhi'⟩
  have hidxt : wholeLineCauchyGlobalIndex p u₀ t = k.pred := by
    apply wholeLineCauchyGlobalIndex_eq_pred_of_mem_cell p u₀ k
    simpa [δ] using htcell
  obtain hseam | hinterior := eq_or_lt_of_le hklo'
  · cases hkcase : k with
    | zero =>
        have hseam0 := hseam
        rw [hkcase] at hseam0
        norm_num at hseam0
        linarith
    | succ n =>
        have hseam' := hseam
        rw [hkcase] at hseam'
        have htn : t = ((n : ℝ) + 1) * δ := by
          push_cast at hseam'
          simpa [add_comm] using hseam'.symm
        have htopen :
            t ∈ Set.Ioo ((n : ℝ) * δ) (((n : ℝ) + 2) * δ) := by
          rw [htn]
          constructor <;> nlinarith
        refine Set.EqOn.eventuallyEq_of_mem ?_
          (isOpen_Ioo.mem_nhds htopen)
        intro s hs
        have hidxt' : wholeLineCauchyGlobalIndex p u₀ t = n := by
          rw [hkcase] at hidxt
          simpa using hidxt
        by_cases hsleft : s < t
        · have hscell : s ∈ Set.Ico ((n : ℝ) * δ)
              (((n : ℝ) + 1) * δ) := by
            exact ⟨hs.1.le, by simpa [htn] using hsleft⟩
          have hnext := wholeLineCauchyGlobalBUC_eq_next_on_cell
            p hregime u₀ hu₀ n (t := s) (by simpa [δ] using hscell)
          simpa [hidxt', δ] using hnext
        · have hscell : s ∈ Set.Ico (((n : ℝ) + 1) * δ)
              (((n : ℝ) + 2) * δ) := by
            exact ⟨by rw [← htn]; exact le_of_not_gt hsleft, hs.2⟩
          have hdirect := wholeLineCauchyGlobalBUC_eq_preferred_on_cell
            p u₀ (n + 1) (t := s) (by
              constructor
              · simpa [δ, Nat.cast_add, Nat.cast_one] using hscell.1
              · rw [show wholeLineCauchyGlobalStep p u₀ = δ from rfl]
                push_cast
                nlinarith [hscell.2])
          simpa [hidxt', δ] using hdirect
  · have htopen :
        t ∈ Set.Ioo ((k : ℝ) * δ) (((k : ℝ) + 1) * δ) :=
      ⟨hinterior, hkhi'⟩
    refine Set.EqOn.eventuallyEq_of_mem ?_ (isOpen_Ioo.mem_nhds htopen)
    intro s hs
    have hscell : s ∈ Set.Ico ((k : ℝ) * δ) (((k : ℝ) + 1) * δ) :=
      ⟨hs.1.le, hs.2⟩
    have hdirect := wholeLineCauchyGlobalBUC_eq_preferred_on_cell
      p u₀ k (t := s) (by simpa [δ] using hscell)
    simpa [hidxt, δ] using hdirect

theorem wholeLineCauchyGlobalSegment_isClassicalSolution
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x) (n : ℕ) :
    IsClassicalSolution p (wholeLineCauchyGlobalSegmentTime p u₀)
      (wholeLineCauchyGlobalSegmentU p u₀ n)
      (wholeLineCauchyGlobalSegmentV p u₀ n) := by
  have hstrip : ∀ z : Set.Icc (0 : ℝ)
      (wholeLineCauchyGlobalSegmentTime p u₀), ∀ x,
      (wholeLineCauchyGlobalSegment p u₀ n z).1 x ∈
        Set.Icc (0 : ℝ) (wholeLineCauchyGlobalClamp p u₀) :=
    (wholeLineCauchyGlobalDatum_segment_bounds p hregime u₀ hu₀ n).2.1
  simpa [wholeLineCauchyGlobalSegmentU, wholeLineCauchyGlobalSegmentV,
    wholeLineCauchyGlobalSegment] using
    (wholeLineCauchyBUCMildFixedPoint_isClassicalSolution
      p (M := wholeLineCauchyGlobalClamp p u₀)
      (T := wholeLineCauchyGlobalSegmentTime p u₀)
      (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
      (wholeLineCauchyGlobalClamp_pos p u₀).le
      (wholeLineCauchyGlobalSegmentTime_pos p u₀)
      (wholeLineCauchyGlobalDatum p u₀ n)
      (wholeLineCauchyGlobalSegmentTime_rate p u₀)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hstrip)

theorem wholeLineCauchyGlobalU_eventuallyEq_segment
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (fun s => wholeLineCauchyGlobalU p u₀ s x) =ᶠ[nhds t]
      fun s => wholeLineCauchyGlobalSegmentU p u₀
        (wholeLineCauchyGlobalIndex p u₀ t)
        (s - (wholeLineCauchyGlobalIndex p u₀ t : ℝ) *
          wholeLineCauchyGlobalStep p u₀) x := by
  have h := (wholeLineCauchyGlobalBUC_eventuallyEq_preferred
    p hregime u₀ hu₀ ht).fun_comp (fun w : WholeLineBUC => w.1 x)
  simpa [Function.comp_def, wholeLineCauchyGlobalU,
    wholeLineCauchyGlobalSegmentU] using h

theorem wholeLineCauchyGlobalV_eventuallyEq_segment
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (fun s => wholeLineCauchyGlobalV p u₀ s x) =ᶠ[nhds t]
      fun s => wholeLineCauchyGlobalSegmentV p u₀
        (wholeLineCauchyGlobalIndex p u₀ t)
        (s - (wholeLineCauchyGlobalIndex p u₀ t : ℝ) *
          wholeLineCauchyGlobalStep p u₀) x := by
  filter_upwards [wholeLineCauchyGlobalBUC_eventuallyEq_preferred
    p hregime u₀ hu₀ ht] with s hs
  have hslice : wholeLineCauchyGlobalU p u₀ s =
      wholeLineCauchyGlobalSegmentU p u₀
        (wholeLineCauchyGlobalIndex p u₀ t)
        (s - (wholeLineCauchyGlobalIndex p u₀ t : ℝ) *
          wholeLineCauchyGlobalStep p u₀) := by
    funext y
    exact congrArg (fun w : WholeLineBUC => w.1 y) hs
  simp only [wholeLineCauchyGlobalV, wholeLineCauchyGlobalSegmentV]
  rw [hslice]

theorem wholeLineCauchyGlobal_isGlobalClassicalSolution
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x) :
    IsGlobalClassicalSolution p
      (wholeLineCauchyGlobalU p u₀) (wholeLineCauchyGlobalV p u₀) := by
  intro T hT
  refine
    { hT := hT
      u_smooth := ?_
      v_smooth := ?_
      pde_u := ?_
      pde_v := ?_ }
  · intro t x ht _htT
    let n := wholeLineCauchyGlobalIndex p u₀ t
    let a := (n : ℝ) * wholeLineCauchyGlobalStep p u₀
    let q := t - a
    have hq0 : 0 < q := by
      simpa [q, a, n, wholeLineCauchyGlobalLocalTime] using
        (wholeLineCauchyGlobalLocalTime_pos p u₀ ht)
    have hqH : q < wholeLineCauchyGlobalSegmentTime p u₀ := by
      simpa [q, a, n, wholeLineCauchyGlobalLocalTime] using
        (wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht.le)
    have hseg := wholeLineCauchyGlobalSegment_isClassicalSolution
      p hregime u₀ hu₀ n
    have hev := wholeLineCauchyGlobalU_eventuallyEq_segment
      p hregime u₀ hu₀ ht x
    constructor
    · have hlocal : DifferentiableAt ℝ
          (fun s => wholeLineCauchyGlobalSegmentU p u₀ n (s - a) x) t :=
        (differentiableAt_comp_sub_const
          (f := fun r => wholeLineCauchyGlobalSegmentU p u₀ n r x)
          (a := t) (b := a)).2
            (by simpa [q] using (hseg.u_smooth q x hq0 hqH).1)
      exact (by
        apply (hev.differentiableAt_iff).2
        simpa [n, a] using hlocal)
    · have hslice : wholeLineCauchyGlobalU p u₀ t =
          wholeLineCauchyGlobalSegmentU p u₀ n q := by
        funext y
        have hy := (wholeLineCauchyGlobalU_eventuallyEq_segment
          p hregime u₀ hu₀ ht y).eq_of_nhds
        simpa [n, a, q] using hy
      rw [hslice]
      exact (hseg.u_smooth q x hq0 hqH).2
  · intro t x ht _htT
    let n := wholeLineCauchyGlobalIndex p u₀ t
    let a := (n : ℝ) * wholeLineCauchyGlobalStep p u₀
    let q := t - a
    have hq0 : 0 < q := by
      simpa [q, a, n, wholeLineCauchyGlobalLocalTime] using
        (wholeLineCauchyGlobalLocalTime_pos p u₀ ht)
    have hqH : q < wholeLineCauchyGlobalSegmentTime p u₀ := by
      simpa [q, a, n, wholeLineCauchyGlobalLocalTime] using
        (wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht.le)
    have hseg := wholeLineCauchyGlobalSegment_isClassicalSolution
      p hregime u₀ hu₀ n
    have hslice : wholeLineCauchyGlobalV p u₀ t =
        wholeLineCauchyGlobalSegmentV p u₀ n q := by
      funext y
      have hy := (wholeLineCauchyGlobalV_eventuallyEq_segment
        p hregime u₀ hu₀ ht y).eq_of_nhds
      simpa [n, a, q] using hy
    rw [hslice]
    exact hseg.v_smooth q x hq0 hqH
  · intro t x ht _htT
    let n := wholeLineCauchyGlobalIndex p u₀ t
    let a := (n : ℝ) * wholeLineCauchyGlobalStep p u₀
    let q := t - a
    have hq0 : 0 < q := by
      simpa [q, a, n, wholeLineCauchyGlobalLocalTime] using
        (wholeLineCauchyGlobalLocalTime_pos p u₀ ht)
    have hqH : q < wholeLineCauchyGlobalSegmentTime p u₀ := by
      simpa [q, a, n, wholeLineCauchyGlobalLocalTime] using
        (wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht.le)
    have hseg := wholeLineCauchyGlobalSegment_isClassicalSolution
      p hregime u₀ hu₀ n
    have hev := wholeLineCauchyGlobalU_eventuallyEq_segment
      p hregime u₀ hu₀ ht x
    have htime : deriv (fun s => wholeLineCauchyGlobalU p u₀ s x) t =
        deriv (fun r => wholeLineCauchyGlobalSegmentU p u₀ n r x) q := by
      calc
        deriv (fun s => wholeLineCauchyGlobalU p u₀ s x) t =
            deriv (fun s =>
              wholeLineCauchyGlobalSegmentU p u₀ n (s - a) x) t := by
                simpa [n, a] using hev.deriv_eq
        _ = deriv (fun r => wholeLineCauchyGlobalSegmentU p u₀ n r x) q := by
              simpa [q] using
                (deriv_comp_sub_const
                  (fun r => wholeLineCauchyGlobalSegmentU p u₀ n r x) a t)
    have hsliceU : wholeLineCauchyGlobalU p u₀ t =
        wholeLineCauchyGlobalSegmentU p u₀ n q := by
      funext y
      have hy := (wholeLineCauchyGlobalU_eventuallyEq_segment
        p hregime u₀ hu₀ ht y).eq_of_nhds
      simpa [n, a, q] using hy
    have hsliceV : wholeLineCauchyGlobalV p u₀ t =
        wholeLineCauchyGlobalSegmentV p u₀ n q := by
      funext y
      have hy := (wholeLineCauchyGlobalV_eventuallyEq_segment
        p hregime u₀ hu₀ ht y).eq_of_nhds
      simpa [n, a, q] using hy
    rw [htime, hsliceU, hsliceV]
    exact hseg.pde_u q x hq0 hqH
  · intro t x ht _htT
    let n := wholeLineCauchyGlobalIndex p u₀ t
    let a := (n : ℝ) * wholeLineCauchyGlobalStep p u₀
    let q := t - a
    have hq0 : 0 < q := by
      simpa [q, a, n, wholeLineCauchyGlobalLocalTime] using
        (wholeLineCauchyGlobalLocalTime_pos p u₀ ht)
    have hqH : q < wholeLineCauchyGlobalSegmentTime p u₀ := by
      simpa [q, a, n, wholeLineCauchyGlobalLocalTime] using
        (wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht.le)
    have hseg := wholeLineCauchyGlobalSegment_isClassicalSolution
      p hregime u₀ hu₀ n
    have hsliceU : wholeLineCauchyGlobalU p u₀ t =
        wholeLineCauchyGlobalSegmentU p u₀ n q := by
      funext y
      have hy := (wholeLineCauchyGlobalU_eventuallyEq_segment
        p hregime u₀ hu₀ ht y).eq_of_nhds
      simpa [n, a, q] using hy
    have hsliceV : wholeLineCauchyGlobalV p u₀ t =
        wholeLineCauchyGlobalSegmentV p u₀ n q := by
      funext y
      have hy := (wholeLineCauchyGlobalV_eventuallyEq_segment
        p hregime u₀ hu₀ ht y).eq_of_nhds
      simpa [n, a, q] using hy
    rw [hsliceU, hsliceV]
    exact hseg.pde_v q x hq0 hqH

theorem wholeLineCauchyGlobalBUC_zero
    (p : CMParams) (u₀ : WholeLineBUC) :
    wholeLineCauchyGlobalBUC p u₀ 0 = u₀ := by
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ)
      (wholeLineCauchyGlobalSegmentTime p u₀) :=
    ⟨le_rfl, (wholeLineCauchyGlobalSegmentTime_pos p u₀).le⟩
  have heq := wholeLineCauchyGlobalBUC_eq_segment p u₀ (t := 0) le_rfl
  have heq' : wholeLineCauchyGlobalBUC p u₀ 0 =
      wholeLineCauchyGlobalSegment p u₀ 0 ⟨0, hzero⟩ := by
    simpa [wholeLineCauchyGlobalIndex, wholeLineCauchyGlobalLocalTime] using heq
  have hinit : wholeLineCauchyGlobalSegment p u₀ 0 ⟨0, hzero⟩ = u₀ := by
    simpa [wholeLineCauchyGlobalSegment, wholeLineCauchyGlobalDatum] using
      (wholeLineCauchyBUCMildFixedPoint_initial
        p (wholeLineCauchyGlobalClamp_pos p u₀).le
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le u₀
        (wholeLineCauchyGlobalSegmentTime_rate p u₀) hzero)
  exact heq'.trans hinit

theorem wholeLineCauchyGlobal_hasInitialDatum
    (p : CMParams) (u₀ : WholeLineBUC) :
    HasInitialDatum (wholeLineCauchyGlobalU p u₀) u₀.1 := by
  intro x
  exact congrArg (fun w : WholeLineBUC => w.1 x)
    (wholeLineCauchyGlobalBUC_zero p u₀)

theorem wholeLineCauchyGlobal_hasUniformInitialTrace
    (p : CMParams) (u₀ : WholeLineBUC) :
    HasUniformInitialTrace (wholeLineCauchyGlobalU p u₀) u₀.1 := by
  let U := wholeLineCauchyGlobalSegment p u₀ 0
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ)
      (wholeLineCauchyGlobalSegmentTime p u₀) :=
    ⟨le_rfl, (wholeLineCauchyGlobalSegmentTime_pos p u₀).le⟩
  have hinit : U ⟨0, hzero⟩ = u₀ := by
    simpa [U, wholeLineCauchyGlobalSegment, wholeLineCauchyGlobalDatum] using
      (wholeLineCauchyBUCMildFixedPoint_initial
        p (wholeLineCauchyGlobalClamp_pos p u₀).le
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le u₀
        (wholeLineCauchyGlobalSegmentTime_rate p u₀) hzero)
  have htrace := wholeLineBUCTrajectoryExtend_hasUniformInitialTrace
    (wholeLineCauchyGlobalSegmentTime_pos p u₀).le U u₀ hinit
  intro ε hε
  rcases htrace ε hε with ⟨d, hd, hclose⟩
  refine ⟨min d (wholeLineCauchyGlobalStep p u₀),
    lt_min hd (wholeLineCauchyGlobalStep_pos p u₀), ?_⟩
  intro t x ht htd
  have htstep : t < wholeLineCauchyGlobalStep p u₀ :=
    htd.trans_le (min_le_right _ _)
  have heq := wholeLineCauchyGlobalBUC_eq_preferred_on_cell
    p u₀ 0 (t := t) (by
      simpa using (show t ∈ Set.Ico
        (((0 : ℕ) : ℝ) * wholeLineCauchyGlobalStep p u₀)
        ((((0 : ℕ) : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀) from
          ⟨by simpa using ht, by simpa using htstep⟩))
  have hpoint := congrArg (fun w : WholeLineBUC => w.1 x) heq
  rw [show wholeLineCauchyGlobalU p u₀ t x =
      (wholeLineBUCTrajectoryExtend
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le U t).1 x by
    simpa [wholeLineCauchyGlobalU, U] using hpoint]
  exact hclose t x ht (htd.trans_le (min_le_left _ _))

theorem wholeLineCauchyGlobal_nonnegative
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    0 ≤ wholeLineCauchyGlobalU p u₀ t x := by
  let n := wholeLineCauchyGlobalIndex p u₀ t
  let q := wholeLineCauchyGlobalLocalTime p u₀ t
  let z : Set.Icc (0 : ℝ) (wholeLineCauchyGlobalSegmentTime p u₀) :=
    ⟨q, wholeLineCauchyGlobalLocalTime_nonneg p u₀ ht,
      (wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht).le⟩
  have hbound :=
    (wholeLineCauchyGlobalDatum_segment_bounds p hregime u₀ hu₀ n).2.1 z x
  have heq := congrArg (fun w : WholeLineBUC => w.1 x)
    (wholeLineCauchyGlobalBUC_eq_segment p u₀ ht)
  have heq' : (wholeLineCauchyGlobalBUC p u₀ t).1 x =
      (wholeLineCauchyGlobalSegment p u₀ n z).1 x := by
    simpa [n, q, z] using heq
  change 0 ≤ (wholeLineCauchyGlobalBUC p u₀ t).1 x
  rw [heq']
  exact hbound.1

theorem wholeLineCauchyGlobal_le_stableCeiling
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    wholeLineCauchyGlobalU p u₀ t x ≤
      wholeLineCauchyStableCeiling p u₀ := by
  let n := wholeLineCauchyGlobalIndex p u₀ t
  let q := wholeLineCauchyGlobalLocalTime p u₀ t
  let z : Set.Icc (0 : ℝ) (wholeLineCauchyGlobalSegmentTime p u₀) :=
    ⟨q, wholeLineCauchyGlobalLocalTime_nonneg p u₀ ht,
      (wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht).le⟩
  have hbound :=
    (wholeLineCauchyGlobalDatum_segment_bounds p hregime u₀ hu₀ n).2.2 z x
  have heq := congrArg (fun w : WholeLineBUC => w.1 x)
    (wholeLineCauchyGlobalBUC_eq_segment p u₀ ht)
  have heq' : (wholeLineCauchyGlobalBUC p u₀ t).1 x =
      (wholeLineCauchyGlobalSegment p u₀ n z).1 x := by
    simpa [n, q, z] using heq
  change (wholeLineCauchyGlobalBUC p u₀ t).1 x ≤
    wholeLineCauchyStableCeiling p u₀
  rw [heq']
  exact hbound

section WholeLineCauchyGlobalGluingAxiomAudit

#print axioms wholeLineCauchyGlobalLocalTime_nonneg
#print axioms wholeLineCauchyGlobalLocalTime_lt_segmentTime
#print axioms wholeLineCauchyGlobalLocalTime_pos
#print axioms wholeLineCauchyGlobalBUC_eq_segment
#print axioms wholeLineCauchyGlobalIndex_eq_pred_of_mem_cell
#print axioms wholeLineCauchyGlobalSegment_overlap_apply
#print axioms wholeLineCauchyGlobalBUC_eq_preferred_on_cell
#print axioms wholeLineCauchyGlobalBUC_eq_next_on_cell
#print axioms wholeLineCauchyGlobalBUC_eventuallyEq_preferred
#print axioms wholeLineCauchyGlobalSegment_isClassicalSolution
#print axioms wholeLineCauchyGlobalU_eventuallyEq_segment
#print axioms wholeLineCauchyGlobalV_eventuallyEq_segment
#print axioms wholeLineCauchyGlobal_isGlobalClassicalSolution
#print axioms wholeLineCauchyGlobalBUC_zero
#print axioms wholeLineCauchyGlobal_hasInitialDatum
#print axioms wholeLineCauchyGlobal_hasUniformInitialTrace
#print axioms wholeLineCauchyGlobal_nonnegative
#print axioms wholeLineCauchyGlobal_le_stableCeiling

end WholeLineCauchyGlobalGluingAxiomAudit

end ShenWork.Paper1
