import ShenWork.PDE.IntervalDuhamelClosedC2

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalDuhamelClosedC2

noncomputable section

namespace ShenWork.Paper2.ParabolicGainInduction

/-- Spatial `C^k` for one interval slice, stated on the closed interval. -/
def SpatialSlice (k : ℕ) (w : intervalDomainPoint → ℝ) : Prop :=
  ContDiffOn ℝ (k : ℕ∞) (intervalDomainLift w) (Set.Icc (0 : ℝ) 1)

/-- Coupled bookkeeping: the elliptic variable is one spatial order ahead. -/
def CoupledSlice (k : ℕ)
    (u v : intervalDomainPoint → ℝ) : Prop :=
  SpatialSlice k u ∧ SpatialSlice (k + 1) v

/-- A relation saying that `w` is the Duhamel image of source `g`. -/
abbrev DuhamelImageRel :=
  (intervalDomainPoint → ℝ) → (intervalDomainPoint → ℝ) → Prop

/-- The exact higher-order parabolic gain missing from the current tree. -/
def DuhamelGainsTwo (Image : DuhamelImageRel) (m : ℕ) : Prop :=
  ∀ {g w : intervalDomainPoint → ℝ},
    Image g w → SpatialSlice m g → SpatialSlice (m + 2) w

/-- Non-circular step atoms for the regularity ladder. -/
structure ParabolicGainAtoms
    (U V F : ℕ → intervalDomainPoint → ℝ) : Prop where
  baseC2 : SpatialSlice 2 (U 2)
  resolverAhead :
    ∀ k, 2 ≤ k → k < 6 → SpatialSlice (k + 1) (V k)
  chemDivLosesOne :
    ∀ k, 2 ≤ k → k < 6 →
      CoupledSlice k (U k) (V k) → SpatialSlice (k - 1) (F k)
  duhamelGainsTwo :
    ∀ k, 2 ≤ k → k < 6 →
      SpatialSlice (k - 1) (F k) → SpatialSlice (k + 1) (U (k + 1))

/-- One non-circular induction step: previous order plus gain, no C2Coeff input. -/
theorem intervalIterate_contDiff_succ
    {U V F : ℕ → intervalDomainPoint → ℝ}
    (A : ParabolicGainAtoms U V F)
    {k : ℕ} (hk2 : 2 ≤ k) (hk6 : k < 6)
    (huk : SpatialSlice k (U k)) :
    SpatialSlice (k + 1) (U (k + 1)) :=
  A.duhamelGainsTwo k hk2 hk6
    (A.chemDivLosesOne k hk2 hk6
      ⟨huk, A.resolverAhead k hk2 hk6⟩)

/-- Climb from the committed `C²` base to `C⁶` by four successor steps. -/
theorem intervalIterate_contDiff_six
    {U V F : ℕ → intervalDomainPoint → ℝ}
    (A : ParabolicGainAtoms U V F) :
    SpatialSlice 6 (U 6) := by
  have h3 : SpatialSlice 3 (U 3) := by
    simpa using
      intervalIterate_contDiff_succ A
        (k := 2) (by norm_num) (by norm_num) A.baseC2
  have h4 : SpatialSlice 4 (U 4) := by
    simpa using
      intervalIterate_contDiff_succ A
        (k := 3) (by norm_num) (by norm_num) h3
  have h5 : SpatialSlice 5 (U 5) := by
    simpa using
      intervalIterate_contDiff_succ A
        (k := 4) (by norm_num) (by norm_num) h4
  have h6 : SpatialSlice 6 (U 6) := by
    simpa using
      intervalIterate_contDiff_succ A
        (k := 5) (by norm_num) (by norm_num) h5
  exact h6

/-- The committed Duhamel gain currently available in this tree is the C2 case. -/
theorem committedDuhamelGain_C0_to_C2
    {t : ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC1 a) (ht : 0 < t) :
    ContDiff ℝ 2
      (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          unitIntervalCosineHeatValue (t - s) (a s) x) :=
  (intervalDuhamelTerm_closedC2_of_timeC1_source src ht).1

end ShenWork.Paper2.ParabolicGainInduction
