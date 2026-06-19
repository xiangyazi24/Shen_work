import ShenWork.PaperOne.WholeLineLongTimeMap
import ShenWork.PaperOne.WholeLineMildMapConcreteContinuity
import Mathlib.Tactic

open Filter Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/--
Right-tail smallness for the whole long-time orbit family.

This is the barrier-decay statement: uniformly in the trapped profile and in
time, the right spatial tail of the orbit, and also the right spatial tail of
the pointwise long-time profile, is small.
-/
def LongTimeMapRightUniformTail (κ κt D : ℝ)
    (w : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ R > 0, ∀ u, u ∈ WaveTrap κ κt D →
    (∀ t x, R ≤ x → |w u t x| < ε) ∧
      (∀ x, R ≤ x → |longTimeMap w u x| < ε)

/--
The right spatial tail follows immediately from the exponential upper barrier.

This is deliberately separate from `LongTimeMapUniformTail`: in the current
codebase that field means locally uniform convergence in time on finite
windows, not spatial tail decay.
-/
theorem longTime_uniform_tail_of_barrier
    {κ κt D : ℝ} {w : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    (hκ : 0 < κ)
    (hlower : ∀ u, u ∈ WaveTrap κ κt D →
      ∀ t x, lowerBarrier κ κt D x ≤ w u t x)
    (hupper : ∀ u, u ∈ WaveTrap κ κt D →
      ∀ t x, w u t x ≤ upperBarrier κ x) :
    LongTimeMapRightUniformTail κ κt D w := by
  intro ε hε
  have htail := upperBarrier_tendsto_zero_atTop (κ := κ) hκ
  rw [Metric.tendsto_atTop] at htail
  rcases htail ε hε with ⟨R0, hR0⟩
  let R : ℝ := max R0 0 + 1
  have hRpos : 0 < R := by
    dsimp [R]
    linarith [le_max_right R0 0]
  have hR0_le_R : R0 ≤ R := by
    dsimp [R]
    linarith [le_max_left R0 0]
  refine ⟨R, hRpos, ?_⟩
  intro u hu
  constructor
  · intro t x hx
    have hx0 : R0 ≤ x := le_trans hR0_le_R hx
    have hbar_lt : upperBarrier κ x < ε := by
      have hdist := hR0 x hx0
      simpa [Real.dist_eq, abs_of_nonneg (upperBarrier_nonneg κ x)] using hdist
    have hnonneg : 0 ≤ w u t x :=
      le_trans (lowerBarrier_nonneg κ κt D x) (hlower u hu t x)
    rw [abs_of_nonneg hnonneg]
    exact lt_of_le_of_lt (hupper u hu t x) hbar_lt
  · intro x hx
    have hx0 : R0 ≤ x := le_trans hR0_le_R hx
    have hbar_lt : upperBarrier κ x < ε := by
      have hdist := hR0 x hx0
      simpa [Real.dist_eq, abs_of_nonneg (upperBarrier_nonneg κ x)] using hdist
    have hlim_nonneg : 0 ≤ longTimeMap w u x := by
      simpa [longTimeMap] using
        le_trans (lowerBarrier_nonneg κ κt D x)
          (wholeLine_longTime_limit_lowerBarrier
            (κ := κ) (κt := κt) (D := D) (w := w u)
            (hlower u hu) x)
    rw [abs_of_nonneg hlim_nonneg]
    exact lt_of_le_of_lt
      (by
        simpa [longTimeMap] using
          wholeLine_longTime_limit_upperBarrier
            (κ := κ) (κt := κt) (D := D) (w := w u)
            (hlower u hu) (hupper u hu) x)
      hbar_lt

/-- The fixed-time long-time-flow continuity field, from the banked mild-map
decomposition continuity. -/
theorem longTime_finite_time_continuity_of_mildmap
    {κ κt D χ : ℝ} {w : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {semigroupTerm : ℝ → ℝ → ℝ}
    {chemDuhamel reactionDuhamel : ℝ → (ℝ → ℝ) → ℝ → ℝ}
    (hdecomp : ∀ t U x, w U t x =
      semigroupTerm t x + (-χ) * chemDuhamel t U x +
        reactionDuhamel t U x)
    (hchem : ∀ t,
      ShenWork.Paper1.LocalUniformContinuousOn
        (fun u => u ∈ WaveTrap κ κt D) (chemDuhamel t))
    (hreaction : ∀ t,
      ShenWork.Paper1.LocalUniformContinuousOn
        (fun u => u ∈ WaveTrap κ κt D) (reactionDuhamel t)) :
    LongTimeMapFiniteTimeContinuity κ κt D w :=
  longTimeMap_finiteTimeContinuity_of_mild_decomp
    (κ := κ) (κt := κt) (D := D) (χ := χ) (w := w)
    (semigroupTerm := semigroupTerm)
    (chemDuhamel := chemDuhamel)
    (reactionDuhamel := reactionDuhamel)
    hdecomp hchem hreaction

/-- Concrete profile-mild-map specialization of the fixed-time continuity
field.  The Duhamel term continuity hypotheses are exactly the banked
locally-uniform continuity inputs. -/
theorem longTime_finite_time_continuity_of_profile_mildmap
    (p : CMParams) (u0 : ℝ → ℝ) (κ κt D : ℝ)
    (hchem : ∀ t,
      ShenWork.Paper1.LocalUniformContinuousOn
        (fun u => u ∈ WaveTrap κ κt D)
        (ShenWork.Paper1.wholeLineProfileChemDuhamel p t))
    (hreaction : ∀ t,
      ShenWork.Paper1.LocalUniformContinuousOn
        (fun u => u ∈ WaveTrap κ κt D)
        (ShenWork.Paper1.wholeLineProfileReactionDuhamel p t)) :
    LongTimeMapFiniteTimeContinuity κ κt D
      (fun U t x => ShenWork.Paper1.wholeLineProfileMildMap p u0 t U x) := by
  refine longTime_finite_time_continuity_of_mildmap
    (κ := κ) (κt := κt) (D := D) (χ := p.χ)
    (w := fun U t x => ShenWork.Paper1.wholeLineProfileMildMap p u0 t U x)
    (semigroupTerm := fun t x => wholeLineHeatOp t u0 x)
    (chemDuhamel := fun t U x =>
      ShenWork.Paper1.wholeLineProfileChemDuhamel p t U x)
    (reactionDuhamel := fun t U x =>
      ShenWork.Paper1.wholeLineProfileReactionDuhamel p t U x)
    ?_ hchem hreaction
  intro t U x
  exact ShenWork.Paper1.wholeLineProfileMildMap_decomp p u0 t U x

/-- A locally uniform time limit of spatially continuous finite-time slices has
continuous long-time image profiles. -/
theorem longTime_image_continuity_of_uniform_time_limit
    {κ κt D : ℝ} {w : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    (hslice : ∀ u, u ∈ WaveTrap κ κt D → ∀ t, Continuous (w u t))
    (htail : LongTimeMapUniformTail κ κt D w) :
    LongTimeMapImageContinuity κ κt D w := by
  intro u hu
  rw [Metric.continuous_iff]
  intro x₀ ε hε
  set R : ℝ := |x₀| + 1 with hR_def
  have hR : 0 < R := by
    rw [hR_def]
    positivity
  have hx₀R : x₀ ∈ Icc (-R) R := by
    have hxabs : |x₀| ≤ R := by
      rw [hR_def]
      linarith
    exact abs_le.mp hxabs
  have hε3 : 0 < ε / 3 := by linarith
  rcases htail R hR (ε / 3) hε3 with ⟨τ, hτ⟩
  have hτu := hτ u hu
  have hslice_at := (hslice u hu τ).continuousAt (x := x₀)
  rw [Metric.continuousAt_iff] at hslice_at
  rcases hslice_at (ε / 3) hε3 with ⟨δ₁, hδ₁, hδslice⟩
  refine ⟨min δ₁ 1, by positivity, ?_⟩
  intro x hx
  have hx_lt_δ₁ : dist x x₀ < δ₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx_lt_one : dist x x₀ < 1 := lt_of_lt_of_le hx (min_le_right _ _)
  have hxR : x ∈ Icc (-R) R := by
    rw [Real.dist_eq] at hx_lt_one
    have hxabs : |x| ≤ R := by
      have h_abs := abs_sub_abs_le_abs_sub x x₀
      rw [hR_def]
      nlinarith [abs_nonneg (x - x₀), h_abs, le_of_lt hx_lt_one]
    exact abs_le.mp hxabs
  have e1 : |longTimeMap w u x - w u τ x| < ε / 3 := by
    simpa [abs_sub_comm] using hτu x hxR
  have e2 : |w u τ x - w u τ x₀| < ε / 3 := by
    rw [← Real.dist_eq]
    exact hδslice hx_lt_δ₁
  have e3 : |w u τ x₀ - longTimeMap w u x₀| < ε / 3 :=
    hτu x₀ hx₀R
  rw [Real.dist_eq]
  have hsplit :
      longTimeMap w u x - longTimeMap w u x₀ =
        (longTimeMap w u x - w u τ x) +
          (w u τ x - w u τ x₀) +
          (w u τ x₀ - longTimeMap w u x₀) := by
    ring
  rw [hsplit]
  have htri :
      |(longTimeMap w u x - w u τ x) +
          (w u τ x - w u τ x₀) +
          (w u τ x₀ - longTimeMap w u x₀)|
        ≤
          |longTimeMap w u x - w u τ x| +
            |w u τ x - w u τ x₀| +
            |w u τ x₀ - longTimeMap w u x₀| := by
    calc
      |(longTimeMap w u x - w u τ x) +
          (w u τ x - w u τ x₀) +
          (w u τ x₀ - longTimeMap w u x₀)|
          ≤
            |(longTimeMap w u x - w u τ x) +
              (w u τ x - w u τ x₀)| +
              |w u τ x₀ - longTimeMap w u x₀| := abs_add_le _ _
      _ ≤
            |longTimeMap w u x - w u τ x| +
              |w u τ x - w u τ x₀| +
              |w u τ x₀ - longTimeMap w u x₀| := by
          have h := abs_add_le
            (longTimeMap w u x - w u τ x) (w u τ x - w u τ x₀)
          linarith
  linarith

/-- The three continuity fields needed by `WholeLineTravelingWaveData`. -/
structure WholeLineLongTimeContinuityFields (κ κt D : ℝ)
    (w : (ℝ → ℝ) → ℝ → ℝ → ℝ) where
  longTime_image_continuity : LongTimeMapImageContinuity κ κt D w
  longTime_finite_time_continuity : LongTimeMapFiniteTimeContinuity κ κt D w
  longTime_uniform_tail : LongTimeMapUniformTail κ κt D w

/-- Package the data fields when finite-time mild continuity and the current
`LongTimeMapUniformTail` field are available. -/
def wholeLine_longTime_continuity_fields_of_mildmap
    {κ κt D χ : ℝ} {w : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {semigroupTerm : ℝ → ℝ → ℝ}
    {chemDuhamel reactionDuhamel : ℝ → (ℝ → ℝ) → ℝ → ℝ}
    (hdecomp : ∀ t U x, w U t x =
      semigroupTerm t x + (-χ) * chemDuhamel t U x +
        reactionDuhamel t U x)
    (hchem : ∀ t,
      ShenWork.Paper1.LocalUniformContinuousOn
        (fun u => u ∈ WaveTrap κ κt D) (chemDuhamel t))
    (hreaction : ∀ t,
      ShenWork.Paper1.LocalUniformContinuousOn
        (fun u => u ∈ WaveTrap κ κt D) (reactionDuhamel t))
    (hslice : ∀ u, u ∈ WaveTrap κ κt D → ∀ t, Continuous (w u t))
    (htail : LongTimeMapUniformTail κ κt D w) :
    WholeLineLongTimeContinuityFields κ κt D w where
  longTime_image_continuity :=
    longTime_image_continuity_of_uniform_time_limit hslice htail
  longTime_finite_time_continuity :=
    longTime_finite_time_continuity_of_mildmap hdecomp hchem hreaction
  longTime_uniform_tail := htail

#print axioms LongTimeMapRightUniformTail
#print axioms longTime_uniform_tail_of_barrier
#print axioms longTime_finite_time_continuity_of_mildmap
#print axioms longTime_finite_time_continuity_of_profile_mildmap
#print axioms longTime_image_continuity_of_uniform_time_limit
#print axioms WholeLineLongTimeContinuityFields
#print axioms wholeLine_longTime_continuity_fields_of_mildmap

end ShenWork.PaperOne
