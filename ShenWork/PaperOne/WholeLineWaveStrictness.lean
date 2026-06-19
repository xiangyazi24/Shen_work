import ShenWork.PaperOne.WholeLineTravelingWave
import Mathlib.Tactic

noncomputable section

open Filter
open scoped Topology

namespace ShenWork.PaperOne

theorem upperBarrier_lt_one_of_pos {κ x : ℝ}
    (hκ : 0 < κ) (hx : 0 < x) :
    upperBarrier κ x < 1 := by
  rw [upperBarrier_eq_exp_of_nonneg hκ.le hx.le, Real.exp_lt_one_iff]
  nlinarith [mul_pos hκ hx]

/--
Strict positivity of a whole-line wave-trap profile.

The proof uses the strict right-tail squeeze from the exponential lower
barrier, then propagates one positive right-tail value back to any finite
point using antitonicity.
-/
theorem waveProfile_pos {κ κt D : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < κ) (hκt : κ < κt)
    (hU : U ∈ WaveTrap κ κt D) :
    ∀ x, 0 < U x := by
  intro x
  have hratio :
      Tendsto (fun y : ℝ => U y / Real.exp (-(κ * y))) atTop (𝓝 1) :=
    wholeLine_waveTrap_rightTail_ratio (κ := κ) (κt := κt)
      (D := D) hκ hκt hU
  have hpos_tail :
      ∀ᶠ y in atTop, 0 < U y / Real.exp (-(κ * y)) := by
    simpa [Set.mem_Ioi] using hratio (isOpen_Ioi.mem_nhds zero_lt_one)
  obtain ⟨y, hypos, hxy⟩ :=
    (hpos_tail.and (eventually_ge_atTop x)).exists
  have hden : 0 < Real.exp (-(κ * y)) := Real.exp_pos _
  have hUy : 0 < U y := by
    have hmul :
        0 < (U y / Real.exp (-(κ * y))) * Real.exp (-(κ * y)) :=
      mul_pos hypos hden
    rwa [div_mul_cancel₀ _ (ne_of_gt hden)] at hmul
  exact lt_of_lt_of_le hUy (hU.2 hxy)

/-- Strict upper bound on the positive spatial side, where the upper barrier is
the strict exponential branch. -/
theorem waveProfile_lt_one {κ κt D : ℝ} {U : ℝ → ℝ} {x : ℝ}
    (hκ : 0 < κ) (hx : 0 < x)
    (hU : U ∈ WaveTrap κ κt D) :
    U x < 1 :=
  lt_of_le_of_lt (hU.1 x).2 (upperBarrier_lt_one_of_pos hκ hx)

/-- Named carrier for the strict comparison/strong-maximum-principle input
needed to upgrade antitonicity to strict antitonicity. -/
structure WaveProfileStrictMonotonicityHyp (U : ℝ → ℝ) : Prop where
  strictAntitone : StrictAnti U

/-- Strict monotonicity, carried as a named hypothesis until the strong
comparison argument is available in this layer. -/
theorem waveProfile_strictAntitone {U : ℝ → ℝ}
    (hstrict : WaveProfileStrictMonotonicityHyp U) :
    StrictAnti U :=
  hstrict.strictAntitone

/-- If strict antitonicity is available, the upper bound is strict at every
finite point. -/
theorem waveProfile_lt_one_of_strictAntitone
    {κ κt D : ℝ} {U : ℝ → ℝ}
    (hU : U ∈ WaveTrap κ κt D)
    (hstrict : WaveProfileStrictMonotonicityHyp U) :
    ∀ x, U x < 1 := by
  intro x
  have hstep : x - 1 < x := by linarith
  have hlt : U x < U (x - 1) :=
    waveProfile_strictAntitone hstrict hstep
  exact lt_of_lt_of_le hlt (waveTrap_mem_le_one hU (x - 1))

#print axioms upperBarrier_lt_one_of_pos
#print axioms waveProfile_pos
#print axioms waveProfile_lt_one
#print axioms waveProfile_strictAntitone
#print axioms waveProfile_lt_one_of_strictAntitone

end ShenWork.PaperOne
