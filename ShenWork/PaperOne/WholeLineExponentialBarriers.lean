import ShenWork.PaperOne.WaveSpeedExponent
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
noncomputable section
open Filter
open scoped Topology
namespace ShenWork.PaperOne
def upperBarrier (κ : ℝ) (x : ℝ) : ℝ := min 1 (Real.exp (-κ * x))
def lowerBarrier (κ κt D : ℝ) (x : ℝ) : ℝ :=
  max 0 (Real.exp (-κ * x) - D * Real.exp (-κt * x))
theorem upperBarrier_nonneg (κ x : ℝ) : 0 ≤ upperBarrier κ x :=
  le_min zero_le_one (Real.exp_pos _).le
theorem upperBarrier_le_one (κ x : ℝ) : upperBarrier κ x ≤ 1 := min_le_left _ _
theorem upperBarrier_eq_exp_of_nonneg {κ x : ℝ} (hκ : 0 ≤ κ) (hx : 0 ≤ x) :
    upperBarrier κ x = Real.exp (-κ * x) := by
  unfold upperBarrier; refine min_eq_right ?_
  rw [← Real.exp_zero, Real.exp_le_exp]; nlinarith [mul_nonneg hκ hx]
theorem upperBarrier_eq_one_of_nonpos {κ x : ℝ} (hκ : 0 ≤ κ) (hx : x ≤ 0) :
    upperBarrier κ x = 1 := by
  unfold upperBarrier; refine min_eq_left ?_
  rw [← Real.exp_zero, Real.exp_le_exp]
  exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hκ) hx
theorem upperBarrier_antitone {κ : ℝ} (hκ : 0 < κ) : Antitone (upperBarrier κ) := by
  intro x y hxy; unfold upperBarrier; refine min_le_min le_rfl ?_
  rw [Real.exp_le_exp]
  exact mul_le_mul_of_nonpos_left hxy (neg_nonpos.mpr hκ.le)
theorem lowerBarrier_nonneg (κ κt D x : ℝ) : 0 ≤ lowerBarrier κ κt D x := le_max_left _ _
theorem lowerBarrier_le_upper {κ κt D x : ℝ}
    (hκ : 0 ≤ κ) (hκt : κ < κt) (hD : 1 ≤ D) :
    lowerBarrier κ κt D x ≤ upperBarrier κ x := by
  unfold lowerBarrier upperBarrier
  by_cases hx : 0 ≤ x
  · have hprod : 0 ≤ D * Real.exp (-κt * x) :=
      mul_nonneg (by linarith) (Real.exp_pos _).le
    have hleExp :
        max 0 (Real.exp (-κ * x) - D * Real.exp (-κt * x)) ≤ Real.exp (-κ * x) :=
      max_le (Real.exp_pos _).le (sub_le_self _ hprod)
    have hexp1 : Real.exp (-κ * x) ≤ 1 := by
      rw [← Real.exp_zero, Real.exp_le_exp]
      nlinarith [mul_nonneg hκ hx]
    exact le_min (le_trans hleExp hexp1) hleExp
  · have hx0 : x ≤ 0 := le_of_not_ge hx
    have harg : -κ * x ≤ -κt * x := by
      have hm : κt * x ≤ κ * x := mul_le_mul_of_nonpos_right hκt.le hx0
      nlinarith
    have hexp : Real.exp (-κ * x) ≤ Real.exp (-κt * x) := by
      rwa [Real.exp_le_exp]
    have hDexp : Real.exp (-κt * x) ≤ D * Real.exp (-κt * x) := by
      simpa [one_mul] using mul_le_mul_of_nonneg_right hD (Real.exp_pos _).le
    have hdiff : Real.exp (-κ * x) - D * Real.exp (-κt * x) ≤ 0 := by
      linarith
    rw [max_eq_left hdiff]
    exact le_min zero_le_one (Real.exp_pos _).le
theorem upperBarrier_tendsto_zero_atTop {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (upperBarrier κ) atTop (𝓝 0) := by
  have hExp : Tendsto (fun x : ℝ => Real.exp (-κ * x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hκ))
  exact hExp.congr'
    (eventually_atTop.2 ⟨0, fun x hx => (upperBarrier_eq_exp_of_nonneg hκ.le hx).symm⟩)
theorem upperBarrier_eventually_one_atBot {κ : ℝ} (hκ : 0 ≤ κ) :
    ∀ᶠ x in atBot, upperBarrier κ x = 1 :=
  eventually_atBot.2 ⟨0, fun _ hx => upperBarrier_eq_one_of_nonpos hκ hx⟩
theorem barrier_squeeze {κ κt D ε : ℝ} {w : ℝ → ℝ} {x : ℝ}
    (hκ : 0 ≤ κ) (hx : 0 ≤ x)
    (hlo : lowerBarrier κ κt D x ≤ w x) (hhi : w x ≤ upperBarrier κ x)
    (htail : D * Real.exp (-(κt - κ) * x) ≤ ε) :
    1 - ε ≤ w x * Real.exp (κ * x) ∧ w x * Real.exp (κ * x) ≤ 1 := by
  have hbase : Real.exp (-κ * x) - D * Real.exp (-κt * x) ≤ w x := by
    exact le_trans (le_max_right _ _) hlo
  have hmul1 : Real.exp (-κ * x) * Real.exp (κ * x) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  have hmul2 :
      Real.exp (-κt * x) * Real.exp (κ * x) = Real.exp (-(κt - κ) * x) := by
    rw [← Real.exp_add]; congr 1; ring
  have hnorm :
      (Real.exp (-κ * x) - D * Real.exp (-κt * x)) * Real.exp (κ * x) =
        1 - D * Real.exp (-(κt - κ) * x) := by
    calc
      (Real.exp (-κ * x) - D * Real.exp (-κt * x)) * Real.exp (κ * x)
          = Real.exp (-κ * x) * Real.exp (κ * x) -
              D * (Real.exp (-κt * x) * Real.exp (κ * x)) := by ring
      _ = 1 - D * Real.exp (-(κt - κ) * x) := by rw [hmul1, hmul2]
  have hlower := mul_le_mul_of_nonneg_right hbase (Real.exp_pos (κ * x)).le
  constructor
  · rw [hnorm] at hlower; linarith
  · have hwu : w x ≤ Real.exp (-κ * x) := by
      simpa [upperBarrier_eq_exp_of_nonneg hκ hx] using hhi
    have hright := mul_le_mul_of_nonneg_right hwu (Real.exp_pos (κ * x)).le
    rwa [hmul1] at hright
theorem waveExponent_upperBarrier_antitone {c : ℝ} (hc : 2 ≤ c) :
    Antitone (upperBarrier (waveExponent c)) :=
  upperBarrier_antitone (waveExponent_pos hc)
#print axioms barrier_squeeze
#print axioms waveExponent_upperBarrier_antitone
end ShenWork.PaperOne
