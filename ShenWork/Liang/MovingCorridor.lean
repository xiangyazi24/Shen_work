/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import ShenWork.Liang.ModelAudit

/-!
# The favorable moving corridor

Long-time convergence to the far-right equilibrium can only be asserted for
observers whose speed is strictly larger than the habitat speed.  This file
formalizes that geometry for both fixed-speed observers and arbitrary point
sequences chosen from a linearly expanding favorable corridor.
-/

open Filter Set Topology

namespace ShenWork.Liang

noncomputable section

/-- The one-sided interior corridor between the habitat and an invasion front,
with a positive margin at each edge. -/
def favorableCorridor (c front ε : ℝ) (n : ℕ) : Set ℝ :=
  Set.Icc ((c + ε) * (n : ℝ)) ((front - ε) * (n : ℝ))

/-- The corrected corridor is nonempty when its two margins fit between the
habitat and front speeds. -/
theorem favorableCorridor_nonempty
    {c front ε : ℝ} (hgap : c + 2 * ε ≤ front) (n : ℕ) :
    (favorableCorridor c front ε n).Nonempty := by
  refine ⟨(c + ε) * (n : ℝ), le_rfl, ?_⟩
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  apply mul_le_mul_of_nonneg_right _ hn
  linarith

/-- Any sequence staying a linear distance ahead of the habitat samples
coordinates tending to positive infinity in the moving frame. -/
theorem aheadByLinearMargin_tendsto_atTop
    {x : ℕ → ℝ} {c ε : ℝ} (hε : 0 < ε)
    (hx : ∀ n : ℕ, (c + ε) * (n : ℝ) ≤ x n) :
    Tendsto (fun n : ℕ => x n - c * (n : ℝ)) atTop atTop := by
  have hbase :
      Tendsto (fun n : ℕ => ε * (n : ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hε).2 tendsto_natCast_atTop_atTop
  apply tendsto_atTop_mono (fun n => ?_) hbase
  nlinarith [hx n]

/-- Every arbitrary point sequence chosen from the favorable corridor samples
the far-right environmental limit. -/
theorem corridorSequence_environment_tendsto
    {ρ : ℝ → ℝ} {ρplus c front ε : ℝ} {x : ℕ → ℝ}
    (hρ : Tendsto ρ atTop (𝓝 ρplus)) (hε : 0 < ε)
    (hx : ∀ n : ℕ, x n ∈ favorableCorridor c front ε n) :
    Tendsto (fun n : ℕ => ρ (x n - c * (n : ℝ)))
      atTop (𝓝 ρplus) := by
  apply hρ.comp
  apply aheadByLinearMargin_tendsto_atTop hε
  exact fun n => (hx n).1

/-- A fixed observer speed in the corrected interval `(c, front)` samples the
far-right environmental limit. -/
theorem interiorObserver_environment_tendsto
    {ρ : ℝ → ℝ} {ρplus c front s : ℝ}
    (hρ : Tendsto ρ atTop (𝓝 ρplus)) (hcs : c < s)
    (_hsfront : s < front) :
    Tendsto (fun n : ℕ => ρ ((s - c) * (n : ℝ)))
      atTop (𝓝 ρplus) :=
  environmentAlongFasterObserver hρ hcs

section AxiomAudit

#print axioms favorableCorridor_nonempty
#print axioms corridorSequence_environment_tendsto
#print axioms interiorObserver_environment_tendsto

end AxiomAudit

end

end ShenWork.Liang
