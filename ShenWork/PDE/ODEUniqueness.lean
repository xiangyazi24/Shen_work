import ShenWork.Paper2.Defs
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

noncomputable section

namespace ShenWork.Paper2

open Set
open scoped NNReal

/-- The scalar Bernoulli-logistic vector field `u' = u (a - b u^α)`. -/
def bernoulliLogisticVectorField (p : CM2Params) (u : ℝ) : ℝ :=
  u * (p.a - p.b * u ^ p.α)

/-- The scalar Bernoulli-decay vector field `u' = -b u^(α+1)`. -/
def bernoulliDecayVectorField (p : CM2Params) (u : ℝ) : ℝ :=
  u * (-(p.b * u ^ p.α))

lemma bernoulliLogisticVectorField_contDiffOn_Icc
    (p : CM2Params) {m M : ℝ} (hm : 0 < m) :
    ContDiffOn ℝ 1 (bernoulliLogisticVectorField p) (Icc m M) := by
  have hpow : ContDiffOn ℝ 1 (fun u : ℝ => u ^ p.α) (Icc m M) :=
    contDiffOn_fun_id.rpow_const_of_ne fun u hu =>
      ne_of_gt (lt_of_lt_of_le hm hu.1)
  have hinner :
      ContDiffOn ℝ 1 (fun u : ℝ => p.a - p.b * u ^ p.α) (Icc m M) :=
    contDiffOn_const.sub (contDiffOn_const.mul hpow)
  simpa [bernoulliLogisticVectorField] using contDiffOn_fun_id.mul hinner

lemma bernoulliLogisticVectorField_exists_lipschitzOnWith_Icc
    (p : CM2Params) {m M : ℝ} (hm : 0 < m) :
    ∃ K : ℝ≥0, LipschitzOnWith K (bernoulliLogisticVectorField p) (Icc m M) :=
  (bernoulliLogisticVectorField_contDiffOn_Icc p hm).exists_lipschitzOnWith
    one_ne_zero (convex_Icc m M) isCompact_Icc

lemma bernoulliDecayVectorField_contDiffOn_Icc
    (p : CM2Params) {m M : ℝ} (hm : 0 < m) :
    ContDiffOn ℝ 1 (bernoulliDecayVectorField p) (Icc m M) := by
  have hpow : ContDiffOn ℝ 1 (fun u : ℝ => u ^ p.α) (Icc m M) :=
    contDiffOn_fun_id.rpow_const_of_ne fun u hu =>
      ne_of_gt (lt_of_lt_of_le hm hu.1)
  have hinner :
      ContDiffOn ℝ 1 (fun u : ℝ => -(p.b * u ^ p.α)) (Icc m M) :=
    (contDiffOn_const.mul hpow).neg
  change ContDiffOn ℝ 1 (fun u : ℝ => u * (-(p.b * u ^ p.α))) (Icc m M)
  exact contDiffOn_fun_id.mul hinner

lemma bernoulliDecayVectorField_exists_lipschitzOnWith_Icc
    (p : CM2Params) {m M : ℝ} (hm : 0 < m) :
    ∃ K : ℝ≥0, LipschitzOnWith K (bernoulliDecayVectorField p) (Icc m M) :=
  (bernoulliDecayVectorField_contDiffOn_Icc p hm).exists_lipschitzOnWith
    one_ne_zero (convex_Icc m M) isCompact_Icc

/-- Picard-Lindelöf uniqueness for the Bernoulli-logistic scalar ODE on a
positive compact state interval.

Both curves solve `u' = u (a - b u^α)` with the same left-end initial value
and remain in `[m, M] ⊂ (0, ∞)` on the half-open time interval where the ODE is
used.  The conclusion is equality on the whole closed time interval. -/
theorem bernoulliLogistic_unique
    (p : CM2Params) {t₀ T m M : ℝ} (hm : 0 < m)
    {u w : ℝ → ℝ}
    (hu_cont : ContinuousOn u (Icc t₀ T))
    (hu_ode : ∀ t ∈ Ico t₀ T,
      HasDerivAt u (bernoulliLogisticVectorField p (u t)) t)
    (hu_mem : ∀ t ∈ Ico t₀ T, u t ∈ Icc m M)
    (hw_cont : ContinuousOn w (Icc t₀ T))
    (hw_ode : ∀ t ∈ Ico t₀ T,
      HasDerivAt w (bernoulliLogisticVectorField p (w t)) t)
    (hw_mem : ∀ t ∈ Ico t₀ T, w t ∈ Icc m M)
    (hinit : u t₀ = w t₀) :
    EqOn u w (Icc t₀ T) := by
  obtain ⟨K, hK⟩ :=
    bernoulliLogisticVectorField_exists_lipschitzOnWith_Icc p hm
  exact ODE_solution_unique_of_mem_Icc_right
    (v := fun _ : ℝ => bernoulliLogisticVectorField p)
    (s := fun _ : ℝ => Icc m M) (K := K)
    (fun _ _ => hK)
    hu_cont
    (fun t ht => (hu_ode t ht).hasDerivWithinAt)
    hu_mem
    hw_cont
    (fun t ht => (hw_ode t ht).hasDerivWithinAt)
    hw_mem
    hinit

/-- Picard-Lindelöf uniqueness for the Bernoulli pure-decay scalar ODE on a
positive compact state interval.

Both curves solve `u' = -b u^(α+1)`, written as `u' = u (-(b u^α))`,
with the same left-end initial value and remain in `[m, M] ⊂ (0, ∞)` on the
half-open time interval where the ODE is used. -/
theorem bernoulliDecay_unique
    (p : CM2Params) {t₀ T m M : ℝ} (hm : 0 < m)
    {u w : ℝ → ℝ}
    (hu_cont : ContinuousOn u (Icc t₀ T))
    (hu_ode : ∀ t ∈ Ico t₀ T,
      HasDerivAt u (bernoulliDecayVectorField p (u t)) t)
    (hu_mem : ∀ t ∈ Ico t₀ T, u t ∈ Icc m M)
    (hw_cont : ContinuousOn w (Icc t₀ T))
    (hw_ode : ∀ t ∈ Ico t₀ T,
      HasDerivAt w (bernoulliDecayVectorField p (w t)) t)
    (hw_mem : ∀ t ∈ Ico t₀ T, w t ∈ Icc m M)
    (hinit : u t₀ = w t₀) :
    EqOn u w (Icc t₀ T) := by
  obtain ⟨K, hK⟩ :=
    bernoulliDecayVectorField_exists_lipschitzOnWith_Icc p hm
  exact ODE_solution_unique_of_mem_Icc_right
    (v := fun _ : ℝ => bernoulliDecayVectorField p)
    (s := fun _ : ℝ => Icc m M) (K := K)
    (fun _ _ => hK)
    hu_cont
    (fun t ht => (hu_ode t ht).hasDerivWithinAt)
    hu_mem
    hw_cont
    (fun t ht => (hw_ode t ht).hasDerivWithinAt)
    hw_mem
    hinit

end ShenWork.Paper2

end
