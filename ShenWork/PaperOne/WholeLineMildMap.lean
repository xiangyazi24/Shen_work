import ShenWork.PDE.HeatSemigroup
import ShenWork.PaperOne.WholeLineResolvent

open MeasureTheory Filter Topology Real

noncomputable section

namespace ShenWork.PaperOne

/-- Whole-line heat operator `e^{t(Δ-I)}` used in Shen (3.1). -/
def wholeLineHeatOp (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  modifiedSemigroup t f x

/-- Whole-line spatial-gradient heat operator `∂ₓ e^{t(Δ-I)}` in kernel form. -/
def wholeLineHeatGradOp (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, Real.exp (-t) *
    (deriv (fun z : ℝ => heatKernel t (z - y)) x * f y)

/-- The chemotaxis flux `Q = U^m · ∂ₓ Ψ(U^γ)`. -/
def wholeLineFlux (p : CMParams) (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  (U x) ^ p.m * deriv (wholeLineResolvent (fun y => (U y) ^ p.γ)) x

/-- Logistic reaction source. -/
def wholeLineReaction (p : CMParams) (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  U x * (1 - (U x) ^ p.α)

def wholeLineFluxDuhamel (p : CMParams) (U : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  -p.χ * ∫ s in Set.Icc (0 : ℝ) t,
    wholeLineHeatGradOp (t - s) (wholeLineFlux p (U s)) x

def wholeLineReactionDuhamel (p : CMParams) (U : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  ∫ s in Set.Icc (0 : ℝ) t,
    wholeLineHeatOp (t - s) (wholeLineReaction p (U s)) x

/-- Shen (3.1), whole-line mild map with `χ ≤ 0` handled by assumptions downstream. -/
def wholeLineMildMap (p : CMParams) (u0 : ℝ → ℝ) (U : ℝ → ℝ → ℝ)
    (t x : ℝ) : ℝ :=
  wholeLineHeatOp t u0 x + wholeLineFluxDuhamel p U t x +
    wholeLineReactionDuhamel p U t x

theorem wholeLineHeatGradOp_eq_deriv_heatOp {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : Integrable f) (x : ℝ) :
    wholeLineHeatGradOp t f x = deriv (fun z => wholeLineHeatOp t f z) x := by
  unfold wholeLineHeatGradOp wholeLineHeatOp
  rw [deriv_modifiedSemigroup ht x hf, MeasureTheory.integral_const_mul]

theorem wholeLineHeatOp_interval_bound {f : ℝ → ℝ} {m M Mf t : ℝ}
    (hf_ge : ∀ x, m ≤ f x) (hf_le : ∀ x, f x ≤ M)
    (hf_bound : ∀ x, |f x| ≤ Mf)
    (hf_meas : AEStronglyMeasurable f volume) (ht : 0 < t) :
    ∀ x, Real.exp (-t) * m ≤ wholeLineHeatOp t f x ∧
      wholeLineHeatOp t f x ≤ Real.exp (-t) * M := by
  intro x
  simpa [wholeLineHeatOp] using
    modifiedSemigroup_interval_bound hf_ge hf_le hf_bound hf_meas ht x

theorem wholeLineReaction_le_barrier (p : CMParams) {U : ℝ → ℝ} {M : ℝ}
    (hU_nonneg : ∀ x, 0 ≤ U x) (hU_le : ∀ x, U x ≤ M) :
    ∀ x, wholeLineReaction p U x ≤ M := by
  intro x
  have hpow : 0 ≤ (U x) ^ p.α := Real.rpow_nonneg (hU_nonneg x) _
  have hfac : 1 - (U x) ^ p.α ≤ 1 := by linarith
  calc
    wholeLineReaction p U x = U x * (1 - (U x) ^ p.α) := rfl
    _ ≤ U x * 1 := mul_le_mul_of_nonneg_left hfac (hU_nonneg x)
    _ ≤ M := by simpa using hU_le x

/-- Exact correction estimates needed for constant-barrier invariance. -/
def WholeLineConstantBarrierCorrections (p : CMParams) (U : ℝ → ℝ → ℝ)
    (lo hi t x : ℝ) : Prop :=
  (1 - Real.exp (-t)) * lo ≤
      wholeLineFluxDuhamel p U t x + wholeLineReactionDuhamel p U t x ∧
    wholeLineFluxDuhamel p U t x + wholeLineReactionDuhamel p U t x ≤
      (1 - Real.exp (-t)) * hi

theorem wholeLineMildMap_mapsTo {p : CMParams} {u0 : ℝ → ℝ} {U : ℝ → ℝ → ℝ}
    {lo hi Mf t : ℝ}
    (hu0_ge : ∀ x, lo ≤ u0 x) (hu0_le : ∀ x, u0 x ≤ hi)
    (hu0_bound : ∀ x, |u0 x| ≤ Mf) (hu0_meas : AEStronglyMeasurable u0 volume)
    (ht : 0 < t)
    (hcorr : ∀ x, WholeLineConstantBarrierCorrections p U lo hi t x) :
    ∀ x, lo ≤ wholeLineMildMap p u0 U t x ∧
      wholeLineMildMap p u0 U t x ≤ hi := by
  intro x
  have hS := wholeLineHeatOp_interval_bound hu0_ge hu0_le hu0_bound hu0_meas ht x
  rcases hcorr x with ⟨hlo, hhi⟩
  constructor
  · unfold wholeLineMildMap
    linarith
  · unfold wholeLineMildMap
    linarith

#print axioms wholeLineHeatGradOp_eq_deriv_heatOp
#print axioms wholeLineMildMap_mapsTo

end ShenWork.PaperOne
