import ShenWork.PaperOne.WholeLineFrozenSignal
import ShenWork.PaperOne.WholeLineExponentialBarrierTrapping

open MeasureTheory Filter Topology Real

noncomputable section

namespace ShenWork.PaperOne

/-- If `U` is bounded, continuous, and nonnegative, then `U^gamma` is a valid
whole-line resolvent source. -/
theorem wholeLine_rpow_source_cunif_bdd
    {γ : ℝ} (hγ : 1 ≤ γ) {U : ℝ → ℝ}
    (hU_bdd : IsCUnifBdd U) (hU_nonneg : ∀ x, 0 ≤ U x) :
    IsCUnifBdd (fun y => (U y) ^ γ) := by
  rcases hU_bdd.2 with ⟨M, hM⟩
  have hγ_nonneg : 0 ≤ γ := le_trans zero_le_one hγ
  refine ⟨hU_bdd.1.rpow_const (fun _ => Or.inr hγ_nonneg), ⟨M ^ γ, ?_⟩⟩
  intro y
  rw [abs_of_nonneg (Real.rpow_nonneg (hU_nonneg y) γ)]
  exact Real.rpow_le_rpow (hU_nonneg y)
    (by simpa [abs_of_nonneg (hU_nonneg y)] using hM y) hγ_nonneg

/-- The diagonal frozen signal satisfies `V'' = V - U^gamma`. -/
theorem wholeLine_frozenSignal_second_deriv
    (p : CMParams) {U : ℝ → ℝ}
    (hU_bdd : IsCUnifBdd U) (hU_nonneg : ∀ x, 0 ≤ U x) (x : ℝ) :
    deriv (deriv (frozenSignal p.γ U)) x =
      frozenSignal p.γ U x - (U x) ^ p.γ := by
  unfold frozenSignal
  exact wholeLineResolvent_second_deriv
    (f := fun y => (U y) ^ p.γ)
    (wholeLine_rpow_source_cunif_bdd p.hγ hU_bdd hU_nonneg)
    (fun y => Real.rpow_nonneg (hU_nonneg y) p.γ) x

/-- The auxiliary expanded stationary operator on the diagonal
`V = frozenSignal gamma U`. -/
def wholeLineAuxStationaryOperator (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : ℝ → ℝ :=
  fun x =>
    iteratedDeriv 2 U x + c * deriv U x
      - p.χ * p.m * (U x) ^ (p.m - 1) * deriv U x *
          deriv (frozenSignal p.γ U) x
      - p.χ * (U x) ^ p.m * frozenSignal p.γ U x
      + p.χ * (U x) ^ (p.m + p.γ)
      + wholeLineReaction p U x

/-- The original divergence-form stationary wave operator on the diagonal
`V = frozenSignal gamma U`. -/
def wholeLineDivergenceStationaryOperator
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : ℝ → ℝ :=
  fun x =>
    iteratedDeriv 2 U x + c * deriv U x
      - p.χ *
          deriv (fun y => (U y) ^ p.m * deriv (frozenSignal p.γ U) y) x
      + wholeLineReaction p U x

def wholeLineAuxStationaryEquation
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ x, wholeLineAuxStationaryOperator p c U x = 0

def wholeLineDivergenceStationaryEquation
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ x, wholeLineDivergenceStationaryOperator p c U x = 0

theorem wholeLine_aux_operator_eq_residual
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) (x : ℝ) :
    wholeLineAuxStationaryOperator p c U x =
      auxiliaryStationaryResidual p c U (fun y => deriv U y)
        (fun y => iteratedDeriv 2 U y) (frozenSignal p.γ U)
        (fun y => deriv (frozenSignal p.γ U) y) x := by
  unfold wholeLineAuxStationaryOperator auxiliaryStationaryResidual
    auxiliaryFrozenNonlinearity wholeLineReaction
  ring

/-- Product rule plus the substitution `V'' = V - U^gamma` for the chemotactic
flux. -/
theorem wholeLine_flux_derivative_substitution
    (p : CMParams) {U V : ℝ → ℝ} (x : ℝ)
    (hU_nonneg : ∀ y, 0 ≤ U y)
    (hU_diff : DifferentiableAt ℝ U x)
    (hV_deriv_diff : DifferentiableAt ℝ (deriv V) x)
    (hVxx : deriv (deriv V) x = V x - (U x) ^ p.γ) :
    -p.χ * deriv (fun y => (U y) ^ p.m * deriv V y) x =
      -p.χ * p.m * (U x) ^ (p.m - 1) * deriv U x * deriv V x
        - p.χ * (U x) ^ p.m * V x
        + p.χ * (U x) ^ (p.m + p.γ) := by
  have hU_pow_deriv : HasDerivAt (fun y => (U y) ^ p.m)
      (deriv U x * p.m * (U x) ^ (p.m - 1)) x :=
    hU_diff.hasDerivAt.rpow_const (Or.inr p.hm)
  have hV_deriv : HasDerivAt (deriv V)
      (V x - (U x) ^ p.γ) x := by
    convert hV_deriv_diff.hasDerivAt using 1
    exact hVxx.symm
  have hprod := hU_pow_deriv.mul hV_deriv
  have hfun_eq :
      (fun y => (U y) ^ p.m * deriv V y) =
        (fun y => (U y) ^ p.m) * deriv V := by
    ext y
    simp [Pi.mul_apply]
  have hflux :
      deriv (fun y => (U y) ^ p.m * deriv V y) x =
        deriv U x * p.m * (U x) ^ (p.m - 1) * deriv V x
          + (U x) ^ p.m * (V x - (U x) ^ p.γ) := by
    rw [hfun_eq, hprod.deriv]
  have hpow_mγ :
      (U x) ^ p.m * (U x) ^ p.γ = (U x) ^ (p.m + p.γ) := by
    by_cases hUx_zero : U x = 0
    · have hm_pos : 0 < p.m := lt_of_lt_of_le zero_lt_one p.hm
      have hγ_pos : 0 < p.γ := lt_of_lt_of_le zero_lt_one p.hγ
      have hmγ_pos : 0 < p.m + p.γ := add_pos hm_pos hγ_pos
      rw [hUx_zero, Real.zero_rpow (ne_of_gt hm_pos),
        Real.zero_rpow (ne_of_gt hγ_pos), Real.zero_rpow (ne_of_gt hmγ_pos)]
      ring
    · have hUx_pos : 0 < U x := lt_of_le_of_ne (hU_nonneg x) (Ne.symm hUx_zero)
      rw [← Real.rpow_add hUx_pos]
  rw [hflux]
  calc
    -p.χ *
        (deriv U x * p.m * (U x) ^ (p.m - 1) * deriv V x
          + (U x) ^ p.m * (V x - (U x) ^ p.γ))
        =
          -p.χ * p.m * (U x) ^ (p.m - 1) * deriv U x * deriv V x
            - p.χ * (U x) ^ p.m * V x
            + p.χ * ((U x) ^ p.m * (U x) ^ p.γ) := by
          ring
    _ =
          -p.χ * p.m * (U x) ^ (p.m - 1) * deriv U x * deriv V x
            - p.χ * (U x) ^ p.m * V x
            + p.χ * (U x) ^ (p.m + p.γ) := by
          rw [hpow_mγ]

theorem wholeLine_frozenSignal_flux_identity
    (p : CMParams) {U : ℝ → ℝ} (x : ℝ)
    (hU_bdd : IsCUnifBdd U)
    (hU_nonneg : ∀ y, 0 ≤ U y)
    (hU_diff : DifferentiableAt ℝ U x)
    (hV_deriv_diff : DifferentiableAt ℝ (deriv (frozenSignal p.γ U)) x) :
    -p.χ *
        deriv (fun y => (U y) ^ p.m * deriv (frozenSignal p.γ U) y) x =
      -p.χ * p.m * (U x) ^ (p.m - 1) * deriv U x *
          deriv (frozenSignal p.γ U) x
        - p.χ * (U x) ^ p.m * frozenSignal p.γ U x
        + p.χ * (U x) ^ (p.m + p.γ) := by
  exact wholeLine_flux_derivative_substitution p (U := U)
    (V := frozenSignal p.γ U) x hU_nonneg hU_diff hV_deriv_diff
    (wholeLine_frozenSignal_second_deriv p hU_bdd hU_nonneg x)

theorem wholeLine_diagonal_stationary_pointwise
    (p : CMParams) {c : ℝ} {U : ℝ → ℝ} (x : ℝ)
    (hU_bdd : IsCUnifBdd U)
    (hU_nonneg : ∀ y, 0 ≤ U y)
    (hU_diff : DifferentiableAt ℝ U x)
    (hV_deriv_diff : DifferentiableAt ℝ (deriv (frozenSignal p.γ U)) x) :
    wholeLineDivergenceStationaryOperator p c U x =
      wholeLineAuxStationaryOperator p c U x := by
  have hflux := wholeLine_frozenSignal_flux_identity p x hU_bdd hU_nonneg
    hU_diff hV_deriv_diff
  unfold wholeLineDivergenceStationaryOperator wholeLineAuxStationaryOperator
  calc
    iteratedDeriv 2 U x + c * deriv U x
        - p.χ *
            deriv (fun y => (U y) ^ p.m * deriv (frozenSignal p.γ U) y) x
        + wholeLineReaction p U x
        =
      iteratedDeriv 2 U x + c * deriv U x
        + (-p.χ *
            deriv (fun y => (U y) ^ p.m * deriv (frozenSignal p.γ U) y) x)
        + wholeLineReaction p U x := by
          ring
    _ =
      iteratedDeriv 2 U x + c * deriv U x
        + (-p.χ * p.m * (U x) ^ (p.m - 1) * deriv U x *
              deriv (frozenSignal p.γ U) x
            - p.χ * (U x) ^ p.m * frozenSignal p.γ U x
            + p.χ * (U x) ^ (p.m + p.γ))
        + wholeLineReaction p U x := by
          rw [hflux]
    _ =
      iteratedDeriv 2 U x + c * deriv U x
        - p.χ * p.m * (U x) ^ (p.m - 1) * deriv U x *
            deriv (frozenSignal p.γ U) x
        - p.χ * (U x) ^ p.m * frozenSignal p.γ U x
        + p.χ * (U x) ^ (p.m + p.γ)
        + wholeLineReaction p U x := by
          ring

/-- On the diagonal `V = Psi(U^gamma)`, the auxiliary stationary equation is
equivalent to the original divergence-form wave equation. -/
theorem wholeLine_diagonal_stationary
    (p : CMParams) {c : ℝ} {U : ℝ → ℝ}
    (hU_bdd : IsCUnifBdd U)
    (hU_nonneg : ∀ y, 0 ≤ U y)
    (hU_diff : ∀ x, DifferentiableAt ℝ U x)
    (hV_deriv_diff : ∀ x, DifferentiableAt ℝ (deriv (frozenSignal p.γ U)) x) :
    wholeLineAuxStationaryEquation p c U ↔
      wholeLineDivergenceStationaryEquation p c U := by
  constructor
  · intro haux x
    rw [wholeLine_diagonal_stationary_pointwise p x hU_bdd hU_nonneg
      (hU_diff x) (hV_deriv_diff x)]
    exact haux x
  · intro hdiv x
    rw [← wholeLine_diagonal_stationary_pointwise p x hU_bdd hU_nonneg
      (hU_diff x) (hV_deriv_diff x)]
    exact hdiv x

section AxiomAudit

#print axioms wholeLine_frozenSignal_second_deriv
#print axioms wholeLine_flux_derivative_substitution
#print axioms wholeLine_frozenSignal_flux_identity
#print axioms wholeLine_diagonal_stationary

end AxiomAudit

end ShenWork.PaperOne
