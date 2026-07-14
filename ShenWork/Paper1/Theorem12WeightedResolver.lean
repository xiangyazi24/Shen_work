import ShenWork.Paper1.Lemma53Full

open MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-!
# The weighted elliptic-difference leaf for Paper 1 stability

`Lemma_5_3_proved` controls the Green potential of the power-source
difference.  The stability calculation is written instead with the difference
of the two frozen elliptic resolvers.  Linearity of `Psi` identifies those two
functions, so the following theorem exports the already-proved estimate in the
exact form consumed by the moving-frame energy identity.
-/

/-- Weighted `L²` control of both a frozen elliptic difference and the
derivative of its exponentially conjugated form.  This is the resolver leaf
used in the nonlinear remainder estimate following (5.31). -/
theorem weighted_frozenElliptic_difference_l2_bound
    (p : CMParams) {M eta : ℝ}
    (hM : 1 ≤ M) (heta_pos : 0 < eta) (heta_one : eta < 1)
    {u1 u2 : ℝ → ℝ}
    (hu1 : IsCUnifBdd u1) (hu2 : IsCUnifBdd u2)
    (hu1_mem : ∀ x, u1 x ∈ Set.Icc (0 : ℝ) M)
    (hu2_mem : ∀ x, u2 x ∈ Set.Icc (0 : ℝ) M)
    (hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2)) :
    let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
    let V := fun x => Real.exp (eta * x) *
      (frozenElliptic p u2 x - frozenElliptic p u1 x)
    (∫ x : ℝ, |V x| ^ 2 ≤
        p.γ ^ 2 * M ^ (2 * (p.γ - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
      (∫ x : ℝ, |deriv V x| ^ 2 ≤
        p.γ ^ 2 * M ^ (2 * (p.γ - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) := by
  have hraw := Lemma_5_3_proved p.γ M eta p.hγ hM
    heta_pos heta_one u1 u2 hu1 hu2 hu1_mem hu2_mem hclose
  have hpow1 : IsCUnifBdd (fun x => u1 x ^ p.γ) :=
    rpow_cunif_bdd_of_nonneg p hu1 (fun x => (hu1_mem x).1)
  have hpow2 : IsCUnifBdd (fun x => u2 x ^ p.γ) :=
    rpow_cunif_bdd_of_nonneg p hu2 (fun x => (hu2_mem x).1)
  have hsignal :
      (fun x => Psi (fun y => u2 y ^ p.γ - u1 y ^ p.γ) 1 1 x) =
        (fun x => frozenElliptic p u2 x - frozenElliptic p u1 x) := by
    funext x
    unfold frozenElliptic
    exact Psi_sub x
      (by simpa [Real.sqrt_one] using
        (Psi_kernel_integrable_of_isCUnifBdd one_pos hpow2 x))
      (by simpa [Real.sqrt_one] using
        (Psi_kernel_integrable_of_isCUnifBdd one_pos hpow1 x))
  have hpoint : ∀ x,
      Psi (fun y => u2 y ^ p.γ - u1 y ^ p.γ) 1 1 x =
        frozenElliptic p u2 x - frozenElliptic p u1 x :=
    fun x => congrFun hsignal x
  dsimp only at hraw ⊢
  simp_rw [hpoint] at hraw
  exact hraw

/-- The same frozen-resolver estimate together with the two square
integrability facts proved internally by Lemma 5.3.  Exporting the
integrability prevents later whole-line energy integrals from using
Mathlib's zero-by-convention value for non-integrable functions. -/
theorem weighted_frozenElliptic_difference_l2_data
    (p : CMParams) {M eta : ℝ}
    (hM : 1 ≤ M) (heta_pos : 0 < eta) (heta_one : eta < 1)
    {u1 u2 : ℝ → ℝ}
    (hu1 : IsCUnifBdd u1) (hu2 : IsCUnifBdd u2)
    (hu1_mem : ∀ x, u1 x ∈ Set.Icc (0 : ℝ) M)
    (hu2_mem : ∀ x, u2 x ∈ Set.Icc (0 : ℝ) M)
    (hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2)) :
    let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
    let V := fun x => Real.exp (eta * x) *
      (frozenElliptic p u2 x - frozenElliptic p u1 x)
    Integrable (fun x => V x ^ 2) ∧
      Integrable (fun x => deriv V x ^ 2) ∧
      (∫ x : ℝ, V x ^ 2) ≤
        p.γ ^ 2 * M ^ (2 * (p.γ - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, U x ^ 2 ∧
      (∫ x : ℝ, deriv V x ^ 2) ≤
        p.γ ^ 2 * M ^ (2 * (p.γ - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, U x ^ 2 := by
  dsimp only
  let s : ℝ → ℝ := fun x => u2 x ^ p.γ - u1 x ^ p.γ
  have hs : IsCUnifBdd s := by
    dsimp [s]
    exact rpow_difference_isCUnifBdd p.hγ hu1 hu2 hu1_mem hu2_mem
  have hsource := weighted_power_difference_sq_integrable_and_bound
    p.hγ (le_trans zero_le_one hM) hu1 hu2 hu1_mem hu2_mem hclose
  have hvalue := weighted_Psi_value_l2_bound
    heta_pos.le heta_one hs (by simpa [s] using hsource.1)
  have hderiv := weighted_Psi_deriv_l2_bound
    heta_pos heta_one hs (by simpa [s] using hsource.1)
  have hpow1 : IsCUnifBdd (fun x => u1 x ^ p.γ) :=
    rpow_cunif_bdd_of_nonneg p hu1 (fun x => (hu1_mem x).1)
  have hpow2 : IsCUnifBdd (fun x => u2 x ^ p.γ) :=
    rpow_cunif_bdd_of_nonneg p hu2 (fun x => (hu2_mem x).1)
  have hsignal :
      (fun x => Psi s 1 1 x) =
        (fun x => frozenElliptic p u2 x - frozenElliptic p u1 x) := by
    funext x
    dsimp [s]
    unfold frozenElliptic
    exact Psi_sub x
      (by simpa [Real.sqrt_one] using
        (Psi_kernel_integrable_of_isCUnifBdd one_pos hpow2 x))
      (by simpa [Real.sqrt_one] using
        (Psi_kernel_integrable_of_isCUnifBdd one_pos hpow1 x))
  have hweighted :
      (fun x => Real.exp (eta * x) * Psi s 1 1 x) =
        (fun x => Real.exp (eta * x) *
          (frozenElliptic p u2 x - frozenElliptic p u1 x)) := by
    funext x
    rw [congrFun hsignal x]
  have hVint : Integrable (fun x =>
      (Real.exp (eta * x) *
        (frozenElliptic p u2 x - frozenElliptic p u1 x)) ^ 2) := by
    refine hvalue.1.congr (Filter.Eventually.of_forall fun x => ?_)
    change |Real.exp (eta * x) * Psi s 1 1 x| ^ 2 =
      (Real.exp (eta * x) *
        (frozenElliptic p u2 x - frozenElliptic p u1 x)) ^ 2
    rw [sq_abs, congrFun hweighted x]
  have hVxint : Integrable (fun x =>
      deriv (fun z => Real.exp (eta * z) *
        (frozenElliptic p u2 z - frozenElliptic p u1 z)) x ^ 2) := by
    rw [← hweighted]
    simpa only [sq_abs] using hderiv.1
  have hbounds := weighted_frozenElliptic_difference_l2_bound p
    hM heta_pos heta_one hu1 hu2 hu1_mem hu2_mem hclose
  exact ⟨hVint, hVxint, by simpa only [sq_abs] using hbounds.1,
    by simpa only [sq_abs] using hbounds.2⟩

section Theorem12WeightedResolverAxiomAudit
#print axioms weighted_frozenElliptic_difference_l2_bound
#print axioms weighted_frozenElliptic_difference_l2_data
end Theorem12WeightedResolverAxiomAudit

end ShenWork.Paper1
