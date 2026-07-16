import ShenWork.Paper1.WholeLineWeightedRegularityLeftTailBarrierNatural

open Filter Topology Set MeasureTheory Real

noncomputable section

namespace ShenWork.Paper1

/-!
# Scaled right-tail traps for the canonical Cauchy orbit

The paper's normalized wave trap fixes the coefficient of the right-tail
exponential to one.  A Cauchy slice naturally carries a scaled tail instead.
The elementary normalization below puts such a slice back into the committed
trap and records the exact scaling of its frozen elliptic resolver.  These are
the coefficient inputs for the matched-divergence positive-part comparison.
-/

/-- A uniform height bound and a faster exponential perturbation envelope
combine into the paper's scaled upper barrier.  The proof treats the two
halves of the line separately: the height bound controls the left half, while
the strict-or-equal exponent ordering controls the right half. -/
theorem le_scaledUpperBarrier_of_uniform_bound_and_weighted_envelope
    {q U : ℝ → ℝ} {kappa eta C S Q : ℝ}
    (hkappa : 0 < kappa) (hkappaEta : kappa ≤ eta)
    (hC : 0 ≤ C) (hQ : max S (1 + C) ≤ Q)
    (hqS : ∀ x, q x ≤ S)
    (hUexp : ∀ x, U x ≤ Real.exp (-kappa * x))
    (henv : ∀ x, |q x - U x| ≤ C * Real.exp (-eta * x)) :
    ∀ x, q x ≤ scaledUpperBarrier kappa Q x := by
  have hQoneC : 1 + C ≤ Q := (le_max_right S (1 + C)).trans hQ
  have hSQ : S ≤ Q := (le_max_left S (1 + C)).trans hQ
  have hQ0 : 0 ≤ Q := by linarith
  intro x
  apply le_min
  · exact (hqS x).trans hSQ
  · by_cases hx : 0 ≤ x
    · have hexp : Real.exp (-eta * x) ≤ Real.exp (-kappa * x) := by
        exact Real.exp_le_exp.mpr (by nlinarith)
      have hCexp : C * Real.exp (-eta * x) ≤
          C * Real.exp (-kappa * x) :=
        mul_le_mul_of_nonneg_left hexp hC
      calc
        q x ≤ U x + |q x - U x| := by
          linarith [le_abs_self (q x - U x)]
        _ ≤ Real.exp (-kappa * x) + C * Real.exp (-eta * x) :=
          add_le_add (hUexp x) (henv x)
        _ ≤ Real.exp (-kappa * x) + C * Real.exp (-kappa * x) :=
          add_le_add_right hCexp _
        _ = (1 + C) * Real.exp (-kappa * x) := by ring
        _ ≤ Q * Real.exp (-kappa * x) :=
          mul_le_mul_of_nonneg_right hQoneC (Real.exp_nonneg _)
    · have hx' : x ≤ 0 := le_of_not_ge hx
      have hexpOne : 1 ≤ Real.exp (-kappa * x) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by nlinarith)
      exact (hqS x).trans (hSQ.trans
        (by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hexpOne hQ0))

/-- Time-family wrapper for the scaled trap.  All constants are common on the
closed slab, which is the non-circular interface needed by the later barrier
comparison. -/
theorem inTimeWaveTrapSet_of_uniform_bound_and_weighted_envelope
    {q : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {kappa eta C S Q T : ℝ}
    (hkappa : 0 < kappa) (hkappaEta : kappa ≤ eta)
    (hC : 0 ≤ C) (hQ : max S (1 + C) ≤ Q)
    (hqC : ∀ t ∈ Set.Icc (0 : ℝ) T, IsCUnifBdd (q t))
    (hq0 : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 ≤ q t x)
    (hqS : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, q t x ≤ S)
    (hUexp : ∀ x, U x ≤ Real.exp (-kappa * x))
    (henv : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      |q t x - U x| ≤ C * Real.exp (-eta * x)) :
    InTimeWaveTrapSet kappa Q T q := by
  intro t ht
  refine ⟨hqC t ht, ?_⟩
  intro x
  exact ⟨hq0 t ht x,
    le_scaledUpperBarrier_of_uniform_bound_and_weighted_envelope
      hkappa hkappaEta hC hQ (hqS t ht) hUexp (henv t ht) x⟩

/-- A nonnegative profile bounded by both `M` and a scaled exponential becomes
a member of the normalized paper trap after division by the tail scale. -/
theorem inWaveTrapSet_div_of_uniform_and_scaled_exp_bounds
    {u : ℝ → ℝ} {kappa M Q : ℝ}
    (hQ : 0 < Q) (hu : IsCUnifBdd u)
    (hu0 : ∀ x, 0 ≤ u x)
    (huM : ∀ x, u x ≤ M)
    (huexp : ∀ x, u x ≤ Q * Real.exp (-kappa * x)) :
    InWaveTrapSet kappa (max 1 (M / Q)) (fun x => u x / Q) := by
  constructor
  · constructor
    · exact hu.1.div_const Q
    · rcases hu.2 with ⟨A, hA⟩
      refine ⟨A / |Q|, ?_⟩
      intro x
      rw [abs_div]
      exact div_le_div_of_nonneg_right (hA x) (abs_nonneg Q)
  · intro x
    constructor
    · exact div_nonneg (hu0 x) hQ.le
    · apply le_min
      · exact ((div_le_div_iff_of_pos_right hQ).2 (huM x)).trans
          (le_max_right _ _)
      · exact (div_le_iff₀ hQ).2 (by simpa [mul_comm] using huexp x)

/-- Exact homogeneity of the unit frozen elliptic resolver under a positive
amplitude normalization. -/
theorem frozenElliptic_eq_rpow_mul_div_profile
    (p : CMParams) {u : ℝ → ℝ} {Q : ℝ}
    (hQ : 0 < Q) (hu : ∀ x, 0 ≤ u x) (x : ℝ) :
    frozenElliptic p u x = Q ^ p.γ *
      frozenElliptic p (fun y => u y / Q) x := by
  unfold frozenElliptic Psi
  have hQ0 : 0 ≤ Q := hQ.le
  have hQpow : 0 < Q ^ p.γ := Real.rpow_pos_of_pos hQ _
  have hsource : ∀ y,
      (u y / Q) ^ p.γ = (u y) ^ p.γ / Q ^ p.γ := by
    intro y
    exact Real.div_rpow (hu y) hQ0 p.γ
  simp_rw [hsource]
  have hkernel :
      (fun y : ℝ => Real.exp (-Real.sqrt 1 * |x - y|) *
        ((u y) ^ p.γ / Q ^ p.γ)) =
      fun y : ℝ =>
        (Real.exp (-Real.sqrt 1 * |x - y|) * (u y) ^ p.γ) /
          Q ^ p.γ := by
    funext y
    ring
  rw [hkernel, MeasureTheory.integral_div]
  field_simp [ne_of_gt hQpow]

/-- The frozen resolver derivative has the same exact amplitude scaling. -/
theorem frozenElliptic_deriv_eq_rpow_mul_div_profile
    (p : CMParams) {u : ℝ → ℝ} {Q : ℝ}
    (hQ : 0 < Q) (hu : ∀ x, 0 ≤ u x) (x : ℝ) :
    deriv (frozenElliptic p u) x = Q ^ p.γ *
      deriv (frozenElliptic p (fun y => u y / Q)) x := by
  have hfun : frozenElliptic p u = fun z => Q ^ p.γ *
      frozenElliptic p (fun y => u y / Q) z := by
    funext z
    exact frozenElliptic_eq_rpow_mul_div_profile p hQ hu z
  rw [hfun, deriv_const_mul_field]

/-- Every slice of the paper's scaled finite-time trap becomes a normalized
coefficient-one wave-trap profile after division by its common scale. -/
theorem InTimeWaveTrapSet.div_slice_inWaveTrapSet_one
    {kappa M T : ℝ} {u : ℝ → ℝ → ℝ}
    (hM : 0 < M) (h : InTimeWaveTrapSet kappa M T u)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    InWaveTrapSet kappa 1 (fun x => u t x / M) := by
  have hraw := inWaveTrapSet_div_of_uniform_and_scaled_exp_bounds
    hM (h.slice_cunif ht) (fun x => h.nonneg ht x)
      (fun x => h.le_M ht x)
      (fun x => (h.le_scaledUpperBarrier ht x).trans
        (scaledUpperBarrier_le_scaled_exp kappa M x))
  simpa [div_self (ne_of_gt hM)] using hraw

/-- The three-case paper resolver tail estimate on a scaled time-trap slice.
The only change from the normalized estimate is the exact factor `M^gamma`. -/
theorem InTimeWaveTrapSet.frozenElliptic_deriv_abs_le_scaled_paper_bound
    (p : CMParams) {c kappa kappaTilde M T : ℝ}
    (hcond : PaperLemma42ExactConditions p c kappa kappaTilde 1)
    (hM : 0 < M) {u : ℝ → ℝ → ℝ}
    (h : InTimeWaveTrapSet kappa M T u)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    {x : ℝ} (hx : 0 ≤ x) :
    |deriv (frozenElliptic p (u t)) x| ≤
      M ^ p.γ * paperEllipticVxBound 1 kappa p.γ x := by
  have hnorm := h.div_slice_inWaveTrapSet_one hM ht
  have hbase :=
    (paperFrozenEllipticSourceBox_of_conditions hcond).right_tail_deriv
      (fun y => u t y / M) hnorm x hx
  rw [frozenElliptic_deriv_eq_rpow_mul_div_profile p hM
    (fun y => h.nonneg ht y) x, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hM.le p.γ)]
  exact mul_le_mul_of_nonneg_left hbase
    (Real.rpow_nonneg hM.le p.γ)

section AxiomAudit

#print axioms inWaveTrapSet_div_of_uniform_and_scaled_exp_bounds
#print axioms le_scaledUpperBarrier_of_uniform_bound_and_weighted_envelope
#print axioms inTimeWaveTrapSet_of_uniform_bound_and_weighted_envelope
#print axioms frozenElliptic_eq_rpow_mul_div_profile
#print axioms frozenElliptic_deriv_eq_rpow_mul_div_profile
#print axioms InTimeWaveTrapSet.div_slice_inWaveTrapSet_one
#print axioms
  InTimeWaveTrapSet.frozenElliptic_deriv_abs_le_scaled_paper_bound

end AxiomAudit

end ShenWork.Paper1
