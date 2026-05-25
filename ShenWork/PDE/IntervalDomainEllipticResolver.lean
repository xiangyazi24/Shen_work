import ShenWork.PDE.ResolventEstimate

/-!
Independent L2 lemmas for the interval-domain elliptic resolver.

The concrete Neumann elliptic resolver is diagonal in the cosine basis.  This
file records the Lipschitz part that follows directly from the existing
spectral resolvent estimate: the difference of two resolved coefficient
vectors is the resolvent of the coefficient difference.
-/

noncomputable section

namespace ShenWork.PDE.ResolventEstimate

/-- The diagonal shifted Neumann resolvent commutes with coefficient
subtraction. -/
theorem shiftedNeumannResolventCoeff_sub
    (ω : ℝ) (z : ℂ) (a b : ℕ → ℂ) (n : ℕ) :
    shiftedNeumannResolventCoeff ω z (fun k => a k - b k) n =
      shiftedNeumannResolventCoeff ω z a n -
        shiftedNeumannResolventCoeff ω z b n := by
  simp [shiftedNeumannResolventCoeff, mul_sub]

/-- Energy-form Lipschitz estimate for the diagonal shifted Neumann resolvent.

This is the coefficient-space resolver estimate needed for a Neumann elliptic
resolver `R`: the resolved difference is controlled by the input difference
with the same resolvent constant. -/
theorem shiftedNeumannResolventCoeff_l2_energy_lipschitz
    {ω : ℝ} (hω : 0 ≤ ω)
    {z : ℂ} (hzre : 0 ≤ z.re) (hz : z ≠ 0)
    {a b : ℕ → ℂ}
    (hab : Summable fun n : ℕ => ‖a n - b n‖ ^ 2) :
    coeffL2Energy
        (fun n : ℕ =>
          shiftedNeumannResolventCoeff ω z a n -
            shiftedNeumannResolventCoeff ω z b n) ≤
      ((1 : ℝ) / ‖z‖) ^ 2 *
        coeffL2Energy (fun n : ℕ => a n - b n) := by
  have hpoint :
      (fun n : ℕ =>
          shiftedNeumannResolventCoeff ω z a n -
            shiftedNeumannResolventCoeff ω z b n) =
        shiftedNeumannResolventCoeff ω z (fun n : ℕ => a n - b n) := by
    funext n
    rw [shiftedNeumannResolventCoeff_sub]
  rw [hpoint]
  exact intervalDomain_shiftedNeumannResolvent_estimate hω z hz hzre
    (fun n : ℕ => a n - b n) hab

/-- Norm-form Lipschitz estimate for the diagonal shifted Neumann resolvent. -/
theorem shiftedNeumannResolventCoeff_l2_norm_lipschitz
    {ω : ℝ} (hω : 0 ≤ ω)
    {z : ℂ} (hzre : 0 ≤ z.re) (hz : z ≠ 0)
    {a b : ℕ → ℂ}
    (hab : Summable fun n : ℕ => ‖a n - b n‖ ^ 2) :
    coeffL2Norm
        (fun n : ℕ =>
          shiftedNeumannResolventCoeff ω z a n -
            shiftedNeumannResolventCoeff ω z b n) ≤
      ((1 : ℝ) / ‖z‖) *
        coeffL2Norm (fun n : ℕ => a n - b n) := by
  have hpoint :
      (fun n : ℕ =>
          shiftedNeumannResolventCoeff ω z a n -
            shiftedNeumannResolventCoeff ω z b n) =
        shiftedNeumannResolventCoeff ω z (fun n : ℕ => a n - b n) := by
    funext n
    rw [shiftedNeumannResolventCoeff_sub]
  rw [hpoint]
  exact intervalDomain_shiftedNeumannResolvent_l2_norm_estimate hω z hz hzre
    (fun n : ℕ => a n - b n) hab

end ShenWork.PDE.ResolventEstimate
