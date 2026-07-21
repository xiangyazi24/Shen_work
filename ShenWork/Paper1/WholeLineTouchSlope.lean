import ShenWork.Paper1.WholeLineExpBarrierConsistency

/-!
# Touch-slope from the rate bound

At a touch of the lower exponential barrier `a t = 1 − D e^{−λt}`, the pointwise
`min_rise` at the argmin (delivered through Danskin as `da t ≥ R⁻`, with
`R⁻ = c'((1 − a) − θ(b − a))` the rate lower bound on the confined band) combines
with the barrier self-consistency `λ < c'(1 − 2θ)` to give the strict touch-slope
`λ D e^{−λt} < da t` required by `far_left_convergence_from_trajectories`.

This collapses two of the assembly's named obligations (touch-slope + barrier
consistency) into ONE: the Danskin rate bound `da ≥ R⁻`.  Verified 0/100k.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- **Lower touch-slope from the rate bound.**  On the confined band at a touch
of the lower barrier, `da t > λ D e^{−λt}`. -/
theorem touch_slope_lower
    {a b da cprime θ lam D t : ℝ}
    (hcp : 0 < cprime) (hθ0 : 0 ≤ θ) (hD : 0 < D)
    (hlam2 : lam < cprime * (1 - 2 * θ))
    (htouch : a = 1 - D * Real.exp (-lam * t))
    (hb : b ≤ 1 + D * Real.exp (-lam * t))
    (hrate : cprime * ((1 - a) - θ * (b - a)) ≤ da) :
    lam * (D * Real.exp (-lam * t)) < da := by
  have hexp : 0 < Real.exp (-lam * t) := Real.exp_pos _
  have hDe : 0 < D * Real.exp (-lam * t) := mul_pos hD hexp
  -- `1 − a = D e^{−λt}`, `b − a ≤ 2 D e^{−λt}`
  have h1a : 1 - a = D * Real.exp (-lam * t) := by rw [htouch]; ring
  have hba : b - a ≤ 2 * (D * Real.exp (-lam * t)) := by rw [htouch]; linarith
  -- `R⁻ ≥ c' D e^{−λt}(1 − 2θ)`
  have hR : cprime * (D * Real.exp (-lam * t) - θ * (2 * (D * Real.exp (-lam * t))))
      ≤ cprime * ((1 - a) - θ * (b - a)) := by
    apply mul_le_mul_of_nonneg_left _ hcp.le
    rw [h1a]
    have : θ * (b - a) ≤ θ * (2 * (D * Real.exp (-lam * t))) :=
      mul_le_mul_of_nonneg_left hba hθ0
    linarith
  -- barrier consistency: `λ D e^{−λt} < c' D e^{−λt}(1 − 2θ)`
  have hcons := symmetric_barrier_rate_ok hcp hD hlam2 t
  linarith [hcons, hR, hrate]

/-- **Upper touch-slope from the rate bound.**  On the confined band at a touch
of the upper barrier `b = 1 + D e^{−λt}`, `db t < −(λ D e^{−λt})`. -/
theorem touch_slope_upper
    {a b db cprime θ lam D t : ℝ}
    (hcp : 0 < cprime) (hθ0 : 0 ≤ θ) (hD : 0 < D)
    (hlam2 : lam < cprime * (1 - 2 * θ))
    (htouch : b = 1 + D * Real.exp (-lam * t))
    (ha : 1 - D * Real.exp (-lam * t) ≤ a)
    (hrate : db ≤ -(cprime * ((b - 1) - θ * (b - a)))) :
    db < -(lam * (D * Real.exp (-lam * t))) := by
  have hexp : 0 < Real.exp (-lam * t) := Real.exp_pos _
  have hDe : 0 < D * Real.exp (-lam * t) := mul_pos hD hexp
  have hb1 : b - 1 = D * Real.exp (-lam * t) := by rw [htouch]; ring
  have hba : b - a ≤ 2 * (D * Real.exp (-lam * t)) := by rw [htouch]; linarith
  have hR : cprime * (D * Real.exp (-lam * t) - θ * (2 * (D * Real.exp (-lam * t))))
      ≤ cprime * ((b - 1) - θ * (b - a)) := by
    apply mul_le_mul_of_nonneg_left _ hcp.le
    rw [hb1]
    have : θ * (b - a) ≤ θ * (2 * (D * Real.exp (-lam * t))) :=
      mul_le_mul_of_nonneg_left hba hθ0
    linarith
  have hcons := symmetric_barrier_rate_ok hcp hD hlam2 t
  linarith [hcons, hR, hrate]

section AxiomAudit

#print axioms touch_slope_lower
#print axioms touch_slope_upper

end AxiomAudit

end ShenWork.Paper1
