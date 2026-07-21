import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Self-consistency of the symmetric exponential barriers

Fable R2 step 3 (2026-07-21): with the rate lower bound at an interior minimum of
value `a` in a band `[a,b]`,

`R⁻(a,b) ≥ c' · ((1 − a) − θ (b − a))`,

the symmetric exponential barriers `α(t) = 1 − D e^{−λt}`, `β(t) = 1 + D e^{−λt}`
(so `1 − α = β − 1 = D e^{−λt}`, `β − α = 2 D e^{−λt}`) satisfy the STRICT
sub-solution inequality `α'(t) < R⁻(α(t), β(t))` at every `t` exactly when

`λ < c' (1 − 2θ)`,

which admits a positive `λ` iff `θ < 1/2` — precisely the two-sided threshold
`χ < χ_max ≈ √(c/2)` (`θ = χ K / (1−a)`-type collects the chemotaxis/resolver
terms).  This file proves that algebraic self-consistency; the barriers then feed
the (deferred) first-touch comparison lemma, whose output feeds
`uniform_convergence_of_expBarrier`.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- `α'(t) = λ D e^{−λt}` (the barrier's time-derivative). -/
theorem expBarrier_deriv {D lam : ℝ} (t : ℝ) :
    HasDerivAt (fun t => 1 - D * Real.exp (-lam * t))
      (lam * (D * Real.exp (-lam * t))) t := by
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-lam * t))
      (Real.exp (-lam * t) * (-lam)) t := by
    have h := (((hasDerivAt_id t).const_mul (-lam))).exp
    simpa using h
  have h2 : HasDerivAt (fun t => D * Real.exp (-lam * t))
      (D * (Real.exp (-lam * t) * (-lam))) t := hexp.const_mul D
  have h3 := (hasDerivAt_const t (1:ℝ)).sub h2
  convert h3 using 1
  ring

/-- **Strict barrier self-consistency.**  For `c' > 0`, `θ < 1/2`, `D > 0`, and any
`0 < λ < c'(1 − 2θ)`, the symmetric exponential barrier's slope `λ D e^{−λt}` is
strictly below the rate lower bound `c'((1−α) − θ(β−α))` at every `t`. -/
theorem symmetric_barrier_rate_ok
    {cprime θ lam D : ℝ} (_hcp : 0 < cprime) (hD : 0 < D)
    (hlam2 : lam < cprime * (1 - 2 * θ)) (t : ℝ) :
    lam * (D * Real.exp (-lam * t))
      < cprime * ((D * Real.exp (-lam * t))
          - θ * (2 * D * Real.exp (-lam * t))) := by
  have hexp : 0 < Real.exp (-lam * t) := Real.exp_pos _
  have hDe : 0 < D * Real.exp (-lam * t) := mul_pos hD hexp
  -- RHS = c'(1−2θ)·(D e^{−λt}), LHS = λ·(D e^{−λt}); divide by the positive factor
  have hrhs : cprime * ((D * Real.exp (-lam * t))
      - θ * (2 * D * Real.exp (-lam * t)))
      = (cprime * (1 - 2 * θ)) * (D * Real.exp (-lam * t)) := by ring
  rw [hrhs]
  exact mul_lt_mul_of_pos_right hlam2 hDe

/-- A positive barrier rate `λ` exists iff `θ < 1/2`. -/
theorem exists_barrier_rate_iff {cprime θ : ℝ} (hcp : 0 < cprime) :
    (∃ lam : ℝ, 0 < lam ∧ lam < cprime * (1 - 2 * θ)) ↔ θ < 1 / 2 := by
  constructor
  · rintro ⟨lam, hlam0, hlam2⟩
    have hpos : 0 < cprime * (1 - 2 * θ) := lt_trans hlam0 hlam2
    -- `c' > 0` and `c'(1−2θ) > 0` force `1 − 2θ > 0`
    have h1 : 0 < 1 - 2 * θ := by
      by_contra hcon
      push_neg at hcon
      exact absurd hpos (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hcp.le hcon))
    linarith
  · intro h
    have h1 : 0 < 1 - 2 * θ := by linarith
    have hpos : 0 < cprime * (1 - 2 * θ) := mul_pos hcp h1
    exact ⟨cprime * (1 - 2 * θ) / 2, by linarith, by linarith⟩

section AxiomAudit

#print axioms symmetric_barrier_rate_ok
#print axioms exists_barrier_rate_iff

end AxiomAudit

end ShenWork.Paper1
