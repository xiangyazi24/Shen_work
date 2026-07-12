/-
  ShenWork/Paper3/IntervalDomainSpectralGapThreshold.lean

  **Fable roadmap L3 — the sharp spectral-gap threshold.**

  Linearizing the (v-eliminated) chemotaxis-growth system at the constant
  equilibrium diagonalizes in the Neumann cosine basis to
    φ_k' = σ_k φ_k,   σ_k = −λ_k(λ_k+μ−κ)/(λ_k+μ) − aα,
  with the single constant κ = χ₀·γν·u*^γ·(1+v*)^{−β}.  For k ≥ 1 the mode is
  stable (σ_k < 0) iff  κ·λ_k < (λ_k+μ)(λ_k+aα).  This file proves the sharp,
  parameter-free sufficient condition for ALL modes at once:
    κ < (√μ + √(aα))²   ⟹   κ·λ < (λ+μ)(λ+aα)  for every λ > 0,
  since (λ+μ)(λ+aα)/λ = λ + (μ+aα) + μaα/λ ≥ (√μ+√(aα))² by AM–GM.
  `(√μ+√(aα))² = μ + aα + 2√(μaα)` is the continuous minimum at λ = √(μaα),
  hence the sharp threshold `κ_crit` of the roadmap.  (No sectorial theory.)

  No `sorry`/`admit`/custom `axiom`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

namespace ShenWork.Paper3.SpectralGapThreshold

open Real

/-- **The sharp spectral-gap threshold (Fable L3 core).**  If `κ` is below the
critical value `(√μ + √c)²`, then for every `λ > 0` the diagonal stability
inequality `κ·λ < (λ+μ)(λ+c)` holds — so every Neumann mode is linearly stable.
Here `c = aα` (the linearized reaction damping) and `μ > 0` is the elliptic mass. -/
theorem kappa_lt_threshold_spectral_gap
    {μ c κ lam : ℝ} (hμ : 0 < μ) (hc : 0 < c) (hlam : 0 < lam)
    (hκ : κ < (Real.sqrt μ + Real.sqrt c) ^ 2) :
    κ * lam < (lam + μ) * (lam + c) := by
  have hμe : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ.le
  have hce : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  -- `(lam − √μ·√c)² ≥ 0`  ⟹  `lam² + μc ≥ 2·√μ·√c·lam`.
  have hsq : 0 ≤ (lam - Real.sqrt μ * Real.sqrt c) ^ 2 := sq_nonneg _
  -- `(√μ + √c)² = μ + c + 2·√μ·√c`.
  have hthr : (Real.sqrt μ + Real.sqrt c) ^ 2
      = μ + c + 2 * (Real.sqrt μ * Real.sqrt c) := by
    have : (Real.sqrt μ + Real.sqrt c) ^ 2
        = Real.sqrt μ ^ 2 + 2 * (Real.sqrt μ * Real.sqrt c) + Real.sqrt c ^ 2 := by
      ring
    rw [this, hμe, hce]; ring
  nlinarith [hsq, hμe, hce, hthr, hκ, mul_pos hlam (mul_pos (Real.sqrt_pos.mpr hμ)
    (Real.sqrt_pos.mpr hc)), hlam]

end ShenWork.Paper3.SpectralGapThreshold
