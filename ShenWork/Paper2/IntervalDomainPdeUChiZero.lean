/-
  Additive: the χ₀=0 pointwise PDE bridge `hpde_u`.

  `∂ₜu = u_xx + reaction` (χ₀=0 drops the chemotaxis term), assembled from the
  three spectral identities — the time-derivative series
  (`restartCosineSeries_hasDerivAt_time`), the laplacian inversion
  (`cosineCoeffSeries_deriv2_eq`), and the source cosine inversion
  (`intervalCosine_hasSum_pointwise`).  This file proves the CORE algebraic
  combination; the three identities are supplied as hypotheses (each provable
  from the restart representation the ledger carries).

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.PDE.IntervalDomain
import ShenWork.Paper2.IntervalMildToClassical
import ShenWork.PDE.CosineSpectrum

open Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift intervalDomain)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)

noncomputable section

namespace ShenWork.IntervalDomainPdeUChiZero

/-- **`hpde_u` core (χ₀=0).**  The pointwise PDE from the three spectral identities:
`∂ₜu = ∑(srcₙ − λₙbₙ)cos`, `u_xx = ∑bₙ(−(nπ)²cos)`, `∑srcₙcos = reaction`. -/
theorem hpde_u_core (p : CM2Params) (hχ0 : p.χ₀ = 0)
    {u : ℝ → intervalDomainPoint → ℝ} {t₀ : ℝ} {x : intervalDomainPoint}
    {b src : ℕ → ℝ}
    (hsum_src : Summable (fun n => src n * cosineMode n x.1))
    (hsum_lb : Summable
      (fun n => unitIntervalCosineEigenvalue n * b n * cosineMode n x.1))
    (htime : intervalDomain.timeDeriv u t₀ x
        = ∑' n, (src n - unitIntervalCosineEigenvalue n * b n) * cosineMode n x.1)
    (hlap : intervalDomain.laplacian (u t₀) x
        = ∑' n, b n * (-(((n : ℝ) * Real.pi) ^ 2)
            * Real.cos ((n : ℝ) * Real.pi * x.1)))
    (hreact : (∑' n, src n * cosineMode n x.1)
        = u t₀ x * (p.a - p.b * (u t₀ x) ^ p.α)) :
    intervalDomain.timeDeriv u t₀ x
      = intervalDomain.laplacian (u t₀) x
        - p.χ₀ * intervalDomain.chemotaxisDiv p (u t₀)
            (mildChemicalConcentration p u t₀) x
        + u t₀ x * (p.a - p.b * (u t₀ x) ^ p.α) := by
  have hsplit : (∑' n, (src n - unitIntervalCosineEigenvalue n * b n) * cosineMode n x.1)
      = (∑' n, src n * cosineMode n x.1)
        - ∑' n, unitIntervalCosineEigenvalue n * b n * cosineMode n x.1 := by
    rw [← hsum_src.tsum_sub hsum_lb]
    exact tsum_congr (fun n => by ring)
  have hlap_eq : (∑' n, b n * (-(((n : ℝ) * Real.pi) ^ 2)
        * Real.cos ((n : ℝ) * Real.pi * x.1)))
      = -∑' n, unitIntervalCosineEigenvalue n * b n * cosineMode n x.1 := by
    rw [← tsum_neg]
    exact tsum_congr (fun n => by
      simp only [unitIntervalCosineEigenvalue, cosineMode]; ring)
  rw [hχ0, zero_mul, sub_zero, htime, hlap, hsplit, hreact, hlap_eq]; ring

end ShenWork.IntervalDomainPdeUChiZero
