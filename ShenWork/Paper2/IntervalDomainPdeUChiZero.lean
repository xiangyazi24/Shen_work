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
import ShenWork.PDE.IntervalDuhamelClosedC2
import ShenWork.PDE.IntervalSourceCoefficientTimeC1

open Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift intervalDomain)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.IntervalSourceCoefficientTimeC1
  (restartCosineSeries_hasDerivAt_time localRestartCoeff)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)

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

/-- **Laplacian identity from the representation.**  If `lift (u t₀)` agrees on
`[0,1]` with the cosine series `∑ bₙ cosineMode n`, then at interior `x` the
laplacian is the spectral 2nd derivative (`cosineCoeffSeries_deriv2_eq`). -/
theorem laplacian_eq_of_rep {u : ℝ → intervalDomainPoint → ℝ} {t₀ : ℝ} {b : ℕ → ℝ}
    (hsum_b : Summable (fun n => unitIntervalCosineEigenvalue n * |b n|))
    (hrep : ∀ y ∈ Set.Icc (0:ℝ) 1,
      intervalDomainLift (u t₀) y = ∑' n, b n * cosineMode n y)
    {x : intervalDomainPoint} (hx : x.1 ∈ Set.Ioo (0:ℝ) 1) :
    intervalDomain.laplacian (u t₀) x
      = ∑' n, b n * (-(((n : ℝ) * Real.pi) ^ 2)
          * Real.cos ((n : ℝ) * Real.pi * x.1)) := by
  show deriv (fun y => deriv (intervalDomainLift (u t₀)) y) x.1 = _
  have hd1eq : Set.EqOn (deriv (intervalDomainLift (u t₀)))
      (deriv (fun y => ∑' n, b n * cosineMode n y)) (Set.Ioo (0:ℝ) 1) := fun z hz =>
    Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hz)
      (fun w hw => hrep w (Set.Ioo_subset_Icc_self hw)))
  rw [Filter.EventuallyEq.deriv_eq
    (Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx) hd1eq)]
  exact ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_deriv2_eq hsum_b x.1

/-- **Time-derivative identity from the representation.**  If `u s y` agrees near
`t₀` with the restart cosine series `∑ localRestartCoeff a₀ a (s−offset) n cos`,
the time derivative is the spectral series (`restartCosineSeries_hasDerivAt_time`
through the `s ↦ s−offset` chain rule). -/
theorem timeDeriv_eq_of_rep {u : ℝ → intervalDomainPoint → ℝ} {t₀ : ℝ}
    {a₀ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (ha₀ : ∀ n, |a₀ n| ≤ M)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a) {offset : ℝ} (hoff : 0 < t₀ - offset)
    (hrep : ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
      u s y = ∑' n, localRestartCoeff a₀ a (s - offset) n * cosineMode n y.1)
    (x : intervalDomainPoint) :
    intervalDomain.timeDeriv u t₀ x
      = ∑' n, (a (t₀ - offset) n - unitIntervalCosineEigenvalue n
          * localRestartCoeff a₀ a (t₀ - offset) n) * cosineMode n x.1 := by
  have hshift : HasDerivAt (fun s : ℝ => s - offset) 1 t₀ :=
    (hasDerivAt_id t₀).sub_const offset
  have hD := (restartCosineSeries_hasDerivAt_time hM ha₀ src hoff x.1).comp t₀ hshift
  have heq : (fun s => u s x) =ᶠ[𝓝 t₀]
      ((fun τ => ∑' n, localRestartCoeff a₀ a τ n * cosineMode n x.1)
        ∘ fun s => s - offset) := by
    filter_upwards [hrep] with s hs using hs x
  have hd := hD.congr_of_eventuallyEq heq
  show deriv (fun s => u s x) t₀ = _
  rw [hd.deriv, mul_one]

end ShenWork.IntervalDomainPdeUChiZero
