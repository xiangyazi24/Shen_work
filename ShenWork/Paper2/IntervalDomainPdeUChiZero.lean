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
import ShenWork.PDE.IntervalCosineInversion
import ShenWork.Paper2.IntervalMildPicardRegularity

open Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift intervalDomain)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.IntervalSourceCoefficientTimeC1
  (restartCosineSeries_hasDerivAt_time localRestartCoeff)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalMildPicardRegularity (logisticSourceFun)
open ShenWork.IntervalCosineInversion (intervalCosine_hasSum_pointwise reflCircle)

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

/-- **Source inversion = reaction (lift-pinned form).**  If the source coefficients
are the cosine coefficients of the logistic source of `u t₀` and that source is
continuous with summable `reflCircle` Fourier coefficients, the source cosine series
sums to the pointwise reaction (`intervalCosine_hasSum_pointwise`).  (Retained for
the downstream `Thm11ChiZeroFinal` consumer whose `hpdeData` carries those facts as
assumed fields.) -/
theorem source_inversion_eq_reaction (p : CM2Params)
    {u : ℝ → intervalDomainPoint → ℝ} {t₀ : ℝ} {src : ℕ → ℝ}
    (hsrc_coeff : ∀ n, src n
        = cosineCoeffs (logisticSourceFun p.a p.b p.α (intervalDomainLift (u t₀))) n)
    (hcont : Continuous (logisticSourceFun p.a p.b p.α (intervalDomainLift (u t₀))))
    (hsum_fourier : Summable (fun n : ℤ => fourierCoeff
        (reflCircle (logisticSourceFun p.a p.b p.α (intervalDomainLift (u t₀)))) n))
    {x : intervalDomainPoint} (hx : x.1 ∈ Set.Ioo (0:ℝ) 1) :
    (∑' n, src n * cosineMode n x.1) = u t₀ x * (p.a - p.b * (u t₀ x) ^ p.α) := by
  have hinv := intervalCosine_hasSum_pointwise
    (logisticSourceFun p.a p.b p.α (intervalDomainLift (u t₀))) hcont hx hsum_fourier
  have hux : intervalDomainLift (u t₀) x.1 = u t₀ x := by
    simp only [intervalDomainLift]; exact dif_pos x.2
  have hsum_eq : (∑' n, src n * cosineMode n x.1)
      = logisticSourceFun p.a p.b p.α (intervalDomainLift (u t₀)) x.1 := by
    rw [← hinv.tsum_eq]
    refine tsum_congr (fun n => ?_)
    rw [hsrc_coeff n]
    simp only [cosineMode, unitIntervalCosineMode]; ring
  rw [hsum_eq]; simp only [logisticSourceFun, hux]

/-- **Source inversion = reaction (continuous-surrogate form).**  Same conclusion
from a CONTINUOUS surrogate `g` that agrees on `[0,1]` with the logistic source of
`u t₀`.  The inversion `intervalCosine_hasSum_pointwise` for the continuous `g` gives
`∑ cosineCoeffs g · cos = g x`; the `[0,1]` agreement (interior `x ∈ (0,1) ⊂ [0,1]`)
turns `g x` into the lift's logistic source value `= reaction`.  This is the honest
form that avoids the FALSE `Continuous (lift)`. -/
theorem source_inversion_eq_reaction_surrogate (p : CM2Params)
    {u : ℝ → intervalDomainPoint → ℝ} {t₀ : ℝ} {src : ℕ → ℝ} {g : ℝ → ℝ}
    (hcont : Continuous g)
    (hgeq : Set.EqOn g (logisticSourceFun p.a p.b p.α (intervalDomainLift (u t₀)))
        (Set.Icc (0:ℝ) 1))
    (hsum_fourier : Summable (fun n : ℤ => fourierCoeff (reflCircle g) n))
    (hsrc_coeff : ∀ n, src n = cosineCoeffs g n)
    {x : intervalDomainPoint} (hx : x.1 ∈ Set.Ioo (0:ℝ) 1) :
    (∑' n, src n * cosineMode n x.1) = u t₀ x * (p.a - p.b * (u t₀ x) ^ p.α) := by
  have hinv := intervalCosine_hasSum_pointwise g hcont hx hsum_fourier
  have hux : intervalDomainLift (u t₀) x.1 = u t₀ x := by
    simp only [intervalDomainLift]; exact dif_pos x.2
  -- `g x = logisticSourceFun … (lift (u t₀)) x.1` at interior `x` (⊂ [0,1])
  have hgx : g x.1
      = logisticSourceFun p.a p.b p.α (intervalDomainLift (u t₀)) x.1 :=
    hgeq (Set.Ioo_subset_Icc_self hx)
  have hsum_eq : (∑' n, src n * cosineMode n x.1) = g x.1 := by
    rw [← hinv.tsum_eq]
    refine tsum_congr (fun n => ?_)
    rw [hsrc_coeff n]
    simp only [cosineMode, unitIntervalCosineMode]; ring
  rw [hsum_eq, hgx]; simp only [logisticSourceFun, hux]

/-- **`hpde_u` (χ₀=0) from the restart representation (lift-pinned form).**
Assembles the three identities: at interior `x`, `∂ₜu = u_xx + reaction` (the χ₀=0
ledger PDE).  Retained with the original signature for `Thm11ChiZeroFinal`. -/
theorem hpde_u_of_representation (p : CM2Params) (hχ0 : p.χ₀ = 0)
    {u : ℝ → intervalDomainPoint → ℝ} {t₀ : ℝ}
    {a₀ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (ha₀ : ∀ n, |a₀ n| ≤ M)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a) {offset : ℝ} (hoff : 0 < t₀ - offset)
    (hrep : ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
      u s y = ∑' n, localRestartCoeff a₀ a (s - offset) n * cosineMode n y.1)
    (hsrc_coeff : ∀ n, a (t₀ - offset) n
        = cosineCoeffs (logisticSourceFun p.a p.b p.α (intervalDomainLift (u t₀))) n)
    (hcont : Continuous (logisticSourceFun p.a p.b p.α (intervalDomainLift (u t₀))))
    (hsum_fourier : Summable (fun n : ℤ => fourierCoeff
        (reflCircle (logisticSourceFun p.a p.b p.α (intervalDomainLift (u t₀)))) n))
    (hsum_b : Summable (fun n => unitIntervalCosineEigenvalue n
        * |localRestartCoeff a₀ a (t₀ - offset) n|))
    {x : intervalDomainPoint} (hx : x.1 ∈ Set.Ioo (0:ℝ) 1)
    (hsum_src : Summable (fun n => a (t₀ - offset) n * cosineMode n x.1))
    (hsum_lb : Summable (fun n => unitIntervalCosineEigenvalue n
        * localRestartCoeff a₀ a (t₀ - offset) n * cosineMode n x.1)) :
    intervalDomain.timeDeriv u t₀ x
      = intervalDomain.laplacian (u t₀) x
        - p.χ₀ * intervalDomain.chemotaxisDiv p (u t₀)
            (mildChemicalConcentration p u t₀) x
        + u t₀ x * (p.a - p.b * (u t₀ x) ^ p.α) := by
  have hrep_real : ∀ z ∈ Set.Icc (0:ℝ) 1,
      intervalDomainLift (u t₀) z
        = ∑' n, localRestartCoeff a₀ a (t₀ - offset) n * cosineMode n z := by
    intro z hz
    rw [intervalDomainLift, dif_pos hz]
    exact hrep.self_of_nhds ⟨z, hz⟩
  exact hpde_u_core p hχ0
    (b := fun n => localRestartCoeff a₀ a (t₀ - offset) n)
    (src := fun n => a (t₀ - offset) n) hsum_src hsum_lb
    (timeDeriv_eq_of_rep hM ha₀ src hoff hrep x)
    (laplacian_eq_of_rep hsum_b hrep_real hx)
    (source_inversion_eq_reaction p hsrc_coeff hcont hsum_fourier hx)

/-- **`hpde_u` (χ₀=0) from the restart representation (continuous-surrogate form).**
Same conclusion, but the source inversion is fed a CONTINUOUS surrogate `g` agreeing
with the logistic source on `[0,1]` (no FALSE `Continuous (lift)`).  This is the form
consumed by `IntervalDomainPdeUProducer.mildSolution_pde_u_of_spectral`. -/
theorem hpde_u_of_representation_surrogate (p : CM2Params) (hχ0 : p.χ₀ = 0)
    {u : ℝ → intervalDomainPoint → ℝ} {t₀ : ℝ}
    {a₀ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (ha₀ : ∀ n, |a₀ n| ≤ M)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a) {offset : ℝ} (hoff : 0 < t₀ - offset)
    (hrep : ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
      u s y = ∑' n, localRestartCoeff a₀ a (s - offset) n * cosineMode n y.1)
    {g : ℝ → ℝ}
    (hcont : Continuous g)
    (hgeq : Set.EqOn g (logisticSourceFun p.a p.b p.α (intervalDomainLift (u t₀)))
        (Set.Icc (0:ℝ) 1))
    (hsum_fourier : Summable (fun n : ℤ => fourierCoeff (reflCircle g) n))
    (hsrc_coeff : ∀ n, a (t₀ - offset) n = cosineCoeffs g n)
    (hsum_b : Summable (fun n => unitIntervalCosineEigenvalue n
        * |localRestartCoeff a₀ a (t₀ - offset) n|))
    {x : intervalDomainPoint} (hx : x.1 ∈ Set.Ioo (0:ℝ) 1)
    (hsum_src : Summable (fun n => a (t₀ - offset) n * cosineMode n x.1))
    (hsum_lb : Summable (fun n => unitIntervalCosineEigenvalue n
        * localRestartCoeff a₀ a (t₀ - offset) n * cosineMode n x.1)) :
    intervalDomain.timeDeriv u t₀ x
      = intervalDomain.laplacian (u t₀) x
        - p.χ₀ * intervalDomain.chemotaxisDiv p (u t₀)
            (mildChemicalConcentration p u t₀) x
        + u t₀ x * (p.a - p.b * (u t₀ x) ^ p.α) := by
  have hrep_real : ∀ z ∈ Set.Icc (0:ℝ) 1,
      intervalDomainLift (u t₀) z
        = ∑' n, localRestartCoeff a₀ a (t₀ - offset) n * cosineMode n z := by
    intro z hz
    rw [intervalDomainLift, dif_pos hz]
    exact hrep.self_of_nhds ⟨z, hz⟩
  exact hpde_u_core p hχ0
    (b := fun n => localRestartCoeff a₀ a (t₀ - offset) n)
    (src := fun n => a (t₀ - offset) n) hsum_src hsum_lb
    (timeDeriv_eq_of_rep hM ha₀ src hoff hrep x)
    (laplacian_eq_of_rep hsum_b hrep_real hx)
    (source_inversion_eq_reaction_surrogate p hcont hgeq hsum_fourier hsrc_coeff hx)

end ShenWork.IntervalDomainPdeUChiZero
