/-
  ShenWork/Paper2/IntervalGradientCoeffDuhamel.lean

  WALL-B — the coefficient-space Duhamel identity connecting the gradient mild
  solution's cosine coefficients to the C²-bootstrap engine's
  `duhamelEnergyCoeff`.

  This is the engine↔solution integration point.  It is NON-circular: it is the
  mild Duhamel equation diagonalized in the cosine basis, NOT a regularity fact.
  The gradient mild solution `u` (the Picard limit) satisfies its mild Duhamel
  equation `u(t) = Φ(u₀,u)(t)` BY CONSTRUCTION (`IntervalMildSolution`), and
  applying `cosineCoeffs` to that equation is exactly the identity proved here.
  No `DuhamelSourceTimeC1` package, no `C²` bootstrap, and no
  `RestartCosineRepresentation` is needed for the engine bridge
  `duhamelSpectralCoeff_eq_duhamelEnergyCoeff` and the heat diagonalization.

  ## What is established

  * `cosineCoeffs_intervalFullSemigroupOperator_diag` — **(a) heat diagonalization
    on cosine modes.**  For `t > 0` and ℓ∞-bounded coefficients,
    `cosineCoeffs (S(t) f) k = e^{−t λ_k} · cosineCoeffs f k`.  The diffusion
    constant is `d = 1` (the value baked into `intervalFullSemigroupOperator`).

  * `duhamelSpectralCoeff_eq_duhamelEnergyCoeff` — **the engine bridge.**  The
    solution-side Duhamel coefficient `duhamelSpectralCoeff a t k` (no `√λ`
    factor, `d = 1`) equals the engine's per-mode divergence-Duhamel coefficient
    `duhamelEnergyCoeff 1 F t k` (which carries the `√λ_k` divergence factor) once
    the engine source `F` absorbs the divergence factor: `a s k = √(λ_k) · F k s`.
    This is the exact algebraic statement of how the `∂ₓ`/divergence factor
    `√λ_k` sits inside the engine's per-mode integrand: the engine consumes the
    source with the `√λ_k` already extracted.  Proved by `integral_congr` + `ring`
    at the integrand level.

  * `gradientSolution_cosineCoeff_eq_duhamelEnergyCoeff` — **WALL-B (χ₀ = 0).**
    For the gradient mild solution `u` (satisfying its mild equation `hfix`),
    `cosineCoeffs (lift (u t)) k = e^{−t λ_k} · â₀(k)
        + duhamelEnergyCoeff 1 (engine source) t k`,
    the diagonalized mild equation in coefficients, with the (logistic) source
    Duhamel term presented through the engine object `duhamelEnergyCoeff`.

  ## Non-circularity verdict (step 4)

  The heat diagonalization and the engine bridge use ONLY: the spectral kernel
  identity (Poisson/theta), the proved coefficient extraction
  `cosineCoeffs_unitIntervalCosineHeatValue`, and scalar interval-integral
  algebra.  The full WALL-B identity feeds on `limit_lift_eq_cosineSeries`, whose
  ONLY use of the solution is the raw mild fixed-point equation `hfix`
  (`= IntervalMildSolution`, available by construction) plus datum/source ℓ∞/ℓ¹
  envelope hypotheses — none a `C²`/regularity fact.  The engine bridge itself is
  regularity-free.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalPicardLimitRestart
import ShenWork.Paper2.IntervalBFormHSigmaDuhamelEnergy
import ShenWork.PDE.IntervalFullKernelSpectralClean
import ShenWork.PDE.IntervalSemigroupComposition

open MeasureTheory
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator cosineCoeffs)
open ShenWork.IntervalSemigroupComposition (cosineCoeffs_unitIntervalCosineHeatValue)
open ShenWork.IntervalFullKernelSpectralClean
  (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc)
open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff DuhamelSourceTimeC1)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.BFormHSigmaDuhamelMode (duhamelModeCoeff)
open ShenWork.Paper2.HSigmaScale (lam)
open ShenWork.IntervalPicardLimitRestart (limitCoeff limit_lift_eq_cosineSeries
  cosineCoeffs_halfstep_eq_limitCoeff summable_abs_limitCoeff)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap logisticLifted)

noncomputable section

namespace ShenWork.Paper2.IntervalGradientCoeffDuhamel

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## (a) Heat semigroup diagonalization on cosine modes -/

/-- **(a) Heat diagonalization on cosine modes.**  For `t > 0` and ℓ∞-bounded
cosine coefficients of `f`, the cosine coefficient of the heat-propagated `S(t) f`
is the diagonal multiplier `e^{−t λ_k}` times the coefficient of `f`:

    cosineCoeffs (intervalFullSemigroupOperator t f) k
      = e^{−t λ_k} · cosineCoeffs f k.

The diffusion constant is `d = 1` (the value baked into
`intervalFullSemigroupOperator`).  Composition of the spectral kernel identity
`intervalFullSemigroupOperator_eq_cosineHeatValue_Icc` (the propagator equals the
cosine heat value on `[0,1]`, which is all `cosineCoeffs` sees) with the
coefficient extraction `cosineCoeffs_unitIntervalCosineHeatValue`. -/
theorem cosineCoeffs_intervalFullSemigroupOperator_diag
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ k, |cosineCoeffs f k| ≤ M) (k : ℕ) :
    cosineCoeffs (fun x => intervalFullSemigroupOperator t f x) k
      = Real.exp (-t * (λ_ k)) * cosineCoeffs f k := by
  -- `cosineCoeffs` only sees `[0,1]`, where the propagator equals the heat value.
  have heq : Set.EqOn (fun x => intervalFullSemigroupOperator t f x)
      (fun x => unitIntervalCosineHeatValue t (cosineCoeffs f) x)
      (Set.Icc (0 : ℝ) 1) := fun x hx =>
    intervalFullSemigroupOperator_eq_cosineHeatValue_Icc ht hf hM hx
  rw [cosineCoeffs_congr_on_Icc heq k]
  exact cosineCoeffs_unitIntervalCosineHeatValue ht hM k

/-! ## The engine bridge: `duhamelSpectralCoeff` ↔ `duhamelEnergyCoeff` -/

/-- **The engine bridge.**  The solution-side per-mode Duhamel coefficient

    duhamelSpectralCoeff a t k = ∫₀ᵗ e^{−(t−s) λ_k} · a(s,k) ds

(no `√λ` factor, diffusion `d = 1`) equals the C²-bootstrap engine's per-mode
divergence-Duhamel coefficient

    duhamelEnergyCoeff 1 F t k = ∫₀ᵗ √(λ_k) · e^{−(t−s) λ_k} · F(k,s) ds,

once the engine source `F` absorbs the divergence factor at mode `k`, i.e.
`a s k = √(λ_k) · F k s` for every time `s` (`hsrc`).

This is the exact algebraic content of how the divergence factor `√λ_k`
(the `∂ₓ` on the cosine kernel → the divergence mode factor) sits inside the
engine's integrand: the engine consumes the source with `√λ_k` already
extracted.  Proved by congruence of the interval integrands followed by `ring`. -/
theorem duhamelSpectralCoeff_eq_duhamelEnergyCoeff
    (a : ℝ → ℕ → ℝ) (F : ℕ → ℝ → ℝ) (t : ℝ) (k : ℕ)
    (hsrc : ∀ s, a s k = (lam k) ^ (1/2 : ℝ) * F k s) :
    duhamelSpectralCoeff a t k = duhamelEnergyCoeff 1 F t k := by
  unfold duhamelSpectralCoeff duhamelEnergyCoeff duhamelModeCoeff
  -- both sides are interval integrals over `[0,t]`; match integrands pointwise.
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  -- `lam k = unitIntervalCosineEigenvalue k` (definitional), `d = 1`.
  rw [hsrc s]
  show Real.exp (-(t - s) * unitIntervalCosineEigenvalue k)
        * ((lam k) ^ (1/2 : ℝ) * F k s)
      = (lam k) ^ (1/2 : ℝ) * Real.exp (-(1 * lam k * (t - s))) * F k s
  have hlam : (lam k : ℝ) = unitIntervalCosineEigenvalue k := rfl
  rw [hlam]
  have harg : -(1 * unitIntervalCosineEigenvalue k * (t - s))
      = -(t - s) * unitIntervalCosineEigenvalue k := by ring
  rw [harg]
  ring

/-! ## WALL-B — the diagonalized mild equation in coefficients (χ₀ = 0) -/

/-- **WALL-B (χ₀ = 0): the gradient mild solution's cosine coefficients are the
diagonalized Duhamel formula, with the source Duhamel term presented through the
engine object `duhamelEnergyCoeff`.**

For the gradient mild solution `u` (satisfying its mild Duhamel equation `hfix`,
which `IntervalMildSolution`/`picardLimit_is_mildSolution` supplies by
construction) with datum coefficient bound and the time-`C¹` source package,

    cosineCoeffs (lift (u t)) k
      = e^{−t λ_k} · cosineCoeffs (lift u₀) k
        + duhamelEnergyCoeff 1 (engineSource) t k,

where `engineSource j s = cosineCoeffs (logisticLifted p (u s)) j / √(λ_j)` is the
logistic source coefficient with the divergence factor `√λ_j` extracted (so that
`√(λ_j) · engineSource j s` reproduces the genuine source coefficient).  This is
the mild EQUATION read off in the cosine basis: the heat term diagonalizes
(`cosineCoeffs_intervalFullSemigroupOperator_diag`), and the Duhamel term is the
engine coefficient via `duhamelSpectralCoeff_eq_duhamelEnergyCoeff`. -/
theorem gradientSolution_cosineCoeff_eq_duhamelEnergyCoeff
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    (hfix : ∀ t, 0 < t → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (u t) x = intervalGradientDuhamelMap p u₀ u t ⟨x, hx⟩)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k))
    {t : ℝ} (ht : 0 < t)
    (hL_cont : ∀ s, 0 < s → s ≤ t → Continuous (logisticLifted p (u s)))
    {k : ℕ} (hk : k ≠ 0) :
    cosineCoeffs (intervalDomainLift (u t)) k
      = Real.exp (-t * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k
        + duhamelEnergyCoeff 1
            (fun j s => cosineCoeffs (logisticLifted p (u s)) j / (lam j) ^ (1/2 : ℝ))
            t k := by
  -- The solution coefficient equals the diagonalized Duhamel limit coefficient.
  have hcoeff : cosineCoeffs (intervalDomainLift (u t)) k = limitCoeff p u₀ u t k :=
    cosineCoeffs_halfstep_eq_limitCoeff p hχ0 u₀ u hfix hu₀_cont hu₀_bound hsrc0 ht
      hL_cont k
  rw [hcoeff]
  unfold limitCoeff
  -- The homogeneous term already matches; rewrite the Duhamel term via the engine
  -- bridge.  At the positive mode `k ≥ 1` the divergence factor `√λ_k > 0`, so the
  -- source coefficient `cosineCoeffs (logisticLifted p (u s)) k` is recovered
  -- exactly from its `√λ`-extracted engine form `coeff/√λ_k`.
  have hlam_pos : 0 < lam k := by
    simp only [lam, unitIntervalCosineEigenvalue]
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    positivity
  have hsqrt_ne : (lam k) ^ (1/2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hlam_pos _)
  have hbridge :
      duhamelSpectralCoeff (fun s j => cosineCoeffs (logisticLifted p (u s)) j) t k
        = duhamelEnergyCoeff 1
            (fun j s => cosineCoeffs (logisticLifted p (u s)) j / (lam j) ^ (1/2 : ℝ))
            t k :=
    duhamelSpectralCoeff_eq_duhamelEnergyCoeff
      (fun s j => cosineCoeffs (logisticLifted p (u s)) j)
      (fun j s => cosineCoeffs (logisticLifted p (u s)) j / (lam j) ^ (1/2 : ℝ))
      t k (fun s => by field_simp)
  rw [hbridge]

end ShenWork.Paper2.IntervalGradientCoeffDuhamel
