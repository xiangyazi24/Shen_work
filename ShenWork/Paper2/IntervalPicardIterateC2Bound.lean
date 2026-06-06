/-
  ShenWork/Paper2/IntervalPicardIterateC2Bound.lean

  Phase-0 / M2-uniform — explicit C² spatial bounds for the NEXT Picard iterate
  slice, from M1's restart cosine identity plus the quantitative gain/weight
  atoms.

  ## Abstract reusable core

  For any ℓ¹-weighted cosine series `g(x) = ∑'ₙ bₙ cos(nπx)` with
  `∑'ₙ λₙ|bₙ| < ∞` (`λₙ = unitIntervalCosineEigenvalue n = (nπ)²`), the first and
  second spatial derivatives are termwise

      ∂ₓ g = ∑'ₙ bₙ·(−nπ·sin(nπx)),   ∂ₓₓ g = ∑'ₙ bₙ·(−(nπ)²·cos(nπx)),

  (`cosineCoeffSeries_grad_hasDerivAt`, `cosineCoeffSeries_grad2_hasDerivAt`), so a
  termwise tsum-triangle inequality (`|sin|,|cos| ≤ 1`) gives the pointwise sup
  bounds by the `√λ`- and `λ`-weighted coefficient ℓ¹ sums (note `√λₙ = nπ`):

      |∂ₓ g x|  ≤ ∑'ₙ √λₙ·|bₙ|,      |∂ₓₓ g x| ≤ ∑'ₙ λₙ·|bₙ|.

  These two lemmas (`cosineSeries_abs_deriv_le_sqrtEig_tsum`,
  `cosineSeries_abs_deriv2_le_eig_tsum`) are reusable for ANY ℓ¹-weighted cosine
  series.

  ## Iterate corollary

  Specialising `bₙ = restartDuhamelCoeff a₀ a τ n`
  (= `e^{−τλₙ}·a₀ₙ + duhamelSpectralCoeff a τ n`, M1's restart series for
  `lift(uₙ₊₁(t))` at `τ = t/2`) and splitting `√λ`/`λ`-weighted sums into the
  homogeneous and Duhamel parts:

   (i)  sup_{x} |∂ₓ lift(uₙ₊₁(t)) x| ≤ M₁·sqrtEigExpWeight(t/2) + C₁·Benv
   (ii) sup_{x} |∂ₓₓ lift(uₙ₊₁(t)) x| ≤ M₁·eigExpWeight(t/2) + C₂·(t/2)^{1/4}·Benv

  with `M₁` the half-step coefficient bound (`|a₀ₙ| = |cosineCoeffs(lift
  uₙ₊₁(t/2)) n| ≤ M₁`), `Benv` the source envelope constant
  (`|aₙ(σ)| ≤ 2·Benv/(nπ)²`, `n ≥ 1`), `C₁ = 2·(∑'ₙ 1/(n+1)³)/π³`,
  `C₂ = 2·(∑'ₙ 1/(n+1)^{3/2})/π^{3/2}` the EXPLICIT constants of
  `IntervalDuhamelQuantGain`, and `sqrtEigExpWeight`/`eigExpWeight` from
  `IntervalHomogeneousQuantBound`.

  The zeroth source mode contributes nothing to the weighted sums: in (i) and
  (ii) its weight is `√λ₀ = 0` resp. `λ₀ = 0`, so no separate zeroth-mode term is
  needed.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.PDE.IntervalDuhamelQuantGain
import ShenWork.PDE.IntervalHomogeneousQuantBound
import ShenWork.Paper2.IntervalPicardIterateRestart

open MeasureTheory Filter Topology
open scoped Real
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode cosineMode_hasDerivAt)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalDuhamelClosedC2
  (duhamelSpectralCoeff DuhamelSourceTimeC1
   cosineCoeffSeries_grad_hasDerivAt cosineCoeffSeries_grad2_hasDerivAt
   cosineCoeff_summable_of_eigenvalue_summable)
open ShenWork.IntervalMildRegularityBootstrap (restartDuhamelCoeff)
open ShenWork.IntervalHomogeneousQuantBound (eigExpWeight sqrtEigExpWeight)
open ShenWork.IntervalDuhamelQuantGain

noncomputable section

namespace ShenWork.IntervalPicardIterateC2Bound

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## §1 — Abstract sup bounds for derivatives of an ℓ¹-weighted cosine series.

These are the reusable core: the pointwise first/second spatial derivative of any
cosine series with `∑ λₙ|bₙ| < ∞` is bounded by the `√λ`/`λ`-weighted coefficient
ℓ¹ sums. -/

/-- `√λₙ = nπ` for the unit-interval cosine eigenvalues. -/
theorem sqrt_eig_eq (n : ℕ) :
    Real.sqrt (unitIntervalCosineEigenvalue n) = (n : ℝ) * Real.pi := by
  have hlam_eq : unitIntervalCosineEigenvalue n = ((n : ℝ) * Real.pi) ^ 2 := rfl
  rw [hlam_eq, Real.sqrt_sq (by positivity)]

/-- **Abstract G1 sup bound.**  For an ℓ¹-weighted cosine series
`g(x) = ∑'ₙ bₙ cos(nπx)` with `∑'ₙ λₙ|bₙ| < ∞`, the first spatial derivative is
bounded pointwise by the `√λ`-weighted coefficient sum:
`|∂ₓ g x| ≤ ∑'ₙ √λₙ·|bₙ|`. -/
theorem cosineSeries_abs_deriv_le_sqrtEig_tsum {b : ℕ → ℝ}
    (hb : Summable (fun n => unitIntervalCosineEigenvalue n * |b n|)) (x : ℝ) :
    |deriv (fun x => ∑' n, b n * cosineMode n x) x|
      ≤ ∑' n, Real.sqrt (unitIntervalCosineEigenvalue n) * |b n| := by
  obtain ⟨hfreq, _hval⟩ := cosineCoeff_summable_of_eigenvalue_summable hb
  -- The deriv equals the gradient cosine series.
  rw [(cosineCoeffSeries_grad_hasDerivAt hb x).deriv, ← Real.norm_eq_abs]
  -- per-term bound: ‖bₙ·(−nπ sin)‖ ≤ nπ·|bₙ| = √λₙ·|bₙ|.
  have hterm_le : ∀ n : ℕ,
      ‖b n * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * x))‖
        ≤ Real.sqrt (unitIntervalCosineEigenvalue n) * |b n| := by
    intro n
    rw [sqrt_eig_eq, Real.norm_eq_abs, abs_mul, abs_mul, abs_neg]
    calc |b n| * (|(n : ℝ) * Real.pi| * |Real.sin ((n : ℝ) * Real.pi * x)|)
        ≤ |b n| * (((n : ℝ) * Real.pi) * 1) := by
          gcongr
          · rw [abs_of_nonneg (by positivity)]
          · exact Real.abs_sin_le_one _
      _ = ((n : ℝ) * Real.pi) * |b n| := by ring
  -- summability of the √λ-weighted sum (= nπ|bₙ|).
  have hsqrt_sum : Summable
      (fun n => Real.sqrt (unitIntervalCosineEigenvalue n) * |b n|) := by
    refine hfreq.congr (fun n => ?_)
    rw [sqrt_eig_eq]
  have hgrad_sum : Summable
      (fun n => b n * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * x))) :=
    Summable.of_norm_bounded hfreq (fun n => by
      have := hterm_le n; rw [sqrt_eig_eq] at this; exact this)
  calc ‖∑' n, b n * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * x))‖
      ≤ ∑' n, ‖b n * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * x))‖ :=
        norm_tsum_le_tsum_norm
          (by
            refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm_le hsqrt_sum)
    _ ≤ ∑' n, Real.sqrt (unitIntervalCosineEigenvalue n) * |b n| :=
        Summable.tsum_le_tsum hterm_le
          (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm_le hsqrt_sum)
          hsqrt_sum

/-- **Abstract G2 sup bound.**  For an ℓ¹-weighted cosine series
`g(x) = ∑'ₙ bₙ cos(nπx)` with `∑'ₙ λₙ|bₙ| < ∞`, the second spatial derivative is
bounded pointwise by the `λ`-weighted coefficient sum:
`|∂ₓₓ g x| ≤ ∑'ₙ λₙ·|bₙ|`. -/
theorem cosineSeries_abs_deriv2_le_eig_tsum {b : ℕ → ℝ}
    (hb : Summable (fun n => unitIntervalCosineEigenvalue n * |b n|)) (x : ℝ) :
    |deriv (deriv (fun x => ∑' n, b n * cosineMode n x)) x|
      ≤ ∑' n, unitIntervalCosineEigenvalue n * |b n| := by
  -- second deriv = ∑ bₙ·(−(nπ)² cos).
  have he1 : deriv (fun x => ∑' n, b n * cosineMode n x)
      = fun z => ∑' n, b n * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * z)) := by
    funext z; exact (cosineCoeffSeries_grad_hasDerivAt hb z).deriv
  rw [he1, (cosineCoeffSeries_grad2_hasDerivAt hb x).deriv, ← Real.norm_eq_abs]
  have hterm_le : ∀ n : ℕ,
      ‖b n * (-(((n : ℝ) * Real.pi) ^ 2) * Real.cos ((n : ℝ) * Real.pi * x))‖
        ≤ unitIntervalCosineEigenvalue n * |b n| := by
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg]
    have hlam : unitIntervalCosineEigenvalue n = ((n : ℝ) * Real.pi) ^ 2 := rfl
    rw [hlam]
    calc |b n| * (|((n : ℝ) * Real.pi) ^ 2| * |Real.cos ((n : ℝ) * Real.pi * x)|)
        ≤ |b n| * ((((n : ℝ) * Real.pi) ^ 2) * 1) := by
          gcongr
          · rw [abs_of_nonneg (by positivity)]
          · exact Real.abs_cos_le_one _
      _ = ((n : ℝ) * Real.pi) ^ 2 * |b n| := by ring
  have hgrad2_sum : Summable
      (fun n => b n * (-(((n : ℝ) * Real.pi) ^ 2) * Real.cos ((n : ℝ) * Real.pi * x))) :=
    Summable.of_norm_bounded hb hterm_le
  calc ‖∑' n, b n * (-(((n : ℝ) * Real.pi) ^ 2) * Real.cos ((n : ℝ) * Real.pi * x))‖
      ≤ ∑' n, ‖b n * (-(((n : ℝ) * Real.pi) ^ 2) * Real.cos ((n : ℝ) * Real.pi * x))‖ :=
        norm_tsum_le_tsum_norm
          (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm_le hb)
    _ ≤ ∑' n, unitIntervalCosineEigenvalue n * |b n| :=
        Summable.tsum_le_tsum hterm_le
          (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm_le hb) hb

/-! ## §1.5 — Summability of the homogeneous / Duhamel weighted sequences. -/

/-- The `√λ`-weighted homogeneous restart sequence is summable. -/
theorem hom_sqrtEig_summable {τ M₁ : ℝ} {a₀ : ℕ → ℝ}
    (hτ : 0 < τ) (ha₀ : ∀ n, |a₀ n| ≤ M₁) :
    Summable (fun n => Real.sqrt (unitIntervalCosineEigenvalue n) *
      |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|) := by
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) (fun n => ?_)
    ((ShenWork.IntervalHomogeneousQuantBound.sqrtEig_mul_exp_summable hτ).mul_left M₁)
  have hexp : (0:ℝ) ≤ Real.exp (-τ * unitIntervalCosineEigenvalue n) := Real.exp_nonneg _
  calc Real.sqrt (unitIntervalCosineEigenvalue n) *
        |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|
      = Real.sqrt (unitIntervalCosineEigenvalue n) *
          (Real.exp (-τ * unitIntervalCosineEigenvalue n) * |a₀ n|) := by
        rw [abs_mul, abs_of_nonneg hexp]
    _ ≤ Real.sqrt (unitIntervalCosineEigenvalue n) *
          (Real.exp (-τ * unitIntervalCosineEigenvalue n) * M₁) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (ha₀ n) hexp) (Real.sqrt_nonneg _)
    _ = M₁ * (Real.sqrt (unitIntervalCosineEigenvalue n) *
          Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by ring

/-- The `λ`-weighted homogeneous restart sequence is summable. -/
theorem hom_eig_summable {τ M₁ : ℝ} {a₀ : ℕ → ℝ}
    (hτ : 0 < τ) (ha₀ : ∀ n, |a₀ n| ≤ M₁) :
    Summable (fun n => unitIntervalCosineEigenvalue n *
      |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|) :=
  ShenWork.IntervalMildRegularityBootstrap.restartHomogeneousCoeff_eigenvalue_summable
    hτ ha₀

/-- The `√λ`-weighted Duhamel sequence is summable (per-mode `τ`-free bound +
shifted `p = 3` series). -/
theorem duh_sqrtEig_summable {τ Benv : ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ) (hBenv : 0 ≤ Benv)
    (hdecay : ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k →
      |a σ k| ≤ 2 * Benv / ((k : ℝ) * Real.pi) ^ 2)
    (hacont : ∀ k, Continuous (fun σ => a σ k)) :
    Summable (fun n => Real.sqrt (unitIntervalCosineEigenvalue n) *
      |duhamelSpectralCoeff a τ n|) := by
  set f : ℕ → ℝ := fun n => Real.sqrt (unitIntervalCosineEigenvalue n) *
    |duhamelSpectralCoeff a τ n| with hf_def
  have hfnn : ∀ n, 0 ≤ f n := fun n => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hg_sum : Summable (fun k : ℕ =>
      (2 * Benv / Real.pi ^ 3) * (1 / ((k : ℝ) + 1) ^ (3 : ℕ))) :=
    ShenWork.IntervalDuhamelQuantGain.summable_one_div_natShift_cube.mul_left _
  have hshift_le : ∀ k : ℕ,
      f (k + 1) ≤ (2 * Benv / Real.pi ^ 3) * (1 / ((k : ℝ) + 1) ^ (3 : ℕ)) := by
    intro k
    have hk : 1 ≤ k + 1 := Nat.le_add_left 1 k
    have hbound := ShenWork.IntervalDuhamelQuantGain.sqrtEigenvalue_mul_coeff_bound
      hτ hBenv hdecay hacont hk
    refine hbound.trans (le_of_eq ?_)
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast, mul_pow]; field_simp
  have hf_shift : Summable (fun k => f (k + 1)) :=
    hg_sum.of_nonneg_of_le (fun k => hfnn (k + 1)) hshift_le
  exact (summable_nat_add_iff (f := f) 1).1 hf_shift

/-- The `λ`-weighted Duhamel sequence is summable (the spectral atom's
`duhamelSpectralCoeff_eigenvalue_summable`, via the `DuhamelSourceTimeC1`
package). -/
theorem duh_eig_summable {τ : ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC1 a) (hτ : 0 < τ) :
    Summable (fun n => unitIntervalCosineEigenvalue n *
      |duhamelSpectralCoeff a τ n|) :=
  ShenWork.IntervalDuhamelClosedC2.duhamelSpectralCoeff_eigenvalue_summable src hτ

/-! ## §2 — Splitting the restart-series weighted sums into homogeneous + Duhamel.

`restartDuhamelCoeff a₀ a τ n = e^{−τλₙ}·a₀ₙ + duhamelSpectralCoeff a τ n`.  The
`√λ`/`λ`-weighted ℓ¹ sums split additively, and each piece is bounded by the
corresponding quant atom. -/

/-- **√λ-weighted restart sum bound (G1).**  Under the half-step coefficient
bound `|a₀ₙ| ≤ M₁` and the source decay `|aₙ(σ)| ≤ 2·Benv/(nπ)²` (`n ≥ 1`),
`∑'ₙ √λₙ·|restartDuhamelCoeff a₀ a τ n| ≤ M₁·sqrtEigExpWeight τ + C₁·Benv`, with
`C₁ = 2·(∑'ₙ 1/(n+1)³)/π³`. -/
theorem restartSeries_sqrtEig_tsum_le
    {τ M₁ Benv : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ) (hBenv : 0 ≤ Benv)
    (ha₀ : ∀ n, |a₀ n| ≤ M₁)
    (hdecay : ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k →
      |a σ k| ≤ 2 * Benv / ((k : ℝ) * Real.pi) ^ 2)
    (hacont : ∀ k, Continuous (fun σ => a σ k)) :
    (∑' n, Real.sqrt (unitIntervalCosineEigenvalue n) *
        |restartDuhamelCoeff a₀ a τ n|)
      ≤ M₁ * sqrtEigExpWeight τ
        + (2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ (3 : ℕ)) / Real.pi ^ 3) * Benv := by
  have hhom_sum := hom_sqrtEig_summable (M₁ := M₁) hτ ha₀
  have hduh_sum := duh_sqrtEig_summable hτ hBenv hdecay hacont
  -- per-mode split.
  have hsplit_le : ∀ n,
      Real.sqrt (unitIntervalCosineEigenvalue n) * |restartDuhamelCoeff a₀ a τ n|
        ≤ Real.sqrt (unitIntervalCosineEigenvalue n) *
            |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|
          + Real.sqrt (unitIntervalCosineEigenvalue n) * |duhamelSpectralCoeff a τ n| := by
    intro n
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    simpa [restartDuhamelCoeff] using
      abs_add_le (Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n)
        (duhamelSpectralCoeff a τ n)
  calc (∑' n, Real.sqrt (unitIntervalCosineEigenvalue n) *
          |restartDuhamelCoeff a₀ a τ n|)
      ≤ ∑' n, (Real.sqrt (unitIntervalCosineEigenvalue n) *
            |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|
          + Real.sqrt (unitIntervalCosineEigenvalue n) * |duhamelSpectralCoeff a τ n|) :=
        Summable.tsum_le_tsum hsplit_le
          (Summable.of_nonneg_of_le
            (fun n => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hsplit_le
            (hhom_sum.add hduh_sum))
          (hhom_sum.add hduh_sum)
    _ = (∑' n, Real.sqrt (unitIntervalCosineEigenvalue n) *
            |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|)
          + ∑' n, Real.sqrt (unitIntervalCosineEigenvalue n) *
            |duhamelSpectralCoeff a τ n| := hhom_sum.tsum_add hduh_sum
    _ ≤ M₁ * sqrtEigExpWeight τ
          + (2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ (3 : ℕ)) / Real.pi ^ 3) * Benv := by
        gcongr
        · exact ShenWork.IntervalHomogeneousQuantBound.homogeneous_sqrtEigenvalue_tsum_le
            hτ ha₀
        · exact ShenWork.IntervalDuhamelQuantGain.duhamelSpectralCoeff_sqrtEigenvalue_tsum_bound
            hτ hBenv hdecay hacont

/-- **λ-weighted restart sum bound (G2).**  Under the half-step coefficient bound
`|a₀ₙ| ≤ M₁`, the source decay `|aₙ(σ)| ≤ 2·Benv/(nπ)²` (`n ≥ 1`), and the
`DuhamelSourceTimeC1` package,
`∑'ₙ λₙ·|restartDuhamelCoeff a₀ a τ n| ≤ M₁·eigExpWeight τ + C₂·τ^{1/4}·Benv`, with
`C₂ = 2·(∑'ₙ 1/(n+1)^{3/2})/π^{3/2}`.  The zeroth source mode drops (`λ₀ = 0`). -/
theorem restartSeries_eig_tsum_le
    {τ M₁ Benv : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ) (hBenv : 0 ≤ Benv)
    (ha₀ : ∀ n, |a₀ n| ≤ M₁)
    (src : DuhamelSourceTimeC1 a)
    (hdecay : ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k →
      |a σ k| ≤ 2 * Benv / ((k : ℝ) * Real.pi) ^ 2)
    (hacont : ∀ k, Continuous (fun σ => a σ k)) :
    (∑' n, unitIntervalCosineEigenvalue n * |restartDuhamelCoeff a₀ a τ n|)
      ≤ M₁ * eigExpWeight τ
        + (2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) /
            Real.pi ^ ((3 : ℝ) / 2)) * τ ^ ((1 : ℝ) / 4) * Benv := by
  have hhom_sum := hom_eig_summable (M₁ := M₁) hτ ha₀
  have hduh_sum := duh_eig_summable src hτ
  have hsplit_le : ∀ n,
      unitIntervalCosineEigenvalue n * |restartDuhamelCoeff a₀ a τ n|
        ≤ unitIntervalCosineEigenvalue n *
            |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|
          + unitIntervalCosineEigenvalue n * |duhamelSpectralCoeff a τ n| := by
    intro n
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (by unfold unitIntervalCosineEigenvalue; positivity)
    simpa [restartDuhamelCoeff] using
      abs_add_le (Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n)
        (duhamelSpectralCoeff a τ n)
  calc (∑' n, unitIntervalCosineEigenvalue n * |restartDuhamelCoeff a₀ a τ n|)
      ≤ ∑' n, (unitIntervalCosineEigenvalue n *
            |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|
          + unitIntervalCosineEigenvalue n * |duhamelSpectralCoeff a τ n|) :=
        Summable.tsum_le_tsum hsplit_le
          (Summable.of_nonneg_of_le
            (fun n => mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity)
              (abs_nonneg _)) hsplit_le (hhom_sum.add hduh_sum))
          (hhom_sum.add hduh_sum)
    _ = (∑' n, unitIntervalCosineEigenvalue n *
            |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|)
          + ∑' n, unitIntervalCosineEigenvalue n *
            |duhamelSpectralCoeff a τ n| := hhom_sum.tsum_add hduh_sum
    _ ≤ M₁ * eigExpWeight τ
          + (2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) /
              Real.pi ^ ((3 : ℝ) / 2)) * τ ^ ((1 : ℝ) / 4) * Benv := by
        gcongr
        · exact ShenWork.IntervalHomogeneousQuantBound.homogeneous_eigenvalue_tsum_le
            hτ ha₀
        · exact ShenWork.IntervalDuhamelQuantGain.duhamelSpectralCoeff_eigenvalue_tsum_tauQuarter_bound
            hτ hBenv hdecay hacont

/-! ## §3 — Explicit C² bounds for the next iterate slice.

Combining the abstract sup bounds (§1) with the restart-series split (§2) and
M1's restart cosine identity (`picardIterateRestart_cosineIdentity`), we obtain
explicit spatial-derivative sup bounds for the next iterate slice represented by
its restart cosine series.  Working with the restart series
`g(x) = ∑'ₙ restartDuhamelCoeff a₀ a (t/2) n · cosineMode n x` (which equals
`lift(uₙ₊₁(t))` on `[0,1]` by M1), the bounds are stated for `deriv g`/`deriv²
g`, valid at every `x` (in particular the sup over `[0,1]`). -/

/-- The restart-series eigenvalue-weighted summability hypothesis from the
half-step bound and a `DuhamelSourceTimeC1` source (needed to invoke the abstract
§1 sup bounds for the restart series). -/
theorem restartSeries_eigenvalue_summable
    {τ M₁ : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ) (ha₀ : ∀ n, |a₀ n| ≤ M₁) (src : DuhamelSourceTimeC1 a) :
    Summable (fun n => unitIntervalCosineEigenvalue n *
      |restartDuhamelCoeff a₀ a τ n|) :=
  ShenWork.IntervalMildRegularityBootstrap.restartDuhamelCoeff_eigenvalue_summable
    hτ ha₀ src

/-- **G1 — explicit first-derivative sup bound for the restart series.**
For the restart cosine series with half-step coefficient bound `|a₀ₙ| ≤ M₁`,
source decay `|aₙ(σ)| ≤ 2·Benv/(nπ)²` (`n ≥ 1`) and a `DuhamelSourceTimeC1`
package, at every `x`:
`|∂ₓ (∑'ₙ restartDuhamelCoeff a₀ a τ n · cosineMode n x)|
   ≤ M₁·sqrtEigExpWeight τ + C₁·Benv`,  `C₁ = 2·(∑'ₙ 1/(n+1)³)/π³`. -/
theorem restartSeries_abs_deriv_le
    {τ M₁ Benv : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ) (hBenv : 0 ≤ Benv)
    (ha₀ : ∀ n, |a₀ n| ≤ M₁)
    (src : DuhamelSourceTimeC1 a)
    (hdecay : ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k →
      |a σ k| ≤ 2 * Benv / ((k : ℝ) * Real.pi) ^ 2)
    (hacont : ∀ k, Continuous (fun σ => a σ k)) (x : ℝ) :
    |deriv (fun x => ∑' n, restartDuhamelCoeff a₀ a τ n * cosineMode n x) x|
      ≤ M₁ * sqrtEigExpWeight τ
        + (2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ (3 : ℕ)) / Real.pi ^ 3) * Benv :=
  (cosineSeries_abs_deriv_le_sqrtEig_tsum
      (restartSeries_eigenvalue_summable hτ ha₀ src) x).trans
    (restartSeries_sqrtEig_tsum_le hτ hBenv ha₀ hdecay hacont)

/-- **G2 — explicit second-derivative sup bound for the restart series.**
For the restart cosine series, at every `x`:
`|∂ₓₓ (∑'ₙ restartDuhamelCoeff a₀ a τ n · cosineMode n x)|
   ≤ M₁·eigExpWeight τ + C₂·τ^{1/4}·Benv`,
`C₂ = 2·(∑'ₙ 1/(n+1)^{3/2})/π^{3/2}`.  Zeroth source mode drops (`λ₀ = 0`). -/
theorem restartSeries_abs_deriv2_le
    {τ M₁ Benv : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ) (hBenv : 0 ≤ Benv)
    (ha₀ : ∀ n, |a₀ n| ≤ M₁)
    (src : DuhamelSourceTimeC1 a)
    (hdecay : ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k →
      |a σ k| ≤ 2 * Benv / ((k : ℝ) * Real.pi) ^ 2)
    (hacont : ∀ k, Continuous (fun σ => a σ k)) (x : ℝ) :
    |deriv (deriv (fun x => ∑' n, restartDuhamelCoeff a₀ a τ n * cosineMode n x)) x|
      ≤ M₁ * eigExpWeight τ
        + (2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) /
            Real.pi ^ ((3 : ℝ) / 2)) * τ ^ ((1 : ℝ) / 4) * Benv :=
  (cosineSeries_abs_deriv2_le_eig_tsum
      (restartSeries_eigenvalue_summable hτ ha₀ src) x).trans
    (restartSeries_eig_tsum_le hτ hBenv ha₀ src hdecay hacont)

/-! ### §3.1 — Next-iterate slice specialisation (via M1's restart identity).

`restartIterateCoeff p u₀ n t` packages M1's restart coefficients for
`lift(uₙ₊₁(t))`: the homogeneous datum is the half-step coefficients
`cosineCoeffs(lift(uₙ₊₁(t/2)))` and the source is the σ-shifted logistic source.
M1's `picardIterateRestart_cosineIdentity` identifies `lift(uₙ₊₁(t))` with the
corresponding restart cosine series on `[0,1]`. -/

/-- The restart coefficient sequence for the next iterate slice `lift(uₙ₊₁(t))`,
`τ = t/2`.  This is the coefficient of the cosine series in M1's identity. -/
def restartIterateCoeff (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (t : ℝ) (k : ℕ) : ℝ :=
  restartDuhamelCoeff
    (cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (t / 2))))
    (fun σ k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k)
    (t / 2) k

/-- **(i) — explicit first-derivative sup bound for the next iterate slice.**
For `p.χ₀ = 0` and `0 < t`, taking `M₁` a bound for the half-step coefficients of
`lift(uₙ₊₁(t/2))`, `Benv` the σ-shifted logistic source envelope constant, and a
`DuhamelSourceTimeC1` package `srcσ` for the σ-shifted source family, the first
spatial derivative of the next iterate slice's restart series satisfies, at every
`x`:
`|∂ₓ (∑'ₖ restartIterateCoeff p u₀ n t k · cosineMode k x)|
   ≤ M₁·sqrtEigExpWeight(t/2) + C₁·Benv`. -/
theorem iterate_abs_deriv_le
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    {t M₁ Benv : ℝ} (ht : 0 < t) (hBenv : 0 ≤ Benv)
    (hM₁ : ∀ k,
      |cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (t / 2))) k| ≤ M₁)
    (srcσ : DuhamelSourceTimeC1
      (fun σ k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k))
    (hdecay : ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k|
        ≤ 2 * Benv / ((k : ℝ) * Real.pi) ^ 2)
    (hσcont : ∀ k, Continuous
      (fun σ => cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k))
    (x : ℝ) :
    |deriv (fun x => ∑' k, restartIterateCoeff p u₀ n t k * cosineMode k x) x|
      ≤ M₁ * sqrtEigExpWeight (t / 2)
        + (2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ (3 : ℕ)) / Real.pi ^ 3) * Benv := by
  have hτ : 0 < t / 2 := by positivity
  simpa only [restartIterateCoeff] using
    restartSeries_abs_deriv_le (a₀ :=
        cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (t / 2))))
      (a := fun σ k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k)
      hτ hBenv hM₁ srcσ hdecay hσcont x

/-- **(ii) — explicit second-derivative sup bound for the next iterate slice.**
Same data as `iterate_abs_deriv_le`; the second spatial derivative of the next
iterate slice's restart series satisfies, at every `x`:
`|∂ₓₓ (∑'ₖ restartIterateCoeff p u₀ n t k · cosineMode k x)|
   ≤ M₁·eigExpWeight(t/2) + C₂·(t/2)^{1/4}·Benv`.  Zeroth source mode drops. -/
theorem iterate_abs_deriv2_le
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    {t M₁ Benv : ℝ} (ht : 0 < t) (hBenv : 0 ≤ Benv)
    (hM₁ : ∀ k,
      |cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (t / 2))) k| ≤ M₁)
    (srcσ : DuhamelSourceTimeC1
      (fun σ k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k))
    (hdecay : ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k|
        ≤ 2 * Benv / ((k : ℝ) * Real.pi) ^ 2)
    (hσcont : ∀ k, Continuous
      (fun σ => cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k))
    (x : ℝ) :
    |deriv (deriv (fun x => ∑' k, restartIterateCoeff p u₀ n t k * cosineMode k x)) x|
      ≤ M₁ * eigExpWeight (t / 2)
        + (2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) /
            Real.pi ^ ((3 : ℝ) / 2)) * (t / 2) ^ ((1 : ℝ) / 4) * Benv := by
  have hτ : 0 < t / 2 := by positivity
  simpa only [restartIterateCoeff] using
    restartSeries_abs_deriv2_le (a₀ :=
        cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (t / 2))))
      (a := fun σ k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k)
      hτ hBenv hM₁ srcσ hdecay hσcont x

end ShenWork.IntervalPicardIterateC2Bound
