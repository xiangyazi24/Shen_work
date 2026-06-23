/-
  ShenWork/Paper2/IntervalDenomSecondDerivBound.lean

  Atom #1F — the τ-UNIFORM second-derivative integral bound for the chemotaxis
  denominator `w = (1+v)^{−β}`, the LAST scalar residual of `#1` (the χ₀<0 flux
  factor-envelope).  Closing it produces a `DenomUniformEnvelope σ t W₂`
  UNCONDITIONALLY from a `TrajectoryHSigmaEnvelope`, hence (via the landed
  `genv_of_traj_denom`) closes `#1` entirely → `FluxFactorEnvelopes` → the
  regularity ladder.

  ## What this file delivers

  Let `v τ = resolverValue μ (cosineCoeffs (u τ))` (the coefficient-side elliptic
  resolver of `u τ`), and `W₂ τ = (1+v τ)^{−β}` the chemotaxis denominator.

  * **Spectral sup bounds** (`resolverGrad_sup_le`, `resolverGrad2_sup_le`).  From
    the termwise differentiation engine `cosineCoeffSeries_grad_hasDerivAt` /
    `_grad2_hasDerivAt`, both `‖v'‖_∞` and `‖v''‖_∞` are bounded by the single
    spectral sum `S := ∑'ₙ (nπ)²·|resolverCoeff μ g n|`, and `S ≤ ∑'ₙ |gₙ|` because
    the resolver multiplier `λₙ/(μ+λₙ) ≤ 1`.

  * **τ-uniform spectral sum** (`resolverSpectralSum_le_envelope`).  `S ≤ ∑'ₙ Uσₙ`
    for the trajectory envelope `Uσ ∈ H^σ` (σ>1/2, so `Uσ ∈ ℓ¹`), uniformly over
    τ — because `|gₙ| = |cosineCoeffs (u τ) n| ≤ Uσₙ` (the per-τ envelope).

  * **Pointwise `w''` bound** (`denomSecondDeriv_abs_le`).  The chain rule gives
    `w'' = β(β+1)(1+v)^{−β−2}(v')² − β(1+v)^{−β−1}v''`, and the denominators have
    `≤1` powers (base `≥1`, exponent `≤0`), so
    `|w''| ≤ β(β+1)(v')² + β|v''| ≤ β(β+1)S₀² + β·S₀ =: B`, where `S₀ = ∑'ₙ Uσₙ`.

  * **The integral bound + the envelope** (`denomSecondDerivIntegral_le`,
    `denomUniformEnvelope_of_trajectoryEnvelope`).  `∫₀¹|w''| ≤ B` (interval length
    1) feeds `cosineCoeffs_decay_two`; the mode-0 bound `A=1` follows from
    `0 ≤ w ≤ 1`.  Together they build the `DenomUniformEnvelope` via the landed
    `denomUniformEnvelope_of_secondDerivBound`.

  * **#1 closed UNCONDITIONALLY** (`genv_of_trajectoryEnvelope_uncond`).  Chaining
    into `genv_of_traj_denom`, the χ₀<0 flux H^σ envelope `genv` is produced from a
    `TrajectoryHSigmaEnvelope` + the per-τ resolver/bridge wiring, with NO carried
    denominator hypothesis.

  ## NON-CIRCULARITY

  `v`'s `C²` comes from the elliptic resolver gain (`resolverValue_contDiff_two`,
  i.e. `u ∈ H^σ → v̂ ∈ H^{σ+2} ↪ C²`), NOT from `C²`-of-`u`.  `u`'s coefficients
  enter ONLY through the trajectory envelope `Uσ` (`|cosineCoeffs (u τ) n| ≤ Uσ n`).
  Never references `localClassicalSolution`, `IsPaper2ClassicalSolution`, or the
  C²-Neumann producers.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.
  `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.
-/
import ShenWork.Paper2.IntervalGWProductEnvelope
import ShenWork.Paper2.IntervalDenomEnvelopeResolver

noncomputable section

open Real MeasureTheory

namespace ShenWork.Paper2.IntervalDenomSecondDerivBound

open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HSigmaScale
  (lam MemHSigma resolverCoeff resolver_memHSigmaPlus2_of_memHSigma lam_nonneg)
open ShenWork.Paper2.IntervalCosineSobolevEmbedding (memHSigma_summable_eigenvalue_abs)
open ShenWork.Paper2.IntervalWienerAlgebra
  (cosineCoeffs_eq_cw cw_zero hSigma_subset_l1_of_gt_half)
open ShenWork.Paper2.IntervalDenomEnvelopeResolver (resolverValue)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelClosedC2
  (cosineCoeffSeries_grad_hasDerivAt cosineCoeffSeries_grad2_hasDerivAt)
open ShenWork.Paper2.IntervalCkComposition (cosineCoeffs_decay_two contDiff_two_tower)
open ShenWork.Paper2.IntervalEnvelopeProp (Envelopes)
open ShenWork.Paper2.IntervalGWProductEnvelope
  (DenomUniformEnvelope denomUniformEnvelope_of_secondDerivBound genv_of_traj_denom)
open ShenWork.Paper2.IntervalTrajectoryEnvelope (TrajectoryHSigmaEnvelope)

/-! ## 1. The spectral sum and its τ-uniform envelope bound. -/

/-- The single spectral sum controlling both `‖v'‖_∞` and `‖v''‖_∞`:
`S = ∑'ₙ λₙ·|resolverCoeff μ g n|` (`λₙ = (nπ)²`). -/
def resolverSpectralSum (μ : ℝ) (g : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ, lam n * |resolverCoeff μ g n|

/-- Per-mode resolver bound: `(nπ)²·|resolverCoeff μ g n| ≤ |g n|` (the resolver
multiplier `λₙ/(μ+λₙ) ≤ 1`). -/
theorem resolverMode_le {μ : ℝ} (hμ : 0 < μ) (g : ℕ → ℝ) (n : ℕ) :
    lam n * |resolverCoeff μ g n| ≤ |g n| := by
  have hlamnn : 0 ≤ lam n := lam_nonneg n
  have hden : 0 < μ + lam n := by linarith
  unfold resolverCoeff
  rw [abs_div, abs_of_pos hden, div_eq_mul_inv]
  have hfrac : lam n * (μ + lam n)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hden]; linarith
  calc lam n * (|g n| * (μ + lam n)⁻¹)
      = (lam n * (μ + lam n)⁻¹) * |g n| := by ring
    _ ≤ 1 * |g n| := mul_le_mul_of_nonneg_right hfrac (abs_nonneg _)
    _ = |g n| := one_mul _

/-- The resolver spectral sum is bounded by the ℓ¹ norm of the source. -/
theorem resolverSpectralSum_le_l1 {μ : ℝ} (hμ : 0 < μ) {g : ℕ → ℝ}
    (hg1 : Summable (fun n => |g n|)) :
    resolverSpectralSum μ g ≤ ∑' n : ℕ, |g n| := by
  unfold resolverSpectralSum
  refine Summable.tsum_mono ?_ hg1 (fun n => resolverMode_le hμ g n)
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (lam_nonneg n) (abs_nonneg _))
    (fun n => resolverMode_le hμ g n) hg1

/-! ## 2. Spectral sup bounds on `v'` and `v''`. -/

/-- The eigenvalue-weighted ℓ¹ summability of the resolver coefficients (from the
`H^{σ+2}` gain), the hypothesis the termwise-differentiation engine consumes. -/
theorem resolver_eigenSummable {μ σ : ℝ} (hμ : 0 < μ) (hσ : 1 / 2 < σ)
    {g : ℕ → ℝ} (hg : MemHSigma σ g) :
    Summable (fun n => lam n * |resolverCoeff μ g n|) := by
  have hv2 : MemHSigma (σ + 2) (resolverCoeff μ g) :=
    (resolver_memHSigmaPlus2_of_memHSigma hμ hg).1
  exact memHSigma_summable_eigenvalue_abs (by linarith : 5 / 2 < σ + 2) hv2

/-- Per-mode gradient majorant: `|bₙ·(−nπ·sin)| ≤ λₙ|bₙ|`
(`nπ ≤ (nπ)² = λₙ` for `n ≥ 1`, both `0` for `n = 0`). -/
theorem gradMode_le (b : ℕ → ℝ) (y : ℝ) (n : ℕ) :
    |b n * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * y))| ≤ lam n * |b n| := by
  rw [abs_mul, abs_mul, abs_neg]
  have hsin : |Real.sin ((n : ℝ) * Real.pi * y)| ≤ 1 := Real.abs_sin_le_one _
  have hnp : |(n : ℝ) * Real.pi| = (n : ℝ) * Real.pi := abs_of_nonneg (by positivity)
  have hlam : lam n = ((n : ℝ) * Real.pi) ^ 2 := rfl
  rw [hlam]
  calc |b n| * (|(n : ℝ) * Real.pi| * |Real.sin ((n : ℝ) * Real.pi * y)|)
      ≤ |b n| * ((n : ℝ) * Real.pi * 1) := by rw [hnp]; gcongr
    _ ≤ ((n : ℝ) * Real.pi) ^ 2 * |b n| := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · have hnp0 : (0 : ℝ) ≤ (n : ℝ) * Real.pi := by positivity
          have h1 : (1 : ℝ) ≤ (n : ℝ) * Real.pi := by
            have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            nlinarith [Real.two_le_pi]
          have hprod : ((n : ℝ) * Real.pi) * 1 ≤ ((n : ℝ) * Real.pi) ^ 2 := by nlinarith
          calc |b n| * ((n : ℝ) * Real.pi * 1)
              ≤ |b n| * ((n : ℝ) * Real.pi) ^ 2 :=
                mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
            _ = ((n : ℝ) * Real.pi) ^ 2 * |b n| := by ring

/-- Per-mode second-gradient majorant: `|bₙ·(−(nπ)²·cos)| ≤ λₙ|bₙ|`. -/
theorem grad2Mode_le (b : ℕ → ℝ) (y : ℝ) (n : ℕ) :
    |b n * (-(((n : ℝ) * Real.pi) ^ 2) * Real.cos ((n : ℝ) * Real.pi * y))|
      ≤ lam n * |b n| := by
  rw [abs_mul, abs_mul, abs_neg]
  have hcos : |Real.cos ((n : ℝ) * Real.pi * y)| ≤ 1 := Real.abs_cos_le_one _
  have hp : |((n : ℝ) * Real.pi) ^ 2| = ((n : ℝ) * Real.pi) ^ 2 := abs_of_nonneg (by positivity)
  have hlam : lam n = ((n : ℝ) * Real.pi) ^ 2 := rfl
  rw [hlam]
  calc |b n| * (|((n : ℝ) * Real.pi) ^ 2| * |Real.cos ((n : ℝ) * Real.pi * y)|)
      ≤ |b n| * (((n : ℝ) * Real.pi) ^ 2 * 1) := by rw [hp]; gcongr
    _ = ((n : ℝ) * Real.pi) ^ 2 * |b n| := by ring

/-- **Sup bound on `v'`.**  `|v'(y)| ≤ S` for `S = resolverSpectralSum μ g`. -/
theorem resolverGrad_sup_le {μ σ : ℝ} (hμ : 0 < μ) (hσ : 1 / 2 < σ)
    {g : ℕ → ℝ} (hg : MemHSigma σ g) (y : ℝ) :
    |deriv (resolverValue μ g) y| ≤ resolverSpectralSum μ g := by
  have hsum := resolver_eigenSummable hμ hσ hg
  have hderiv : deriv (resolverValue μ g) y
      = ∑' n, resolverCoeff μ g n
          * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * y)) := by
    rw [show (resolverValue μ g)
      = (fun x => ∑' n, resolverCoeff μ g n * cosineMode n x) from rfl]
    exact (cosineCoeffSeries_grad_hasDerivAt hsum y).deriv
  rw [hderiv, resolverSpectralSum]
  set F : ℕ → ℝ := fun n => resolverCoeff μ g n
      * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * y)) with hF
  have hFle : ∀ n, |F n| ≤ lam n * |resolverCoeff μ g n| := fun n => by
    rw [hF]; exact gradMode_le (resolverCoeff μ g) y n
  have hnorm : Summable (fun n => ‖F n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => by rw [Real.norm_eq_abs]; exact hFle n) hsum
  have hbnd : ‖∑' n, F n‖ ≤ ∑' n, ‖F n‖ := norm_tsum_le_tsum_norm hnorm
  rw [Real.norm_eq_abs] at hbnd
  refine le_trans hbnd (le_trans (le_of_eq (tsum_congr (fun n => Real.norm_eq_abs (F n)))) ?_)
  exact Summable.tsum_mono
    (Summable.of_nonneg_of_le (fun n => abs_nonneg _) hFle hsum) hsum hFle

/-- **Sup bound on `v''`.**  `|v''(y)| ≤ S` for `S = resolverSpectralSum μ g`. -/
theorem resolverGrad2_sup_le {μ σ : ℝ} (hμ : 0 < μ) (hσ : 1 / 2 < σ)
    {g : ℕ → ℝ} (hg : MemHSigma σ g) (y : ℝ) :
    |deriv (deriv (resolverValue μ g)) y| ≤ resolverSpectralSum μ g := by
  have hsum := resolver_eigenSummable hμ hσ hg
  have he1 : deriv (resolverValue μ g)
      = fun z => ∑' n, resolverCoeff μ g n
          * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * z)) := by
    funext z
    rw [show (resolverValue μ g)
      = (fun x => ∑' n, resolverCoeff μ g n * cosineMode n x) from rfl]
    exact (cosineCoeffSeries_grad_hasDerivAt hsum z).deriv
  have hderiv : deriv (deriv (resolverValue μ g)) y
      = ∑' n, resolverCoeff μ g n
          * (-(((n : ℝ) * Real.pi) ^ 2) * Real.cos ((n : ℝ) * Real.pi * y)) := by
    rw [he1]; exact (cosineCoeffSeries_grad2_hasDerivAt hsum y).deriv
  rw [hderiv, resolverSpectralSum]
  set F : ℕ → ℝ := fun n => resolverCoeff μ g n
      * (-(((n : ℝ) * Real.pi) ^ 2) * Real.cos ((n : ℝ) * Real.pi * y)) with hF
  have hFle : ∀ n, |F n| ≤ lam n * |resolverCoeff μ g n| := fun n => by
    rw [hF]; exact grad2Mode_le (resolverCoeff μ g) y n
  have hnorm : Summable (fun n => ‖F n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => by rw [Real.norm_eq_abs]; exact hFle n) hsum
  have hbnd : ‖∑' n, F n‖ ≤ ∑' n, ‖F n‖ := norm_tsum_le_tsum_norm hnorm
  rw [Real.norm_eq_abs] at hbnd
  refine le_trans hbnd (le_trans (le_of_eq (tsum_congr (fun n => Real.norm_eq_abs (F n)))) ?_)
  exact Summable.tsum_mono
    (Summable.of_nonneg_of_le (fun n => abs_nonneg _) hFle hsum) hsum hFle

/-! ## 3. The pointwise second-derivative bound for `w = (1+v)^{−β}`. -/

/-- The chain-rule second derivative of `w = (1+v)^{−β}` as an explicit `HasDerivAt`
of `w' = (−β)(1+v)^{−β−1}v'`. -/
theorem denomSecondDeriv_hasDerivAt {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (hvnn : ∀ x, 0 ≤ v x) (β x : ℝ) :
    HasDerivAt (fun y => (-β) * (1 + v y) ^ (-β - 1) * deriv v y)
      (β * (β + 1) * (1 + v x) ^ (-β - 2) * (deriv v x) ^ 2
        + (-β) * (1 + v x) ^ (-β - 1) * (deriv (deriv v) x)) x := by
  have hd1 : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hv1 : ContDiff ℝ 1 (deriv v) := ContDiff.deriv' hv
  have hdv : Differentiable ℝ (deriv v) := hv1.differentiable (by norm_num)
  have hbase : 1 + v x ≠ 0 := by have := hvnn x; positivity
  have hinner : HasDerivAt (fun y => 1 + v y) (deriv v x) x := (hd1 x).hasDerivAt.const_add 1
  have hpow : HasDerivAt (fun y => (1 + v y) ^ (-β - 1))
      ((-β - 1) * (1 + v x) ^ (-β - 2) * deriv v x) x := by
    have h := hinner.rpow_const (p := -β - 1) (Or.inl hbase)
    have he : (-β - 1 - 1 : ℝ) = -β - 2 := by ring
    rw [he] at h
    convert h using 1; ring
  have hvd1 : HasDerivAt (deriv v) (deriv (deriv v) x) x := (hdv x).hasDerivAt
  have hP := ((hpow.const_mul (-β)).mul hvd1)
  have hfun : (fun y => (-β) * (1 + v y) ^ (-β - 1) * deriv v y)
      = (fun y => -β * (1 + v y) ^ (-β - 1)) * deriv v := by funext y; rfl
  rw [hfun]
  convert hP using 1
  ring

/-- **Pointwise `w''` bound.**  For `v ≥ 0` and `β ≥ 0`, with sup bounds
`|v'(x)| ≤ S`, `|v''(x)| ≤ S` (and `0 ≤ S`),
`|w''(x)| ≤ β(β+1)S² + β·S` because the denominators have `≤1` powers. -/
theorem denomSecondDeriv_abs_le {v : ℝ → ℝ} {β S x : ℝ} (hβ : 0 ≤ β)
    (hvnn : ∀ x, 0 ≤ v x) (hS0 : 0 ≤ S)
    (hv1 : |deriv v x| ≤ S) (hv2 : |deriv (deriv v) x| ≤ S) :
    |β * (β + 1) * (1 + v x) ^ (-β - 2) * (deriv v x) ^ 2
        + (-β) * (1 + v x) ^ (-β - 1) * (deriv (deriv v) x)|
      ≤ β * (β + 1) * S ^ 2 + β * S := by
  have hbase : (1 : ℝ) ≤ 1 + v x := by have := hvnn x; linarith
  have hp2 : (1 + v x) ^ (-β - 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
  have hp2nn : 0 ≤ (1 + v x) ^ (-β - 2) :=
    Real.rpow_nonneg (by linarith) _
  have hp1 : (1 + v x) ^ (-β - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
  have hp1nn : 0 ≤ (1 + v x) ^ (-β - 1) :=
    Real.rpow_nonneg (by linarith) _
  -- bound each summand in absolute value
  have hT1 : |β * (β + 1) * (1 + v x) ^ (-β - 2) * (deriv v x) ^ 2|
      ≤ β * (β + 1) * S ^ 2 := by
    rw [abs_mul, abs_mul]
    have ha : |β * (β + 1)| = β * (β + 1) := abs_of_nonneg (by nlinarith)
    have hb : |(1 + v x) ^ (-β - 2)| = (1 + v x) ^ (-β - 2) := abs_of_nonneg hp2nn
    have hc : |(deriv v x) ^ 2| = (deriv v x) ^ 2 := abs_of_nonneg (by positivity)
    rw [ha, hb, hc]
    have hsq : (deriv v x) ^ 2 ≤ S ^ 2 := by
      have := sq_abs (deriv v x); nlinarith [abs_nonneg (deriv v x), hv1, hS0]
    calc β * (β + 1) * (1 + v x) ^ (-β - 2) * (deriv v x) ^ 2
        ≤ β * (β + 1) * 1 * S ^ 2 := by
          apply mul_le_mul
          · apply mul_le_mul_of_nonneg_left hp2 (by nlinarith)
          · exact hsq
          · positivity
          · nlinarith
      _ = β * (β + 1) * S ^ 2 := by ring
  have hT2 : |(-β) * (1 + v x) ^ (-β - 1) * (deriv (deriv v) x)| ≤ β * S := by
    rw [abs_mul, abs_mul]
    have ha : |(-β)| = β := by rw [abs_neg, abs_of_nonneg hβ]
    have hb : |(1 + v x) ^ (-β - 1)| = (1 + v x) ^ (-β - 1) := abs_of_nonneg hp1nn
    rw [ha, hb]
    calc β * (1 + v x) ^ (-β - 1) * |deriv (deriv v) x|
        ≤ β * 1 * S := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hp1 hβ
          · exact hv2
          · exact abs_nonneg _
          · positivity
      _ = β * S := by ring
  calc |β * (β + 1) * (1 + v x) ^ (-β - 2) * (deriv v x) ^ 2
          + (-β) * (1 + v x) ^ (-β - 1) * (deriv (deriv v) x)|
      ≤ |β * (β + 1) * (1 + v x) ^ (-β - 2) * (deriv v x) ^ 2|
          + |(-β) * (1 + v x) ^ (-β - 1) * (deriv (deriv v) x)| := abs_add_le _ _
    _ ≤ β * (β + 1) * S ^ 2 + β * S := add_le_add hT1 hT2

/-! ## 4. The τ-uniform integral bound + mode-0 bound, assembled into the envelope. -/

/-- Continuity of `w = (1+v)^{−β}` (from `v ∈ C²`, `v ≥ 0`). -/
theorem denom_continuous {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvnn : ∀ x, 0 ≤ v x)
    (β : ℝ) : Continuous (fun x => (1 + v x) ^ (-β)) :=
  (ShenWork.Paper2.IntervalCkComposition.contDiff_two_one_add_rpow_neg hv hvnn β).continuous

/-- `0 ≤ w ≤ 1` for `w = (1+v)^{−β}`, `v ≥ 0`, `β ≥ 0`. -/
theorem denom_mem_unitInterval {v : ℝ → ℝ} {β : ℝ} (hβ : 0 ≤ β)
    (hvnn : ∀ x, 0 ≤ v x) (x : ℝ) :
    0 ≤ (1 + v x) ^ (-β) ∧ (1 + v x) ^ (-β) ≤ 1 := by
  have hbase : (1 : ℝ) ≤ 1 + v x := by have := hvnn x; linarith
  exact ⟨Real.rpow_nonneg (by linarith) _,
    Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)⟩

/-- **The mode-0 bound `A = 1`** for `w = (1+v)^{−β}` (since `0 ≤ w ≤ 1`). -/
theorem denom_mode0_le {v : ℝ → ℝ} {β : ℝ} (hβ : 0 ≤ β) (hv : ContDiff ℝ 2 v)
    (hvnn : ∀ x, 0 ≤ v x) :
    |cosineCoeffs (fun x => (1 + v x) ^ (-β)) 0| ≤ 1 := by
  have hw : Continuous (fun x => (1 + v x) ^ (-β)) := denom_continuous hv hvnn β
  rw [cosineCoeffs_eq_cw _ hw 0, cw_zero, one_mul]
  have hsimp : (∫ x in (0:ℝ)..1, Real.cos (((0:ℕ) : ℝ) * Real.pi * x) * (1 + v x) ^ (-β))
      = ∫ x in (0:ℝ)..1, (1 + v x) ^ (-β) := by
    apply intervalIntegral.integral_congr; intro x _; simp
  rw [hsimp, abs_of_nonneg (intervalIntegral.integral_nonneg (by norm_num)
    (fun x _ => (denom_mem_unitInterval hβ hvnn x).1))]
  have hle : (∫ x in (0:ℝ)..1, (1 + v x) ^ (-β)) ≤ ∫ x in (0:ℝ)..1, (1 : ℝ) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (hw.intervalIntegrable 0 1) intervalIntegrable_const
    intro x _; exact (denom_mem_unitInterval hβ hvnn x).2
  simpa using hle

/-- **The τ-uniform second-derivative integral bound** `∫₀¹|w''| ≤ B` for
`w = (1+v)^{−β}`, `B = β(β+1)S² + β·S`, from the sup bounds `|v'|,|v''| ≤ S`. -/
theorem denomSecondDerivIntegral_le {v : ℝ → ℝ} {β S : ℝ} (hβ : 0 ≤ β)
    (hv : ContDiff ℝ 2 v) (hvnn : ∀ x, 0 ≤ v x) (hS0 : 0 ≤ S)
    (hv1 : ∀ x, |deriv v x| ≤ S) (hv2 : ∀ x, |deriv (deriv v) x| ≤ S) :
    (∫ x in (0:ℝ)..1, |deriv (deriv (fun y => (1 + v y) ^ (-β))) x|)
      ≤ β * (β + 1) * S ^ 2 + β * S := by
  -- identify deriv (deriv w) pointwise with the explicit chain-rule formula.
  obtain ⟨_, _, _, hda, _⟩ := contDiff_two_tower
    (ShenWork.Paper2.IntervalCkComposition.contDiff_two_one_add_rpow_neg hv hvnn β)
  have hwd1 : deriv (fun y => (1 + v y) ^ (-β))
      = fun y => (-β) * (1 + v y) ^ (-β - 1) * deriv v y := by
    funext y
    have hbase : 1 + v y ≠ 0 := by have := hvnn y; positivity
    have hinner : HasDerivAt (fun z => 1 + v z) (deriv v y) y :=
      ((hv.differentiable (by norm_num)) y).hasDerivAt.const_add 1
    have hpow := hinner.rpow_const (p := -β) (Or.inl hbase)
    have : deriv (fun z => (1 + v z) ^ (-β)) y
        = (-β) * (1 + v y) ^ (-β - 1) * deriv v y := by
      rw [hpow.deriv]; ring
    exact this
  have hd2eq : ∀ x, deriv (deriv (fun y => (1 + v y) ^ (-β))) x
      = β * (β + 1) * (1 + v x) ^ (-β - 2) * (deriv v x) ^ 2
        + (-β) * (1 + v x) ^ (-β - 1) * (deriv (deriv v) x) := by
    intro x
    rw [hwd1]
    exact (denomSecondDeriv_hasDerivAt hv hvnn β x).deriv
  have hcont : Continuous (fun x => |deriv (deriv (fun y => (1 + v y) ^ (-β))) x|) := by
    have hc2 : Continuous (deriv (deriv (fun y => (1 + v y) ^ (-β)))) := by
      obtain ⟨_, _, hcc, _, _⟩ := contDiff_two_tower
        (ShenWork.Paper2.IntervalCkComposition.contDiff_two_one_add_rpow_neg hv hvnn β)
      exact hcc
    exact hc2.abs
  have hbnd : ∀ x, |deriv (deriv (fun y => (1 + v y) ^ (-β))) x|
      ≤ β * (β + 1) * S ^ 2 + β * S := by
    intro x; rw [hd2eq x]
    exact denomSecondDeriv_abs_le hβ hvnn hS0 (hv1 x) (hv2 x)
  have hmono : (∫ x in (0:ℝ)..1, |deriv (deriv (fun y => (1 + v y) ^ (-β))) x|)
      ≤ ∫ x in (0:ℝ)..1, (β * (β + 1) * S ^ 2 + β * S) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (hcont.intervalIntegrable 0 1) intervalIntegrable_const
    intro x _; exact hbnd x
  simpa using hmono

/-! ## 5. Bridges: envelope → `H^σ` membership, and the per-τ decay bound. -/

/-- **Envelope domination ⟹ `H^σ` membership.**  If `|g n| ≤ env n` with
`env ∈ H^σ`, then `g ∈ H^σ` (per-mode comparison of the `H^σ` energy). -/
theorem memHSigma_of_envelope {σ : ℝ} {env g : ℕ → ℝ} (henv : MemHSigma σ env)
    (hdom : ∀ n, |g n| ≤ env n) : MemHSigma σ g := by
  unfold MemHSigma at *
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) henv
  · have := ShenWork.Paper2.HSigmaScale.one_add_lam_pos n; positivity
  · have h1 := ShenWork.Paper2.HSigmaScale.one_add_lam_pos n
    have h0 : 0 ≤ env n := le_trans (abs_nonneg _) (hdom n)
    have hgsq : (g n) ^ 2 ≤ (env n) ^ 2 := by
      nlinarith [abs_nonneg (g n), hdom n, sq_abs (g n), h0]
    exact mul_le_mul_of_nonneg_left hgsq (Real.rpow_nonneg h1.le σ)

/-- **The per-τ `n^{−2}` decay bound** for `w = (1+v)^{−β}`, `v = resolverValue μ g`,
`g ∈ H^σ` (`1/2 < σ`), `β ≥ 0`, resolver positivity, given a second-derivative
integral bound `∫₀¹|w''| ≤ B`.  Routes `cosineCoeffs_decay_two` (`C²` + Neumann,
both discharged from the resolver `C²`/Neumann bricks) then the integral bound. -/
theorem denomDecayBound {μ σ β B : ℝ} (hμ : 0 < μ) (hσ : 1 / 2 < σ) {g : ℕ → ℝ}
    (hg : MemHSigma σ g) (hvnn : ∀ x, 0 ≤ resolverValue μ g x)
    (hintB : (∫ x in (0:ℝ)..1,
        |deriv (deriv (fun y => (1 + resolverValue μ g y) ^ (-β))) x|) ≤ B)
    (n : ℕ) (hn : 1 ≤ n) :
    |cosineCoeffs (fun x => (1 + resolverValue μ g x) ^ (-β)) n|
      ≤ (2 / Real.pi ^ 2 * B) / (n : ℝ) ^ 2 := by
  set v := resolverValue μ g with hv
  have hvC2 : ContDiff ℝ 2 v :=
    ShenWork.Paper2.IntervalDenomEnvelopeResolver.resolverValue_contDiff_two hμ hσ hg
  have hwC2 : ContDiff ℝ 2 (fun x => (1 + v x) ^ (-β)) :=
    ShenWork.Paper2.IntervalCkComposition.contDiff_two_one_add_rpow_neg hvC2 hvnn β
  obtain ⟨hc0, hc1, hc2, hda, hdb⟩ := contDiff_two_tower hwC2
  have hdiff : Differentiable ℝ v := hvC2.differentiable (by norm_num)
  have hd0 : deriv v 0 = 0 :=
    ShenWork.Paper2.IntervalDenomEnvelopeResolver.resolverValue_deriv_at_zero hμ hσ hg
  have hd1 : deriv v 1 = 0 :=
    ShenWork.Paper2.IntervalDenomEnvelopeResolver.resolverValue_deriv_at_one hμ hσ hg
  have hbase0 : 1 + v 0 ≠ 0 := by have := hvnn 0; positivity
  have hbase1 : 1 + v 1 ≠ 0 := by have := hvnn 1; positivity
  have hN0 : deriv (fun x => (1 + v x) ^ (-β)) 0 = 0 :=
    ShenWork.Paper2.IntervalDenomEnvelopeResolver.denom_deriv_zero_of_inner_deriv_zero
      (hdiff 0) hd0 hbase0
  have hN1 : deriv (fun x => (1 + v x) ^ (-β)) 1 = 0 :=
    ShenWork.Paper2.IntervalDenomEnvelopeResolver.denom_deriv_zero_of_inner_deriv_zero
      (hdiff 1) hd1 hbase1
  have hdecay := cosineCoeffs_decay_two (fun x => (1 + v x) ^ (-β))
    (deriv (fun x => (1 + v x) ^ (-β))) (deriv (deriv (fun x => (1 + v x) ^ (-β))))
    hc0 hc1 (fun x _ => hda x) (fun x _ => hdb x) hc2 hN0 hN1 n hn
  refine le_trans hdecay ?_
  have hnpos : (0:ℝ) < (n:ℝ) ^ 2 := by
    have : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    positivity
  have hpi : (0:ℝ) ≤ 2 / Real.pi ^ 2 := by positivity
  gcongr

/-! ## 6. The τ-uniform denominator envelope from a trajectory envelope. -/

/-- **The τ-uniform denominator envelope `DenomUniformEnvelope σ t W₂`**, built
UNCONDITIONALLY from a trajectory envelope `Uσ` (`= E.env`).

`W₂ τ = (1+v τ)^{−β}` with `v τ = resolverValue μ (cosineCoeffs (u τ))`, `μ>0`,
`β ≥ 0`, resolver positivity `0 ≤ v τ`, `1/2 < σ < 3/2`.  The mode-0 bound `A=1`
and the second-derivative integral bound `B = β(β+1)S₀² + β·S₀` with
`S₀ = ∑'ₙ |E.env n|` (τ-uniform, since `|cosineCoeffs (u τ) n| ≤ E.env n`) are
both discharged here, then fed into the landed `n^{−2}`-decay constructor. -/
def denomUniformEnvelope_of_trajectoryEnvelope {μ σ β t : ℝ} (hμ : 0 < μ)
    (hσ0 : 1 / 2 < σ) (hσ1 : σ < 3 / 2) (hβ : 0 ≤ β)
    {u : ℝ → ℝ → ℝ} (E : TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (u τ)))
    (hvnn : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ x, 0 ≤ resolverValue μ (cosineCoeffs (u τ)) x) :
    DenomUniformEnvelope σ t
      (fun τ x => (1 + resolverValue μ (cosineCoeffs (u τ)) x) ^ (-β)) := by
  -- τ-uniform ℓ¹ sup S₀ = ∑ |E.env n|
  have henv_l1 : Summable (fun n => |E.env n|) := hSigma_subset_l1_of_gt_half hσ0 E.henv
  set S₀ : ℝ := ∑' n : ℕ, |E.env n| with hS₀
  have hS₀nn : 0 ≤ S₀ := by rw [hS₀]; exact tsum_nonneg (fun n => abs_nonneg _)
  set B : ℝ := β * (β + 1) * S₀ ^ 2 + β * S₀ with hB
  have hB0 : 0 ≤ B := by
    rw [hB]
    have h1 : 0 ≤ β * (β + 1) * S₀ ^ 2 := by positivity
    have h2 : 0 ≤ β * S₀ := mul_nonneg hβ hS₀nn
    have hβ1 : 0 ≤ β + 1 := by linarith
    nlinarith [mul_nonneg (mul_nonneg hβ hβ1) (sq_nonneg S₀), h2]
  -- per-τ spectral sum ≤ S₀
  have hspec : ∀ τ ∈ Set.Icc (0:ℝ) t,
      resolverSpectralSum μ (cosineCoeffs (u τ)) ≤ S₀ := by
    intro τ hτ
    have hdom_abs : ∀ n, |cosineCoeffs (u τ) n| ≤ |E.env n| := fun n =>
      le_trans (E.hdom τ hτ n) (le_abs_self _)
    have hg1 : Summable (fun n => |cosineCoeffs (u τ) n|) :=
      Summable.of_nonneg_of_le (fun n => abs_nonneg _) hdom_abs henv_l1
    refine le_trans (resolverSpectralSum_le_l1 hμ hg1) ?_
    exact Summable.tsum_mono hg1 henv_l1 hdom_abs
  -- per-τ H^σ membership of u's coefficients (from the envelope)
  have hgmem : ∀ τ ∈ Set.Icc (0:ℝ) t, MemHSigma σ (cosineCoeffs (u τ)) := fun τ hτ =>
    memHSigma_of_envelope E.henv (fun n => E.hdom τ hτ n)
  -- assemble via the landed n^{-2} decay constructor
  refine denomUniformEnvelope_of_secondDerivBound (A := 1) (B := B)
    (by linarith : (0:ℝ) ≤ σ) hσ1 hB0 ?_ ?_
  · -- mode-0 bound A = 1
    intro τ hτ
    have hvC2 : ContDiff ℝ 2 (resolverValue μ (cosineCoeffs (u τ))) :=
      ShenWork.Paper2.IntervalDenomEnvelopeResolver.resolverValue_contDiff_two
        hμ hσ0 (hgmem τ hτ)
    exact denom_mode0_le hβ hvC2 (hvnn τ hτ)
  · -- decay bound B per τ via the integral bound + cosineCoeffs_decay_two
    intro τ hτ n hn
    have hgm := hgmem τ hτ
    have hvC2 : ContDiff ℝ 2 (resolverValue μ (cosineCoeffs (u τ))) :=
      ShenWork.Paper2.IntervalDenomEnvelopeResolver.resolverValue_contDiff_two hμ hσ0 hgm
    -- the τ-uniform integral bound ∫|w''| ≤ B from the spectral sup bounds
    have hsup1 : ∀ x, |deriv (resolverValue μ (cosineCoeffs (u τ))) x| ≤ S₀ := fun x =>
      le_trans (resolverGrad_sup_le hμ hσ0 hgm x) (hspec τ hτ)
    have hsup2 : ∀ x, |deriv (deriv (resolverValue μ (cosineCoeffs (u τ)))) x| ≤ S₀ :=
      fun x => le_trans (resolverGrad2_sup_le hμ hσ0 hgm x) (hspec τ hτ)
    have hintB : (∫ x in (0:ℝ)..1,
        |deriv (deriv (fun y => (1 + resolverValue μ (cosineCoeffs (u τ)) y) ^ (-β))) x|)
          ≤ B :=
      denomSecondDerivIntegral_le hβ hvC2 (hvnn τ hτ) hS₀nn hsup1 hsup2
    exact denomDecayBound hμ hσ0 hgm (hvnn τ hτ) hintB n hn

/-! ## 7. #1 closed UNCONDITIONALLY — the χ₀<0 flux H^σ envelope `genv`. -/

/-- **#1 CLOSED UNCONDITIONALLY.**  The χ₀<0 flux H^σ envelope `genv` is produced
from a `TrajectoryHSigmaEnvelope` `Uσ` (`= E.env`) PLUS the per-τ resolver/bridge
wiring, with NO carried denominator hypothesis: the τ-uniform denominator envelope
`D` is built here (`denomUniformEnvelope_of_trajectoryEnvelope`) and fed into the
landed `genv_of_traj_denom`.  This removes the last scalar residual `#1F` of `#1`. -/
theorem genv_of_trajectoryEnvelope_uncond {μ σ β t : ℝ} (hμ : 0 < μ)
    (hσ0 : 1 / 2 < σ) (hσ1 : σ < 3 / 2) (hβ : 0 ≤ β)
    {Q W vx : ℝ → ℝ → ℝ} {u v : ℝ → ℝ → ℝ}
    (E : TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (u τ)))
    (hvnn : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ x, 0 ≤ resolverValue μ (cosineCoeffs (u τ)) x)
    (hQ : ∀ τ, Q τ = fun x => W τ x * vx τ x)
    (hWdef : ∀ τ, W τ = fun x => u τ x
      * (1 + resolverValue μ (cosineCoeffs (u τ)) x) ^ (-β))
    (hbr : ∀ τ ∈ Set.Icc (0:ℝ) t,
      ShenWork.Paper2.IntervalWienerAlgebra.CosineMulBridge (u τ)
        (fun x => (1 + resolverValue μ (cosineCoeffs (u τ)) x) ^ (-β)))
    (heU : ∀ τ ∈ Set.Icc (0:ℝ) t, Envelopes E.env (cosineCoeffs (u τ)))
    (hbridge : ∀ τ ∈ Set.Icc (0:ℝ) t,
      ShenWork.Paper2.IntervalMixedProduct.MixedMulBridge (W τ) (vx τ))
    (hvrel : ∀ τ ∈ Set.Icc (0:ℝ) t,
      Envelopes (ShenWork.Paper2.HSigmaScale.resolverCoeff 1 E.env) (cosineCoeffs (v τ)))
    (hdiv : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
      |ShenWork.Paper2.IntervalDivergenceModeIdentity.sineCoeffs (vx τ) k|
        = Real.sqrt (ShenWork.Paper2.HSigmaScale.lam k)
          * |cosineCoeffs (v τ) k|) :
    MemHSigma σ
        (ShenWork.Paper2.IntervalWienerAlgebra.trueCosProd
          (ShenWork.Paper2.IntervalGWProductEnvelope.gW E.env
            (denomUniformEnvelope_of_trajectoryEnvelope hμ hσ0 hσ1 hβ E hvnn).Gden)
          (ShenWork.Paper2.IntervalFluxFactorEnvelope.sineEnv E.env)) ∧
      ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
        |ShenWork.Paper2.IntervalDivergenceModeIdentity.sineCoeffs (Q τ) k|
          ≤ ShenWork.Paper2.IntervalWienerAlgebra.trueCosProd
              (ShenWork.Paper2.IntervalGWProductEnvelope.gW E.env
                (denomUniformEnvelope_of_trajectoryEnvelope hμ hσ0 hσ1 hβ E hvnn).Gden)
              (ShenWork.Paper2.IntervalFluxFactorEnvelope.sineEnv E.env) k :=
  genv_of_traj_denom hσ0 E.henv
    (denomUniformEnvelope_of_trajectoryEnvelope hμ hσ0 hσ1 hβ E hvnn)
    hQ hWdef hbr heU hbridge hvrel hdiv

#print axioms resolverMode_le
#print axioms memHSigma_of_envelope
#print axioms resolverGrad_sup_le
#print axioms resolverGrad2_sup_le
#print axioms denomSecondDeriv_abs_le
#print axioms denomSecondDerivIntegral_le
#print axioms denomDecayBound
#print axioms denomUniformEnvelope_of_trajectoryEnvelope
#print axioms genv_of_trajectoryEnvelope_uncond

end ShenWork.Paper2.IntervalDenomSecondDerivBound
