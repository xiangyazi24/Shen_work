/-
  ShenWork/Paper2/IntervalCompactSliceGradientBounds.lean

  COMPACT-localized, σ-uniform gradient / Hessian bounds for the Picard limit
  slice `u(σ)` via its cosine-series representation.

  A TIME-UNIFORM gradient bound on all of `(0,T)` is FALSE for merely-continuous
  initial data (parabolic smoothing `~σ^{-1/2}` blow-up as `σ → 0⁺`).  The
  correct, satisfiable statement localizes to compact subwindows
  `[a', b'] ⊂ (0,T)`, where the eigenvalue-weighted coefficient envelope
  `M₀ λ_k e^{-a' λ_k} + env_k` is summable and σ-uniform (monotonicity of
  `e^{-σλ}` in `σ`).

  ## Deliverables (namespace `ShenWork.Paper2.CompactSliceGradientBounds`)

  A.  `eigenvalue_mul_abs_limitCoeff_le_uniform` — σ-uniform eigenvalue-weighted
      envelope on `[a', ∞) ∩ (·, T]` for `limitCoeff`, mirroring
      `summable_eigenvalue_mul_abs_limitCoeff_weak` with `e^{-σλ}` replaced by the
      σ-monotone `e^{-a' λ}`.  Plus `envelope_summable`.
  B.  Series derivative bounds (analytic core): per-term and series tsum bounds for
      `deriv` / `deriv∘deriv` of `∑ c_k cos(kπx)` against the eigenvalue envelope.
  C.  `deriv_lift_bound_on_compact` / `deriv2_lift_bound_on_compact` — the
      gradient / Hessian bounds on `[a', b'] × [0,1]`, with junk-deriv handling at
      the (non-differentiable) endpoints.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalPicardLimitRestartWeak

open MeasureTheory Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalPicardLimitRestartWeak (DuhamelSourceL1ContOn)
-- `summable_eigenvalue_mul_abs_limitCoeff_weak` and
-- `eigenvalue_mul_abs_duhamelSpectralCoeff_le_envelope` live in the ROOT
-- namespace (after `end ShenWork.IntervalPicardLimitRestartWeak`), so they are
-- referenced by bare name.
open ShenWork.IntervalDuhamelClosedC2
  (duhamelSpectralCoeff cosineCoeffSeries_grad_hasDerivAt
   cosineCoeffSeries_deriv2_eq)
open ShenWork.IntervalMildRegularityBootstrap
  (unitIntervalCosineEigenvalue_mul_exp_summable)

namespace ShenWork.Paper2.CompactSliceGradientBounds

open ShenWork.IntervalPicardLimitRestart (limitCoeff)

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## A. σ-uniform eigenvalue-weighted envelope for `limitCoeff` on `[a', T]`.

The weak engine derives the pointwise bound
`λ_k |limitCoeff σ k| ≤ M₀ λ_k e^{-σ λ_k} + env_k`.  Replacing `e^{-σ λ_k}` by
`e^{-a' λ_k}` (monotone in `σ ≥ a'`) gives a σ-UNIFORM envelope valid for every
`σ ∈ [a', T]`. -/

/-- **σ-uniform eigenvalue-weighted envelope on a compact window.**
For `0 < a' ≤ σ ≤ T` and every mode `k`,
`λ_k |limitCoeff σ k| ≤ M₀ (λ_k e^{-a' λ_k}) + env_k`.  Mirrors the σ-dependent
bound inside `summable_eigenvalue_mul_abs_limitCoeff_weak`, with the homogeneous
part frozen at `a'` via `Real.exp` monotonicity and the Duhamel part supplied by
`eigenvalue_mul_abs_duhamelSpectralCoeff_le_envelope`. -/
theorem eigenvalue_mul_abs_limitCoeff_le_uniform
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {T : ℝ}
    (hsrc0 : DuhamelSourceL1ContOn
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k) T)
    {a' : ℝ} (ha' : 0 < a') {σ : ℝ} (hσ : a' ≤ σ) (hσT : σ ≤ T) (k : ℕ) :
    unitIntervalCosineEigenvalue k * |limitCoeff p u₀ u σ k|
      ≤ M₀ * (unitIntervalCosineEigenvalue k * Real.exp (-a' * unitIntervalCosineEigenvalue k))
        + hsrc0.envelope k := by
  have hσpos : 0 < σ := lt_of_lt_of_le ha' hσ
  have heig_nn : 0 ≤ (λ_ k) := by unfold unitIntervalCosineEigenvalue; positivity
  -- λ_k |limitCoeff σ k| ≤ M₀·λ_k·e^{-σλ_k} + env_k  (the σ-bound).
  have hbound_sigma :
      (λ_ k) * |limitCoeff p u₀ u σ k|
        ≤ M₀ * ((λ_ k) * Real.exp (-σ * (λ_ k))) + hsrc0.envelope k := by
    unfold ShenWork.IntervalPicardLimitRestart.limitCoeff
    calc (λ_ k) * |Real.exp (-σ * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k
            + duhamelSpectralCoeff (fun s k => cosineCoeffs (logisticLifted p (u s)) k) σ k|
        ≤ (λ_ k) * (|Real.exp (-σ * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k|
            + |duhamelSpectralCoeff (fun s k => cosineCoeffs (logisticLifted p (u s)) k) σ k|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) heig_nn
      _ = (λ_ k) * |Real.exp (-σ * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k|
            + (λ_ k) * |duhamelSpectralCoeff (fun s k => cosineCoeffs (logisticLifted p (u s)) k) σ k| := by ring
      _ ≤ M₀ * ((λ_ k) * Real.exp (-σ * (λ_ k))) + hsrc0.envelope k := by
          apply add_le_add
          · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
            calc (λ_ k) * (Real.exp (-σ * (λ_ k)) *
                    |cosineCoeffs (intervalDomainLift u₀) k|)
                ≤ (λ_ k) * (Real.exp (-σ * (λ_ k)) * M₀) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left (hu₀_bound k) (Real.exp_pos _).le) heig_nn
              _ = M₀ * ((λ_ k) * Real.exp (-σ * (λ_ k))) := by ring
          · exact eigenvalue_mul_abs_duhamelSpectralCoeff_le_envelope hsrc0 hσpos hσT k
  -- Monotonicity: e^{-σλ_k} ≤ e^{-a'λ_k} since σ ≥ a' and λ_k ≥ 0.
  have hexp_mono : Real.exp (-σ * (λ_ k)) ≤ Real.exp (-a' * (λ_ k)) :=
    Real.exp_le_exp.mpr (by nlinarith [heig_nn, hσ])
  have hstep :
      M₀ * ((λ_ k) * Real.exp (-σ * (λ_ k)))
        ≤ M₀ * ((λ_ k) * Real.exp (-a' * (λ_ k))) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hexp_mono heig_nn) hM₀
  exact le_trans hbound_sigma (add_le_add hstep le_rfl)

/-- **Summability of the σ-uniform envelope.**
`∑ₖ (M₀·λ_k·e^{-a' λ_k} + env_k) < ∞`: homogeneous part is the parabolic-gain
series `λ_k e^{-a' λ_k}`, source part is `hsrc0.envelope`. -/
theorem envelope_summable
    {a : ℝ → ℕ → ℝ} {T : ℝ} (hsrc0 : DuhamelSourceL1ContOn a T)
    {M₀ : ℝ} {a' : ℝ} (ha' : 0 < a') :
    Summable (fun k => M₀ * (unitIntervalCosineEigenvalue k
        * Real.exp (-a' * unitIntervalCosineEigenvalue k)) + hsrc0.envelope k) :=
  ((unitIntervalCosineEigenvalue_mul_exp_summable ha').mul_left M₀).add hsrc0.henv_summable

/-! ## The σ-uniform envelope as a function of `k`. -/

/-- The σ-uniform envelope (for fixed `M₀, a'` and a source envelope `env`). -/
noncomputable def envU (env : ℕ → ℝ) (M₀ a' : ℝ) (k : ℕ) : ℝ :=
  M₀ * (unitIntervalCosineEigenvalue k * Real.exp (-a' * unitIntervalCosineEigenvalue k))
    + env k

theorem envU_nonneg {env : ℕ → ℝ} (henv : ∀ k, 0 ≤ env k)
    {M₀ : ℝ} (hM₀ : 0 ≤ M₀) {a' : ℝ} (k : ℕ) : 0 ≤ envU env M₀ a' k := by
  have h1 : 0 ≤ M₀ * (unitIntervalCosineEigenvalue k
      * Real.exp (-a' * unitIntervalCosineEigenvalue k)) :=
    mul_nonneg hM₀ (mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity)
      (Real.exp_nonneg _))
  unfold envU; linarith [henv k]

theorem envU_summable
    {a : ℝ → ℕ → ℝ} {T : ℝ} (hsrc0 : DuhamelSourceL1ContOn a T)
    {M₀ : ℝ} {a' : ℝ} (ha' : 0 < a') :
    Summable (envU hsrc0.envelope M₀ a') :=
  envelope_summable hsrc0 ha'

/-! ## B. Series derivative bounds (the analytic core).

For a coefficient sequence `c` with `Summable (λ_k |c k|)`, the cosine series
`g x = ∑' k, c k · cosineMode k x` has `deriv g x` and `deriv (deriv g) x`
expressible as tsums (via `cosineCoeffSeries_grad_hasDerivAt` and
`cosineCoeffSeries_deriv2_eq`); we bound them termwise by `λ_k |c k|`. -/

/-- Per-term gradient bound: `|c n·(-(nπ)·sin(nπx))| ≤ (nπ)|c n| ≤ λ_n|c n|`. -/
theorem grad_term_abs_le (c : ℕ → ℝ) (x : ℝ) (n : ℕ) :
    |c n * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * x))|
      ≤ unitIntervalCosineEigenvalue n * |c n| := by
  have hterm : |c n * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * x))|
      ≤ ((n : ℝ) * Real.pi) * |c n| := by
    rw [abs_mul, abs_mul, abs_neg]
    calc |c n| * (|(n : ℝ) * Real.pi| * |Real.sin ((n : ℝ) * Real.pi * x)|)
        ≤ |c n| * (((n : ℝ) * Real.pi) * 1) := by
          gcongr
          · rw [abs_of_nonneg (by positivity)]
          · exact Real.abs_sin_le_one _
      _ = ((n : ℝ) * Real.pi) * |c n| := by ring
  have hle : ((n : ℝ) * Real.pi) ≤ unitIntervalCosineEigenvalue n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [unitIntervalCosineEigenvalue]
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      have hnpi : (1 : ℝ) ≤ (n : ℝ) * Real.pi := by nlinarith [Real.two_le_pi, hn1]
      unfold unitIntervalCosineEigenvalue; nlinarith [hnpi]
  exact le_trans hterm (mul_le_mul_of_nonneg_right hle (abs_nonneg _))

/-- Per-term second-derivative bound:
`|c n·(-(nπ)²·cos(nπx))| ≤ λ_n|c n|`. -/
theorem grad2_term_abs_le (c : ℕ → ℝ) (x : ℝ) (n : ℕ) :
    |c n * (-(((n : ℝ) * Real.pi) ^ 2) * Real.cos ((n : ℝ) * Real.pi * x))|
      ≤ unitIntervalCosineEigenvalue n * |c n| := by
  rw [abs_mul, abs_mul, abs_neg]
  have hlam : unitIntervalCosineEigenvalue n = ((n : ℝ) * Real.pi) ^ 2 := by
    unfold unitIntervalCosineEigenvalue; ring
  rw [hlam, mul_comm]
  calc (|((n : ℝ) * Real.pi) ^ 2| * |Real.cos ((n : ℝ) * Real.pi * x)|) * |c n|
      ≤ (((n : ℝ) * Real.pi) ^ 2 * 1) * |c n| := by
        gcongr
        · rw [abs_of_nonneg (by positivity)]
        · exact Real.abs_cos_le_one _
    _ = ((n : ℝ) * Real.pi) ^ 2 * |c n| := by ring

/-- Generic gradient-series absolute bound: if `λ_n|c n|` is dominated by a
summable envelope `E`, then `|deriv (∑' cₙcos)|(x) ≤ ∑ E`. -/
theorem grad_series_abs_le (c E : ℕ → ℝ) (x : ℝ)
    (hE_summable : Summable E)
    (hcE : ∀ n, unitIntervalCosineEigenvalue n * |c n| ≤ E n) :
    |∑' n, c n * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * x))|
      ≤ ∑' n, E n := by
  have hterm : ∀ n, |c n * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * x))| ≤ E n :=
    fun n => le_trans (grad_term_abs_le c x n) (hcE n)
  have hsum_absg : Summable (fun n =>
      ‖c n * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * x))‖) :=
    hE_summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => by rw [Real.norm_eq_abs]; exact hterm n)
  rw [← Real.norm_eq_abs]
  refine le_trans (norm_tsum_le_tsum_norm hsum_absg) ?_
  refine Summable.tsum_le_tsum (fun n => ?_) hsum_absg hE_summable
  rw [Real.norm_eq_abs]; exact hterm n

/-- Generic second-derivative-series absolute bound. -/
theorem grad2_series_abs_le (c E : ℕ → ℝ) (x : ℝ)
    (hE_summable : Summable E)
    (hcE : ∀ n, unitIntervalCosineEigenvalue n * |c n| ≤ E n) :
    |∑' n, c n * (-(((n : ℝ) * Real.pi) ^ 2) * Real.cos ((n : ℝ) * Real.pi * x))|
      ≤ ∑' n, E n := by
  have hterm : ∀ n, |c n * (-(((n : ℝ) * Real.pi) ^ 2) * Real.cos ((n : ℝ) * Real.pi * x))| ≤ E n :=
    fun n => le_trans (grad2_term_abs_le c x n) (hcE n)
  have hsum_absg : Summable (fun n =>
      ‖c n * (-(((n : ℝ) * Real.pi) ^ 2) * Real.cos ((n : ℝ) * Real.pi * x))‖) :=
    hE_summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => by rw [Real.norm_eq_abs]; exact hterm n)
  rw [← Real.norm_eq_abs]
  refine le_trans (norm_tsum_le_tsum_norm hsum_absg) ?_
  refine Summable.tsum_le_tsum (fun n => ?_) hsum_absg hE_summable
  rw [Real.norm_eq_abs]; exact hterm n

/-! ## Endpoint non-differentiability / junk-derivative bookkeeping.

The zero-extension lift jumps at `0` (and `1`): `lift(0) = u(σ,0) > 0` but
`lift(x) = 0` for `x < 0`.  So the lift is not differentiable at `0,1`, and the
deriv there is junk `0`; likewise the second deriv at the endpoints is `0`. -/

/-- The lift of `u σ` is NOT differentiable at the left endpoint `0` when its
value there is strictly positive (jump from `0` on `Iio 0`). -/
theorem not_differentiableAt_lift_left (u : ℝ → intervalDomainPoint → ℝ) (σ : ℝ)
    (hval : 0 < intervalDomainLift (u σ) 0) :
    ¬ DifferentiableAt ℝ (intervalDomainLift (u σ)) 0 := by
  intro hdiff
  have hcont := hdiff.continuousAt
  have htleft : Filter.Tendsto (intervalDomainLift (u σ))
      (nhdsWithin 0 (Set.Iio 0)) (nhds (intervalDomainLift (u σ) 0)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hlift0 : (intervalDomainLift (u σ)) =ᶠ[nhdsWithin 0 (Set.Iio 0)] (fun _ => 0) := by
    filter_upwards [self_mem_nhdsWithin] with x (hx : x < 0)
    simp [intervalDomainLift,
      show ¬((x : ℝ) ∈ Set.Icc 0 1) from fun h => absurd h.1 (not_le.mpr hx)]
  have htleft0 : Filter.Tendsto (fun _ : ℝ => (0 : ℝ))
      (nhdsWithin 0 (Set.Iio 0)) (nhds (intervalDomainLift (u σ) 0)) :=
    htleft.congr' hlift0
  have heq : intervalDomainLift (u σ) 0 = 0 :=
    tendsto_nhds_unique htleft0 tendsto_const_nhds
  linarith

/-- The lift of `u σ` is NOT differentiable at the right endpoint `1` when its
value there is strictly positive (jump to `0` on `Ioi 1`). -/
theorem not_differentiableAt_lift_right (u : ℝ → intervalDomainPoint → ℝ) (σ : ℝ)
    (hval : 0 < intervalDomainLift (u σ) 1) :
    ¬ DifferentiableAt ℝ (intervalDomainLift (u σ)) 1 := by
  intro hdiff
  have hcont := hdiff.continuousAt
  have htright : Filter.Tendsto (intervalDomainLift (u σ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (intervalDomainLift (u σ) 1)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hlift0 : (intervalDomainLift (u σ)) =ᶠ[nhdsWithin 1 (Set.Ioi 1)] (fun _ => 0) := by
    filter_upwards [self_mem_nhdsWithin] with x (hx : (1 : ℝ) < x)
    simp [intervalDomainLift,
      show ¬((x : ℝ) ∈ Set.Icc 0 1) from fun h => absurd h.2 (not_le.mpr hx)]
  have htright0 : Filter.Tendsto (fun _ : ℝ => (0 : ℝ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (intervalDomainLift (u σ) 1)) :=
    htright.congr' hlift0
  have heq : intervalDomainLift (u σ) 1 = 0 :=
    tendsto_nhds_unique htright0 tendsto_const_nhds
  linarith

/-- `deriv (lift (u σ))` is identically `0` on `Iio 0` (lift `≡ 0` there). -/
theorem deriv_lift_eq_zero_on_Iio (u : ℝ → intervalDomainPoint → ℝ) (σ : ℝ) :
    Set.EqOn (deriv (intervalDomainLift (u σ))) (fun _ => 0) (Set.Iio 0) := by
  intro y hy
  have hloc : intervalDomainLift (u σ) =ᶠ[nhds y] (fun _ => 0) := by
    have hmem : Set.Iio (0:ℝ) ∈ nhds y := isOpen_Iio.mem_nhds hy
    filter_upwards [hmem] with z (hz : z < 0)
    simp [intervalDomainLift,
      show ¬((z : ℝ) ∈ Set.Icc 0 1) from fun h => absurd h.1 (not_le.mpr hz)]
  rw [hloc.deriv_eq]; simp

/-- `deriv (lift (u σ))` is identically `0` on `Ioi 1`. -/
theorem deriv_lift_eq_zero_on_Ioi (u : ℝ → intervalDomainPoint → ℝ) (σ : ℝ) :
    Set.EqOn (deriv (intervalDomainLift (u σ))) (fun _ => 0) (Set.Ioi 1) := by
  intro y hy
  have hloc : intervalDomainLift (u σ) =ᶠ[nhds y] (fun _ => 0) := by
    have hmem : Set.Ioi (1:ℝ) ∈ nhds y := isOpen_Ioi.mem_nhds hy
    filter_upwards [hmem] with z (hz : (1:ℝ) < z)
    simp [intervalDomainLift,
      show ¬((z : ℝ) ∈ Set.Icc 0 1) from fun h => absurd h.2 (not_le.mpr hz)]
  rw [hloc.deriv_eq]; simp

/-- `deriv (lift (u σ)) 0 = 0` unconditionally: if not differentiable at `0` it
is junk `0`; otherwise the left-derivative (from `Iio 0` where lift `≡ 0`) forces
the derivative to be `0` (`UniqueDiffWithinAt.eq_deriv` on `Iio 0`). -/
theorem deriv_lift_eq_zero_at_left (u : ℝ → intervalDomainPoint → ℝ) (σ : ℝ) :
    deriv (intervalDomainLift (u σ)) 0 = 0 := by
  by_cases hd : DifferentiableAt ℝ (intervalDomainLift (u σ)) 0
  · have hwithin : HasDerivWithinAt (intervalDomainLift (u σ))
        (deriv (intervalDomainLift (u σ)) 0) (Set.Iio 0) 0 :=
      hd.hasDerivAt.hasDerivWithinAt
    have hcong : intervalDomainLift (u σ) =ᶠ[nhdsWithin 0 (Set.Iio 0)] (fun _ => 0) := by
      filter_upwards [self_mem_nhdsWithin] with z (hz : z < 0)
      simp [intervalDomainLift,
        show ¬((z : ℝ) ∈ Set.Icc 0 1) from fun h => absurd h.1 (not_le.mpr hz)]
    -- lift 0 = 0 (continuity from the left, lift ≡ 0 there).
    have hpt : intervalDomainLift (u σ) 0 = 0 := by
      have hcont := hd.continuousAt
      have htleft : Filter.Tendsto (intervalDomainLift (u σ))
          (nhdsWithin 0 (Set.Iio 0)) (nhds (intervalDomainLift (u σ) 0)) :=
        hcont.tendsto.mono_left nhdsWithin_le_nhds
      have htleft0 : Filter.Tendsto (fun _ : ℝ => (0:ℝ))
          (nhdsWithin 0 (Set.Iio 0)) (nhds (intervalDomainLift (u σ) 0)) :=
        htleft.congr' hcong
      exact tendsto_nhds_unique htleft0 tendsto_const_nhds
    have hconst : HasDerivWithinAt (intervalDomainLift (u σ)) 0 (Set.Iio 0) 0 :=
      (hasDerivWithinAt_const (0:ℝ) (Set.Iio 0) (0:ℝ)).congr_of_eventuallyEq hcong hpt
    exact UniqueDiffWithinAt.eq_deriv (Set.Iio 0) (uniqueDiffWithinAt_Iio 0) hwithin hconst
  · exact deriv_zero_of_not_differentiableAt hd

/-- `deriv (lift (u σ)) 1 = 0` unconditionally. -/
theorem deriv_lift_eq_zero_at_right (u : ℝ → intervalDomainPoint → ℝ) (σ : ℝ) :
    deriv (intervalDomainLift (u σ)) 1 = 0 := by
  by_cases hd : DifferentiableAt ℝ (intervalDomainLift (u σ)) 1
  · have hwithin : HasDerivWithinAt (intervalDomainLift (u σ))
        (deriv (intervalDomainLift (u σ)) 1) (Set.Ioi 1) 1 :=
      hd.hasDerivAt.hasDerivWithinAt
    have hcong : intervalDomainLift (u σ) =ᶠ[nhdsWithin 1 (Set.Ioi 1)] (fun _ => 0) := by
      filter_upwards [self_mem_nhdsWithin] with z (hz : (1:ℝ) < z)
      simp [intervalDomainLift,
        show ¬((z : ℝ) ∈ Set.Icc 0 1) from fun h => absurd h.2 (not_le.mpr hz)]
    have hpt : intervalDomainLift (u σ) 1 = 0 := by
      have hcont := hd.continuousAt
      have htright : Filter.Tendsto (intervalDomainLift (u σ))
          (nhdsWithin 1 (Set.Ioi 1)) (nhds (intervalDomainLift (u σ) 1)) :=
        hcont.tendsto.mono_left nhdsWithin_le_nhds
      have htright0 : Filter.Tendsto (fun _ : ℝ => (0:ℝ))
          (nhdsWithin 1 (Set.Ioi 1)) (nhds (intervalDomainLift (u σ) 1)) :=
        htright.congr' hcong
      exact tendsto_nhds_unique htright0 tendsto_const_nhds
    have hconst : HasDerivWithinAt (intervalDomainLift (u σ)) 0 (Set.Ioi 1) 1 :=
      (hasDerivWithinAt_const (1:ℝ) (Set.Ioi 1) (0:ℝ)).congr_of_eventuallyEq hcong hpt
    exact UniqueDiffWithinAt.eq_deriv (Set.Ioi 1) (uniqueDiffWithinAt_Ioi 1) hwithin hconst
  · exact deriv_zero_of_not_differentiableAt hd

/-- **Second derivative of the lift vanishes at the left endpoint `0`.**
`deriv(lift)` is `0` both AT `0` and on `Iio 0`, so locally `0` to the left;
either not differentiable at `0` (junk `0`) or matched against the const-`0`
left-derivative. -/
theorem deriv2_lift_eq_zero_left (u : ℝ → intervalDomainPoint → ℝ) (σ : ℝ) :
    deriv (deriv (intervalDomainLift (u σ))) 0 = 0 := by
  by_cases hd : DifferentiableAt ℝ (deriv (intervalDomainLift (u σ))) 0
  · have hwithin : HasDerivWithinAt (deriv (intervalDomainLift (u σ)))
        (deriv (deriv (intervalDomainLift (u σ))) 0) (Set.Iio 0) 0 :=
      hd.hasDerivAt.hasDerivWithinAt
    have hcong : deriv (intervalDomainLift (u σ))
        =ᶠ[nhdsWithin 0 (Set.Iio 0)] (fun _ => 0) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact deriv_lift_eq_zero_on_Iio u σ hy
    have hconst : HasDerivWithinAt (deriv (intervalDomainLift (u σ))) 0 (Set.Iio 0) 0 :=
      (hasDerivWithinAt_const (0:ℝ) (Set.Iio 0) (0:ℝ)).congr_of_eventuallyEq hcong
        (deriv_lift_eq_zero_at_left u σ)
    exact UniqueDiffWithinAt.eq_deriv (Set.Iio 0) (uniqueDiffWithinAt_Iio 0) hwithin hconst
  · exact deriv_zero_of_not_differentiableAt hd

/-- **Second derivative of the lift vanishes at the right endpoint `1`.** -/
theorem deriv2_lift_eq_zero_right (u : ℝ → intervalDomainPoint → ℝ) (σ : ℝ) :
    deriv (deriv (intervalDomainLift (u σ))) 1 = 0 := by
  by_cases hd : DifferentiableAt ℝ (deriv (intervalDomainLift (u σ))) 1
  · have hwithin : HasDerivWithinAt (deriv (intervalDomainLift (u σ)))
        (deriv (deriv (intervalDomainLift (u σ))) 1) (Set.Ioi 1) 1 :=
      hd.hasDerivAt.hasDerivWithinAt
    have hcong : deriv (intervalDomainLift (u σ))
        =ᶠ[nhdsWithin 1 (Set.Ioi 1)] (fun _ => 0) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact deriv_lift_eq_zero_on_Ioi u σ hy
    have hconst : HasDerivWithinAt (deriv (intervalDomainLift (u σ))) 0 (Set.Ioi 1) 1 :=
      (hasDerivWithinAt_const (1:ℝ) (Set.Ioi 1) (0:ℝ)).congr_of_eventuallyEq hcong
        (deriv_lift_eq_zero_at_right u σ)
    exact UniqueDiffWithinAt.eq_deriv (Set.Ioi 1) (uniqueDiffWithinAt_Ioi 1) hwithin hconst
  · exact deriv_zero_of_not_differentiableAt hd

/-! ## C. The producers — gradient / Hessian bounds on a compact window. -/

/-- **Gradient bound on a compact window `[a', b'] ⊂ (0,T)`.**
With `G1 := ∑ₖ envU k`, for every `σ ∈ [a', b']` and `x ∈ [0,1]`,
`|deriv (lift (u σ)) x| ≤ G1`.  Interior `x` uses the series-deriv transfer via
`EventuallyEq.deriv_eq` (lift agrees with the series on the open `Ioo 0 1`);
endpoints use junk-deriv (`= 0`) from non-differentiability of the lift. -/
theorem deriv_lift_bound_on_compact
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {T : ℝ}
    (hsrc0 : DuhamelSourceL1ContOn
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k) T)
    (hagree : ∀ σ, 0 < σ → σ < T → Set.EqOn (intervalDomainLift (u σ))
      (fun x => ∑' n, limitCoeff p u₀ u σ n * cosineMode n x) (Set.Icc (0:ℝ) 1))
    (hpost : ∀ σ, 0 < σ → σ < T → ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < intervalDomainLift (u σ) x)
    {a' b' : ℝ} (ha' : 0 < a') (hb'T : b' < T) :
    ∃ G1, 0 ≤ G1 ∧ ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0:ℝ) 1,
      |deriv (intervalDomainLift (u σ)) x| ≤ G1 := by
  by_cases hab : a' ≤ b'
  · -- inhabited window: 0 < a' ≤ b' < T gives 0 < T, hence envelope nonneg.
    have hTpos : 0 < T := lt_of_le_of_lt (le_trans ha'.le hab) hb'T
    have henv_nn : ∀ k, 0 ≤ hsrc0.envelope k :=
      fun k => le_trans (abs_nonneg _) (hsrc0.henv_bound 0 le_rfl hTpos.le k)
    have hsumU : Summable (envU hsrc0.envelope M₀ a') := envU_summable hsrc0 ha'
    refine ⟨∑' k, envU hsrc0.envelope M₀ a' k,
      tsum_nonneg (fun k => envU_nonneg henv_nn hM₀ k), ?_⟩
    intro σ hσ x hx
    obtain ⟨hσa, hσb⟩ := hσ
    have hσpos : 0 < σ := lt_of_lt_of_le ha' hσa
    have hσT : σ < T := lt_of_le_of_lt hσb hb'T
    have hσT' : σ ≤ T := hσT.le
    have hbsum : Summable (fun k => unitIntervalCosineEigenvalue k
          * |limitCoeff p u₀ u σ k|) :=
      summable_eigenvalue_mul_abs_limitCoeff_weak p u₀ u hM₀ hu₀_bound hsrc0 hσpos hσT'
    have henvU : ∀ k, unitIntervalCosineEigenvalue k * |limitCoeff p u₀ u σ k|
        ≤ envU hsrc0.envelope M₀ a' k :=
      fun k => eigenvalue_mul_abs_limitCoeff_le_uniform p u₀ u hM₀ hu₀_bound hsrc0 ha'
        hσa hσT' k
    -- series-derivative formula at x and its tsum bound.
    have hgrad_bound : |∑' n, limitCoeff p u₀ u σ n
          * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * x))|
        ≤ ∑' k, envU hsrc0.envelope M₀ a' k :=
      grad_series_abs_le (fun n => limitCoeff p u₀ u σ n) (envU hsrc0.envelope M₀ a') x
        hsumU henvU
    rcases eq_or_lt_of_le hx.1 with hx0 | hx0
    · -- x = 0 endpoint.
      have hnd : ¬ DifferentiableAt ℝ (intervalDomainLift (u σ)) x := by
        rw [← hx0]
        exact not_differentiableAt_lift_left u σ
          (hpost σ hσpos hσT 0 (Set.left_mem_Icc.mpr zero_le_one))
      rw [deriv_zero_of_not_differentiableAt hnd, abs_zero]
      exact tsum_nonneg (fun k => envU_nonneg henv_nn hM₀ k)
    · rcases eq_or_lt_of_le hx.2 with hx1 | hx1
      · -- x = 1 endpoint.
        have hnd : ¬ DifferentiableAt ℝ (intervalDomainLift (u σ)) x := by
          rw [hx1]
          exact not_differentiableAt_lift_right u σ
            (hpost σ hσpos hσT 1 (Set.right_mem_Icc.mpr zero_le_one))
        rw [deriv_zero_of_not_differentiableAt hnd, abs_zero]
        exact tsum_nonneg (fun k => envU_nonneg henv_nn hM₀ k)
      · -- interior x ∈ (0,1).
        have hxIoo : x ∈ Set.Ioo (0:ℝ) 1 := ⟨hx0, hx1⟩
        have hEq : intervalDomainLift (u σ)
            =ᶠ[nhds x] (fun y => ∑' n, limitCoeff p u₀ u σ n * cosineMode n y) := by
          have hmem : Set.Ioo (0:ℝ) 1 ∈ nhds x := isOpen_Ioo.mem_nhds hxIoo
          filter_upwards [hmem] with y hy
          exact hagree σ hσpos hσT (Set.Ioo_subset_Icc_self hy)
        rw [hEq.deriv_eq, (cosineCoeffSeries_grad_hasDerivAt hbsum x).deriv]
        exact hgrad_bound
  · -- empty window: Icc a' b' = ∅, so the ∀ part is vacuous; take G1 = 0.
    refine ⟨0, le_rfl, ?_⟩
    intro σ hσ
    exact absurd (le_trans hσ.1 hσ.2) hab

/-- **Hessian (second-derivative) bound on a compact window `[a', b'] ⊂ (0,T)`.**
With `G2 := ∑ₖ envU k`, for every `σ ∈ [a', b']` and `x ∈ [0,1]`,
`|deriv (deriv (lift (u σ))) x| ≤ G2`.  Interior `x` transfers the second deriv
from the series (`cosineCoeffSeries_deriv2_eq`); endpoints give second deriv `= 0`
(`deriv2_lift_eq_zero_left/right`). -/
theorem deriv2_lift_bound_on_compact
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {T : ℝ}
    (hsrc0 : DuhamelSourceL1ContOn
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k) T)
    (hagree : ∀ σ, 0 < σ → σ < T → Set.EqOn (intervalDomainLift (u σ))
      (fun x => ∑' n, limitCoeff p u₀ u σ n * cosineMode n x) (Set.Icc (0:ℝ) 1))
    {a' b' : ℝ} (ha' : 0 < a') (hb'T : b' < T) :
    ∃ G2, 0 ≤ G2 ∧ ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0:ℝ) 1,
      |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2 := by
  by_cases hab : a' ≤ b'
  · have hTpos : 0 < T := lt_of_le_of_lt (le_trans ha'.le hab) hb'T
    have henv_nn : ∀ k, 0 ≤ hsrc0.envelope k :=
      fun k => le_trans (abs_nonneg _) (hsrc0.henv_bound 0 le_rfl hTpos.le k)
    have hsumU : Summable (envU hsrc0.envelope M₀ a') := envU_summable hsrc0 ha'
    refine ⟨∑' k, envU hsrc0.envelope M₀ a' k,
      tsum_nonneg (fun k => envU_nonneg henv_nn hM₀ k), ?_⟩
    intro σ hσ x hx
    obtain ⟨hσa, hσb⟩ := hσ
    have hσpos : 0 < σ := lt_of_lt_of_le ha' hσa
    have hσT : σ < T := lt_of_le_of_lt hσb hb'T
    have hσT' : σ ≤ T := hσT.le
    have hbsum : Summable (fun k => unitIntervalCosineEigenvalue k
          * |limitCoeff p u₀ u σ k|) :=
      summable_eigenvalue_mul_abs_limitCoeff_weak p u₀ u hM₀ hu₀_bound hsrc0 hσpos hσT'
    have henvU : ∀ k, unitIntervalCosineEigenvalue k * |limitCoeff p u₀ u σ k|
        ≤ envU hsrc0.envelope M₀ a' k :=
      fun k => eigenvalue_mul_abs_limitCoeff_le_uniform p u₀ u hM₀ hu₀_bound hsrc0 ha'
        hσa hσT' k
    have hgrad2_bound : |∑' n, limitCoeff p u₀ u σ n
          * (-(((n : ℝ) * Real.pi) ^ 2) * Real.cos ((n : ℝ) * Real.pi * x))|
        ≤ ∑' k, envU hsrc0.envelope M₀ a' k :=
      grad2_series_abs_le (fun n => limitCoeff p u₀ u σ n) (envU hsrc0.envelope M₀ a') x
        hsumU henvU
    rcases eq_or_lt_of_le hx.1 with hx0 | hx0
    · rw [← hx0, deriv2_lift_eq_zero_left u σ, abs_zero]
      exact tsum_nonneg (fun k => envU_nonneg henv_nn hM₀ k)
    · rcases eq_or_lt_of_le hx.2 with hx1 | hx1
      · rw [hx1, deriv2_lift_eq_zero_right u σ, abs_zero]
        exact tsum_nonneg (fun k => envU_nonneg henv_nn hM₀ k)
      · -- interior: lift =ᶠ series ⟹ deriv lift =ᶠ deriv series ⟹ deriv² equal.
        have hxIoo : x ∈ Set.Ioo (0:ℝ) 1 := ⟨hx0, hx1⟩
        have hEq : intervalDomainLift (u σ)
            =ᶠ[nhds x] (fun y => ∑' n, limitCoeff p u₀ u σ n * cosineMode n y) := by
          have hmem : Set.Ioo (0:ℝ) 1 ∈ nhds x := isOpen_Ioo.mem_nhds hxIoo
          filter_upwards [hmem] with y hy
          exact hagree σ hσpos hσT (Set.Ioo_subset_Icc_self hy)
        have hderiv_eq : deriv (intervalDomainLift (u σ))
            =ᶠ[nhds x] deriv (fun y => ∑' n, limitCoeff p u₀ u σ n * cosineMode n y) :=
          hEq.deriv
        rw [hderiv_eq.deriv_eq, cosineCoeffSeries_deriv2_eq hbsum x]
        exact hgrad2_bound
  · refine ⟨0, le_rfl, ?_⟩
    intro σ hσ
    exact absurd (le_trans hσ.1 hσ.2) hab

end ShenWork.Paper2.CompactSliceGradientBounds
