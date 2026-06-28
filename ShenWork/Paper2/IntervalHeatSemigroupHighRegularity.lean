/-
  ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean

  The heat semigroup `S(t)u₀ = ∑ exp(-t λ_k) û₀_k cos(kπx)` has eigenvalue-
  squared-weighted summability for t > 0, hence C⁴ spatial regularity via
  `cosineCoeffSeries_contDiff_four_of_eigenvalue_sq_summable`.

  ## §1 (Spatial regularity): 0 sorry — axiom-clean.
  ## §2 (Joint (t,x) C² regularity via smooth time cutoff):
  Uses `smoothRightCutoff` to localize in time.  The cutoff term
  `φ(t) · exp(-t λ_n) · â_n · cos(nπx)` has globally bounded iterated
  derivatives (φ kills the t < 0 blow-up, exponential decay handles t → ∞).
  `contDiff_tsum` gives `ContDiff ℝ 2` of the cutoff series; near points
  with `s₀ > c` the cutoff equals 1 so the cutoff series = original series,
  yielding `ContDiffAt ℝ 2`.

  0 sorry — axiom-clean.
  - `heatTerm_iteratedFDeriv_global_bound`:
    ‖D^j(heatTerm)‖ ≤ 4·(1+λ_n)^j · M₀ · exp(-(c/2)·λ_n) for q.1 ≥ c/2.
    Proved via Leibniz product rule + projection bounds + 1D derivative
    computation (iteratedDeriv_exp_const_mul, cosineMode bound).  The
    factor 4 absorbs 2^j ≤ 4 for j ≤ 2.
  - `smoothRightCutoff_iteratedFDeriv_bound_exists` (k ≥ 1 case):
    derivatives of the C² cutoff are globally bounded (compact support).
-/
import ShenWork.Paper2.IntervalParabolicDuhamelGainNonCircular
import ShenWork.Paper2.ChemMildC1etaComm
import ShenWork.PDE.IntervalResolverSpectralJointC2Cutoff
import ShenWork.PDE.IntervalResolverSpectralJointC2CutoffBounds
import ShenWork.PDE.IntervalResolverJointC2PhysicalConcrete
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalHeatSemigroupFlooredSourceTimeData
import Mathlib.Analysis.Calculus.SmoothSeries

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.Paper2.HeatSemigroupHighRegularity

/-- Eigenvalue-squared-weighted summability of heat semigroup coefficients.
For t > 0, `∑ λ_k² |exp(-tλ_k) û₀_k|` converges because:
`λ_k² |exp(-tλ_k)| |û₀_k| ≤ M₀ · λ_k² exp(-tλ_k)` and the latter sums
(by `eigenvalueSq_mul_exp_summable`). -/
theorem heatSemigroup_eigenvalueSq_summable
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun k => unitIntervalCosineEigenvalue k ^ 2 *
      |Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k|) := by
  have hM₀nn : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (by positivity) (abs_nonneg _))
    (fun k => ?_)
    ((ShenWork.Paper2.eigenvalueSq_mul_exp_summable ht).mul_right M₀)
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc unitIntervalCosineEigenvalue k ^ 2 *
      (Real.exp (-t * unitIntervalCosineEigenvalue k) *
        |cosineCoeffs (intervalDomainLift u₀) k|)
      ≤ unitIntervalCosineEigenvalue k ^ 2 *
        (Real.exp (-t * unitIntervalCosineEigenvalue k) * M₀) := by
        gcongr
        exact hu₀_bound k
    _ = unitIntervalCosineEigenvalue k ^ 2 *
        Real.exp (-t * unitIntervalCosineEigenvalue k) * M₀ := by ring

set_option maxHeartbeats 800000 in
/-- The heat semigroup applied to bounded initial data is C⁴ in space for t > 0. -/
theorem heatSemigroup_contDiff_four
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ 4 (fun x => ∑' k,
      (Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x) := by
  apply ShenWork.Paper2.ParabolicDuhamelGainNonCircular.cosineCoeffSeries_contDiff_four_of_eigenvalue_sq_summable
  convert heatSemigroup_eigenvalueSq_summable hu₀_bound ht using 1
  ext k; ring

#print axioms heatSemigroup_eigenvalueSq_summable
#print axioms heatSemigroup_contDiff_four

end ShenWork.Paper2.HeatSemigroupHighRegularity

/-! ## Joint `(t,x)` C² regularity of the heat semigroup cosine series

The uncurried map `(t,x) ↦ ∑' k, exp(-t λ_k) â_k cos(kπx)` is `ContDiffAt ℝ 2`
at every point with positive time coordinate.

**Strategy (smooth time cutoff).**  Fix `c > 0` and `s₀ > c`.  Set
`φ := smoothRightCutoff (c/2) c` — a smooth function that is 0 on `(-∞, c/2]`
and 1 on `[c, ∞)`.  The *cutoff heat term*
  `(t,x) ↦ φ(t) · exp(-t lam) · ahat · cos(nπx)`
is C∞ and its iterated derivatives are globally bounded:
  - for `t ≤ c/2`:  φ(t) = 0 so the term and all its derivatives vanish;
  - for `t ≥ c/2`:  `exp(-t lam) ≤ exp(-(c/2) lam)` and φ derivatives are
    bounded (φ is compactly-supported on `[c/2, c]` with respect to derivatives).
The global bound has the shape `C_k · (1+lam)^k · M₀ · exp(-(c/2) lam)`,
which is summable (polynomial × exp decay).  Applying `contDiff_tsum` gives
`ContDiff ℝ 2` of the cutoff series.  Near `(s₀, x₀)` with `s₀ > c`, φ = 1,
so the cutoff series = original series, giving `ContDiffAt ℝ 2`.
-/

namespace ShenWork.Paper2.HeatSemigroupJointRegularity

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalResolverSpectralJointC2Cutoff (smoothRightCutoff
  smoothRightCutoff_contDiff smoothRightCutoff_eq_zero_of_le
  smoothRightCutoff_eq_one_of_ge smoothRightCutoff_eventually_eq_one)
open ShenWork.IntervalResolverSpectralJointC2CutoffBounds
  (norm_iteratedFDeriv_comp_fst_le norm_iteratedFDeriv_comp_snd_le)

noncomputable section

/-- The `n`-th term of the heat semigroup series, as a function of `(t, x)`:
`(t, x) ↦ exp(-t lam) · ahat · cos(nπx)`. -/
def heatTerm (u₀ : intervalDomainPoint → ℝ) (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q => (Real.exp (-q.1 * unitIntervalCosineEigenvalue n) *
    cosineCoeffs (intervalDomainLift u₀) n) * cosineMode n q.2

/-- Each heat term is `C∞` in `(t,x)` (product of smooth factors). -/
theorem heatTerm_contDiff (u₀ : intervalDomainPoint → ℝ) (n : ℕ) :
    ContDiff ℝ ⊤ (heatTerm u₀ n) := by
  unfold heatTerm
  have hexp : ContDiff ℝ ⊤
      (fun q : ℝ × ℝ => Real.exp (-q.1 * unitIntervalCosineEigenvalue n)) := by
    have : ContDiff ℝ ⊤ (fun t : ℝ => Real.exp (-t * unitIntervalCosineEigenvalue n)) := by
      fun_prop
    exact this.comp contDiff_fst
  have hcoeff : ContDiff ℝ ⊤
      (fun _ : ℝ × ℝ => cosineCoeffs (intervalDomainLift u₀) n) :=
    contDiff_const
  have hcos : ContDiff ℝ ⊤ (fun q : ℝ × ℝ => cosineMode n q.2) := by
    have h₀ : ContDiff ℝ ⊤ (cosineMode n) := by unfold cosineMode; fun_prop
    exact h₀.comp contDiff_snd
  exact (hexp.mul hcoeff).mul hcos

/-- The cutoff heat term: `(t,x) ↦ φ(t) · exp(-t lam) · ahat · cos(nπx)`. -/
def cutoffHeatTerm (u₀ : intervalDomainPoint → ℝ)
    (c : ℝ) (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q => smoothRightCutoff (c / 2) c q.1 *
    ((Real.exp (-q.1 * unitIntervalCosineEigenvalue n) *
      cosineCoeffs (intervalDomainLift u₀) n) * cosineMode n q.2)

/-- Each cutoff heat term is C² (product of C² cutoff and C∞ heat term). -/
theorem cutoffHeatTerm_contDiff_two (u₀ : intervalDomainPoint → ℝ)
    {c : ℝ} (_hc : 0 < c) (n : ℕ) :
    ContDiff ℝ 2 (cutoffHeatTerm u₀ c n) := by
  unfold cutoffHeatTerm
  have hφ : ContDiff ℝ 2 (fun q : ℝ × ℝ => smoothRightCutoff (c / 2) c q.1) :=
    (smoothRightCutoff_contDiff (c' := c / 2) (c := c)).comp contDiff_fst
  exact hφ.mul ((heatTerm_contDiff u₀ n).of_le le_top)

/-- `∑ lam^m · exp(-τ · lam)` is summable for `τ > 0`.  This is
`IntervalCD6Tail.eigenvalue_pow_mul_exp_summable` lifted to the public
namespace. -/
theorem eigenvalue_pow_mul_exp_summable
    (m : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n ^ m *
        Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by
  have hc : 0 < τ * Real.pi ^ 2 := by positivity
  have hbase : Summable (fun n : ℕ =>
      Real.pi ^ (2 * m) * ((n : ℝ) ^ (2 * m) *
        Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ)))) := by
    simpa [mul_assoc] using
      (Real.summable_pow_mul_exp_neg_nat_mul (2 * m) hc).mul_left
        (Real.pi ^ (2 * m))
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hbase
  · have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue; positivity
    exact mul_nonneg (pow_nonneg hlam m) (Real.exp_nonneg _)
  · have hn_sq_ge : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst n; norm_num
      · exact le_self_pow₀ (by exact_mod_cast hn) (by norm_num)
    have hlam_eq :
        unitIntervalCosineEigenvalue n = (n : ℝ) ^ 2 * Real.pi ^ 2 := by
      unfold unitIntervalCosineEigenvalue; ring
    have hexp_le :
        Real.exp (-τ * unitIntervalCosineEigenvalue n) ≤
          Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      rw [hlam_eq]
      nlinarith [mul_nonneg hτ.le (sq_nonneg Real.pi), hn_sq_ge]
    have hpow_eq :
        unitIntervalCosineEigenvalue n ^ m =
          Real.pi ^ (2 * m) * (n : ℝ) ^ (2 * m) := by
      rw [hlam_eq, mul_pow, pow_mul, pow_mul, mul_comm]
    calc unitIntervalCosineEigenvalue n ^ m *
          Real.exp (-τ * unitIntervalCosineEigenvalue n)
        = Real.pi ^ (2 * m) * ((n : ℝ) ^ (2 * m) *
            Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by
          rw [hpow_eq]; ring
      _ ≤ Real.pi ^ (2 * m) * ((n : ℝ) ^ (2 * m) *
            Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hexp_le (by positivity))
            (by positivity)

/-- Coefficient-weighted eigenvalue-power summability: the majorant series
`∑ lam^m · M₀ · exp(-c · lam)` is summable for `c > 0`. -/
theorem eigenvalue_pow_mul_coeff_exp_summable
    (m : ℕ) {M₀ c : ℝ} (hc : 0 < c) (_hM₀ : 0 ≤ M₀) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n ^ m * M₀ *
        Real.exp (-c * unitIntervalCosineEigenvalue n)) :=
  (eigenvalue_pow_mul_exp_summable m hc).mul_right M₀ |>.congr (fun n => by ring)

/-- Existence of a global bound for iterated derivatives of `smoothRightCutoff`.

Because `smoothRightCutoff c' c` is C² (proved by `smoothRightCutoff_contDiff`),
constant `0` on `(-∞, c']`, and constant `1` on `[c, ∞)`, its `k`-th derivative
(`k ≥ 1`) is continuous with support inside the compact interval `[c', c]`,
hence bounded.  For `k = 0` the function is valued in `[0, 1]`. -/
private theorem smoothRightCutoff_iteratedFDeriv_bound_exists
    (c' c : ℝ) (hc'c : c' < c) (k : ℕ) (hk : (k : ℕ∞) ≤ 2) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ t : ℝ, ‖iteratedFDeriv ℝ k (smoothRightCutoff c' c) t‖ ≤ B := by
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · -- k = 0: smoothRightCutoff ∈ [0, 1]
    refine ⟨1, zero_le_one, fun t => ?_⟩
    rw [norm_iteratedFDeriv_zero]
    unfold smoothRightCutoff
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  · -- k ≥ 1: the k-th derivative is continuous and has compact support
    -- (smoothRightCutoff is constant outside [c', c]), hence bounded.
    have hcont : Continuous
        (fun t : ℝ => iteratedFDeriv ℝ k (smoothRightCutoff c' c) t) :=
      smoothRightCutoff_contDiff.continuous_iteratedFDeriv (by exact_mod_cast hk)
    have hk_ne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk_pos
    -- The iterated derivative vanishes outside [c', c]: on (-∞, c') the function
    -- is locally 0, and on (c, ∞) it is locally 1.
    have hzero : ∀ t, t ∉ Set.Icc c' c →
        iteratedFDeriv ℝ k (smoothRightCutoff c' c) t = 0 := by
      intro t ht
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
      rcases ht with ht_lt | ht_gt
      · -- t < c': function is locally 0
        have hev : smoothRightCutoff c' c =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
          filter_upwards [Iio_mem_nhds ht_lt] with s hs
          exact smoothRightCutoff_eq_zero_of_le hc'c (le_of_lt hs)
        have := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev k).eq_of_nhds
        rwa [iteratedFDeriv_const_of_ne hk_ne, Pi.zero_apply] at this
      · -- t > c: function is locally 1
        have hev : smoothRightCutoff c' c =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
          filter_upwards [Ioi_mem_nhds ht_gt] with s hs
          exact smoothRightCutoff_eq_one_of_ge hc'c (le_of_lt hs)
        have := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev k).eq_of_nhds
        rwa [iteratedFDeriv_const_of_ne hk_ne, Pi.zero_apply] at this
    have hcomp : HasCompactSupport
        (fun t : ℝ => iteratedFDeriv ℝ k (smoothRightCutoff c' c) t) :=
      HasCompactSupport.intro' isCompact_Icc isClosed_Icc hzero
    rcases hcont.bounded_above_of_compact_support hcomp with ⟨C, hC⟩
    exact ⟨max C 0, le_max_right C 0, fun t => (hC t).trans (le_max_left C 0)⟩

/-- Noncomputable global bound for the `k`-th iterated derivative of
`smoothRightCutoff c' c`. Guaranteed nonneg and universal in `t`. -/
private noncomputable def smoothRightCutoffDerivBound (c' c : ℝ) (hc'c : c' < c) (k : ℕ)
    (hk : (k : ℕ∞) ≤ 2) : ℝ :=
  Classical.choose (smoothRightCutoff_iteratedFDeriv_bound_exists c' c hc'c k hk)

private theorem smoothRightCutoffDerivBound_nonneg {c' c : ℝ} (hc'c : c' < c) {k : ℕ}
    (hk : (k : ℕ∞) ≤ 2) :
    0 ≤ smoothRightCutoffDerivBound c' c hc'c k hk :=
  (Classical.choose_spec
    (smoothRightCutoff_iteratedFDeriv_bound_exists c' c hc'c k hk)).1

private theorem smoothRightCutoffDerivBound_spec {c' c : ℝ} (hc'c : c' < c) {k : ℕ}
    (hk : (k : ℕ∞) ≤ 2) (t : ℝ) :
    ‖iteratedFDeriv ℝ k (smoothRightCutoff c' c) t‖ ≤
      smoothRightCutoffDerivBound c' c hc'c k hk :=
  (Classical.choose_spec
    (smoothRightCutoff_iteratedFDeriv_bound_exists c' c hc'c k hk)).2 t

/-- The correct majorant for the cutoff heat term.

Uses `(1 + lam)^k` rather than `lam^k` to handle the `n = 0` case (where
`λ_0 = 0` but the cutoff derivatives contribute a nonzero constant).

`v k n = (∑ C(k,i) · Φ_i) · 4 · (1 + lam)^k · M₀ · exp(-(c/2)·lam)` where
`Φ_i` is the global bound on the `i`-th derivative of `smoothRightCutoff(c/2,c)`.
The factor `4` absorbs the `2^j ≤ 4` from the Leibniz sum over the inner product
`exp(-t·lam)·ahat · cos(nπx)`.

The Leibniz constant and majorant are folded into one definition, indexed by `k`
and `hk`. -/
private noncomputable def cutoffHeatMajorant (c M₀ : ℝ) (hc : 0 < c) (k : ℕ)
    (_hk : (k : ℕ∞) ≤ 2) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) *
      if hi : (i : ℕ∞) ≤ 2
      then smoothRightCutoffDerivBound (c / 2) c (by linarith) i hi
      else 0) *
    (4 * ((1 + unitIntervalCosineEigenvalue n) ^ k * M₀ *
      Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n)))

/-- Summability of `(1 + eigenvalue n)^k * M0 * exp(-tau * eigenvalue n)`. -/
private theorem one_add_eigenvalue_pow_mul_exp_summable
    (m : ℕ) {τ M₀ : ℝ} (hτ : 0 < τ) (hM₀ : 0 ≤ M₀) :
    Summable (fun n : ℕ =>
      (1 + unitIntervalCosineEigenvalue n) ^ m * M₀ *
        Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by
  -- Domination: (1 + lam)^m <= 2^m * (1 + lam^m), so the function is bounded
  -- by a sum of two summable series (constant * exp and eigenvalue^m * exp).
  have hS0 : Summable (fun n : ℕ =>
      M₀ * Real.exp (-τ * unitIntervalCosineEigenvalue n)) :=
    (eigenvalue_pow_mul_exp_summable 0 hτ).mul_left M₀ |>.congr (fun n => by ring)
  have hSm : Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n ^ m * M₀ *
        Real.exp (-τ * unitIntervalCosineEigenvalue n)) :=
    eigenvalue_pow_mul_coeff_exp_summable m hτ hM₀
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((hS0.add hSm).mul_left (2 ^ m))
  · exact mul_nonneg (mul_nonneg (pow_nonneg (by
        linarith [show 0 ≤ unitIntervalCosineEigenvalue n from by
          unfold unitIntervalCosineEigenvalue; positivity]) m) hM₀)
      (Real.exp_nonneg _)
  · have hlam_nn : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue; positivity
    have h1lam : (1 + unitIntervalCosineEigenvalue n) ^ m ≤
        2 ^ m * (1 + unitIntervalCosineEigenvalue n ^ m) := by
      calc (1 + unitIntervalCosineEigenvalue n) ^ m
          ≤ (2 * max 1 (unitIntervalCosineEigenvalue n)) ^ m := by
            gcongr
            rcases le_or_gt (unitIntervalCosineEigenvalue n) 1 with h | h
            · linarith [le_max_left 1 (unitIntervalCosineEigenvalue n)]
            · linarith [le_max_right 1 (unitIntervalCosineEigenvalue n)]
        _ = 2 ^ m * (max 1 (unitIntervalCosineEigenvalue n)) ^ m := by
            rw [mul_pow]
        _ ≤ 2 ^ m * (1 + unitIntervalCosineEigenvalue n ^ m) := by
            gcongr
            rcases le_or_gt (unitIntervalCosineEigenvalue n) 1 with h | h
            · rw [max_eq_left h, one_pow]; linarith [pow_nonneg hlam_nn m]
            · rw [max_eq_right h.le]; linarith
    calc (1 + unitIntervalCosineEigenvalue n) ^ m * M₀ *
          Real.exp (-τ * unitIntervalCosineEigenvalue n)
        ≤ 2 ^ m * (1 + unitIntervalCosineEigenvalue n ^ m) * M₀ *
            Real.exp (-τ * unitIntervalCosineEigenvalue n) := by gcongr
      _ = 2 ^ m * (M₀ * Real.exp (-τ * unitIntervalCosineEigenvalue n) +
            unitIntervalCosineEigenvalue n ^ m * M₀ *
              Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by ring

/-- The cutoff heat majorant is summable for each `k ≤ 2`. -/
private theorem cutoffHeatMajorant_summable
    {c M₀ : ℝ} (hc : 0 < c) (hM₀ : 0 ≤ M₀) {k : ℕ}
    (hk : (k : ℕ∞) ≤ 2) :
    Summable (cutoffHeatMajorant c M₀ hc k hk) := by
  show Summable (fun n =>
    (∑ i ∈ Finset.range (k + 1), _) *
      (4 * ((1 + unitIntervalCosineEigenvalue n) ^ k * M₀ *
        Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n))))
  exact ((one_add_eigenvalue_pow_mul_exp_summable k (half_pos hc) hM₀).mul_left 4).mul_left _

set_option maxHeartbeats 800000 in
/-- Bound on `‖D^j (heatTerm u₀ n) q‖` for `q.1 ≥ c/2`.  The bound is
`4 · (1 + λ_n)^j · M₀ · exp(-(c/2) · λ_n)`, proved via the Leibniz product
rule for `exp(-t·λ_n)·â_n · cos(nπx)`, projection bounds, and
`iteratedDeriv_exp_const_mul` + `unitIntervalCosineMode_iteratedFDeriv_bound`.
The factor `4` absorbs `2^j ≤ 4` for `j ≤ 2`. -/
private theorem heatTerm_iteratedFDeriv_global_bound
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {c : ℝ} (_hc : 0 < c) (j n : ℕ) (q : ℝ × ℝ)
    (hj : (j : ℕ∞) ≤ 2)
    (hq : c / 2 ≤ q.1) :
    ‖iteratedFDeriv ℝ j (heatTerm u₀ n) q‖ ≤
      4 * ((1 + unitIntervalCosineEigenvalue n) ^ j * M₀ *
        Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n)) := by
  set lam := unitIntervalCosineEigenvalue n with hlam_def
  set ahat := cosineCoeffs (intervalDomainLift u₀) n with hahat_def
  have hlam_nn : 0 ≤ lam := by rw [hlam_def]; unfold unitIntervalCosineEigenvalue; positivity
  have hM₀nn : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
  have hjNat : j ≤ 2 := by exact_mod_cast hj
  -- Decompose heatTerm = G * H where G depends on q.1, H depends on q.2
  let G : ℝ × ℝ → ℝ := fun q => Real.exp (-q.1 * lam) * ahat
  let H : ℝ × ℝ → ℝ := fun q => cosineMode n q.2
  have hterm : heatTerm u₀ n = fun q => G q * H q := rfl
  -- Both factors are C∞ (hence C²)
  have hA : ContDiff ℝ ⊤ (fun t : ℝ => Real.exp (-t * lam) * ahat) := by fun_prop
  have hG : ContDiff ℝ (2 : ℕ∞) G := (hA.comp contDiff_fst).of_le le_top
  have hB₀ : ContDiff ℝ ⊤ (cosineMode n) := by unfold cosineMode; fun_prop
  have hH : ContDiff ℝ (2 : ℕ∞) H := (hB₀.comp contDiff_snd).of_le le_top
  have hjTop : (j : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hj
  rw [hterm]
  -- Apply Leibniz rule for the product G · H
  have hleib : ‖iteratedFDeriv ℝ j (fun q => G q * H q) q‖ ≤
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i G q‖ * ‖iteratedFDeriv ℝ (j - i) H q‖ := by
    simpa [mul_assoc] using norm_iteratedFDeriv_mul_le hG hH q hjTop
  refine hleib.trans ?_
  -- Bound each Leibniz term
  -- 1D bounds for G factor: ‖D^i(A∘fst) q‖ ≤ ‖D^i A q.1‖ ≤ lam^i · M₀ · exp(-(c/2)·lam)
  have hG_1d : ∀ i, i ≤ j →
      ‖iteratedFDeriv ℝ i G q‖ ≤ lam ^ i * M₀ *
        Real.exp (-(c / 2) * lam) := by
    intro i hi
    refine (norm_iteratedFDeriv_comp_fst_le hA le_top q).trans ?_
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    -- Compute iteratedDeriv i A t for A t = exp((-lam)·t) · ahat
    have hrewrite : (fun t : ℝ => Real.exp (-t * lam) * ahat) =
        (fun t => Real.exp ((-lam) * t) * ahat) := by
      funext t; ring_nf
    rw [hrewrite, show (fun t => Real.exp ((-lam) * t) * ahat) =
        ((fun t => Real.exp ((-lam) * t)) · * ahat) from rfl]
    rw [iteratedDeriv_mul_const_field, iteratedDeriv_exp_const_mul]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
    -- |(-lam)^i| = lam^i since |(-lam)| = lam
    rw [show |(-lam)| = lam from by rw [abs_neg, abs_of_nonneg hlam_nn]]
    -- |exp((-lam)·q.1)| = exp(-q.1·lam) since exp > 0
    rw [show (-lam) * q.1 = -(q.1 * lam) from by ring,
        abs_of_pos (Real.exp_pos _)]
    -- |ahat| ≤ M₀
    have hahat_bound : |ahat| ≤ M₀ := hu₀_bound n
    -- exp(-q.1·lam) ≤ exp(-(c/2)·lam) since q.1 ≥ c/2 and exp is decreasing
    have hexp_le : Real.exp (-(q.1 * lam)) ≤ Real.exp (-(c / 2 * lam)) := by
      apply Real.exp_le_exp.mpr
      linarith [mul_le_mul_of_nonneg_right hq hlam_nn]
    calc lam ^ i * Real.exp (-(q.1 * lam)) * |ahat|
        ≤ lam ^ i * Real.exp (-(c / 2 * lam)) * M₀ := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hexp_le (pow_nonneg hlam_nn i)
          · exact hahat_bound
          · exact abs_nonneg _
          · exact mul_nonneg (pow_nonneg hlam_nn i) (Real.exp_nonneg _)
      _ = lam ^ i * M₀ * Real.exp (-(c / 2) * lam) := by ring
  -- 1D bounds for H factor: ‖D^l(B∘snd) q‖ ≤ ‖D^l B q.2‖ ≤ |nπ|^l
  have hH_1d : ∀ l, l ≤ j →
      ‖iteratedFDeriv ℝ l H q‖ ≤ |(n : ℝ) * Real.pi| ^ l := by
    intro l hl
    refine (norm_iteratedFDeriv_comp_snd_le hB₀ le_top q).trans ?_
    change ‖iteratedFDeriv ℝ l (cosineMode n) q.2‖ ≤ _
    have : cosineMode n = unitIntervalCosineMode n := by
      funext x; simp [cosineMode, unitIntervalCosineMode]
    rw [this]
    exact ShenWork.Paper2.CD6CosineModeBounds.unitIntervalCosineMode_iteratedFDeriv_bound l n q.2
  -- Bound each Leibniz term and sum
  -- Each term: C(j,i) · lam^i · M₀ · exp(…) · |nπ|^{j-i}
  --   ≤ C(j,i) · (1+lam)^i · (1+lam)^{j-i} · M₀ · exp(…)
  --   = C(j,i) · (1+lam)^j · M₀ · exp(…)
  -- Sum: 2^j · (1+lam)^j · M₀ · exp(…) ≤ 4 · (1+lam)^j · M₀ · exp(…)
  have h1lam : 1 ≤ 1 + lam := le_add_of_nonneg_right hlam_nn
  -- Key: lam ≤ 1 + lam and |nπ| ≤ 1 + lam
  have hfreq_le : |(n : ℝ) * Real.pi| ≤ 1 + lam := by
    rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) Real.pi_pos.le), hlam_def]
    unfold unitIntervalCosineEigenvalue
    nlinarith [sq_nonneg ((n : ℝ) * Real.pi - 1/2)]
  calc ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i G q‖ * ‖iteratedFDeriv ℝ (j - i) H q‖
      ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          (lam ^ i * M₀ * Real.exp (-(c / 2) * lam)) *
          (|(n : ℝ) * Real.pi| ^ (j - i)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hik : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (hG_1d i hik) (Nat.cast_nonneg _)
        · exact hH_1d (j - i) (Nat.sub_le j i)
        · exact norm_nonneg _
        · exact mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (mul_nonneg (pow_nonneg hlam_nn i) hM₀nn) (Real.exp_nonneg _))
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ((1 + lam) ^ j * M₀ * Real.exp (-(c / 2) * lam)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hik : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have h1 : lam ^ i ≤ (1 + lam) ^ i :=
          pow_le_pow_left₀ hlam_nn (le_add_of_nonneg_left zero_le_one) i
        have h2 : |(n : ℝ) * Real.pi| ^ (j - i) ≤ (1 + lam) ^ (j - i) :=
          pow_le_pow_left₀ (by positivity)
            hfreq_le (j - i)
        have hprod : lam ^ i * (|(n : ℝ) * Real.pi| ^ (j - i)) ≤
            (1 + lam) ^ j := by
          calc lam ^ i * |(n : ℝ) * Real.pi| ^ (j - i)
              ≤ (1 + lam) ^ i * (1 + lam) ^ (j - i) :=
                mul_le_mul h1 h2 (by positivity) (pow_nonneg (by linarith) i)
            _ = (1 + lam) ^ (i + (j - i)) := by rw [pow_add]
            _ = (1 + lam) ^ j := by rw [Nat.add_sub_cancel' hik]
        calc (j.choose i : ℝ) *
              (lam ^ i * M₀ * Real.exp (-(c / 2) * lam)) *
              |(n : ℝ) * Real.pi| ^ (j - i)
            = (j.choose i : ℝ) *
                (lam ^ i * |(n : ℝ) * Real.pi| ^ (j - i)) *
                (M₀ * Real.exp (-(c / 2) * lam)) := by ring
          _ ≤ (j.choose i : ℝ) * (1 + lam) ^ j *
                (M₀ * Real.exp (-(c / 2) * lam)) := by
              gcongr
          _ = (j.choose i : ℝ) *
                ((1 + lam) ^ j * M₀ * Real.exp (-(c / 2) * lam)) := by ring
    _ = (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) *
          ((1 + lam) ^ j * M₀ * Real.exp (-(c / 2) * lam)) := by
        rw [Finset.sum_mul]
    _ ≤ 4 * ((1 + lam) ^ j * M₀ * Real.exp (-(c / 2) * lam)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (mul_nonneg
          (pow_nonneg (by linarith) j) hM₀nn) (Real.exp_nonneg _))
        -- ∑ C(j,i) = 2^j ≤ 4 for j ≤ 2
        have hsum : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) =
            (2 ^ j : ℕ) := by
          push_cast
          exact_mod_cast Nat.sum_range_choose j
        rw [hsum]
        have : (2 : ℝ) ^ j ≤ 4 := by
          interval_cases j <;> norm_num
        exact_mod_cast this

/-- Uniform iterated-derivative bound for the cutoff heat term.

For `φ = smoothRightCutoff (c/2) c`, the cutoff heat term
`φ(t) · exp(-t lam) · ahat · cos(nπx)` satisfies the global bound:
  `‖iteratedFDeriv ℝ k (cutoffHeatTerm u₀ c n) q‖ ≤ v k n`
for all `q : ℝ × ℝ`, where the majorant `v k n` is summable in `n`.

The bound holds because:
  - For `t ≤ c/2`: `φ(t) = 0`, so the function and all derivatives vanish.
  - For `t ≥ c/2`: `exp(-t lam) ≤ exp(-(c/2) lam)`, and by the Leibniz
    rule (`norm_iteratedFDeriv_mul_le`), each order-`k` derivative picks up
    at most `lam^k` from differentiating exp/cos (each derivative of
    `exp(-t lam)` contributes `lam`, of `cos(nπx)` contributes `nπ ≤ √lam`),
    and bounded factors from the cutoff φ.

The majorant uses `(1 + lam)^k` (not `lam^k`) because for `n = 0` (where
`λ_0 = 0`) the cutoff derivative contributes a nonzero constant. -/
theorem cutoffHeatTerm_iteratedFDeriv_bound
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {c : ℝ} (hc : 0 < c) (k n : ℕ) (q : ℝ × ℝ)
    (hk : (k : ℕ∞) ≤ 2) :
    ‖iteratedFDeriv ℝ k (cutoffHeatTerm u₀ c n) q‖ ≤
      cutoffHeatMajorant c M₀ hc k hk n := by
  have hc'c : c / 2 < c := by linarith
  -- Case split: when q.1 < c/2, the cutoff kills the term (locally 0).
  by_cases hq : c / 2 ≤ q.1
  · -- Case q.1 ≥ c/2: Leibniz decomposition with heat term bound
    -- Decompose cutoffHeatTerm as G * H where
    -- G = fun q => smoothRightCutoff (c/2) c q.1  (C², depends only on q.1)
    -- H = heatTerm u₀ n                           (C∞, proved by heatTerm_contDiff)
    let G : ℝ × ℝ → ℝ := fun q => smoothRightCutoff (c / 2) c q.1
    let H : ℝ × ℝ → ℝ := heatTerm u₀ n
    have hkNat : k ≤ 2 := by exact_mod_cast hk
    have hterm : cutoffHeatTerm u₀ c n = fun q => G q * H q := by
      funext q; simp [cutoffHeatTerm, heatTerm, G, H]
    have hG : ContDiff ℝ (2 : ℕ∞) G :=
      (smoothRightCutoff_contDiff (c' := c / 2) (c := c)).comp contDiff_fst
    have hH : ContDiff ℝ (2 : ℕ∞) H :=
      (heatTerm_contDiff u₀ n).of_le le_top
    have hk' : (k : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hk
    rw [hterm]
    -- Apply Leibniz, then bound each term in the sum
    calc ‖iteratedFDeriv ℝ k (fun q => G q * H q) q‖
        ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i G q‖ * ‖iteratedFDeriv ℝ (k - i) H q‖ := by
          simpa [mul_assoc] using norm_iteratedFDeriv_mul_le hG hH q hk'
      _ ≤ cutoffHeatMajorant c M₀ hc k hk n := by
          show _ ≤ (∑ i ∈ Finset.range (k + 1), _) *
            (4 * ((1 + unitIntervalCosineEigenvalue n) ^ k * M₀ *
              Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n)))
          rw [Finset.sum_mul]
          apply Finset.sum_le_sum
          intro i hi
          have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hiTop : (i : ℕ∞) ≤ (2 : ℕ∞) := le_trans (Nat.cast_le.mpr hik) hk
          have hkiTop : ((k - i : ℕ) : ℕ∞) ≤ (2 : ℕ∞) :=
            le_trans (Nat.cast_le.mpr (Nat.sub_le k i)) (Nat.cast_le.mpr hkNat)
          -- Bound ‖D^i G q‖ via fst-projection + cutoff derivative bound
          have hG_bound : ‖iteratedFDeriv ℝ i G q‖ ≤
              smoothRightCutoffDerivBound (c / 2) c hc'c i hiTop := by
            exact (norm_iteratedFDeriv_comp_fst_le smoothRightCutoff_contDiff
              (by exact_mod_cast hiTop) q).trans
              (smoothRightCutoffDerivBound_spec hc'c hiTop q.1)
          -- Bound ‖D^{k-i} H q‖ via heatTerm bound (uses hq: q.1 ≥ c/2)
          have hH_bound : ‖iteratedFDeriv ℝ (k - i) H q‖ ≤
              4 * ((1 + unitIntervalCosineEigenvalue n) ^ (k - i) * M₀ *
                Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n)) :=
            heatTerm_iteratedFDeriv_global_bound hu₀_bound hc (k - i) n q hkiTop hq
          -- Combine: C(k,i) · Φ_i · 4·(1+λ)^{k-i} ≤ C(k,i) · Φ_i · 4·(1+λ)^k
          have hΦ_nn := smoothRightCutoffDerivBound_nonneg (c' := c / 2) (c := c)
            hc'c hiTop
          have hlam_nn : 0 ≤ unitIntervalCosineEigenvalue n := by
            unfold unitIntervalCosineEigenvalue; positivity
          have hM₀nn : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
          have hbase : (1 + unitIntervalCosineEigenvalue n) ^ (k - i) ≤
              (1 + unitIntervalCosineEigenvalue n) ^ k :=
            pow_le_pow_right₀ (by linarith) (Nat.sub_le k i)
          calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i G q‖ *
                ‖iteratedFDeriv ℝ (k - i) H q‖
              ≤ (k.choose i : ℝ) *
                  smoothRightCutoffDerivBound (c / 2) c hc'c i hiTop *
                  (4 * ((1 + unitIntervalCosineEigenvalue n) ^ (k - i) * M₀ *
                    Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n))) := by
                apply mul_le_mul
                · exact mul_le_mul_of_nonneg_left hG_bound (Nat.cast_nonneg _)
                · exact hH_bound
                · exact norm_nonneg _
                · exact mul_nonneg (Nat.cast_nonneg _) hΦ_nn
            _ ≤ (k.choose i : ℝ) *
                  smoothRightCutoffDerivBound (c / 2) c hc'c i hiTop *
                  (4 * ((1 + unitIntervalCosineEigenvalue n) ^ k * M₀ *
                    Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n))) := by
                apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg _) hΦ_nn)
                apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 4)
                apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
                exact mul_le_mul_of_nonneg_right hbase hM₀nn
            _ = (k.choose i : ℝ) *
                  (if hi : (i : ℕ∞) ≤ 2
                   then smoothRightCutoffDerivBound (c / 2) c hc'c i hi
                   else 0) *
                  (4 * ((1 + unitIntervalCosineEigenvalue n) ^ k * M₀ *
                    Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n))) := by
                rw [dif_pos hiTop]
  · -- Case q.1 < c/2: the cutoff φ(q.1) = 0, so cutoffHeatTerm is locally 0.
    simp only [not_le] at hq
    -- The cutoff term is 0 in a neighborhood of q (φ = 0 on Iic (c/2))
    have hev : cutoffHeatTerm u₀ c n =ᶠ[𝓝 q] fun _ => (0 : ℝ) := by
      filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds
        (Iio_mem_nhds hq)] with q' hq'
      simp only [Set.mem_preimage, Set.mem_Iio] at hq'
      simp [cutoffHeatTerm, smoothRightCutoff_eq_zero_of_le hc'c (le_of_lt hq')]
    -- So ‖D^k(cutoffHeatTerm) q‖ = 0
    have hlam_nn : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue; positivity
    have hM₀nn : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
    have hnorm_zero : ‖iteratedFDeriv ℝ k (cutoffHeatTerm u₀ c n) q‖ = 0 := by
      rcases Nat.eq_zero_or_pos k with rfl | hk_pos
      · rw [norm_iteratedFDeriv_zero, hev.eq_of_nhds, norm_zero]
      · have hev' := Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev k
        have := hev'.eq_of_nhds
        rw [iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.mp hk_pos), Pi.zero_apply]
          at this
        rw [this, norm_zero]
    rw [hnorm_zero]
    -- The majorant is nonneg
    unfold cutoffHeatMajorant
    apply mul_nonneg
    · apply Finset.sum_nonneg; intro i _
      apply mul_nonneg (Nat.cast_nonneg _)
      split_ifs with hi
      · exact smoothRightCutoffDerivBound_nonneg hc'c hi
      · exact le_refl 0
    · exact mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (mul_nonneg (mul_nonneg
        (pow_nonneg (by linarith) k) hM₀nn) (Real.exp_nonneg _))

set_option maxHeartbeats 1600000 in
/-- **Global C² of the cutoff heat semigroup series.**

The series `(t,x) ↦ ∑' n, φ(t) · exp(-t lam) ahat cos(nπx)` is `ContDiff ℝ 2`
as a function `ℝ² → ℝ`, where `φ = smoothRightCutoff (c/2) c`.  The proof uses
`contDiff_tsum` with the majorant from `cutoffHeatTerm_iteratedFDeriv_bound`. -/
theorem cutoffHeatSeries_contDiff_two
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {c : ℝ} (hc : 0 < c) :
    ContDiff ℝ 2 (fun q : ℝ × ℝ =>
      ∑' n : ℕ, cutoffHeatTerm u₀ c n q) := by
  have hM₀nn : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
  have hc'c : c / 2 < c := by linarith
  -- Use a majorant that doesn't depend on a proof argument for summability
  let v : ℕ → ℕ → ℝ := fun k n =>
    (∑ i ∈ Finset.range 3,
      (k.choose i : ℝ) *
        if hi : (i : ℕ∞) ≤ 2
        then smoothRightCutoffDerivBound (c / 2) c hc'c i hi
        else 0) *
      (4 * ((1 + unitIntervalCosineEigenvalue n) ^ k * M₀ *
        Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n)))
  apply contDiff_tsum (𝕜 := ℝ) (f := cutoffHeatTerm u₀ c) (v := v)
  -- (1) Each cutoff term is C²
  · intro n
    exact cutoffHeatTerm_contDiff_two u₀ hc n
  -- (2) Majorant summability for each k ≤ 2
  · intro k hk
    show Summable (v k)
    show Summable (fun n => _ * (4 * ((1 + unitIntervalCosineEigenvalue n) ^ k * M₀ *
      Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n))))
    exact ((one_add_eigenvalue_pow_mul_exp_summable k (half_pos hc) hM₀nn).mul_left 4).mul_left _
  -- (3) Uniform iterated-derivative bound
  · intro k n q hk
    -- The majorant v k n ≥ cutoffHeatMajorant c M₀ hc k hk n because for k ≤ 2,
    -- range 3 ⊇ range (k+1), and the extra terms are ≥ 0 (k.choose i = 0 for i > k).
    -- So the bound from cutoffHeatTerm_iteratedFDeriv_bound applies.
    have hkNat : k ≤ 2 := by exact_mod_cast hk
    refine (cutoffHeatTerm_iteratedFDeriv_bound hu₀_bound hc k n q hk).trans ?_
    -- cutoffHeatMajorant and v k n differ only in the sum range:
    -- cutoffHeatMajorant sums over range(k+1), v sums over range 3.
    -- Since k ≤ 2, range(k+1) ⊆ range 3, and extra terms are nonneg.
    show cutoffHeatMajorant c M₀ hc k hk n ≤ v k n
    unfold cutoffHeatMajorant
    apply mul_le_mul_of_nonneg_right
    · apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intro i _ _
      apply mul_nonneg (Nat.cast_nonneg _)
      split_ifs with hi
      · exact smoothRightCutoffDerivBound_nonneg hc'c hi
      · exact le_refl 0
    · have hlam_nn : 0 ≤ unitIntervalCosineEigenvalue n := by
        unfold unitIntervalCosineEigenvalue; positivity
      exact mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (mul_nonneg (mul_nonneg
        (pow_nonneg (by linarith) k) hM₀nn) (Real.exp_nonneg _))

/-- Near `(s₀, x₀)` with `s₀ > c`, the original heat semigroup series equals
the cutoff series (because `φ(t) = 1` in a neighborhood of `s₀`). -/
theorem heatSeries_eventuallyEq_cutoff
    {u₀ : intervalDomainPoint → ℝ}
    {c s₀ x₀ : ℝ} (hc : 0 < c) (hs₀ : c < s₀) :
    (fun q : ℝ × ℝ =>
      ∑' n : ℕ, heatTerm u₀ n q) =ᶠ[𝓝 (s₀, x₀)]
    (fun q : ℝ × ℝ =>
      ∑' n : ℕ, cutoffHeatTerm u₀ c n q) := by
  -- φ = 1 in a neighborhood of s₀ (since s₀ > c)
  have hφ_one : smoothRightCutoff (c / 2) c =ᶠ[𝓝 s₀] fun _ => (1 : ℝ) :=
    smoothRightCutoff_eventually_eq_one (by linarith) hs₀
  -- Lift to ℝ × ℝ via fst
  have hφ_prod :
      (fun q : ℝ × ℝ => smoothRightCutoff (c / 2) c q.1) =ᶠ[𝓝 (s₀, x₀)]
        fun _ : ℝ × ℝ => (1 : ℝ) :=
    hφ_one.comp_tendsto continuous_fst.continuousAt
  -- Where φ = 1, cutoff term = original term
  filter_upwards [hφ_prod] with q hq
  congr 1; ext n
  simp [cutoffHeatTerm, heatTerm, hq]

/-- **Joint `ContDiffAt ℝ 2`** of the heat semigroup series at any point with
`s₀ > c > 0`.  This is the form actually needed downstream.

Proof: `cutoffHeatSeries_contDiff_two` gives global `ContDiff ℝ 2` of the
cutoff series.  Near `(s₀, x₀)` with `s₀ > c`, the cutoff series agrees with
the original series (`cutoffHeatSeries_eventuallyEq`), so `ContDiffAt` of the
original series follows by `ContDiffAt.congr_of_eventuallyEq`. -/
theorem heatSemigroup_jointContDiffAt_two
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {c : ℝ} (hc : 0 < c) {s₀ x₀ : ℝ} (hs₀ : c < s₀) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ =>
      ∑' k : ℕ, (Real.exp (-q.1 * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k q.2) (s₀, x₀) := by
  -- The original series = heatTerm series pointwise
  have hfEq : (fun q : ℝ × ℝ =>
      ∑' k : ℕ, (Real.exp (-q.1 * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k q.2) =
      fun q => ∑' n, heatTerm u₀ n q := by
    funext q; congr 1
  rw [hfEq]
  -- The cutoff series is globally C² ...
  have hCutoff := (cutoffHeatSeries_contDiff_two hu₀_bound hc).contDiffAt
    (x := (s₀, x₀))
  -- ... and agrees with the original series near (s₀, x₀)
  exact hCutoff.congr_of_eventuallyEq
    (heatSeries_eventuallyEq_cutoff hc hs₀)

#print axioms heatSemigroup_jointContDiffAt_two

end

end ShenWork.Paper2.HeatSemigroupJointRegularity

/-! ## §3: Joint `(t,x)` C² regularity of the *resolver* coupled concentration
at the heat semigroup base iterate (level 0)

The coupled chemical concentration `v(s,x) = coupledChemicalConcentration p u s x`
(where `u = conjugatePicardIter p u₀ 0 = S(t)u₀`, the heat semigroup) is
`ContDiffAt ℝ 2` at `(s₀, x₀)` for `s₀ > c > 0` and `x₀ ∈ (0,1)`.

**Route.**  The resolver concentration has cosine series
`v(s,x) = ∑' k, resolverTimeCoeff p u k s · cos(kπx)` where
`resolverTimeCoeff p u k s = wₖ · srcTimeCoeff p u k s` with the constant
elliptic weight `wₖ = 1/(μ+λ_k)`.  The existing infrastructure chain

  `PhysicalResolverJointC2Data  →  coupledChemical_jointContDiffAt_two`

delivers `ContDiffAt ℝ 2` of the uncurried lifted concentration from the
bounded-weight time-coefficient data.  For the heat semigroup base iterate the
source `ν·S(t)u₀^γ` is smooth in time (exponential coefficient decay) and `C²`
in space (heat smoothing + rpow chain rule under the positivity floor), giving
the source cosine coefficients `(kπ)⁻²` decay at each of the three time orders
`0,1,2`.

The sorry'd sub-pieces are:
* `heatSemigroup_level0_resolverJointC2Data` — building the
  `PhysicalResolverJointC2Data` for the heat semigroup base iterate, which
  requires the floor positivity, the time-Leibniz chain on the source slices,
  and the `(kπ)⁻²` spatial decay envelopes.  This is the upstream infrastructure
  that connects the heat semigroup smoothing to the floored source time-`C²`
  data (`FlooredSourceTimeData`).
-/

namespace ShenWork.Paper2.HeatResolverJointRegularity

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemicalConcentration)
open ShenWork.IntervalResolverJointC2PhysicalConcrete
  (PhysicalResolverJointC2Data coupledChemical_jointContDiffAt_two
   resolverTimeCoeff)
open ShenWork.PDE (intervalNeumannResolverWeight intervalNeumannResolverCoeff
  intervalNeumannResolverSourceCoeff)
open ShenWork.Paper3 (unitIntervalNeumannSpectrum)

noncomputable section

/-- **Physical resolver joint-C² data for the heat semigroup base iterate.**

For `u = conjugatePicardIter p u₀ 0 = S(t)u₀` (the heat semigroup applied to
bounded continuous initial data `u₀`), the resolver time-coefficients
`resolverTimeCoeff p u k t = wₖ · cosineCoeffs(ν·(S(t)u₀)^γ, k)` are `C²` in
time with summable bounded-weight joint majorants.

**Proof route (committed chain):**
1. `heatSemigroup_flooredSourceTimeData` builds the `FlooredSourceTimeData`
   (6 sorry'd fields, all finite and non-circular).
2. `physicalSourceTimeC2_of_floored` converts to `PhysicalSourceTimeC2`
   (needs summability hypotheses, sorry'd here).
3. `physicalResolverJointC2Data_of_floor` converts to `PhysicalResolverJointC2Data`. -/
theorem heatSemigroup_level0_resolverJointC2Data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x) :
    ∃ Bt : ℕ → ℕ → ℝ,
      PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0) Bt := by
  -- Step 1: Build the FlooredSourceTimeData via the heat semigroup constructor.
  set u := conjugatePicardIter p u₀ 0
  have hFSTD := ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_flooredSourceTimeData
    hu₀_bound hu₀_cont (p := p)
    (hfloor := by
      intro t ht x hx
      exact ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
        hu₀_cont hu₀_pos ht hx)
    (hsliceC2 := by intro i hi t ht; sorry)
    (hsliceNeumann := by intro i hi t ht; sorry)
    (hzerothBound := by intro i hi; sorry)
    (hlaplBound := by intro i hi; sorry)
  -- Step 2: Convert to PhysicalSourceTimeC2 via the floored producer.
  -- The summability hypotheses (value and gradient majorants) need to be established;
  -- they follow from the (kπ)⁻² IBP decay in the builtEs envelope combined with
  -- the elliptic weight wₖ = 1/(μ+λ_k).
  set Es := ShenWork.IntervalPhysicalSourceTimeC2Concrete.builtEs hFSTD
  have hSTC2 : ShenWork.IntervalPhysicalResolverDataConcrete.PhysicalSourceTimeC2 p u Es :=
    ShenWork.IntervalPhysicalSourceTimeC2Concrete.physicalSourceTimeC2_of_floored hFSTD
      (by -- value_summable: ∀ m ≤ 2, Summable (boundedWeightJointMajorant (wₖ·Es) m)
          -- Each summand has wₖ · (kπ)⁻² · envelope, and the weight
          -- wₖ = 1/(μ+λ_k) ≤ 1/μ combined with (kπ)⁻² decay gives summability.
          intro m hm; sorry)
      (by -- grad_summable: ∀ m ≤ 2, Summable (boundedWeightJointGradMajorant (wₖ·Es) m)
          -- Same with an extra eigenvalue factor absorbed by (kπ)⁻² decay.
          intro m hm; sorry)
  -- Step 3: Convert to PhysicalResolverJointC2Data via the floor producer.
  exact ⟨_, ShenWork.IntervalPhysicalResolverDataConcrete.physicalResolverJointC2Data_of_floor hSTC2⟩

/-- **Joint `ContDiffAt ℝ 2`** of the resolver coupled concentration at the heat
semigroup base iterate `conjugatePicardIter p u₀ 0`, at any interior space
point `x₀ ∈ (0,1)` and positive time `s₀ > c > 0`.

This single theorem unlocks the 3 remaining Level0 sorry in the FAC chain:
- SUB-SORRY 3C (resolver joint C²)
- SUB-SORRY 3D (resolver gradient joint C²)
- SUB-SORRY 3E (resolver positivity floor) — via the `PhysicalResolverJointC2Data`.

**Proof route:**  Existentially extract `PhysicalResolverJointC2Data` from
`heatSemigroup_level0_resolverJointC2Data`, then apply the committed
bounded-weight assembler `coupledChemical_jointContDiffAt_two`. -/
theorem heatResolverJointContDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    {c : ℝ} (_hc : 0 < c) {s₀ x₀ : ℝ} (_hs₀ : c < s₀)
    (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ =>
      intervalDomainLift (coupledChemicalConcentration p
        (conjugatePicardIter p u₀ 0) q.1) q.2) (s₀, x₀) := by
  -- `_hc` and `_hs₀` are retained in the API for downstream callers that pass
  -- a time-positivity witness; the bounded-weight route via
  -- `PhysicalResolverJointC2Data` is globally valid (no time cutoff needed).
  obtain ⟨Bt, hBt⟩ := heatSemigroup_level0_resolverJointC2Data
    (p := p) hu₀_bound hu₀_cont hu₀_pos
  exact coupledChemical_jointContDiffAt_two hBt hx₀

#print axioms heatResolverJointContDiffAt_two

end

end ShenWork.Paper2.HeatResolverJointRegularity
