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

  1 sorry: the uniform iterated-derivative bound for the cutoff heat term
  (Leibniz product rule computation).
-/
import ShenWork.Paper2.IntervalParabolicDuhamelGainNonCircular
import ShenWork.Paper2.ChemMildC1etaComm
import ShenWork.PDE.IntervalResolverSpectralJointC2Cutoff
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
  `(t,x) ↦ φ(t) · exp(-t λ_n) · â_n · cos(nπx)`
is C∞ and its iterated derivatives are globally bounded:
  - for `t ≤ c/2`:  φ(t) = 0 so the term and all its derivatives vanish;
  - for `t ≥ c/2`:  `exp(-t λ_n) ≤ exp(-(c/2) λ_n)` and φ derivatives are
    bounded (φ is compactly-supported on `[c/2, c]` with respect to derivatives).
The global bound has the shape `C_k · λ_n^k · M₀ · exp(-(c/2) λ_n)`, which is
summable via `eigenvalue_pow_mul_exp_summable`.  Applying `contDiff_tsum` gives
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

noncomputable section

/-- The `n`-th term of the heat semigroup series, as a function of `(t, x)`:
`(t, x) ↦ exp(-t λ_n) · â_n · cos(nπx)`. -/
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

/-- The cutoff heat term: `(t,x) ↦ φ(t) · exp(-t λ_n) · â_n · cos(nπx)`. -/
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

/-- `∑ λ_n^m · exp(-τ · λ_n)` is summable for `τ > 0`.  This is
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
`∑ λ_n^m · M₀ · exp(-c · λ_n)` is summable for `c > 0`. -/
theorem eigenvalue_pow_mul_coeff_exp_summable
    (m : ℕ) {M₀ c : ℝ} (hc : 0 < c) (_hM₀ : 0 ≤ M₀) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n ^ m * M₀ *
        Real.exp (-c * unitIntervalCosineEigenvalue n)) :=
  (eigenvalue_pow_mul_exp_summable m hc).mul_right M₀ |>.congr (fun n => by ring)

/-- Uniform iterated-derivative bound for the cutoff heat term.

For `φ = smoothRightCutoff (c/2) c`, the cutoff heat term
`φ(t) · exp(-t λ_n) · â_n · cos(nπx)` satisfies the global bound:
  `‖iteratedFDeriv ℝ k (cutoffHeatTerm u₀ c n) q‖ ≤ v k n`
for all `q : ℝ × ℝ`, where the majorant `v k n` is summable in `n`.

The bound holds because:
  - For `t ≤ c/2`: `φ(t) = 0`, so the function and all derivatives vanish.
  - For `t ≥ c/2`: `exp(-t λ_n) ≤ exp(-(c/2) λ_n)`, and by the Leibniz
    rule (`norm_iteratedFDeriv_mul_le`), each order-`k` derivative picks up
    at most `λ_n^k` from differentiating exp (each derivative of
    `exp(-t λ_n)` contributes a factor `λ_n`), at most `(nπ)^k ≤ λ_n^{k/2}`
    from differentiating cos, and bounded factors from the cutoff φ.
    The combined bound is `C_k · λ_n^k · M₀ · exp(-(c/2) λ_n)`.

This is the Leibniz product-rule computation; the structure mirrors
`cutoffValueTerm_leibniz_bound` from the resolver lane. -/
theorem cutoffHeatTerm_iteratedFDeriv_bound
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {c : ℝ} (hc : 0 < c) (k n : ℕ) (q : ℝ × ℝ)
    (hk : (k : ℕ∞) ≤ 2) :
    ‖iteratedFDeriv ℝ k (cutoffHeatTerm u₀ c n) q‖ ≤
      (2 * k + 1) ^ k *
        (unitIntervalCosineEigenvalue n ^ k * M₀ *
          Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n)) := by
  -- Decompose cutoffHeatTerm as G * H where
  -- G = fun q => smoothRightCutoff (c/2) c q.1  (C∞, depends only on q.1)
  -- H = heatTerm u₀ n                           (C∞, proved by heatTerm_contDiff)
  -- Then apply the Leibniz rule norm_iteratedFDeriv_mul_le.
  let G : ℝ × ℝ → ℝ := fun q => smoothRightCutoff (c / 2) c q.1
  let H : ℝ × ℝ → ℝ := heatTerm u₀ n
  -- cutoffHeatTerm = G * H
  have hterm : cutoffHeatTerm u₀ c n = fun q => G q * H q := by
    funext q; simp [cutoffHeatTerm, heatTerm, G, H]
  -- Both factors are C²
  have hG : ContDiff ℝ (2 : ℕ∞) G :=
    (smoothRightCutoff_contDiff (c' := c / 2) (c := c)).comp contDiff_fst
  have hH : ContDiff ℝ (2 : ℕ∞) H :=
    (heatTerm_contDiff u₀ n).of_le le_top
  -- Leibniz rule gives the sum bound
  have hk' : (k : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hk
  -- Rewrite the goal to use G * H
  rw [hterm]
  -- Apply Leibniz then bound
  calc ‖iteratedFDeriv ℝ k (fun q => G q * H q) q‖
      ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i G q‖ * ‖iteratedFDeriv ℝ (k - i) H q‖ := by
        simpa [mul_assoc] using norm_iteratedFDeriv_mul_le hG hH q hk'
    _ ≤ (2 * k + 1) ^ k *
          (unitIntervalCosineEigenvalue n ^ k * M₀ *
            Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n)) := by
        -- Each term in the Leibniz sum is bounded by the majorant.
        -- Factor G = smoothRightCutoff ∘ fst: ‖D^i G q‖ ≤ 1 (cutoff is [0,1]-valued
        --   with bounded derivatives on compact support [c/2, c]).
        -- Factor H = heatTerm: ‖D^j H q‖ ≤ λ_n^j · M₀ · exp(-(c/2)·λ_n)
        --   (derivatives of exp(-t·λ_n)·â_n contribute λ_n per order,
        --    derivatives of cos(nπx) contribute nπ ≤ √λ_n per order,
        --    φ=0 for t≤c/2 kills the blow-up, for t≥c/2: exp(-t·λ_n)≤exp(-(c/2)·λ_n))
        -- The sum of C(k,i) terms for k≤2 is bounded by (2k+1)^k.
        sorry

set_option maxHeartbeats 1600000 in
/-- **Global C² of the cutoff heat semigroup series.**

The series `(t,x) ↦ ∑' n, φ(t) · exp(-t λ_n) â_n cos(nπx)` is `ContDiff ℝ 2`
as a function `ℝ² → ℝ`, where `φ = smoothRightCutoff (c/2) c`.  The proof uses
`contDiff_tsum` with the majorant from `cutoffHeatTerm_iteratedFDeriv_bound`. -/
theorem cutoffHeatSeries_contDiff_two
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {c : ℝ} (hc : 0 < c) :
    ContDiff ℝ 2 (fun q : ℝ × ℝ =>
      ∑' n : ℕ, cutoffHeatTerm u₀ c n q) := by
  have hM₀nn : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
  -- Majorant: v k n = (2k+1)^k · λ_n^k · M₀ · exp(-(c/2)·λ_n)
  let v : ℕ → ℕ → ℝ := fun k n =>
    (2 * k + 1) ^ k * (unitIntervalCosineEigenvalue n ^ k * M₀ *
      Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n))
  apply contDiff_tsum (𝕜 := ℝ) (f := cutoffHeatTerm u₀ c) (v := v)
  -- (1) Each cutoff term is C²
  · intro n
    exact cutoffHeatTerm_contDiff_two u₀ hc n
  -- (2) Majorant summability for each k ≤ 2
  · intro k hk
    show Summable (v k)
    change Summable (fun n => (2 * (k : ℝ) + 1) ^ k *
      (unitIntervalCosineEigenvalue n ^ k * M₀ *
        Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n)))
    exact (eigenvalue_pow_mul_coeff_exp_summable k (half_pos hc) hM₀nn).mul_left _
  -- (3) Uniform iterated-derivative bound (from cutoffHeatTerm_iteratedFDeriv_bound)
  · intro k n q hk
    exact cutoffHeatTerm_iteratedFDeriv_bound hu₀_bound hc k n q hk

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
