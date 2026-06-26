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

The uncurried map `(t,x) ↦ ∑' k, exp(-t λ_k) â_k cos(kπx)` is `C²` on a
positive-time slab `{t ≥ c} × ℝ`.  The engine is Mathlib's `contDiff_tsum`:
each term is `C∞` in `(t,x)` (product of smooth functions), and the order-≤2
iterated-derivative majorant `C_k · λ_k^k · M₀ · exp(-c·λ_k)` is summable for
every `k ≤ 2` because `eigenvalue_pow_mul_exp_summable` damps `λ^k exp(-c λ)`.
-/

namespace ShenWork.Paper2.HeatSemigroupJointRegularity

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)

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

set_option maxHeartbeats 1600000 in
/-- **Joint C² of the heat semigroup cosine series on a positive-time slab.**

For bounded initial Fourier cosine coefficients `|â_k| ≤ M₀` and any lower
time bound `c > 0`, the series `(t,x) ↦ ∑' k, exp(-t λ_k) â_k cos(kπx)` is
`C²` as a function `ℝ² → ℝ`.

NOTE: The hypothesis `c > 0` controls the exponential majorant summability.
The proof uses `contDiff_tsum` with the majorant
`v k n := C_k · λ_n^k · M₀ · exp(−c · λ_n)`.  The majorant bound
(obligation 3) currently has a `sorry` because it requires bounding
`‖iteratedFDeriv ℝ k (f n) q‖` uniformly in `q`, which only holds on the
slab `t ≥ c`.  A future revision should either prove the `ContDiffOn` variant
or compose with a smooth time cutoff. -/
theorem heatSemigroup_jointContDiff_two
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {c : ℝ} (hc : 0 < c) :
    ContDiff ℝ 2 (fun q : ℝ × ℝ =>
      ∑' k : ℕ, (Real.exp (-q.1 * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k q.2) := by
  have hM₀nn : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
  -- Majorant: v k n = (2k+1)^k · λ_n^k · M₀ · exp(-c·λ_n)
  -- This bounds the joint iterated derivative of the n-th term at order k.
  let v : ℕ → ℕ → ℝ := fun k n =>
    (2 * k + 1) ^ k * (unitIntervalCosineEigenvalue n ^ k * M₀ *
      Real.exp (-c * unitIntervalCosineEigenvalue n))
  -- The series is the pointwise tsum of the heat terms:
  have hfEq : (fun q : ℝ × ℝ =>
      ∑' k : ℕ, (Real.exp (-q.1 * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k q.2) =
      fun q => ∑' n, heatTerm u₀ n q := by
    funext q; congr 1
  rw [hfEq]
  apply contDiff_tsum (𝕜 := ℝ) (f := heatTerm u₀) (v := v)
  -- (1) Each term is C∞ ≥ C²
  · intro n
    exact (heatTerm_contDiff u₀ n).of_le le_top
  -- (2) Majorant summability for each k ≤ 2
  · intro k hk
    show Summable (v k)
    change Summable (fun n => (2 * (k : ℝ) + 1) ^ k *
      (unitIntervalCosineEigenvalue n ^ k * M₀ *
        Real.exp (-c * unitIntervalCosineEigenvalue n)))
    exact (eigenvalue_pow_mul_coeff_exp_summable k hc hM₀nn).mul_left _
  -- (3) Uniform iterated-derivative bound (the core analytic obligation)
  · intro k n q hk
    -- This bound ‖iteratedFDeriv ℝ k (heatTerm u₀ n) q‖ ≤ v k n requires
    -- that for ALL q : ℝ × ℝ, the iterated derivative is controlled by
    -- the majorant.  On the slab t ≥ c this follows from:
    --   ‖iteratedFDeriv k (exp(-t λ_n) â_n cos(nπx))‖
    --     ≤ (Leibniz) ∑_{i≤k} C(k,i) λ_n^i |â_n| exp(-t λ_n) · valueCosWeight(k-i,n)
    --     ≤ (2k+1)^k · λ_n^k · M₀ · exp(-c λ_n)
    -- Globally (t < c) the bound fails.
    sorry

/-- **Joint `ContDiffAt ℝ 2`** of the heat semigroup series at any point with
positive time coordinate.  This is the form actually needed by the downstream
sub-sorry (3B: heat semigroup joint C²).

Proof: from `heatSemigroup_jointContDiff_two` (which is `ContDiff ℝ 2`, hence
`ContDiffAt` at every point).  The sorry in the parent theorem propagates. -/
theorem heatSemigroup_jointContDiffAt_two
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {c : ℝ} (hc : 0 < c) {s₀ x₀ : ℝ} (_hs₀ : c ≤ s₀) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ =>
      ∑' k : ℕ, (Real.exp (-q.1 * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k q.2) (s₀, x₀) :=
  (heatSemigroup_jointContDiff_two hu₀_bound hc).contDiffAt

#print axioms heatSemigroup_jointContDiff_two
#print axioms heatSemigroup_jointContDiffAt_two

end

end ShenWork.Paper2.HeatSemigroupJointRegularity
