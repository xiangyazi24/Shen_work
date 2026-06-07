/-
  Additive: resolver strict positivity (the ledger `Hvpos` residual), and the
  reusable `cosineCoeffs_const`.

  `Hvpos : 0 < mildChemicalConcentration p u t x` is needed by the frontier
  assembly.  Route: the source `ν·u^γ ≥ c₀ := ν·m^γ > 0` (m = min u on [0,1]),
  and the elliptic resolver of a source bounded below by the constant `c₀` is
  bounded below by `c₀/μ`:
    `R(u) = c₀/μ + (reconstruction of ν·u^γ − c₀)`,  the second term ≥ 0.

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.Paper2.IntervalMildPicardRegularity
import ShenWork.PDE.IntervalResolverPositivity
import ShenWork.PDE.IntervalNeumannEllipticResolverR
import ShenWork.PDE.IntervalFullKernelInterchange
import ShenWork.PDE.IntervalFullKernelSupBound
import ShenWork.Paper2.IntervalPicardLimitCoeffConv
import ShenWork.PDE.IntervalResolverGradientBridge

open Set Filter Topology MeasureTheory
open ShenWork.PDE (intervalNeumannResolverR intervalNeumannResolverCoeff
  intervalNeumannResolverSourceCoeff intervalNeumannResolverWeight
  intervalNeumannResolver_denom_pos)
open ShenWork.IntervalResolverGradientBridge (resolverCoeff_re_eq)
open ShenWork.IntervalResolverPositivity (summable_abs_sourceCoeff_mul_weight)
open ShenWork.Paper3 (unitIntervalNeumannSpectrum)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalNeumannFullKernel
  intervalFullSemigroupOperator intervalNeumannFullKernel_integrable
  intervalNeumannFullKernel_nonneg)
open ShenWork.IntervalResolverPositivity (intervalNeumannFullKernel_cosineKernel_identity)
open ShenWork.IntervalFullKernelInterchange
  (intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional)
open ShenWork.IntervalDomain (intervalMeasure intervalDomainPoint)
open ShenWork.IntervalResolverPositivity
  (laplaceHeatTrunc_tendsto laplaceHeatTrunc_nonneg summable_resolverTarget)
open ShenWork.IntervalPicardLimitCoeffConv (cosineCoeffs_sub_eq)
open ShenWork.IntervalMildPicardRegularity (cosineCoeffs_eq_factor_mul_integral)

noncomputable section

namespace ShenWork.IntervalDomainResolverStrictPos

/-- **Cosine coefficients of a constant.**  `cosineCoeffs (const c) n = c` at the
zeroth mode and `0` for `n ≥ 1` (`∫₀¹ cos(nπx) dx = sin(nπ)/(nπ) = 0`). -/
theorem cosineCoeffs_const (c : ℝ) (n : ℕ) :
    cosineCoeffs (fun _ => c) n = if n = 0 then c else 0 := by
  rw [cosineCoeffs_eq_factor_mul_integral]
  by_cases hn : n = 0
  · subst hn
    simp only [Nat.cast_zero, zero_mul, Real.cos_zero, one_mul]
    rw [intervalIntegral.integral_const]
    norm_num
  · simp only [if_neg hn]
    have hcos_int : (∫ x in (0:ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x)) = 0 := by
      have key : ∀ x : ℝ,
          HasDerivAt (fun y => Real.sin ((n : ℝ) * Real.pi * y) / ((n : ℝ) * Real.pi))
            (Real.cos ((n : ℝ) * Real.pi * x)) x := by
        intro x
        have h1 : HasDerivAt (fun y : ℝ => (n : ℝ) * Real.pi * y) ((n : ℝ) * Real.pi) x := by
          simpa using (hasDerivAt_id x).const_mul ((n : ℝ) * Real.pi)
        have h2 : HasDerivAt (fun y => Real.sin ((n : ℝ) * Real.pi * y))
            (Real.cos ((n : ℝ) * Real.pi * x) * ((n : ℝ) * Real.pi)) x := h1.sin
        have hnp : (n : ℝ) * Real.pi ≠ 0 := by
          have : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
          positivity
        have h3 := h2.div_const ((n : ℝ) * Real.pi)
        convert h3 using 1
        field_simp
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => key x)
        ((Real.continuous_cos.comp (by fun_prop)).intervalIntegrable 0 1)]
      have h1 : (n : ℝ) * Real.pi * 1 = (n : ℝ) * Real.pi := by ring
      rw [h1, Real.sin_nat_mul_pi]; simp
    rw [intervalIntegral.integral_mul_const, hcos_int, zero_mul, mul_zero]

/-- **Heat value lower bound.**  If `f` is continuous, bounded, and `≥ c₀` on
all of `ℝ`, then the cosine-spectral heat value is `≥ c₀` at interior `x`
(`t > 0`): `S(t)f = ∫K·f ≥ ∫K·c₀ = S(t)(const c₀) = c₀`. -/
theorem heatValue_ge_const {f : ℝ → ℝ} {c₀ M : ℝ}
    (hf_cont : Continuous f) (hf_ge : ∀ y, c₀ ≤ f y) (hf_bdd : ∀ y, |f y| ≤ M)
    {t : ℝ} (ht : 0 < t) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    c₀ ≤ unitIntervalCosineHeatValue t (cosineCoeffs f) x := by
  have hker : ∀ y, intervalNeumannFullKernel t x y
      = ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
        (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y)) :=
    fun y => intervalNeumannFullKernel_cosineKernel_identity ht x y
  have hSf := intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional t ht f hf_cont x hx hker
  have hSc := intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional t ht
    (fun _ => c₀) continuous_const x hx hker
  have hConst : unitIntervalCosineHeatValue t (cosineCoeffs (fun _ => c₀)) x = c₀ := by
    rw [unitIntervalCosineHeatValue, tsum_eq_single 0
      (fun n hn => by rw [cosineCoeffs_const, if_neg hn, mul_zero])]
    rw [cosineCoeffs_const, if_pos rfl]
    simp [unitIntervalCosineHeatPointWeight, unitIntervalCosineEigenvalue,
      unitIntervalCosineMode]
  have hKint : Integrable (fun y => intervalNeumannFullKernel t x y) (intervalMeasure 1) :=
    intervalNeumannFullKernel_integrable ht x
  have hKc : Integrable (fun y => intervalNeumannFullKernel t x y * c₀) (intervalMeasure 1) :=
    hKint.mul_const c₀
  have hKf : Integrable (fun y => intervalNeumannFullKernel t x y * f y) (intervalMeasure 1) := by
    have h := hKint.bdd_mul hf_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => by rw [Real.norm_eq_abs]; exact hf_bdd y))
    refine h.congr ?_
    filter_upwards with y using mul_comm (f y) (intervalNeumannFullKernel t x y)
  have hmono : intervalFullSemigroupOperator t (fun _ => c₀) x
      ≤ intervalFullSemigroupOperator t f x := by
    simp only [intervalFullSemigroupOperator]
    refine integral_mono hKc hKf (fun y => ?_)
    exact mul_le_mul_of_nonneg_left (hf_ge y) (intervalNeumannFullKernel_nonneg ht x y)
  rw [← hSf]
  calc c₀ = unitIntervalCosineHeatValue t (cosineCoeffs (fun _ => c₀)) x := hConst.symm
    _ = intervalFullSemigroupOperator t (fun _ => c₀) x := hSc.symm
    _ ≤ intervalFullSemigroupOperator t f x := hmono

/-- **Standalone cosine reconstruction nonnegativity** (the `u`-tie-free core of
`intervalNeumannResolverR_nonneg_interior`): for `g ≥ 0` continuous with `ℓ²`
coefficients, the resolved cosine series is `≥ 0` at interior `x`. -/
theorem cosineReconstruction_nonneg (p : CM2Params) {g : ℝ → ℝ}
    (hg_cont : Continuous g) (hg_nonneg : ∀ y, 0 ≤ g y)
    (hĝ : Summable (fun k => (cosineCoeffs g k) ^ 2))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ ∑' k, cosineCoeffs g k * unitIntervalCosineMode k x
          / (p.μ + unitIntervalCosineEigenvalue k) := by
  refine isClosed_Ici.mem_of_tendsto (laplaceHeatTrunc_tendsto (p := p) hĝ x) ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
  exact laplaceHeatTrunc_nonneg hg_cont hg_nonneg hx hT

/-- **Constant-source reconstruction** `= c₀/μ` (only the `k = 0` mode survives;
`mode₀ = 1`, `λ₀ = 0`). -/
theorem const_reconstruction (p : CM2Params) (c₀ x : ℝ) :
    (∑' k, cosineCoeffs (fun _ => c₀) k * unitIntervalCosineMode k x
        / (p.μ + unitIntervalCosineEigenvalue k)) = c₀ / p.μ := by
  rw [tsum_eq_single 0
    (fun n hn => by rw [cosineCoeffs_const, if_neg hn, zero_mul, zero_div])]
  rw [cosineCoeffs_const, if_pos rfl]
  simp [unitIntervalCosineMode, unitIntervalCosineEigenvalue]

/-- **Reconstruction lower bound.**  For `f ≥ c₀` continuous with `ℓ²`
coefficients (and `f − c₀` likewise), the resolved cosine series is `≥ c₀/μ` at
interior `x`: split `f = (f − c₀) + c₀`, the first reconstruction is `≥ 0`, the
constant one `= c₀/μ`. -/
theorem reconstruction_ge_const (p : CM2Params) {f : ℝ → ℝ} {c₀ : ℝ}
    (hf_cont : Continuous f) (hf_ge : ∀ y, c₀ ≤ f y)
    (hĝ : Summable (fun k => (cosineCoeffs (fun y => f y - c₀) k) ^ 2))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    c₀ / p.μ ≤ ∑' k, cosineCoeffs f k * unitIntervalCosineMode k x
          / (p.μ + unitIntervalCosineEigenvalue k) := by
  have hsplit : ∀ k, cosineCoeffs f k
      = cosineCoeffs (fun y => f y - c₀) k + cosineCoeffs (fun _ => c₀) k := by
    intro k
    have hsub : cosineCoeffs (fun y => f y - c₀) k
        = cosineCoeffs f k - cosineCoeffs (fun _ => c₀) k :=
      cosineCoeffs_sub_eq hf_cont.continuousOn continuousOn_const k
    linarith [hsub]
  have hterm : ∀ k, cosineCoeffs f k * unitIntervalCosineMode k x
        / (p.μ + unitIntervalCosineEigenvalue k)
      = cosineCoeffs (fun y => f y - c₀) k * unitIntervalCosineMode k x
          / (p.μ + unitIntervalCosineEigenvalue k)
        + cosineCoeffs (fun _ => c₀) k * unitIntervalCosineMode k x
          / (p.μ + unitIntervalCosineEigenvalue k) := by
    intro k; rw [hsplit k]; ring
  have hconst_summable : Summable (fun k => cosineCoeffs (fun _ => c₀) k
      * unitIntervalCosineMode k x / (p.μ + unitIntervalCosineEigenvalue k)) := by
    refine summable_of_ne_finset_zero (s := {0}) (fun k hk => ?_)
    rw [cosineCoeffs_const, if_neg (by simpa using hk), zero_mul, zero_div]
  rw [tsum_congr hterm,
    (summable_resolverTarget (p := p) hĝ x).tsum_add hconst_summable,
    const_reconstruction]
  have hnn := cosineReconstruction_nonneg p (hf_cont.sub continuous_const)
    (fun y => by linarith [hf_ge y]) hĝ hx
  linarith [hnn]

/-- **Resolver strict lower bound.**  If the source `f` is continuous, `≥ c₀`,
`ℓ²` (and `f − c₀` too), and matches the resolver source coefficients of `u`,
then `R(u) ≥ c₀/μ` on the closed interval.  (Mirror of
`intervalNeumannResolverR_nonneg_of_nonneg_source` with the `c₀/μ` floor.) -/
theorem intervalNeumannResolverR_ge_of_source_ge {p : CM2Params}
    {u : intervalDomainPoint → ℝ} {f : ℝ → ℝ} {c₀ : ℝ}
    (hf_cont : Continuous f) (hf_ge : ∀ y, c₀ ≤ f y)
    (hf_coeff : ∀ k, cosineCoeffs f k = (intervalNeumannResolverSourceCoeff p u k).re)
    (hâ : Summable (fun k => (cosineCoeffs f k) ^ 2))
    (hĝ : Summable (fun k => (cosineCoeffs (fun y => f y - c₀) k) ^ 2))
    (xp : intervalDomainPoint) :
    c₀ / p.μ ≤ intervalNeumannResolverR p u xp := by
  set g : ℝ → ℝ := fun x => ∑' k, (intervalNeumannResolverCoeff p u k).re
    * unitIntervalCosineMode k x with hg
  have hl1 : Summable (fun k => |(intervalNeumannResolverCoeff p u k).re|) := by
    have hbase : Summable (fun k => |(intervalNeumannResolverSourceCoeff p u k).re|
        * intervalNeumannResolverWeight p k) :=
      summable_abs_sourceCoeff_mul_weight (p := p) (hâ.congr (fun k => by rw [hf_coeff]))
    refine hbase.congr (fun k => ?_)
    rw [resolverCoeff_re_eq, abs_div, abs_of_pos (intervalNeumannResolver_denom_pos p k),
      intervalNeumannResolverWeight]; ring
  have hg_cont : Continuous g := by
    refine continuous_tsum (fun k => ?_) hl1 (fun k x => ?_)
    · exact continuous_const.mul (by unfold unitIntervalCosineMode; fun_prop)
    · rw [Real.norm_eq_abs, abs_mul]
      calc |(intervalNeumannResolverCoeff p u k).re| * |unitIntervalCosineMode k x|
          ≤ |(intervalNeumannResolverCoeff p u k).re| * 1 :=
            mul_le_mul_of_nonneg_left
              (by rw [unitIntervalCosineMode]; exact Real.abs_cos_le_one _) (abs_nonneg _)
        _ = |(intervalNeumannResolverCoeff p u k).re| := mul_one _
  have heig : ∀ k, p.μ + unitIntervalNeumannSpectrum.eigenvalue k
      = p.μ + unitIntervalCosineEigenvalue k := by
    intro k; congr 1
    rw [show unitIntervalNeumannSpectrum.eigenvalue k = (k : ℝ) ^ 2 * Real.pi ^ 2 from rfl,
      unitIntervalCosineEigenvalue]; ring
  have hsub : Set.Ioo (0:ℝ) 1 ⊆ {x : ℝ | c₀ / p.μ ≤ g x} := by
    intro x hx
    have hrecon : g x = ∑' k, cosineCoeffs f k * unitIntervalCosineMode k x
        / (p.μ + unitIntervalCosineEigenvalue k) := by
      rw [hg]; refine tsum_congr (fun k => ?_)
      rw [resolverCoeff_re_eq, hf_coeff k, heig k]; ring
    show c₀ / p.μ ≤ g x
    rw [hrecon]; exact reconstruction_ge_const p hf_cont hf_ge hĝ hx
  have hIcc : Set.Icc (0:ℝ) 1 ⊆ {x : ℝ | c₀ / p.μ ≤ g x} := by
    rw [← closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]
    exact (isClosed_le continuous_const hg_cont).closure_subset_iff.mpr hsub
  show c₀ / p.μ ≤ g xp.1
  exact hIcc xp.2

end ShenWork.IntervalDomainResolverStrictPos
