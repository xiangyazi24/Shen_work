/-
  ShenWork/Paper2/IntervalResolverHighRegularity.lean

  High regularity (C⁴), evenness about 0, and symmetry about x=1 for the
  lifted interval Neumann elliptic resolver cosine series
  `x ↦ ∑' k, (v̂_k).re · cos(kπx)`.

  ## ContDiff ℝ 4

  The resolver coefficient `v̂_k = â_k / (μ + λ_k)` satisfies the bounded
  multiplier relation `λ_k |v̂_k| ≤ |â_k|` (from the coefficient-form
  elliptic equation `(μ+λ_k)·v̂_k = â_k`).  Hence
  `λ_k² |v̂_k| ≤ λ_k |â_k|`, so eigenvalue-weighted ℓ¹ summability of the
  source coefficients implies eigenvalue-squared summability of the resolver
  coefficients, feeding `cosineCoeffSeries_contDiff_four_of_eigenvalue_sq_summable`
  for C⁴.

  ## Evenness about 0

  `cos(kπ(−x)) = cos(kπx)`, so the cosine series is even by `tsum_congr`.

  ## Symmetry about x = 1

  `cos(kπ(2−x)) = cos(kπ((−x)+2)) = cos(kπ(−x)) = cos(kπx)` (period-2 +
  evenness), giving `f(2−x) = f(x)` by `tsum_congr`.
-/
import ShenWork.PDE.IntervalNeumannEllipticResolverR
import ShenWork.PDE.CosineSpectrum
import ShenWork.Paper2.IntervalParabolicDuhamelGainNonCircular

open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.PDE
open ShenWork.Paper3 (unitIntervalNeumannSpectrum)
open scoped BigOperators

noncomputable section

namespace ShenWork.Paper2.IntervalResolverHighRegularity

/-! ## The lifted resolver cosine series -/

/-- The lifted resolver cosine series as a function `ℝ → ℝ`.  This is the
ambient-line extension of `intervalNeumannResolverR p u` via the cosine series
representation — the two agree on `[0,1]` (each term is
`(v̂_k).re · cos(kπx)` = `(v̂_k).re · unitIntervalCosineMode k x`). -/
def intervalResolverLiftR (p : CM2Params) (u : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun x => ∑' k : ℕ, (intervalNeumannResolverCoeff p u k).re * cosineMode k x

/-! ## Cosine mode symmetry lemmas (self-contained, no HeatFloor import) -/

/-- `cosineMode k` is even: `cos(kπ(−x)) = cos(kπx)`. -/
private theorem cosineMode_neg (k : ℕ) (x : ℝ) :
    cosineMode k (-x) = cosineMode k x := by
  unfold cosineMode
  rw [show (k : ℝ) * Real.pi * (-x) = -((k : ℝ) * Real.pi * x) from by ring, Real.cos_neg]

/-- `cosineMode k` has period `2`: `cos(kπ(x+2)) = cos(kπx)`. -/
private theorem cosineMode_add_two (k : ℕ) (x : ℝ) :
    cosineMode k (x + 2) = cosineMode k x := by
  unfold cosineMode
  rw [show (k : ℝ) * Real.pi * (x + 2)
        = (k : ℝ) * Real.pi * x + ((k : ℤ) : ℝ) * (2 * Real.pi) from by push_cast; ring,
    Real.cos_add_int_mul_two_pi _ (k : ℤ)]

/-! ## Eigenvalue-squared summability of resolver coefficients -/

/-- The eigenvalue `λ_k = (kπ)²` as defined in the heat semigroup module. -/
private theorem eigenvalue_eq (k : ℕ) :
    unitIntervalCosineEigenvalue k =
      unitIntervalNeumannSpectrum.eigenvalue k := by
  change ((k : ℝ) * Real.pi) ^ 2 = (k : ℝ) ^ 2 * Real.pi ^ 2; ring

/-- **Bounded resolvent multiplier**: from the coefficient-form elliptic equation
`(μ+λ_k)·v̂_k = â_k`, the eigenvalue-weighted resolver coefficient is dominated
by the source coefficient: `λ_k · |(v̂_k).re| ≤ |(â_k).re|`. -/
theorem resolverCoeff_eigenWeighted_le_source
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (k : ℕ) :
    unitIntervalCosineEigenvalue k * |(intervalNeumannResolverCoeff p u k).re| ≤
      |(intervalNeumannResolverSourceCoeff p u k).re| := by
  -- The real-part elliptic identity: (μ + λ_k)·v̂_k.re = â_k.re
  have hpos : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue k := by
    have hlam : 0 ≤ unitIntervalNeumannSpectrum.eigenvalue k := by
      change (0 : ℝ) ≤ (k : ℝ) ^ 2 * Real.pi ^ 2; positivity
    linarith [p.hμ]
  have hellRe : (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) *
        (intervalNeumannResolverCoeff p u k).re =
      (intervalNeumannResolverSourceCoeff p u k).re := by
    have hcast :
        ((p.μ : ℂ) + (unitIntervalNeumannSpectrum.eigenvalue k : ℂ)) =
          (((p.μ + unitIntervalNeumannSpectrum.eigenvalue k : ℝ)) : ℂ) := by
      push_cast; ring
    have hk := congrArg Complex.re (intervalNeumannResolverCoeff_elliptic p u k)
    rw [hcast, Complex.re_ofReal_mul] at hk
    exact hk
  -- λ_k ≤ μ + λ_k, so λ_k |v̂_k.re| ≤ (μ + λ_k) |v̂_k.re| = |â_k.re|
  rw [eigenvalue_eq]
  have habs : (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) *
      |(intervalNeumannResolverCoeff p u k).re| =
      |(intervalNeumannResolverSourceCoeff p u k).re| := by
    rw [← abs_of_pos hpos, ← abs_mul, hellRe]
  have hle : unitIntervalNeumannSpectrum.eigenvalue k ≤
      p.μ + unitIntervalNeumannSpectrum.eigenvalue k := by linarith [p.hμ]
  calc unitIntervalNeumannSpectrum.eigenvalue k *
          |(intervalNeumannResolverCoeff p u k).re|
      ≤ (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) *
          |(intervalNeumannResolverCoeff p u k).re| :=
        mul_le_mul_of_nonneg_right hle (abs_nonneg _)
    _ = |(intervalNeumannResolverSourceCoeff p u k).re| := habs

/-- **Eigenvalue-squared summability of resolver coefficients** from
eigenvalue-weighted ℓ¹ of source coefficients.

`λ_k² |v̂_k.re| = λ_k · (λ_k |v̂_k.re|) ≤ λ_k · |â_k.re|`. -/
theorem resolverCoeff_eigenSq_summable_of_sourceEigenL1
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hsrc : Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        |(intervalNeumannResolverSourceCoeff p u k).re|)) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        (unitIntervalCosineEigenvalue k *
          |(intervalNeumannResolverCoeff p u k).re|)) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hsrc
  · have h0 : (0 : ℝ) ≤ unitIntervalCosineEigenvalue k := by
      change (0 : ℝ) ≤ ((k : ℝ) * Real.pi) ^ 2; positivity
    exact mul_nonneg h0 (mul_nonneg h0 (abs_nonneg _))
  · have h0 : (0 : ℝ) ≤ unitIntervalCosineEigenvalue k := by
      change (0 : ℝ) ≤ ((k : ℝ) * Real.pi) ^ 2; positivity
    calc unitIntervalCosineEigenvalue k *
            (unitIntervalCosineEigenvalue k *
              |(intervalNeumannResolverCoeff p u k).re|)
        ≤ unitIntervalCosineEigenvalue k *
            |(intervalNeumannResolverSourceCoeff p u k).re| := by
          gcongr
          exact resolverCoeff_eigenWeighted_le_source p u k

/-! ## ContDiff ℝ 4 -/

/-- **The lifted resolver cosine series is C⁴** when the source coefficients
have eigenvalue-weighted ℓ¹ summability.

Route: eigenvalue-weighted ℓ¹ of source ⟹ eigenvalue-squared summability
of resolver (via `resolverCoeff_eigenSq_summable_of_sourceEigenL1`) ⟹ C⁴
(via `cosineCoeffSeries_contDiff_four_of_eigenvalue_sq_summable`).

The C⁴ engine (`contDiff_tsum_of_eventually` with eigenvalue⁴ majorant) is
the standard cosine-series smoothing tool from
`IntervalParabolicDuhamelGainNonCircular`. -/
theorem intervalResolverLiftR_contDiff_four
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hsrc : Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        |(intervalNeumannResolverSourceCoeff p u k).re|)) :
    ContDiff ℝ 4 (intervalResolverLiftR p u) := by
  unfold intervalResolverLiftR
  exact ShenWork.Paper2.ParabolicDuhamelGainNonCircular.cosineCoeffSeries_contDiff_four_of_eigenvalue_sq_summable
    (resolverCoeff_eigenSq_summable_of_sourceEigenL1 hsrc)

/-! ## Evenness about 0 -/

/-- The lifted resolver cosine series is **even**: `f(−x) = f(x)`.  This is
immediate from `cos(kπ(−x)) = cos(kπx)`. -/
theorem intervalResolverLiftR_even
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (x : ℝ) :
    intervalResolverLiftR p u (-x) = intervalResolverLiftR p u x := by
  unfold intervalResolverLiftR
  exact tsum_congr (fun k => by rw [cosineMode_neg])

/-- The lifted resolver cosine series is **even** (function-level statement). -/
theorem intervalResolverLiftR_even_fun
    (p : CM2Params) (u : intervalDomainPoint → ℝ) :
    intervalResolverLiftR p u ∘ Neg.neg = intervalResolverLiftR p u := by
  funext x
  exact intervalResolverLiftR_even p u x

/-! ## Symmetry about x = 1 -/

/-- `cosineMode k` satisfies `cos(kπ(2−x)) = cos(kπx)`.  This is the
reflection-about-1 identity: `2 − x = (−x) + 2`, then period-2 + evenness. -/
private theorem cosineMode_reflect_one (k : ℕ) (x : ℝ) :
    cosineMode k (2 - x) = cosineMode k x := by
  rw [show (2 : ℝ) - x = (-x) + 2 from by ring, cosineMode_add_two, cosineMode_neg]

/-- The lifted resolver cosine series is **symmetric about x = 1**:
`f(2−x) = f(x)`.  This is the cosine-series counterpart of the Neumann
boundary condition at `x = 1`: reflection about the right endpoint. -/
theorem intervalResolverLiftR_reflect_one
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (x : ℝ) :
    intervalResolverLiftR p u (2 - x) = intervalResolverLiftR p u x := by
  unfold intervalResolverLiftR
  exact tsum_congr (fun k => by rw [cosineMode_reflect_one])

/-- The lifted resolver cosine series has **period 2**: `f(x+2) = f(x)`.
From `cos(kπ(x+2)) = cos(kπx)`. -/
theorem intervalResolverLiftR_periodic
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (x : ℝ) :
    intervalResolverLiftR p u (x + 2) = intervalResolverLiftR p u x := by
  unfold intervalResolverLiftR
  exact tsum_congr (fun k => by rw [cosineMode_add_two])

/-! ## Global nonnegativity from [0,1] nonnegativity + symmetry + periodicity -/

/-- The lifted resolver is `Function.Periodic` with period `2`. -/
theorem intervalResolverLiftR_periodic_fun
    (p : CM2Params) (u : intervalDomainPoint → ℝ) :
    Function.Periodic (intervalResolverLiftR p u) 2 :=
  intervalResolverLiftR_periodic p u

/-- **Global nonnegativity** of the lifted resolver cosine series from
nonnegativity on `[0,1]`.

The argument uses three symmetries:
- Period 2: `f(x+2) = f(x)` → reduces arbitrary `x` to `[0,2)`.
- Reflection about 1: `f(2-x) = f(x)` → reduces `[1,2)` to `(0,1]`.
Combined: every `x ∈ ℝ` maps to some `x' ∈ [0,1]` with `f(x) = f(x')`. -/
theorem intervalResolverLiftR_nonneg_of_nonneg_on_Icc
    (p : CM2Params) (u : intervalDomainPoint → ℝ)
    (hnn : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalResolverLiftR p u x)
    (x : ℝ) :
    0 ≤ intervalResolverLiftR p u x := by
  set V := intervalResolverLiftR p u with hV
  have hper := intervalResolverLiftR_periodic_fun p u
  have hsymm := intervalResolverLiftR_reflect_one p u
  set n := ⌊x / 2⌋ with hn_def
  set r := x - n * 2 with hr_def
  have hrV : V x = V r := by
    show V x = V (x - ↑n * 2)
    exact (hper.sub_int_mul_eq n).symm
  have hr_lo : 0 ≤ r := by
    have := Int.floor_le (x / 2)
    linarith
  have hr_hi : r < 2 := by
    have := Int.lt_floor_add_one (x / 2)
    linarith
  rw [hrV]
  by_cases hr1 : r ≤ 1
  · exact hnn r ⟨hr_lo, hr1⟩
  · simp only [not_le] at hr1
    have : V r = V (2 - r) := (hsymm r).symm
    rw [this]
    exact hnn (2 - r) ⟨by linarith, by linarith⟩

/-- **Global strict positivity** of `1 + V` where `V` is the lifted resolver
cosine series, from nonnegativity on `[0,1]`. -/
theorem intervalResolverLiftR_one_add_pos_of_nonneg_on_Icc
    (p : CM2Params) (u : intervalDomainPoint → ℝ)
    (hnn : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalResolverLiftR p u x)
    (x : ℝ) :
    (0 : ℝ) < 1 + intervalResolverLiftR p u x :=
  lt_of_lt_of_le one_pos (le_add_of_nonneg_right
    (intervalResolverLiftR_nonneg_of_nonneg_on_Icc p u hnn x))

-- Axiom audit
#print axioms resolverCoeff_eigenWeighted_le_source
#print axioms resolverCoeff_eigenSq_summable_of_sourceEigenL1
#print axioms intervalResolverLiftR_contDiff_four
#print axioms intervalResolverLiftR_even
#print axioms intervalResolverLiftR_reflect_one
#print axioms intervalResolverLiftR_periodic
#print axioms intervalResolverLiftR_nonneg_of_nonneg_on_Icc
#print axioms intervalResolverLiftR_one_add_pos_of_nonneg_on_Icc

end ShenWork.Paper2.IntervalResolverHighRegularity
