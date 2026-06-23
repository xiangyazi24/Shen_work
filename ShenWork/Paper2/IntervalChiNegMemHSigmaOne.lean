/-
  ShenWork/Paper2/IntervalChiNegMemHSigmaOne.lean

  χ₀<0 — DISCHARGE of the Neumann-resolver positivity residual `hvnn`.

  The capstone `meanReach_H1_conjugate` (IntervalChiNegSeamFixedReach) reaches
  `TrajectoryHSigmaEnvelope 1` for `u = conjugatePicardLimit p u₀ DB.T` carrying
  the explicit `CarrySeam`.  This file PROVES — fully unconditionally, from the
  landed heat-Laplace positivity primitives — the genuinely-irreducible carried
  field `hvnn`:

    `0 ≤ resolverValue μ (cosineCoeffs f) x`   for every real `x`,

  whenever `f` is continuous, nonnegative, and ℓ²(cosine).  The Neumann resolvent
  `(μ−Δ)⁻¹ = ∫₀^∞ e^{−μt} e^{tΔ} dt` is positivity-preserving because the Neumann
  heat semigroup is; the landed `laplaceHeatTrunc_{tendsto,nonneg}` build exactly
  this representation (interior), extended to `[0,1]` by continuity of the cosine
  series and to all of `ℝ` by the even/period-2 symmetry of the cosine basis.

  This is the heat-positivity discharge of `hvnn` only — NON-CIRCULAR (no
  `localClassicalSolution`, no `C²`-of-`u`); it uses only continuity + ℓ² of `f`.
  The remaining `CarrySeam`/bundle residuals (the per-τ bridges from `E`, the base
  flux-factor envelope `E₀`, the per-τ decomp `hmd`) are genuine mild content and
  are NOT discharged here; see the SIGNATURE AUDIT at the end of the file.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.  Lines ≤100.
-/
import ShenWork.PDE.IntervalResolverPositivity
import ShenWork.Paper2.IntervalDenomEnvelopeResolver
import ShenWork.Paper2.IntervalChiNegCloseBaseSeed
import ShenWork.Paper2.IntervalMildPicard

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegMemHSigmaOne

open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HSigmaScale (lam)
open ShenWork.Paper2.IntervalDenomEnvelopeResolver (resolverValue)
open ShenWork.PDE (intervalNeumannResolverWeight intervalNeumannResolverWeight_sq_summable)
open ShenWork.IntervalResolverPositivity
  (laplaceHeatTrunc_nonneg laplaceHeatTrunc_tendsto)
open ShenWork.Paper3 (unitIntervalNeumannSpectrum)

/-- A dummy `CM2Params` carrying an arbitrary `μ > 0` in its `μ` field (all other
fields are inert positives), used only to instantiate the `p.μ`-parametrized
heat-Laplace primitives at a generic spectral parameter. -/
def dummyParams {μ : ℝ} (hμ : 0 < μ) : CM2Params where
  N := 1; hN := by norm_num
  α := 1; hα := by norm_num
  γ := 1; hγ := by norm_num
  m := 1; hm := by norm_num
  μ := μ; hμ := hμ
  ν := 1; hν := by norm_num
  χ₀ := 0
  a := 0; ha := le_refl 0
  b := 0; hb := le_refl 0
  β := 0; hβ := le_refl 0

/-- `λ_k = (kπ)² = lam k`, in both spectral notations. -/
theorem eig_eq_lam (k : ℕ) :
    unitIntervalNeumannSpectrum.eigenvalue k = lam k := by
  show (k : ℝ) ^ 2 * Real.pi ^ 2 = ((k : ℝ) * Real.pi) ^ 2
  ring

/-- ℓ¹ majorant of the resolver coefficients (AM–GM of the two ℓ²'s). -/
theorem resolverCoeff_l1 {μ : ℝ} (hμ : 0 < μ) {f : ℝ → ℝ}
    (hfsq : Summable fun k : ℕ => (cosineCoeffs f k) ^ 2) :
    Summable fun k : ℕ => |cosineCoeffs f k| / (μ + lam k) := by
  have hw := intervalNeumannResolverWeight_sq_summable (dummyParams hμ)
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    ((hfsq.add hw).div_const 2)
  · have hd : 0 < μ + lam k := by have := HSigmaScale.lam_nonneg k; linarith
    positivity
  have hd : 0 < μ + lam k := by have := HSigmaScale.lam_nonneg k; linarith
  have hweq : intervalNeumannResolverWeight (dummyParams hμ) k = 1 / (μ + lam k) := by
    rw [intervalNeumannResolverWeight, eig_eq_lam]; rfl
  rw [hweq]
  have h1 : |cosineCoeffs f k| / (μ + lam k)
      = |cosineCoeffs f k| * (1 / (μ + lam k)) := by ring
  rw [h1]
  nlinarith [sq_nonneg (|cosineCoeffs f k| - 1 / (μ + lam k)), sq_abs (cosineCoeffs f k),
    abs_nonneg (cosineCoeffs f k), one_div_nonneg.mpr hd.le, hd]

/-- Continuity of the resolver value as a function of `x` (Weierstrass-M). -/
theorem resolverValue_continuous {μ : ℝ} (hμ : 0 < μ) {f : ℝ → ℝ}
    (hfsq : Summable fun k : ℕ => (cosineCoeffs f k) ^ 2) :
    Continuous (resolverValue μ (cosineCoeffs f)) := by
  have hl1 := resolverCoeff_l1 hμ hfsq
  refine continuous_tsum (fun k => ?_) hl1 (fun k x => ?_)
  · exact (continuous_const.mul
      (by unfold ShenWork.CosineSpectrum.cosineMode; fun_prop))
  · have hd : 0 < μ + lam k := by have := HSigmaScale.lam_nonneg k; linarith
    rw [HSigmaScale.resolverCoeff, Real.norm_eq_abs, abs_mul, abs_div,
      abs_of_pos hd]
    calc |cosineCoeffs f k| / (μ + lam k) * |ShenWork.CosineSpectrum.cosineMode k x|
        ≤ |cosineCoeffs f k| / (μ + lam k) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          unfold ShenWork.CosineSpectrum.cosineMode; exact Real.abs_cos_le_one _
      _ = |cosineCoeffs f k| / (μ + lam k) := mul_one _

/-- **Interior positivity (generic μ).**  Combines `laplaceHeatTrunc_nonneg` with
`laplaceHeatTrunc_tendsto` and the closed cone `Ici 0`. -/
theorem resolverValue_nonneg_interior {μ : ℝ} (hμ : 0 < μ) {f : ℝ → ℝ}
    (hf_cont : Continuous f) (hf_nonneg : ∀ y, 0 ≤ f y)
    (hfsq : Summable fun k : ℕ => (cosineCoeffs f k) ^ 2)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ resolverValue μ (cosineCoeffs f) x := by
  set p := dummyParams hμ with hp
  have hlim := laplaceHeatTrunc_tendsto (p := p) (â := cosineCoeffs f) hfsq x
  have hev : ∀ᶠ T in Filter.atTop,
      0 ≤ ∫ t in (0:ℝ)..T, Real.exp (-p.μ * t)
        * unitIntervalCosineHeatValue t (cosineCoeffs f) x := by
    filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with T hT
    exact laplaceHeatTrunc_nonneg (p := p) hf_cont hf_nonneg hx hT
  have hge : 0 ≤ ∑' k : ℕ, cosineCoeffs f k * unitIntervalCosineMode k x
      / (p.μ + unitIntervalCosineEigenvalue k) :=
    Set.mem_Ici.mp (isClosed_Ici.mem_of_tendsto hlim hev)
  rw [resolverValue]
  have heq : (∑' k : ℕ, HSigmaScale.resolverCoeff μ (cosineCoeffs f) k
        * ShenWork.CosineSpectrum.cosineMode k x)
      = ∑' k : ℕ, cosineCoeffs f k * unitIntervalCosineMode k x
        / (p.μ + unitIntervalCosineEigenvalue k) := by
    refine tsum_congr (fun k => ?_)
    have hpμ : p.μ = μ := rfl
    rw [HSigmaScale.resolverCoeff, hpμ, unitIntervalCosineMode_eq_cosineMode]
    show cosineCoeffs f k / (μ + lam k) * ShenWork.CosineSpectrum.cosineMode k x = _
    show cosineCoeffs f k / (μ + lam k) * ShenWork.CosineSpectrum.cosineMode k x
      = cosineCoeffs f k * ShenWork.CosineSpectrum.cosineMode k x
        / (μ + unitIntervalCosineEigenvalue k)
    rw [show unitIntervalCosineEigenvalue k = lam k from rfl]; ring
  rw [heq]; exact hge

/-- **Closed-interval positivity (generic μ).**  Continuity extends interior
positivity to `[0,1]` (`{x | 0 ≤ R x}` closed, contains `(0,1)`, hence `[0,1]`). -/
theorem resolverValue_nonneg_Icc {μ : ℝ} (hμ : 0 < μ) {f : ℝ → ℝ}
    (hf_cont : Continuous f) (hf_nonneg : ∀ y, 0 ≤ f y)
    (hfsq : Summable fun k : ℕ => (cosineCoeffs f k) ^ 2)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ resolverValue μ (cosineCoeffs f) x := by
  have hcont := resolverValue_continuous hμ hfsq
  have hsub : Set.Ioo (0:ℝ) 1 ⊆ {x : ℝ | 0 ≤ resolverValue μ (cosineCoeffs f) x} :=
    fun y hy => resolverValue_nonneg_interior hμ hf_cont hf_nonneg hfsq hy
  have hIcc : Set.Icc (0:ℝ) 1 ⊆ {x : ℝ | 0 ≤ resolverValue μ (cosineCoeffs f) x} := by
    rw [← closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]
    exact (isClosed_le continuous_const hcont).closure_subset_iff.mpr hsub
  exact hIcc hx

/-- The resolver value is even in `x` (the cosine basis is even). -/
theorem resolverValue_even (μ : ℝ) (g : ℕ → ℝ) (x : ℝ) :
    resolverValue μ g (-x) = resolverValue μ g x := by
  unfold resolverValue
  refine tsum_congr (fun k => ?_)
  unfold ShenWork.CosineSpectrum.cosineMode
  rw [show (k : ℝ) * Real.pi * (-x) = -((k : ℝ) * Real.pi * x) by ring, Real.cos_neg]

/-- The resolver value has period `2` in `x`. -/
theorem resolverValue_add_two (μ : ℝ) (g : ℕ → ℝ) (x : ℝ) :
    resolverValue μ g (x + 2) = resolverValue μ g x := by
  unfold resolverValue
  refine tsum_congr (fun k => ?_)
  unfold ShenWork.CosineSpectrum.cosineMode
  rw [show (k : ℝ) * Real.pi * (x + 2)
      = (k : ℝ) * Real.pi * x + (k : ℤ) * (2 * Real.pi) by push_cast; ring,
    Real.cos_add_int_mul_two_pi]

/-- Period `2 * n` (integer multiples). -/
theorem resolverValue_add_int_two (μ : ℝ) (g : ℕ → ℝ) (x : ℝ) (n : ℤ) :
    resolverValue μ g (x + 2 * n) = resolverValue μ g x := by
  unfold resolverValue
  refine tsum_congr (fun k => ?_)
  unfold ShenWork.CosineSpectrum.cosineMode
  rw [show (k : ℝ) * Real.pi * (x + 2 * (n : ℝ))
      = (k : ℝ) * Real.pi * x + (((k : ℤ) * n : ℤ) : ℝ) * (2 * Real.pi) by
        push_cast; ring,
    Real.cos_add_int_mul_two_pi]

/-- **`hvnn` — Neumann-resolver positivity for ALL real `x` (generic μ).**
Reduce `x` mod 2 into `[0,2)`, fold by evenness/period into `[0,1]`. -/
theorem resolverValue_nonneg {μ : ℝ} (hμ : 0 < μ) {f : ℝ → ℝ}
    (hf_cont : Continuous f) (hf_nonneg : ∀ y, 0 ≤ f y)
    (hfsq : Summable fun k : ℕ => (cosineCoeffs f k) ^ 2)
    (x : ℝ) : 0 ≤ resolverValue μ (cosineCoeffs f) x := by
  set n : ℤ := ⌊x / 2⌋ with hn
  set y : ℝ := x - 2 * n with hy
  have hxy : x = y + 2 * n := by rw [hy]; ring
  have hy0 : 0 ≤ y := by
    have := Int.floor_le (x / 2); rw [hy]; nlinarith [this]
  have hy2 : y < 2 := by
    have := Int.lt_floor_add_one (x / 2); rw [hy]; nlinarith [this]
  rw [hxy, resolverValue_add_int_two]
  rcases le_or_gt y 1 with h1 | h1
  · exact resolverValue_nonneg_Icc hμ hf_cont hf_nonneg hfsq ⟨hy0, h1⟩
  · -- `y ∈ (1,2)`: fold by evenness + period 2 to `2 − y ∈ (0,1)`.
    have hfold : resolverValue μ (cosineCoeffs f) y
        = resolverValue μ (cosineCoeffs f) (2 - y) := by
      have h := resolverValue_even μ (cosineCoeffs f) y
      have h2 := resolverValue_add_two μ (cosineCoeffs f) (-y)
      rw [resolverValue_even] at h2
      rw [← h2]; ring_nf
    rw [hfold]
    exact resolverValue_nonneg_Icc hμ hf_cont hf_nonneg hfsq
      ⟨by linarith, by linarith⟩

/-! ## The `hvnn` PRODUCER for the interval-domain slice. -/

open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)
open ShenWork.Paper2.ChiNegCloseBaseSeed (memHSigma_zero_of_continuousOn)

/-- The clamp `ℝ → [0,1]`. -/
def clip : ℝ → intervalDomainPoint := fun x =>
  ⟨max 0 (min x 1), le_max_left 0 _, max_le (by norm_num) (min_le_right x 1)⟩

theorem clip_continuous : Continuous clip :=
  Continuous.subtype_mk (continuous_const.max (continuous_id.min continuous_const)) _

theorem clip_eq_lift_on_Icc (g : intervalDomainPoint → ℝ) {x : ℝ}
    (hx : x ∈ Set.Icc (0:ℝ) 1) : (g ∘ clip) x = intervalDomainLift g x := by
  have he : max 0 (min x 1) = x := by rw [min_eq_left hx.2, max_eq_right hx.1]
  simp only [Function.comp, clip, intervalDomainLift, dif_pos hx]
  exact congrArg g (Subtype.ext he)

/-- **`hvnn` for one interval slice.**  Given a slice `g : intervalDomainPoint → ℝ`
that is continuous and `≥ 0` (on the domain), the Neumann resolver of its lift is
`≥ 0` at every real `x`.  Uses the globally-continuous clip extension `g ∘ clip`. -/
theorem slice_hvnn {μ : ℝ} (hμ : 0 < μ) {g : intervalDomainPoint → ℝ}
    (hg_cont : Continuous g) (hg_nonneg : ∀ z, 0 ≤ g z) (x : ℝ) :
    0 ≤ resolverValue μ (cosineCoeffs (intervalDomainLift g)) x := by
  set cs : ℝ → ℝ := g ∘ clip with hcs
  have hcs_cont : Continuous cs := hg_cont.comp clip_continuous
  have hcs_nonneg : ∀ y, 0 ≤ cs y := fun y => hg_nonneg (clip y)
  have hagree : Set.EqOn (intervalDomainLift g) cs (Set.Icc (0:ℝ) 1) :=
    fun y hy => (clip_eq_lift_on_Icc g hy).symm
  have hcoeff : cosineCoeffs (intervalDomainLift g) = cosineCoeffs cs :=
    funext (fun k => cosineCoeffs_congr_on_Icc hagree k)
  have hfsq : Summable fun k : ℕ => (cosineCoeffs cs k) ^ 2 := by
    have hmem := memHSigma_zero_of_continuousOn (g := cs) hcs_cont.continuousOn
    rw [HSigmaScale.memHSigma_zero] at hmem
    exact hmem
  rw [hcoeff]
  exact resolverValue_nonneg hμ hcs_cont hcs_nonneg hfsq x

/-- **The `hvnn` field of `CarrySeam` — DISCHARGED.**  Exactly the carried
`hvnn` shape `∀ τ ∈ Icc 0 t, ∀ x, 0 ≤ resolverValue μ (cosineCoeffs (lift (u τ))) x`,
produced from per-slice continuity + nonnegativity of the conjugate solution `u`.
No longer an independent carried obligation: it reduces to (continuity + ≥0) of the
slices, both of which are carried mild facts threaded through `meanReach_H1_conjugate`. -/
theorem carrySeam_hvnn {μ t : ℝ} (hμ : 0 < μ)
    {u : ℝ → intervalDomainPoint → ℝ}
    (hu_cont : ∀ τ ∈ Set.Icc (0:ℝ) t, Continuous (u τ))
    (hu_nonneg : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ z, 0 ≤ u τ z) :
    ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ x,
      0 ≤ resolverValue μ (cosineCoeffs (intervalDomainLift (u τ))) x :=
  fun τ hτ x => slice_hvnn hμ (hu_cont τ hτ) (hu_nonneg τ hτ) x

end ShenWork.Paper2.IntervalChiNegMemHSigmaOne

namespace ShenWork.Paper2.IntervalChiNegMemHSigmaOne
#print axioms resolverValue_nonneg
#print axioms slice_hvnn
#print axioms carrySeam_hvnn
end ShenWork.Paper2.IntervalChiNegMemHSigmaOne
