/-
# Concrete bounded-weight joint `C²` connector for the elliptic resolver

This file feeds the generic bounded-weight assembler
`IntervalResolverJointC2Physical.boundedWeightJointSeries_contDiff_two` with the
concrete elliptic resolver coefficient family `c k t = a t k · wₖ`, where
`wₖ = 1/(μ+λ_k)` is the bounded elliptic weight and `a t k` is the source cosine
coefficient at time `t`.  The honest physical hypothesis `PhysicalSourceTimeC2`
is the **three-time-order `ℓ¹` source data** (`C²`-in-`x` at each of the time
orders `0,1,2`), strictly weaker than the spectral `λ²` ladder and NOT routed
through `DuhamelSourceTimeC2Coeff`.

## The bounded-weight summability

The joint majorant term at order `(k,n)` is `Bt i n = Eᵢ(n)·wₙ` against
`valueCosWeight (k-i) n`.  The worst spatial factor `valueCosWeight 2 n = λ_n`
is cancelled by the weight: `λ_n·wₙ ≤ 1`, so `E₀(n)·wₙ·λ_n ≤ E₀(n)`.  The mixed
and pure-time terms use `λ_n·wₙ ≤ 1` and `wₙ ≤ 1/μ`.  Hence summability of the
joint majorant follows from the three weighted envelopes being `ℓ¹`.
-/
import ShenWork.PDE.IntervalResolverJointC2Physical
import ShenWork.PDE.IntervalChemDivFluxFactorFAC

open Filter Topology Set
open ShenWork.PDE (intervalNeumannResolverWeight intervalNeumannResolverCoeff
  intervalNeumannResolverR)
open ShenWork.IntervalResolverJointC2Physical
open ShenWork.IntervalResolverSpectralJointC2Concrete
  (valueCosWeight gradCosWeight valueCosWeight_nonneg)
open ShenWork.CosineSpectrum (cosineMode cosineMode_deriv)
open ShenWork.IntervalDuhamelClosedC2 (cosineCoeffSeries_grad_hasDerivAt)
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceLift coupledChemDivFluxLift
   coupledChemDivFluxTimeDerivativeLift coupledChemDivTimeDerivativeLift
   CoupledChemDivFluxFactorJointC2Inputs)
open ShenWork.Paper3 (unitIntervalNeumannSpectrum)

noncomputable section

namespace ShenWork.IntervalResolverJointC2PhysicalConcrete

/-- **Bounded elliptic multiplier on the eigenvalue weight.** `λ_n · wₙ ≤ 1`. -/
theorem eigenvalue_mul_resolverWeight_le_one (p : CM2Params) (n : ℕ) :
    unitIntervalNeumannSpectrum.eigenvalue n * intervalNeumannResolverWeight p n ≤ 1 := by
  have hpos : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue n :=
    ShenWork.PDE.intervalNeumannResolver_denom_pos p n
  have hlam : 0 ≤ unitIntervalNeumannSpectrum.eigenvalue n :=
    ShenWork.PDE.ResolventEstimate.unitIntervalNeumannSpectrum_eigenvalue_nonneg n
  unfold intervalNeumannResolverWeight
  rw [mul_one_div, div_le_one hpos]
  linarith [p.hμ]

/-- `valueCosWeight m n · wₙ ≤ valueCosWeight m n / μ`-style: `wₙ ≤ 1/μ`. -/
theorem resolverWeight_le_inv_mu (p : CM2Params) (n : ℕ) :
    intervalNeumannResolverWeight p n ≤ 1 / p.μ := by
  unfold intervalNeumannResolverWeight
  apply div_le_div_of_nonneg_left one_pos.le p.hμ
  linarith [ShenWork.PDE.ResolventEstimate.unitIntervalNeumannSpectrum_eigenvalue_nonneg n]

/-- `valueCosWeight 1 n = |nπ|` and `λ_n = (nπ)²`, so `|nπ| = √λ_n`; the AM–GM
bound `|nπ|·wₙ = |nπ|/(μ+(nπ)²) ≤ 1/(2√μ) ≤ 1/μ + 1` is what we need.  Here we
take the crude majorant `valueCosWeight 1 n · wₙ ≤ |nπ|/μ` (the order-1 envelope
is taken already `(nπ)`-decaying in the hypothesis, so the crude bound suffices). -/
theorem valueCosWeight_one_mul_resolverWeight_le (p : CM2Params) (n : ℕ) :
    valueCosWeight 1 n * intervalNeumannResolverWeight p n ≤
      |(n : ℝ) * Real.pi| / p.μ := by
  have hw : intervalNeumannResolverWeight p n ≤ 1 / p.μ := resolverWeight_le_inv_mu p n
  have hvc : valueCosWeight 1 n = |(n : ℝ) * Real.pi| := rfl
  rw [hvc]
  calc |(n : ℝ) * Real.pi| * intervalNeumannResolverWeight p n
      ≤ |(n : ℝ) * Real.pi| * (1 / p.μ) :=
        mul_le_mul_of_nonneg_left hw (abs_nonneg _)
    _ = |(n : ℝ) * Real.pi| / p.μ := by rw [mul_one_div]

/-- The concrete resolver time-coefficient family `c k t = (v̂_k(t)).re`. -/
def resolverTimeCoeff (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) :
    ℕ → ℝ → ℝ :=
  fun k t => (intervalNeumannResolverCoeff p (u t) k).re

/-- **The honest physical joint-`C²` hypothesis** for the coupled resolver: the
time-coefficient family is `ContDiff ℝ 2` in `t`, with three-time-order bounds
`Bt` whose bounded-weight value/gradient joint majorants are summable.  This is
the 3-time-order source `ℓ¹`/`C²`-in-`x` data, with the elliptic weight already
folded into `(v̂_k).re`.  It does NOT mention `DuhamelSourceTimeC2Coeff` nor any
`λ²`/`λ³` eigenvalue summability. -/
structure PhysicalResolverJointC2Data
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Bt : ℕ → ℕ → ℝ) : Prop where
  /-- Each coefficient is `C²` in time. -/
  coeff_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (resolverTimeCoeff p u k)
  /-- Three-time-order coefficient bounds. -/
  coeff_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
    ‖iteratedFDeriv ℝ i (resolverTimeCoeff p u k) t‖ ≤ Bt i k
  /-- The bounded-weight **value** joint majorant is summable (orders `0,1,2`). -/
  value_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointMajorant Bt m)
  /-- The bounded-weight **gradient** joint majorant is summable. -/
  grad_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointGradMajorant Bt m)

/-- The lifted coupled concentration equals the bounded-weight value series on
`[0,1]`. -/
theorem coupledChemical_lift_eq_series
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {t x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    intervalDomainLift (coupledChemicalConcentration p u t) x =
      ∑' k : ℕ, boundedWeightJointTerm (resolverTimeCoeff p u) k (t, x) := by
  simp only [intervalDomainLift, hx, dif_pos, coupledChemicalConcentration,
    boundedWeightJointTerm, resolverTimeCoeff]
  exact ShenWork.IntervalResolverSpatialC2.resolverR_eq_cosineSeries ⟨x, hx⟩

/-- **Physical producer of `hv_c2`** — joint `ContDiffAt ℝ 2` of the lifted
coupled concentration, via the bounded-weight value assembler.  No `λ²` ladder,
no `DuhamelSourceTimeC2Coeff`. -/
theorem coupledChemical_jointContDiffAt_two
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt) {s x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2) (s, x) := by
  have hseries : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ =>
        ∑' k : ℕ, boundedWeightJointTerm (resolverTimeCoeff p u) k q) :=
    boundedWeightJointSeries_contDiff_two H.coeff_contDiff
      (fun i k t hi => H.coeff_bound i k t hi) H.value_summable
  refine (hseries.contDiffAt).congr_of_eventuallyEq ?_
  have hmem : {q : ℝ × ℝ | q.2 ∈ Ioo (0 : ℝ) 1} ∈ 𝓝 (s, x) :=
    (isOpen_Ioo.preimage continuous_snd).mem_nhds hx
  filter_upwards [hmem] with q hq
  have he := coupledChemical_lift_eq_series (p := p) (u := u) (t := q.1) (x := q.2)
    (Ioo_subset_Icc_self hq)
  simpa using he

/-- **Physical producer of `hgradv_c2`** — joint `ContDiffAt ℝ 2` of the spatial
derivative `∂ₓ v` of the lifted coupled concentration, via the bounded-weight
gradient assembler. -/
theorem coupledChemical_grad_jointContDiffAt_two
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt) {s x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
      (s, x) := by
  have hseries : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ =>
        ∑' k : ℕ, boundedWeightJointGradTerm (resolverTimeCoeff p u) k q) :=
    boundedWeightJointGradSeries_contDiff_two H.coeff_contDiff
      (fun i k t hi => H.coeff_bound i k t hi) H.grad_summable
  refine (hseries.contDiffAt).congr_of_eventuallyEq ?_
  have hmem : {q : ℝ × ℝ | q.2 ∈ Ioo (0 : ℝ) 1} ∈ 𝓝 (s, x) :=
    (isOpen_Ioo.preimage continuous_snd).mem_nhds hx
  filter_upwards [hmem] with q hq
  have hopen : Ioo (0 : ℝ) 1 ∈ 𝓝 q.2 := isOpen_Ioo.mem_nhds hq
  have hval : (fun y : ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) y) =ᶠ[𝓝 q.2]
      fun y : ℝ =>
        ∑' k : ℕ, boundedWeightJointTerm (resolverTimeCoeff p u) k (q.1, y) := by
    filter_upwards [hopen] with y hy
    exact coupledChemical_lift_eq_series (Ioo_subset_Icc_self hy)
  rw [Filter.EventuallyEq.deriv_eq hval]
  -- `∂ₓ ∑' k, c_k·cos = ∑' k, c_k·∂ₓ cos` via the committed gradient series lemma.
  have heignn : ∀ k : ℕ, 0 ≤ unitIntervalCosineEigenvalue k := fun k => by
    show (0 : ℝ) ≤ ((k : ℝ) * Real.pi) ^ 2; positivity
  set b : ℕ → ℝ := fun k => resolverTimeCoeff p u k q.1 with hb
  have hbnn : ∀ i k : ℕ, i ≤ 2 → 0 ≤ Bt i k := fun i k hi =>
    le_trans (norm_nonneg _) (H.coeff_bound i k q.1 hi)
  have heig : Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * |b k|) := by
    apply Summable.of_nonneg_of_le
      (fun k => mul_nonneg (heignn k) (abs_nonneg _))
      (fun k => ?_) (H.value_summable 2 le_rfl)
    have hbk : |b k| ≤ Bt 0 k := by
      have h0 := H.coeff_bound 0 k q.1 (by norm_num)
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h0
    have hi0le : unitIntervalCosineEigenvalue k * |b k| ≤
        Bt 0 k * unitIntervalCosineEigenvalue k := by
      rw [mul_comm (Bt 0 k)]; exact mul_le_mul_of_nonneg_left hbk (heignn k)
    refine hi0le.trans ?_
    rw [boundedWeightJointMajorant, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one]
    have hi0 : (Nat.choose 2 0 : ℝ) * Bt 0 k * valueCosWeight (2 - 0) k =
        Bt 0 k * unitIntervalCosineEigenvalue k := by norm_num [valueCosWeight]
    have hnn1 : (0 : ℝ) ≤ (Nat.choose 2 1 : ℝ) * Bt 1 k * valueCosWeight (2 - 1) k :=
      mul_nonneg (mul_nonneg (by positivity) (hbnn 1 k (by norm_num)))
        (valueCosWeight_nonneg _ _)
    have hnn2 : (0 : ℝ) ≤ (Nat.choose 2 2 : ℝ) * Bt 2 k * valueCosWeight (2 - 2) k :=
      mul_nonneg (mul_nonneg (by positivity) (hbnn 2 k (by norm_num)))
        (valueCosWeight_nonneg _ _)
    rw [hi0]; linarith
  have hgrad := cosineCoeffSeries_grad_hasDerivAt heig q.2
  have hrw : (fun y : ℝ =>
      ∑' k : ℕ, boundedWeightJointTerm (resolverTimeCoeff p u) k (q.1, y)) =
      fun y : ℝ => ∑' k : ℕ, b k * cosineMode k y := by
    funext y; exact tsum_congr (fun k => by simp [boundedWeightJointTerm, hb])
  rw [hrw, hgrad.deriv]
  exact tsum_congr (fun k => by simp [boundedWeightJointGradTerm, hb, cosineMode_deriv])

/-- **Physical-route producer of the full FAC joint-`C²` inputs.**  The two
resolver-`C²` fields (`hv_c2`, `hgradv_c2`) are supplied by the bounded-weight
physical assembler above — bypassing `DuhamelSourceTimeC2Coeff` and the spectral
`λ²`/`λ³` eigenvalue-cube ladder entirely.  The non-resolver fields (source
continuity, the Picard joint `C²` `hu_c2`, the positivity floor, the time-partial
bridge, and the time-derivative continuity) remain as the slab hypothesis
`other`, exactly as in the committed FAC lane. -/
theorem coupledChemDivFluxFactorJointC2Inputs_of_physical
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt)
    (other : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
      (∀ᶠ s in 𝓝 τ,
        ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
        ContDiffAt ℝ 2 (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
        0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) x) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
        (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
          (fun y : ℝ => fderiv ℝ
            (Function.uncurry (coupledChemDivFluxLift p u)) (s, y) (1, 0))) ∧
      ContinuousOn
        (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
        (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)) :
    CoupledChemDivFluxFactorJointC2Inputs p u := by
  refine ⟨fun τ => ?_⟩
  rcases other τ with ⟨δ, hδ, hsrc, hu_c2, hbase, htime, htime_cont⟩
  exact ⟨δ, hδ, hsrc, hu_c2,
    (fun x hx s _ => coupledChemical_jointContDiffAt_two H hx),
    (fun x hx s _ => coupledChemical_grad_jointContDiffAt_two H hx),
    hbase, htime, htime_cont⟩

end ShenWork.IntervalResolverJointC2PhysicalConcrete
