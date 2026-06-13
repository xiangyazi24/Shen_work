/-
# Physical producer of `PhysicalResolverJointC2Data` from the floor

This file closes the FAC resolver-`C²` lane **physically**, under the committed
floor `u ≥ δ > 0`.  It produces the bounded-weight joint-`C²` data structure
`PhysicalResolverJointC2Data p u Bt` (the input to
`coupledChemDivFluxFactorJointC2Inputs_of_physical`) from the *source* side: the
three-time-order `C²`-in-`x` source `ℓ¹` data, with the **constant elliptic
weight** `wₖ = 1/(μ+λ_k)` factored out.

## The clean factorization

The resolver time-coefficient is, by the coefficient-form resolvent identity,
exactly a *constant scalar multiple* of the source cosine coefficient in time:

  `resolverTimeCoeff p u k t = wₖ · srcTimeCoeff p u k t`,

where `srcTimeCoeff p u k t = (â_k(u t)).re = (intervalNeumannResolverSourceCoeff
p (u t) k).re` is the `k`-th cosine coefficient of the chemotaxis source
`ν·u(t)^γ` at time `t`, and `wₖ = 1/(μ+λ_k)` is a `t`-independent real constant.

Because `wₖ` is constant in `t`, *all* time-regularity and *all* time-derivative
bounds transfer with a single factor `wₖ`:

  `∂ₜⁱ (resolverTimeCoeff p u k) = wₖ · ∂ₜⁱ (srcTimeCoeff p u k)`,
  `‖∂ₜⁱ (resolverTimeCoeff p u k) t‖ = wₖ · ‖∂ₜⁱ (srcTimeCoeff p u k) t‖`.

So `ContDiff ℝ 2`-in-`t` and the three-order bounds `Bt i k = wₖ · Es i k` follow
mechanically from the **source-side** data:

* `srcTimeCoeff p u k` is `ContDiff ℝ 2` in `t` — this is the physical content
  "under the floor `u ≥ δ > 0`, `u^γ` is `ContDiff` in `t`, hence so is each cosine
  coefficient" (`Real.rpow` smooth away from `0`; the committed iterate time-`C²`
  regularity).
* `‖∂ₜⁱ srcTimeCoeff p u k t‖ ≤ Es i k` with the three weighted envelopes `Es`
  carrying the spatial `C²`-in-`x` decay `(kπ)⁻²` at each time-order `i = 0,1,2`.

These are exactly the honest "3-time-order `C²`-in-`x` source `ℓ¹` data" of the
chemotaxis source, packaged as `PhysicalSourceTimeC2`.  The summability of the
bounded-weight joint majorants of `Bt = w·Es` is then a hypothesis on the
source envelopes — strictly the source `ℓ¹` data, NO `λ²`/`λ³` eigen-cube ladder
and NO `DuhamelSourceTimeC2Coeff`.
-/
import ShenWork.PDE.IntervalResolverJointC2PhysicalConcrete

open Filter Topology Set
open ShenWork.PDE (intervalNeumannResolverWeight intervalNeumannResolverCoeff
  intervalNeumannResolverSourceCoeff)
open ShenWork.IntervalResolverJointC2Physical
  (boundedWeightJointMajorant boundedWeightJointGradMajorant)
open ShenWork.IntervalResolverJointC2PhysicalConcrete (resolverTimeCoeff
  PhysicalResolverJointC2Data)
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.Paper3 (unitIntervalNeumannSpectrum)

noncomputable section

namespace ShenWork.IntervalPhysicalResolverDataConcrete

/-- The `k`-th **source** cosine coefficient of the chemotaxis source `ν·u(t)^γ`
in time: `srcTimeCoeff p u k t = (â_k(u t)).re`.  Under the floor `u ≥ δ > 0`
this is the `t`-regular real scalar that drives the resolver coefficient. -/
def srcTimeCoeff (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) :
    ℕ → ℝ → ℝ :=
  fun k t => (intervalNeumannResolverSourceCoeff p (u t) k).re

/-- **The constant-weight factorization.**  The resolver time-coefficient is the
source time-coefficient scaled by the `t`-independent elliptic weight `wₖ`:
`resolverTimeCoeff p u k t = wₖ · srcTimeCoeff p u k t`.  Read off from the
coefficient-form resolvent identity `v̂_k = (μ+λ_k)⁻¹ · â_k` with all data real. -/
theorem resolverTimeCoeff_eq_weight_smul
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (k : ℕ) (t : ℝ) :
    resolverTimeCoeff p u k t =
      intervalNeumannResolverWeight p k * srcTimeCoeff p u k t := by
  -- From the committed coefficient-form elliptic identity `(μ+λ_k)·v̂_k = â_k`,
  -- taking real parts: `(μ+λ_k)·(v̂_k).re = (â_k).re`, with `μ+λ_k > 0`.
  have hpos : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue k :=
    ShenWork.PDE.intervalNeumannResolver_denom_pos p k
  have hcast : ((p.μ : ℂ) + (unitIntervalNeumannSpectrum.eigenvalue k : ℂ)) =
      (((p.μ + unitIntervalNeumannSpectrum.eigenvalue k : ℝ)) : ℂ) := by
    push_cast; ring
  have hk := congrArg Complex.re
    (ShenWork.PDE.intervalNeumannResolverCoeff_elliptic p (u t) k)
  rw [hcast, Complex.re_ofReal_mul] at hk
  -- `hk : (μ+λ_k) * (v̂_k).re = (â_k).re`.
  rw [resolverTimeCoeff, srcTimeCoeff, intervalNeumannResolverWeight, hk.symm,
    one_div, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]

/-- `resolverTimeCoeff p u k = wₖ • srcTimeCoeff p u k` as functions of `t`
(real `smul` is multiplication).  This is the form consumed by the const-`smul`
`iteratedFDeriv` lemma. -/
theorem resolverTimeCoeff_eq_smul
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (k : ℕ) :
    resolverTimeCoeff p u k =
      (intervalNeumannResolverWeight p k) • srcTimeCoeff p u k := by
  funext t
  rw [Pi.smul_apply, smul_eq_mul]
  exact resolverTimeCoeff_eq_weight_smul p u k t

/-- **The honest physical source-time `C²`/`ℓ¹` data** for the chemotaxis source.
The *source* cosine coefficient family is `ContDiff ℝ 2` in `t` (under the floor
`u ≥ δ > 0`, `u^γ` is `ℝ.rpow`-smooth in `t`), with three-time-order envelopes
`Es i k ≥ ‖∂ₜⁱ srcTimeCoeff k‖` whose **weighted** joint majorants
(weight `wₖ = 1/(μ+λ_k)`) are summable for orders `0,1,2`.  This is exactly the
"`C²`-in-`x` source at 3 time-orders" data — the spatial decay `(kπ)⁻²` lives in
`Es`, the elliptic weight in `wₖ`.  NO eigen-cube ladder. -/
structure PhysicalSourceTimeC2
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Es : ℕ → ℕ → ℝ) : Prop where
  /-- Each source coefficient is `C²` in time (`u^γ` smooth under the floor). -/
  src_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p u k)
  /-- Three-time-order source coefficient bounds. -/
  src_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
    ‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ ≤ Es i k
  /-- The weighted **value** joint majorant `Bt = w·Es` is summable. -/
  value_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointMajorant
      (fun i k => intervalNeumannResolverWeight p k * Es i k) m)
  /-- The weighted **gradient** joint majorant `Bt = w·Es` is summable. -/
  grad_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointGradMajorant
      (fun i k => intervalNeumannResolverWeight p k * Es i k) m)

/-- `wₖ ≥ 0`. -/
theorem resolverWeight_nonneg (p : CM2Params) (k : ℕ) :
    0 ≤ intervalNeumannResolverWeight p k := by
  unfold intervalNeumannResolverWeight
  have := ShenWork.PDE.intervalNeumannResolver_denom_pos p k
  positivity

/-- The const-`smul` `iteratedFDeriv` transfer: `∂ₜⁱ (w·src) = w·∂ₜⁱ src`. -/
theorem resolverTimeCoeff_iteratedFDeriv_eq
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (hsrcC2 : ∀ k, ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p u k))
    (i k : ℕ) (t : ℝ) (hi : i ≤ 2) :
    iteratedFDeriv ℝ i (resolverTimeCoeff p u k) t =
      (intervalNeumannResolverWeight p k) •
        iteratedFDeriv ℝ i (srcTimeCoeff p u k) t := by
  rw [resolverTimeCoeff_eq_smul]
  have hcd : ContDiffAt ℝ (i : ℕ∞) (srcTimeCoeff p u k) t :=
    ((hsrcC2 k).of_le (by exact_mod_cast hi)).contDiffAt
  exact iteratedFDeriv_const_smul_apply hcd

/-- The three-time-order bound transfer: `‖∂ₜⁱ resolverTimeCoeff k‖ ≤ wₖ·Es i k`. -/
theorem resolverTimeCoeff_bound
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) {Es : ℕ → ℕ → ℝ}
    (hsrcC2 : ∀ k, ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p u k))
    (hsrcB : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
      ‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ ≤ Es i k)
    (i k : ℕ) (t : ℝ) (hi : i ≤ 2) :
    ‖iteratedFDeriv ℝ i (resolverTimeCoeff p u k) t‖ ≤
      intervalNeumannResolverWeight p k * Es i k := by
  rw [resolverTimeCoeff_iteratedFDeriv_eq p u hsrcC2 i k t hi]
  rw [norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (resolverWeight_nonneg p k)]
  exact mul_le_mul_of_nonneg_left (hsrcB i k t hi) (resolverWeight_nonneg p k)

/-- **The physical producer.**  Under the floor (encoded as the honest source-side
`PhysicalSourceTimeC2` data: `u^γ`-driven `ContDiff`-in-`t` source coefficients +
3-time-order `C²`-in-`x` envelopes), the resolver bounded-weight joint-`C²` data
`PhysicalResolverJointC2Data` holds with `Bt i k = wₖ · Es i k`.  This bypasses
the eigen-cube ladder: the only spatial growth is the committed `λ_n` in the
`valueCosWeight`/`gradCosWeight`, cancelled by the elliptic weight folded into
`Bt`. -/
theorem physicalResolverJointC2Data_of_floor
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Es : ℕ → ℕ → ℝ}
    (H : PhysicalSourceTimeC2 p u Es) :
    PhysicalResolverJointC2Data p u
      (fun i k => intervalNeumannResolverWeight p k * Es i k) where
  coeff_contDiff k := by
    have : resolverTimeCoeff p u k =
        fun t => intervalNeumannResolverWeight p k * srcTimeCoeff p u k t := by
      funext t; exact resolverTimeCoeff_eq_weight_smul p u k t
    rw [this]
    exact contDiff_const.mul (H.src_contDiff k)
  coeff_bound i k t hi :=
    resolverTimeCoeff_bound p u H.src_contDiff H.src_bound i k t hi
  value_summable := H.value_summable
  grad_summable := H.grad_summable

/-- **End-to-end physical FAC producer.**  Feeding the floor-driven resolver data
into the committed FAC connector
`coupledChemDivFluxFactorJointC2Inputs_of_physical` discharges the two resolver-
`C²` fields (`hv_c2`, `hgradv_c2`) of the FAC inputs **physically** — from the
3-time-order source data `PhysicalSourceTimeC2` (constant elliptic weight folded
in) — bypassing the `λ²`/`λ³` eigen-cube ladder and `DuhamelSourceTimeC2Coeff`.
The non-resolver FAC fields remain the committed slab hypothesis `other`. -/
theorem coupledChemDivFluxFactorJointC2Inputs_of_floor
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Es : ℕ → ℕ → ℝ}
    (H : PhysicalSourceTimeC2 p u Es)
    (other : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
      (∀ᶠ s in 𝓝 τ,
        ContinuousOn
          (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivSourceLift
            p u s) (Icc (0 : ℝ) 1)) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
        ContDiffAt ℝ 2
          (fun q : ℝ × ℝ =>
            ShenWork.IntervalDomain.intervalDomainLift (u q.1) q.2) (s, x)) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
        0 < 1 + ShenWork.IntervalDomain.intervalDomainLift
          (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemicalConcentration
            p u s) x) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
        (fun y : ℝ =>
            ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivFluxTimeDerivativeLift
              p u s y) =ᶠ[𝓝 x]
          (fun y : ℝ => fderiv ℝ
            (Function.uncurry
              (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivFluxLift p u))
            (s, y) (1, 0))) ∧
      ContinuousOn
        (Function.uncurry
          (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivTimeDerivativeLift
            p u))
        (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)) :
    ShenWork.IntervalCoupledRegularityBootstrap.CoupledChemDivFluxFactorJointC2Inputs
      p u :=
  ShenWork.IntervalResolverJointC2PhysicalConcrete.coupledChemDivFluxFactorJointC2Inputs_of_physical
    (physicalResolverJointC2Data_of_floor H) other

end ShenWork.IntervalPhysicalResolverDataConcrete
