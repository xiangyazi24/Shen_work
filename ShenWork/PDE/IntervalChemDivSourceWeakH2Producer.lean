import ShenWork.PDE.IntervalCoupledSourceTimeC1
import ShenWork.Paper2.IntervalWeakH2SmoothRepresentative
import ShenWork.Paper2.IntervalEvenDerivParity
import ShenWork.Paper2.IntervalResolverHighRegularity

/-!
# Weak-`H²_N` witness for the chemotaxis-divergence source (HSpectral crux gap)

`coupledChemDivSource_timeC1_of_factorJointC2Inputs`
(`IntervalChemDivFluxJointC2Producer.lean:190`) carries
`hH2 : ∀ s, 0 ≤ s → IntervalWeakH2Neumann (coupledChemDivSourceLift p u s)` as a
hypothesis that is never produced; producing it makes the `O(k⁻²)` source-coefficient
decay follow free from `intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound`.

## Route (parity) and what is reused

The source `coupledChemDivSourceLift p u s = ∂ₓ(u·∂ₓR·(1+R)^{-β})` is the chemotaxis
divergence.  Under the Neumann even reflection: `u, R` are doubly-even ⇒ `∂ₓR` is
doubly-odd ⇒ the flux `Q = u·∂ₓR·(1+R)^{-β}` is doubly-**odd** ⇒ the divergence source
`∂ₓQ` is doubly-**even**.  Hence the committed adapter
`intervalWeakH2Neumann_of_doublyEven_agree` (which builds the full weak-`H²_N`
certificate — including the cosine-Laplacian weak-IBP identity — for FREE from a
doubly-even `C²` representative agreeing with the target on `[0,1]`) is exactly the
right tool: no pointwise `Q''(0)=0` is needed at the weak level, the reflection supplies
the endpoint data.

This file wires that adapter to the divergence source.  The remaining input — a
per-slice doubly-even `C²` representative of the source on `[0,1]` — is CARRIED as a
named hypothesis: it is discharged by taking the doubly-odd `C³` reflection of the flux
`Q` (from the flux-`C³` regularity, `IntervalTruncatedFluxC3Bounds` + the joint-`C²`
flux inputs) and differentiating once (`deriv` of doubly-odd is doubly-even, cf.
`DoublyEven.deriv_deriv`).  No weak-form/IBP reasoning remains after this reduction.
-/

namespace ShenWork.PDE.IntervalChemDivSourceWeakH2Producer

open ShenWork.IntervalDomain
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.Paper2.WeakH2SmoothRepresentative
open ShenWork.Paper2.SourceRepresentative
open ShenWork.Paper2.EvenDerivParity
open ShenWork.Paper2.IntervalResolverHighRegularity
open ShenWork.PDE.IntervalMildSourceDecayHelper

/-! ## Sub-lemma #1: the resolver gradient `∂ₓR` is odd about the endpoints

From the global `C⁴` doubly-even resolver representative `intervalResolverLiftR`
(`_even`, `_reflect_one`, `_contDiff_four`) and the parity base
`deriv_odd_of_evenAboutZero/One`, its derivative `∂ₓR = deriv (intervalResolverLiftR)`
is odd about `x=0` and `x=1`, and hence vanishes at both endpoints.  This is the
parity anchor of the flux/source reflection chain. -/

/-- `∂ₓR` is **odd about `0`**: `∂ₓR(-x) = -∂ₓR(x)`. -/
theorem intervalResolverLiftR_deriv_odd_about_zero
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hcd : ContDiff ℝ 1 (intervalResolverLiftR p u)) (x : ℝ) :
    deriv (intervalResolverLiftR p u) (-x) = - deriv (intervalResolverLiftR p u) x := by
  have hder : ∀ y, HasDerivAt (intervalResolverLiftR p u)
      (deriv (intervalResolverLiftR p u) y) y :=
    fun y => (hcd.differentiable (by norm_num)).differentiableAt.hasDerivAt
  exact deriv_odd_of_evenAboutZero (intervalResolverLiftR_even p u) hder x

/-- `∂ₓR` is **odd about `1`**: `∂ₓR(2-x) = -∂ₓR(x)`. -/
theorem intervalResolverLiftR_deriv_odd_about_one
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hcd : ContDiff ℝ 1 (intervalResolverLiftR p u)) (x : ℝ) :
    deriv (intervalResolverLiftR p u) (2 - x) = - deriv (intervalResolverLiftR p u) x := by
  have hder : ∀ y, HasDerivAt (intervalResolverLiftR p u)
      (deriv (intervalResolverLiftR p u) y) y :=
    fun y => (hcd.differentiable (by norm_num)).differentiableAt.hasDerivAt
  exact deriv_odd_of_evenAboutOne (intervalResolverLiftR_reflect_one p u) hder x

/-- `∂ₓR(0) = 0` (Neumann endpoint, from odd-about-`0`). -/
theorem intervalResolverLiftR_deriv_zero_at_zero
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hcd : ContDiff ℝ 1 (intervalResolverLiftR p u)) :
    deriv (intervalResolverLiftR p u) 0 = 0 := by
  have hder : ∀ y, HasDerivAt (intervalResolverLiftR p u)
      (deriv (intervalResolverLiftR p u) y) y :=
    fun y => (hcd.differentiable (by norm_num)).differentiableAt.hasDerivAt
  exact deriv_zero_at_zero_of_evenAboutZero (intervalResolverLiftR_even p u) hder

/-- `∂ₓR(1) = 0` (Neumann endpoint, from odd-about-`1`). -/
theorem intervalResolverLiftR_deriv_zero_at_one
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hcd : ContDiff ℝ 1 (intervalResolverLiftR p u)) :
    deriv (intervalResolverLiftR p u) 1 = 0 := by
  have hder : ∀ y, HasDerivAt (intervalResolverLiftR p u)
      (deriv (intervalResolverLiftR p u) y) y :=
    fun y => (hcd.differentiable (by norm_num)).differentiableAt.hasDerivAt
  exact deriv_zero_at_one_of_evenAboutOne (intervalResolverLiftR_reflect_one p u) hder

/-- **Per-slice weak-`H²_N` witness for the chemotaxis-divergence source.**
From a doubly-even `C²` representative `G` agreeing with the source on `[0,1]`, the
committed `doublyEven` adapter produces the full `IntervalWeakH2Neumann` certificate
(second derivative, `L¹` bound, and the Neumann cosine weak-Laplacian identity) — the
reflection supplies the endpoint data, so no pointwise second-derivative boundary
condition is required. -/
noncomputable def coupledChemDivSourceLift_weakH2Neumann_of_evenRepresentative
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s : ℝ}
    (G : ℝ → ℝ) (hG : ContDiff ℝ 2 G) (hDE : DoublyEven G)
    (hagree : ∀ x ∈ Set.Icc (0 : ℝ) 1, G x = coupledChemDivSourceLift p u s x) :
    IntervalWeakH2Neumann (coupledChemDivSourceLift p u s) :=
  intervalWeakH2Neumann_of_doublyEven_agree hG hDE hagree

/-- **The `hH2` supplier** consumed by
`coupledChemDivSource_timeC1_of_factorJointC2Inputs`: per-slice weak-`H²_N` for the
chemotaxis-divergence source, from per-slice doubly-even `C²` representatives
(`G s` for slice `s`). -/
noncomputable def coupledChemDivSource_weakH2Neumann_of_evenRepresentatives
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (G : ℝ → ℝ → ℝ)
    (hG : ∀ s, 0 ≤ s → ContDiff ℝ 2 (G s))
    (hDE : ∀ s, 0 ≤ s → DoublyEven (G s))
    (hagree : ∀ s, 0 ≤ s → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      G s x = coupledChemDivSourceLift p u s x) :
    ∀ s, 0 ≤ s → IntervalWeakH2Neumann (coupledChemDivSourceLift p u s) :=
  fun s hs =>
    coupledChemDivSourceLift_weakH2Neumann_of_evenRepresentative
      (G s) (hG s hs) (hDE s hs) (hagree s hs)

end ShenWork.PDE.IntervalChemDivSourceWeakH2Producer
