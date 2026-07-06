import ShenWork.Paper2.IntervalChiNegH1InitialDerivativeRHS
import ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars

/-!
# Physical H¹ RHS strict/initial route

This file connects the physical H¹ RHS scalar triple to the route-C
strict-positive-time/zero-start split.  The new route asks for strict component
continuity away from `0` plus a near-zero L¹ majorant for the assembled physical
RHS; it does not require zero-start component continuity.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer
open ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer
open ShenWork.Paper2.IntervalChiNegH1DerivativeIntegrability
open ShenWork.Paper2.IntervalChiNegH1SupBoundDIProducer
open ShenWork.Paper2.IntervalChiNegH1Bridge
open ShenWork.Paper2.IntervalChiNegH1StrictRHSIntegrability
open ShenWork.Paper2.IntervalChiNegH1InitialDerivativeProducer
open ShenWork.Paper2.IntervalChiNegH1InitialDerivativeRHS
open ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1PhysicalInitialRHS

/-- Strict-positive-time component continuity plus a zero-start RHS majorant
gives the existing full explicit-RHS integrability package. -/
theorem H1IdentityRHSIntegrableBefore_of_componentsStrictBefore_initialMajorant
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hStrict : H1IdentityRHSComponentsContinuousStrictBefore p u T
      taxisX uvxx reactX)
    (hMaj : H1IdentityRHSInitialWindowMajorantBefore p u T
      taxisX uvxx reactX) :
    H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX :=
  H1IdentityRHSIntegrableBefore_of_componentsStrictBefore_initialWindow
    hId hStrict
    (H1IdentityRHSInitialWindowIntegrableBefore_of_majorant hMaj)

/-- Pointwise identity, square-root bounds, strict-positive-time component
continuity, and a zero-start RHS majorant give the combined sqrt/RHS package. -/
theorem
    H1SupBoundSqrtRHSIntegrableBefore_of_identity_sqrtBounds_componentsStrict_initialMajorant
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hb : H1SqrtTermBoundsBefore p u T V₁ V₂ M L
      taxisX uvxx reactX)
    (hStrict : H1IdentityRHSComponentsContinuousStrictBefore p u T
      taxisX uvxx reactX)
    (hMaj : H1IdentityRHSInitialWindowMajorantBefore p u T
      taxisX uvxx reactX) :
    H1SupBoundSqrtRHSIntegrableBefore p u T V₁ V₂ M L
      taxisX uvxx reactX :=
  H1SupBoundSqrtRHSIntegrableBefore_of_identity_sqrtBounds_RHSInt
    hId hb
    (H1IdentityRHSIntegrableBefore_of_componentsStrictBefore_initialMajorant
      hId hStrict hMaj).rhs_intervalIntegrable

/-- Strict-positive-time component continuity for the concrete physical scalar
triple. -/
structure H1PhysicalRHSComponentsContinuousStrictBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T : ℝ) : Prop where
  components : H1IdentityRHSComponentsContinuousStrictBefore p u T
    (H1PhysicalTaxisX p u v)
    (H1PhysicalUvxxX p u v)
    (H1PhysicalReactX p u)

/-- Near-zero L¹ majorant for the assembled concrete physical H¹ RHS. -/
structure H1PhysicalRHSInitialWindowMajorantBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T : ℝ) : Prop where
  majorant : H1IdentityRHSInitialWindowMajorantBefore p u T
    (H1PhysicalTaxisX p u v)
    (H1PhysicalUvxxX p u v)
    (H1PhysicalReactX p u)

/-- Local zero-window majorant for the assembled concrete physical H¹ RHS. -/
def H1PhysicalRHSZeroWindowMajorantBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T : ℝ) : Prop :=
  H1IdentityRHSZeroWindowMajorantBefore p u T
    (H1PhysicalTaxisX p u v)
    (H1PhysicalUvxxX p u v)
    (H1PhysicalReactX p u)

/-- Spatial square profile for the taxis non-lap factor. -/
def H1PhysicalTaxisPartSq (p : CM2Params)
    (u v : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, (H1PhysicalChemTaxisPart p u v τ x) ^ 2

/-- Spatial square profile for the `uvxx`/denominator non-lap factor. -/
def H1PhysicalUvxxPartSq (p : CM2Params)
    (u v : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, (H1PhysicalChemUvxxPart p u v τ x) ^ 2

/-- Spatial square profile for the reaction non-lap factor. -/
def H1PhysicalReactPartSq (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, (H1PhysicalLogisticReactionPart p u τ x) ^ 2

/-- Additive local scalar majorants for the four physical pieces in the
assembled H¹ RHS, all on one zero-window `(0, δ]`. -/
def H1PhysicalRHSAdditiveScalarZeroMajorantsBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T : ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ ∧ δ < T ∧
    ∃ Glap Gtaxis Guvxx Greact : ℝ → ℝ,
      IntervalIntegrable Glap volume (0 : ℝ) δ ∧
      IntervalIntegrable Gtaxis volume (0 : ℝ) δ ∧
      IntervalIntegrable Guvxx volume (0 : ℝ) δ ∧
      IntervalIntegrable Greact volume (0 : ℝ) δ ∧
      AEStronglyMeasurable
        (H1IdentityRHSValue p u
          (H1PhysicalTaxisX p u v)
          (H1PhysicalUvxxX p u v)
          (H1PhysicalReactX p u))
        (volume.restrict (Set.Ioc (0 : ℝ) δ)) ∧
      (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
        ‖lapL2sq u r‖ ≤ ‖Glap r‖) ∧
      (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
        ‖H1PhysicalTaxisX p u v r‖ ≤ ‖Gtaxis r‖) ∧
      (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
        ‖H1PhysicalUvxxX p u v r‖ ≤ ‖Guvxx r‖) ∧
      (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
        ‖H1PhysicalReactX p u r‖ ≤ ‖Greact r‖)

/-- Source-friendly version of the additive local scalar majorants where the
majorizing functions are known to be nonnegative a.e. on the zero window. -/
def H1PhysicalRHSAdditiveNonnegScalarZeroMajorantsBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T : ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ ∧ δ < T ∧
    ∃ Glap Gtaxis Guvxx Greact : ℝ → ℝ,
      IntervalIntegrable Glap volume (0 : ℝ) δ ∧
      IntervalIntegrable Gtaxis volume (0 : ℝ) δ ∧
      IntervalIntegrable Guvxx volume (0 : ℝ) δ ∧
      IntervalIntegrable Greact volume (0 : ℝ) δ ∧
      AEStronglyMeasurable
        (H1IdentityRHSValue p u
          (H1PhysicalTaxisX p u v)
          (H1PhysicalUvxxX p u v)
          (H1PhysicalReactX p u))
        (volume.restrict (Set.Ioc (0 : ℝ) δ)) ∧
      (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ), 0 ≤ Glap r) ∧
      (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ), 0 ≤ Gtaxis r) ∧
      (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ), 0 ≤ Guvxx r) ∧
      (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ), 0 ≤ Greact r) ∧
      (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
        ‖lapL2sq u r‖ ≤ Glap r) ∧
      (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
        ‖H1PhysicalTaxisX p u v r‖ ≤ Gtaxis r) ∧
      (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
        ‖H1PhysicalUvxxX p u v r‖ ≤ Guvxx r) ∧
      (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
        ‖H1PhysicalReactX p u r‖ ≤ Greact r)

/-- Young-type local scalar majorants for the physical pieces.  The lap
majorant is shared by the three product scalar bounds, while the remaining
nonnegative functions are the source-facing component-square contributions. -/
def H1PhysicalRHSYoungScalarZeroMajorantsBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T : ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ ∧ δ < T ∧
    ∃ Glap Gtaxis Guvxx Greact : ℝ → ℝ,
      IntervalIntegrable Glap volume (0 : ℝ) δ ∧
      IntervalIntegrable Gtaxis volume (0 : ℝ) δ ∧
      IntervalIntegrable Guvxx volume (0 : ℝ) δ ∧
      IntervalIntegrable Greact volume (0 : ℝ) δ ∧
      AEStronglyMeasurable
        (H1IdentityRHSValue p u
          (H1PhysicalTaxisX p u v)
          (H1PhysicalUvxxX p u v)
          (H1PhysicalReactX p u))
        (volume.restrict (Set.Ioc (0 : ℝ) δ)) ∧
      (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ), 0 ≤ Glap r) ∧
      (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ), 0 ≤ Gtaxis r) ∧
      (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ), 0 ≤ Guvxx r) ∧
      (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ), 0 ≤ Greact r) ∧
      (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
        ‖lapL2sq u r‖ ≤ Glap r) ∧
      (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
        ‖H1PhysicalTaxisX p u v r‖
          ≤ ((1 : ℝ) / 2) * Glap r + Gtaxis r) ∧
      (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
        ‖H1PhysicalUvxxX p u v r‖
          ≤ ((1 : ℝ) / 2) * Glap r + Guvxx r) ∧
      (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
        ‖H1PhysicalReactX p u r‖
          ≤ ((1 : ℝ) / 2) * Glap r + Greact r)

/-- Nonnegative additive local scalar majorants produce the norm-majorant
interface used by the route. -/
theorem H1PhysicalRHSAdditiveScalarZeroMajorantsBefore_of_nonneg
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (h : H1PhysicalRHSAdditiveNonnegScalarZeroMajorantsBefore p u v T) :
    H1PhysicalRHSAdditiveScalarZeroMajorantsBefore p u v T := by
  rcases h with
    ⟨δ, hδ_pos, hδ_before, Glap, Gtaxis, Guvxx, Greact,
      hGlap_int, hGtaxis_int, hGuvxx_int, hGreact_int, hRHS_meas,
      hGlap_nonneg, hGtaxis_nonneg, hGuvxx_nonneg, hGreact_nonneg,
      hLap_bound, hTaxis_bound, hUvxx_bound, hReact_bound⟩
  refine
    ⟨δ, hδ_pos, hδ_before, Glap, Gtaxis, Guvxx, Greact,
      hGlap_int, hGtaxis_int, hGuvxx_int, hGreact_int, hRHS_meas,
      ?_, ?_, ?_, ?_⟩
  · filter_upwards [hGlap_nonneg, hLap_bound] with r hnonneg hbound
    rwa [Real.norm_of_nonneg hnonneg]
  · filter_upwards [hGtaxis_nonneg, hTaxis_bound] with r hnonneg hbound
    rwa [Real.norm_of_nonneg hnonneg]
  · filter_upwards [hGuvxx_nonneg, hUvxx_bound] with r hnonneg hbound
    rwa [Real.norm_of_nonneg hnonneg]
  · filter_upwards [hGreact_nonneg, hReact_bound] with r hnonneg hbound
    rwa [Real.norm_of_nonneg hnonneg]

/-- Young-type product scalar bounds produce the nonnegative additive local
scalar majorants expected by the zero-window route. -/
theorem H1PhysicalRHSAdditiveNonnegScalarZeroMajorantsBefore_of_young
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (h : H1PhysicalRHSYoungScalarZeroMajorantsBefore p u v T) :
    H1PhysicalRHSAdditiveNonnegScalarZeroMajorantsBefore p u v T := by
  rcases h with
    ⟨δ, hδ_pos, hδ_before, Glap, Gtaxis, Guvxx, Greact,
      hGlap_int, hGtaxis_int, hGuvxx_int, hGreact_int, hRHS_meas,
      hGlap_nonneg, hGtaxis_nonneg, hGuvxx_nonneg, hGreact_nonneg,
      hLap_bound, hTaxis_bound, hUvxx_bound, hReact_bound⟩
  refine
    ⟨δ, hδ_pos, hδ_before, Glap,
      (fun r => ((1 : ℝ) / 2) * Glap r + Gtaxis r),
      (fun r => ((1 : ℝ) / 2) * Glap r + Guvxx r),
      (fun r => ((1 : ℝ) / 2) * Glap r + Greact r),
      hGlap_int, ?_, ?_, ?_, hRHS_meas,
      hGlap_nonneg, ?_, ?_, ?_, hLap_bound,
      hTaxis_bound, hUvxx_bound, hReact_bound⟩
  · exact (hGlap_int.const_mul ((1 : ℝ) / 2)).add hGtaxis_int
  · exact (hGlap_int.const_mul ((1 : ℝ) / 2)).add hGuvxx_int
  · exact (hGlap_int.const_mul ((1 : ℝ) / 2)).add hGreact_int
  · filter_upwards [hGlap_nonneg, hGtaxis_nonneg] with r hGlap hGtaxis
    exact add_nonneg
      (mul_nonneg (by norm_num : 0 ≤ ((1 : ℝ) / 2)) hGlap)
      hGtaxis
  · filter_upwards [hGlap_nonneg, hGuvxx_nonneg] with r hGlap hGuvxx
    exact add_nonneg
      (mul_nonneg (by norm_num : 0 ≤ ((1 : ℝ) / 2)) hGlap)
      hGuvxx
  · filter_upwards [hGlap_nonneg, hGreact_nonneg] with r hGlap hGreact
    exact add_nonneg
      (mul_nonneg (by norm_num : 0 ≤ ((1 : ℝ) / 2)) hGlap)
      hGreact

/-- Component-square zero-window data for the Task93 Young-style interface.
The three Young fields are local scalar-product estimates; the remaining data
are explicit square-profile integrability and assembled-RHS measurability on
one common zero window. -/
def H1PhysicalRHSComponentSquareZeroDataBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T : ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ ∧ δ < T ∧
    AEStronglyMeasurable
      (H1IdentityRHSValue p u
        (H1PhysicalTaxisX p u v)
        (H1PhysicalUvxxX p u v)
        (H1PhysicalReactX p u))
      (volume.restrict (Set.Ioc (0 : ℝ) δ)) ∧
    IntervalIntegrable (lapL2sq u) volume (0 : ℝ) δ ∧
    IntervalIntegrable (H1PhysicalTaxisPartSq p u v) volume (0 : ℝ) δ ∧
    IntervalIntegrable (H1PhysicalUvxxPartSq p u v) volume (0 : ℝ) δ ∧
    IntervalIntegrable (H1PhysicalReactPartSq p u) volume (0 : ℝ) δ ∧
    (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
      ‖H1PhysicalTaxisX p u v r‖
        ≤ ((1 : ℝ) / 2) * lapL2sq u r
          + ((1 : ℝ) / 2) * H1PhysicalTaxisPartSq p u v r) ∧
    (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
      ‖H1PhysicalUvxxX p u v r‖
        ≤ ((1 : ℝ) / 2) * lapL2sq u r
          + ((1 : ℝ) / 2) * H1PhysicalUvxxPartSq p u v r) ∧
    (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
      ‖H1PhysicalReactX p u r‖
        ≤ ((1 : ℝ) / 2) * lapL2sq u r
          + ((1 : ℝ) / 2) * H1PhysicalReactPartSq p u r)

/-- Component-square zero-window data lower to the Task93 Young-style
zero-window scalar majorants. -/
theorem H1PhysicalRHSYoungScalarZeroMajorantsBefore_of_componentSquareZeroData
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (h : H1PhysicalRHSComponentSquareZeroDataBefore p u v T) :
    H1PhysicalRHSYoungScalarZeroMajorantsBefore p u v T := by
  rcases h with
    ⟨δ, hδ_pos, hδ_before, hRHS_meas,
      hLap_int, hTaxisSq_int, hUvxxSq_int, hReactSq_int,
      hTaxis_young, hUvxx_young, hReact_young⟩
  refine
    ⟨δ, hδ_pos, hδ_before,
      lapL2sq u,
      (fun r => ((1 : ℝ) / 2) * H1PhysicalTaxisPartSq p u v r),
      (fun r => ((1 : ℝ) / 2) * H1PhysicalUvxxPartSq p u v r),
      (fun r => ((1 : ℝ) / 2) * H1PhysicalReactPartSq p u r),
      hLap_int,
      hTaxisSq_int.const_mul ((1 : ℝ) / 2),
      hUvxxSq_int.const_mul ((1 : ℝ) / 2),
      hReactSq_int.const_mul ((1 : ℝ) / 2),
      hRHS_meas, ?_, ?_, ?_, ?_, ?_,
      hTaxis_young, hUvxx_young, hReact_young⟩
  · exact ae_of_all _ fun r => lapL2sq_nonneg u r
  · exact ae_of_all _ fun r =>
      mul_nonneg (by norm_num : 0 ≤ ((1 : ℝ) / 2)) (by
        unfold H1PhysicalTaxisPartSq
        exact intervalIntegral.integral_nonneg
          (show (0 : ℝ) ≤ 1 by norm_num)
          (fun x _hx => sq_nonneg (H1PhysicalChemTaxisPart p u v r x)))
  · exact ae_of_all _ fun r =>
      mul_nonneg (by norm_num : 0 ≤ ((1 : ℝ) / 2)) (by
        unfold H1PhysicalUvxxPartSq
        exact intervalIntegral.integral_nonneg
          (show (0 : ℝ) ≤ 1 by norm_num)
          (fun x _hx => sq_nonneg (H1PhysicalChemUvxxPart p u v r x)))
  · exact ae_of_all _ fun r =>
      mul_nonneg (by norm_num : 0 ≤ ((1 : ℝ) / 2)) (by
        unfold H1PhysicalReactPartSq
        exact intervalIntegral.integral_nonneg
          (show (0 : ℝ) ≤ 1 by norm_num)
          (fun x _hx => sq_nonneg (H1PhysicalLogisticReactionPart p u r x)))
  · exact ae_of_all _ fun r => by
      rw [Real.norm_of_nonneg (lapL2sq_nonneg u r)]

/-- Additive local scalar majorants assemble to a local zero-window majorant
for the concrete physical H¹ RHS. -/
theorem H1PhysicalRHSZeroWindowMajorantBefore_of_additiveScalarMajorants
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (h : H1PhysicalRHSAdditiveScalarZeroMajorantsBefore p u v T) :
    H1PhysicalRHSZeroWindowMajorantBefore p u v T := by
  rcases h with
    ⟨δ, hδ_pos, hδ_before, Glap, Gtaxis, Guvxx, Greact,
      hGlap_int, hGtaxis_int, hGuvxx_int, hGreact_int,
      hRHS_meas, hLap_bound, hTaxis_bound, hUvxx_bound, hReact_bound⟩
  refine
    ⟨δ, hδ_pos, hδ_before,
      (fun r =>
        ‖Glap r‖ + ‖(-p.χ₀)‖ * ‖Gtaxis r‖ +
          ‖(-p.χ₀)‖ * ‖Guvxx r‖ + ‖Greact r‖),
      ?_, hRHS_meas, ?_⟩
  · exact
      (((hGlap_int.norm.add
        (hGtaxis_int.norm.const_mul ‖(-p.χ₀)‖)).add
        (hGuvxx_int.norm.const_mul ‖(-p.χ₀)‖)).add
        hGreact_int.norm)
  · filter_upwards [hLap_bound, hTaxis_bound, hUvxx_bound, hReact_bound]
      with r hLap hTaxis hUvxx hReact
    have hTaxis_scaled :
        ‖(-p.χ₀)‖ * ‖H1PhysicalTaxisX p u v r‖
          ≤ ‖(-p.χ₀)‖ * ‖Gtaxis r‖ :=
      mul_le_mul_of_nonneg_left hTaxis (norm_nonneg (-p.χ₀))
    have hUvxx_scaled :
        ‖(-p.χ₀)‖ * ‖H1PhysicalUvxxX p u v r‖
          ≤ ‖(-p.χ₀)‖ * ‖Guvxx r‖ :=
      mul_le_mul_of_nonneg_left hUvxx (norm_nonneg (-p.χ₀))
    have hterms :
        ‖lapL2sq u r‖
            + ‖(-p.χ₀)‖ * ‖H1PhysicalTaxisX p u v r‖
            + ‖(-p.χ₀)‖ * ‖H1PhysicalUvxxX p u v r‖
            + ‖H1PhysicalReactX p u r‖
          ≤ ‖Glap r‖ + ‖(-p.χ₀)‖ * ‖Gtaxis r‖
            + ‖(-p.χ₀)‖ * ‖Guvxx r‖ + ‖Greact r‖ :=
      add_le_add (add_le_add (add_le_add hLap hTaxis_scaled) hUvxx_scaled) hReact
    have hG_nonneg :
        0 ≤ ‖Glap r‖ + ‖(-p.χ₀)‖ * ‖Gtaxis r‖
          + ‖(-p.χ₀)‖ * ‖Guvxx r‖ + ‖Greact r‖ :=
      add_nonneg
        (add_nonneg
          (add_nonneg (norm_nonneg (Glap r))
            (mul_nonneg (norm_nonneg (-p.χ₀)) (norm_nonneg (Gtaxis r))))
          (mul_nonneg (norm_nonneg (-p.χ₀)) (norm_nonneg (Guvxx r))))
        (norm_nonneg (Greact r))
    exact
      (H1IdentityRHSValue_norm_le_scalar_sum p u
          (H1PhysicalTaxisX p u v)
          (H1PhysicalUvxxX p u v)
          (H1PhysicalReactX p u) r).trans
        (by rwa [Real.norm_of_nonneg hG_nonneg])

/-- Route package for the concrete physical scalar triple with strict
positive-time component continuity and a zero-start assembled-RHS majorant. -/
structure H1PhysicalRHSStrictInitialRouteBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T V₁ V₂ M L : ℝ) : Prop where
  identity : H1PhysicalRHSIdentityBefore p u v T
  bounds : H1PhysicalRHSSqrtBoundsBefore p u v T V₁ V₂ M L
  componentsStrict : H1PhysicalRHSComponentsContinuousStrictBefore p u v T
  initialMajorant : H1PhysicalRHSInitialWindowMajorantBefore p u v T

/-- The physical initial majorant gives the generic assembled-RHS initial
majorant for the same concrete scalar triple. -/
theorem H1IdentityRHSInitialWindowMajorantBefore_of_physicalInitialMajorant
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (h : H1PhysicalRHSInitialWindowMajorantBefore p u v T) :
    H1IdentityRHSInitialWindowMajorantBefore p u T
      (H1PhysicalTaxisX p u v)
      (H1PhysicalUvxxX p u v)
      (H1PhysicalReactX p u) :=
  h.majorant

/-- A physical zero-window majorant and strict positive-time physical component
continuity give the global physical initial-window majorant. -/
theorem H1PhysicalRHSInitialWindowMajorantBefore_of_zeroWindow_strict
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hStrict : H1PhysicalRHSComponentsContinuousStrictBefore p u v T)
    (hZero : H1PhysicalRHSZeroWindowMajorantBefore p u v T) :
    H1PhysicalRHSInitialWindowMajorantBefore p u v T :=
  ⟨H1IdentityRHSInitialWindowMajorantBefore_of_zeroWindow_strict
    hStrict.components hZero⟩

/-- Additive local scalar majorants plus strict positive-time physical component
continuity give the global physical initial-window majorant. -/
theorem H1PhysicalRHSInitialWindowMajorantBefore_of_additiveScalar_zeroWindow_strict
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hStrict : H1PhysicalRHSComponentsContinuousStrictBefore p u v T)
    (hAdd : H1PhysicalRHSAdditiveScalarZeroMajorantsBefore p u v T) :
    H1PhysicalRHSInitialWindowMajorantBefore p u v T :=
  H1PhysicalRHSInitialWindowMajorantBefore_of_zeroWindow_strict
    hStrict
    (H1PhysicalRHSZeroWindowMajorantBefore_of_additiveScalarMajorants hAdd)

/-- Physical identity, square-root bounds, strict component continuity, and
additive local scalar zero-window majorants assemble the strict/initial route. -/
theorem H1PhysicalRHSStrictInitialRouteBefore_of_additiveScalar_zeroWindow
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hId : H1PhysicalRHSIdentityBefore p u v T)
    (hBounds : H1PhysicalRHSSqrtBoundsBefore p u v T V₁ V₂ M L)
    (hStrict : H1PhysicalRHSComponentsContinuousStrictBefore p u v T)
    (hAdd : H1PhysicalRHSAdditiveScalarZeroMajorantsBefore p u v T) :
    H1PhysicalRHSStrictInitialRouteBefore p u v T V₁ V₂ M L :=
  ⟨hId, hBounds, hStrict,
    H1PhysicalRHSInitialWindowMajorantBefore_of_additiveScalar_zeroWindow_strict
      hStrict hAdd⟩

/-- Nonnegative additive local scalar zero-window majorants assemble the
strict/initial route after rewriting the nonnegative bounds as norm bounds. -/
theorem H1PhysicalRHSStrictInitialRouteBefore_of_nonnegScalar_zeroWindow
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hId : H1PhysicalRHSIdentityBefore p u v T)
    (hBounds : H1PhysicalRHSSqrtBoundsBefore p u v T V₁ V₂ M L)
    (hStrict : H1PhysicalRHSComponentsContinuousStrictBefore p u v T)
    (hNonneg :
      H1PhysicalRHSAdditiveNonnegScalarZeroMajorantsBefore p u v T) :
    H1PhysicalRHSStrictInitialRouteBefore p u v T V₁ V₂ M L :=
  H1PhysicalRHSStrictInitialRouteBefore_of_additiveScalar_zeroWindow
    hId hBounds hStrict
    (H1PhysicalRHSAdditiveScalarZeroMajorantsBefore_of_nonneg hNonneg)

/-- Young-type local scalar zero-window majorants assemble the strict/initial
route through the nonnegative scalar-majorant adapter. -/
theorem H1PhysicalRHSStrictInitialRouteBefore_of_youngScalar_zeroWindow
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hId : H1PhysicalRHSIdentityBefore p u v T)
    (hBounds : H1PhysicalRHSSqrtBoundsBefore p u v T V₁ V₂ M L)
    (hStrict : H1PhysicalRHSComponentsContinuousStrictBefore p u v T)
    (hYoung :
      H1PhysicalRHSYoungScalarZeroMajorantsBefore p u v T) :
    H1PhysicalRHSStrictInitialRouteBefore p u v T V₁ V₂ M L :=
  H1PhysicalRHSStrictInitialRouteBefore_of_nonnegScalar_zeroWindow
    hId hBounds hStrict
    (H1PhysicalRHSAdditiveNonnegScalarZeroMajorantsBefore_of_young hYoung)

/-- The physical initial majorant gives initial-window integrability of the
assembled physical H¹ RHS. -/
theorem H1IdentityRHSInitialWindowIntegrableBefore_of_physicalInitialMajorant
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (h : H1PhysicalRHSInitialWindowMajorantBefore p u v T) :
    H1IdentityRHSInitialWindowIntegrableBefore p u T
      (H1PhysicalTaxisX p u v)
      (H1PhysicalUvxxX p u v)
      (H1PhysicalReactX p u) :=
  H1IdentityRHSInitialWindowIntegrableBefore_of_majorant h.majorant

/-- A physical identity plus a physical initial RHS majorant gives the scalar
zero-start H¹ derivative-integrability input. -/
theorem H1EnergyDerivativeInitialWindowIntegrableBefore_of_physicalInitialMajorant
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hId : H1PhysicalRHSIdentityBefore p u v T)
    (hMaj : H1PhysicalRHSInitialWindowMajorantBefore p u v T) :
    H1EnergyDerivativeInitialWindowIntegrableBefore u T :=
  H1EnergyDerivativeInitialWindowIntegrableBefore_of_identityRHSMajorant
    hId.identity hMaj.majorant

/-- Physical identity, strict component continuity, and a physical zero-window
majorant give the scalar zero-start H¹ derivative-integrability input. -/
theorem H1EnergyDerivativeInitialWindowIntegrableBefore_of_physicalZeroWindowMajorant
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hId : H1PhysicalRHSIdentityBefore p u v T)
    (hStrict : H1PhysicalRHSComponentsContinuousStrictBefore p u v T)
    (hZero : H1PhysicalRHSZeroWindowMajorantBefore p u v T) :
    H1EnergyDerivativeInitialWindowIntegrableBefore u T :=
  H1EnergyDerivativeInitialWindowIntegrableBefore_of_physicalInitialMajorant
    hId
    (H1PhysicalRHSInitialWindowMajorantBefore_of_zeroWindow_strict
      hStrict hZero)

/-- The strict/initial physical route supplies full explicit-RHS integrability
for the concrete scalar triple. -/
theorem H1IdentityRHSIntegrableBefore_of_physicalStrictInitialRoute
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (h : H1PhysicalRHSStrictInitialRouteBefore p u v T V₁ V₂ M L) :
    H1IdentityRHSIntegrableBefore p u T
      (H1PhysicalTaxisX p u v)
      (H1PhysicalUvxxX p u v)
      (H1PhysicalReactX p u) :=
  H1IdentityRHSIntegrableBefore_of_componentsStrictBefore_initialMajorant
    h.identity.identity
    h.componentsStrict.components
    h.initialMajorant.majorant

/-- The strict/initial physical route supplies the square-root DI package. -/
theorem H1SupBoundSqrtDIDataBefore_of_physicalStrictInitialRoute
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (h : H1PhysicalRHSStrictInitialRouteBefore p u v T V₁ V₂ M L) :
    H1SupBoundSqrtDIDataBefore p u T V₁ V₂ M L
      (H1PhysicalTaxisX p u v)
      (H1PhysicalUvxxX p u v)
      (H1PhysicalReactX p u) :=
  H1SupBoundSqrtDIDataBefore_of_identity_and_sqrtBounds
    h.identity.identity
    h.bounds.bounds

/-- The strict/initial physical route supplies the combined sqrt/RHS package
without requiring zero-start component continuity. -/
theorem H1SupBoundSqrtRHSIntegrableBefore_of_physicalStrictInitialRoute
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (h : H1PhysicalRHSStrictInitialRouteBefore p u v T V₁ V₂ M L) :
    H1SupBoundSqrtRHSIntegrableBefore p u T V₁ V₂ M L
      (H1PhysicalTaxisX p u v)
      (H1PhysicalUvxxX p u v)
      (H1PhysicalReactX p u) :=
  H1SupBoundSqrtRHSIntegrableBefore_of_identity_sqrtBounds_componentsStrict_initialMajorant
    h.identity.identity
    h.bounds.bounds
    h.componentsStrict.components
    h.initialMajorant.majorant

/-- Bounded-before wrapper from the concrete physical strict/initial route and
the remaining scalar regularity inputs. -/
theorem intervalDomain_boundedBefore_of_physicalStrictInitialRoute_before
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hcont0 : ContinuousWithinAt (H1energy u) (Set.Ici (0 : ℝ)) 0)
    {V₁ V₂ M L : ℝ}
    (h : H1PhysicalRHSStrictInitialRouteBefore params u v T V₁ V₂ M L) :
    IsPaper2BoundedBefore intervalDomain T u :=
  intervalDomain_boundedBefore_of_H1supBoundSqrtRHS_before
    hbounded ha hu₀ hT hsol htrace hfrontier
    hUxxL1 hcont0
    (H1SupBoundSqrtRHSIntegrableBefore_of_physicalStrictInitialRoute h)

#print axioms
  H1IdentityRHSIntegrableBefore_of_componentsStrictBefore_initialMajorant
#print axioms
  H1SupBoundSqrtRHSIntegrableBefore_of_identity_sqrtBounds_componentsStrict_initialMajorant
#print axioms
  H1IdentityRHSInitialWindowMajorantBefore_of_physicalInitialMajorant
#print axioms
  H1IdentityRHSInitialWindowIntegrableBefore_of_physicalInitialMajorant
#print axioms
  H1EnergyDerivativeInitialWindowIntegrableBefore_of_physicalInitialMajorant
#print axioms H1PhysicalRHSZeroWindowMajorantBefore_of_additiveScalarMajorants
#print axioms H1PhysicalRHSInitialWindowMajorantBefore_of_zeroWindow_strict
#print axioms
  H1PhysicalRHSInitialWindowMajorantBefore_of_additiveScalar_zeroWindow_strict
#print axioms H1PhysicalRHSAdditiveScalarZeroMajorantsBefore_of_nonneg
#print axioms H1PhysicalRHSAdditiveNonnegScalarZeroMajorantsBefore_of_young
#print axioms
  H1PhysicalRHSYoungScalarZeroMajorantsBefore_of_componentSquareZeroData
#print axioms H1PhysicalRHSStrictInitialRouteBefore_of_additiveScalar_zeroWindow
#print axioms H1PhysicalRHSStrictInitialRouteBefore_of_nonnegScalar_zeroWindow
#print axioms H1PhysicalRHSStrictInitialRouteBefore_of_youngScalar_zeroWindow
#print axioms
  H1EnergyDerivativeInitialWindowIntegrableBefore_of_physicalZeroWindowMajorant
#print axioms H1IdentityRHSIntegrableBefore_of_physicalStrictInitialRoute
#print axioms H1SupBoundSqrtDIDataBefore_of_physicalStrictInitialRoute
#print axioms H1SupBoundSqrtRHSIntegrableBefore_of_physicalStrictInitialRoute
#print axioms intervalDomain_boundedBefore_of_physicalStrictInitialRoute_before

end ShenWork.Paper2.IntervalChiNegH1PhysicalInitialRHS
