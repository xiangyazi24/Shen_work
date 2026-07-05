import ShenWork.Paper2.IntervalChiNegH1InitialDerivativeFTC

/-!
# Initial-window H¹ derivative producers from assembled RHS data

This file records the non-circular direction from an independently produced
zero-start integrable H¹ identity RHS to the scalar derivative proxy.  It does
not use the full `H1IdentityRHSIntegrableBefore` package, bounded-before data,
or zero-start component continuity.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1DerivativeIntegrability
open ShenWork.Paper2.IntervalChiNegH1RHSIntegrabilityProducer
open ShenWork.Paper2.IntervalChiNegH1Bridge
open ShenWork.Paper2.IntervalChiNegH1StrictRHSIntegrability
open ShenWork.Paper2.IntervalChiNegH1InitialDerivativeProducer
open ShenWork.Paper2.IntervalChiNegH1InitialDerivativeFTC

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1InitialDerivativeRHS

/-- Near-zero L¹ majorant for a scalar function on all zero-start windows before
`T`.  This is the reusable scalar version used to assemble H¹ RHS majorants
term by term. -/
def H1ScalarInitialWindowMajorantBefore
    (T : ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ G : ℝ → ℝ,
    (∀ {b : ℝ}, 0 ≤ b → b < T →
      IntervalIntegrable G volume (0 : ℝ) b) ∧
    (∀ {b : ℝ}, 0 ≤ b → b < T →
      AEStronglyMeasurable f
        (volume.restrict (Set.Ioc (0 : ℝ) b))) ∧
    (∀ {b : ℝ}, 0 ≤ b → b < T →
      ∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) b),
        ‖f r‖ ≤ ‖G r‖)

/-- Scalar initial-window majorants are stable under negation. -/
theorem H1ScalarInitialWindowMajorantBefore.neg
    {T : ℝ} {f : ℝ → ℝ}
    (hf : H1ScalarInitialWindowMajorantBefore T f) :
    H1ScalarInitialWindowMajorantBefore T (fun r => -f r) := by
  rcases hf with ⟨G, hG_integrable, hf_meas, hf_bound⟩
  refine ⟨G, hG_integrable, ?_, ?_⟩
  · intro b hb0 hbT
    exact (hf_meas hb0 hbT).neg
  · intro b hb0 hbT
    filter_upwards [hf_bound hb0 hbT] with r hr
    simpa using hr

/-- Scalar initial-window majorants are stable under multiplication by a fixed
real coefficient. -/
theorem H1ScalarInitialWindowMajorantBefore.const_mul
    {T : ℝ} {f : ℝ → ℝ}
    (hf : H1ScalarInitialWindowMajorantBefore T f) (c : ℝ) :
    H1ScalarInitialWindowMajorantBefore T (fun r => c * f r) := by
  rcases hf with ⟨G, hG_integrable, hf_meas, hf_bound⟩
  refine ⟨fun r => ‖c‖ * ‖G r‖, ?_, ?_, ?_⟩
  · intro b hb0 hbT
    exact (hG_integrable hb0 hbT).norm.const_mul ‖c‖
  · intro b hb0 hbT
    exact (hf_meas hb0 hbT).const_mul c
  · intro b hb0 hbT
    filter_upwards [hf_bound hb0 hbT] with r hr
    have hscaled : ‖c‖ * ‖f r‖ ≤ ‖c‖ * ‖G r‖ :=
      mul_le_mul_of_nonneg_left hr (norm_nonneg c)
    have hnonneg : 0 ≤ ‖c‖ * ‖G r‖ :=
      mul_nonneg (norm_nonneg c) (norm_nonneg (G r))
    calc
      ‖c * f r‖ = ‖c‖ * ‖f r‖ := norm_mul c (f r)
      _ ≤ ‖c‖ * ‖G r‖ := hscaled
      _ = ‖‖c‖ * ‖G r‖‖ := (Real.norm_of_nonneg hnonneg).symm

/-- Scalar initial-window majorants are stable under addition. -/
theorem H1ScalarInitialWindowMajorantBefore.add
    {T : ℝ} {f g : ℝ → ℝ}
    (hf : H1ScalarInitialWindowMajorantBefore T f)
    (hg : H1ScalarInitialWindowMajorantBefore T g) :
    H1ScalarInitialWindowMajorantBefore T (fun r => f r + g r) := by
  rcases hf with ⟨F, hF_integrable, hf_meas, hf_bound⟩
  rcases hg with ⟨G, hG_integrable, hg_meas, hg_bound⟩
  refine ⟨fun r => ‖F r‖ + ‖G r‖, ?_, ?_, ?_⟩
  · intro b hb0 hbT
    exact (hF_integrable hb0 hbT).norm.add (hG_integrable hb0 hbT).norm
  · intro b hb0 hbT
    exact (hf_meas hb0 hbT).add (hg_meas hb0 hbT)
  · intro b hb0 hbT
    filter_upwards [hf_bound hb0 hbT, hg_bound hb0 hbT] with r hrF hrG
    have hsum :
        ‖f r + g r‖ ≤ ‖F r‖ + ‖G r‖ := by
      exact (norm_add_le (f r) (g r)).trans (add_le_add hrF hrG)
    have hnonneg : 0 ≤ ‖F r‖ + ‖G r‖ :=
      add_nonneg (norm_nonneg (F r)) (norm_nonneg (G r))
    rwa [Real.norm_of_nonneg hnonneg]

/-- Near-zero L¹ majorant for the assembled H¹ identity RHS.

This is weaker than zero-start component continuity: it only estimates the
already assembled scalar RHS on zero-start windows. -/
def H1IdentityRHSInitialWindowMajorantBefore
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ)
    (taxisX uvxx reactX : ℝ → ℝ) : Prop :=
  ∃ G : ℝ → ℝ,
    (∀ {b : ℝ}, 0 ≤ b → b < T →
      IntervalIntegrable G volume (0 : ℝ) b) ∧
    (∀ {b : ℝ}, 0 ≤ b → b < T →
      AEStronglyMeasurable
        (H1IdentityRHSValue p u taxisX uvxx reactX)
        (volume.restrict (Set.Ioc (0 : ℝ) b))) ∧
    (∀ {b : ℝ}, 0 ≤ b → b < T →
      ∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) b),
        ‖H1IdentityRHSValue p u taxisX uvxx reactX r‖ ≤ ‖G r‖)

/-- Repackage the reusable scalar majorant for the assembled H¹ RHS into the
route-specific RHS majorant predicate. -/
theorem H1IdentityRHSInitialWindowMajorantBefore_of_scalarMajorant
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (h : H1ScalarInitialWindowMajorantBefore T
      (H1IdentityRHSValue p u taxisX uvxx reactX)) :
    H1IdentityRHSInitialWindowMajorantBefore p u T
      taxisX uvxx reactX := by
  rcases h with ⟨G, hG_integrable, hRHS_meas, hRHS_bound⟩
  exact ⟨G, hG_integrable, hRHS_meas, hRHS_bound⟩

/-- Initial-window integrability of the assembled RHS gives a tautological
majorant by using the RHS itself as the majorizing function. -/
theorem H1IdentityRHSInitialWindowMajorantBefore_of_initialWindowIntegrable
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hInit : H1IdentityRHSInitialWindowIntegrableBefore p u T
      taxisX uvxx reactX) :
    H1IdentityRHSInitialWindowMajorantBefore p u T
      taxisX uvxx reactX := by
  refine ⟨H1IdentityRHSValue p u taxisX uvxx reactX, ?_, ?_, ?_⟩
  · intro b hb0 hbT
    exact hInit hb0 hbT
  · intro b hb0 hbT
    exact (hInit hb0 hbT).aestronglyMeasurable
  · intro b _hb0 _hbT
    exact ae_of_all _ fun _ => le_rfl

/-- A near-zero majorant for the assembled H¹ identity RHS gives the explicit
initial-window RHS integrability input. -/
theorem H1IdentityRHSInitialWindowIntegrableBefore_of_majorant
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hMaj : H1IdentityRHSInitialWindowMajorantBefore p u T
      taxisX uvxx reactX) :
    H1IdentityRHSInitialWindowIntegrableBefore p u T
      taxisX uvxx reactX := by
  rcases hMaj with ⟨G, hG_integrable, hRHS_meas, hRHS_bound⟩
  intro b hb0 hbT
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb0]
  rw [IntegrableOn]
  have hG :
      Integrable G (volume.restrict (Set.Ioc (0 : ℝ) b)) := by
    simpa [IntegrableOn] using
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hb0).mp
        (hG_integrable hb0 hbT)
  exact Integrable.mono' hG.norm
    (hRHS_meas hb0 hbT)
    (by simpa using hRHS_bound hb0 hbT)

/-- A genuinely local zero-endpoint majorant for the assembled H¹ identity RHS.
It asks for one positive window `(0, δ]`, not every zero-start window before
`T`. -/
def H1IdentityRHSZeroWindowMajorantBefore
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ)
    (taxisX uvxx reactX : ℝ → ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ ∧ δ < T ∧
    ∃ G : ℝ → ℝ,
      IntervalIntegrable G volume (0 : ℝ) δ ∧
      AEStronglyMeasurable
        (H1IdentityRHSValue p u taxisX uvxx reactX)
        (volume.restrict (Set.Ioc (0 : ℝ) δ)) ∧
      (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
        ‖H1IdentityRHSValue p u taxisX uvxx reactX r‖ ≤ ‖G r‖)

/-- A local zero-window majorant plus strict positive-time component continuity
gives initial-window RHS integrability on every zero-start window before `T`.
The local majorant handles `(0, δ]`; strict continuity handles `[δ,b]`. -/
theorem H1IdentityRHSInitialWindowIntegrableBefore_of_zeroWindow_strict
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hStrict : H1IdentityRHSComponentsContinuousStrictBefore p u T
      taxisX uvxx reactX)
    (hZero : H1IdentityRHSZeroWindowMajorantBefore p u T
      taxisX uvxx reactX) :
    H1IdentityRHSInitialWindowIntegrableBefore p u T
      taxisX uvxx reactX := by
  rcases hZero with
    ⟨δ, hδ_pos, hδ_before, G, hG_integrable, hRHS_meas, hRHS_bound⟩
  have hZeroInt_le :
      ∀ {b : ℝ}, 0 ≤ b → b ≤ δ →
        IntervalIntegrable
          (H1IdentityRHSValue p u taxisX uvxx reactX) volume
          (0 : ℝ) b := by
    intro b hb0 hbδ
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb0]
    rw [IntegrableOn]
    have hb_mem : b ∈ Set.uIcc (0 : ℝ) δ :=
      Set.mem_uIcc_of_le hb0 hbδ
    have hsub_uIcc : Set.uIcc (0 : ℝ) b ⊆ Set.uIcc (0 : ℝ) δ :=
      Set.uIcc_subset_uIcc Set.left_mem_uIcc hb_mem
    have hG_b :
        IntervalIntegrable G volume (0 : ℝ) b :=
      hG_integrable.mono_set hsub_uIcc
    have hG_int :
        Integrable G (volume.restrict (Set.Ioc (0 : ℝ) b)) := by
      simpa [IntegrableOn] using
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hb0).mp hG_b
    have hIoc_sub : Set.Ioc (0 : ℝ) b ⊆ Set.Ioc (0 : ℝ) δ :=
      Set.Ioc_subset_Ioc le_rfl hbδ
    have hMeas :
        AEStronglyMeasurable
          (H1IdentityRHSValue p u taxisX uvxx reactX)
          (volume.restrict (Set.Ioc (0 : ℝ) b)) :=
      hRHS_meas.mono_measure (Measure.restrict_mono hIoc_sub le_rfl)
    have hBound :
        ∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) b),
          ‖H1IdentityRHSValue p u taxisX uvxx reactX r‖ ≤ ‖G r‖ :=
      ae_restrict_of_ae_restrict_of_subset hIoc_sub hRHS_bound
    exact Integrable.mono' hG_int.norm hMeas hBound
  intro b hb0 hbT
  rcases le_or_gt b δ with hbδ | hδb
  · exact hZeroInt_le hb0 hbδ
  · have hZeroInt :
        IntervalIntegrable
          (H1IdentityRHSValue p u taxisX uvxx reactX) volume
          (0 : ℝ) δ :=
      hZeroInt_le hδ_pos.le le_rfl
    have hδb_le : δ ≤ b := le_of_lt hδb
    have hRHSCont :
        ContinuousOn
          (H1IdentityRHSValue p u taxisX uvxx reactX)
          (Set.Icc δ b) :=
      H1IdentityRHS_continuousOn_Icc_of_components
        (hStrict.lap_cont hδ_pos hδb_le hbT)
        (hStrict.taxis_cont hδ_pos hδb_le hbT)
        (hStrict.uvxx_cont hδ_pos hδb_le hbT)
        (hStrict.react_cont hδ_pos hδb_le hbT)
    exact hZeroInt.trans (hRHSCont.intervalIntegrable_of_Icc hδb_le)

/-- A local zero-window majorant plus strict positive-time component continuity
gives the global initial-window majorant expected by the route-C adapters. -/
theorem H1IdentityRHSInitialWindowMajorantBefore_of_zeroWindow_strict
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hStrict : H1IdentityRHSComponentsContinuousStrictBefore p u T
      taxisX uvxx reactX)
    (hZero : H1IdentityRHSZeroWindowMajorantBefore p u T
      taxisX uvxx reactX) :
    H1IdentityRHSInitialWindowMajorantBefore p u T
      taxisX uvxx reactX :=
  H1IdentityRHSInitialWindowMajorantBefore_of_initialWindowIntegrable
    (H1IdentityRHSInitialWindowIntegrableBefore_of_zeroWindow_strict
      hStrict hZero)

/-- Pure norm algebra for the assembled H¹ identity RHS. -/
theorem H1IdentityRHSValue_norm_le_scalar_sum
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (taxisX uvxx reactX : ℝ → ℝ) (r : ℝ) :
    ‖H1IdentityRHSValue p u taxisX uvxx reactX r‖
      ≤ ‖lapL2sq u r‖
        + ‖(-p.χ₀)‖ * ‖taxisX r‖
        + ‖(-p.χ₀)‖ * ‖uvxx r‖
        + ‖reactX r‖ := by
  unfold H1IdentityRHSValue
  let c : ℝ := -p.χ₀
  change
    ‖((-(lapL2sq u r) + c * taxisX r) + c * uvxx r) + reactX r‖
      ≤ ‖lapL2sq u r‖
        + ‖c‖ * ‖taxisX r‖
        + ‖c‖ * ‖uvxx r‖
        + ‖reactX r‖
  have h1 :
      ‖((-(lapL2sq u r) + c * taxisX r) + c * uvxx r) + reactX r‖
        ≤ ‖(-(lapL2sq u r) + c * taxisX r) + c * uvxx r‖ +
            ‖reactX r‖ :=
    norm_add_le _ _
  have h2 :
      ‖(-(lapL2sq u r) + c * taxisX r) + c * uvxx r‖
        ≤ ‖-(lapL2sq u r) + c * taxisX r‖ + ‖c * uvxx r‖ :=
    norm_add_le _ _
  have h3 :
      ‖-(lapL2sq u r) + c * taxisX r‖
        ≤ ‖-(lapL2sq u r)‖ + ‖c * taxisX r‖ :=
    norm_add_le _ _
  simp [norm_mul] at h1 h2 h3 ⊢
  nlinarith

/-- Term-by-term zero-start majorants for the four scalar pieces of the
assembled H¹ identity RHS.  This is a source-facing interface for estimates
that naturally control the Laplacian, taxis, `uvxx`, and reaction terms
separately. -/
def H1IdentityRHSInitialWindowTermMajorantsBefore
    (_p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ)
    (taxisX uvxx reactX : ℝ → ℝ) : Prop :=
  H1ScalarInitialWindowMajorantBefore T (lapL2sq u) ∧
  H1ScalarInitialWindowMajorantBefore T taxisX ∧
  H1ScalarInitialWindowMajorantBefore T uvxx ∧
  H1ScalarInitialWindowMajorantBefore T reactX

/-- Term-by-term zero-start majorants assemble to a majorant for the explicit
H¹ identity RHS. -/
theorem H1IdentityRHSInitialWindowMajorantBefore_of_termMajorants
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hTerms : H1IdentityRHSInitialWindowTermMajorantsBefore p u T
      taxisX uvxx reactX) :
    H1IdentityRHSInitialWindowMajorantBefore p u T
      taxisX uvxx reactX := by
  rcases hTerms with ⟨hLap, hTaxis, hUvxx, hReact⟩
  refine H1IdentityRHSInitialWindowMajorantBefore_of_scalarMajorant ?_
  have hsum :
      H1ScalarInitialWindowMajorantBefore T
        (fun r =>
          (-(lapL2sq u r) + (-p.χ₀) * taxisX r) +
            (-p.χ₀) * uvxx r + reactX r) :=
    (((hLap.neg).add (hTaxis.const_mul (-p.χ₀))).add
      (hUvxx.const_mul (-p.χ₀))).add hReact
  change H1ScalarInitialWindowMajorantBefore T
    (fun r =>
      -(lapL2sq u r) + (-p.χ₀) * taxisX r +
        (-p.χ₀) * uvxx r + reactX r)
  simpa [neg_mul, add_assoc] using hsum

/-- Term-by-term zero-start majorants give initial-window integrability of the
assembled H¹ identity RHS. -/
theorem H1IdentityRHSInitialWindowIntegrableBefore_of_termMajorants
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hTerms : H1IdentityRHSInitialWindowTermMajorantsBefore p u T
      taxisX uvxx reactX) :
    H1IdentityRHSInitialWindowIntegrableBefore p u T
      taxisX uvxx reactX :=
  H1IdentityRHSInitialWindowIntegrableBefore_of_majorant
    (H1IdentityRHSInitialWindowMajorantBefore_of_termMajorants hTerms)

/-- An independently integrable assembled H¹ identity RHS on every zero-start
window gives the pointwise derivative proxy from Task 83.

The H¹ identity is used only on `Ioc 0 b`; the endpoint value at zero is not
queried. -/
theorem H1EnergyDerivativeInitialWindowProxyBefore_of_identityRHSInitialWindow
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hInitRHS : H1IdentityRHSInitialWindowIntegrableBefore p u T
      taxisX uvxx reactX) :
    H1EnergyDerivativeInitialWindowProxyBefore u T := by
  refine
    ⟨H1IdentityRHSValue p u taxisX uvxx reactX, ?_, ?_⟩
  · intro b hb0 hbT
    exact hInitRHS hb0 hbT
  · intro b _hb0 hbT r hr
    have hrT : r < T := lt_of_le_of_lt hr.2 hbT
    have hEnergy := hId r ⟨hr.1, hrT⟩
    unfold H1EnergyIdentity at hEnergy
    simpa [H1IdentityRHSValue] using hEnergy.deriv

/-- The same assembled-RHS initial-window data, lowered to the a.e. proxy
frontier from Task 86. -/
theorem H1EnergyDerivativeInitialWindowAEProxyBefore_of_identityRHSInitialWindow
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hInitRHS : H1IdentityRHSInitialWindowIntegrableBefore p u T
      taxisX uvxx reactX) :
    H1EnergyDerivativeInitialWindowAEProxyBefore u T :=
  H1EnergyDerivativeInitialWindowAEProxyBefore_of_proxy
    (H1EnergyDerivativeInitialWindowProxyBefore_of_identityRHSInitialWindow
      hId hInitRHS)

/-- Assembled-RHS initial-window integrability gives the Task 83 derivative
majorant frontier. -/
theorem H1EnergyDerivativeInitialWindowMajorantBefore_of_identityRHSInitialWindow
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hInitRHS : H1IdentityRHSInitialWindowIntegrableBefore p u T
      taxisX uvxx reactX) :
    H1EnergyDerivativeInitialWindowMajorantBefore u T :=
  H1EnergyDerivativeInitialWindowMajorantBefore_of_aeProxy
    (H1EnergyDerivativeInitialWindowAEProxyBefore_of_identityRHSInitialWindow
      hId hInitRHS)

/-- Assembled-RHS initial-window integrability gives the scalar derivative
initial-window input consumed by the strict route. -/
theorem H1EnergyDerivativeInitialWindowIntegrableBefore_of_identityRHSInitialWindow
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hInitRHS : H1IdentityRHSInitialWindowIntegrableBefore p u T
      taxisX uvxx reactX) :
    H1EnergyDerivativeInitialWindowIntegrableBefore u T :=
  H1EnergyDerivativeInitialWindowIntegrableBefore_of_proxy
    (H1EnergyDerivativeInitialWindowProxyBefore_of_identityRHSInitialWindow
      hId hInitRHS)

/-- Term-by-term zero-start majorants plus the pointwise H¹ identity give the
scalar derivative initial-window input consumed by the strict route. -/
theorem H1EnergyDerivativeInitialWindowIntegrableBefore_of_identityRHSTermMajorants
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hTerms : H1IdentityRHSInitialWindowTermMajorantsBefore p u T
      taxisX uvxx reactX) :
    H1EnergyDerivativeInitialWindowIntegrableBefore u T :=
  H1EnergyDerivativeInitialWindowIntegrableBefore_of_identityRHSInitialWindow
    hId
    (H1IdentityRHSInitialWindowIntegrableBefore_of_termMajorants hTerms)

/-- An assembled-RHS majorant plus the pointwise H¹ identity gives the Task 83
pointwise derivative proxy. -/
theorem H1EnergyDerivativeInitialWindowProxyBefore_of_identityRHSMajorant
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hMaj : H1IdentityRHSInitialWindowMajorantBefore p u T
      taxisX uvxx reactX) :
    H1EnergyDerivativeInitialWindowProxyBefore u T :=
  H1EnergyDerivativeInitialWindowProxyBefore_of_identityRHSInitialWindow
    hId
    (H1IdentityRHSInitialWindowIntegrableBefore_of_majorant hMaj)

/-- An assembled-RHS majorant plus the pointwise H¹ identity gives the Task 86
a.e. derivative proxy. -/
theorem H1EnergyDerivativeInitialWindowAEProxyBefore_of_identityRHSMajorant
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hMaj : H1IdentityRHSInitialWindowMajorantBefore p u T
      taxisX uvxx reactX) :
    H1EnergyDerivativeInitialWindowAEProxyBefore u T :=
  H1EnergyDerivativeInitialWindowAEProxyBefore_of_proxy
    (H1EnergyDerivativeInitialWindowProxyBefore_of_identityRHSMajorant
      hId hMaj)

/-- An assembled-RHS majorant plus the pointwise H¹ identity gives the Task 83
derivative majorant frontier. -/
theorem H1EnergyDerivativeInitialWindowMajorantBefore_of_identityRHSMajorant
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hMaj : H1IdentityRHSInitialWindowMajorantBefore p u T
      taxisX uvxx reactX) :
    H1EnergyDerivativeInitialWindowMajorantBefore u T :=
  H1EnergyDerivativeInitialWindowMajorantBefore_of_aeProxy
    (H1EnergyDerivativeInitialWindowAEProxyBefore_of_identityRHSMajorant
      hId hMaj)

/-- An assembled-RHS majorant plus the pointwise H¹ identity gives the scalar
derivative initial-window input consumed by the strict route. -/
theorem H1EnergyDerivativeInitialWindowIntegrableBefore_of_identityRHSMajorant
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hMaj : H1IdentityRHSInitialWindowMajorantBefore p u T
      taxisX uvxx reactX) :
    H1EnergyDerivativeInitialWindowIntegrableBefore u T :=
  H1EnergyDerivativeInitialWindowIntegrableBefore_of_proxy
    (H1EnergyDerivativeInitialWindowProxyBefore_of_identityRHSMajorant
      hId hMaj)

#print axioms H1IdentityRHSInitialWindowMajorantBefore_of_scalarMajorant
#print axioms H1IdentityRHSInitialWindowIntegrableBefore_of_majorant
#print axioms H1IdentityRHSInitialWindowMajorantBefore_of_initialWindowIntegrable
#print axioms
  H1IdentityRHSInitialWindowIntegrableBefore_of_zeroWindow_strict
#print axioms
  H1IdentityRHSInitialWindowMajorantBefore_of_zeroWindow_strict
#print axioms H1IdentityRHSValue_norm_le_scalar_sum
#print axioms H1IdentityRHSInitialWindowMajorantBefore_of_termMajorants
#print axioms H1IdentityRHSInitialWindowIntegrableBefore_of_termMajorants
#print axioms
  H1EnergyDerivativeInitialWindowIntegrableBefore_of_identityRHSTermMajorants
#print axioms
  H1EnergyDerivativeInitialWindowProxyBefore_of_identityRHSInitialWindow
#print axioms
  H1EnergyDerivativeInitialWindowAEProxyBefore_of_identityRHSInitialWindow
#print axioms
  H1EnergyDerivativeInitialWindowMajorantBefore_of_identityRHSInitialWindow
#print axioms
  H1EnergyDerivativeInitialWindowIntegrableBefore_of_identityRHSInitialWindow
#print axioms
  H1EnergyDerivativeInitialWindowProxyBefore_of_identityRHSMajorant
#print axioms
  H1EnergyDerivativeInitialWindowAEProxyBefore_of_identityRHSMajorant
#print axioms
  H1EnergyDerivativeInitialWindowMajorantBefore_of_identityRHSMajorant
#print axioms
  H1EnergyDerivativeInitialWindowIntegrableBefore_of_identityRHSMajorant

end ShenWork.Paper2.IntervalChiNegH1InitialDerivativeRHS
