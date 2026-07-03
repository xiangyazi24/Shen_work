/-
  ShenWork/Wiener/EWA/SourceReducedCoreWireV5Auto.lean

  **Auto-assembly of `CoupledDuhamelReducedClassicalCore` from the minimal
  interface: Picard framework + PPID datum cosine data + heat floor.**

  All spectral chain hypotheses (hsumR, hgrad, f-family, flux/log regularity,
  L1ContOn, hsumE, hdefect, htrace) are derived internally from the
  auto-producers in `SourceResolverSummabilityDischarge.lean` and the
  newly discharged atoms in `SourceInitialTraceDischarge.lean`.

  This is the "last mile" theorem that eliminates ~15 carried hypotheses
  from `realSlice_reducedCore_wired_v4` down to the irreducible Picard
  framework + datum data.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceReducedCoreWireV2
import ShenWork.Wiener.EWA.SourceResolverSummabilityDischarge
import ShenWork.Wiener.EWA.SourceInitialTraceDischarge

open Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalPicardLimitRestartWeak (DuhamelSourceL1ContOn)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

theorem realSlice_reducedCore_wired_v5_auto (p : CM2Params)
    (u_star : EWA T 1) (u₀ : intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ)
    {Mu0 : ℝ} (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    {u₀E : WA 1} {δ ρ : ℝ} (hδρ : 0 < δ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ)
    (hu_ball : u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    (hsumc : Summable (fun k => |u₀cos k|))
    (hmem : MemW 1 (ofCosineCoeffs u₀cos))
    (hT0 : (0 : ℝ) ≤ T) (hT : (0 : ℝ) < T)
    (hfix : u_star = picardEWA p p.μ p.ν p.γ p.hμ hT0
      (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1) u_star)
    (hρ : 0 ≤ ρ)
    (hself : MapsTo
      (picardEWA p p.μ p.ν p.γ p.hμ hT0 (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1))
      (Metric.closedBall (heatEWA (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ)
      (Metric.closedBall (heatEWA (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ))
    {L_Q L_G : ℝ}
    (hLipQ : ∀ a ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ∀ b ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ‖chemFluxEWA p.μ p.ν p.β p.γ p.hμ a - chemFluxEWA p.μ p.ν p.β p.γ p.hμ b‖
        ≤ L_Q * ‖a - b‖)
    (hLipG : ∀ a ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ∀ b ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ‖growthEWA p.α p.a p.b a - growthEWA p.α p.a p.b b‖ ≤ L_G * ‖a - b‖)
    (hKnn : (0 : ℝ) ≤ |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T)
    (hK : |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T < 1)
    (hmem_star : u_star ∈ Metric.closedBall (heatEWA (T := T)
      (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ)
    (hβpos : 0 < p.β) (hαnn : 0 ≤ p.α) (hμle1 : p.μ ≤ 1)
    (hfloor : UniformFloor u_star T)
    (hrecon : ∀ x : intervalDomainPoint,
      u₀ x = ∑' n, u₀cos n * cosineMode n x.1) :
    CoupledDuhamelReducedClassicalCore p T u₀ (realSlice u_star) := by
  -- Step A: derive EvenRealEWA from the Picard fixed-point parity.
  have hER : EvenRealEWA u_star :=
    picardEWA_evenReal_fixedPoint p p.hμ hT0 u₀cos hmem hρ hself hLipQ hLipG
      hKnn hK u_star hmem_star hfix
  have hνnn : 0 ≤ p.ν := le_of_lt p.hν
  -- Step B: auto-produce the source family.
  have hsumR : ∀ σ : TimeDom T, ResolverSourceSummable p (realSlice u_star σ.1) :=
    fun σ => resolverSourceSummable_of_evenReal p u_star hER hT hfloor σ
  have hgrad : ∀ (τ : TimeDom T),
      Summable fun k : ℕ =>
        |(intervalNeumannResolverCoeff p (realSlice u_star τ.1) k).re|
          * ((k : ℝ) * Real.pi) :=
    fun τ => resolverGradSummable_of_evenReal p u_star hER hT hfloor τ
  set f : ℝ → ℝ → ℝ := fun s y =>
    if h : s ∈ Set.Icc (0 : ℝ) T then
      p.ν * (WA.evalAt (y : WA.Circ)
        (sliceWA ⟨s, h⟩ (GWA.incl (by omega : (0:ℕ) ≤ 1) u_star))).re ^ p.γ
    else 0
  have hf_cont : ∀ σ : TimeDom T, Continuous (f σ.1) := by
    intro σ; simp only [f, dif_pos σ.2]
    exact sourceFn_continuous p u_star hT hfloor σ
  have hf_nonneg : ∀ (σ : TimeDom T) (y : ℝ), 0 ≤ f σ.1 y := by
    intro σ y; simp only [f, dif_pos σ.2]
    exact sourceFn_nonneg p u_star hνnn hT hfloor σ y
  have hf_coeff : ∀ (σ : TimeDom T) (k : ℕ),
      cosineCoeffs (f σ.1) k =
        (intervalNeumannResolverSourceCoeff p (realSlice u_star σ.1) k).re := by
    intro σ k
    have : f σ.1 = (fun (y : ℝ) =>
        p.ν * (WA.evalAt (y : WA.Circ)
          (sliceWA σ (GWA.incl (by omega : (0:ℕ) ≤ 1) u_star))).re ^ p.γ) := by
      funext y; simp only [f, dif_pos σ.2]
    rw [this, sourceFn_coeff]
  have hf2 : ∀ σ : TimeDom T, Summable (fun k => (cosineCoeffs (f σ.1) k) ^ 2) := by
    intro σ
    have hcoeff : ∀ k, cosineCoeffs (f σ.1) k =
        resolverSourceReCoeff p (realSlice u_star σ.1) k := by
      intro k; simp only [hf_coeff σ k, resolverSourceReCoeff]
    simp_rw [hcoeff]
    exact summable_sq_of_summable_abs (hsumR σ)
  -- Step C: auto-produce flux/log regularity.
  have h_flux_diff : ∀ (τ : TimeDom T),
      ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        DifferentiableAt ℝ (chemFluxLifted p (realSlice u_star τ.1)) x :=
    fun τ x hx => chemFluxLifted_differentiableAt_of_EWA p u_star hER hT hfloor hνnn τ hx
  have h_src_cont_log : ∀ (τ : TimeDom T), Continuous (wLog p u_star τ.1) :=
    fun τ => wLog_continuous_of_floor p u_star hT hfloor τ
  -- Step D: auto-produce L1ContOn.
  have hlog_l1 : DuhamelSourceL1ContOn
      (coupledLogisticSourceCoeffs p (realSlice u_star)) T :=
    logisticSourceL1ContOn_auto p u_star hT hER hfloor hαnn hT0
  have hchem_l1 : DuhamelSourceL1ContOn
      (coupledChemDivSourceCoeffs p (realSlice u_star)) T :=
    chemDivSourceL1ContOn_auto p u_star hT hER hT hfloor hβpos hνnn hμle1
  -- Step E: auto-produce hsumE.
  have hsumE : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |fullSourceCoeff p (realSlice u_star) u₀cos t n|) :=
    fun t ht => hsumE_of_L1ContOn p (realSlice u_star) u₀cos hu0bd hchem_l1 hlog_l1 ht.1 ht.2.le
  -- Step F: auto-produce hdefect (via SourceInitialTraceDischarge).
  have hdefect : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun n =>
        |fullSourceCoeff p (realSlice u_star) u₀cos t n - u₀cos n|) :=
    fullSourceCoeff_defect_summable_of_L1ContOn p (realSlice u_star) u₀cos hsumc
      hchem_l1 hlog_l1
  -- Step G: auto-produce htrace (via SourceInitialTraceDischarge).
  have htrace : Tendsto
      (fun t => ∑' n, |fullSourceCoeff p (realSlice u_star) u₀cos t n - u₀cos n|)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    fullSourceCoeff_trace_tendsto_of_L1ContOn p (realSlice u_star) u₀cos hsumc
      hchem_l1 hlog_l1 hT
  -- Step H: feed everything into v4.
  exact realSlice_reducedCore_wired_v4 p u_star u₀ u₀cos hu0bd hδρ hheat hu_ball
    hsumc hmem hT0 hT rfl hfix hρ hself hLipQ hLipG hKnn hK hmem_star
    hβpos hαnn hμle1 rfl hfloor hsumR hgrad f hf_cont hf_nonneg hf_coeff hf2
    h_flux_diff h_src_cont_log hchem_l1 hlog_l1 hsumE hT hsumc hrecon hdefect htrace

end ShenWork.EWA

#print axioms ShenWork.EWA.realSlice_reducedCore_wired_v5_auto
