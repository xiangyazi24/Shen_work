/-
  ShenWork/Wiener/EWA/SourceReducedCoreWireV6EvenReal.lean

  **`CoupledDuhamelReducedClassicalCore` from `EvenRealEWA` directly.**

  The existing v4/v5 chain derived `EvenRealEWA u_star` from the contraction
  framework (hself, hLipQ, hLipG, hKnn, hK) via `picardEWA_evenReal_fixedPoint`.
  This theorem takes `EvenRealEWA u_star` as given — produced by
  `picardEWA_clean_fixedPoint_evenReal` (SourceFixedPointEvenReal.lean) which
  gets it from the EvenReal-restricted Banach fixed point.

  The proof merges:
  - v5_auto's spectral derivation (auto-produce source family, L1ContOn,
    hsumE, hdefect, htrace from EvenRealEWA + hfloor)
  - The NEW `hrealizes` path via slab atoms + `realizes_of_picardFixedPoint`,
    bypassing the contraction framework entirely
  - v4's downstream assembly (endpoint nonvanishing, time derivative,
    classical regularity, chimney, core)

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceReducedCoreWireV2
import ShenWork.Wiener.EWA.SourceResolverSummabilityDischarge
import ShenWork.Wiener.EWA.SourceInitialTraceDischarge

open Set Filter Topology
open ShenWork.GWA
open ShenWork.Wiener (WA MemW ofCosineCoeffs)
open ShenWork.IntervalDomain
  (intervalDomainPoint intervalDomainLift intervalDomain intervalDomainClassicalRegularity)
open ShenWork.PDE
  (intervalNeumannResolverSourceCoeff intervalNeumannResolverCoeff)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)
open ShenWork.IntervalPicardLimitRestartWeak (DuhamelSourceL1ContOn)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs
   coupledChemicalConcentration CoupledDuhamelReducedClassicalCore)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.IntervalResolverDirectTimeRegularity (HasResolverDirectSpectralData)
open ShenWork.Paper2 (SourceCoeffQuadraticDecay)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

private theorem cosineMode_abs_le_v6 (n : ℕ) (x : ℝ) :
    |cosineMode n x| ≤ 1 := by
  simp only [cosineMode]
  exact Real.abs_cos_le_one _

private theorem hsum_chem_of_l1_v6 (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ)
    (src : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T) :
    ∀ t ∈ Ioo (0 : ℝ) T,
      ∀ x : intervalDomainPoint, x.1 ∈ Ioo (0 : ℝ) 1 →
        Summable (fun n =>
          coupledChemDivSourceCoeffs p u t n * cosineMode n x.1) := by
  intro t ht x _
  exact Summable.of_norm
    (src.henv_summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      fun n => by
        rw [Real.norm_eq_abs, abs_mul]
        exact (mul_le_of_le_one_right (abs_nonneg _)
          (cosineMode_abs_le_v6 n x.1)).trans
            (src.henv_bound t ht.1.le ht.2.le n))

private theorem hsum_log_of_l1_v6 (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ)
    (src : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T) :
    ∀ t ∈ Ioo (0 : ℝ) T,
      ∀ x : intervalDomainPoint, x.1 ∈ Ioo (0 : ℝ) 1 →
        Summable (fun n =>
          coupledLogisticSourceCoeffs p u t n * cosineMode n x.1) := by
  intro t ht x _
  exact Summable.of_norm
    (src.henv_summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      fun n => by
        rw [Real.norm_eq_abs, abs_mul]
        exact (mul_le_of_le_one_right (abs_nonneg _)
          (cosineMode_abs_le_v6 n x.1)).trans
            (src.henv_bound t ht.1.le ht.2.le n))

theorem realSlice_reducedCore_of_evenReal (p : CM2Params)
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
    (hER : EvenRealEWA u_star)
    (hβpos : 0 < p.β) (hαnn : 0 ≤ p.α) (hμle1 : p.μ ≤ 1)
    {η : ℝ} (hηpos : 0 < η) (hfloor : UniformFloor u_star η)
    (hrecon : ∀ x : intervalDomainPoint,
      u₀ x = ∑' n, u₀cos n * cosineMode n x.1) :
    CoupledDuhamelReducedClassicalCore p T u₀ (realSlice u_star) := by
  have hνnn : 0 ≤ p.ν := le_of_lt p.hν
  -- *** Part I: auto-produce spectral data from EvenRealEWA + hfloor ***
  have hsumR : ∀ σ : TimeDom T, ResolverSourceSummable p (realSlice u_star σ.1) :=
    fun σ => resolverSourceSummable_of_evenReal p u_star hER hηpos hfloor σ
  have hgrad : ∀ (τ : TimeDom T),
      Summable fun k : ℕ =>
        |(intervalNeumannResolverCoeff p (realSlice u_star τ.1) k).re|
          * ((k : ℝ) * Real.pi) :=
    fun τ => resolverGradSummable_of_evenReal p u_star hER hηpos hfloor τ
  set f : ℝ → ℝ → ℝ := fun s y =>
    if h : s ∈ Set.Icc (0 : ℝ) T then
      p.ν * (WA.evalAt (y : WA.Circ)
        (sliceWA ⟨s, h⟩ (GWA.incl (by omega : (0:ℕ) ≤ 1) u_star))).re ^ p.γ
    else 0
  have hf_cont : ∀ σ : TimeDom T, Continuous (f σ.1) := by
    intro σ; simp only [f, dif_pos σ.2]
    exact sourceFn_continuous p u_star hηpos hfloor σ
  have hf_nonneg : ∀ (σ : TimeDom T) (y : ℝ), 0 ≤ f σ.1 y := by
    intro σ y; simp only [f, dif_pos σ.2]
    exact sourceFn_nonneg p u_star hνnn hηpos hfloor σ y
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
  have h_flux_diff : ∀ (τ : TimeDom T),
      ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        DifferentiableAt ℝ (chemFluxLifted p (realSlice u_star τ.1)) x :=
    fun τ x hx => chemFluxLifted_differentiableAt_of_EWA p u_star hER hηpos hfloor hνnn τ hx
  have h_src_cont_log : ∀ (τ : TimeDom T), Continuous (wLog p u_star τ.1) :=
    fun τ => wLog_continuous_of_floor p u_star hηpos hfloor τ
  have hlog_l1 : DuhamelSourceL1ContOn
      (coupledLogisticSourceCoeffs p (realSlice u_star)) T :=
    logisticSourceL1ContOn_auto p u_star hηpos hER hfloor hαnn hT0
  have hchem_l1 : DuhamelSourceL1ContOn
      (coupledChemDivSourceCoeffs p (realSlice u_star)) T :=
    chemDivSourceL1ContOn_auto p u_star hηpos hER hT hfloor hβpos hνnn hμle1
  have hsumE : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |fullSourceCoeff p (realSlice u_star) u₀cos t n|) :=
    fun t ht => hsumE_of_L1ContOn p (realSlice u_star) u₀cos hu0bd hchem_l1 hlog_l1 ht.1 ht.2.le
  have hdefect : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun n =>
        |fullSourceCoeff p (realSlice u_star) u₀cos t n - u₀cos n|) :=
    fullSourceCoeff_defect_summable_of_L1ContOn p (realSlice u_star) u₀cos hsumc
      hchem_l1 hlog_l1
  have htrace : Tendsto
      (fun t => ∑' n, |fullSourceCoeff p (realSlice u_star) u₀cos t n - u₀cos n|)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    fullSourceCoeff_trace_tendsto_of_L1ContOn p (realSlice u_star) u₀cos hsumc
      hchem_l1 hlog_l1 hT
  -- *** Part II: hrealizes via slab atoms + realizes_of_picardFixedPoint ***
  have h_u := realSlice_h_u_slab hER
  have h_uα := realSlice_h_uα_slab p hηpos hER hfloor hαnn
  have h_flux_nbhd := realSlice_h_flux_slab p hηpos hβpos hER hfloor hsumR hgrad hμle1
    f hf_cont hf_nonneg hf_coeff hf2
  have H_chem := chemDiv_realizesOn p u_star hER hgrad h_flux_nbhd h_flux_diff
  have H_log := logistic_realizesOn p u_star hER h_u h_uα h_src_cont_log
  have hrealizes : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x =
        ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n
          * cosineMode n x := by
    intro t ht
    exact realizes_of_picardFixedPoint p u₀cos hsumc hmem hT0 u_star hfix hER
      (wChem p u_star) H_chem (wChem_lift_eq p u_star)
      (wLog p u_star) H_log (wLog_lift_eq p u_star) t ht.1 ht.2.le
  -- *** Part III: downstream assembly ***
  have huNE0 := realSlice_lift_endpoint0_ne_zero hδρ hheat hu_ball (T := T)
  have huNE1 := realSlice_lift_endpoint1_ne_zero hδρ hheat hu_ball (T := T)
  have htimeDeriv : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      ∀ x : intervalDomainPoint,
        deriv (fun s : ℝ => realSlice u_star s x) t =
          ∑' n, fullSourceCoeffDot p (realSlice u_star) u₀cos t n *
            cosineMode n x.1 :=
    fun t ht x =>
      (slice_hasDerivAt_of_l1 p (realSlice u_star) u₀cos hu0bd
        hchem_l1 hlog_l1 hrealizes ht x).deriv
  have hdiffU : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      ∀ x : intervalDomainPoint,
        DifferentiableAt ℝ (fun s : ℝ => realSlice u_star s x) t :=
    fun t ht x =>
      (slice_hasDerivAt_of_l1 p (realSlice u_star) u₀cos hu0bd
        hchem_l1 hlog_l1 hrealizes ht x).differentiableAt
  have hdecay : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      SourceCoeffQuadraticDecay p (realSlice u_star t) :=
    realSlice_resolverDecay p u_star u₀cos hδρ hheat hu_ball
      hsumE hrealizes huNE0 huNE1
  have Hv : HasResolverDirectSpectralData T
      (mildChemicalConcentration p (realSlice u_star)) p :=
    realSlice_Hv_full_of_L1ContOn p u_star u₀cos hu0bd
      hchem_l1 hlog_l1 hδρ hheat hu_ball hsumE hrealizes
  have Hvpos : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      ∀ x : intervalDomainPoint,
        0 < mildChemicalConcentration p (realSlice u_star) t x :=
    realSlice_resolverPos p u_star u₀cos hδρ hheat hu_ball
      hsumE hrealizes
  have hclassReg : intervalDomainClassicalRegularity T
      (realSlice u_star)
      (mildChemicalConcentration p (realSlice u_star)) :=
    realSlice_classicalRegularity_of_L1ContOn p u_star u₀cos
      hu0bd hchem_l1 hlog_l1 hsumE hrealizes htimeDeriv hdiffU
      huNE0 huNE1 hdecay Hv Hvpos
  have htime :
      ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
        x.1 ∈ Set.Ioo (0 : ℝ) 1 →
          intervalDomain.timeDeriv (realSlice u_star) t x =
            ∑' n, fullSourceCoeffDot p (realSlice u_star) u₀cos t n *
              cosineMode n x.1 :=
    fun t ht x _ =>
      (slice_hasDerivAt_of_l1 p (realSlice u_star) u₀cos hu0bd
        hchem_l1 hlog_l1 hrealizes ht x).deriv
  have hlap := realSlice_hlap_of_atoms p (realSlice u_star)
    u₀cos hsumE hrealizes
  have hsum_lap := realSlice_hsum_lap_of_atoms p
    (realSlice u_star) u₀cos hsumE
  have hsc := hsum_chem_of_l1_v6 p (realSlice u_star) hchem_l1
  have hsl := hsum_log_of_l1_v6 p (realSlice u_star) hlog_l1
  have hchemInv := realSlice_hchemInv_of_L1ContOn p u_star
    hηpos hER hT hfloor hβpos hνnn hμle1
  have hlogInv := realSlice_hlogInv_of_L1ContOn p u_star
    hηpos hER hfloor hαnn hT0 u₀cos hsumE hrealizes
  exact realSlice_reducedCore p u_star u₀ u₀cos hδρ hheat
    hu_ball htime hlap hchemInv hlogInv hsum_lap hsc hsl
    hclassReg hrealizes hT hsumc hrecon hdefect htrace

end ShenWork.EWA

#print axioms ShenWork.EWA.realSlice_reducedCore_of_evenReal
