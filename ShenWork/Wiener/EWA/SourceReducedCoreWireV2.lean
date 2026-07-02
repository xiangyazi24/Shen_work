/-
  ShenWork/Wiener/EWA/SourceReducedCoreWireV2.lean

  v2 retypes of `realSlice_classicalRegularity` and
  `realSlice_reducedCore_wired` against `DuhamelSourceL1ContOn`
  (no `derivBound`).

  This replaces `DuhamelSourceTimeC1(On)` everywhere with
  `DuhamelSourceL1ContOn`, using the v2 synthesis chain from
  `SourceSynthesisL1.lean`.  The proof bodies are identical
  to the originals modulo 4+3 call substitutions.
-/
import ShenWork.Wiener.EWA.SourceReducedCoreWire
import ShenWork.Wiener.EWA.SourceClassicalRegularity
import ShenWork.Wiener.EWA.SourceSynthesisL1

noncomputable section

namespace ShenWork.EWA

open Set Filter Topology
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain
  (intervalDomain intervalDomainPoint intervalDomainLift
   intervalDomainClassicalRegularity)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs
   CoupledDuhamelReducedClassicalCore)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.IntervalPicardLimitRestartWeak (DuhamelSourceL1ContOn)
open ShenWork.IntervalResolverDirectTimeRegularity
  (HasResolverDirectSpectralData)
open ShenWork.Paper2 (SourceCoeffQuadraticDecay)

variable {T : ℝ}

/-! ### Private windowed wrappers (L1ContOn). -/

private theorem cosineMode_abs_le' (n : ℕ) (x : ℝ) :
    |cosineMode n x| ≤ 1 := by
  simp only [cosineMode]; exact Real.abs_cos_le_one _

private theorem hsum_chem_of_l1 (p : CM2Params)
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
          (cosineMode_abs_le' n x.1)).trans
            (src.henv_bound t ht.1.le ht.2.le n))

private theorem hsum_log_of_l1 (p : CM2Params)
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
          (cosineMode_abs_le' n x.1)).trans
            (src.henv_bound t ht.1.le ht.2.le n))

/-! ### Slice HasDerivAt + time derivative (L1ContOn). -/

private theorem slice_hasDerivAt_of_l1 (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T)
    (hrealizes : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) x =
        ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (x : intervalDomainPoint) :
    HasDerivAt (fun s => u s x)
      (∑' n, fullSourceCoeffDot p u u₀cos t n * cosineMode n x.1)
      t :=
  (synthesis_hasDerivAt_of_L1ContOn p u u₀cos hu0bd hchem hlog ht
    x.1).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht)
      fun s hs => by
        have : intervalDomainLift (u s) x.1 = u s x := by
          simp [intervalDomainLift]
        rw [← this, hrealizes s hs x.1 x.2])

private theorem htime_of_l1 (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T)
    (hrealizes : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) x =
        ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      x.1 ∈ Ioo (0 : ℝ) 1 →
        intervalDomain.timeDeriv u t x =
          ∑' n, fullSourceCoeffDot p u u₀cos t n *
            cosineMode n x.1 :=
  fun t ht x _ =>
    (slice_hasDerivAt_of_l1 p u u₀cos hu0bd hchem hlog hrealizes
      ht x).deriv

/-! ### v2 classical regularity (L1ContOn). -/

theorem realSlice_classicalRegularity_of_L1ContOn
    (p : CM2Params) (u_star : EWA T 1)
    (u₀cos : ℕ → ℝ) {Mu0 : ℝ} (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn
      (coupledChemDivSourceCoeffs p (realSlice u_star)) T)
    (hlog : DuhamelSourceL1ContOn
      (coupledLogisticSourceCoeffs p (realSlice u_star)) T)
    (hsumE : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |fullSourceCoeff p (realSlice u_star) u₀cos t n|))
    (hrealizes : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        intervalDomainLift (realSlice u_star t) x =
          ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n *
            cosineMode n x)
    (htimeDeriv : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      ∀ x : intervalDomainPoint,
        deriv (fun s : ℝ => realSlice u_star s x) t =
          ∑' n, fullSourceCoeffDot p (realSlice u_star) u₀cos t n *
            cosineMode n x.1)
    (hdiffU : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      ∀ x : intervalDomainPoint,
        DifferentiableAt ℝ (fun s : ℝ => realSlice u_star s x) t)
    (huNE0 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift (realSlice u_star t) 0 ≠ 0)
    (huNE1 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift (realSlice u_star t) 1 ≠ 0)
    (hdecay : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      SourceCoeffQuadraticDecay p (realSlice u_star t))
    (Hv : HasResolverDirectSpectralData T
      (mildChemicalConcentration p (realSlice u_star)) p)
    (Hvpos : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      ∀ x : intervalDomainPoint,
        0 < mildChemicalConcentration p (realSlice u_star) t x) :
    intervalDomainClassicalRegularity T (realSlice u_star)
      (mildChemicalConcentration p (realSlice u_star)) := by
  set u := realSlice u_star with hu
  set v := mildChemicalConcentration p u with hvdef
  have hvR : ∀ s, v s = intervalNeumannResolverR p (u s) :=
    fun s => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    refine ⟨intervalDomainCosineSlice_contDiffOn_Ioo (hsumE t ht)
        (realSlice_lift_eqOn_Icc p u_star u₀cos (hrealizes t ht)),
      ?_⟩
    rw [hvR t]
    exact intervalDomainCosineSlice_contDiffOn_Ioo
      (resolverR_summability (hdecay t ht))
      (resolver_lift_eqOn_Icc p (u t))
  · intro x t ht
    have hvts := timeSlices_v_of_resolverSpectral Hv x
    refine ⟨⟨hdiffU t ht x, hvts.1 t ht⟩, ?_, hvts.2⟩
    have hjoint :=
      fullSourceCoeffDot_jointTimeDerivClosed_of_L1ContOn
        p u u₀cos hu0bd hchem hlog
    have hmapCont : Continuous (fun s : ℝ => (s, x.1)) := by
      fun_prop
    have hmap : Set.MapsTo (fun s : ℝ => (s, x.1))
        (Set.Ioo (0 : ℝ) T)
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
      fun s hs => ⟨hs, x.2⟩
    have hcomp := hjoint.comp hmapCont.continuousOn hmap
    have hcont : ContinuousOn
        (fun s : ℝ => ∑' n,
          fullSourceCoeffDot p u u₀cos s n * cosineMode n x.1)
        (Set.Ioo (0 : ℝ) T) := by
      simpa only [Function.uncurry, Function.comp] using hcomp
    exact ContinuousOn.congr hcont (fun s hs => htimeDeriv s hs x)
  · refine ⟨?_, jointTimeDerivInterior_v_of_resolverSpectral Hv⟩
    have hjoint :=
      fullSourceCoeffDot_jointTimeDerivInterior_of_L1ContOn
        p u u₀cos hu0bd hchem hlog
    refine ContinuousOn.congr hjoint (fun q hq => ?_)
    obtain ⟨ht, hx⟩ := hq
    have hxIcc : q.2 ∈ Set.Icc (0 : ℝ) 1 :=
      Set.Ioo_subset_Icc_self hx
    simp only [Function.uncurry]
    rw [deriv_lift_slice_eq_subtype u hxIcc q.1]
    exact htimeDeriv q.1 ht ⟨q.2, hxIcc⟩
  · intro t ht
    refine ⟨⟨intervalDomainCosineSlice_neumann_limit_left
        (hsumE t ht)
        (realSlice_lift_eqOn_Icc p u_star u₀cos (hrealizes t ht)),
      intervalDomainCosineSlice_neumann_limit_right
        (hsumE t ht)
        (realSlice_lift_eqOn_Icc p u_star u₀cos
          (hrealizes t ht))⟩, ?_⟩
    rw [hvR t]
    exact ⟨intervalDomainCosineSlice_neumann_limit_left
        (resolverR_summability (hdecay t ht))
        (resolver_lift_eqOn_Icc p (u t)),
      intervalDomainCosineSlice_neumann_limit_right
        (resolverR_summability (hdecay t ht))
        (resolver_lift_eqOn_Icc p (u t))⟩
  · intro t ht
    refine ⟨intervalDomainCosineSlice_conjunct7 (hsumE t ht)
        (realSlice_lift_eqOn_Icc p u_star u₀cos (hrealizes t ht))
        (huNE0 t ht) (huNE1 t ht), ?_⟩
    rw [hvR t]
    have hpos0 :
        intervalDomainLift (intervalNeumannResolverR p (u t)) 0
          ≠ 0 := by
      have h := Hvpos t ht ⟨0, by constructor <;> norm_num⟩
      rw [hvR t] at h
      have : intervalDomainLift
            (intervalNeumannResolverR p (u t)) 0
          = intervalNeumannResolverR p (u t)
            ⟨0, by constructor <;> norm_num⟩ := by
        rw [intervalDomainLift, dif_pos
          (show (0:ℝ) ∈ Set.Icc (0:ℝ) 1 by
            constructor <;> norm_num)]
      rw [this]; exact ne_of_gt h
    have hpos1 :
        intervalDomainLift (intervalNeumannResolverR p (u t)) 1
          ≠ 0 := by
      have h := Hvpos t ht ⟨1, by constructor <;> norm_num⟩
      rw [hvR t] at h
      have : intervalDomainLift
            (intervalNeumannResolverR p (u t)) 1
          = intervalNeumannResolverR p (u t)
            ⟨1, by constructor <;> norm_num⟩ := by
        rw [intervalDomainLift, dif_pos
          (show (1:ℝ) ∈ Set.Icc (0:ℝ) 1 by
            constructor <;> norm_num)]
      rw [this]; exact ne_of_gt h
    exact intervalDomainCosineSlice_conjunct7
      (resolverR_summability (hdecay t ht))
      (resolver_lift_eqOn_Icc p (u t)) hpos0 hpos1
  · refine ⟨?_, jointTimeDerivClosed_v_of_resolverSpectral Hv⟩
    have hjoint :=
      fullSourceCoeffDot_jointTimeDerivClosed_of_L1ContOn
        p u u₀cos hu0bd hchem hlog
    refine ContinuousOn.congr hjoint (fun q hq => ?_)
    obtain ⟨ht, hx⟩ := hq
    simp only [Function.uncurry]
    rw [deriv_lift_slice_eq_subtype u hx q.1]
    exact htimeDeriv q.1 ht ⟨q.2, hx⟩
  · refine ⟨?_, jointSolutionClosed_v_of_resolverSpectral Hv⟩
    have hjoint :=
      fullSourceCoeff_jointSolutionClosed_of_L1ContOn
        p u u₀cos hu0bd hchem hlog
    refine ContinuousOn.congr hjoint (fun q hq => ?_)
    obtain ⟨ht, hx⟩ := hq
    simp only [Function.uncurry]
    exact hrealizes q.1 ht q.2 hx

/-! ### v2 reduced core (L1ContOn). -/

-- TEMPORARILY commented out to verify classicalRegularity in isolation
/-
theorem realSlice_reducedCore_wired_v2 (p : CM2Params)
    (u_star : EWA T 1)
    (u₀ : intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ)
    {Mu0 : ℝ} (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    {u₀E : WA 1} {δ ρ : ℝ} (hδρ : 0 < δ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ)
    (hu_ball : u_star ∈ Metric.closedBall
      (heatEWA (T := T) u₀E) ρ)
    (hsumc : Summable (fun k => |u₀cos k|))
    (hmem : MemW 1 (ofCosineCoeffs u₀cos))
    (hT0 : (0 : ℝ) ≤ T) {L_Q L_G δ' ρ' : ℝ}
    (hδ'pos : 0 < δ') (hρ'ρ : ρ' = ρ)
    (hfix : u_star = picardEWA p p.μ p.ν p.γ p.hμ hT0
      (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1) u_star)
    (hρ' : 0 ≤ ρ')
    (hself : MapsTo
      (picardEWA p p.μ p.ν p.γ p.hμ hT0
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1))
      (Metric.closedBall
        (heatEWA (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ')
      (Metric.closedBall
        (heatEWA (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ'))
    (hLipQ : ∀ a ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ',
      ∀ b ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ',
      ‖chemFluxEWA p.μ p.ν p.β p.γ p.hμ a
        - chemFluxEWA p.μ p.ν p.β p.γ p.hμ b‖
          ≤ L_Q * ‖a - b‖)
    (hLipG : ∀ a ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ',
      ∀ b ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ',
      ‖growthEWA p.α p.a p.b a - growthEWA p.α p.a p.b b‖
        ≤ L_G * ‖a - b‖)
    (hKnn : (0 : ℝ) ≤
      |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T)
    (hK : |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T < 1)
    (hmem_star : u_star ∈ Metric.closedBall (heatEWA (T := T)
      (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ')
    (hβpos : 0 < p.β) (hαnn : 0 ≤ p.α) (hμle1 : p.μ ≤ 1)
    (hfloorδ : δ' = T) (hfloor : UniformFloor u_star δ')
    (hsumR : ∀ σ : TimeDom T,
      ResolverSourceSummable p (realSlice u_star σ.1))
    (hgrad : ∀ (τ : TimeDom T),
      Summable fun k : ℕ =>
        |(intervalNeumannResolverCoeff p
          (realSlice u_star τ.1) k).re| * ((k : ℝ) * Real.pi))
    (f : ℝ → ℝ → ℝ)
    (hf_cont : ∀ σ : TimeDom T, Continuous (f σ.1))
    (hf_nonneg : ∀ (σ : TimeDom T) (y : ℝ), 0 ≤ f σ.1 y)
    (hf_coeff : ∀ (σ : TimeDom T) (k : ℕ),
      cosineCoeffs (f σ.1) k =
        (intervalNeumannResolverSourceCoeff p
          (realSlice u_star σ.1) k).re)
    (hf2 : ∀ σ : TimeDom T,
      Summable (fun k => (cosineCoeffs (f σ.1) k) ^ 2))
    (h_flux_diff : ∀ (τ : TimeDom T),
      ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        DifferentiableAt ℝ
          (chemFluxLifted p (realSlice u_star τ.1)) x)
    (h_src_cont_log : ∀ (τ : TimeDom T),
      Continuous (wLog p u_star τ.1))
    (hchem_l1 : DuhamelSourceL1ContOn
      (coupledChemDivSourceCoeffs p (realSlice u_star)) T)
    (hlog_l1 : DuhamelSourceL1ContOn
      (coupledLogisticSourceCoeffs p (realSlice u_star)) T)
    (hclassReg : intervalDomainClassicalRegularity T
      (realSlice u_star)
      (mildChemicalConcentration p (realSlice u_star)))
    (hsumE : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |fullSourceCoeff p (realSlice u_star) u₀cos t n|))
    {μc νc γc : ℝ} (hμc : 0 < μc) (Uc : EWA T 1)
    (hcontChem : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Continuous (fun x : intervalDomainPoint =>
        intervalDomainChemotaxisDiv p (realSlice u_star t)
          (coupledChemicalConcentration p
            (realSlice u_star) t) x))
    (h_coeffChem : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
        |coupledChemDivSourceCoeffs p (realSlice u_star) s n|
          ≤ sourceEnvelope (chemDivEWA μc νc γc hμc p Uc) n)
    (hlogNE0 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift
        (intervalLogisticSource p (realSlice u_star t)) 0 ≠ 0)
    (hlogNE1 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift
        (intervalLogisticSource p (realSlice u_star t)) 1 ≠ 0)
    (Hv : HasResolverDirectSpectralData T
      (mildChemicalConcentration p (realSlice u_star)) p)
    (hT : (0 : ℝ) < T)
    (hu0cos : Summable (fun n => |u₀cos n|))
    (hrecon : ∀ x : intervalDomainPoint,
      u₀ x = ∑' n, u₀cos n * cosineMode n x.1)
    (hdefect : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun n =>
        |fullSourceCoeff p (realSlice u_star) u₀cos t n
          - u₀cos n|))
    (htrace : Filter.Tendsto
      (fun t => ∑' n,
        |fullSourceCoeff p (realSlice u_star) u₀cos t n
          - u₀cos n|)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    CoupledDuhamelReducedClassicalCore p T u₀
      (realSlice u_star) := by
  have hrealizes :
      ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        intervalDomainLift (realSlice u_star t) x =
          ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n
            * cosineMode n x := by
    refine realSlice_realizes_slab_evalST_discharged p u₀cos
      hsumc hmem hT0 hδ'pos u_star ?_ hρ' ?_ ?_ ?_ hKnn hK ?_
      hβpos hαnn hμle1 hfloorδ hfloor hsumR hgrad
      f hf_cont hf_nonneg hf_coeff hf2 h_flux_diff
      h_src_cont_log
    · exact hfix
    · exact hρ'ρ ▸ hself
    · exact hρ'ρ ▸ hLipQ
    · exact hρ'ρ ▸ hLipG
    · exact hρ'ρ ▸ hmem_star
  have huNE0 := realSlice_lift_endpoint0_ne_zero hδρ hheat
    hu_ball (T := T)
  have huNE1 := realSlice_lift_endpoint1_ne_zero hδρ hheat
    hu_ball (T := T)
  have htime := htime_of_l1 p (realSlice u_star) u₀cos hu0bd
    hchem_l1 hlog_l1 hrealizes
  have hlap := realSlice_hlap_of_atoms p (realSlice u_star)
    u₀cos hsumE hrealizes
  have hsum_lap := realSlice_hsum_lap_of_atoms p
    (realSlice u_star) u₀cos hsumE
  have hsc := hsum_chem_of_l1 p (realSlice u_star) hchem_l1
  have hsl := hsum_log_of_l1 p (realSlice u_star) hlog_l1
  have hchemInv := realSlice_hchemInv_direct_realSlice hμc p
    u_star Uc hcontChem h_coeffChem
  have hlogInv := realSlice_hlogInv_of_bankedU p u_star u₀cos
    hδρ hheat hu_ball hsumE hrealizes hlogNE0 hlogNE1
  exact realSlice_reducedCore p u_star u₀ u₀cos hδρ hheat
    hu_ball htime hlap hchemInv hlogInv hsum_lap hsc hsl
    hclassReg hrealizes hT hu0cos hrecon hdefect htrace
-/

end ShenWork.EWA

#print axioms ShenWork.EWA.realSlice_classicalRegularity_of_L1ContOn
