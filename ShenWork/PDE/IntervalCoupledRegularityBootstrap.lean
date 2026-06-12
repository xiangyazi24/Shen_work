import ShenWork.PDE.IntervalDomainExistence
import ShenWork.Paper2.IntervalMildToClassical
import ShenWork.Paper2.IntervalResolverWeakBounds
import ShenWork.Paper2.IntervalMildSourceDecay
import ShenWork.PDE.IntervalResolverSpatialC2

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.PDE
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalMildSourceDecay
open ShenWork.IntervalResolverLaplacianBridge
open ShenWork.IntervalResolverGradientBridge
open ShenWork.IntervalResolverPositivity
open ShenWork.IntervalResolverWeakBounds
open ShenWork.IntervalNeumannFullKernel
open ShenWork.CosineSpectrum
open ShenWork.IntervalCosineInversion
open ShenWork.PDE.IntervalMildSourceDecayHelper
open scoped Topology

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

/-- The concrete elliptic signal attached to a coupled trajectory. -/
def coupledChemicalConcentration (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) :
    ℝ → intervalDomainPoint → ℝ :=
  fun t => intervalNeumannResolverR p (u t)

/-- The power-source slice `x ↦ ν u(x)^γ` is `C²` on `[0,1]`. -/
theorem powerSource_contDiffOn_Icc
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hC2 : ContDiffOn ℝ 2 (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift u x) :
    ContDiffOn ℝ 2
      (fun x : ℝ => p.ν * intervalDomainLift u x ^ p.γ)
      (Set.Icc (0 : ℝ) 1) := by
  have hpow :
      ContDiffOn ℝ 2 (fun x : ℝ => intervalDomainLift u x ^ p.γ)
        (Set.Icc (0 : ℝ) 1) :=
    hC2.rpow_const_of_ne (fun x hx => ne_of_gt (hpos x hx))
  exact hpow.const_smul p.ν |>.congr (fun x _ => by rw [smul_eq_mul])

/-- Closed `C²` plus homogeneous endpoint derivative data gives the quadratic
decay needed by the elliptic resolver. -/
def sourceCoeffQuadraticDecay_of_closedC2_neumann_slice
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hC2 : ContDiffOn ℝ 2 (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    (hN0 : Filter.Tendsto (deriv (intervalDomainLift u))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hN1 : Filter.Tendsto (deriv (intervalDomainLift u))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift u x) :
    SourceCoeffQuadraticDecay p u := by
  classical
  set g : ℝ → ℝ := fun x => p.ν * intervalDomainLift u x ^ p.γ with hg
  have hC2g : ContDiffOn ℝ 2 g (Set.Icc (0 : ℝ) 1) := by
    simpa [g] using powerSource_contDiffOn_Icc (p := p) hC2 hpos
  obtain ⟨htend0, htend1⟩ :=
    powerSource_deriv_tendsto_endpoint_of_neumann
      (p := p) (u := u) hC2 hpos hN0 hN1
  have hbc0 : deriv g 0 = 0 := by
    simpa [g] using
      powerSource_deriv_endpoint_eq_zero (p := p) (u := u) hpos (Or.inl rfl)
  have hbc1 : deriv g 1 = 0 := by
    simpa [g] using
      powerSource_deriv_endpoint_eq_zero (p := p) (u := u) hpos (Or.inr rfl)
  have hH2 : IntervalWeakH2Neumann g := by
    simpa [g] using
      powerSource_intervalWeakH2Neumann
        (ν := p.ν) (γ := p.γ) (u := intervalDomainLift u)
        hC2g htend0 htend1 hbc0 hbc1
  let hdecay_exists := intervalWeakH2Neumann_cosineCoeff_quadratic_decay hH2
  let C := Classical.choose hdecay_exists
  have hC : 0 ≤ C := (Classical.choose_spec hdecay_exists).1
  have hdecay : ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs g k| ≤ C / ((k : ℝ) * Real.pi) ^ 2 :=
    (Classical.choose_spec hdecay_exists).2
  refine ⟨C, hC, fun k hk => ?_⟩
  have hkne : k ≠ 0 := by omega
  have hre_eq : (intervalNeumannResolverSourceCoeff p u k).re =
      cosineCoeffs g k := by
    unfold intervalNeumannResolverSourceCoeff cosineCoeffs g
    simp only [Complex.ofReal_re,
      ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff,
      if_neg hkne]
  rw [hre_eq]
  exact hdecay k hk

/-- Positivity of the concrete resolver from a nonnegative continuous slice. -/
theorem coupledChemical_nonneg
    (p : CM2Params) {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hu_nonneg :
      ∀ t, 0 < t → t < T → ∀ x : intervalDomainPoint, 0 ≤ u t x)
    (hu_cont : ∀ t, 0 < t → t < T → Continuous (u t))
    {t : ℝ} (ht : 0 < t) (htT : t < T) (x : intervalDomainPoint) :
    0 ≤ coupledChemicalConcentration p u t x := by
  unfold coupledChemicalConcentration
  have hw_cont : Continuous (u t) := hu_cont t ht htT
  have hw_nonneg : ∀ y : intervalDomainPoint, 0 ≤ u t y :=
    hu_nonneg t ht htT
  have hcont_on :
      ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have hrestrict :
        Set.restrict (Set.Icc (0 : ℝ) 1) (intervalDomainLift (u t)) =
          u t := by
      ext ⟨y, hy⟩
      simp [Set.restrict, intervalDomainLift, hy]
      rfl
    rw [hrestrict]
    exact hw_cont
  have hcont_src :
      Continuous (fun y : intervalDomainPoint => p.ν * (u t y) ^ p.γ) :=
    continuous_const.mul (hw_cont.rpow_const (fun _ => Or.inr p.hγ.le))
  set clip : ℝ → intervalDomainPoint := fun y =>
    ⟨max 0 (min y 1), le_max_left 0 _,
      max_le (by norm_num) (min_le_right y 1)⟩
  have hclip_cont : Continuous clip :=
    Continuous.subtype_mk
      (continuous_const.max (continuous_id.min continuous_const)) _
  set f : ℝ → ℝ :=
    (fun y : intervalDomainPoint => p.ν * (u t y) ^ p.γ) ∘ clip
  have hf_cont : Continuous f := hcont_src.comp hclip_cont
  have hf_nonneg : ∀ z, 0 ≤ f z := fun _ =>
    mul_nonneg p.hν.le (Real.rpow_nonneg (hw_nonneg _) _)
  have hf_coeff : ∀ k, cosineCoeffs f k =
      (intervalNeumannResolverSourceCoeff p (u t) k).re := by
    intro k
    have hsrc_eq :
        (intervalNeumannResolverSourceCoeff p (u t) k).re =
          cosineCoeffs (fun y => p.ν * intervalDomainLift (u t) y ^ p.γ) k := by
      simp [cosineCoeffs, intervalNeumannResolverSourceCoeff,
        Complex.ofReal_re]
    rw [hsrc_eq]
    exact cosineCoeffs_congr_on_Icc (fun y hy => by
      simp only [f, Function.comp, clip]
      have hclip_eq : max 0 (min y 1) = y := by
        rw [min_eq_left hy.2, max_eq_right hy.1]
      simp only [hclip_eq, intervalDomainLift, dif_pos hy]) k
  have ha_sq : Summable (fun k => (cosineCoeffs f k) ^ 2) := by
    have h := resolverSourceCoeff_re_sq_summable_of_continuousOn p hcont_on
    simp only [intervalNeumannResolverSourceCoeff_zero, sub_zero] at h
    exact h.congr (fun k => by rw [hf_coeff])
  exact intervalNeumannResolverR_nonneg_of_nonneg_source
    hf_cont hf_nonneg hf_coeff ha_sq x

/-- Cosine source-value reconstruction for a closed `C²` positive slice. -/
theorem sourceValue_eq_powerSource_of_closedC2_neumann
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hC2 : ContDiffOn ℝ 2 (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    (hN0 : Filter.Tendsto (deriv (intervalDomainLift u))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hN1 : Filter.Tendsto (deriv (intervalDomainLift u))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift u x)
    (y : intervalDomainPoint) :
    intervalNeumannResolverSourceValue p u y =
      p.ν * intervalDomainLift u y.1 ^ p.γ := by
  classical
  set g : ℝ → ℝ := fun x => p.ν * intervalDomainLift u x ^ p.γ with hg
  have hC2g : ContDiffOn ℝ 2 g (Set.Icc (0 : ℝ) 1) := by
    simpa [g] using powerSource_contDiffOn_Icc (p := p) hC2 hpos
  have hbc0 : deriv g 0 = 0 := by
    simpa [g] using
      powerSource_deriv_endpoint_eq_zero (p := p) (u := u) hpos (Or.inl rfl)
  have hbc1 : deriv g 1 = 0 := by
    simpa [g] using
      powerSource_deriv_endpoint_eq_zero (p := p) (u := u) hpos (Or.inr rfl)
  obtain ⟨htend0, htend1⟩ :=
    powerSource_deriv_tendsto_endpoint_of_neumann
      (p := p) (u := u) hC2 hpos hN0 hN1
  have hgC0 : ContinuousOn g (Set.Icc (0 : ℝ) 1) := hC2g.continuousOn
  set G : ℝ → ℝ := fun x => g (clamp01 x) with hGdef
  have hGcont : Continuous G := by
    refine continuousOn_univ.mp ?_
    refine hgC0.comp clamp01_continuous.continuousOn ?_
    intro x _; exact clamp01_mem x
  have hGeqOn : ∀ x ∈ Set.Icc (0 : ℝ) 1, G x = g x := by
    intro x hx
    change g (clamp01 x) = g x
    rw [clamp01_eq_self hx]
  have hGsum : Summable (fun n : ℤ => fourierCoeff (reflCircle G) n) :=
    fourierCoeff_reflCircle_summable_of_repr
      hGcont hC2g hGeqOn htend0 htend1 hbc0 hbc1
  have hcoeff_eq : ∀ k : ℕ,
      (intervalNeumannResolverSourceCoeff p u k).re = cosineCoeffs G k := by
    intro k
    have h1 : (intervalNeumannResolverSourceCoeff p u k).re =
        cosineCoeffs g k := by
      simp only [intervalNeumannResolverSourceCoeff, Complex.ofReal_re,
        cosineCoeffs, hg]
    rw [h1]
    exact cosineCoeffs_congr_on_Icc (fun x hx => (hGeqOn x hx).symm) k
  set S : ℝ → ℝ := fun x =>
    ∑' k : ℕ, (intervalNeumannResolverSourceCoeff p u k).re *
      Real.cos ((k : ℝ) * Real.pi * x) with hSdef
  have habs : Summable fun k : ℕ => |cosineCoeffs G k| :=
    intervalCosineCoeff_summable_abs G hGcont hGsum
  have habs' :
      Summable fun k : ℕ => |(intervalNeumannResolverSourceCoeff p u k).re| := by
    refine habs.congr (fun k => ?_)
    rw [hcoeff_eq]
  have hScont : Continuous S := by
    refine continuous_tsum (fun k => ?_) habs' (fun k x => ?_)
    · exact continuous_const.mul (Real.continuous_cos.comp (by fun_prop))
    · rw [Real.norm_eq_abs, abs_mul]
      have hcos : |Real.cos ((k : ℝ) * Real.pi * x)| ≤ 1 :=
        Real.abs_cos_le_one _
      calc |(intervalNeumannResolverSourceCoeff p u k).re| *
              |Real.cos ((k : ℝ) * Real.pi * x)|
          ≤ |(intervalNeumannResolverSourceCoeff p u k).re| * 1 :=
            mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
        _ = |(intervalNeumannResolverSourceCoeff p u k).re| := mul_one _
  have hSeq_int : ∀ x ∈ Set.Ioo (0 : ℝ) 1, S x = g x := by
    intro x hx
    have hinv :
        HasSum (fun k => unitIntervalCosineMode k x * cosineCoeffs G k) (G x) :=
      intervalCosine_hasSum_pointwise G hGcont hx hGsum
    have hterm : ∀ k : ℕ,
        unitIntervalCosineMode k x * cosineCoeffs G k =
          (intervalNeumannResolverSourceCoeff p u k).re *
            Real.cos ((k : ℝ) * Real.pi * x) := by
      intro k
      rw [← hcoeff_eq k]
      unfold unitIntervalCosineMode
      ring
    have hinv' :
        HasSum
          (fun k => (intervalNeumannResolverSourceCoeff p u k).re *
            Real.cos ((k : ℝ) * Real.pi * x))
          (G x) :=
      hinv.congr_fun (fun k => (hterm k).symm)
    have hSx : S x = G x := hinv'.tsum_eq
    rw [hSx, hGeqOn x (Set.Ioo_subset_Icc_self hx)]
  have hSeq_closed : ∀ x ∈ Set.Icc (0 : ℝ) 1, S x = g x := by
    have hcl : closure (Set.Ioo (0 : ℝ) 1) = Set.Icc (0 : ℝ) 1 :=
      closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)
    have hsub : Set.Ioo (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 :=
      Set.Ioo_subset_Icc_self
    have hts : Set.Icc (0 : ℝ) 1 ⊆ closure (Set.Ioo (0 : ℝ) 1) := hcl.ge
    have hEq : Set.EqOn S g (Set.Ioo (0 : ℝ) 1) := fun x hx => hSeq_int x hx
    have hclosed : Set.EqOn S g (Set.Icc (0 : ℝ) 1) :=
      hEq.of_subset_closure hScont.continuousOn hgC0 hsub hts
    intro x hx
    exact hclosed hx
  change S y.1 = g y.1
  exact hSeq_closed y.1 y.2

/-- Convert closed `C²` and endpoint derivative limits into the formal
`normalDeriv = 0` boundary statement. -/
theorem normalDeriv_zero_of_closedC2_neumann
    {w : intervalDomainPoint → ℝ}
    (hC2 : ContDiffOn ℝ 2 (intervalDomainLift w) (Set.Icc (0 : ℝ) 1))
    (hN0 : Filter.Tendsto (deriv (intervalDomainLift w))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hN1 : Filter.Tendsto (deriv (intervalDomainLift w))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    {x : intervalDomainPoint} (hx : x ∈ intervalDomain.boundary) :
    intervalDomain.normalDeriv w x = 0 := by
  change intervalDomainNormalDeriv w x = 0
  have hdiff : DifferentiableOn ℝ (intervalDomainLift w) (Set.Ioo (0 : ℝ) 1) :=
    (hC2.differentiableOn (by norm_num)).mono Set.Ioo_subset_Icc_self
  have hcont0 :
      ContinuousWithinAt (intervalDomainLift w) (Set.Ioo (0 : ℝ) 1) 0 :=
    (hC2.continuousOn 0 (by constructor <;> norm_num)).mono
      Set.Ioo_subset_Icc_self
  have hcont1 :
      ContinuousWithinAt (intervalDomainLift w) (Set.Ioo (0 : ℝ) 1) 1 :=
    (hC2.continuousOn 1 (by constructor <;> norm_num)).mono
      Set.Ioo_subset_Icc_self
  have hmem0 : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    mem_nhdsWithin.mpr ⟨Set.Iio 1, isOpen_Iio, by norm_num,
      fun z hz => ⟨hz.2, hz.1⟩⟩
  have hmem1 : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) :=
    mem_nhdsWithin.mpr ⟨Set.Ioi 0, isOpen_Ioi, by norm_num,
      fun z hz => ⟨hz.1, hz.2⟩⟩
  rcases hx with h0 | h1
  · unfold intervalDomainNormalDeriv
    rw [if_pos h0]
    exact (hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hcont0 hmem0 hN0).derivWithin
      (uniqueDiffWithinAt_Ici (0 : ℝ))
  · unfold intervalDomainNormalDeriv
    rw [if_neg (by rw [h1]; norm_num), if_pos h1]
    exact (hasDerivWithinAt_Iic_of_tendsto_deriv hdiff hcont1 hmem1 hN1).derivWithin
      (uniqueDiffWithinAt_Iic (1 : ℝ))

/-- The resolver laplacian equals the `RLap` series on the open interval. -/
theorem resolver_laplacian_eq_RLap_of_sourceDecay
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p u)
    {x : intervalDomainPoint} (hx : x ∈ intervalDomain.inside) :
    intervalDomain.laplacian (intervalNeumannResolverR p u) x =
      intervalNeumannResolverRLap p u x := by
  change intervalDomainLaplacian (intervalNeumannResolverR p u) x =
    intervalNeumannResolverRLap p u x
  unfold intervalDomainLaplacian
  have hxIcc : x.1 ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
  have hloc :
      deriv (intervalDomainLift (intervalNeumannResolverR p u))
        =ᶠ[𝓝 x.1] resolverGradReal p u := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioo hx] with y hy
    classical
    set S : ℝ → ℝ := fun z =>
      ∑' k : ℕ, (intervalNeumannResolverCoeff p u k).re *
        Real.cos ((k : ℝ) * Real.pi * z) with hS
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
    have hSderiv :
        HasDerivAt S (intervalNeumannResolverRGrad p u ⟨y, hyIcc⟩) y := by
      rw [hS]
      exact solution_resolver_grad_hasDerivAt_of_sourceDecay hdecay hyIcc
    have hEq : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
        intervalDomainLift (intervalNeumannResolverR p u) z = S z := by
      intro z hz
      have hzIcc : z ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hz
      simp only [intervalDomainLift, hzIcc, dif_pos]
      rw [resolverR_apply_eq, hS]
    have hlocS : intervalDomainLift (intervalNeumannResolverR p u) =ᶠ[𝓝 y] S := by
      refine Filter.eventuallyEq_of_mem ?_ hEq
      exact IsOpen.mem_nhds isOpen_Ioo hy
    rw [hlocS.deriv_eq, hSderiv.deriv, resolverGradReal_eq p u ⟨y, hyIcc⟩]
  rw [hloc.deriv_eq]
  exact deriv_resolverGradReal_eq_RLap hdecay hxIcc

/-- The concrete resolver has zero formal normal derivative on the boundary. -/
theorem resolver_normalDeriv_zero_of_sourceDecay
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p u)
    {x : intervalDomainPoint} (hx : x ∈ intervalDomain.boundary) :
    intervalDomain.normalDeriv (intervalNeumannResolverR p u) x = 0 := by
  classical
  change intervalDomainNormalDeriv (intervalNeumannResolverR p u) x = 0
  set S : ℝ → ℝ := fun z =>
    ∑' k : ℕ, (intervalNeumannResolverCoeff p u k).re *
      Real.cos ((k : ℝ) * Real.pi * z) with hS
  have hS0 : HasDerivWithinAt S 0 (Set.Ici (0 : ℝ)) 0 := by
    have h0Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> norm_num
    have h := solution_resolver_grad_hasDerivAt_of_sourceDecay hdecay h0Icc
    have hgrad0 : intervalNeumannResolverRGrad p u ⟨0, h0Icc⟩ = 0 := by
      rw [resolverRGrad_apply_eq]
      have hzero :
          (fun k : ℕ => (intervalNeumannResolverCoeff p u k).re *
            (-((k : ℝ) * Real.pi) *
              Real.sin ((k : ℝ) * Real.pi * (0 : ℝ)))) =
            fun _ => (0 : ℝ) := by
        funext k
        simp
      rw [hzero, tsum_zero]
    have hderiv : HasDerivAt S 0 0 := by
      simpa [S] using h.congr_deriv hgrad0
    exact hderiv.hasDerivWithinAt
  have hS1 : HasDerivWithinAt S 0 (Set.Iic (1 : ℝ)) 1 := by
    have h1Icc : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> norm_num
    have h := solution_resolver_grad_hasDerivAt_of_sourceDecay hdecay h1Icc
    have hgrad1 : intervalNeumannResolverRGrad p u ⟨1, h1Icc⟩ = 0 := by
      rw [resolverRGrad_apply_eq]
      have hzero :
          (fun k : ℕ => (intervalNeumannResolverCoeff p u k).re *
            (-((k : ℝ) * Real.pi) *
              Real.sin ((k : ℝ) * Real.pi * (1 : ℝ)))) =
            fun _ => (0 : ℝ) := by
        funext k
        have hsin : Real.sin ((k : ℝ) * Real.pi) = 0 := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using Real.sin_nat_mul_pi k
        simp [hsin]
      rw [hzero, tsum_zero]
    have hderiv : HasDerivAt S 0 1 := by
      simpa [S] using h.congr_deriv hgrad1
    exact hderiv.hasDerivWithinAt
  have hEq0 :
      intervalDomainLift (intervalNeumannResolverR p u)
        =ᶠ[nhdsWithin (0 : ℝ) (Set.Ici 0)] S := by
    have hnear :
        ∀ᶠ y in nhdsWithin (0 : ℝ) (Set.Ici 0),
          y ∈ Set.Icc (0 : ℝ) 1 := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
        with y hy0 hy1 using ⟨hy0, hy1⟩
    filter_upwards [hnear] with y hy
    simp only [intervalDomainLift, hy, dif_pos]
    rw [resolverR_apply_eq, hS]
  have hEq1 :
      intervalDomainLift (intervalNeumannResolverR p u)
        =ᶠ[nhdsWithin (1 : ℝ) (Set.Iic 1)] S := by
    have hnear :
        ∀ᶠ y in nhdsWithin (1 : ℝ) (Set.Iic 1),
          y ∈ Set.Icc (0 : ℝ) 1 := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Ici_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
        with y hy1 hy0 using ⟨hy0, hy1⟩
    filter_upwards [hnear] with y hy
    simp only [intervalDomainLift, hy, dif_pos]
    rw [resolverR_apply_eq, hS]
  rcases hx with h0 | h1
  · unfold intervalDomainNormalDeriv
    rw [if_pos h0]
    have h0Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> norm_num
    have hEqAt0 : intervalDomainLift (intervalNeumannResolverR p u) 0 = S 0 := by
      simp only [intervalDomainLift, h0Icc, dif_pos]
      rw [resolverR_apply_eq, hS]
    exact (hS0.congr_of_eventuallyEq hEq0 hEqAt0).derivWithin
      (uniqueDiffWithinAt_Ici (0 : ℝ))
  · unfold intervalDomainNormalDeriv
    rw [if_neg (by rw [h1]; norm_num), if_pos h1]
    have h1Icc : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> norm_num
    have hEqAt1 : intervalDomainLift (intervalNeumannResolverR p u) 1 = S 1 := by
      simp only [intervalDomainLift, h1Icc, dif_pos]
      rw [resolverR_apply_eq, hS]
    exact (hS1.congr_of_eventuallyEq hEq1 hEqAt1).derivWithin
      (uniqueDiffWithinAt_Iic (1 : ℝ))

/-- The concrete resolver solves the elliptic PDE once `u` has closed `C²`
and homogeneous endpoint derivative data. -/
theorem coupledChemical_ellipticPDE_of_closedC2_neumann
    (p : CM2Params) {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hpos : ∀ t x, 0 < t → t < T → 0 < u t x)
    (hC2 : ∀ t, 0 < t → t < T →
      ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1))
    (hN0 : ∀ t, 0 < t → t < T →
      Filter.Tendsto (deriv (intervalDomainLift (u t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hN1 : ∀ t, 0 < t → t < T →
      Filter.Tendsto (deriv (intervalDomainLift (u t)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)) :
    ∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
      0 = intervalDomain.laplacian (coupledChemicalConcentration p u t) x
        - p.μ * coupledChemicalConcentration p u t x
        + p.ν * (u t x) ^ p.γ := by
  intro t x ht htT hx
  have hpos_lift : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u t) y := by
    intro y hy
    simp only [intervalDomainLift, hy, dif_pos]
    exact hpos t ⟨y, hy⟩ ht htT
  have hdecay : SourceCoeffQuadraticDecay p (u t) :=
    sourceCoeffQuadraticDecay_of_closedC2_neumann_slice
      (hC2 t ht htT) (hN0 t ht htT) (hN1 t ht htT) hpos_lift
  have hRLap := intervalNeumannResolverRLap_elliptic_identity hdecay x
  have hlap :
      intervalDomain.laplacian (coupledChemicalConcentration p u t) x =
        intervalNeumannResolverRLap p (u t) x := by
    unfold coupledChemicalConcentration
    exact resolver_laplacian_eq_RLap_of_sourceDecay hdecay hx
  have hsource :
      intervalNeumannResolverSourceValue p (u t) x =
        p.ν * intervalDomainLift (u t) x.1 ^ p.γ :=
    sourceValue_eq_powerSource_of_closedC2_neumann
      (hC2 t ht htT) (hN0 t ht htT) (hN1 t ht htT) hpos_lift x
  have hxIcc : x.1 ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
  rw [hlap, hRLap, hsource]
  have hxsub : (⟨x.1, hxIcc⟩ : intervalDomainPoint) = x := Subtype.ext rfl
  simp only [coupledChemicalConcentration, intervalDomainLift, hxIcc, dif_pos]
  rw [hxsub]
  ring

/-- Boundary conditions for `u` and its concrete resolver from closed `C²`
and homogeneous endpoint derivative data for `u`. -/
theorem coupledChemical_neumannBC_of_closedC2_neumann
    (p : CM2Params) {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hpos : ∀ t x, 0 < t → t < T → 0 < u t x)
    (hC2 : ∀ t, 0 < t → t < T →
      ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1))
    (hN0 : ∀ t, 0 < t → t < T →
      Filter.Tendsto (deriv (intervalDomainLift (u t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hN1 : ∀ t, 0 < t → t < T →
      Filter.Tendsto (deriv (intervalDomainLift (u t)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)) :
    ∀ t x, 0 < t → t < T → x ∈ intervalDomain.boundary →
      intervalDomain.normalDeriv (u t) x = 0 ∧
      intervalDomain.normalDeriv (coupledChemicalConcentration p u t) x = 0 := by
  intro t x ht htT hx
  have hpos_lift : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u t) y := by
    intro y hy
    simp only [intervalDomainLift, hy, dif_pos]
    exact hpos t ⟨y, hy⟩ ht htT
  have hdecay : SourceCoeffQuadraticDecay p (u t) :=
    sourceCoeffQuadraticDecay_of_closedC2_neumann_slice
      (hC2 t ht htT) (hN0 t ht htT) (hN1 t ht htT) hpos_lift
  constructor
  · exact normalDeriv_zero_of_closedC2_neumann
      (hC2 t ht htT) (hN0 t ht htT) (hN1 t ht htT) hx
  · change intervalDomainNormalDeriv (coupledChemicalConcentration p u t) x = 0
    unfold coupledChemicalConcentration
    exact resolver_normalDeriv_zero_of_sourceDecay hdecay hx

/-- The remaining non-resolver fields needed to regularize a coupled fixed
point.  These are exactly the parabolic/Schauder and trace fields not supplied
by the elliptic resolver lemmas in this file. -/
structure CoupledDuhamelClassicalCore
    (p : CM2Params) (T : ℝ) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  u_pos : ∀ t x, 0 < t → t < T → 0 < u t x
  u_nonneg : ∀ t, 0 < t → t < T → ∀ x : intervalDomainPoint, 0 ≤ u t x
  u_cont : ∀ t, 0 < t → t < T → Continuous (u t)
  u_closedC2 : ∀ t, 0 < t → t < T →
    ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1)
  u_neumann_left : ∀ t, 0 < t → t < T →
    Filter.Tendsto (deriv (intervalDomainLift (u t)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)
  u_neumann_right : ∀ t, 0 < t → t < T →
    Filter.Tendsto (deriv (intervalDomainLift (u t)))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)
  pde_u : ∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
    intervalDomain.timeDeriv u t x =
      intervalDomain.laplacian (u t) x
        - p.χ₀ * intervalDomain.chemotaxisDiv p (u t)
            (coupledChemicalConcentration p u t) x
        + u t x * (p.a - p.b * (u t x) ^ p.α)
  classicalRegularity :
    intervalDomainClassicalRegularity T u (coupledChemicalConcentration p u)
  initialTrace : InitialTrace intervalDomain u₀ u

/-- Coupled fixed-point regularization from the reduced classical core. -/
theorem regularityBootstrap_of_coupledDuhamel_core
    (p : CM2Params) {T : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (C : CoupledDuhamelClassicalCore p T u₀ u) :
    RegularityBootstrap p T u₀ u := by
  refine ⟨coupledChemicalConcentration p u, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact C.u_pos
  · intro t x ht htT
    exact coupledChemical_nonneg p C.u_nonneg C.u_cont ht htT x
  · exact C.pde_u
  · exact coupledChemical_ellipticPDE_of_closedC2_neumann p
      C.u_pos C.u_closedC2 C.u_neumann_left C.u_neumann_right
  · exact coupledChemical_neumannBC_of_closedC2_neumann p
      C.u_pos C.u_closedC2 C.u_neumann_left C.u_neumann_right
  · exact C.classicalRegularity
  · exact C.initialTrace

/-- Concrete-resolver local existence from the reduced classical core. -/
theorem localExistence_of_coupledDuhamel_concreteResolver_estimates_and_classical_core
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {A L K T M : ℝ} (hA : 0 < A) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hT : 0 < T) (hAT : A * T < 1) (hM : 0 ≤ M)
    (hA_bound : |p.χ₀| * K + L ≤ A)
    (hL_lip : ∀ a b : ℝ, |a| ≤ M → |b| ≤ M →
      |a * (p.a - p.b * a ^ p.α) - b * (p.a - p.b * b ^ p.α)| ≤
        L * |a - b|)
    (hest :
      IntervalCoupledResolverBallEstimates p
        (fun w : intervalDomainPoint → ℝ => intervalNeumannResolverR p w)
        u₀ T M K)
    (hcore :
      ∀ u : ℝ → intervalDomainPoint → ℝ,
        intervalTrajectoryBoundedOn T M u →
        (∀ t x, 0 ≤ t → t ≤ T →
          u t x =
            intervalCoupledDuhamelOperator p
              (fun w : intervalDomainPoint → ℝ => intervalNeumannResolverR p w)
              u₀ u t x) →
        CoupledDuhamelClassicalCore p T u₀ u) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u₀ u := by
  refine
    localExistence_of_coupledDuhamel_resolver_estimates_and_regularization
      p (fun w : intervalDomainPoint → ℝ => intervalNeumannResolverR p w) u₀
      hu₀ hA hL hK hT hAT hM hA_bound hL_lip hest ?_
  intro u _v hu_bound hfp _hv
  exact regularityBootstrap_of_coupledDuhamel_core p (hcore u hu_bound hfp)

end ShenWork.IntervalCoupledRegularityBootstrap
