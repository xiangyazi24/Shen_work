/-
  ShenWork/Paper2/IntervalMildToClassical.lean

  T7e bridge: GradientMildSolutionData -> RegularityBootstrap -> localExistence.

  Route A (ChatGPT R2): new direct bridge that consumes the gradient-form mild
  solution, bypassing the old intervalDuhamelOperator entirely.

  **Status (post-reduction):**
  - InitialTrace: closed from uniform mild-map initial approach
  - Elliptic PDE: closed under C²/Neumann snapshot hypotheses
  - Neumann BC: closed under C²/Neumann snapshot hypotheses
  - Parabolic PDE: closed from classical-solution hypothesis
  - Classical regularity: closed from classical-solution hypothesis
-/
import ShenWork.Paper2.IntervalMildPicard
import ShenWork.PDE.IntervalDomainExistence
import ShenWork.PDE.IntervalResolverPositivity
import ShenWork.Paper2.Statements
import ShenWork.PDE.IntervalResolverLaplacianBridge
import ShenWork.PDE.IntervalCosineSliceRegularity
import ShenWork.PDE.IntervalFullSemigroupNeumann
import ShenWork.Paper2.IntervalMildSourceDecay

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalMildToClassical

open ShenWork.IntervalMildPicard
open ShenWork.IntervalDomain
open ShenWork.PDE ShenWork.Paper2
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalResolverGradientBridge
open ShenWork.IntervalResolverLaplacianBridge
open ShenWork.IntervalGradientDuhamelMap
open ShenWork.IntervalMildSourceDecay
open ShenWork.IntervalMildRegularityBootstrap
open ShenWork.IntervalCosineCoeffDecay
open ShenWork.IntervalCosineInversion
open ShenWork.CosineSpectrum

/-! ## Bridge: GradientMildSolutionData -> RegularityBootstrap -/

/-- The chemical concentration v(t) := resolver(u(t)) for the mild solution. -/
noncomputable def mildChemicalConcentration (p : CM2Params)
    (u : ℝ -> intervalDomainPoint -> ℝ) (t : ℝ) : intervalDomainPoint -> ℝ :=
  intervalNeumannResolverR p (u t)

/-- v(t,x) >= 0 when u(t) >= 0: resolver preserves nonnegativity. -/
theorem mildChemical_nonneg (p : CM2Params)
    {u : ℝ -> intervalDomainPoint -> ℝ}
    (hu_nonneg : ∀ t, 0 < t -> t ≤ T -> ∀ x, 0 ≤ u t x)
    (hu_cont : HasContinuousSlices T u)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : intervalDomainPoint) :
    0 ≤ mildChemicalConcentration p u t x := by
  unfold mildChemicalConcentration
  have hw_cont : Continuous (u t) := hu_cont t ht htT
  have hw_nonneg : ∀ y : intervalDomainPoint, 0 ≤ u t y := hu_nonneg t ht htT
  have hcont_on : ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have : Set.restrict (Set.Icc (0 : ℝ) 1) (intervalDomainLift (u t)) = u t := by
      ext ⟨x, hx⟩
      simp [Set.restrict, intervalDomainLift, hx]
      rfl
    rw [this]
    exact hw_cont
  have hcont_src : Continuous
      (fun y : intervalDomainPoint ↦ p.ν * (u t y) ^ p.γ) :=
    continuous_const.mul (hw_cont.rpow_const (fun y ↦ Or.inr p.hγ.le))
  set clip : ℝ -> intervalDomainPoint := fun x ↦
    ⟨max 0 (min x 1), le_max_left 0 _,
      max_le (by norm_num) (min_le_right x 1)⟩
  have hclip_cont : Continuous clip :=
    Continuous.subtype_mk
      (continuous_const.max (continuous_id.min continuous_const)) _
  set f : ℝ -> ℝ :=
    (fun y : intervalDomainPoint ↦ p.ν * (u t y) ^ p.γ) ∘ clip
  have hf_cont : Continuous f := hcont_src.comp hclip_cont
  have hf_nonneg : ∀ z, 0 ≤ f z := fun z ↦
    mul_nonneg p.hν.le (Real.rpow_nonneg (hw_nonneg _) _)
  have hf_coeff : ∀ k, cosineCoeffs f k =
      (intervalNeumannResolverSourceCoeff p (u t) k).re := by
    intro k
    have hsrc_eq :
        (intervalNeumannResolverSourceCoeff p (u t) k).re =
        cosineCoeffs (fun x ↦ p.ν * intervalDomainLift (u t) x ^ p.γ) k := by
      simp [cosineCoeffs, intervalNeumannResolverSourceCoeff,
        Complex.ofReal_re]
    rw [hsrc_eq]
    exact cosineCoeffs_congr_on_Icc (fun x hx ↦ by
      simp only [f, Function.comp, clip]
      have hclip_eq : max 0 (min x 1) = x := by
        rw [min_eq_left hx.2, max_eq_right hx.1]
      simp only [hclip_eq, intervalDomainLift,
        dif_pos (Set.mem_Icc.mpr hx)]) k
  open ShenWork.IntervalResolverWeakBounds in
  have ha_sq : Summable (fun k ↦ (cosineCoeffs f k) ^ 2) := by
    have h := resolverSourceCoeff_re_sq_summable_of_continuousOn p hcont_on
    simp only [intervalNeumannResolverSourceCoeff_zero, sub_zero] at h
    exact h.congr (fun k ↦ by rw [hf_coeff])
  open ShenWork.IntervalResolverPositivity in
  exact intervalNeumannResolverR_nonneg_of_nonneg_source
    hf_cont hf_nonneg hf_coeff ha_sq x

/-- u(t,x) > 0 (strict positivity) from the Picard iteration. -/
theorem mildSolution_strictlyPositive (p : CM2Params)
    {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) (x : intervalDomainPoint) :
    0 < D.u t x := by
  exact D.hpos t ht htT x

/-! ## Mild equation pointwise: lift agrees with Duhamel RHS on [0,1]

This is the key bridge: the lift of the mild solution agrees with the explicit
Duhamel formula on the closed interval [0,1]. The Duhamel formula is a sum of
semigroup terms, each of which is C-infinity for t > 0.
-/

/-- The mild equation as a pointwise identity on the lift.
For `t > 0` and `y in [0,1]`, `intervalDomainLift (D.u t) y` equals the
gradient Duhamel map evaluated at `<y, hy>`. -/
theorem mildSolution_lift_eq_duhamelMap (p : CM2Params)
    {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T)
    {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    intervalDomainLift (D.u t) y =
      intervalGradientDuhamelMap p u₀ D.u t ⟨y, hy⟩ := by
  simp only [intervalDomainLift, dif_pos hy]
  exact D.hmild t ht htT ⟨y, hy⟩

private theorem intervalDomainNormalDeriv_zero_of_contDiffOn_neumann
    {u : intervalDomainPoint → ℝ}
    (hC2 : ContDiffOn ℝ 2 (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    (hN0 : Filter.Tendsto (deriv (intervalDomainLift u))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hN1 : Filter.Tendsto (deriv (intervalDomainLift u))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    {x : intervalDomainPoint} (hx : x ∈ intervalDomain.boundary) :
    intervalDomain.normalDeriv u x = 0 := by
  change intervalDomainNormalDeriv u x = 0
  have hdiff : DifferentiableOn ℝ (intervalDomainLift u) (Set.Ioo (0 : ℝ) 1) :=
    (hC2.differentiableOn (by norm_num)).mono Set.Ioo_subset_Icc_self
  have hcont0 : ContinuousWithinAt (intervalDomainLift u) (Set.Ioo (0 : ℝ) 1) 0 :=
    (hC2.continuousOn 0 (by constructor <;> norm_num)).mono Set.Ioo_subset_Icc_self
  have hcont1 : ContinuousWithinAt (intervalDomainLift u) (Set.Ioo (0 : ℝ) 1) 1 :=
    (hC2.continuousOn 1 (by constructor <;> norm_num)).mono Set.Ioo_subset_Icc_self
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

private theorem mild_source_contDiffOn_Icc
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hC2 : ContDiffOn ℝ 2 (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift u x) :
    ContDiffOn ℝ 2 (fun x : ℝ => p.ν * intervalDomainLift u x ^ p.γ)
      (Set.Icc (0 : ℝ) 1) := by
  have hpow :
      ContDiffOn ℝ 2 (fun x : ℝ => intervalDomainLift u x ^ p.γ)
        (Set.Icc (0 : ℝ) 1) :=
    hC2.rpow_const_of_ne (fun x hx => ne_of_gt (hpos x hx))
  exact hpow.const_smul p.ν |>.congr (fun x _ => by rw [smul_eq_mul])

private theorem mild_sourceValue_eq_source
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hC2 : ContDiffOn ℝ 2 (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    (hN0 : Filter.Tendsto (deriv (intervalDomainLift u))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hN1 : Filter.Tendsto (deriv (intervalDomainLift u))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift u x)
    (y : intervalDomainPoint) :
    intervalNeumannResolverSourceValue p u y =
      p.ν * (intervalDomainLift u y.1) ^ p.γ := by
  classical
  set g : ℝ → ℝ := fun x => p.ν * intervalDomainLift u x ^ p.γ with hgdef
  have hC2g : ContDiffOn ℝ 2 g (Set.Icc (0:ℝ) 1) := by
    simpa [g] using mild_source_contDiffOn_Icc (p := p) hC2 hpos
  have hbc0 : deriv g 0 = 0 := by
    simpa [g] using powerSource_deriv_endpoint_eq_zero (p := p) (u := u) hpos (Or.inl rfl)
  have hbc1 : deriv g 1 = 0 := by
    simpa [g] using powerSource_deriv_endpoint_eq_zero (p := p) (u := u) hpos (Or.inr rfl)
  obtain ⟨htend0, htend1⟩ :=
    powerSource_deriv_tendsto_endpoint_of_neumann (p := p) (u := u) hC2 hpos hN0 hN1
  have hgC0 : ContinuousOn g (Set.Icc (0:ℝ) 1) := hC2g.continuousOn
  set G : ℝ → ℝ := fun x => g (clamp01 x) with hGdef
  have hGcont : Continuous G := by
    refine continuousOn_univ.mp ?_
    refine hgC0.comp clamp01_continuous.continuousOn ?_
    intro x _; exact clamp01_mem x
  have hGeqOn : ∀ x ∈ Set.Icc (0:ℝ) 1, G x = g x := by
    intro x hx; show g (clamp01 x) = g x; rw [clamp01_eq_self hx]
  have hGsum : Summable (fun n : ℤ => fourierCoeff (reflCircle G) n) :=
    fourierCoeff_reflCircle_summable_of_repr hGcont hC2g hGeqOn htend0 htend1 hbc0 hbc1
  have hcoeff_eq : ∀ k : ℕ,
      (intervalNeumannResolverSourceCoeff p u k).re = cosineCoeffs G k := by
    intro k
    have h1 : (intervalNeumannResolverSourceCoeff p u k).re =
        cosineCoeffs g k := by
      simp only [intervalNeumannResolverSourceCoeff, Complex.ofReal_re,
        cosineCoeffs, hgdef]
    rw [h1]
    exact cosineCoeffs_congr_on_Icc (fun x hx => (hGeqOn x hx).symm) k
  set S : ℝ → ℝ := fun x =>
    ∑' k : ℕ, (intervalNeumannResolverSourceCoeff p u k).re *
      Real.cos ((k : ℝ) * Real.pi * x) with hSdef
  have habs : Summable fun k : ℕ => |cosineCoeffs G k| :=
    intervalCosineCoeff_summable_abs G hGcont hGsum
  have habs' : Summable fun k : ℕ => |(intervalNeumannResolverSourceCoeff p u k).re| := by
    refine habs.congr (fun k => ?_)
    rw [hcoeff_eq]
  have hScont : Continuous S := by
    refine continuous_tsum (fun k => ?_) habs' (fun k x => ?_)
    · exact continuous_const.mul (Real.continuous_cos.comp (by fun_prop))
    · rw [Real.norm_eq_abs, abs_mul]
      have hcos : |Real.cos ((k : ℝ) * Real.pi * x)| ≤ 1 := Real.abs_cos_le_one _
      calc |(intervalNeumannResolverSourceCoeff p u k).re| *
              |Real.cos ((k : ℝ) * Real.pi * x)|
          ≤ |(intervalNeumannResolverSourceCoeff p u k).re| * 1 :=
            mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
        _ = |(intervalNeumannResolverSourceCoeff p u k).re| := mul_one _
  have hSeq_int : ∀ x ∈ Set.Ioo (0:ℝ) 1, S x = g x := by
    intro x hx
    have hinv : HasSum (fun k => unitIntervalCosineMode k x * cosineCoeffs G k) (G x) :=
      intervalCosine_hasSum_pointwise G hGcont hx hGsum
    have hterm : ∀ k : ℕ,
        unitIntervalCosineMode k x * cosineCoeffs G k =
          (intervalNeumannResolverSourceCoeff p u k).re *
            Real.cos ((k : ℝ) * Real.pi * x) := by
      intro k
      rw [← hcoeff_eq k]
      unfold unitIntervalCosineMode
      ring
    have hinv' : HasSum (fun k => (intervalNeumannResolverSourceCoeff p u k).re *
        Real.cos ((k : ℝ) * Real.pi * x)) (G x) :=
      hinv.congr_fun (fun k => (hterm k).symm)
    have hSx : S x = G x := hinv'.tsum_eq
    rw [hSx, hGeqOn x (Set.Ioo_subset_Icc_self hx)]
  have hSeq_closed : ∀ x ∈ Set.Icc (0:ℝ) 1, S x = g x := by
    have hcl : closure (Set.Ioo (0:ℝ) 1) = Set.Icc (0:ℝ) 1 :=
      closure_Ioo (by norm_num : (0:ℝ) ≠ 1)
    have hsub : Set.Ioo (0:ℝ) 1 ⊆ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self
    have hts : Set.Icc (0:ℝ) 1 ⊆ closure (Set.Ioo (0:ℝ) 1) := hcl.ge
    have hEq : Set.EqOn S g (Set.Ioo (0:ℝ) 1) := fun x hx => hSeq_int x hx
    have hclosed : Set.EqOn S g (Set.Icc (0:ℝ) 1) :=
      hEq.of_subset_closure hScont.continuousOn hgC0 hsub hts
    intro x hx; exact hclosed hx
  show S y.1 = g y.1
  exact hSeq_closed y.1 y.2

private theorem resolver_lift_deriv_eq_resolverGrad_of_sourceDecay
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p u)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (intervalDomainLift (intervalNeumannResolverR p u)) x =
      resolverGradReal p u x := by
  classical
  set S : ℝ → ℝ := fun z : ℝ =>
    ∑' k : ℕ, (intervalNeumannResolverCoeff p u k).re *
      Real.cos ((k : ℝ) * Real.pi * z) with hS
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
  have hSderiv : HasDerivAt S (intervalNeumannResolverRGrad p u ⟨x, hxIcc⟩) x := by
    rw [hS]; exact solution_resolver_grad_hasDerivAt_of_sourceDecay hdecay hxIcc
  have hEq : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      intervalDomainLift (intervalNeumannResolverR p u) y = S y := by
    intro y hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
    simp [intervalDomainLift, hyIcc]
    rw [resolverR_apply_eq, hS]
  have hloc : intervalDomainLift (intervalNeumannResolverR p u) =ᶠ[𝓝 x] S := by
    refine Filter.eventuallyEq_of_mem ?_ hEq
    exact IsOpen.mem_nhds isOpen_Ioo hx
  rw [hloc.deriv_eq, hSderiv.deriv, resolverGradReal_eq p u ⟨x, hxIcc⟩]

private theorem resolver_laplacian_eq_RLap_of_sourceDecay
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p u)
    {x : intervalDomainPoint} (hx : x ∈ intervalDomain.inside) :
    intervalDomain.laplacian (intervalNeumannResolverR p u) x =
      intervalNeumannResolverRLap p u x := by
  change intervalDomainLaplacian (intervalNeumannResolverR p u) x =
    intervalNeumannResolverRLap p u x
  unfold intervalDomainLaplacian
  have hxIcc : x.1 ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
  have hloc : deriv (intervalDomainLift (intervalNeumannResolverR p u))
      =ᶠ[𝓝 x.1] resolverGradReal p u := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioo hx] with y hy
    exact resolver_lift_deriv_eq_resolverGrad_of_sourceDecay hdecay hy
  rw [hloc.deriv_eq]
  exact deriv_resolverGradReal_eq_RLap hdecay hxIcc

private theorem intervalNeumannResolverR_normalDeriv_zero_of_sourceDecay
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p u)
    {x : intervalDomainPoint} (hx : x ∈ intervalDomain.boundary) :
    intervalDomain.normalDeriv (intervalNeumannResolverR p u) x = 0 := by
  classical
  change intervalDomainNormalDeriv (intervalNeumannResolverR p u) x = 0
  set S : ℝ → ℝ := fun z : ℝ =>
    ∑' k : ℕ, (intervalNeumannResolverCoeff p u k).re *
      Real.cos ((k : ℝ) * Real.pi * z) with hS
  have hS0 : HasDerivWithinAt S 0 (Set.Ici (0 : ℝ)) 0 := by
    have h0Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
    have h := solution_resolver_grad_hasDerivAt_of_sourceDecay hdecay h0Icc
    have hgrad0 : intervalNeumannResolverRGrad p u ⟨0, h0Icc⟩ = 0 := by
      rw [resolverRGrad_apply_eq]
      have : (fun k : ℕ => (intervalNeumannResolverCoeff p u k).re *
          (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * (0:ℝ)))) =
          fun _ => (0 : ℝ) := by
        funext k; simp
      rw [this, tsum_zero]
    have hderiv : HasDerivAt S 0 0 := by
      simpa [S] using h.congr_deriv hgrad0
    exact hderiv.hasDerivWithinAt
  have hS1 : HasDerivWithinAt S 0 (Set.Iic (1 : ℝ)) 1 := by
    have h1Icc : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
    have h := solution_resolver_grad_hasDerivAt_of_sourceDecay hdecay h1Icc
    have hgrad1 : intervalNeumannResolverRGrad p u ⟨1, h1Icc⟩ = 0 := by
      rw [resolverRGrad_apply_eq]
      have : (fun k : ℕ => (intervalNeumannResolverCoeff p u k).re *
          (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * (1:ℝ)))) =
          fun _ => (0 : ℝ) := by
        funext k
        rw [mul_one, Real.sin_nat_mul_pi]
        ring
      rw [this, tsum_zero]
    have hderiv : HasDerivAt S 0 1 := by
      simpa [S] using h.congr_deriv hgrad1
    exact hderiv.hasDerivWithinAt
  have hEq0 : intervalDomainLift (intervalNeumannResolverR p u)
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ici 0)] S := by
    have hnear : ∀ᶠ y in nhdsWithin (0 : ℝ) (Set.Ici 0), y ∈ Set.Icc (0 : ℝ) 1 := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
        with y hy0 hy1 using ⟨hy0, hy1⟩
    filter_upwards [hnear] with y hy
    simp [intervalDomainLift, hy]
    rw [resolverR_apply_eq, hS]
  have hEq1 : intervalDomainLift (intervalNeumannResolverR p u)
      =ᶠ[nhdsWithin (1 : ℝ) (Set.Iic 1)] S := by
    have hnear : ∀ᶠ y in nhdsWithin (1 : ℝ) (Set.Iic 1), y ∈ Set.Icc (0 : ℝ) 1 := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Ici_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
        with y hy1 hy0 using ⟨hy0, hy1⟩
    filter_upwards [hnear] with y hy
    simp [intervalDomainLift, hy]
    rw [resolverR_apply_eq, hS]
  rcases hx with h0 | h1
  · unfold intervalDomainNormalDeriv
    rw [if_pos h0]
    have h0Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
    have hEqAt0 : intervalDomainLift (intervalNeumannResolverR p u) 0 = S 0 := by
      simp [intervalDomainLift, h0Icc]
      rw [resolverR_apply_eq, hS]
    exact (hS0.congr_of_eventuallyEq hEq0 hEqAt0).derivWithin
      (uniqueDiffWithinAt_Ici (0 : ℝ))
  · unfold intervalDomainNormalDeriv
    rw [if_neg (by rw [h1]; norm_num), if_pos h1]
    have h1Icc : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
    have hEqAt1 : intervalDomainLift (intervalNeumannResolverR p u) 1 = S 1 := by
      simp [intervalDomainLift, h1Icc]
      rw [resolverR_apply_eq, hS]
    exact (hS1.congr_of_eventuallyEq hEq1 hEqAt1).derivWithin
      (uniqueDiffWithinAt_Iic (1 : ℝ))

/-! ## Initial trace -/

theorem mildSolution_initialTrace (p : CM2Params)
    {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀)
    (hInitialApproach : ∀ ε, 0 < ε ->
      ∃ δ > 0, ∀ t, 0 < t -> t < δ ->
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u₀ D.u t x - u₀ x| < ε) :
    InitialTrace intervalDomain u₀ D.u := by
  intro ε hε
  obtain ⟨δ₀, hδ₀, hsmall⟩ := hInitialApproach (ε / 2) (by linarith)
  refine ⟨min δ₀ D.T, lt_min hδ₀ D.hT, fun t ht htδ => ?_⟩
  have htδ₀ : t < δ₀ := lt_of_lt_of_le htδ (min_le_left _ _)
  have htT : t ≤ D.T := le_of_lt (lt_of_lt_of_le htδ (min_le_right _ _))
  change intervalDomainSupNorm (fun x => D.u t x - u₀ x) < ε
  unfold intervalDomainSupNorm
  have hpt : ∀ x : intervalDomainPoint, |D.u t x - u₀ x| < ε / 2 := by
    intro x
    rw [D.hmild t ht htT x]
    exact hsmall t ht htδ₀ x
  have hbdd : BddAbove
      (Set.range (fun x : intervalDomainPoint => |D.u t x - u₀ x|)) := by
    exact ⟨ε / 2, fun y hy => by
      rcases hy with ⟨x, rfl⟩
      exact le_of_lt (hpt x)⟩
  haveI : Nonempty intervalDomainPoint :=
    ⟨⟨0, by constructor <;> norm_num⟩⟩
  have hle :
      sSup (Set.range (fun x : intervalDomainPoint => |D.u t x - u₀ x|)) ≤
        ε / 2 := by
    apply csSup_le (Set.range_nonempty _)
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact le_of_lt (hpt x)
  linarith

/-! ## Parabolic PDE -/

theorem mildSolution_parabolicPDE (p : CM2Params)
    {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀)
    (hclassical : IsPaper2ClassicalSolution intervalDomain p D.T D.u
      (mildChemicalConcentration p D.u)) :
    ∀ t x, 0 < t -> t < D.T -> x ∈ intervalDomain.inside ->
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α) := by
  intro t x ht htT hx
  exact hclassical.pde_u ht htT hx

/-! ## Elliptic PDE for v -/

theorem mildChemical_ellipticPDE_of_closedC2_neumann (p : CM2Params)
    {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀)
    (hC2 : ∀ t, 0 < t -> t < D.T ->
      ContDiffOn ℝ 2 (intervalDomainLift (D.u t)) (Set.Icc (0 : ℝ) 1))
    (hN0 : ∀ t, 0 < t -> t < D.T ->
      Filter.Tendsto (deriv (intervalDomainLift (D.u t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hN1 : ∀ t, 0 < t -> t < D.T ->
      Filter.Tendsto (deriv (intervalDomainLift (D.u t)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)) :
    ∀ t x, 0 < t -> t < D.T -> x ∈ intervalDomain.inside ->
      0 = intervalDomain.laplacian
            (mildChemicalConcentration p D.u t) x
          - p.μ * mildChemicalConcentration p D.u t x
          + p.ν * (D.u t x) ^ p.γ := by
  intro t x ht htT hx
  have htTle : t ≤ D.T := le_of_lt htT
  have hdecay : SourceCoeffQuadraticDecay p (D.u t) :=
    sourceCoeffQuadraticDecay_of_mildSolution_of_closedC2_neumann p D ht htTle
      (hC2 t ht htT) (hN0 t ht htT) (hN1 t ht htT)
  have hRLap := intervalNeumannResolverRLap_elliptic_identity hdecay x
  have hlap :
      intervalDomain.laplacian (mildChemicalConcentration p D.u t) x =
        intervalNeumannResolverRLap p (D.u t) x := by
    unfold mildChemicalConcentration
    exact resolver_laplacian_eq_RLap_of_sourceDecay hdecay hx
  have hpos : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (D.u t) y := by
    intro y hy
    simp only [intervalDomainLift, hy, dif_pos]
    exact D.hpos t ht htTle ⟨y, hy⟩
  have hsource :
      intervalNeumannResolverSourceValue p (D.u t) x =
        p.ν * (intervalDomainLift (D.u t) x.1) ^ p.γ :=
    mild_sourceValue_eq_source (p := p) (u := D.u t)
      (hC2 t ht htT) (hN0 t ht htT) (hN1 t ht htT) hpos x
  have hxIcc : x.1 ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
  rw [hlap, hRLap, hsource]
  have hxsub : (⟨x.1, hxIcc⟩ : intervalDomainPoint) = x := Subtype.ext rfl
  simp only [mildChemicalConcentration, intervalDomainLift, hxIcc, dif_pos]
  rw [hxsub]
  ring

/-- Elliptic PDE for the mild chemical concentration, with the closed-interval
`C²` and one-sided Neumann hypotheses supplied by the restart-cosine bootstrap. -/
theorem mildChemical_ellipticPDE (p : CM2Params)
    {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀)
    (H : HasRestartCosineRepresentations D.T D.u) :
    ∀ t x, 0 < t -> t < D.T -> x ∈ intervalDomain.inside ->
      0 = intervalDomain.laplacian
            (mildChemicalConcentration p D.u t) x
          - p.μ * mildChemicalConcentration p D.u t x
          + p.ν * (D.u t x) ^ p.γ := by
  obtain ⟨hC2, hN0, hN1⟩ :=
    gradientMild_closedC2_neumann_of_restartCosineRepresentations D H
  exact mildChemical_ellipticPDE_of_closedC2_neumann p D hC2 hN0 hN1

/-- Alias emphasizing the restart-cosine route to the unconditional elliptic PDE. -/
theorem mildChemical_ellipticPDE_of_restartCosineRepresentations (p : CM2Params)
    {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀)
    (H : HasRestartCosineRepresentations D.T D.u) :
    ∀ t x, 0 < t -> t < D.T -> x ∈ intervalDomain.inside ->
      0 = intervalDomain.laplacian
            (mildChemicalConcentration p D.u t) x
          - p.μ * mildChemicalConcentration p D.u t x
          + p.ν * (D.u t x) ^ p.γ :=
  mildChemical_ellipticPDE p D H

/-- Elliptic PDE with restart-cosine representations built from half-step source
regularity and series agreement. -/
theorem mildChemical_ellipticPDE_of_gradientMildHalfStepRestartData (p : CM2Params)
    {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀)
    (R : GradientMildHalfStepRestartData D) :
    ∀ t x, 0 < t -> t < D.T -> x ∈ intervalDomain.inside ->
      0 = intervalDomain.laplacian
            (mildChemicalConcentration p D.u t) x
          - p.μ * mildChemicalConcentration p D.u t x
          + p.ν * (D.u t x) ^ p.γ :=
  mildChemical_ellipticPDE_of_restartCosineRepresentations p D
    (hasRestartCosineRepresentations_of_gradientMildHalfStepRestartData D R)

/-- Elliptic PDE with restart-cosine representations built from H²-Neumann
half-step source data, quadratic coefficient decay, and series agreement. -/
theorem mildChemical_ellipticPDE_of_gradientMildHalfStepH2SourceData
    (p : CM2Params) {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀)
    (S : GradientMildHalfStepH2SourceData D) :
    ∀ t x, 0 < t -> t < D.T -> x ∈ intervalDomain.inside ->
      0 = intervalDomain.laplacian
            (mildChemicalConcentration p D.u t) x
          - p.μ * mildChemicalConcentration p D.u t x
          + p.ν * (D.u t x) ^ p.γ :=
  mildChemical_ellipticPDE_of_gradientMildHalfStepRestartData p D
    (gradientMildHalfStepRestartData_of_H2SourceData D S)

/-! ## Neumann BC -/

theorem mildSolution_neumannBC_of_closedC2_neumann (p : CM2Params)
    {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀)
    (hC2 : ∀ t, 0 < t -> t < D.T ->
      ContDiffOn ℝ 2 (intervalDomainLift (D.u t)) (Set.Icc (0 : ℝ) 1))
    (hN0 : ∀ t, 0 < t -> t < D.T ->
      Filter.Tendsto (deriv (intervalDomainLift (D.u t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hN1 : ∀ t, 0 < t -> t < D.T ->
      Filter.Tendsto (deriv (intervalDomainLift (D.u t)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)) :
    ∀ t x, 0 < t -> t < D.T -> x ∈ intervalDomain.boundary ->
      intervalDomain.normalDeriv (D.u t) x = 0 ∧
      intervalDomain.normalDeriv
        (mildChemicalConcentration p D.u t) x = 0 := by
  intro t x ht htT hx
  have htTle : t ≤ D.T := le_of_lt htT
  have hdecay : SourceCoeffQuadraticDecay p (D.u t) :=
    sourceCoeffQuadraticDecay_of_mildSolution_of_closedC2_neumann p D ht htTle
      (hC2 t ht htT) (hN0 t ht htT) (hN1 t ht htT)
  constructor
  · exact intervalDomainNormalDeriv_zero_of_contDiffOn_neumann
      (hC2 t ht htT) (hN0 t ht htT) (hN1 t ht htT) hx
  · unfold mildChemicalConcentration
    exact intervalNeumannResolverR_normalDeriv_zero_of_sourceDecay hdecay hx

/-- Neumann boundary conditions for the mild solution and chemical concentration,
with the closed-interval `C²` and one-sided Neumann hypotheses supplied by the
restart-cosine bootstrap. -/
theorem mildSolution_neumannBC (p : CM2Params)
    {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀)
    (H : HasRestartCosineRepresentations D.T D.u) :
    ∀ t x, 0 < t -> t < D.T -> x ∈ intervalDomain.boundary ->
      intervalDomain.normalDeriv (D.u t) x = 0 ∧
      intervalDomain.normalDeriv
        (mildChemicalConcentration p D.u t) x = 0 := by
  obtain ⟨hC2, hN0, hN1⟩ :=
    gradientMild_closedC2_neumann_of_restartCosineRepresentations D H
  exact mildSolution_neumannBC_of_closedC2_neumann p D hC2 hN0 hN1

/-- Alias emphasizing the restart-cosine route to the unconditional Neumann
boundary conditions. -/
theorem mildSolution_neumannBC_of_restartCosineRepresentations (p : CM2Params)
    {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀)
    (H : HasRestartCosineRepresentations D.T D.u) :
    ∀ t x, 0 < t -> t < D.T -> x ∈ intervalDomain.boundary ->
      intervalDomain.normalDeriv (D.u t) x = 0 ∧
      intervalDomain.normalDeriv
        (mildChemicalConcentration p D.u t) x = 0 :=
  mildSolution_neumannBC p D H

/-- Neumann boundary conditions with restart-cosine representations built from
half-step source regularity and series agreement. -/
theorem mildSolution_neumannBC_of_gradientMildHalfStepRestartData (p : CM2Params)
    {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀)
    (R : GradientMildHalfStepRestartData D) :
    ∀ t x, 0 < t -> t < D.T -> x ∈ intervalDomain.boundary ->
      intervalDomain.normalDeriv (D.u t) x = 0 ∧
      intervalDomain.normalDeriv
        (mildChemicalConcentration p D.u t) x = 0 :=
  mildSolution_neumannBC_of_restartCosineRepresentations p D
    (hasRestartCosineRepresentations_of_gradientMildHalfStepRestartData D R)

/-- Neumann boundary conditions with restart-cosine representations built from
H²-Neumann half-step source data, quadratic coefficient decay, and series
agreement. -/
theorem mildSolution_neumannBC_of_gradientMildHalfStepH2SourceData
    (p : CM2Params) {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀)
    (S : GradientMildHalfStepH2SourceData D) :
    ∀ t x, 0 < t -> t < D.T -> x ∈ intervalDomain.boundary ->
      intervalDomain.normalDeriv (D.u t) x = 0 ∧
      intervalDomain.normalDeriv
        (mildChemicalConcentration p D.u t) x = 0 :=
  mildSolution_neumannBC_of_gradientMildHalfStepRestartData p D
    (gradientMildHalfStepRestartData_of_H2SourceData D S)

/-! ## Classical regularity -/

/-- The remaining regularity frontier after `HasRestartCosineRepresentations`
has supplied the mild solution's spatial `C²` regularity and genuine Neumann
data.

The restart-cosine bootstrap discharges the `u` half of conjuncts (3), (6), and
(7) of `intervalDomainClassicalRegularity`.  The fields below are exactly the
pieces still not supplied by that bootstrap: sup-norm monotonicity, the `v`
spatial/Neumann package, time regularity, and joint slab continuity. -/
structure GradientMildClassicalRegularityFrontierData
    (p : CM2Params) {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀) : Prop where
  supnormLogistic :
    ∀ q : CM2Params, q.χ₀ ≤ 0 -> 0 < q.a -> 0 < q.b ->
      ∀ t₀, 0 < t₀ -> t₀ < D.T ->
        (q.a / q.b) ^ (1 / q.α) < intervalDomainSupNorm (D.u t₀) ->
          IntervalDomainSupNormDerivativeNonposOn D.u (Set.Ioc (0 : ℝ) t₀)
  supnormZero :
    ∀ q : CM2Params, q.χ₀ ≤ 0 -> q.a = 0 -> q.b = 0 ->
      IntervalDomainSupNormDerivativeNonposOn D.u (Set.Ioo (0 : ℝ) D.T)
  vSpatialInterior :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) D.T ->
      ContDiffOn ℝ 2
        (intervalDomainLift (mildChemicalConcentration p D.u t))
        (Set.Ioo (0 : ℝ) 1)
  timeSlices :
    ∀ x : intervalDomainPoint,
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) D.T ->
        (DifferentiableAt ℝ (fun s : ℝ => D.u s x) t ∧
            DifferentiableAt ℝ
              (fun s : ℝ => mildChemicalConcentration p D.u s x) t) ∧
          (ContinuousOn (fun s : ℝ => deriv (fun r : ℝ => D.u r x) s)
              (Set.Ioo (0 : ℝ) D.T) ∧
            ContinuousOn
              (fun s : ℝ =>
                deriv (fun r : ℝ => mildChemicalConcentration p D.u r x) s)
              (Set.Ioo (0 : ℝ) D.T))
  jointTimeDerivInterior :
    ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv (fun s : ℝ => intervalDomainLift (D.u s) x) t))
        (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Ioo (0 : ℝ) 1) ∧
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv
              (fun s : ℝ =>
                intervalDomainLift (mildChemicalConcentration p D.u s) x) t))
        (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Ioo (0 : ℝ) 1)
  vNeumannLimits :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) D.T ->
      Filter.Tendsto
          (deriv (intervalDomainLift (mildChemicalConcentration p D.u t)))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto
          (deriv (intervalDomainLift (mildChemicalConcentration p D.u t)))
          (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)
  vClosedSpatial :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) D.T ->
      ContDiffOn ℝ 2
          (intervalDomainLift (mildChemicalConcentration p D.u t))
          (Set.Icc (0 : ℝ) 1) ∧
        deriv (intervalDomainLift (mildChemicalConcentration p D.u t)) 0 = 0 ∧
        deriv (intervalDomainLift (mildChemicalConcentration p D.u t)) 1 = 0
  jointTimeDerivClosed :
    ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv (fun s : ℝ => intervalDomainLift (D.u s) x) t))
        (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) ∧
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv
              (fun s : ℝ =>
                intervalDomainLift (mildChemicalConcentration p D.u s) x) t))
        (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1)
  jointSolutionClosed :
    ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (D.u t) x))
        (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) ∧
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            intervalDomainLift (mildChemicalConcentration p D.u t) x))
        (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1)

/-- Classical regularity for `(u, resolver(u))` from restart-cosine regularity
plus the remaining frontier data. -/
theorem mildSolution_classicalRegularity_of_restartCosineRepresentations_and_frontier
    (p : CM2Params) {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀)
    (H : HasRestartCosineRepresentations D.T D.u)
    (F : GradientMildClassicalRegularityFrontierData p D) :
    intervalDomainClassicalRegularity D.T D.u
      (mildChemicalConcentration p D.u) := by
  unfold intervalDomainClassicalRegularity
  refine ⟨F.supnormLogistic, F.supnormZero, ?_, F.timeSlices,
    F.jointTimeDerivInterior, ?_, ?_, F.jointTimeDerivClosed,
    F.jointSolutionClosed⟩
  · intro t ht
    exact ⟨(gradientMild_contDiffOn_of_restartCosineRepresentations
        D H t ht.1 ht.2).mono Set.Ioo_subset_Icc_self,
      F.vSpatialInterior t ht⟩
  · intro t ht
    exact
      ⟨⟨gradientMild_neumann_left_of_restartCosineRepresentations
            D H t ht.1 ht.2,
          gradientMild_neumann_right_of_restartCosineRepresentations
            D H t ht.1 ht.2⟩,
        F.vNeumannLimits t ht⟩
  · intro t ht
    exact
      ⟨gradientMild_closedC2_endpointDerivs_of_restartCosineRepresentations
          D H t ht.1 ht.2,
        F.vClosedSpatial t ht⟩

/-- Same classical-regularity bridge, with restart representations produced
from the half-step restart package. -/
theorem mildSolution_classicalRegularity_of_halfStepRestartData_and_frontier
    (p : CM2Params) {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀)
    (R : GradientMildHalfStepRestartData D)
    (F : GradientMildClassicalRegularityFrontierData p D) :
    intervalDomainClassicalRegularity D.T D.u
      (mildChemicalConcentration p D.u) :=
  mildSolution_classicalRegularity_of_restartCosineRepresentations_and_frontier
    p D (hasRestartCosineRepresentations_of_gradientMildHalfStepRestartData D R) F

/-- Same classical-regularity bridge, with restart representations produced
from H²-Neumann half-step source data and quadratic source-coefficient decay. -/
theorem mildSolution_classicalRegularity_of_halfStepH2SourceData_and_frontier
    (p : CM2Params) {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀)
    (S : GradientMildHalfStepH2SourceData D)
    (F : GradientMildClassicalRegularityFrontierData p D) :
    intervalDomainClassicalRegularity D.T D.u
      (mildChemicalConcentration p D.u) :=
  mildSolution_classicalRegularity_of_halfStepRestartData_and_frontier
    p D (gradientMildHalfStepRestartData_of_H2SourceData D S) F

theorem mildSolution_classicalRegularity (p : CM2Params)
    {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀)
    (hclassical : IsPaper2ClassicalSolution intervalDomain p D.T D.u
      (mildChemicalConcentration p D.u)) :
    intervalDomainClassicalRegularity D.T D.u
      (mildChemicalConcentration p D.u) := by
  simpa [intervalDomain] using hclassical.regularity

end ShenWork.IntervalMildToClassical
