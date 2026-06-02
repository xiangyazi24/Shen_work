/-
  ShenWork/Paper2/IntervalMildToClassical.lean

  T7e bridge: GradientMildSolutionData -> RegularityBootstrap -> localExistence.

  Route A (ChatGPT R2): new direct bridge that consumes the gradient-form mild
  solution, bypassing the old intervalDuhamelOperator entirely.

  **Status (post-reduction):**
  - Sorry 3 (InitialTrace): 1 sorry -- needs semigroup approx identity + Duhamel->0
  - Sorry 4 (Elliptic PDE): 1 sorry -- needs SourceCoeffQuadraticDecay for mild sol
  - Sorry 5 (Neumann BC): split into v-part (1 sorry) + u-part (1 sorry)
  - Sorry 6 (Parabolic PDE): 1 sorry -- Schauder bootstrap
  - Sorry 7 (Classical regularity): 1 sorry -- full regularity bundle
-/
import ShenWork.Paper2.IntervalMildPicard
import ShenWork.PDE.IntervalDomainExistence
import ShenWork.PDE.IntervalResolverPositivity
import ShenWork.Paper2.Statements
import ShenWork.PDE.IntervalResolverLaplacianBridge
import ShenWork.PDE.IntervalCosineSliceRegularity

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalMildToClassical

open ShenWork.IntervalMildPicard
open ShenWork.IntervalDomain
open ShenWork.PDE ShenWork.Paper2
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalResolverGradientBridge
open ShenWork.IntervalResolverLaplacianBridge

/-! ## Bridge: GradientMildSolutionData -> RegularityBootstrap

The easy conjuncts (v exists, v >= 0, u > 0) are wired from existing
infrastructure. The hard conjuncts (PDE pointwise, classical regularity)
are sorry -- they require the Schauder bootstrap.
-/

/-- The chemical concentration v(t) := resolver(u(t)) for the mild solution. -/
noncomputable def mildChemicalConcentration (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) : intervalDomainPoint → ℝ :=
  intervalNeumannResolverR p (u t)

/-- v(t,x) >= 0 when u(t) >= 0: resolver preserves nonnegativity. -/
theorem mildChemical_nonneg (p : CM2Params)
    {u : ℝ → intervalDomainPoint → ℝ}
    (hu_nonneg : ∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ u t x)
    (hu_cont : HasContinuousSlices T u)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : intervalDomainPoint) :
    0 ≤ mildChemicalConcentration p u t x := by
  unfold mildChemicalConcentration
  -- Specialize to time slice: w := u t
  have hw_cont : Continuous (u t) := hu_cont t ht htT
  have hw_nonneg : ∀ y : intervalDomainPoint, 0 ≤ u t y := hu_nonneg t ht htT
  -- ContinuousOn for the lift
  have hcont_on : ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have : Set.restrict (Set.Icc (0 : ℝ) 1) (intervalDomainLift (u t)) = u t := by
      ext ⟨x, hx⟩
      simp [Set.restrict, intervalDomainLift, hx]
      rfl
    rw [this]
    exact hw_cont
  -- Source function continuous on R via clip
  have hcont_src : Continuous
      (fun y : intervalDomainPoint ↦ p.ν * (u t y) ^ p.γ) :=
    continuous_const.mul (hw_cont.rpow_const (fun y ↦ Or.inr p.hγ.le))
  set clip : ℝ → intervalDomainPoint := fun x ↦
    ⟨max 0 (min x 1), le_max_left 0 _,
      max_le (by norm_num) (min_le_right x 1)⟩
  have hclip_cont : Continuous clip :=
    Continuous.subtype_mk
      (continuous_const.max (continuous_id.min continuous_const)) _
  set f : ℝ → ℝ :=
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
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) (x : intervalDomainPoint) :
    0 < D.u t x := by
  exact D.hpos t ht htT x

/-! ## Sorry 3: Initial trace

The mild equation gives u(t,x) = S(t)u0(x) + correction(t,x) where:
- S(t)u0 -> u0 as t -> 0+ uniformly (semigroup approx identity)
- correction -> 0 as t -> 0+ (Duhamel integrals over [0,t])

BLOCKER: The spectral approx-identity `intervalFullSemigroup_tendsto_id_at_zero`
gives pointwise convergence under l1 + pointwise reconstruction hypotheses.
Upgrading to uniform convergence (supNorm) needs either:
  (a) uniform version of the spectral approximate identity, or
  (b) equicontinuity + Arzela-Ascoli on [0,1] compact.
Neither is currently in the repository. -/

theorem mildSolution_initialTrace (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) :
    InitialTrace intervalDomain u₀ D.u := by
  sorry

/-! ## Sorry 6: Parabolic PDE (Schauder bootstrap)

BLOCKER: Differentiating the Duhamel integral representation requires
the source to be time-Holder, which requires u to be time-Holder,
creating a bootstrap loop. The atom IntervalDuhamelClosedC2 breaks this
for sources that are a priori time-C1, but proving time-C1 of the mild
solution source needs interior parabolic regularity not yet formalized. -/

theorem mildSolution_parabolicPDE (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) :
    ∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α) := by
  sorry

/-! ## Sorry 4: Elliptic PDE for v

The resolver satisfies the elliptic equation spectrally:
- `intervalNeumannResolverRLap_elliptic_identity`:
    RLap p u y = mu * R p u y - sourceValue p u y
  which rearranges to laplacian(Ru) - mu*(Ru) + sourceValue = 0.

BLOCKER: Connecting `intervalDomainLaplacian (resolverR ...)` to
`intervalNeumannResolverRLap` requires SourceCoeffQuadraticDecay
(C2 of source), which is circular with the regularity bootstrap. -/

theorem mildChemical_ellipticPDE (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) :
    ∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      0 = intervalDomain.laplacian
            (mildChemicalConcentration p D.u t) x
          - p.μ * mildChemicalConcentration p D.u t x
          + p.ν * (D.u t x) ^ p.γ := by
  sorry

/-! ## Sorry 5: Neumann BC

v-part: The resolver R(u) = sum v_hat_k cos(k pi x) is a cosine series.
- resolverGradReal_zero/one: gradient series vanishes at 0,1 (pure trig)
- BLOCKER: connecting to intervalDomainNormalDeriv requires
  resolverR_hasDerivAt_grad (gradient majorant summability from C2 source)

u-part: The mild solution is S(t)u0 + Duhamel integrals, each from cosine
kernels with Neumann BC. Same regularity BLOCKER. -/

theorem mildSolution_neumannBC (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) :
    ∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.boundary →
      intervalDomain.normalDeriv (D.u t) x = 0 ∧
      intervalDomain.normalDeriv
        (mildChemicalConcentration p D.u t) x = 0 := by
  sorry

/-! ## Sorry 7: Classical regularity -/

theorem mildSolution_classicalRegularity (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) :
    intervalDomainClassicalRegularity D.T D.u
      (mildChemicalConcentration p D.u) := by
  sorry

end ShenWork.IntervalMildToClassical
