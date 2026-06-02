/-
  ShenWork/Paper2/IntervalMildToClassical.lean

  T7e bridge: GradientMildSolutionData -> RegularityBootstrap -> localExistence.

  Route A (ChatGPT R2): new direct bridge that consumes the gradient-form mild
  solution, bypassing the old intervalDuhamelOperator entirely.

  **Status (post-reduction):**
  - Sorry 3 (InitialTrace): 1 sorry -- semigroup approx identity + Duhamel->0
  - Sorry 4 (Elliptic PDE): 1 sorry -- SourceCoeffQuadraticDecay for mild sol
  - Sorry 5 (Neumann BC): 1 sorry -- normalDeriv of mild sol at boundary
  - Sorry 6 (Parabolic PDE): 1 sorry -- Schauder bootstrap
  - Sorry 7 (Classical regularity): 1 sorry -- full regularity bundle
-/
import ShenWork.Paper2.IntervalMildPicard
import ShenWork.PDE.IntervalDomainExistence
import ShenWork.PDE.IntervalResolverPositivity
import ShenWork.Paper2.Statements
import ShenWork.PDE.IntervalResolverLaplacianBridge
import ShenWork.PDE.IntervalCosineSliceRegularity
import ShenWork.PDE.IntervalFullSemigroupNeumann

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

/-! ## Sorry 3: Initial trace -/

theorem mildSolution_initialTrace (p : CM2Params)
    {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀) :
    InitialTrace intervalDomain u₀ D.u := by
  -- The mild equation gives u(t,x) = S(t)u0(x) + correction(t,x).
  -- The Duhamel corrections are bounded by C*sqrt(t) + C*t -> 0.
  -- The semigroup part S(t)u0 -> u0 uniformly needs the heat kernel
  -- approximate identity in L-infinity norm.
  -- BLOCKER: uniform semigroup convergence not yet in the repository.
  sorry

/-! ## Sorry 6: Parabolic PDE (Schauder bootstrap) -/

theorem mildSolution_parabolicPDE (p : CM2Params)
    {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀) :
    ∀ t x, 0 < t -> t < D.T -> x ∈ intervalDomain.inside ->
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α) := by
  -- BLOCKER: Schauder bootstrap. Differentiating the Duhamel integral
  -- requires time-Holder continuity of the source, which requires
  -- time-Holder of u, creating a bootstrap loop.
  sorry

/-! ## Sorry 4: Elliptic PDE for v -/

theorem mildChemical_ellipticPDE (p : CM2Params)
    {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀) :
    ∀ t x, 0 < t -> t < D.T -> x ∈ intervalDomain.inside ->
      0 = intervalDomain.laplacian
            (mildChemicalConcentration p D.u t) x
          - p.μ * mildChemicalConcentration p D.u t x
          + p.ν * (D.u t x) ^ p.γ := by
  -- The resolver satisfies the elliptic equation spectrally:
  -- intervalNeumannResolverRLap_elliptic_identity gives
  --   RLap = mu * R - sourceValue
  -- i.e. laplacian(R) - mu*R + sourceValue = 0.
  -- BLOCKER: Connecting intervalDomainLaplacian to RLap requires
  -- SourceCoeffQuadraticDecay (C2 of source), circular with sorry 7.
  sorry

/-! ## Sorry 5: Neumann BC -/

theorem mildSolution_neumannBC (p : CM2Params)
    {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀) :
    ∀ t x, 0 < t -> t < D.T -> x ∈ intervalDomain.boundary ->
      intervalDomain.normalDeriv (D.u t) x = 0 ∧
      intervalDomain.normalDeriv
        (mildChemicalConcentration p D.u t) x = 0 := by
  -- The mild solution lift agrees with the Duhamel formula on [0,1].
  -- Each semigroup term S(t)f is even about 0 and 1
  -- (IntervalFullSemigroupNeumann), hence has derivative 0 at endpoints.
  -- The gradient Duhamel term needs careful analysis: its contribution
  -- to the boundary derivative involves second-order effects that
  -- cancel by the self-consistency of the mild equation.
  -- BLOCKER: derivWithin of the lift at endpoints requires showing the
  -- lift is differentiable from the appropriate side, which needs C1
  -- regularity of the mild solution up to the boundary.
  sorry

/-! ## Sorry 7: Classical regularity -/

theorem mildSolution_classicalRegularity (p : CM2Params)
    {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀) :
    intervalDomainClassicalRegularity D.T D.u
      (mildChemicalConcentration p D.u) := by
  -- The 9-conjunct classical regularity bundle requires:
  -- (1-2) Sup-norm derivative nonpositive (comparison principle)
  -- (3) Spatial C2 on open interior
  -- (4) Time differentiability + continuity
  -- (5-6) Joint space-time continuity of time-derivative
  -- (7) Closed-domain C2 + genuine endpoint Neumann values
  -- (8) Closed-slab joint continuity of time-derivative
  -- (9) Joint space-time continuity of solution field
  -- All conjuncts require the Schauder bootstrap (sorry 6).
  sorry

end ShenWork.IntervalMildToClassical
