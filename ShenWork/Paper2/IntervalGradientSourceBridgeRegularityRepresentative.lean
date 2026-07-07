import ShenWork.Paper2.IntervalGradientSourceBridgeRegularity
import ShenWork.PDE.IntervalEllipticCharacterization

open MeasureTheory intervalIntegral
open scoped Topology

noncomputable section

namespace ShenWork.Paper2.IntervalGradientSourceBridgeOpen

open Set
open ShenWork.IntervalDomain
  (intervalDomain intervalDomainPoint intervalDomainLift intervalDomainChemotaxisDiv
    intervalDomainClassicalRegularity)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceLift
    resolver_lift_deriv_eq_resolverGradReal_of_sourceDecay
    sourceValue_eq_powerSource_of_closedC2_neumann)
open ShenWork.IntervalCoupledClassicalBallEstimates (intervalChemDivRepr)
open ShenWork.IntervalResolverLaplacianBridge
  (intervalNeumannResolverRLap intervalNeumannResolverSourceValue
    intervalNeumannResolverRLap_elliptic_identity resolverGradReal_hasDerivAt_RLap)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration mildChemical_nonneg)
open ShenWork.IntervalMildSourceDecay
  (sourceCoeffQuadraticDecay_of_mildSolution_of_closedC2_neumann)
open ShenWork.IntervalEllipticCharacterization
  (continuousOn_derivWithin_of_contDiffOn_two deriv_eq_derivWithin_interior)

/-- Closed-interval continuous representative for the chemotaxis-divergence
source, using `derivWithin` at the spatial endpoints.

On `(0,1)` it agrees with the physical product-rule expression, but unlike the
ordinary-`deriv` expression it is directly continuous on `[0,1]` from closed
`C²` slice regularity. -/
def gradientBridgeChemDivWithinRep
    (p : CM2Params) (u v : intervalDomainPoint → ℝ) (x : ℝ) : ℝ :=
  derivWithin (intervalDomainLift u) (Set.Icc (0 : ℝ) 1) x *
      derivWithin (intervalDomainLift v) (Set.Icc (0 : ℝ) 1) x /
    (1 + intervalDomainLift v x) ^ p.β +
  intervalDomainLift u x *
      (p.μ * intervalDomainLift v x -
        p.ν * (intervalDomainLift u x) ^ p.γ) /
    (1 + intervalDomainLift v x) ^ p.β -
  p.β * intervalDomainLift u x *
      (derivWithin (intervalDomainLift v) (Set.Icc (0 : ℝ) 1) x) ^ 2 /
    (1 + intervalDomainLift v x) ^ (p.β + 1)

/-- The `derivWithin` representative is continuous on the closed interval from
closed spatial `C²`, positivity of `u`, and nonnegativity of `v`. -/
theorem gradientBridgeChemDivWithinRep_continuousOn_Icc
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    (hC2u : ContDiffOn ℝ 2 (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    (hC2v : ContDiffOn ℝ 2 (intervalDomainLift v) (Set.Icc (0 : ℝ) 1))
    (hu_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift u x)
    (hv_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift v x) :
    ContinuousOn (gradientBridgeChemDivWithinRep p u v) (Set.Icc (0 : ℝ) 1) := by
  have hu_cont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1) :=
    hC2u.continuousOn
  have hv_cont : ContinuousOn (intervalDomainLift v) (Set.Icc (0 : ℝ) 1) :=
    hC2v.continuousOn
  have hdu_cont :
      ContinuousOn (derivWithin (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
        (Set.Icc (0 : ℝ) 1) :=
    continuousOn_derivWithin_of_contDiffOn_two hC2u
  have hdv_cont :
      ContinuousOn (derivWithin (intervalDomainLift v) (Set.Icc (0 : ℝ) 1))
        (Set.Icc (0 : ℝ) 1) :=
    continuousOn_derivWithin_of_contDiffOn_two hC2v
  have hbase : ContinuousOn (fun x : ℝ => 1 + intervalDomainLift v x)
      (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.add hv_cont
  have hbase_pos :
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < 1 + intervalDomainLift v x := by
    intro x hx
    have := hv_nonneg x hx
    linarith
  have hden_beta :
      ContinuousOn (fun x : ℝ => (1 + intervalDomainLift v x) ^ p.β)
        (Set.Icc (0 : ℝ) 1) :=
    hbase.rpow_const (fun x hx => Or.inl (ne_of_gt (hbase_pos x hx)))
  have hden_beta_ne :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        (1 + intervalDomainLift v x) ^ p.β ≠ 0 :=
    fun x hx => ne_of_gt (Real.rpow_pos_of_pos (hbase_pos x hx) _)
  have hden_beta_one :
      ContinuousOn (fun x : ℝ => (1 + intervalDomainLift v x) ^ (p.β + 1))
        (Set.Icc (0 : ℝ) 1) :=
    hbase.rpow_const (fun x hx => Or.inl (ne_of_gt (hbase_pos x hx)))
  have hden_beta_one_ne :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        (1 + intervalDomainLift v x) ^ (p.β + 1) ≠ 0 :=
    fun x hx => ne_of_gt (Real.rpow_pos_of_pos (hbase_pos x hx) _)
  have hu_pow :
      ContinuousOn (fun x : ℝ => (intervalDomainLift u x) ^ p.γ)
        (Set.Icc (0 : ℝ) 1) :=
    hu_cont.rpow_const (fun x hx => Or.inl (ne_of_gt (hu_pos x hx)))
  have hterm1 :
      ContinuousOn
        (fun x : ℝ =>
          derivWithin (intervalDomainLift u) (Set.Icc (0 : ℝ) 1) x *
              derivWithin (intervalDomainLift v) (Set.Icc (0 : ℝ) 1) x /
            (1 + intervalDomainLift v x) ^ p.β)
        (Set.Icc (0 : ℝ) 1) :=
    (hdu_cont.mul hdv_cont).div hden_beta hden_beta_ne
  have hterm2 :
      ContinuousOn
        (fun x : ℝ =>
          intervalDomainLift u x *
              (p.μ * intervalDomainLift v x -
                p.ν * (intervalDomainLift u x) ^ p.γ) /
            (1 + intervalDomainLift v x) ^ p.β)
        (Set.Icc (0 : ℝ) 1) := by
    have hsource :
        ContinuousOn
          (fun x : ℝ =>
            p.μ * intervalDomainLift v x -
              p.ν * (intervalDomainLift u x) ^ p.γ)
          (Set.Icc (0 : ℝ) 1) :=
      (continuousOn_const.mul hv_cont).sub (continuousOn_const.mul hu_pow)
    exact (hu_cont.mul hsource).div hden_beta hden_beta_ne
  have hterm3 :
      ContinuousOn
        (fun x : ℝ =>
          p.β * intervalDomainLift u x *
              (derivWithin (intervalDomainLift v) (Set.Icc (0 : ℝ) 1) x) ^ 2 /
            (1 + intervalDomainLift v x) ^ (p.β + 1))
        (Set.Icc (0 : ℝ) 1) :=
    ((continuousOn_const.mul hu_cont).mul (hdv_cont.pow 2)).div
      hden_beta_one hden_beta_one_ne
  simpa [gradientBridgeChemDivWithinRep] using (hterm1.add hterm2).sub hterm3

/-- Regularity-only version of the interior chem-div product-rule expansion
for the concrete resolver chemical concentration. -/
theorem intervalDomainChemotaxisDiv_eq_chemDivRepr_interior_of_mildRegularity
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hreg : intervalDomainClassicalRegularity D.T D.u
      (coupledChemicalConcentration p D.u))
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) D.T)
    {y : intervalDomainPoint} (hy_int : y.1 ∈ Set.Ioo (0 : ℝ) 1) :
    intervalDomainChemotaxisDiv p (D.u s) (coupledChemicalConcentration p D.u s) y =
      intervalChemDivRepr p (D.u s) (coupledChemicalConcentration p D.u s) y := by
  classical
  set y₀ : ℝ := y.1 with hy₀
  have hy_Icc : y₀ ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy_int
  have hC2u_open : ContDiffOn ℝ 2 (intervalDomainLift (D.u s)) (Set.Ioo (0:ℝ) 1) :=
    (hreg.1 s hs).1
  have hC2v_open :
      ContDiffOn ℝ 2
        (intervalDomainLift (coupledChemicalConcentration p D.u s))
        (Set.Ioo (0:ℝ) 1) :=
    (hreg.1 s hs).2
  have hC2u_closed : ContDiffOn ℝ 2 (intervalDomainLift (D.u s)) (Set.Icc (0 : ℝ) 1) :=
    (hreg.2.2.2.2.1 s hs).1.1
  have hN0 : Filter.Tendsto (deriv (intervalDomainLift (D.u s)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    (hreg.2.2.2.1 s hs).1.1
  have hN1 : Filter.Tendsto (deriv (intervalDomainLift (D.u s)))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) :=
    (hreg.2.2.2.1 s hs).1.2
  have hdecay : SourceCoeffQuadraticDecay p (D.u s) :=
    sourceCoeffQuadraticDecay_of_mildSolution_of_closedC2_neumann
      p D hs.1 hs.2.le hC2u_closed hN0 hN1
  have hU_diff : DifferentiableAt ℝ (intervalDomainLift (D.u s)) y₀ :=
    (hC2u_open.differentiableOn (by norm_num)).differentiableAt
      (IsOpen.mem_nhds isOpen_Ioo hy_int)
  have hU_has : HasDerivAt (intervalDomainLift (D.u s))
      (deriv (intervalDomainLift (D.u s)) y₀) y₀ := hU_diff.hasDerivAt
  have hV_diff :
      DifferentiableAt ℝ
        (intervalDomainLift (coupledChemicalConcentration p D.u s)) y₀ :=
    (hC2v_open.differentiableOn (by norm_num)).differentiableAt
      (IsOpen.mem_nhds isOpen_Ioo hy_int)
  have hdv_eq :
      deriv (intervalDomainLift (coupledChemicalConcentration p D.u s)) y₀ =
        resolverGradReal p (D.u s) y₀ := by
    simpa [coupledChemicalConcentration] using
      resolver_lift_deriv_eq_resolverGradReal_of_sourceDecay
        (p := p) (u := D.u s) hdecay hy_int
  set g₀ : ℝ := resolverGradReal p (D.u s) y₀ with hg₀_def
  have hV_has :
      HasDerivAt (intervalDomainLift (coupledChemicalConcentration p D.u s))
        g₀ y₀ := by
    have h := hV_diff.hasDerivAt
    rw [hdv_eq] at h
    exact h
  have hdv_eqOn : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      deriv (intervalDomainLift (coupledChemicalConcentration p D.u s)) x =
        resolverGradReal p (D.u s) x := by
    intro x hx
    simpa [coupledChemicalConcentration] using
      resolver_lift_deriv_eq_resolverGradReal_of_sourceDecay
        (p := p) (u := D.u s) hdecay hx
  have hdv_eventuallyEq :
      deriv (intervalDomainLift (coupledChemicalConcentration p D.u s))
        =ᶠ[𝓝 y₀] resolverGradReal p (D.u s) := by
    refine Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Ioo hy_int) ?_
    intro x hx
    exact hdv_eqOn x hx
  have hRgrad_has : HasDerivAt (fun z : ℝ => resolverGradReal p (D.u s) z)
      (intervalNeumannResolverRLap p (D.u s) ⟨y₀, hy_Icc⟩) y₀ :=
    resolverGradReal_hasDerivAt_RLap hdecay hy_Icc
  set H₀ : ℝ := intervalNeumannResolverRLap p (D.u s) ⟨y₀, hy_Icc⟩ with hH₀_def
  have hW_has :
      HasDerivAt
        (deriv (intervalDomainLift (coupledChemicalConcentration p D.u s))) H₀ y₀ :=
    hRgrad_has.congr_of_eventuallyEq hdv_eventuallyEq
  have hv_nonneg :
      0 ≤ intervalDomainLift (coupledChemicalConcentration p D.u s) y₀ := by
    have hv_point :
        0 ≤ coupledChemicalConcentration p D.u s ⟨y₀, hy_Icc⟩ := by
      simpa [coupledChemicalConcentration, mildChemicalConcentration] using
        mildChemical_nonneg (p := p) (T := D.T) (u := D.u)
          D.hnonneg D.hcont hs.1 hs.2.le ⟨y₀, hy_Icc⟩
    simpa [intervalDomainLift, hy_Icc] using hv_point
  set V₀ : ℝ := intervalDomainLift (coupledChemicalConcentration p D.u s) y₀
    with hV₀_def
  have hV₀_pos : 0 < 1 + V₀ := by linarith
  have hV₀_ne : (1 + V₀) ≠ 0 := ne_of_gt hV₀_pos
  have hOnePlusV_has :
      HasDerivAt
        (fun z : ℝ => 1 + intervalDomainLift (coupledChemicalConcentration p D.u s) z)
        g₀ y₀ := by
    have h := (hasDerivAt_const y₀ (1 : ℝ)).add hV_has
    have : (fun z : ℝ =>
          (1 : ℝ) + intervalDomainLift (coupledChemicalConcentration p D.u s) z)
        = (fun _ : ℝ => (1 : ℝ)) +
          intervalDomainLift (coupledChemicalConcentration p D.u s) := by
      funext z
      simp [Pi.add_apply]
    rw [this]
    simpa using h
  have hpow_at : HasDerivAt (fun x : ℝ => x ^ p.β)
      (p.β * (1 + V₀) ^ (p.β - 1)) (1 + V₀) :=
    Real.hasDerivAt_rpow_const (Or.inl hV₀_ne)
  have hD_has :
      HasDerivAt
        (fun z : ℝ =>
          (1 + intervalDomainLift (coupledChemicalConcentration p D.u s) z) ^ p.β)
        (p.β * (1 + V₀) ^ (p.β - 1) * g₀) y₀ := by
    have hcomp := hpow_at.comp y₀ hOnePlusV_has
    simpa [Function.comp] using hcomp
  set D₀ : ℝ := (1 + V₀) ^ p.β with hD₀_def
  have hD₀_pos : 0 < D₀ := Real.rpow_pos_of_pos hV₀_pos _
  have hD₀_ne : D₀ ≠ 0 := ne_of_gt hD₀_pos
  have hN_has : HasDerivAt
      (fun z : ℝ =>
        intervalDomainLift (D.u s) z *
          deriv (intervalDomainLift (coupledChemicalConcentration p D.u s)) z)
      (deriv (intervalDomainLift (D.u s)) y₀ *
          deriv (intervalDomainLift (coupledChemicalConcentration p D.u s)) y₀
        + intervalDomainLift (D.u s) y₀ * H₀) y₀ := by
    simpa using hU_has.mul hW_has
  have hQ_has : HasDerivAt
      (fun z : ℝ =>
        intervalDomainLift (D.u s) z *
            deriv (intervalDomainLift (coupledChemicalConcentration p D.u s)) z /
          (1 + intervalDomainLift (coupledChemicalConcentration p D.u s) z) ^ p.β)
      (((deriv (intervalDomainLift (D.u s)) y₀ *
              deriv (intervalDomainLift (coupledChemicalConcentration p D.u s)) y₀
            + intervalDomainLift (D.u s) y₀ * H₀) * D₀
          - intervalDomainLift (D.u s) y₀ *
              deriv (intervalDomainLift (coupledChemicalConcentration p D.u s)) y₀ *
              (p.β * (1 + V₀) ^ (p.β - 1) * g₀))
          / D₀ ^ 2) y₀ := by
    have := hN_has.div hD_has hD₀_ne
    simpa using this
  have hLHS :
      intervalDomainChemotaxisDiv p (D.u s) (coupledChemicalConcentration p D.u s) y
        =
      (((deriv (intervalDomainLift (D.u s)) y₀ *
              deriv (intervalDomainLift (coupledChemicalConcentration p D.u s)) y₀
            + intervalDomainLift (D.u s) y₀ * H₀) * D₀
          - intervalDomainLift (D.u s) y₀ *
              deriv (intervalDomainLift (coupledChemicalConcentration p D.u s)) y₀ *
              (p.β * (1 + V₀) ^ (p.β - 1) * g₀))
          / D₀ ^ 2) := by
    unfold intervalDomainChemotaxisDiv
    exact hQ_has.deriv
  have hD₀_eq : D₀ = (1 + V₀) ^ p.β := hD₀_def
  have hrpow_neg_β : (1 + V₀) ^ (-p.β) = ((1 + V₀) ^ p.β)⁻¹ :=
    Real.rpow_neg hV₀_pos.le p.β
  have hrpow_neg_β_minus1 : (1 + V₀) ^ (-p.β - 1) =
      ((1 + V₀) ^ (p.β + 1))⁻¹ := by
    have h := Real.rpow_neg hV₀_pos.le (p.β + 1)
    have : -(p.β + 1) = -p.β - 1 := by ring
    rw [this] at h
    exact h
  have hD₀_sq : D₀ ^ 2 = (1 + V₀) ^ (2 * p.β) := by
    have h1 : D₀ ^ 2 = ((1 + V₀) ^ p.β) ^ (2 : ℕ) := by rw [hD₀_eq]
    rw [h1, ← Real.rpow_natCast ((1 + V₀) ^ p.β) 2,
        ← Real.rpow_mul hV₀_pos.le]
    congr 1
    push_cast
    ring
  have hrpow_combine : (1 + V₀) ^ (p.β - 1) / (1 + V₀) ^ (2 * p.β)
      = (1 + V₀) ^ (-p.β - 1) := by
    rw [← Real.rpow_sub hV₀_pos]
    congr 1
    ring
  have hRHS_simplify :
      (((deriv (intervalDomainLift (D.u s)) y₀ *
              deriv (intervalDomainLift (coupledChemicalConcentration p D.u s)) y₀
            + intervalDomainLift (D.u s) y₀ * H₀) * D₀
          - intervalDomainLift (D.u s) y₀ *
              deriv (intervalDomainLift (coupledChemicalConcentration p D.u s)) y₀ *
              (p.β * (1 + V₀) ^ (p.β - 1) * g₀))
          / D₀ ^ 2)
        = intervalChemDivRepr p (D.u s) (coupledChemicalConcentration p D.u s) y := by
    rw [hdv_eq]
    have hsplit :
        (((deriv (intervalDomainLift (D.u s)) y₀ * g₀
              + intervalDomainLift (D.u s) y₀ * H₀) * D₀
            - intervalDomainLift (D.u s) y₀ * g₀
                * (p.β * (1 + V₀) ^ (p.β - 1) * g₀)) / D₀ ^ 2)
        =
        (deriv (intervalDomainLift (D.u s)) y₀ * g₀ * (1 / D₀)
          + intervalDomainLift (D.u s) y₀ * H₀ * (1 / D₀))
            - p.β * intervalDomainLift (D.u s) y₀ * g₀ ^ 2
                * ((1 + V₀) ^ (p.β - 1) / D₀ ^ 2) := by
      have hD₀_sq_ne : D₀ ^ 2 ≠ 0 := pow_ne_zero 2 hD₀_ne
      field_simp
    rw [hsplit]
    have h1D₀ : (1 : ℝ) / D₀ = (1 + V₀) ^ (-p.β) := by
      rw [hrpow_neg_β, hD₀_eq, one_div]
    rw [h1D₀]
    rw [hD₀_sq, hrpow_combine]
    have hH₀_eq : H₀ = intervalNeumannResolverRLap p (D.u s) y := by
      rw [hH₀_def]
      rfl
    unfold intervalChemDivRepr
    rw [hg₀_def, hV₀_def, hH₀_eq, hy₀]
  rw [hLHS, hRHS_simplify]

/-- On the open spatial interior, the resolver-based chem-div representative
from the ball-estimate layer is the closed-interval `derivWithin`
representative built only from mild regularity and resolver identities. -/
theorem intervalChemDivRepr_eq_gradientBridgeChemDivWithinRep_interior_of_mildRegularity
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hreg : intervalDomainClassicalRegularity D.T D.u
      (coupledChemicalConcentration p D.u))
    {s x : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) D.T)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    intervalChemDivRepr p (D.u s) (coupledChemicalConcentration p D.u s)
        ⟨x, Set.Ioo_subset_Icc_self hx⟩ =
      gradientBridgeChemDivWithinRep p (D.u s)
        (coupledChemicalConcentration p D.u s) x := by
  classical
  let X : intervalDomainPoint := ⟨x, Set.Ioo_subset_Icc_self hx⟩
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
  have hC2u_closed : ContDiffOn ℝ 2 (intervalDomainLift (D.u s)) (Set.Icc (0 : ℝ) 1) :=
    (hreg.2.2.2.2.1 s hs).1.1
  have hN0 : Filter.Tendsto (deriv (intervalDomainLift (D.u s)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    (hreg.2.2.2.1 s hs).1.1
  have hN1 : Filter.Tendsto (deriv (intervalDomainLift (D.u s)))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) :=
    (hreg.2.2.2.1 s hs).1.2
  have hdecay : SourceCoeffQuadraticDecay p (D.u s) :=
    sourceCoeffQuadraticDecay_of_mildSolution_of_closedC2_neumann
      p D hs.1 hs.2.le hC2u_closed hN0 hN1
  have hpos_lift : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (D.u s) y := by
    intro y hy
    simpa [intervalDomainLift, hy] using
      D.hpos s hs.1 hs.2.le ⟨y, hy⟩
  have hgrad :
      deriv (intervalDomainLift (coupledChemicalConcentration p D.u s)) x =
        resolverGradReal p (D.u s) x := by
    simpa [coupledChemicalConcentration] using
      resolver_lift_deriv_eq_resolverGradReal_of_sourceDecay
        (p := p) (u := D.u s) hdecay hx
  have hduWithin :
      derivWithin (intervalDomainLift (D.u s)) (Set.Icc (0 : ℝ) 1) x =
        deriv (intervalDomainLift (D.u s)) x := by
    rw [← deriv_eq_derivWithin_interior (g := intervalDomainLift (D.u s)) hx]
  have hdvWithin :
      derivWithin (intervalDomainLift (coupledChemicalConcentration p D.u s))
          (Set.Icc (0 : ℝ) 1) x =
        deriv (intervalDomainLift (coupledChemicalConcentration p D.u s)) x := by
    rw [← deriv_eq_derivWithin_interior
      (g := intervalDomainLift (coupledChemicalConcentration p D.u s)) hx]
  have hR :
      ShenWork.PDE.intervalNeumannResolverR p (D.u s) X =
        intervalDomainLift (coupledChemicalConcentration p D.u s) x := by
    have hX : X = (⟨x, hxIcc⟩ : intervalDomainPoint) := Subtype.ext rfl
    rw [hX]
    simp [coupledChemicalConcentration, intervalDomainLift, hxIcc]
  have hsource :
      intervalNeumannResolverSourceValue p (D.u s) X =
        p.ν * (intervalDomainLift (D.u s) x) ^ p.γ := by
    simpa [X] using
      sourceValue_eq_powerSource_of_closedC2_neumann
        (p := p) hC2u_closed hN0 hN1 hpos_lift X
  have hrlap :
      intervalNeumannResolverRLap p (D.u s) X =
        p.μ * intervalDomainLift (coupledChemicalConcentration p D.u s) x -
          p.ν * (intervalDomainLift (D.u s) x) ^ p.γ := by
    rw [intervalNeumannResolverRLap_elliptic_identity hdecay X, hR, hsource]
  have hv_nonneg : 0 ≤ intervalDomainLift (coupledChemicalConcentration p D.u s) x := by
    have hv_point :
        0 ≤ coupledChemicalConcentration p D.u s X := by
      simpa [X, coupledChemicalConcentration, mildChemicalConcentration] using
        mildChemical_nonneg (p := p) (T := D.T) (u := D.u)
          D.hnonneg D.hcont hs.1 hs.2.le X
    simpa [X, intervalDomainLift, hxIcc] using hv_point
  have hbase_pos :
      0 < 1 + intervalDomainLift (coupledChemicalConcentration p D.u s) x := by
    linarith
  have hneg_beta :
      (1 + intervalDomainLift (coupledChemicalConcentration p D.u s) x) ^ (-p.β) =
        ((1 + intervalDomainLift (coupledChemicalConcentration p D.u s) x) ^ p.β)⁻¹ :=
    Real.rpow_neg hbase_pos.le p.β
  have hneg_beta_one :
      (1 + intervalDomainLift (coupledChemicalConcentration p D.u s) x) ^ (-p.β - 1) =
        ((1 + intervalDomainLift (coupledChemicalConcentration p D.u s) x) ^
          (p.β + 1))⁻¹ := by
    have h := Real.rpow_neg hbase_pos.le (p.β + 1)
    have hexp : -(p.β + 1) = -p.β - 1 := by ring
    rwa [hexp] at h
  change intervalChemDivRepr p (D.u s) (coupledChemicalConcentration p D.u s) X =
    gradientBridgeChemDivWithinRep p (D.u s)
      (coupledChemicalConcentration p D.u s) x
  unfold intervalChemDivRepr gradientBridgeChemDivWithinRep
  rw [← hgrad, hrlap, hduWithin, hdvWithin, hneg_beta, hneg_beta_one]
  simp only [X, div_eq_mul_inv]

/-- The literal coupled chem-div lift agrees on `(0,1)` with the closed
`derivWithin` representative produced from mild regularity. -/
theorem coupledChemDivSourceLift_eq_gradientBridgeChemDivWithinRep_Ioo_of_mildRegularity
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hreg : intervalDomainClassicalRegularity D.T D.u
      (coupledChemicalConcentration p D.u))
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) D.T) :
    Set.EqOn (coupledChemDivSourceLift p D.u s)
      (gradientBridgeChemDivWithinRep p (D.u s)
        (coupledChemicalConcentration p D.u s))
      (Set.Ioo (0 : ℝ) 1) := by
  intro x hx
  let X : intervalDomainPoint := ⟨x, Set.Ioo_subset_Icc_self hx⟩
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
  calc
    coupledChemDivSourceLift p D.u s x =
        intervalDomainChemotaxisDiv p (D.u s)
          (coupledChemicalConcentration p D.u s) X := by
      simp [coupledChemDivSourceLift, intervalDomainLift, X, hxIcc]
    _ = intervalChemDivRepr p (D.u s)
          (coupledChemicalConcentration p D.u s) X := by
      exact intervalDomainChemotaxisDiv_eq_chemDivRepr_interior_of_mildRegularity
        (p := p) D hreg hs (y := X) hx
    _ = gradientBridgeChemDivWithinRep p (D.u s)
          (coupledChemicalConcentration p D.u s) x := by
      exact
        intervalChemDivRepr_eq_gradientBridgeChemDivWithinRep_interior_of_mildRegularity
          (p := p) D hreg hs hx

/-- Mild regularity and the resolver structure produce the endpoint-insensitive
continuous chem-div representative required by the regularity-only
gradient-source bridge. -/
theorem coupledChemDivSourceLift_continuousRepresentative_of_mildRegularity
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hreg : intervalDomainClassicalRegularity D.T D.u
      (coupledChemicalConcentration p D.u))
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) D.T) :
    ∃ Gdiv : ℝ → ℝ,
      ContinuousOn Gdiv (Set.Icc (0 : ℝ) 1) ∧
      Set.EqOn (coupledChemDivSourceLift p D.u s) Gdiv (Set.Ioo (0 : ℝ) 1) := by
  refine
    ⟨gradientBridgeChemDivWithinRep p (D.u s)
        (coupledChemicalConcentration p D.u s), ?_, ?_⟩
  · have hC2u_closed :
        ContDiffOn ℝ 2 (intervalDomainLift (D.u s)) (Set.Icc (0 : ℝ) 1) :=
      (hreg.2.2.2.2.1 s hs).1.1
    have hC2v_closed :
        ContDiffOn ℝ 2
          (intervalDomainLift (coupledChemicalConcentration p D.u s))
          (Set.Icc (0 : ℝ) 1) :=
      (hreg.2.2.2.2.1 s hs).2.1
    have hu_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        0 < intervalDomainLift (D.u s) x := by
      intro x hx
      simpa [intervalDomainLift, hx] using
        D.hpos s hs.1 hs.2.le ⟨x, hx⟩
    have hv_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        0 ≤ intervalDomainLift (coupledChemicalConcentration p D.u s) x := by
      intro x hx
      have hv_point :
          0 ≤ coupledChemicalConcentration p D.u s ⟨x, hx⟩ := by
        simpa [coupledChemicalConcentration, mildChemicalConcentration] using
          mildChemical_nonneg (p := p) (T := D.T) (u := D.u)
            D.hnonneg D.hcont hs.1 hs.2.le ⟨x, hx⟩
      simpa [intervalDomainLift, hx] using hv_point
    exact gradientBridgeChemDivWithinRep_continuousOn_Icc
      (p := p) hC2u_closed hC2v_closed hu_pos hv_nonneg
  · exact coupledChemDivSourceLift_eq_gradientBridgeChemDivWithinRep_Ioo_of_mildRegularity
      (p := p) D hreg hs

end ShenWork.Paper2.IntervalGradientSourceBridgeOpen

namespace ShenWork.IntervalMildToLocalExistence

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainPoint intervalDomainClassicalRegularity)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceLift coupledLogisticSourceCoeffs)
open ShenWork.Paper2.IntervalGradientSourceBridgeOpen

set_option linter.style.longLine false in
/-- Source-certificate regularity bridge with the chem-div representative
discharged from mild regularity itself. -/
theorem gradientMildDuhamelTerms_eq_integral_mixedSpectralSource_of_gradientMildSolutionData_and_regular
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hreg : intervalDomainClassicalRegularity D.T D.u
      (coupledChemicalConcentration p D.u))
    {t x : ℝ} (ht0 : 0 < t) (htT : t < D.T) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    gradientMildChemotaxisDuhamelTerm p D.u t x
      + gradientMildLogisticDuhamelTerm p D.u t x
      =
    ∫ s in (0 : ℝ)..t,
      ((-p.χ₀) *
          unitIntervalSineHeatValue (t - s)
            (sineCoeffs (coupledChemDivSourceLift p D.u s)) x
        + unitIntervalCosineHeatValue (t - s)
            (coupledLogisticSourceCoeffs p D.u s) x) := by
  exact
    gradientMildDuhamelTerms_eq_integral_mixedSpectralSource_of_gradientMildSolutionData_and_regularRepr
      (p := p) (D := D) hreg
      (fun s hs =>
        coupledChemDivSourceLift_continuousRepresentative_of_mildRegularity
          (p := p) D hreg hs)
      ht0 htT hx

end ShenWork.IntervalMildToLocalExistence
