/- Exact Route-A derivative of the faithful general-`m` flux remainder. -/
import ShenWork.Paper3.IntervalDomainPhysicalFluxRemainderGeneralM
import ShenWork.Paper3.IntervalDomainChemotaxisRemainderModeGeneralM
import ShenWork.Paper3.IntervalDomainFluxRemainderDerivative
import ShenWork.Paper3.IntervalDomainSignalC2Bridge
import ShenWork.Paper3.IntervalDomainSensitivityDerivative
import ShenWork.Paper2.IntervalDomainMClassicalRestart
import ShenWork.Paper2.IntervalSpectralBasicLemmas

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.IntervalNeumannFullKernel
open scoped Topology

noncomputable section

/-- On an interior positive-time slice of a faithful `intervalDomainM`
solution, the physical chemotaxis flux remainder has the exact seven-term
Route-A derivative.  The first derivative factor is the chain-rule value
`m u^(m-1) u_x`; strict positivity of the classical slice handles arbitrary
positive real `m` without a spurious `m = 1` restriction. -/
theorem solution_paper3ChemFluxRemainderProfileM_hasDerivAt_routeA_generalM
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (Hsplit : IntervalSolutionSignalSplitData p uStar (u t))
    (Hlin : ResolvedSourceProfileRegularity
      (paper3IntervalEllipticLinearProfile p uStar (u t)))
    (Hquad : ResolvedSourceProfileRegularity
      (paper3IntervalEllipticRemainderProfile p uStar (u t)))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (paper3ChemFluxRemainderProfileM p uStar vStar (u t) (v t))
      (paper3EliminatedFluxRemainderDerivativeValue
        (uStar ^ p.m) (paper3SensitivityFactor p.β vStar)
        ((intervalDomainLift (u t) x) ^ p.m - uStar ^ p.m)
        (p.m * (intervalDomainLift (u t) x) ^ (p.m - 1) *
          deriv (intervalDomainLift (u t)) x)
        (paper3LinearSignalGradient p uStar (u t) x)
        (paper3LinearSignalLaplacian p uStar (u t) x)
        (paper3QuadraticSignalGradient p uStar (u t) x)
        (paper3QuadraticSignalLaplacian p uStar (u t) x)
        (paper3SensitivityFactor p.β (intervalDomainLift (v t) x) -
          paper3SensitivityFactor p.β vStar)
        (paper3SensitivityDerivativeValue p.β
          (intervalDomainLift (v t) x)
          (deriv (intervalDomainLift (v t)) x))
        (paper3LinearSignalGradient p uStar (u t) x +
          paper3QuadraticSignalGradient p uStar (u t) x)
        (paper3LinearSignalLaplacian p uStar (u t) x +
          paper3QuadraticSignalLaplacian p uStar (u t) x)) x := by
  let wpow : ℝ → ℝ := fun y =>
    (intervalDomainLift (u t) y) ^ p.m - uStar ^ p.m
  let z1x : ℝ → ℝ := paper3LinearSignalGradient p uStar (u t)
  let z2x : ℝ → ℝ := paper3QuadraticSignalGradient p uStar (u t)
  let q : ℝ → ℝ := fun y =>
    paper3SensitivityFactor p.β (intervalDomainLift (v t) y)
  let zx : ℝ → ℝ := fun y => z1x y + z2x y
  let three : ℝ → ℝ :=
    paper3EliminatedFluxRemainderThreeTermProfile (uStar ^ p.m)
      (paper3SensitivityFactor p.β vStar) wpow z1x z2x q zx
  have hC2u : ContDiffOn ℝ 2 (intervalDomainLift (u t))
      (Set.Ioo (0 : ℝ) 1) := (hsol.regularity.1 t ht).1
  have hC2v : ContDiffOn ℝ 2 (intervalDomainLift (v t))
      (Set.Ioo (0 : ℝ) 1) := (hsol.regularity.1 t ht).2
  have huDiff : DifferentiableAt ℝ (intervalDomainLift (u t)) x :=
    (hC2u.differentiableOn (by norm_num)).differentiableAt
      (IsOpen.mem_nhds isOpen_Ioo hx)
  have hvDiff : DifferentiableAt ℝ (intervalDomainLift (v t)) x :=
    (hC2v.differentiableOn (by norm_num)).differentiableAt
      (IsOpen.mem_nhds isOpen_Ioo hx)
  have hu_pos : 0 < intervalDomainLift (u t) x := by
    simpa [intervalDomainLift, Set.Ioo_subset_Icc_self hx] using
      hsol.u_pos'
        (x := (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint))
        ht.1 ht.2
  have hpow : HasDerivAt
      (fun y => (intervalDomainLift (u t) y) ^ p.m)
      (p.m * (intervalDomainLift (u t) x) ^ (p.m - 1) *
        deriv (intervalDomainLift (u t)) x) x := by
    exact (Real.hasDerivAt_rpow_const
      (x := intervalDomainLift (u t) x) (p := p.m)
      (Or.inl hu_pos.ne')).comp x huDiff.hasDerivAt
  have hwpow : HasDerivAt wpow
      (p.m * (intervalDomainLift (u t) x) ^ (p.m - 1) *
        deriv (intervalDomainLift (u t)) x) x := by
    simpa [wpow] using hpow.sub_const (uStar ^ p.m)
  have hz1 := paper3LinearSignalGradient_hasDerivAt_laplacian
    p uStar (u t) Hlin hx
  have hz2 := paper3QuadraticSignalGradient_hasDerivAt_laplacian
    p uStar (u t) Hquad hx
  have hv_nonneg : 0 ≤ intervalDomainLift (v t) x :=
    lift_v_nonneg_Icc hsol ht.1 ht.2 x (Set.Ioo_subset_Icc_self hx)
  have hq := paper3SensitivityFactor_comp_hasDerivAt
    (beta := p.β) hvDiff.hasDerivAt (by linarith)
      (rfl : intervalDomainLift (v t) x = intervalDomainLift (v t) x)
  have hthree : HasDerivAt three
      (paper3EliminatedFluxRemainderDerivativeValue
        (uStar ^ p.m) (paper3SensitivityFactor p.β vStar)
        ((intervalDomainLift (u t) x) ^ p.m - uStar ^ p.m)
        (p.m * (intervalDomainLift (u t) x) ^ (p.m - 1) *
          deriv (intervalDomainLift (u t)) x)
        (paper3LinearSignalGradient p uStar (u t) x)
        (paper3LinearSignalLaplacian p uStar (u t) x)
        (paper3QuadraticSignalGradient p uStar (u t) x)
        (paper3QuadraticSignalLaplacian p uStar (u t) x)
        (paper3SensitivityFactor p.β (intervalDomainLift (v t) x) -
          paper3SensitivityFactor p.β vStar)
        (paper3SensitivityDerivativeValue p.β
          (intervalDomainLift (v t) x)
          (deriv (intervalDomainLift (v t)) x))
        (paper3LinearSignalGradient p uStar (u t) x +
          paper3QuadraticSignalGradient p uStar (u t) x)
        (paper3LinearSignalLaplacian p uStar (u t) x +
          paper3QuadraticSignalLaplacian p uStar (u t) x)) x := by
    apply paper3EliminatedFluxRemainderThreeTermProfile_hasDerivAt
      hwpow hz1 hz2 hq (hz1.add hz2)
    all_goals rfl
  have heqOn : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      paper3ChemFluxRemainderProfileM p uStar vStar (u t) (v t) y =
        three y := by
    intro y hy
    have hphys := solution_paper3ChemFluxRemainderProfileM_eq_threeTerms_generalM
      hsol ht heq Hsplit (Set.Ioo_subset_Icc_self hy)
    have hgrad := solution_lift_v_deriv_eq_signalGradientComponents_generalM
      hsol ht heq Hsplit (Set.Ioo_subset_Icc_self hy)
    dsimp [three, paper3EliminatedFluxRemainderThreeTermProfile,
      wpow, z1x, z2x, q, zx]
    rw [hphys, hgrad]
    ring
  have hevent :
      paper3ChemFluxRemainderProfileM p uStar vStar (u t) (v t) =ᶠ[𝓝 x]
        three := by
    refine Filter.eventuallyEq_of_mem
      (IsOpen.mem_nhds isOpen_Ioo hx) ?_
    intro y hy
    exact heqOn y hy
  exact hthree.congr_of_eventuallyEq hevent

/-- Modal identification of the faithful general-`m` Route-A remainder with
the cosine coefficient of its physical differentiated flux. -/
theorem paper3ChemotaxisRemainderCoeffM_eq_routeA_cosine_generalM
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (Hsplit : IntervalSolutionSignalSplitData p uStar (u t))
    (Hlin : ResolvedSourceProfileRegularity
      (paper3IntervalEllipticLinearProfile p uStar (u t)))
    (Hquad : ResolvedSourceProfileRegularity
      (paper3IntervalEllipticRemainderProfile p uStar (u t)))
    (hderivInt : IntervalIntegrable
      (deriv (paper3ChemFluxRemainderProfileM
        p uStar vStar (u t) (v t))) volume 0 1)
    (k : ℕ) :
    paper3ChemotaxisRemainderCoeffM p uStar vStar u v t k =
      cosineCoeffs (fun x => -p.χ₀ *
        deriv (paper3ChemFluxRemainderProfileM
          p uStar vStar (u t) (v t)) x) k := by
  let g : ℝ → ℝ :=
    paper3ChemFluxRemainderProfileM p uStar vStar (u t) (v t)
  have hfluxCont : ContinuousOn (intervalFluxM p (u t) (v t))
      (Set.Icc (0 : ℝ) 1) :=
    (fluxM_contDiffOn_Icc hsol ht.1 ht.2).continuousOn
  have hlinGradCont := paper3LinearSignalGradient_continuous
    p uStar (u t) Hlin
  have hlinearCont : ContinuousOn
      (paper3LinearChemFluxProfile p uStar vStar (u t))
      (Set.Icc (0 : ℝ) 1) := by
    unfold paper3LinearChemFluxProfile
    fun_prop
  have hgCont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    exact hfluxCont.sub hlinearCont
  have hfluxInt : IntervalIntegrable
      (intervalFluxM p (u t) (v t)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hfluxCont
  have hlinearInt : IntervalIntegrable
      (paper3LinearChemFluxProfile p uStar vStar (u t)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hlinearCont
  obtain ⟨hflux0, hflux1⟩ := fluxM_endpoint_zero hsol ht.1 ht.2
  have hlin0 : paper3LinearChemFluxProfile p uStar vStar (u t) 0 = 0 := by
    simp [paper3LinearChemFluxProfile, paper3LinearSignalGradient]
  have hlin1 : paper3LinearChemFluxProfile p uStar vStar (u t) 1 = 0 := by
    simp [paper3LinearChemFluxProfile, paper3LinearSignalGradient]
  have hg0 : g 0 = 0 := by
    dsimp [g, paper3ChemFluxRemainderProfileM]
    rw [hflux0, hlin0, zero_sub]
    norm_num
  have hg1 : g 1 = 0 := by
    dsimp [g, paper3ChemFluxRemainderProfileM]
    rw [hflux1, hlin1, zero_sub]
    norm_num
  have hgd : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt g (deriv g x) x := by
    intro x hx
    have h :=
      solution_paper3ChemFluxRemainderProfileM_hasDerivAt_routeA_generalM
        hsol ht heq Hsplit Hlin Hquad hx
    exact h.congr_deriv h.deriv.symm
  have hfreq :=
    ShenWork.Paper2.BFormPositiveDatumNegPart.freq_sineInner_eq_cosineCoeffs_deriv
      (g := g) (s_g := (∅ : Set ℝ)) Set.countable_empty hgCont
      (by simpa using hgd) hderivInt hg0 hg1 k
  have hchem := paper3ChemotaxisRemainderCoeffM_eq_fluxRemainder_generalM
    p heq u v t k
    ((hsol.regularity.2.2.2.2.1 t ht).1.1).continuousOn
    Hsplit.linear_source_sq_summable hfluxInt hlinearInt
  have hscale := cosineCoeffs_const_mul_of_intervalIntegrable
    (-p.χ₀) k hderivInt
  dsimp [g] at hfreq
  rw [hchem, hfreq, ← hscale]

#print axioms
  solution_paper3ChemFluxRemainderProfileM_hasDerivAt_routeA_generalM
#print axioms paper3ChemotaxisRemainderCoeffM_eq_routeA_cosine_generalM

end


end ShenWork.Paper3
