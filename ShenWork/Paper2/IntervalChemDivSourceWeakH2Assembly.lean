import ShenWork.PDE.IntervalSolutionEvenRepresentative
import ShenWork.Paper2.IntervalChemDivSpatialC2
import ShenWork.Paper2.IntervalDomainL2StaticVDifference
import ShenWork.PDE.IntervalProfileBoundaryRegularity
import ShenWork.Paper2.IntervalResolverHighRegularity

/-!
# Cosine reconstruction and the chem-div weak-H2 assembly

This file closes the two representation seams used by the chi-negative source
producer.

* A C2 Neumann interval slice is reconstructed on the closed interval by its
  cosine series.  The proof uses the public `IntervalCosineInversion` route via
  the clamped continuous representative; it does not use the private
  level-specific bootstrap theorem.
* The solution cosine representative and the resolver cosine representative
  feed the endpoint-insensitive product construction in
  `IntervalChemDivSpatialC2`.  That construction compares derivatives only on
  the open spatial interior and transfers the weak identity by almost-everywhere
  integral congruence, so no false endpoint derivative equality is asserted.
-/

open Set Filter Topology MeasureTheory

noncomputable section

namespace ShenWork.Paper2.IntervalChemDivSourceWeakH2Assembly

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs)
open ShenWork.CosineSpectrum
  (cosineMode)
open ShenWork.IntervalCosineInversion
  (intervalCosineCoeff_summable_abs intervalCosine_hasSum_pointwise reflCircle)
open ShenWork.IntervalFullKernelRegularity
  (eqOn_Icc_of_eqOn_Ioo_of_continuousOn)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceLift)
open ShenWork.PDE.IntervalSolutionEvenRepresentative
  (cosineSeriesLift intervalSolutionLiftU intervalSolutionLiftU_contDiff_three
   intervalSolutionLiftU_doublyEven)
open ShenWork.Paper2.IntervalResolverHighRegularity
  (intervalResolverLiftR intervalResolverLiftR_contDiff_four
   intervalResolverLiftR_even intervalResolverLiftR_reflect_one
   intervalResolverLiftR_one_add_pos_of_nonneg_on_Icc)
open ShenWork.PDE.IntervalMildSourceDecayHelper
  (IntervalWeakH2Neumann)

/-- A C2 Neumann interval datum is reconstructed by its cosine series on the
closed interval.  Endpoint equality is obtained from continuity after applying
the generic pointwise inversion theorem on `Ioo 0 1`. -/
theorem cosineSeriesLift_eq_lift_on_Icc_of_C2_neumann
    {w : intervalDomainPoint → ℝ}
    (hC2 : ContDiffOn ℝ 2 (intervalDomainLift w) (Icc (0 : ℝ) 1))
    (htend0 : Tendsto (deriv (intervalDomainLift w))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0))
    (htend1 : Tendsto (deriv (intervalDomainLift w))
      (nhdsWithin (1 : ℝ) (Iio 1)) (nhds 0))
    (hbc0 : deriv (intervalDomainLift w) 0 = 0)
    (hbc1 : deriv (intervalDomainLift w) 1 = 0) :
    EqOn
      (cosineSeriesLift (cosineCoeffs (intervalDomainLift w)))
      (intervalDomainLift w) (Icc (0 : ℝ) 1) := by
  let F : ℝ → ℝ := liftRepr w
  have hFcont : Continuous F :=
    liftRepr_continuous hC2.continuousOn
  have hFagree : ∀ x ∈ Icc (0 : ℝ) 1, F x = intervalDomainLift w x := by
    intro x hx
    exact liftRepr_eq_on_Icc hx
  have hFsum : Summable (fun n : ℤ ↦ fourierCoeff (reflCircle F) n) :=
    fourierCoeff_reflCircle_summable_of_repr
      hFcont hC2 hFagree htend0 htend1 hbc0 hbc1
  have hcoeff : ∀ n : ℕ,
      cosineCoeffs F n = cosineCoeffs (intervalDomainLift w) n := by
    intro n
    simpa [F] using cosineCoeffs_liftRepr (w := w) n
  have habsF : Summable (fun n : ℕ ↦ |cosineCoeffs F n|) :=
    intervalCosineCoeff_summable_abs F hFcont hFsum
  have habs : Summable
      (fun n : ℕ ↦ |cosineCoeffs (intervalDomainLift w) n|) :=
    habsF.congr (fun n ↦ by rw [hcoeff n])
  have hseriesCont : Continuous
      (cosineSeriesLift (cosineCoeffs (intervalDomainLift w))) := by
    unfold cosineSeriesLift
    refine continuous_tsum (fun n ↦ ?_) habs (fun n x ↦ ?_)
    · exact continuous_const.mul
        (Real.continuous_cos.comp (by fun_prop))
    · rw [Real.norm_eq_abs, abs_mul]
      have hcos : |cosineMode n x| ≤ 1 := by
        simpa [cosineMode] using
          Real.abs_cos_le_one ((n : ℝ) * Real.pi * x)
      calc
        |cosineCoeffs (intervalDomainLift w) n| * |cosineMode n x|
            ≤ |cosineCoeffs (intervalDomainLift w) n| * 1 :=
          mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
        _ = |cosineCoeffs (intervalDomainLift w) n| := mul_one _
  have hIoo : EqOn
      (cosineSeriesLift (cosineCoeffs (intervalDomainLift w)))
      (intervalDomainLift w) (Ioo (0 : ℝ) 1) := by
    intro x hx
    have hinv := intervalCosine_hasSum_pointwise F hFcont hx hFsum
    calc
      cosineSeriesLift (cosineCoeffs (intervalDomainLift w)) x
          = ∑' n : ℕ, unitIntervalCosineMode n x * cosineCoeffs F n := by
              unfold cosineSeriesLift
              refine tsum_congr (fun n ↦ ?_)
              rw [hcoeff n]
              simp only [cosineMode, unitIntervalCosineMode, mul_comm]
      _ = F x := hinv.tsum_eq
      _ = intervalDomainLift w x :=
        hFagree x (Ioo_subset_Icc_self hx)
  exact eqOn_Icc_of_eqOn_Ioo_of_continuousOn
    hseriesCont.continuousOn hC2.continuousOn hIoo

/-- Slice-specialized spelling of the closed cosine reconstruction. -/
theorem intervalSolutionLiftU_eq_lift_on_Icc_of_C2_neumann
    {u : ℝ → intervalDomainPoint → ℝ} {s : ℝ}
    (hC2 : ContDiffOn ℝ 2 (intervalDomainLift (u s)) (Icc (0 : ℝ) 1))
    (htend0 : Tendsto (deriv (intervalDomainLift (u s)))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0))
    (htend1 : Tendsto (deriv (intervalDomainLift (u s)))
      (nhdsWithin (1 : ℝ) (Iio 1)) (nhds 0))
    (hbc0 : deriv (intervalDomainLift (u s)) 0 = 0)
    (hbc1 : deriv (intervalDomainLift (u s)) 1 = 0) :
    EqOn (intervalSolutionLiftU u s) (intervalDomainLift (u s))
      (Icc (0 : ℝ) 1) := by
  simpa [intervalSolutionLiftU] using
    cosineSeriesLift_eq_lift_on_Icc_of_C2_neumann
      hC2 htend0 htend1 hbc0 hbc1

/-- The global resolver cosine representative agrees with the concrete
coupled chemical slice on the physical interval. -/
theorem intervalResolverLiftR_eq_coupledChemicalLift_on_Icc
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s : ℝ} :
    EqOn (intervalResolverLiftR p (u s))
      (intervalDomainLift (coupledChemicalConcentration p u s))
      (Icc (0 : ℝ) 1) := by
  intro x hx
  rw [intervalDomainLift, dif_pos hx]
  rfl

/-- Assemble the per-slice weak-H2 Neumann witness for the chemotaxis-divergence
source from the solution and resolver cosine representatives.

The solution needs only C3 as a global representative; the resolver is C4.
The product-source transfer is endpoint-insensitive inside
`chemDivSource_weakH2_of_cosineRep`, so its agreement proof is made only on the
open interior before passing to interval integrals. -/
noncomputable def coupledChemDivSourceLift_weakH2Neumann_of_cosineRepresentatives
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s : ℝ}
    (huSum : Summable (fun n : ℕ ↦
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          |cosineCoeffs (intervalDomainLift (u s)) n|)))
    (huC2 : ContDiffOn ℝ 2 (intervalDomainLift (u s)) (Icc (0 : ℝ) 1))
    (hutend0 : Tendsto (deriv (intervalDomainLift (u s)))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0))
    (hutend1 : Tendsto (deriv (intervalDomainLift (u s)))
      (nhdsWithin (1 : ℝ) (Iio 1)) (nhds 0))
    (hubc0 : deriv (intervalDomainLift (u s)) 0 = 0)
    (hubc1 : deriv (intervalDomainLift (u s)) 1 = 0)
    (hRsrc : Summable (fun n : ℕ ↦
      unitIntervalCosineEigenvalue n *
        |(ShenWork.PDE.intervalNeumannResolverSourceCoeff p (u s) n).re|))
    (hRnonneg : ∀ x ∈ Icc (0 : ℝ) 1,
      0 ≤ intervalResolverLiftR p (u s) x) :
    IntervalWeakH2Neumann (coupledChemDivSourceLift p u s) := by
  let U : ℝ → ℝ := intervalSolutionLiftU u s
  let V : ℝ → ℝ := intervalResolverLiftR p (u s)
  have hUC3 : ContDiff ℝ 3 U := by
    simpa [U] using intervalSolutionLiftU_contDiff_three huSum
  have hVC4 : ContDiff ℝ 4 V := by
    simpa [V] using intervalResolverLiftR_contDiff_four hRsrc
  have hUagree : EqOn U (intervalDomainLift (u s)) (Icc (0 : ℝ) 1) := by
    simpa [U] using
      intervalSolutionLiftU_eq_lift_on_Icc_of_C2_neumann
        huC2 hutend0 hutend1 hubc0 hubc1
  have hVagree : EqOn V
      (intervalDomainLift (coupledChemicalConcentration p u s))
      (Icc (0 : ℝ) 1) := by
    simpa [V] using
      (intervalResolverLiftR_eq_coupledChemicalLift_on_Icc
        (p := p) (u := u) (s := s))
  have hVpos : ∀ x, (0 : ℝ) < 1 + V x := by
    intro x
    simpa [V] using
      intervalResolverLiftR_one_add_pos_of_nonneg_on_Icc
        p (u s) hRnonneg x
  have hUDE := intervalSolutionLiftU_doublyEven u s
  have hH2 :=
    ShenWork.Paper2.ChemDivSpatialC2.chemDivSource_weakH2_of_cosineRep
      (p := p) (u := u s) (v := coupledChemicalConcentration p u s)
      (U_cos := U) (V_cos := V)
      hUC3 hVC4 hVpos
      (fun _x hx ↦ (hUagree hx).symm)
      (fun _x hx ↦ (hVagree hx).symm)
      hUDE.about0
      (fun x ↦ by simpa [V] using intervalResolverLiftR_even p (u s) x)
      hUDE.about1
      (fun x ↦ by simpa [V] using intervalResolverLiftR_reflect_one p (u s) x)
  simpa [coupledChemDivSourceLift,
    ShenWork.IntervalBFormSpectral.chemDivLift] using hH2

#print axioms cosineSeriesLift_eq_lift_on_Icc_of_C2_neumann
#print axioms intervalSolutionLiftU_eq_lift_on_Icc_of_C2_neumann
#print axioms intervalResolverLiftR_eq_coupledChemicalLift_on_Icc
#print axioms coupledChemDivSourceLift_weakH2Neumann_of_cosineRepresentatives

end ShenWork.Paper2.IntervalChemDivSourceWeakH2Assembly
