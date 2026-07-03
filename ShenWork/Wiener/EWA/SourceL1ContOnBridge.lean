import ShenWork.Wiener.EWA.SourceEnvelope
import ShenWork.Wiener.EWA.HCoeffDischarge
import ShenWork.Wiener.EWA.NonCircularCoeffBridge
import ShenWork.Wiener.EWA.GrowthEvenReal
import ShenWork.Wiener.EWA.GrowthEvalBridge
import ShenWork.Wiener.EWA.EvenRealClosure
import ShenWork.Paper2.IntervalPicardLimitRestartWeak
import ShenWork.PDE.IntervalCoupledSourceTimeC1

open scoped BigOperators

noncomputable section

namespace ShenWork.EWA

open Set Filter Topology
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledChemDivSourceLift
   coupledLogisticSourceCoeffs coupledLogisticSourceLift)
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalPicardLimitRestartWeak (DuhamelSourceL1ContOn)

variable {T : ℝ}

/-- Real-time wrapper for the EWA cosine-coefficient extractor on `[0,T]`. -/
noncomputable def ewaCosCoeffAtReal (F : EWA T 0) (hT : 0 ≤ T)
    (s : ℝ) (n : ℕ) : ℝ :=
  (fun _ : 0 ≤ T =>
    if hs : s ∈ Set.Icc (0 : ℝ) T then ewaCosCoeffAt F ⟨s, hs⟩ n else 0) hT

private theorem ewaCosCoeffAt_continuous (F : EWA T 0) (n : ℕ) :
    Continuous (fun τ : TimeDom T => ewaCosCoeffAt F τ n) := by
  unfold ewaCosCoeffAt
  by_cases hn : n = 0
  · simp [hn]
    simpa using Complex.continuous_re.comp ((F.toFun (0 : ℤ)).continuous)
  · simp [hn]
    have hsum : Continuous fun τ : TimeDom T =>
        (F.toFun (n : ℤ)) τ + (F.toFun (-(n : ℤ))) τ :=
      ((F.toFun (n : ℤ)).continuous).add ((F.toFun (-(n : ℤ))).continuous)
    simpa using Complex.continuous_re.comp hsum

theorem ewaCosCoeffAtReal_continuousOn
    (F : EWA T 0) (hT : 0 ≤ T) (n : ℕ) :
    ContinuousOn (fun s : ℝ => ewaCosCoeffAtReal F hT s n) (Set.Icc 0 T) := by
  rw [continuousOn_iff_continuous_restrict]
  exact (ewaCosCoeffAt_continuous F n).congr (fun τ => by
    simp [Set.restrict, ewaCosCoeffAtReal, τ.2])

theorem logistic_coeff_bound_of_EWA
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (U : EWA T 1)
    (hU : EvenRealEWA U)
    (h_eval : ∀ (τ : TimeDom T) (x : ℝ), x ∈ Set.Ioo (0 : ℝ) 1 →
        evalST τ (x : WA.Circ)
          (GWA.incl (by omega : (0 : ℕ) ≤ 1) (growthEWA p.α p.a p.b U))
          = ((coupledLogisticSourceLift p u τ.1 x : ℝ) : ℂ))
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) T) (n : ℕ) :
    |coupledLogisticSourceCoeffs p u s n|
      ≤ sourceEnvelope
          (GWA.incl (by omega : (0 : ℕ) ≤ 1) (growthEWA p.α p.a p.b U)) n := by
  have hgr : EvenRealEWA
      (GWA.incl (by omega : (0 : ℕ) ≤ 1) (growthEWA p.α p.a p.b U)) :=
    (growthEWA_evenReal FnegEWA_evenReal_Hyp_proved hU).incl (by omega)
  let τ : TimeDom T := ⟨s, hs⟩
  have hbridge : ewaCosCoeffAt
        (GWA.incl (by omega : (0 : ℕ) ≤ 1) (growthEWA p.α p.a p.b U)) τ n
      = cosineCoeffs (coupledLogisticSourceLift p u s) n :=
    ewaCosCoeffAt_eq_cosineCoeffs_of_even_real
      (F := GWA.incl (by omega : (0 : ℕ) ≤ 1) (growthEWA p.α p.a p.b U))
      (f := coupledLogisticSourceLift p u s) τ
      (fun m => hgr.even τ m) (fun m => hgr.real τ m)
      (fun x hx => h_eval τ x hx) n
  have hcoeff : coupledLogisticSourceCoeffs p u s n
      = ewaCosCoeffAt
          (GWA.incl (by omega : (0 : ℕ) ≤ 1) (growthEWA p.α p.a p.b U)) τ n := by
    rw [coupledLogisticSourceCoeffs, hbridge]
  rw [hcoeff]
  exact ewaCosCoeffAt_abs_le_envelope
    (GWA.incl (by omega : (0 : ℕ) ≤ 1) (growthEWA p.α p.a p.b U)) τ n

noncomputable def chemDivSourceL1ContOn_of_EWA
    {μ ν γ : ℝ} (hμ : 0 < μ) (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (U : EWA T 1)
    (hT : 0 ≤ T)
    (hU : EvenRealEWA U)
    (h_eval : ∀ (τ : TimeDom T) (x : ℝ), x ∈ Set.Ioo (0 : ℝ) 1 →
        evalST τ (x : WA.Circ) (chemDivEWA μ ν γ hμ p U)
          = ((coupledChemDivSourceLift p u τ.1 x : ℝ) : ℂ)) :
    DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T where
  envelope := sourceEnvelope (chemDivEWA μ ν γ hμ p U)
  henv_summable := sourceEnvelope_summable _
  henv_bound := fun s hs0 hsT n =>
    chemDiv_coeff_bound_of_EWA hμ p u U hU h_eval s ⟨hs0, hsT⟩ n
  hcont := fun n => by
    have hdiv : EvenRealEWA (chemDivEWA μ ν γ hμ p U) :=
      chemDivEWA_evenReal FnegEWA_evenReal_Hyp_proved hμ p hU
    refine ContinuousOn.congr
      (ewaCosCoeffAtReal_continuousOn (chemDivEWA μ ν γ hμ p U) hT n) ?_
    intro s hs
    show cosineCoeffs (coupledChemDivSourceLift p u s) n
      = ewaCosCoeffAtReal (chemDivEWA μ ν γ hμ p U) hT s n
    simp only [ewaCosCoeffAtReal, dif_pos hs]
    exact (ewaCosCoeffAt_eq_cosineCoeffs_of_even_real
      (F := chemDivEWA μ ν γ hμ p U)
      (f := coupledChemDivSourceLift p u s) ⟨s, hs⟩
      (fun m => hdiv.even ⟨s, hs⟩ m)
      (fun m => hdiv.real ⟨s, hs⟩ m)
      (fun x hx => h_eval ⟨s, hs⟩ x hx) n).symm

noncomputable def logisticSourceL1ContOn_of_EWA
    (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (U : EWA T 1)
    (hT : 0 ≤ T)
    (hU : EvenRealEWA U)
    (h_eval : ∀ (τ : TimeDom T) (x : ℝ), x ∈ Set.Ioo (0 : ℝ) 1 →
        evalST τ (x : WA.Circ)
          (GWA.incl (by omega : (0 : ℕ) ≤ 1) (growthEWA p.α p.a p.b U))
          = ((coupledLogisticSourceLift p u τ.1 x : ℝ) : ℂ)) :
    DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T where
  envelope :=
    sourceEnvelope
      (GWA.incl (by omega : (0 : ℕ) ≤ 1) (growthEWA p.α p.a p.b U))
  henv_summable := sourceEnvelope_summable _
  henv_bound := fun s hs0 hsT n =>
    logistic_coeff_bound_of_EWA p u U hU h_eval s ⟨hs0, hsT⟩ n
  hcont := fun n => by
    have hgr : EvenRealEWA
        (GWA.incl (by omega : (0 : ℕ) ≤ 1) (growthEWA p.α p.a p.b U)) :=
      (growthEWA_evenReal FnegEWA_evenReal_Hyp_proved hU).incl (by omega)
    refine ContinuousOn.congr
      (ewaCosCoeffAtReal_continuousOn
        (GWA.incl (by omega : (0 : ℕ) ≤ 1) (growthEWA p.α p.a p.b U)) hT n) ?_
    intro s hs
    show cosineCoeffs (coupledLogisticSourceLift p u s) n
      = ewaCosCoeffAtReal
          (GWA.incl (by omega : (0 : ℕ) ≤ 1) (growthEWA p.α p.a p.b U))
          hT s n
    simp only [ewaCosCoeffAtReal, dif_pos hs]
    exact (ewaCosCoeffAt_eq_cosineCoeffs_of_even_real
      (F := GWA.incl (by omega : (0 : ℕ) ≤ 1) (growthEWA p.α p.a p.b U))
      (f := coupledLogisticSourceLift p u s) ⟨s, hs⟩
      (fun m => hgr.even ⟨s, hs⟩ m)
      (fun m => hgr.real ⟨s, hs⟩ m)
      (fun x hx => h_eval ⟨s, hs⟩ x hx) n).symm

end ShenWork.EWA

#print axioms ShenWork.EWA.chemDivSourceL1ContOn_of_EWA
#print axioms ShenWork.EWA.logisticSourceL1ContOn_of_EWA
