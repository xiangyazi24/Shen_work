import ShenWork.Paper2.IntervalSoftClampFloorAudit

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.Paper2.ChiNegConcreteConnectors
open ShenWork.Paper2.ChiNegConcreteSpectralAdapters
open ShenWork.Paper2.ChiNegSourceTail
open ShenWork.Paper2.ParabolicDuhamelGainNonCircular
open ShenWork.Paper2.ParabolicGainInduction
open ShenWork.Paper2.SoftClampFloorAudit
open ShenWork.Paper2.PicardLimitK1 (LocalRestart)

noncomputable section

namespace ShenWork.Paper2.ChiNegFloorClosure

theorem slice_pos_of_window_floor
    {w : ℝ → intervalDomainPoint → ℝ} {lo hi t δ : ℝ}
    (hδ : 0 < δ)
    (hfloor : ∀ s ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      δ ≤ intervalDomainLift (w s) x)
    (ht : t ∈ Set.Icc lo hi) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (w t) x := by
  intro x hx
  exact lt_of_lt_of_le hδ (hfloor t ht x hx)

theorem concreteChemDivLosesOneAtomC7_of_window_floor
    {p : CM2Params} {w : ℝ → intervalDomainPoint → ℝ} {lo hi t δ : ℝ}
    (hδ : 0 < δ)
    (hfloor : ∀ s ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      δ ≤ intervalDomainLift (w s) x)
    (ht : t ∈ Set.Icc lo hi)
    (hchem : ∀ k, 2 ≤ k → k < 7 →
      CoupledSlice k ((concreteU (w t)) k) ((concreteV p (w t)) k) →
        SpatialSlice (k - 1)
          (ShenWork.IntervalDomain.intervalDomainChemotaxisDiv p
            ((concreteU (w t)) k) ((concreteV p (w t)) k))) :
    ConcreteChemDivLosesOneAtomC7 p (w t) :=
  concreteChemDivLosesOneAtomC7_of_component_atoms_positive hchem
    (slice_pos_of_window_floor hδ hfloor ht)

theorem concreteChemDivLosesOneAtomC7_of_joint_positive
    {p : CM2Params} {w : ℝ → intervalDomainPoint → ℝ} {lo hi t : ℝ}
    (hlohi : lo ≤ hi)
    (hjoint : ContinuousOn
      (Function.uncurry (fun s x => intervalDomainLift (w s) x))
      (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1))
    (hpos : ∀ s ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (w s) x)
    (ht : t ∈ Set.Icc lo hi)
    (hchem : ∀ k, 2 ≤ k → k < 7 →
      CoupledSlice k ((concreteU (w t)) k) ((concreteV p (w t)) k) →
        SpatialSlice (k - 1)
          (ShenWork.IntervalDomain.intervalDomainChemotaxisDiv p
            ((concreteU (w t)) k) ((concreteV p (w t)) k))) :
    ConcreteChemDivLosesOneAtomC7 p (w t) := by
  obtain ⟨δ, hδ, hfloor⟩ :=
    exists_uniform_profile_floor_on_time_window hlohi hjoint hpos
  exact concreteChemDivLosesOneAtomC7_of_window_floor hδ hfloor ht hchem

structure ConcreteDuhamelDataC7Fields
    (p : CM2Params) (u : intervalDomainPoint → ℝ) : Type where
  a : (k : ℕ) → 2 ≤ k → k < 7 → ℝ → ℕ → ℝ
  τ : (k : ℕ) → 2 ≤ k → k < 7 → ℝ
  hτ : ∀ k hk2 hk7, 0 < τ k hk2 hk7
  eqOn : ∀ k hk2 hk7,
    Set.EqOn (intervalDomainLift ((concreteU u) (k + 1)))
      (fun x : ℝ =>
        ∫ s in (0 : ℝ)..τ k hk2 hk7,
          unitIntervalCosineHeatValue
            (τ k hk2 hk7 - s) (a k hk2 hk7 s) x)
      (Set.Icc (0 : ℝ) 1)
  lowSource : ∀ k hk2 hk7,
    k = 2 ∨ k = 3 →
      SpatialSlice (k - 1) ((concreteF p u) k) →
        DuhamelSourceSpatialWeightOne (a k hk2 hk7)
  highSource : ∀ k hk2 hk7,
    k = 4 ∨ k = 5 →
      SpatialSlice (k - 1) ((concreteF p u) k) →
        DuhamelSourceSpatialWeightTwo (a k hk2 hk7)
  topSource : ∀ k hk2 hk7,
    k = 6 →
      SpatialSlice (k - 1) ((concreteF p u) k) →
        DuhamelSourceSpatialWeightThree (a k hk2 hk7)

structure ConcreteDuhamelDataFields
    (p : CM2Params) (u : intervalDomainPoint → ℝ) : Type where
  a : (k : ℕ) → 2 ≤ k → k < 6 → ℝ → ℕ → ℝ
  τ : (k : ℕ) → 2 ≤ k → k < 6 → ℝ
  hτ : ∀ k hk2 hk6, 0 < τ k hk2 hk6
  eqOn : ∀ k hk2 hk6,
    Set.EqOn (intervalDomainLift ((concreteU u) (k + 1)))
      (fun x : ℝ =>
        ∫ s in (0 : ℝ)..τ k hk2 hk6,
          unitIntervalCosineHeatValue
            (τ k hk2 hk6 - s) (a k hk2 hk6 s) x)
      (Set.Icc (0 : ℝ) 1)
  lowSource : ∀ k hk2 hk6,
    k = 2 ∨ k = 3 →
      SpatialSlice (k - 1) ((concreteF p u) k) →
        DuhamelSourceSpatialWeightOne (a k hk2 hk6)
  highSource : ∀ k hk2 hk6,
    k = 4 ∨ k = 5 →
      SpatialSlice (k - 1) ((concreteF p u) k) →
        DuhamelSourceSpatialWeightTwo (a k hk2 hk6)

def ConcreteDuhamelDataFields.toAtom
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (D : ConcreteDuhamelDataFields p u) :
    ConcreteDuhamelDataAtom p u := by
  intro k hk2 hk6
  exact duhamelGainSliceData_of_spatialWeights
    (D.hτ k hk2 hk6)
    (D.eqOn k hk2 hk6)
    (D.lowSource k hk2 hk6)
    (D.highSource k hk2 hk6)

def ConcreteDuhamelDataC7Fields.toAtom
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (D : ConcreteDuhamelDataC7Fields p u) :
    ConcreteDuhamelDataAtomC7 p u := by
  intro k hk2 hk7
  exact duhamelGainSliceDataC7_of_spatialWeights
    (D.hτ k hk2 hk7)
    (D.eqOn k hk2 hk7)
    (D.lowSource k hk2 hk7)
    (D.highSource k hk2 hk7)
    (D.topSource k hk2 hk7)

theorem concreteTailOfC7Atom_of_eigenCubeTail
    {p : CM2Params} {u0 : intervalDomainPoint → ℝ}
    {T : ℝ} {utraj : ℝ → intervalDomainPoint → ℝ}
    {mkL : ∀ σ, 0 < σ → σ < T → LocalRestart p utraj T σ}
    {C0 C C0dot Cdot : ℝ → ℝ}
    (tail : ∀ σ (hσ0 : 0 < σ) (hσT : σ < T),
      SourceEigenCubeTailFields
        (mkL σ hσ0 hσT) (C0 σ) (C σ) (C0dot σ) (Cdot σ)) :
    ConcreteTailOfC7Atom p u0 utraj mkL C0 C C0dot Cdot := by
  intro _hU7 σ hσ0 hσT
  exact tail σ hσ0 hσT

theorem concreteTailOfC6Atom_of_eigenCubeTail
    {p : CM2Params} {u0 : intervalDomainPoint → ℝ}
    {T : ℝ} {utraj : ℝ → intervalDomainPoint → ℝ}
    {mkL : ∀ σ, 0 < σ → σ < T → LocalRestart p utraj T σ}
    {C0 C C0dot Cdot : ℝ → ℝ}
    (tail : ∀ σ (hσ0 : 0 < σ) (hσT : σ < T),
      SourceEigenCubeTailFields
        (mkL σ hσ0 hσT) (C0 σ) (C σ) (C0dot σ) (Cdot σ)) :
    ConcreteTailOfC6Atom p u0 utraj mkL C0 C C0dot Cdot := by
  intro _hU6 σ hσ0 hσT
  exact tail σ hσ0 hσT

theorem chiNeg_close_C7_of_window_floor
    {p : CM2Params} {T lo hi t δ : ℝ}
    {utraj : ℝ → intervalDomainPoint → ℝ}
    (baseC2 : SpatialSlice 2 ((concreteU (utraj t)) 2))
    (hδ : 0 < δ)
    (hfloor : ∀ s ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      δ ≤ intervalDomainLift (utraj s) x)
    (ht : t ∈ Set.Icc lo hi)
    (hchem : ∀ k, 2 ≤ k → k < 7 →
      CoupledSlice k ((concreteU (utraj t)) k)
        ((concreteV p (utraj t)) k) →
        SpatialSlice (k - 1)
          (ShenWork.IntervalDomain.intervalDomainChemotaxisDiv p
            ((concreteU (utraj t)) k)
            ((concreteV p (utraj t)) k)))
    (hsrcCube : Summable fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            |(ShenWork.PDE.intervalNeumannResolverSourceCoeff
              p (utraj t) n).re|)))
    (data : ConcreteDuhamelDataC7Fields p (utraj t))
    (H : ShenWork.IntervalResolverTimeRegularity.ResolverHasSpectralAgreement
      T utraj)
    (mkL : ∀ σ, 0 < σ → σ < T → LocalRestart p utraj T σ)
    (C0 C C0dot Cdot : ℝ → ℝ)
    (hC6 : ∀ σ, 0 ≤ max (C0 σ) (64 * C σ))
    (hCdot6 : ∀ σ, 0 ≤ max (C0dot σ) (64 * Cdot σ))
    (tail : ∀ σ (hσ0 : 0 < σ) (hσT : σ < T),
      SourceEigenCubeTailFields
        (mkL σ hσ0 hσT) (C0 σ) (C σ) (C0dot σ) (Cdot σ)) :
    ShenWork.IntervalResolverJointC2.ResolverHasSpectralAgreementC2Coeff
      T utraj :=
  chiNeg_concrete_close_of_nonCircular_atoms_C7
    baseC2
    (concreteResolverAheadC7_of_sourceEigenCube_summable hsrcCube)
    (concreteChemDivLosesOneAtomC7_of_window_floor hδ hfloor ht hchem)
    data.toAtom H mkL C0 C C0dot Cdot hC6 hCdot6
    (concreteTailOfC7Atom_of_eigenCubeTail tail)

theorem chiNeg_close_C7_of_joint_positive
    {p : CM2Params} {T lo hi t : ℝ}
    {utraj : ℝ → intervalDomainPoint → ℝ}
    (baseC2 : SpatialSlice 2 ((concreteU (utraj t)) 2))
    (hlohi : lo ≤ hi)
    (hjoint : ContinuousOn
      (Function.uncurry (fun s x => intervalDomainLift (utraj s) x))
      (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1))
    (hpos : ∀ s ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (utraj s) x)
    (ht : t ∈ Set.Icc lo hi)
    (hchem : ∀ k, 2 ≤ k → k < 7 →
      CoupledSlice k ((concreteU (utraj t)) k)
        ((concreteV p (utraj t)) k) →
        SpatialSlice (k - 1)
          (ShenWork.IntervalDomain.intervalDomainChemotaxisDiv p
            ((concreteU (utraj t)) k)
            ((concreteV p (utraj t)) k)))
    (hsrcCube : Summable fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            |(ShenWork.PDE.intervalNeumannResolverSourceCoeff
              p (utraj t) n).re|)))
    (data : ConcreteDuhamelDataC7Fields p (utraj t))
    (H : ShenWork.IntervalResolverTimeRegularity.ResolverHasSpectralAgreement
      T utraj)
    (mkL : ∀ σ, 0 < σ → σ < T → LocalRestart p utraj T σ)
    (C0 C C0dot Cdot : ℝ → ℝ)
    (hC6 : ∀ σ, 0 ≤ max (C0 σ) (64 * C σ))
    (hCdot6 : ∀ σ, 0 ≤ max (C0dot σ) (64 * Cdot σ))
    (tail : ∀ σ (hσ0 : 0 < σ) (hσT : σ < T),
      SourceEigenCubeTailFields
        (mkL σ hσ0 hσT) (C0 σ) (C σ) (C0dot σ) (Cdot σ)) :
    ShenWork.IntervalResolverJointC2.ResolverHasSpectralAgreementC2Coeff
      T utraj := by
  obtain ⟨δ, hδ, hfloor⟩ :=
    exists_uniform_profile_floor_on_time_window hlohi hjoint hpos
  exact chiNeg_close_C7_of_window_floor
    baseC2 hδ hfloor ht hchem hsrcCube data H mkL
    C0 C C0dot Cdot hC6 hCdot6 tail

#print axioms slice_pos_of_window_floor
#print axioms concreteChemDivLosesOneAtomC7_of_window_floor
#print axioms concreteChemDivLosesOneAtomC7_of_joint_positive
#print axioms ConcreteDuhamelDataFields.toAtom
#print axioms ConcreteDuhamelDataC7Fields.toAtom
#print axioms concreteTailOfC6Atom_of_eigenCubeTail
#print axioms concreteTailOfC7Atom_of_eigenCubeTail
#print axioms chiNeg_close_C7_of_window_floor
#print axioms chiNeg_close_C7_of_joint_positive

end ShenWork.Paper2.ChiNegFloorClosure
