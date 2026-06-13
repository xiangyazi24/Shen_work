import ShenWork.Paper2.IntervalChiNegConcreteSpectralAdapters
import ShenWork.PDE.IntervalDomainExistence
import ShenWork.PDE.IntervalNeumannEllipticResolverR
import ShenWork.PDE.IntervalResolverSpatialC2

open ShenWork.IntervalDomain
  (intervalDomainClassicalRegularity intervalDomainLift intervalDomainPoint)
open ShenWork.PDE (intervalNeumannResolverCoeff intervalNeumannResolverR)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.Paper2.ParabolicGainInduction
open ShenWork.Paper2.ParabolicDuhamelGainNonCircular
open ShenWork.Paper2.ChiNegConcreteSpectralAdapters
open ShenWork.Paper2.ChiNegSourceTail
open ShenWork.Paper2.PicardLimitK1 (LocalRestart)

noncomputable section

namespace ShenWork.Paper2.ChiNegConcreteConnectors

/-- The fixed spatial slice, viewed as the order-indexed iterate family used by
the non-circular climb. -/
def concreteU (u : intervalDomainPoint → ℝ) :
    ℕ → intervalDomainPoint → ℝ :=
  fun _ => u

/-- The concrete elliptic resolver family for the same fixed slice. -/
def concreteV (p : CM2Params) (u : intervalDomainPoint → ℝ) :
    ℕ → intervalDomainPoint → ℝ :=
  fun _ => intervalNeumannResolverR p u

/-- The concrete coupled chemotaxis-logistic source family. -/
def concreteF (p : CM2Params) (u : intervalDomainPoint → ℝ) :
    ℕ → intervalDomainPoint → ℝ :=
  fun _ =>
    ShenWork.IntervalDomainExistence.intervalCoupledSource p u
      (intervalNeumannResolverR p u)

/-- The concrete `resolverAhead` atom shape for the fixed slice. -/
abbrev ConcreteResolverAheadAtom
    (p : CM2Params) (u : intervalDomainPoint → ℝ) : Prop :=
  ∀ k, 2 ≤ k → k < 6 → SpatialSlice (k + 1) ((concreteV p u) k)

/-- The concrete `resolverAhead` atom shape for the widened C7 climb. -/
abbrev ConcreteResolverAheadAtomC7
    (p : CM2Params) (u : intervalDomainPoint → ℝ) : Prop :=
  ∀ k, 2 ≤ k → k < 7 → SpatialSlice (k + 1) ((concreteV p u) k)

/-- The concrete chem-div loss atom shape for the fixed slice. -/
abbrev ConcreteChemDivLosesOneAtom
    (p : CM2Params) (u : intervalDomainPoint → ℝ) : Prop :=
  ∀ k, 2 ≤ k → k < 6 →
    CoupledSlice k ((concreteU u) k) ((concreteV p u) k) →
      SpatialSlice (k - 1) ((concreteF p u) k)

/-- The concrete chem-div loss atom shape for the widened C7 climb. -/
abbrev ConcreteChemDivLosesOneAtomC7
    (p : CM2Params) (u : intervalDomainPoint → ℝ) : Prop :=
  ∀ k, 2 ≤ k → k < 7 →
    CoupledSlice k ((concreteU u) k) ((concreteV p u) k) →
      SpatialSlice (k - 1) ((concreteF p u) k)

/-- The concrete Duhamel data atom shape for the fixed slice. -/
abbrev ConcreteDuhamelDataAtom
    (p : CM2Params) (u : intervalDomainPoint → ℝ) : Type :=
  ∀ k, 2 ≤ k → k < 6 →
    DuhamelGainSliceData k ((concreteF p u) k) ((concreteU u) (k + 1))

/-- The concrete Duhamel data atom shape for the widened C7 climb. -/
abbrev ConcreteDuhamelDataAtomC7
    (p : CM2Params) (u : intervalDomainPoint → ℝ) : Type :=
  ∀ k, 2 ≤ k → k < 7 →
    DuhamelGainSliceDataC7 k ((concreteF p u) k)
      ((concreteU u) (k + 1))

/-- The concrete source-tail atom shape for the fixed trajectory. -/
abbrev ConcreteTailOfC6Atom
    (p : CM2Params) (u : intervalDomainPoint → ℝ)
    {T : ℝ} (utraj : ℝ → intervalDomainPoint → ℝ)
    (mkL : ∀ σ, 0 < σ → σ < T → LocalRestart p utraj T σ)
    (C0 C C0dot Cdot : ℝ → ℝ) : Prop :=
  SpatialSlice 6 ((concreteU u) 6) →
    ∀ σ (hσ0 : 0 < σ) (hσT : σ < T),
      SourceEigenCubeTailFields
        (mkL σ hσ0 hσT) (C0 σ) (C σ) (C0dot σ) (Cdot σ)

/-- The concrete source-tail atom shape after the widened C7 climb. -/
abbrev ConcreteTailOfC7Atom
    (p : CM2Params) (u : intervalDomainPoint → ℝ)
    {T : ℝ} (utraj : ℝ → intervalDomainPoint → ℝ)
    (mkL : ∀ σ, 0 < σ → σ < T → LocalRestart p utraj T σ)
    (C0 C C0dot Cdot : ℝ → ℝ) : Prop :=
  SpatialSlice 7 ((concreteU u) 7) →
    ∀ σ (hσ0 : 0 < σ) (hσT : σ < T),
      SourceEigenCubeTailFields
        (mkL σ hσ0 hσT) (C0 σ) (C σ) (C0dot σ) (Cdot σ)

/-- The concrete `baseC2` atom comes directly from the committed closed-spatial
`C²` conjunct of `intervalDomainClassicalRegularity`. -/
theorem baseC2_of_intervalDomainClassicalRegularity
    {T t : ℝ} {utraj vtraj : ℝ → intervalDomainPoint → ℝ}
    (hreg : intervalDomainClassicalRegularity T utraj vtraj)
    (ht0 : 0 < t) (htT : t < T) :
    SpatialSlice 2 ((concreteU (utraj t)) 2) := by
  simpa [SpatialSlice, concreteU] using
    (hreg.2.2.2.2.1 t ⟨ht0, htT⟩).1.1

/-- The committed elliptic resolver estimate gives concrete spatial `C²`.
The `resolverAhead` atom first asks for `C³` at `k = 2`, so this theorem records
the current one-order-short committed endpoint. -/
theorem committed_resolver_spatialC2
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hdecay : ShenWork.Paper2.SourceCoeffQuadraticDecay p u) :
    SpatialSlice 2 ((concreteV p u) 0) := by
  have hseries :
      ContDiffOn ℝ 2
        (fun x : ℝ => ∑' k : ℕ,
          (intervalNeumannResolverCoeff p u k).re * cosineMode k x)
        (Set.Icc (0 : ℝ) 1) :=
    ShenWork.IntervalResolverSpatialC2.resolverR_contDiffOn_Icc hdecay
  simpa [SpatialSlice, concreteV] using hseries.congr (fun x hx => by
    have hval :
        intervalDomainLift (intervalNeumannResolverR p u) x =
          intervalNeumannResolverR p u ⟨x, hx⟩ := by
      simp [intervalDomainLift, hx]
    rw [hval]
    exact (ShenWork.IntervalResolverSpatialC2.resolverR_eq_cosineSeries
      (p := p) (u := u) ⟨x, hx⟩).symm)

/-- Concrete resolver-ahead from the exact sixth-order resolved-coefficient tail.
This is the spectral elliptic-gain input still missing from the concrete source
regularity side. -/
theorem concreteResolverAhead_of_resolverCoeff_eigenCube_summable
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hcube : Summable fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            |(intervalNeumannResolverCoeff p u n).re|))) :
    ConcreteResolverAheadAtom p u := by
  simpa [ConcreteResolverAheadAtom, concreteV] using
    resolverAhead_of_resolverCoeff_eigenCube_summable
      (p := p) (u := u) hcube

/-- Concrete resolver-ahead after the elliptic gain has converted source
two-weight summability into resolved coefficient cube summability. -/
theorem concreteResolverAhead_of_sourceEigenSq_summable
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hsrc : Summable fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          |(ShenWork.PDE.intervalNeumannResolverSourceCoeff p u n).re|)) :
    ConcreteResolverAheadAtom p u :=
  concreteResolverAhead_of_resolverCoeff_eigenCube_summable
    (resolverCoeff_eigenCube_summable_of_sourceEigenSq_summable
      (p := p) (u := u) hsrc)

/-- Concrete widened resolver-ahead from the exact eighth-order resolved
coefficient summability used by the C7 climb. -/
theorem concreteResolverAheadC7_of_resolverCoeff_eigenFourth_summable
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hfourth : Summable fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              |(intervalNeumannResolverCoeff p u n).re|)))) :
    ConcreteResolverAheadAtomC7 p u := by
  simpa [ConcreteResolverAheadAtomC7, concreteV] using
    resolverAheadC7_of_resolverCoeff_eigenFourth_summable
      (p := p) (u := u) hfourth

/-- Concrete widened resolver-ahead after the elliptic gain has converted source
eigen-cube summability into resolved fourth-weight summability. -/
theorem concreteResolverAheadC7_of_sourceEigenCube_summable
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hsrc : Summable fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            |(ShenWork.PDE.intervalNeumannResolverSourceCoeff p u n).re|))) :
    ConcreteResolverAheadAtomC7 p u :=
  concreteResolverAheadC7_of_resolverCoeff_eigenFourth_summable
    (resolverCoeff_eigenFourth_summable_of_sourceEigenCube_summable
      (p := p) (u := u) hsrc)

/-- The final concrete source algebra after the chemotaxis-divergence and
logistic components have been produced at the target order. -/
theorem intervalCoupledSource_spatialSlice_of_components
    {p : CM2Params} {u v : intervalDomainPoint → ℝ} {k : ℕ}
    (hchem :
      SpatialSlice (k - 1)
        (ShenWork.IntervalDomain.intervalDomainChemotaxisDiv p u v))
    (hlog :
      SpatialSlice (k - 1)
        (ShenWork.IntervalDomainExistence.intervalLogisticSource p u)) :
    SpatialSlice (k - 1)
      (ShenWork.IntervalDomainExistence.intervalCoupledSource p u v) := by
  have hsrc :
      ContDiffOn ℝ ((k - 1 : ℕ) : ℕ∞)
        (fun x : ℝ =>
          (-p.χ₀) •
            intervalDomainLift
              (ShenWork.IntervalDomain.intervalDomainChemotaxisDiv p u v) x +
          intervalDomainLift
            (ShenWork.IntervalDomainExistence.intervalLogisticSource p u) x)
        (Set.Icc (0 : ℝ) 1) :=
    (hchem.const_smul (-p.χ₀)).add hlog
  exact hsrc.congr (fun x hx => by
    simp [intervalDomainLift, hx,
      ShenWork.IntervalDomainExistence.intervalCoupledSource])

/-- Logistic source regularity from a nonzero floor for the lifted profile.
The nonzero floor is the exact condition needed by the committed `rpow`
`ContDiffOn` API for arbitrary positive real exponent `p.α`. -/
theorem intervalLogisticSource_spatialSlice_of_nonzero
    {p : CM2Params} {u : intervalDomainPoint → ℝ} {k : ℕ}
    (hu : SpatialSlice k u)
    (hfloor : ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift u x ≠ 0) :
    SpatialSlice k
      (ShenWork.IntervalDomainExistence.intervalLogisticSource p u) := by
  have hpow :
      ContDiffOn ℝ (k : ℕ∞)
        (fun x : ℝ => intervalDomainLift u x ^ p.α)
        (Set.Icc (0 : ℝ) 1) :=
    hu.rpow_const_of_ne hfloor
  have hreaction :
      ContDiffOn ℝ (k : ℕ∞)
        (fun x : ℝ =>
          intervalDomainLift u x *
            (p.a - p.b * intervalDomainLift u x ^ p.α))
        (Set.Icc (0 : ℝ) 1) := by
    have hloss :
        ContDiffOn ℝ (k : ℕ∞)
          (fun x : ℝ => p.b * intervalDomainLift u x ^ p.α)
          (Set.Icc (0 : ℝ) 1) :=
      (hpow.const_smul p.b).congr (fun _ _ => by rw [smul_eq_mul])
    exact hu.mul (contDiffOn_const.sub hloss)
  exact hreaction.congr (fun x hx => by
    simp [intervalDomainLift, hx,
      ShenWork.IntervalDomainExistence.intervalLogisticSource])

/-- Lower-order form of `intervalLogisticSource_spatialSlice_of_nonzero`,
matching the source-loss atom. -/
theorem intervalLogisticSource_spatialSlice_lower_of_nonzero
    {p : CM2Params} {u : intervalDomainPoint → ℝ} {k : ℕ}
    (hu : SpatialSlice k u)
    (hfloor : ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift u x ≠ 0) :
    SpatialSlice (k - 1)
      (ShenWork.IntervalDomainExistence.intervalLogisticSource p u) :=
  (intervalLogisticSource_spatialSlice_of_nonzero
    (p := p) (u := u) (k := k) hu hfloor).of_le (by
      exact_mod_cast Nat.sub_le k 1)

/-- Component-wise producer for the widened concrete chem-div-loss atom.
This keeps the unresolved component regularity obligations explicit. -/
theorem concreteChemDivLosesOneAtomC7_of_component_atoms
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hchem : ∀ k, 2 ≤ k → k < 7 →
      CoupledSlice k ((concreteU u) k) ((concreteV p u) k) →
        SpatialSlice (k - 1)
          (ShenWork.IntervalDomain.intervalDomainChemotaxisDiv p
            ((concreteU u) k) ((concreteV p u) k)))
    (hlog : ∀ k, 2 ≤ k → k < 7 →
      SpatialSlice k ((concreteU u) k) →
        SpatialSlice (k - 1)
          (ShenWork.IntervalDomainExistence.intervalLogisticSource p
            ((concreteU u) k))) :
    ConcreteChemDivLosesOneAtomC7 p u := by
  intro k hk2 hk7 hcoupled
  exact intervalCoupledSource_spatialSlice_of_components
    (hchem k hk2 hk7 hcoupled) (hlog k hk2 hk7 hcoupled.1)

/-- The closed χ-negative branch once the four concrete atom families have been
supplied for the fixed-slice `concreteU`, `concreteV`, and `concreteF` objects. -/
theorem chiNeg_concrete_close_of_nonCircular_atoms
    {p : CM2Params} {T : ℝ}
    {utraj : ℝ → intervalDomainPoint → ℝ}
    {u : intervalDomainPoint → ℝ}
    (baseC2 : SpatialSlice 2 ((concreteU u) 2))
    (resolverAhead : ConcreteResolverAheadAtom p u)
    (chemDivLosesOne : ConcreteChemDivLosesOneAtom p u)
    (data : ConcreteDuhamelDataAtom p u)
    (H : ShenWork.IntervalResolverTimeRegularity.ResolverHasSpectralAgreement
      T utraj)
    (mkL : ∀ σ, 0 < σ → σ < T → LocalRestart p utraj T σ)
    (C0 C C0dot Cdot : ℝ → ℝ)
    (hC6 : ∀ σ, 0 ≤ max (C0 σ) (64 * C σ))
    (hCdot6 : ∀ σ, 0 ≤ max (C0dot σ) (64 * Cdot σ))
    (tailOfC6 :
      ConcreteTailOfC6Atom p u utraj mkL C0 C C0dot Cdot) :
    ShenWork.IntervalResolverJointC2.ResolverHasSpectralAgreementC2Coeff
      T utraj :=
  chiNeg_close_of_nonCircular_climb
    (U := concreteU u) (V := concreteV p u) (F := concreteF p u)
    baseC2 resolverAhead chemDivLosesOne data
    H mkL C0 C C0dot Cdot hC6 hCdot6 tailOfC6

/-- The widened concrete χ-negative branch once the C7 atom families have been
supplied for the fixed-slice `concreteU`, `concreteV`, and `concreteF` objects. -/
theorem chiNeg_concrete_close_of_nonCircular_atoms_C7
    {p : CM2Params} {T : ℝ}
    {utraj : ℝ → intervalDomainPoint → ℝ}
    {u : intervalDomainPoint → ℝ}
    (baseC2 : SpatialSlice 2 ((concreteU u) 2))
    (resolverAhead : ConcreteResolverAheadAtomC7 p u)
    (chemDivLosesOne : ConcreteChemDivLosesOneAtomC7 p u)
    (data : ConcreteDuhamelDataAtomC7 p u)
    (H : ShenWork.IntervalResolverTimeRegularity.ResolverHasSpectralAgreement
      T utraj)
    (mkL : ∀ σ, 0 < σ → σ < T → LocalRestart p utraj T σ)
    (C0 C C0dot Cdot : ℝ → ℝ)
    (hC6 : ∀ σ, 0 ≤ max (C0 σ) (64 * C σ))
    (hCdot6 : ∀ σ, 0 ≤ max (C0dot σ) (64 * Cdot σ))
    (tailOfC7 :
      ConcreteTailOfC7Atom p u utraj mkL C0 C C0dot Cdot) :
    ShenWork.IntervalResolverJointC2.ResolverHasSpectralAgreementC2Coeff
      T utraj :=
  chiNeg_close_of_nonCircular_climb_C7
    (U := concreteU u) (V := concreteV p u) (F := concreteF p u)
    baseC2 resolverAhead chemDivLosesOne data
    H mkL C0 C C0dot Cdot hC6 hCdot6 tailOfC7

/-- The first concrete `resolverAhead` subgoal, exposed as a named target for
the current stall report. -/
abbrev ResolverAheadK2Goal (p : CM2Params)
    (u : intervalDomainPoint → ℝ) : Prop :=
  SpatialSlice 3 ((concreteV p u) 2)

#print axioms baseC2_of_intervalDomainClassicalRegularity
#print axioms committed_resolver_spatialC2
#print axioms concreteResolverAhead_of_resolverCoeff_eigenCube_summable
#print axioms concreteResolverAhead_of_sourceEigenSq_summable
#print axioms concreteResolverAheadC7_of_resolverCoeff_eigenFourth_summable
#print axioms concreteResolverAheadC7_of_sourceEigenCube_summable
#print axioms intervalCoupledSource_spatialSlice_of_components
#print axioms intervalLogisticSource_spatialSlice_of_nonzero
#print axioms intervalLogisticSource_spatialSlice_lower_of_nonzero
#print axioms concreteChemDivLosesOneAtomC7_of_component_atoms
#print axioms chiNeg_concrete_close_of_nonCircular_atoms
#print axioms chiNeg_concrete_close_of_nonCircular_atoms_C7

end ShenWork.Paper2.ChiNegConcreteConnectors
