import ShenWork.Paper2.IntervalParabolicDuhamelGainNonCircular
import ShenWork.PDE.IntervalDomainExistence
import ShenWork.PDE.IntervalNeumannEllipticResolverR
import ShenWork.PDE.IntervalResolverSpatialC2

open ShenWork.IntervalDomain
  (intervalDomainClassicalRegularity intervalDomainLift intervalDomainPoint)
open ShenWork.PDE (intervalNeumannResolverCoeff intervalNeumannResolverR)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.Paper2.ParabolicGainInduction
open ShenWork.Paper2.ParabolicDuhamelGainNonCircular
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

/-- The concrete chem-div loss atom shape for the fixed slice. -/
abbrev ConcreteChemDivLosesOneAtom
    (p : CM2Params) (u : intervalDomainPoint → ℝ) : Prop :=
  ∀ k, 2 ≤ k → k < 6 →
    CoupledSlice k ((concreteU u) k) ((concreteV p u) k) →
      SpatialSlice (k - 1) ((concreteF p u) k)

/-- The concrete Duhamel data atom shape for the fixed slice. -/
abbrev ConcreteDuhamelDataAtom
    (p : CM2Params) (u : intervalDomainPoint → ℝ) : Type :=
  ∀ k, 2 ≤ k → k < 6 →
    DuhamelGainSliceData k ((concreteF p u) k) ((concreteU u) (k + 1))

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

/-- The first concrete `resolverAhead` subgoal, exposed as a named target for
the current stall report. -/
abbrev ResolverAheadK2Goal (p : CM2Params)
    (u : intervalDomainPoint → ℝ) : Prop :=
  SpatialSlice 3 ((concreteV p u) 2)

#print axioms baseC2_of_intervalDomainClassicalRegularity
#print axioms committed_resolver_spatialC2

end ShenWork.Paper2.ChiNegConcreteConnectors
