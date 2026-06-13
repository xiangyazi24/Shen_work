import ShenWork.Paper2.IntervalChiNegFloorClosure

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.Paper2.ChiNegConcreteConnectors
open ShenWork.Paper2.ChiNegFloorClosure
open ShenWork.Paper2.ParabolicDuhamelGainNonCircular
open ShenWork.Paper2.ParabolicGainInduction

noncomputable section

namespace ShenWork.Paper2.ConcreteIterateC7

/-- The concrete iterate's spatial-`C⁷` regularity, produced by feeding the
discharged concrete atoms into the non-circular climb
`assembledAtoms_climb_C2_to_C7_nonCircular`.

Discharged (committed) atoms used internally:
* `resolverAhead := concreteResolverAheadC7_of_sourceEigenCube_summable hsrcCube`
  (the elliptic spectral gain), and
* `chemDivLosesOne := concreteChemDivLosesOneAtomC7_of_joint_positive ...`
  (the chem-div loss under the compactness floor, fed by `hlohi`/`hjoint`/`hpos`),
* `data := data.toAtom` (the Duhamel-gain packaging adapter).

Honest open hypotheses of this theorem (genuinely not yet discharged in the
committed connectors):
* `baseC2` — the closed-spatial `C²` base of the iterate (the committed
  classical-regularity conjunct; supplied to the climb as its base point);
* `hsrcCube` — the source eigen-cube summability feeding the elliptic gain;
* `hchem` — the chemotaxis-divergence component regularity;
* `data` — the `ConcreteDuhamelDataC7Fields` packaging of the Duhamel kernel. -/
theorem concreteIterate_spatialSlice_seven
    {p : CM2Params} {lo hi t : ℝ}
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
    (data : ConcreteDuhamelDataC7Fields p (utraj t)) :
    SpatialSlice 7 ((concreteU (utraj t)) 7) :=
  assembledAtoms_climb_C2_to_C7_nonCircular
    (U := concreteU (utraj t)) (V := concreteV p (utraj t))
    (F := concreteF p (utraj t))
    baseC2
    (concreteResolverAheadC7_of_sourceEigenCube_summable hsrcCube)
    (concreteChemDivLosesOneAtomC7_of_joint_positive
      hlohi hjoint hpos ht hchem)
    data.toAtom

#print axioms concreteIterate_spatialSlice_seven

end ShenWork.Paper2.ConcreteIterateC7
