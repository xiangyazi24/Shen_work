# Q773 / cron1: per-slice ContinuousOn for coupledChemDivSourceLift

Repo inspected: xiangyazi24/Shen_work
Branch: chatgpt-scratch
Question: is there already a theorem discharging

  forall s,
    ContinuousOn
      (coupledChemDivSourceLift p (conjugatePicardIter p u0 0) s)
      (Set.Icc (0 : Real) 1)

from smoothness of the heat slice and its elliptic resolver?

## Verdict

I did not find a direct committed theorem of the form

  u/v spatial regularity ->
  ContinuousOn (coupledChemDivSourceLift p u s) (Set.Icc 0 1)

nor a theorem specialized to

  coupledChemDivSourceLift p (conjugatePicardIter p u0 0) s.

The current code mostly carries this closed-slice continuity as an input field in the flux-C2 / outer-commute packages.

The closest reusable theorem is slice-level, not coupled-level:

  ShenWork.Paper2.ChemDivSpatialC2.chemDivLift_contDiffOn_two_of_global

It proves

  ContDiffOn Real 2 (chemDivLift p u v) (Set.Icc (0 : Real) 1)

from stronger hypotheses:

  ContDiff Real 4 (intervalDomainLift u)
  ContDiff Real 4 (intervalDomainLift v)
  forall x, 0 < 1 + intervalDomainLift v x

So if those strong fixed-slice hypotheses are available, the desired continuity follows by

  hC2.continuousOn

and then by unfolding/simpa using

  coupledChemDivSourceLift
  ShenWork.IntervalBFormSpectral.chemDivLift

with

  v := coupledChemicalConcentration p (conjugatePicardIter p u0 0) s.

## Relevant hits

1. Definition of coupledChemDivSourceLift

File: ShenWork/PDE/IntervalCoupledSourceTimeC1.lean

  def coupledChemDivSourceLift (p : CM2Params)
      (u : Real -> intervalDomainPoint -> Real) (s : Real) : Real -> Real :=
    intervalDomainLift
      (fun x => intervalDomainChemotaxisDiv p (u s)
        (coupledChemicalConcentration p u s) x)

2. Definition of chemDivLift

File: ShenWork/Paper2/IntervalBFormSpectralHchem.lean

  def chemDivLift (p : CM2Params) (u v : intervalDomainPoint -> Real) : Real -> Real :=
    intervalDomainLift (fun x => intervalDomainChemotaxisDiv p u v x)

Thus a fixed coupled slice is definitionally the corresponding chemDivLift slice.

3. Closest closed-Icc theorem

File: ShenWork/Paper2/IntervalChemDivSpatialC2.lean

  theorem chemDivLift_contDiffOn_two_of_global
      {p : CM2Params} {u v : intervalDomainPoint -> Real}
      (hu : ContDiff Real 4 (intervalDomainLift u))
      (hv : ContDiff Real 4 (intervalDomainLift v))
      (hv_pos : forall x, 0 < 1 + intervalDomainLift v x) :
      ContDiffOn Real 2 (chemDivLift p u v) (Set.Icc (0 : Real) 1)

This is the best theorem to use if closed-interval continuity is required and global C4 of the lifted slice is in hand.

4. Interior-only continuity theorem

File: ShenWork/Paper2/IntervalBankChemSliceFix.lean

  theorem chemDivLift_continuousOn_Ioo
      {p : CM2Params} {u v : intervalDomainPoint -> Real}
      (hC2 : ContDiffOn Real 2 (chemDivLift p u v) (Set.Icc (0 : Real) 1)) :
      ContinuousOn (chemDivLift p u v) (Set.Ioo (0 : Real) 1)

This is only Ioo, not the requested closed Icc. The comments in that file warn that endpoint behavior of the extension is delicate, so do not silently replace an Icc target with Ioo unless the consumer is endpoint-insensitive.

5. The desired continuity is carried as a field

Files where the source continuity appears as an assumption/input:

- ShenWork/PDE/IntervalChemDivOuterCommute.lean
  CoupledChemDivOuterCommuteAtoms.exists_local_slab contains:

    forall eventually s in nhds tau,
      ContinuousOn (coupledChemDivSourceLift p u s) (Set.Icc (0 : Real) 1)

- ShenWork/PDE/IntervalChemDivOuterCommuteProducer.lean
  CoupledChemDivFluxJointC2Hyp carries the same field.

- ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean
  CoupledChemDivFluxFactorJointC2Inputs carries the same field.

- ShenWork/PDE/IntervalChemDivFluxFactorFAC.lean
  FACLocalSlabInputs carries the same field.

These producers propagate the source-continuity input; they do not prove it from factor C2.

6. Sub-goal 3A location

File: ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean

The current 3A hole is the first field while constructing

  CoupledChemDivFluxJointC2Hyp p (conjugatePicardIter p u0 0)

and asks for the local/eventual form:

  forall eventually s in nhds tau,
    ContinuousOn
      (coupledChemDivSourceLift p (conjugatePicardIter p u0 0) s)
      (Set.Icc (0 : Real) 1)

A stronger theorem for all positive s would discharge it on positive windows, provided the local neighborhood stays inside s > 0. The global structure is indexed by arbitrary tau, so if only heat smoothing for s > 0 is available, a positive-window/on version may be cleaner.

## Practical route

For fixed s > 0, try:

1. Prove C4 of the heat cosine representative and resolver representative.
2. If those facts can be stated for intervalDomainLift itself, apply
   chemDivLift_contDiffOn_two_of_global and finish with .continuousOn.
3. If they are only smooth representative facts, follow the cosine-representative pattern in
   chemDivSource_weakH2_of_cosineRep and be careful about endpoints.

Bottom line: no direct per-slice coupled ContinuousOn theorem was found. The closest theorem is
chemDivLift_contDiffOn_two_of_global; the continuity field used by sub-goal 3A is currently assumed/carried by the local packages.
