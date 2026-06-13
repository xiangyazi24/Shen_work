/-
# Iterate order-2 spatial-gradient `ℓ¹` majorant summability (`Hg2u`)

`Hg2u : Summable (boundedWeightJointGradMajorant Btu 2)` is the iterate's
order-2 spatial-gradient bounded-weight majorant summability — the natural
companion of the resolver's committed `grad_summable` (a field of
`PhysicalResolverJointC2Data`).

## The honest accounting

For the **resolver** the gradient majorant summability is a *committed field*:
the elliptic weight `1/(μ+λ_n)` folded into `(v̂_n).re` absorbs one extra
eigenvalue, so the gradient series stays `ℓ¹`.  The **iterate** carries no
elliptic weight: `IteratePicardJointC2Data` only commits the *value* majorant
summability `value_summable` (orders `0,1,2`), i.e. summability of

  `boundedWeightJointMajorant Btu m`  for `m ≤ 2`,

whose order-2 instance is `Btu0·λ_k + 2·Btu1·|kπ| + Btu2`.

The order-2 **gradient** majorant is

  `boundedWeightJointGradMajorant Btu 2 k
      = Btu0·(|kπ|·λ_k) + 2·Btu1·λ_k + Btu2·|kπ|`,

i.e. the order-2 value majorant with **one extra `|kπ|` weight on every term**.
The value weight `valueCosWeight` saturates at `λ_k` for all orders `≥ 2`, so NO
finite-order `value_summable` instance supplies the extra `|kπ|·λ_k = |kπ|³`
factor.  Hence `Hg2u` is genuinely **one spatial order beyond** the committed
iterate value data: it is the iterate's own order-`≤2` gradient summability,
the exact mirror of the resolver's `grad_summable`.

This file isolates that minimal honest leg and proves `Hg2u` from it (and, more
finely, from the three explicit per-order gradient-weighted component
summabilities).  NO eigen-cube ladder; NO resolver `C²`; NO `htime_cont`.
-/
import ShenWork.PDE.IntervalChemDivMixedReprWitness

open Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalResolverJointC2Physical (boundedWeightJointGradMajorant)
open ShenWork.IntervalResolverSpectralJointC2Concrete (gradCosWeight gradCosWeight_nonneg)

noncomputable section

namespace ShenWork.IntervalIterateGradMajorant

/-- The three order-2 gradient-weighted component bounds expand the order-2
gradient majorant exactly:
`boundedWeightJointGradMajorant Bt 2 k
   = |kπ|·λ_k·Bt0 k + 2·λ_k·Bt1 k + |kπ|·Bt2 k`. -/
theorem gradMajorant_two_eq (Bt : ℕ → ℕ → ℝ) (k : ℕ) :
    boundedWeightJointGradMajorant Bt 2 k
      = |(k : ℝ) * Real.pi| * unitIntervalCosineEigenvalue k * Bt 0 k
        + 2 * (unitIntervalCosineEigenvalue k * Bt 1 k)
        + |(k : ℝ) * Real.pi| * Bt 2 k := by
  rw [boundedWeightJointGradMajorant, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  simp only [gradCosWeight, Nat.choose]
  push_cast
  ring

/-- **`Hg2u` from the three honest iterate gradient-weighted component legs.**
The order-2 iterate gradient majorant is summable as soon as the three
gradient-weighted iterate coefficient sums are summable:
`∑ |kπ|·λ_k·Bt0`, `∑ λ_k·Bt1`, `∑ |kπ|·Bt2`. -/
theorem grad2_summable_of_components {Bt : ℕ → ℕ → ℝ}
    (h0 : Summable (fun k : ℕ =>
      |(k : ℝ) * Real.pi| * unitIntervalCosineEigenvalue k * Bt 0 k))
    (h1 : Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * Bt 1 k))
    (h2 : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Bt 2 k)) :
    Summable (boundedWeightJointGradMajorant Bt 2) := by
  have hsum := (h0.add (h1.mul_left 2)).add h2
  refine hsum.congr (fun k => ?_)
  rw [gradMajorant_two_eq]

/-- **`Hg2u` for the iterate, from the iterate's own order-`≤2` gradient
summability** — the exact mirror of the resolver's committed `grad_summable`,
supplied here as the single minimal honest leg for the iterate (which, lacking
the elliptic weight, cannot derive it from `value_summable`).  Feeding this into
`chemDivMixedTimeDerivClosedRepr_of_mkWitness` discharges the regularity half
down to `{PhysicalResolverJointC2Data + IteratePicardJointC2Data + iterate
grad_summable + floor + boundary}`. -/
theorem iterate_Hg2u_of_gradSummable {Bt : ℕ → ℕ → ℝ}
    (hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant Bt m)) :
    Summable (boundedWeightJointGradMajorant Bt 2) :=
  hgrad 2 (by norm_num)

open ShenWork.IntervalChemDivMixedReprWitness
open ShenWork.IntervalIteratePicardJointC2 (IteratePicardJointC2Data)
open ShenWork.IntervalResolverJointC2PhysicalConcrete (PhysicalResolverJointC2Data
  resolverTimeCoeff)
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalChemDivMixedReprConstruct

/-- **Regularity-half capstone with the honest iterate gradient leg explicit.**
`htime_cont` (the `χ₀<0` regularity half) is discharged from
`{PhysicalResolverJointC2Data + IteratePicardJointC2Data + iterate order-`≤2`
gradient summability + floor + boundary}`, where the iterate gradient
summability is the single minimal honest leg this file isolates (the exact
mirror of the resolver's committed `grad_summable`, supplied for the iterate
which lacks the elliptic weight). -/
theorem chemDivMixedClosedRepr_of_iterateGradSummable
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {c : ℕ → ℝ → ℝ}
    {Bt Btu : ℕ → ℕ → ℝ} {τ δ : ℝ}
    (H : PhysicalResolverJointC2Data p u Bt)
    (Hu : IteratePicardJointC2Data u c Btu)
    (HuGrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant Btu m))
    (hfloor : ∀ q : ℝ × ℝ, 0 < 1 + valueSeriesRep (resolverTimeCoeff p u) q)
    (bdry : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ ({0, 1} : Set ℝ),
      coupledChemDivTimeDerivativeLift p u t x =
        mixedAlgebra p.β (valueSeriesRep c) (iterateDtValue c) (iterateDtGrad c)
          (gradSeriesRep c) (valueSeriesRep (resolverTimeCoeff p u))
          (gradSeriesRep (resolverTimeCoeff p u))
          (grad2SeriesRep (resolverTimeCoeff p u)) (resolverDtValue p u)
          (resolverDtGrad p u) (resolverDtGrad2 p u) (t, x)) :
    ChemDivMixedTimeDerivClosedRepr p u τ δ :=
  chemDivMixedTimeDerivClosedRepr_of_mkWitness H Hu
    (iterate_Hg2u_of_gradSummable HuGrad) hfloor bdry

end ShenWork.IntervalIterateGradMajorant
