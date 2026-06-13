/-
# u-side joint `C²` of the Picard iterate from its parabolic space-time regularity

The Picard iterate `u` is a Neumann cosine series
`intervalDomainLift (u t) x = ∑' k, c k t · cos(kπx)` with coefficients
`c k t = iterateCoeff …` (`IntervalPicardIterateRestart.iterate_lift_eq_cosineSeries`).
Its joint `(t,x)` `ContDiffAt ℝ 2` — the FAC u-side field `hu_c2` — follows from
the SAME bounded-weight joint-`C²` assembler used for the resolver
(`IntervalResolverJointC2Physical.boundedWeightJointSeries_contDiff_two`), but the
iterate carries NO elliptic weight `1/(μ+λ)`: the majorant is built directly from
the iterate's own coefficient space-time regularity —
* `coeff_contDiff` : each `c k` is `C²` in `t` (the honest iterate time-`C²` leg,
  isolated as `IterateSourceTimeData.time2` / `d²ₜu`);
* `coeff_bound`    : three-time-order bounds `Bt i k` (spatial-`C²` IBP decay
  `λ_k|a_k|`, `(kπ)|d_t a_k|`, `|d²_t a_k|`);
* `value_summable` : the bounded-weight VALUE joint majorant is `ℓ¹`
  (`|a_k| ≤ C/(kπ)²` + the time-derivative coefficient decay).

NO eigen-cube ladder, NO `DuhamelSourceTimeC2Coeff`, NO resolver-`C²`/FAC field.
The series equality is the committed honest input; the assembly is pure
bounded-weight summability, mirroring `coupledChemical_jointContDiffAt_two`.
-/
import ShenWork.PDE.IntervalResolverJointC2PhysicalConcrete

open Filter Topology Set
open ShenWork.IntervalResolverJointC2Physical
open ShenWork.IntervalResolverSpectralJointC2Concrete (valueCosWeight)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)

noncomputable section

namespace ShenWork.IntervalIteratePicardJointC2

/-- **The honest iterate space-time regularity datum.**  The iterate's own cosine
coefficient family `c k t` is `C²` in time, with three-time-order bounds `Bt`
whose bounded-weight VALUE joint majorant is summable — and the iterate slice
equals its cosine series on `[0,1]`.  This carries the iterate's parabolic
space-time `C²` directly (NO elliptic weight, NO `λ²`/`λ³` ladder, NO
`DuhamelSourceTimeC2Coeff`). -/
structure IteratePicardJointC2Data
    (u : ℝ → intervalDomainPoint → ℝ) (c : ℕ → ℝ → ℝ) (Bt : ℕ → ℕ → ℝ) : Prop where
  /-- The iterate slice equals its cosine series on `[0,1]`. -/
  lift_eq_series : ∀ {t x : ℝ}, x ∈ Icc (0 : ℝ) 1 →
    intervalDomainLift (u t) x = ∑' k : ℕ, c k t * cosineMode k x
  /-- Each coefficient is `C²` in time (the honest iterate time-`C²` leg). -/
  coeff_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (c k)
  /-- Three-time-order coefficient bounds. -/
  coeff_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
    ‖iteratedFDeriv ℝ i (c k) t‖ ≤ Bt i k
  /-- The bounded-weight VALUE joint majorant is summable (orders `0,1,2`). -/
  value_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointMajorant Bt m)

/-- **The u-side `hu_c2` producer** — joint `ContDiffAt ℝ 2` of the lifted Picard
iterate, via the bounded-weight VALUE assembler applied to the iterate's own
coefficient family.  This is the direct mirror of `coupledChemical_jointContDiffAt_two`
with the elliptic weight removed: the majorant `Bt` is the iterate's own
space-time coefficient regularity.  NO eigen-cube ladder, NO resolver-`C²` field. -/
theorem iterate_lift_jointContDiffAt_two
    {u : ℝ → intervalDomainPoint → ℝ} {c : ℕ → ℝ → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : IteratePicardJointC2Data u c Bt) {s x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x) := by
  have hseries : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => ∑' k : ℕ, boundedWeightJointTerm c k q) :=
    boundedWeightJointSeries_contDiff_two H.coeff_contDiff
      (fun i k t hi => H.coeff_bound i k t hi) H.value_summable
  refine (hseries.contDiffAt).congr_of_eventuallyEq ?_
  have hmem : {q : ℝ × ℝ | q.2 ∈ Ioo (0 : ℝ) 1} ∈ 𝓝 (s, x) :=
    (isOpen_Ioo.preimage continuous_snd).mem_nhds hx
  filter_upwards [hmem] with q hq
  have he := H.lift_eq_series (t := q.1) (x := q.2) (Ioo_subset_Icc_self hq)
  simpa [boundedWeightJointTerm] using he

/-- **u-side slab discharge.**  For every `x ∈ Ioo 0 1` and every `s` the Picard
iterate's joint `C²` field `hu_c2` holds, discharged from the honest iterate
space-time regularity — exactly the FAC `FACLocalSlabInputs` / `other` u-side
field. -/
theorem iterate_hu_c2_slab
    {u : ℝ → intervalDomainPoint → ℝ} {c : ℕ → ℝ → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : IteratePicardJointC2Data u c Bt) :
    ∀ x ∈ Ioo (0 : ℝ) 1, ∀ _s : ℝ,
      ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (_s, x) :=
  fun _x hx _s => iterate_lift_jointContDiffAt_two H hx

end ShenWork.IntervalIteratePicardJointC2
