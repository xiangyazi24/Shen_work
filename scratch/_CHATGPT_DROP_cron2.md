# Q1068 (cron2) — Level0 SORRY 3A: `IntervalIntegrable` from positive-time source regularity

Static GitHub-connector inspection only; I did **not** run Lean locally.

## Verdict

The local-neighborhood part of SORRY 3A is straightforward, but the current exported API does **not** yet contain the final source-slice representative lemma needed to close the hole as a standalone proof body.

The current hole in `IntervalConjugateLevel0BFormSourceOn.lean` is:

```lean
exact Filter.Eventually.of_forall (fun r =>
  sorry) -- [SORRY 3A: IntervalIntegrable from interior smoothness.
```

That should not be `Eventually.of_forall`: the proof only knows the selected neighborhood keeps `r > 0`. The correct outer wrapper is an `Eventually.of_mem` over the chosen ball `Metric.ball s (min 1 (s/2))`.

What is missing is an exported lemma of the shape:

```lean
level0_chemDivSourceLift_intervalIntegrable_of_pos :
  0 < r →
  IntervalIntegrable
    (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) r)
    volume 0 1
```

or, better, a source-representative lemma producing a closed-interval `C²` flux representative whose derivative agrees a.e. with `coupledChemDivSourceLift`.

## Exact reusable integrability lemma

This is the exact core proof that 3A wants. It avoids the false endpoint `ContinuousOn` requirement by proving integrability from a closed-interval `C²` representative and a.e. equality on `Ioc 0 1`, ignoring the singleton endpoint `{1}`.

```lean
import ShenWork.PDE.IntervalEllipticCharacterization

open MeasureTheory Set Filter
open scoped Topology

namespace ShenWork.Paper2.ConjugateLevel0BFormSourceOn

/-- If `f` agrees on the open interval with the ambient derivative of a closed-`Icc`
`C²` representative `Q`, then `f` is interval-integrable on `[0,1]`.

This is the endpoint-safe replacement for trying to prove `ContinuousOn f (Icc 0 1)`.
The endpoint values of `f` may be the `intervalDomainLift` junk/zero-extension values;
they are irrelevant for `IntervalIntegrable` because the interval measure ignores the
single endpoint where `Ioc 0 1` is not open-interior. -/
theorem intervalIntegrable_of_deriv_repr_ae
    {f Q : ℝ → ℝ}
    (hQ : ContDiffOn ℝ 2 Q (Set.Icc (0 : ℝ) 1))
    (h_ioo : ∀ x ∈ Set.Ioo (0 : ℝ) 1, f x = deriv Q x) :
    IntervalIntegrable f volume (0 : ℝ) 1 := by
  have hQint : IntervalIntegrable (deriv Q) volume (0 : ℝ) 1 :=
    ShenWork.IntervalEllipticCharacterization.intervalIntegrable_deriv_of_contDiffOn_two hQ
  refine hQint.congr_ae ?_
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
  have hnull : volume ({(1 : ℝ)} : Set ℝ) = 0 := by simp
  refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  push_neg at hx
  obtain ⟨hxIoc, hne⟩ := hx
  simp only [Set.mem_singleton_iff]
  by_contra hx1
  have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hx1⟩
  exact hne (h_ioo x hxIoo).symm

end ShenWork.Paper2.ConjugateLevel0BFormSourceOn
```

This proof mirrors the already-landed pattern in `IntervalEllipticCharacterization.intervalIntegrable_deriv_of_contDiffOn_two`: prove integrability for the closed representative, then transfer by `congr_ae` after throwing away the endpoint singleton.

## Exact local replacement for SORRY 3A, assuming the positive-time helper is exported

Once the source-slice helper exists, the local SORRY 3A replacement inside `hlocal_slab` should be:

```lean
import ShenWork.Paper2.IntervalConjugateLevel0BFormSourceOn

open MeasureTheory Set Filter
open scoped Topology
open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalDomain)
open ShenWork.IntervalConjugatePicard
  (conjugatePicardIter ConjugateMildExistenceData)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceLift)
open ShenWork.IntervalPicardLevel0SourceTimeC1On (heatCoeff)

namespace ShenWork.Paper2.ConjugateLevel0BFormSourceOn

-- Replacement for the first field after:
--   refine ⟨min 1 (s / 2), lt_min one_pos (half_pos hs_pos), ?_, ?_, ?_⟩
-- where the surrounding context contains:
--   p : CM2Params
--   u₀ : intervalDomainPoint → ℝ
--   c T M M₀ : ℝ
--   hc : 0 < c
--   _hu₀_cont : Continuous u₀
--   _hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀
--   s : ℝ
--   hs : s ∈ Icc c T
--   hs_pos : 0 < s

    · -- Field 1: `IntervalIntegrable` of the source near `s`.
      have hδ_pos : 0 < min (1 : ℝ) (s / 2) :=
        lt_min one_pos (half_pos hs_pos)
      exact Filter.Eventually.of_mem (Metric.ball_mem_nhds s hδ_pos) (fun r hr => by
        have hr_gt_half : s / 2 < r := by
          have hdist := Metric.mem_ball.mp hr
          rw [Real.dist_eq] at hdist
          have hlt := lt_of_lt_of_le hdist (min_le_right (1 : ℝ) (s / 2))
          linarith [(abs_lt.mp hlt).1]
        have hr_pos : 0 < r := by linarith
        exact level0_chemDivSourceLift_intervalIntegrable_of_pos
          (p := p) (u₀ := u₀) (M₀ := M₀)
          _hu₀_cont _hu₀_bound hr_pos)

end ShenWork.Paper2.ConjugateLevel0BFormSourceOn
```

The important detail is the `Metric.ball_mem_nhds` wrapper. It proves the eventual slice only on the positive-time ball, instead of incorrectly asking for all `r : ℝ`.

## The missing helper to export

The exact helper that should be added/exported can be phrased through the reusable lemma above:

```lean
import ShenWork.Paper2.IntervalConjugateLevel0BFormSourceOn
import ShenWork.Paper2.IntervalChemDivSpatialC2
import ShenWork.PDE.IntervalEllipticCharacterization

open MeasureTheory Set Filter
open scoped Topology
open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalDomain)
open ShenWork.IntervalConjugatePicard
  (conjugatePicardIter)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceLift coupledChemicalConcentration)
open ShenWork.IntervalPicardLevel0SourceTimeC1On (heatCoeff)
open ShenWork.Paper2.ChemDivSpatialC2
  (chemFluxFun chemFluxDeriv_contDiff_two)

namespace ShenWork.Paper2.ConjugateLevel0BFormSourceOn

/-- Positive-time Level0 chem-div source slice integrability.

This is the missing exported 3A helper.  Its proof should construct the smooth
cosine representative `Q_r` for the chemotactic flux at time `r`, prove
`ContDiffOn ℝ 2 Q_r (Icc 0 1)`, prove the open-interval agreement
`coupledChemDivSourceLift ... r x = deriv Q_r x`, and then call
`intervalIntegrable_of_deriv_repr_ae`. -/
theorem level0_chemDivSourceLift_intervalIntegrable_of_pos
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ} {M₀ r : ℝ}
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hr_pos : 0 < r) :
    IntervalIntegrable
      (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) r)
      volume (0 : ℝ) 1 := by
  -- Required construction, not currently exported as a theorem:
  --   ∃ Qr : ℝ → ℝ,
  --     ContDiffOn ℝ 2 Qr (Icc 0 1) ∧
  --     ∀ x ∈ Ioo 0 1,
  --       coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) r x = deriv Qr x
  --
  -- Once that representative theorem exists, the proof body is exactly:
  --
  --   obtain ⟨Qr, hQr_C2, hQr_agree⟩ :=
  --     level0_chemDivSource_derivRepr_of_pos
  --       (p := p) (u₀ := u₀) (M₀ := M₀)
  --       hu₀_cont hu₀_bound hr_pos
  --   exact intervalIntegrable_of_deriv_repr_ae hQr_C2 hQr_agree
  --
  -- This is not fillable from current exports: the closed representative theorem
  -- `level0_chemDivSource_derivRepr_of_pos` does not exist yet.
  admit

end ShenWork.Paper2.ConjugateLevel0BFormSourceOn
```

Do **not** add the `admit`; the block above documents the missing exported theorem and the exact final two lines after it exists. The intended source representative theorem is the actual remaining work for 3A.

## Why current exports do not close 3A by themselves

1. `PhysicalResolverJointC2Data` gives interior joint `ContDiffAt ℝ 2` for the resolver value and gradient, but it does not itself package a closed-interval source representative or source-slice `IntervalIntegrable` theorem.

2. `chemDivSource_weakH2_of_cosineRep` constructs `IntervalWeakH2Neumann (chemDivLift p u v)`, but `IntervalWeakH2Neumann` only stores integrability of `secondDeriv`; it does not expose `IntervalIntegrable` of the source slice itself.

3. `level0_chemDiv_envelope_summable` internally builds an `hSup` package containing interval-integrability of slices on a fixed positive window `[c,T]`, but that information is not exported; the theorem result erases it into an envelope.

4. The local 3A obligation is a full-neighborhood statement near `s`. At endpoints of `[c,T]`, the neighborhood cannot be kept inside `[c,T]`, so the proof must be genuinely positive-time-local, not merely a reuse of the `[c,T]` window hypotheses.

## Minimal work item to make 3A close

Add a small exported helper, preferably in `IntervalConjugateLevel0BFormSourceOn.lean` or a new Level0 source-integrability file imported by it:

```lean
level0_chemDivSource_derivRepr_of_pos :
  0 < r →
  ∃ Qr : ℝ → ℝ,
    ContDiffOn ℝ 2 Qr (Icc (0 : ℝ) 1) ∧
    ∀ x ∈ Ioo (0 : ℝ) 1,
      coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) r x = deriv Qr x
```

Then `level0_chemDivSourceLift_intervalIntegrable_of_pos` is a two-line call to `intervalIntegrable_of_deriv_repr_ae`, and SORRY 3A closes with the `Metric.ball_mem_nhds` wrapper shown above.
