# Q1119 (cron3): resolver C⁴ source summability route

## Verdict

For the sorry at `IntervalConjugateLevel0BFormSourceOn.lean` around the `hV_C4` proof, the route is:

1. Reduce the resolver-source coefficient to the cosine coefficient of the power source
   `x ↦ p.ν * intervalDomainLift (conjugatePicardIter p u₀ 0 r) x ^ p.γ`.
2. Do **not** try to prove resolver regularity directly from the denominator at this call site. The current theorem `intervalResolverLiftR_contDiff_four` asks for the stronger source-side summability
   `Summable (fun k => λ_k * |sourceCoeff_k|)`.
3. Prove that summability by applying `IntervalSourceDecayQuantitative.intervalWeakH4Neumann_eigenvalue_L1_summable` to a depth-2 weak Neumann certificate for the power source.
4. Build the two weak-H² certificates from the smooth cosine representative
   `U_cos x = ∑' k, exp (-r * λ_k) * heatCoeff u₀ k * cosineMode k x`, then transfer the first certificate to the zero-extension source by `[0,1]` agreement.

The main catch is not the IBP/summability theorem. The main catch is **positivity for the representative**. Since `p.γ` is only known positive as a real, not necessarily a natural/integer exponent, the global `ContDiff.rpow_const_of_ne` route needs `U_cos x ≠ 0` for all `x`. You get that from positivity on `[0,1]` plus cosine symmetry/periodicity. At the line-1084 local block, `r > 0` alone does not supply this positivity unless an appropriate heat-floor or positive-window hypothesis is available in scope.

## What `intervalResolverLiftR_contDiff_four` actually requires

In `ShenWork/Paper2/IntervalResolverHighRegularity.lean`, the theorem is:

`intervalResolverLiftR_contDiff_four : Summable (fun k => unitIntervalCosineEigenvalue k * |(intervalNeumannResolverSourceCoeff p u k).re|) -> ContDiff ℝ 4 (intervalResolverLiftR p u)`.

So the current API does **not** ask for the denominator-weighted sequence directly. Internally it uses the elliptic coefficient identity to prove

`λ_k * |v̂_k.re| ≤ |â_k.re|`,

and therefore

`λ_k * (λ_k * |v̂_k.re|) ≤ λ_k * |â_k.re|`.

That is exactly why source eigenvalue-weighted `ℓ¹` is sufficient for C⁴ of the resolver cosine series.

Your observation about the denominator is mathematically correct: if one opened the resolver multiplier directly, the C⁴ target wants summability of

`λ_k^2 / (p.μ + λ_k) * |â_k|`,

and this is bounded by `λ_k * |â_k|` because `λ_k ≤ p.μ + λ_k`. That is what the current theorem already packages, but it packages it behind the stronger, cleaner hypothesis `Summable (λ_k * |â_k|)`. A weaker theorem could be added, but it would be a new API and is not necessary for this sorry.

## Is `intervalWeakH4Neumann_eigenvalue_L1_summable` the right tool?

Yes, for the existing API it is the right tool.

The theorem in `ShenWork/PDE/IntervalSourceDecayQuantitative.lean` has exactly the needed shape after rewriting resolver-source coefficients:

`intervalWeakH4Neumann_eigenvalue_L1_summable hf hf'' : Summable (fun k => λ_k * |cosineCoeffs f k|)`.

Here:

* `hf : IntervalWeakH2Neumann f`,
* `hf'' : IntervalWeakH2Neumann hf.secondDeriv`,
* `f` should be the resolver power source on the physical interval, i.e. `fun x => p.ν * intervalDomainLift w x ^ p.γ`, where `w = conjugatePicardIter p u₀ 0 r`.

The repo already has the coefficient bridge in `IntervalDomainLogisticWeakH2Adapter.lean`:

`resolverSourceCoeff_re_eq_cosineCoeffs p w k : (intervalNeumannResolverSourceCoeff p w k).re = cosineCoeffs (fun x => p.ν * intervalDomainLift w x ^ p.γ) k`.

Use that theorem instead of reproving the `simp only` bridge inline.

## How to build the depth-2 Neumann data

There are two possible meanings of “NeumannTower” in this repository:

* `IntervalIBPCoeffExtraction.NeumannTower g j`, a general tower used by higher-order coefficient extraction.
* The two weak certificates consumed by `intervalWeakH4Neumann_eigenvalue_L1_summable`, namely `IntervalWeakH2Neumann f` and `IntervalWeakH2Neumann hf.secondDeriv`.

For this sorry, you do **not** need the general `NeumannTower` structure. Build the two weak-H² certificates directly. This is shorter and aligns with the theorem you want to use.

Recommended construction:

1. Set `w := conjugatePicardIter p u₀ 0 r`.
2. Set
   `U_cos x := ∑' k, (Real.exp (-r * unitIntervalCosineEigenvalue k) * heatCoeff u₀ k) * cosineMode k x`.
3. Use `heatSemigroup_contDiff_four _hu₀_bound hr_pos` to get `hU_C4 : ContDiff ℝ 4 U_cos`.
4. Use `hagree_zero` to get `intervalDomainLift w = U_cos` on `[0,1]`.
5. Prove `U_cos` is even and symmetric about `1`; equivalently, use the same `cosineMode_neg` / period-2 helpers already written earlier in the same file.
6. From `[0,1]` positivity of `intervalDomainLift w` and `[0,1]` agreement, get positivity of `U_cos` on `[0,1]`; then use evenness + period 2/reflection to get `∀ x, 0 < U_cos x`.
7. Define the smooth representative
   `g_smooth := fun x => p.ν * U_cos x ^ p.γ`.
8. Use global positivity and `hU_C4.rpow_const_of_ne` to show `hg_C4 : ContDiff ℝ 4 g_smooth`.
9. Build `hf_smooth_H2 : IntervalWeakH2Neumann g_smooth` with `intervalWeakH2Neumann_of_contDiffOn`:
   * `ContDiffOn ℝ 2 g_smooth (Icc 0 1)` comes from `hg_C4.of_le`.
   * `deriv g_smooth 0 = 0` follows from evenness of `g_smooth`.
   * `deriv g_smooth 1 = 0` follows from symmetry `g_smooth (2 - x) = g_smooth x`.
   * the one-sided tendsto hypotheses follow from continuity of `deriv g_smooth`.
10. Transfer this first certificate from `g_smooth` to the actual zero-extension source with `IntervalWeakH2Neumann.congr_on_Icc`. This is the important simplification: the transfer preserves the chosen `secondDeriv`, so the resulting `hf_H2.secondDeriv` is still definitionally the smooth `deriv (deriv g_smooth)`.
11. Build `hf''_H2 : IntervalWeakH2Neumann hf_H2.secondDeriv` by applying `intervalWeakH2Neumann_of_contDiffOn` to `deriv (deriv g_smooth)`:
   * `ContDiffOn ℝ 2 (deriv (deriv g_smooth)) (Icc 0 1)` comes from `hg_C4`.
   * its derivative is `deriv (deriv (deriv g_smooth))`.
   * this third derivative vanishes at `0` and `1` because `g_smooth` is even and symmetric about `1`; the parity chain is `g` even -> `g'` odd -> `g''` even -> `g'''` odd.
   * the one-sided tendsto hypotheses follow from continuity of `g'''`.
12. Apply `intervalWeakH4Neumann_eigenvalue_L1_summable hf_H2 hf''_H2`.
13. Rewrite back through `resolverSourceCoeff_re_eq_cosineCoeffs` and feed `intervalResolverLiftR_contDiff_four`.

This avoids the more complicated line-315 route where the first `IntervalWeakH2Neumann` is built directly for the zero-extension source and the second certificate then requires an algebraic reconstruction of the weak-Laplacian identity. That algebraic reconstruction works in principle, but it is self-inflicted. If the first certificate is built from `g_smooth` and only then transferred by `congr_on_Icc`, the second derivative remains the smooth representative’s second derivative.

## The important positivity caveat at line 1084

The local block around line 1084 proves integrability near a point `s` by taking a small ball around `s` and then an arbitrary `r` in that ball. It proves `hr_pos' : 0 < r`, but the visible code at that site does not by itself show

`∀ x ∈ Icc (0 : ℝ) 1, 0 < intervalDomainLift (conjugatePicardIter p u₀ 0 r) x`.

If the surrounding theorem has only a window positivity assumption `_hpos : ∀ σ ∈ Icc c T, ...`, be careful: a metric ball around an endpoint `s ∈ Icc c T` can contain `r` outside `[c,T]`. For the C⁴ resolver-source proof, you need positivity of the heat profile at that actual `r`, not just positivity at `s`.

There are three clean ways to resolve this:

1. **Best if available:** use a heat-floor theorem from positive initial data. The repo has `IntervalConjugatePicardInfThreshold.intervalFullSemigroupOperator_ge_paperPositiveFloor`, which gives a positive lower bound for the heat semigroup at every `t > 0` from `PaperPositiveInitialDatum`. If the current theorem can access such a datum, this is the most robust source of `hpos_r`.
2. **Window-local variant:** if you only need the proof for `r ∈ [c,T]`, shrink the eventual neighborhood to remain in the window and carry `r ∈ Icc c T`; then use `_hpos r hr_window`.
3. **Add a local assumption/helper:** factor the resolver-source summability lemma so it explicitly takes `hpos_r : ∀ x ∈ Icc 0 1, 0 < intervalDomainLift w x`. Then each call site must supply that hypothesis honestly.

I would not hide this inside `intervalResolverLiftR_contDiff_four`, because the resolver theorem should remain a spectral regularity theorem. Positivity is only needed to make the nonlinear source `ν * u^γ` smooth for real `γ`.

## Suggested helper shape

Below is the helper shape I would add before the main proof, or in a small adjacent file imported by `IntervalConjugateLevel0BFormSourceOn.lean`. It is intentionally factored around a single time `r` and a supplied positivity hypothesis.

```lean
import ShenWork.Paper2.IntervalConjugateLevel0BFormSourceOn
import ShenWork.PDE.IntervalSourceDecayQuantitative
import ShenWork.Paper2.IntervalDomainLogisticWeakH2Adapter

open MeasureTheory Set Filter
open scoped Topology BigOperators
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.PDE.IntervalMildSourceDecayHelper (IntervalWeakH2Neumann)
open ShenWork.Paper2.HeatSemigroupHighRegularity (heatSemigroup_contDiff_four)

noncomputable section

namespace ShenWork.Paper2.ConjugateLevel0BFormSourceOn

/-- Single-time resolver-source eigenvalue L¹ summability for the level-0 heat profile.

This is the lemma that should discharge the `intervalResolverLiftR_contDiff_four`
hypothesis.  The proof body should be filled with the route described above:
build the smooth power-source representative `g_smooth := p.ν * U_cos ^ p.γ`,
construct the two weak-H² Neumann certificates, apply
`intervalWeakH4Neumann_eigenvalue_L1_summable`, and rewrite the resolver-source
coefficient real part to `cosineCoeffs` using
`resolverSourceCoeff_re_eq_cosineCoeffs`.
-/
theorem level0_resolverSourceCoeff_eigenvalue_L1_summable
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ} {r M₀ : ℝ}
    (hr_pos : 0 < r)
    (hu₀_bound : ∀ k,
      |ShenWork.IntervalPicardLevel0SourceTimeC1On.heatCoeff u₀ k| ≤ M₀)
    (hpos_r : ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 r) x) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        |(ShenWork.PDE.intervalNeumannResolverSourceCoeff p
          (conjugatePicardIter p u₀ 0 r) k).re|) := by
  classical

  set w := conjugatePicardIter p u₀ 0 r
  set U_cos : ℝ → ℝ := fun x => ∑' k : ℕ,
    (Real.exp (-r * unitIntervalCosineEigenvalue k) *
      ShenWork.IntervalPicardLevel0SourceTimeC1On.heatCoeff u₀ k) * cosineMode k x

  have hU_C4 : ContDiff ℝ 4 U_cos := by
    simpa [U_cos] using heatSemigroup_contDiff_four hu₀_bound hr_pos

  have hU_agree : ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift w x = U_cos x := by
    intro x hx
    -- Same theorem used at the existing call sites.
    simpa [w, U_cos] using
      ShenWork.IntervalPicardIterateRepresentation.hagree_zero
        p u₀ hr_pos (by infer_instance) hu₀_bound hx

  -- Prove these with the same cosine-mode parity/period helpers already used earlier
  -- in `IntervalConjugateLevel0BFormSourceOn.lean`.
  have hU_even : ∀ x, U_cos (-x) = U_cos x := by
    -- `tsum_congr`, `cosineMode k (-x) = cosineMode k x`.
    sorry

  have hU_symm1 : ∀ x, U_cos (2 - x) = U_cos x := by
    -- Combine period two with evenness: `2 - x = -x + 2`.
    sorry

  have hU_period : Function.Periodic U_cos 2 := by
    -- Direct `tsum_congr` from `cosineMode k (x + 2) = cosineMode k x`.
    sorry

  have hU_pos_all : ∀ x, 0 < U_cos x := by
    -- Reduce arbitrary `x` to `[0,1]` using `hU_period`, `hU_even`, and `hU_symm1`;
    -- on `[0,1]`, use `hU_agree` and `hpos_r`.
    sorry

  set g_smooth : ℝ → ℝ := fun x => p.ν * U_cos x ^ p.γ

  have hg_C4 : ContDiff ℝ 4 g_smooth := by
    have hne : ∀ x, U_cos x ≠ 0 := fun x => ne_of_gt (hU_pos_all x)
    simpa [g_smooth] using
      contDiff_const.mul (hU_C4.rpow_const_of_ne hne)

  have hg_even : ∀ x, g_smooth (-x) = g_smooth x := by
    intro x
    simp [g_smooth, hU_even]

  have hg_symm1 : ∀ x, g_smooth (2 - x) = g_smooth x := by
    intro x
    simp [g_smooth, hU_symm1]

  have hf_smooth_H2 : IntervalWeakH2Neumann g_smooth := by
    -- Use `intervalWeakH2Neumann_of_contDiffOn`.
    -- Boundary data: `deriv g_smooth 0 = 0` from evenness,
    -- and `deriv g_smooth 1 = 0` from symmetry about 1.
    -- Tendsto data follows from continuity of `deriv g_smooth`.
    sorry

  have hsrc_agree : ∀ x ∈ Icc (0 : ℝ) 1,
      g_smooth x = p.ν * intervalDomainLift w x ^ p.γ := by
    intro x hx
    simp [g_smooth, hU_agree x hx]

  have hf_H2 : IntervalWeakH2Neumann
      (fun x : ℝ => p.ν * intervalDomainLift w x ^ p.γ) := by
    -- The adapter theorem is in `IntervalDomainLogisticWeakH2Adapter.lean`.
    exact hf_smooth_H2.congr_on_Icc hsrc_agree

  have hf''_H2 : IntervalWeakH2Neumann hf_H2.secondDeriv := by
    -- Because `congr_on_Icc` preserves the `secondDeriv` field, this target is
    -- definitionally the H² certificate for `deriv (deriv g_smooth)`.
    -- Use `intervalWeakH2Neumann_of_contDiffOn` again.
    -- Boundary data is `g_smooth''' 0 = 0` and `g_smooth''' 1 = 0`, obtained from
    -- parity/symmetry: `g` even/symmetric => `g'` odd/antisymmetric =>
    -- `g''` even/symmetric => `g'''` odd/antisymmetric.
    sorry

  have hcoeff_sum : Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        |cosineCoeffs (fun x : ℝ => p.ν * intervalDomainLift w x ^ p.γ) k|) := by
    exact ShenWork.IntervalSourceDecayQuantitative
      .intervalWeakH4Neumann_eigenvalue_L1_summable hf_H2 hf''_H2

  simpa [w] using hcoeff_sum.congr (fun k => by
    rw [ShenWork.IntervalDomainLogisticWeakH2Adapter
      .resolverSourceCoeff_re_eq_cosineCoeffs p w k])

end ShenWork.Paper2.ConjugateLevel0BFormSourceOn
```

Two notes about the skeleton:

* I used `by infer_instance` as a placeholder for the continuity argument in `hagree_zero` only because I did not re-check that exact local argument through Lean. In the existing file, the call passes `_hu₀_cont` and `_hu₀_bound`; the real helper should include `hu₀_cont : Continuous u₀` if `hagree_zero` requires it.
* The proof should factor the parity lemmas rather than copy/paste them twice. The file already has local versions earlier; making public helper lemmas for heat cosine series evenness/periodicity/symmetry will make the line-1084 proof much smaller.

## How the sorry should then close

At the target site, after you have a proof of positivity for the actual time `r`, the replacement should be small:

```lean
have hsrcL1 : Summable (fun k : ℕ =>
    unitIntervalCosineEigenvalue k *
      |(ShenWork.PDE.intervalNeumannResolverSourceCoeff p
        (conjugatePicardIter p u₀ 0 r) k).re|) := by
  exact level0_resolverSourceCoeff_eigenvalue_L1_summable
    p hr_pos' _hu₀_bound hpos_r

have hV_C4 : ContDiff ℝ 4 V_cos := by
  simpa [hV_cos_def] using
    intervalResolverLiftR_contDiff_four (p := p)
      (u := conjugatePicardIter p u₀ 0 r) hsrcL1
```

The only nontrivial missing input here is `hpos_r`. If the proof is still inside a neighborhood argument and `r` is not known to lie in the positive window, use a positive-time heat floor from the initial datum, or modify the neighborhood/window argument so that `r ∈ Icc c T` is available.

## Should a more direct denominator-weighted theorem be added?

It is possible, but I would not do it first.

A direct theorem would look like:

`Summable (fun k => unitIntervalCosineEigenvalue k ^ 2 / (p.μ + unitIntervalCosineEigenvalue k) * |sourceCoeff k|) -> ContDiff ℝ 4 (intervalResolverLiftR p u)`.

That theorem is mathematically closer to the exact multiplier, but it does not remove the real nonlinear-analysis work. You still need a source coefficient decay strong enough to make that weighted series summable. Quartic decay of the power-source coefficients gives it immediately, and the existing `intervalWeakH4Neumann_eigenvalue_L1_summable` already packages precisely that decay in the source-side form expected by `intervalResolverLiftR_contDiff_four`.

So the efficient proof route is:

`C⁴ heat representative + positive power source -> two weak-H² Neumann certificates -> intervalWeakH4Neumann_eigenvalue_L1_summable -> intervalResolverLiftR_contDiff_four`.

The direct denominator theorem is a nice optional refactor, not the shortest way to discharge this sorry.
