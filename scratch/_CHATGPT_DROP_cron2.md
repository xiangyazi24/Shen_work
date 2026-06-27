# Q1123 (cron2) — resolver-source eigenvalue summability

Static GitHub-connector inspection only; I did **not** run Lean locally.

## Bottom line

For the `hV_C4` hole under

```lean
have hV_C4 : ContDiff ℝ 4 V_cos := by
  apply intervalResolverLiftR_contDiff_four
  -- goal: Summable (fun k => λ_k * |(resolverSourceCoeff p w k).re|)
```

use the depth-2 weak-H² route, but build the first certificate for the actual source with the **smooth** second derivative:

```lean
secondDeriv := deriv (deriv g_smooth)
```

This avoids the harder algebraic transfer from the zero-extension helper’s `secondDeriv`.

Useful checked names:

```lean
ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann
ShenWork.PDE.IntervalMildSourceDecayHelper.intervalWeakH2Neumann_of_contDiffOn
ShenWork.IntervalSourceDecayQuantitative.intervalWeakH4Neumann_eigenvalue_L1_summable
ShenWork.Paper2.IntervalResolverHighRegularity.intervalResolverLiftR_contDiff_four
ShenWork.IntervalDomainLogisticWeakH2Adapter.resolverSourceCoeff_re_eq_cosineCoeffs
ShenWork.IntervalSemigroupNeumann.heatCoeff_eigenvalue_summable
```

Add these imports explicitly if not already available transitively:

```lean
import ShenWork.Paper2.IntervalDomainLogisticWeakH2Adapter
import ShenWork.PDE.IntervalSourceDecayQuantitative
```

## Positivity prerequisite

Before the `hV_C4` proof, produce:

```lean
have hU_pos_Icc : ∀ x ∈ Icc (0 : ℝ) 1, 0 < U_cos x := by
  -- envelope theorem, if the local time is in [c,T]:
  --   intro x hx
  --   have h := _hpos r hr_Icc x hx
  --   rw [hU_agree x hx] at h
  --   exact h
  --
  -- local-slab theorem, where r is only known positive:
  --   add `(hu₀pos : PositiveInitialDatum intervalDomain u₀)` and use
  --   intervalFullSemigroupOperator_pos_of_positiveInitialDatum.
  intro x hx
  rw [← hU_agree x hx]
  simpa [intervalDomainLift, conjugatePicardIter, hx] using
    ShenWork.Paper2.BFormPositiveDatumNegPart
      .intervalFullSemigroupOperator_pos_of_positiveInitialDatum
        hu₀pos hr_pos' x
```

If you do not want to pass `PositiveInitialDatum`, the minimal assumptions are `hu₀_nonneg : ∀ x, 0 ≤ u₀ x` plus `hu₀_pos_somewhere : ∃ x, 0 < u₀ x`. Nonnegativity alone does not give strict positivity.

## Pasteable proof body

This code is meant to be pasted **after** `apply intervalResolverLiftR_contDiff_four`; it assumes `hU_pos_Icc` is already in scope.

```lean
import ShenWork.Paper2.IntervalDomainLogisticWeakH2Adapter
import ShenWork.PDE.IntervalSourceDecayQuantitative

open MeasureTheory Set Filter
open scoped Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalDomain)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalPicardLevel0SourceTimeC1On (heatCoeff)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.PDE.IntervalMildSourceDecayHelper (IntervalWeakH2Neumann)

set w := conjugatePicardIter p u₀ 0 r with hw_def
set b : ℕ → ℝ := fun n =>
  Real.exp (-r * unitIntervalCosineEigenvalue n) * heatCoeff u₀ n with hb_def

have hbc_sum : Summable (fun n : ℕ => unitIntervalCosineEigenvalue n * |b n|) := by
  simpa [b, hb_def] using
    ShenWork.IntervalSemigroupNeumann.heatCoeff_eigenvalue_summable
      hr_pos' _hu₀_bound

have hagree_w : Set.EqOn (intervalDomainLift w)
    (fun x : ℝ => ∑' n : ℕ, b n * cosineMode n x) (Icc (0 : ℝ) 1) := by
  intro x hx
  simpa [w, hw_def, b, hb_def, hU_cos_def] using hU_agree x hx

have hpos_w : ∀ x ∈ Icc (0 : ℝ) 1, 0 < intervalDomainLift w x := by
  intro x hx
  have hposU := hU_pos_Icc x hx
  have h := hU_agree x hx
  simpa [w, hw_def] using (h.symm ▸ hposU)

have cosineMode_neg' : ∀ k x, cosineMode k (-x) = cosineMode k x := by
  intro k x
  unfold cosineMode
  rw [show (k : ℝ) * Real.pi * (-x) = -((k : ℝ) * Real.pi * x) from by ring,
    Real.cos_neg]

have cosineMode_add_two' : ∀ k x, cosineMode k (x + 2) = cosineMode k x := by
  intro k x
  unfold cosineMode
  rw [show (k : ℝ) * Real.pi * (x + 2) =
      (k : ℝ) * Real.pi * x + ((k : ℤ) : ℝ) * (2 * Real.pi) from by
        push_cast; ring,
    Real.cos_add_int_mul_two_pi _ (k : ℤ)]

have hU_even : ∀ x, U_cos (-x) = U_cos x := by
  intro x
  simp only [hU_cos_def]
  exact tsum_congr (fun k => by congr 1; exact cosineMode_neg' k x)

have hU_period : Function.Periodic U_cos 2 := by
  intro x
  simp only [hU_cos_def]
  exact tsum_congr (fun k => by congr 1; exact cosineMode_add_two' k x)

have hU_symm1 : ∀ x, U_cos (2 - x) = U_cos x := by
  intro x
  rw [show (2 : ℝ) - x = (-x) + 2 from by ring]
  rw [hU_period (-x), hU_even x]

have hU_pos_all : ∀ x : ℝ, 0 < U_cos x := by
  intro x
  set n : ℤ := ⌊x / 2⌋
  set y : ℝ := x - n * 2
  have hxy : U_cos x = U_cos y := by
    show U_cos x = U_cos (x - ↑n * 2)
    exact (hU_period.sub_int_mul_eq n).symm
  have hy_lo : 0 ≤ y := by
    have := Int.floor_le (x / 2); linarith
  have hy_hi : y < 2 := by
    have := Int.lt_floor_add_one (x / 2); linarith
  rw [hxy]
  by_cases hy1 : y ≤ 1
  · exact hU_pos_Icc y ⟨hy_lo, hy1⟩
  · simp only [not_le] at hy1
    rw [(hU_symm1 y).symm]
    exact hU_pos_Icc (2 - y) ⟨by linarith, by linarith⟩

set g_smooth : ℝ → ℝ := fun x => p.ν * U_cos x ^ p.γ with hg_smooth_def

have hg_C4 : ContDiff ℝ 4 g_smooth := by
  show ContDiff ℝ 4 (fun x : ℝ => p.ν * U_cos x ^ p.γ)
  exact contDiff_const.mul
    (hU_C4.rpow_const_of_ne (fun x => ne_of_gt (hU_pos_all x)))

have hg_C2_on : ContDiffOn ℝ 2 g_smooth (Icc (0 : ℝ) 1) :=
  (hg_C4.of_le (by norm_num)).contDiffOn

have hg_even : ∀ x, g_smooth (-x) = g_smooth x := by
  intro x; simp only [hg_smooth_def, hU_even]

have hg_symm1 : ∀ x, g_smooth (2 - x) = g_smooth x := by
  intro x; simp only [hg_smooth_def, hU_symm1]

have deriv_even_odd : ∀ {g : ℝ → ℝ}, ContDiff ℝ 1 g →
    (∀ x, g (-x) = g x) → ∀ x, deriv g (-x) = -(deriv g x) := by
  intro g _hg heven x
  have h1 := deriv_comp_neg (f := g) (x := x)
  rw [show (fun x : ℝ => g (-x)) = g from funext heven] at h1
  linarith

have deriv_odd_even : ∀ {g : ℝ → ℝ}, ContDiff ℝ 1 g →
    (∀ x, g (-x) = -(g x)) → ∀ x, deriv g (-x) = deriv g x := by
  intro g _hg hodd x
  have h1 := deriv_comp_neg (f := g) (x := x)
  rw [show (fun x : ℝ => g (-x)) = fun x : ℝ => -(g x) from funext hodd] at h1
  simp [deriv_neg] at h1
  linarith

have odd_zero : ∀ {g : ℝ → ℝ}, (∀ x, g (-x) = -(g x)) → g 0 = 0 := by
  intro g hodd
  have h := hodd 0
  rw [neg_zero] at h
  linarith

have hg'_odd : ∀ x, deriv g_smooth (-x) = -(deriv g_smooth x) :=
  deriv_even_odd (hg_C4.of_le (by norm_num)) hg_even

have hg'_bc0 : deriv g_smooth 0 = 0 := odd_zero hg'_odd

have hg'_antisymm1 : ∀ x, deriv g_smooth (2 - x) = -(deriv g_smooth x) := by
  intro x
  have h1 := deriv_comp_const_sub (f := g_smooth) (a := 2) (x := x)
  rw [show (fun x : ℝ => g_smooth (2 - x)) = g_smooth from funext hg_symm1] at h1
  linarith

have hg'_bc1 : deriv g_smooth 1 = 0 := by
  have h := hg'_antisymm1 1
  rw [show (2 : ℝ) - 1 = 1 from by norm_num] at h
  linarith

have hg'_cont : Continuous (deriv g_smooth) :=
  hg_C4.continuous_deriv (by norm_num)

have hg'_tend0 : Filter.Tendsto (deriv g_smooth)
    (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  conv_rhs => rw [← hg'_bc0]
  exact hg'_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

have hg'_tend1 : Filter.Tendsto (deriv g_smooth)
    (nhdsWithin (1 : ℝ) (Iio 1)) (nhds 0) := by
  conv_rhs => rw [← hg'_bc1]
  exact hg'_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

have hg_H2 : IntervalWeakH2Neumann g_smooth :=
  ShenWork.PDE.IntervalMildSourceDecayHelper.intervalWeakH2Neumann_of_contDiffOn
    hg_C2_on hg'_tend0 hg'_tend1 hg'_bc0 hg'_bc1

set f_lift : ℝ → ℝ := fun x => p.ν * intervalDomainLift w x ^ p.γ with hf_lift_def

have h_src_Ioo : ∀ x ∈ Ioo (0 : ℝ) 1, f_lift x = g_smooth x := by
  intro x hx
  have hx_icc : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
  have h := hagree_w hx_icc
  simp only [f_lift, hf_lift_def, g_smooth, hg_smooth_def]
  rw [h]

have h_cos_src_eq : ∀ k : ℕ,
    (∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * f_lift x) =
      ∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * g_smooth x := by
  intro k
  refine intervalIntegral.integral_congr_ae ?_
  have hne1 : ∀ᵐ x : ℝ ∂MeasureTheory.volume, x ≠ (1 : ℝ) := by
    rw [MeasureTheory.ae_iff,
      show {x : ℝ | ¬ x ≠ (1 : ℝ)} = ({1} : Set ℝ) from by ext x; simp [eq_comm]]
    exact Real.volume_singleton
  filter_upwards [hne1] with x hxne hxmem
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hxmem
  have hx_ioo : x ∈ Ioo (0 : ℝ) 1 := ⟨hxmem.1, lt_of_le_of_ne hxmem.2 hxne⟩
  rw [h_src_Ioo x hx_ioo]

have hf_H2 : IntervalWeakH2Neumann f_lift where
  secondDeriv := deriv (deriv g_smooth)
  second_intervalIntegrable := by
    simpa [ShenWork.PDE.IntervalMildSourceDecayHelper.intervalWeakH2Neumann_of_contDiffOn]
      using hg_H2.second_intervalIntegrable
  second_abs_integral_bound := by
    simpa [ShenWork.PDE.IntervalMildSourceDecayHelper.intervalWeakH2Neumann_of_contDiffOn]
      using hg_H2.second_abs_integral_bound
  weak_cosine_laplacian := by
    intro k
    have h := hg_H2.weak_cosine_laplacian k
    rw [h_cos_src_eq k]
    simpa [ShenWork.PDE.IntervalMildSourceDecayHelper.intervalWeakH2Neumann_of_contDiffOn] using h

have hg_C3 : ContDiff ℝ 3 (deriv g_smooth) := by
  have h : ContDiff ℝ (3 + 1) g_smooth := by simpa using hg_C4
  exact h.deriv'

have hg_C2_dd : ContDiff ℝ 2 (deriv (deriv g_smooth)) := by
  have h : ContDiff ℝ (2 + 1) (deriv g_smooth) := by simpa using hg_C3
  exact h.deriv'

have hg_C2_dd_on : ContDiffOn ℝ 2 (deriv (deriv g_smooth)) (Icc (0 : ℝ) 1) :=
  hg_C2_dd.contDiffOn

have hg''_even : ∀ x, deriv (deriv g_smooth) (-x) = deriv (deriv g_smooth) x :=
  deriv_odd_even (hg_C3.of_le (by norm_num)) hg'_odd

have hg'''_odd : ∀ x, deriv (deriv (deriv g_smooth)) (-x) =
    -(deriv (deriv (deriv g_smooth)) x) :=
  deriv_even_odd (hg_C2_dd.of_le (by norm_num)) hg''_even

have hg'''_bc0 : deriv (deriv (deriv g_smooth)) 0 = 0 := odd_zero hg'''_odd

have hg''_symm1 : ∀ x, deriv (deriv g_smooth) (2 - x) = deriv (deriv g_smooth) x := by
  intro x
  have h1 := deriv_comp_const_sub (f := deriv g_smooth) (a := 2) (x := x)
  rw [show (fun x : ℝ => deriv g_smooth (2 - x)) =
      fun x : ℝ => -(deriv g_smooth x) from funext hg'_antisymm1] at h1
  simp [deriv_neg] at h1
  linarith

have hg'''_bc1 : deriv (deriv (deriv g_smooth)) 1 = 0 := by
  have h1 := deriv_comp_const_sub (f := deriv (deriv g_smooth)) (a := 2) (x := 1)
  rw [show (fun x : ℝ => deriv (deriv g_smooth) (2 - x)) =
      deriv (deriv g_smooth) from funext hg''_symm1] at h1
  rw [show (2 : ℝ) - 1 = 1 from by norm_num] at h1
  linarith

have hg'''_cont : Continuous (deriv (deriv (deriv g_smooth))) :=
  hg_C2_dd.continuous_deriv (by norm_num)

have hg'''_tend0 : Filter.Tendsto (deriv (deriv (deriv g_smooth)))
    (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  conv_rhs => rw [← hg'''_bc0]
  exact hg'''_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

have hg'''_tend1 : Filter.Tendsto (deriv (deriv (deriv g_smooth)))
    (nhdsWithin (1 : ℝ) (Iio 1)) (nhds 0) := by
  conv_rhs => rw [← hg'''_bc1]
  exact hg'''_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

have hg_dd_H2 : IntervalWeakH2Neumann (deriv (deriv g_smooth)) :=
  ShenWork.PDE.IntervalMildSourceDecayHelper.intervalWeakH2Neumann_of_contDiffOn
    hg_C2_dd_on hg'''_tend0 hg'''_tend1 hg'''_bc0 hg'''_bc1

have hf_dd_H2 : IntervalWeakH2Neumann hf_H2.secondDeriv := by
  change IntervalWeakH2Neumann (deriv (deriv g_smooth))
  exact hg_dd_H2

have hsrc_cos_summable : Summable (fun k : ℕ =>
    unitIntervalCosineEigenvalue k * |cosineCoeffs f_lift k|) :=
  ShenWork.IntervalSourceDecayQuantitative
    .intervalWeakH4Neumann_eigenvalue_L1_summable hf_H2 hf_dd_H2

exact hsrc_cos_summable.congr (fun k => by
  rw [ShenWork.IntervalDomainLogisticWeakH2Adapter
    .resolverSourceCoeff_re_eq_cosineCoeffs p w k]
  simp [f_lift, hf_lift_def])
```

## If the `hf_H2` field unfolding resists

Replace the `hf_H2` constructor’s two `simpa` field proofs by repeating the constructor term explicitly:

```lean
have htmp :=
  ShenWork.PDE.IntervalMildSourceDecayHelper.intervalWeakH2Neumann_of_contDiffOn
    hg_C2_on hg'_tend0 hg'_tend1 hg'_bc0 hg'_bc1
```

then use `htmp.second_intervalIntegrable`, `htmp.second_abs_integral_bound`, and `htmp.weak_cosine_laplacian`. This is definitional cleanup only, not a new mathematical step.

## Why this works

`intervalResolverLiftR_contDiff_four` needs eigenvalue-weighted source coefficient summability. `intervalWeakH4Neumann_eigenvalue_L1_summable` gives that from `IntervalWeakH2Neumann f` plus `IntervalWeakH2Neumann f''`. The actual source and `g_smooth` agree on the interval interior, so their cosine integrals agree. Choosing the source certificate’s `secondDeriv` to be the smooth `g_smooth''` makes the depth-2 certificate exactly the C²/Neumann certificate for `g_smooth''`.
