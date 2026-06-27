# Q1292 / cron1 — depth-2 `IntervalWeakH2Neumann` for `ν * U_cos^γ` at line 1094

Repo: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target file updated by this drop:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## What I read

Target file:

```text
ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean
```

The earlier block around lines 460–560 already does the construction:

1. build

```lean
hf_H2 : IntervalWeakH2Neumann (fun x => p.ν * intervalDomainLift w x ^ p.γ)
```

from `intervalWeakH2Neumann_of_eigenvalue_summable`;

2. set

```lean
g_smooth := fun x => p.ν * U_cos x ^ p.γ
```

and prove `ContDiff ℝ 4 g_smooth` from `hU_C4` and positivity;

3. use evenness and symmetry about `1` to prove the third-derivative Neumann endpoint conditions for `g_smooth`;

4. build

```lean
h_smooth_H2 : IntervalWeakH2Neumann (deriv (deriv g_smooth))
```

5. transfer it to

```lean
hf''_H2 : IntervalWeakH2Neumann hf_H2.secondDeriv
```

by the same cosine-laplacian algebra;

6. finish with

```lean
ShenWork.IntervalSourceDecayQuantitative.intervalWeakH4Neumann_eigenvalue_L1_summable
  hf_H2 hf''_H2
```

The line-1094 context is the same except the local time is `r`, not the earlier `s`, so the only extra work is producing positivity of the heat profile at `r > 0`.

## Imports to make explicit

Add these if they are not already imported transitively:

```lean
import ShenWork.PDE.IntervalSourceDecayQuantitative
import ShenWork.Paper2.IntervalDomainLogisticWeakH2Adapter
```

The target file already imports `IntervalBFormNegPartStrictPosBarrier`, which provides:

```lean
ShenWork.Paper2.BFormPositiveDatumNegPart.intervalFullSemigroupOperator_pos_of_nonneg_nonzero
```

That theorem is useful for the `r > 0` positivity input.

## Replacement block for the line-1094 sorry

This replaces the `sorry` after the existing rewrite to

```lean
Summable (fun k => unitIntervalCosineEigenvalue k *
  |cosineCoeffs (fun x => p.ν * intervalDomainLift
    (conjugatePicardIter p u₀ 0 r) x ^ p.γ) k|)
```

Use this whole block at the `sorry` site.

```lean
        -- Abbreviate the heat profile at the auxiliary time `r`.
        set w := conjugatePicardIter p u₀ 0 r with hw_def
        let bc : ℕ → ℝ := fun k =>
          Real.exp (-r * unitIntervalCosineEigenvalue k) * heatCoeff u₀ k

        -- Eigenvalue-weighted summability of the heat coefficients at positive time.
        have hbc_sum : Summable (fun n : ℕ =>
            unitIntervalCosineEigenvalue n * |bc n|) := by
          simpa [bc] using
            ShenWork.IntervalSemigroupNeumann.heatCoeff_eigenvalue_summable
              hr_pos' _hu₀_bound

        -- The heat cosine representative agrees with the actual heat profile on `[0,1]`.
        have hU_agree_w : ∀ x ∈ Icc (0 : ℝ) 1,
            intervalDomainLift w x = U_cos x := by
          intro x hx
          simpa [w, hw_def] using hU_agree x hx

        have hagree_w : Set.EqOn (intervalDomainLift w)
            (fun x => ∑' n : ℕ, bc n * cosineMode n x) (Icc (0 : ℝ) 1) := by
          intro x hx
          calc intervalDomainLift w x
              = U_cos x := hU_agree_w x hx
            _ = ∑' n : ℕ, bc n * cosineMode n x := by
                simp [bc, hU_cos_def]

        -- Positivity of the initial datum somewhere.  If it were zero everywhere on
        -- `[0,1]`, nonnegativity would force the heat profile to be zero, contradicting
        -- `_hpos s hs` at an interior point.
        have h_u0_pos_somewhere : ∃ y₀ ∈ Icc (0 : ℝ) 1,
            0 < intervalDomainLift u₀ y₀ := by
          by_contra hnone
          push_neg at hnone
          have h_u0_zero : intervalDomainLift u₀ = fun _ : ℝ => 0 := by
            funext y
            by_cases hy : y ∈ Icc (0 : ℝ) 1
            · have hnn : 0 ≤ intervalDomainLift u₀ y := by
                simpa [intervalDomainLift, dif_pos hy] using _hu₀_nonneg ⟨y, hy⟩
              have hnpos : ¬ 0 < intervalDomainLift u₀ y := hnone y hy
              exact le_antisymm (le_of_not_gt hnpos) hnn
            · simp [intervalDomainLift, hy]
          have hhalf : ((1 : ℝ) / 2) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
          have hheat_zero :
              intervalDomainLift (conjugatePicardIter p u₀ 0 s) ((1 : ℝ) / 2) = 0 := by
            rw [h_u0_zero]
            simp [conjugatePicardIter, intervalDomainLift, hhalf,
              ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator]
          have hpos_half := _hpos s hs ((1 : ℝ) / 2) hhalf
          rw [hheat_zero] at hpos_half
          exact (lt_irrefl (0 : ℝ)) hpos_half

        -- Continuity/nonnegativity of the lifted initial datum on `[0,1]`.
        have hu0_contOn : ContinuousOn (intervalDomainLift u₀) (Icc (0 : ℝ) 1) := by
          rw [continuousOn_iff_continuous_restrict]
          have hrestr : (Icc (0 : ℝ) 1).restrict (intervalDomainLift u₀) = u₀ := by
            funext y
            simp only [Set.restrict_apply, intervalDomainLift]
            rw [dif_pos y.2]
            exact congr_arg u₀ (Subtype.ext rfl)
          rw [hrestr]
          exact _hu₀_cont
        have hu0_nonnegOn : ∀ y ∈ Icc (0 : ℝ) 1,
            0 ≤ intervalDomainLift u₀ y := by
          intro y hy
          simpa [intervalDomainLift, dif_pos hy] using _hu₀_nonneg ⟨y, hy⟩

        -- Strict positivity of the heat profile at every positive time `r`.
        have hheat_pos : ∀ x : ℝ,
            0 < intervalFullSemigroupOperator r (intervalDomainLift u₀) x :=
          ShenWork.Paper2.BFormPositiveDatumNegPart
            .intervalFullSemigroupOperator_pos_of_nonneg_nonzero
              hr_pos' hu0_contOn hu0_nonnegOn h_u0_pos_somewhere

        have hpos_w : ∀ x ∈ Icc (0 : ℝ) 1,
            0 < intervalDomainLift w x := by
          intro x hx
          simpa [w, hw_def, conjugatePicardIter, intervalDomainLift, dif_pos hx]
            using hheat_pos x

        -- Symmetry helpers for the cosine representative.
        have cosineMode_neg' : ∀ (k : ℕ) (x : ℝ), cosineMode k (-x) = cosineMode k x := by
          intro k x
          unfold cosineMode
          rw [show (k : ℝ) * Real.pi * (-x) = -((k : ℝ) * Real.pi * x) from by ring,
            Real.cos_neg]
        have cosineMode_add_two' : ∀ (k : ℕ) (x : ℝ),
            cosineMode k (x + 2) = cosineMode k x := by
          intro k x
          unfold cosineMode
          rw [show (k : ℝ) * Real.pi * (x + 2)
                = (k : ℝ) * Real.pi * x + ((k : ℤ) : ℝ) * (2 * Real.pi) from by
              push_cast; ring,
            Real.cos_add_int_mul_two_pi _ (k : ℤ)]

        have hU_even : ∀ x, U_cos (-x) = U_cos x := by
          intro x
          simp only [hU_cos_def]
          exact tsum_congr (fun k => by congr 1; exact cosineMode_neg' k x)
        have hU_symm1 : ∀ x, U_cos (2 - x) = U_cos x := by
          intro x
          rw [show (2 : ℝ) - x = (-x) + 2 from by ring]
          simp only [hU_cos_def]
          rw [show (fun k =>
                (Real.exp (-r * unitIntervalCosineEigenvalue k) * heatCoeff u₀ k) *
                  cosineMode k ((-x) + 2)) =
              (fun k =>
                (Real.exp (-r * unitIntervalCosineEigenvalue k) * heatCoeff u₀ k) *
                  cosineMode k (-x)) from
            funext (fun k => by congr 1; exact cosineMode_add_two' k (-x))]
          exact hU_even x

        -- Global positivity of `U_cos`, by period-2/even/reflection reduction to `[0,1]`.
        have hU_period_fun : Function.Periodic U_cos 2 := by
          intro x
          show U_cos (x + 2) = U_cos x
          simp only [hU_cos_def]
          exact tsum_congr (fun k => by congr 1; exact cosineMode_add_two' k x)
        have hU_pos_all : ∀ x, 0 < U_cos x := by
          have hU_pos_Icc : ∀ y ∈ Icc (0 : ℝ) 1, 0 < U_cos y := by
            intro y hy
            rw [← hU_agree_w y hy]
            exact hpos_w y hy
          intro x
          have hx_abs : U_cos x = U_cos |x| := by
            by_cases h : 0 ≤ x
            · rw [abs_of_nonneg h]
            · rw [abs_of_neg (not_le.mp h)]
              exact (hU_even x).symm
          rw [hx_abs]
          set n := ⌊|x| / 2⌋ with hn_def
          set r0 := |x| - n * 2 with hr0_def
          have hrV : U_cos |x| = U_cos r0 :=
            (hU_period_fun.sub_int_mul_eq n).symm
          have hr_lo : 0 ≤ r0 := by
            have := Int.floor_le (|x| / 2)
            linarith
          have hr_hi : r0 < 2 := by
            have := Int.lt_floor_add_one (|x| / 2)
            linarith
          rw [hrV]
          by_cases hr1 : r0 ≤ 1
          · exact hU_pos_Icc r0 ⟨hr_lo, hr1⟩
          · push_neg at hr1
            have : U_cos r0 = U_cos (2 - r0) := (hU_symm1 r0).symm
            rw [this]
            exact hU_pos_Icc (2 - r0) ⟨by linarith, by linarith⟩

        -- Depth 1: weak-H² certificate for the actual source `ν * lift(w)^γ`.
        have hf_H2 :
            ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann
              (fun x : ℝ => p.ν * intervalDomainLift w x ^ p.γ) :=
          ShenWork.PDE.IntervalMildSourceDecayHelper.intervalWeakH2Neumann_of_eigenvalue_summable
            p.hν p.hγ hbc_sum hagree_w hpos_w

        -- Smooth C⁴ representative `g_smooth = ν * U_cos^γ`.
        have hU_ne : ∀ x, U_cos x ≠ 0 := fun x => ne_of_gt (hU_pos_all x)
        set g_smooth := fun x => p.ν * U_cos x ^ p.γ with hg_smooth_def
        have hg_C4 : ContDiff ℝ 4 g_smooth := by
          show ContDiff ℝ 4 (fun x => p.ν * U_cos x ^ p.γ)
          exact contDiff_const.mul (hU_C4.rpow_const_of_ne hU_ne)
        have hg_even : ∀ x, g_smooth (-x) = g_smooth x := by
          intro x
          simp only [hg_smooth_def, hU_even]
        have hg_symm1 : ∀ x, g_smooth (2 - x) = g_smooth x := by
          intro x
          simp only [hg_smooth_def, hU_symm1]

        -- C² of `g_smooth''`.
        have hg_C3 : ContDiff ℝ 3 (deriv g_smooth) := hg_C4.deriv'
        have hg_C2_dd : ContDiff ℝ 2 (deriv (deriv g_smooth)) := hg_C3.deriv'
        have hg_C2_dd_on : ContDiffOn ℝ 2 (deriv (deriv g_smooth)) (Icc (0 : ℝ) 1) :=
          hg_C2_dd.contDiffOn

        -- Parity helpers, copied from the same-file depth-2 block.
        have deriv_even_odd : ∀ {g : ℝ → ℝ}, ContDiff ℝ 1 g →
            (∀ x, g (-x) = g x) → ∀ x, deriv g (-x) = -(deriv g x) := by
          intro g _hg heven x
          have h1 := deriv_comp_neg (f := g) (x := x)
          rw [show (fun x => g (-x)) = g from funext heven] at h1
          linarith
        have odd_zero : ∀ {g : ℝ → ℝ}, (∀ x, g (-x) = -(g x)) → g 0 = 0 := by
          intro g hodd
          have h := hodd 0
          rw [neg_zero] at h
          linarith
        have deriv_odd_even : ∀ {g : ℝ → ℝ}, ContDiff ℝ 1 g →
            (∀ x, g (-x) = -(g x)) → ∀ x, deriv g (-x) = deriv g x := by
          intro g _hg hodd x
          have h1 := deriv_comp_neg (f := g) (x := x)
          rw [show (fun x => g (-x)) = fun x => -(g x) from funext hodd] at h1
          simp at h1
          linarith

        -- Parity chain: g even → g' odd → g'' even → g''' odd.
        have hg'_odd : ∀ x, deriv g_smooth (-x) = -(deriv g_smooth x) :=
          deriv_even_odd (hg_C4.of_le (by norm_num)) hg_even
        have hg''_even : ∀ x, deriv (deriv g_smooth) (-x) =
            deriv (deriv g_smooth) x :=
          deriv_odd_even (hg_C3.of_le (by norm_num)) hg'_odd
        have hg'''_odd : ∀ x, deriv (deriv (deriv g_smooth)) (-x) =
            -(deriv (deriv (deriv g_smooth)) x) :=
          deriv_even_odd (hg_C2_dd.of_le (by norm_num)) hg''_even

        -- Neumann BCs for g''' at 0 and 1.
        have hbc30 : deriv (deriv (deriv g_smooth)) 0 = 0 :=
          odd_zero hg'''_odd
        have hg'_antisymm1 : ∀ x, deriv g_smooth (2 - x) = -(deriv g_smooth x) := by
          intro x
          have h1 := deriv_comp_const_sub (f := g_smooth) (a := 2) (x := x)
          rw [show (fun x => g_smooth (2 - x)) = g_smooth from funext hg_symm1] at h1
          linarith
        have hg''_symm1 : ∀ x, deriv (deriv g_smooth) (2 - x) =
            deriv (deriv g_smooth) x := by
          intro x
          have h1 := deriv_comp_const_sub (f := deriv g_smooth) (a := 2) (x := x)
          rw [show (fun x => deriv g_smooth (2 - x)) =
              fun x => -(deriv g_smooth x) from funext hg'_antisymm1] at h1
          simp at h1
          linarith
        have hbc31 : deriv (deriv (deriv g_smooth)) 1 = 0 := by
          have h1 := deriv_comp_const_sub (f := deriv (deriv g_smooth)) (a := 2) (x := 1)
          rw [show (fun x => deriv (deriv g_smooth) (2 - x)) =
              deriv (deriv g_smooth) from funext hg''_symm1] at h1
          have : (2 : ℝ) - 1 = 1 := by norm_num
          rw [this] at h1
          linarith

        -- Tendsto endpoint conditions for g'''.
        have hg'''_cont : Continuous (deriv (deriv (deriv g_smooth))) :=
          hg_C2_dd.continuous_deriv (by norm_num)
        have htend30 : Filter.Tendsto (deriv (deriv (deriv g_smooth)))
            (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
          conv_rhs => rw [← hbc30]
          exact hg'''_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        have htend31 : Filter.Tendsto (deriv (deriv (deriv g_smooth)))
            (nhdsWithin (1 : ℝ) (Iio 1)) (nhds 0) := by
          conv_rhs => rw [← hbc31]
          exact hg'''_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

        -- Smooth H² certificate for `g_smooth''`.
        have h_smooth_H2 :
            ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann
              (deriv (deriv g_smooth)) :=
          ShenWork.PDE.IntervalMildSourceDecayHelper.intervalWeakH2Neumann_of_contDiffOn
            hg_C2_dd_on htend30 htend31 hbc30 hbc31

        -- Agreement of the actual lifted source with the smooth source on `[0,1]`.
        have h_src_Icc : ∀ x ∈ Icc (0 : ℝ) 1,
            (fun z => p.ν * intervalDomainLift w z ^ p.γ) x = g_smooth x := by
          intro x hx
          show p.ν * intervalDomainLift w x ^ p.γ = p.ν * U_cos x ^ p.γ
          rw [hU_agree_w x hx]
        have h_cos_int_eq : ∀ k : ℕ,
            (∫ x in (0 : ℝ)..1,
              Real.cos ((k : ℝ) * Real.pi * x) *
                (fun z => p.ν * intervalDomainLift w z ^ p.γ) x) =
            ∫ x in (0 : ℝ)..1,
              Real.cos ((k : ℝ) * Real.pi * x) * g_smooth x :=
          fun k => intervalIntegral.integral_congr (fun x hx => by
            rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
            rw [h_src_Icc x hx])

        -- Depth-1 IBP for `g_smooth` itself.
        have hg_C2_on : ContDiffOn ℝ 2 g_smooth (Icc (0 : ℝ) 1) :=
          (hg_C4.of_le (by norm_num)).contDiffOn
        have hg'_bc0 : deriv g_smooth 0 = 0 := odd_zero hg'_odd
        have hg'_bc1 : deriv g_smooth 1 = 0 := by
          have := hg'_antisymm1 1
          rw [show (2 : ℝ) - 1 = 1 from by norm_num] at this
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
        have h_depth1_ibp : ∀ k : ℕ,
            (∫ x in (0 : ℝ)..1,
              Real.cos ((k : ℝ) * Real.pi * x) * deriv (deriv g_smooth) x) =
            -((k : ℝ) * Real.pi) ^ 2 *
              ∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * g_smooth x :=
          fun k =>
            ShenWork.IntervalEllipticCharacterization.intervalCosineLaplacianCoeff_eq_of_contDiffOn
              k hg_C2_on hg'_tend0 hg'_tend1 hg'_bc0 hg'_bc1

        -- Depth 2: H² certificate for `hf_H2.secondDeriv`.
        have hf''_H2 :
            ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann
              hf_H2.secondDeriv :=
          { secondDeriv := h_smooth_H2.secondDeriv
            second_intervalIntegrable := h_smooth_H2.second_intervalIntegrable
            second_abs_integral_bound := h_smooth_H2.second_abs_integral_bound
            weak_cosine_laplacian := fun k => by
              have hA := hf_H2.weak_cosine_laplacian k
              have hB := h_smooth_H2.weak_cosine_laplacian k
              have hC := h_cos_int_eq k
              have hD := h_depth1_ibp k
              rw [hC] at hA
              rw [hD] at hB
              rw [hA]
              exact hB }

        -- Quartic decay gives the required eigenvalue-weighted L¹ summability.
        have hsum_power : Summable (fun k : ℕ => unitIntervalCosineEigenvalue k *
            |cosineCoeffs (fun x : ℝ => p.ν * intervalDomainLift w x ^ p.γ) k|) :=
          ShenWork.IntervalSourceDecayQuantitative.intervalWeakH4Neumann_eigenvalue_L1_summable
            hf_H2 hf''_H2

        simpa [w, hw_def] using hsum_power
```

## Notes

The proof is line-for-line the earlier depth-2 construction, adapted to the local `r` context.

The only extra subproof versus lines 460–560 is `hpos_w` at time `r`.  The block above derives it from:

```lean
intervalFullSemigroupOperator_pos_of_nonneg_nonzero
```

using `_hu₀_nonneg`, `_hu₀_cont`, and a positive-somewhere fact for `intervalDomainLift u₀`.  The positive-somewhere fact is obtained by contradiction from `_hpos s hs`: if `u₀` were zero on `[0,1]`, the level-0 heat profile at the known positive window time `s` would be zero, contradicting `_hpos s hs` at `1/2`.

If this positivity proof is too brittle in elaboration, replace just `h_u0_pos_somewhere` by any already-available datum-level positive-somewhere lemma for `u₀`; the rest of the block is independent.

No local `lake build` was run; this drop was produced through the GitHub connector only.
