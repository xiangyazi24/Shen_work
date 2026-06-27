# Q1285 (cron2) — filling `intervalResolverLiftR_contDiff_four` at line 1088

Static GitHub-connector inspection only. I did **not** run Lean locally.

## Exact theorem names found

The requested route exists, but with one naming correction.

There is **no separate structure named** `IntervalWeakH4Neumann` in the indexed source I found.  The H⁴ route is encoded as a depth-2 weak-H² tower:

```lean
ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann f
ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann hf.secondDeriv
```

The exact summability theorem is:

```lean
ShenWork.IntervalSourceDecayQuantitative.intervalWeakH4Neumann_eigenvalue_L1_summable
```

with signature:

```lean
theorem intervalWeakH4Neumann_eigenvalue_L1_summable
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f)
    (hf'' : IntervalWeakH2Neumann hf.secondDeriv) :
    Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * |cosineCoeffs f k|)
```

The other exact names are:

```lean
ShenWork.PDE.IntervalMildSourceDecayHelper.intervalWeakH2Neumann_of_contDiffOn
ShenWork.PDE.IntervalMildSourceDecayHelper.intervalWeakH2Neumann_of_eigenvalue_summable
ShenWork.IntervalDomainLogisticWeakH2Adapter.resolverSourceCoeff_re_eq_cosineCoeffs
ShenWork.Paper2.IntervalResolverHighRegularity.intervalResolverLiftR_contDiff_four
```

`intervalResolverLiftR_contDiff_four` expects:

```lean
Summable (fun k : ℕ =>
  unitIntervalCosineEigenvalue k *
    |(ShenWork.PDE.intervalNeumannResolverSourceCoeff p u k).re|)
```

The bridge is exactly:

```lean
(intervalNeumannResolverSourceCoeff p u k).re
  = cosineCoeffs (fun x => p.ν * intervalDomainLift u x ^ p.γ) k
```

## Important obstruction in the current line-1088 context

The proof route needs strict positivity of the heat profile at the positive time `r`:

```lean
hpos_w : ∀ x ∈ Icc (0 : ℝ) 1,
  0 < intervalDomainLift (conjugatePicardIter p u₀ 0 r) x
```

This is required by

```lean
intervalWeakH2Neumann_of_eigenvalue_summable p.hν p.hγ hbc_sum hagree_w hpos_w
```

and also by the `ContDiff ℝ 4` chain rule for

```lean
g_smooth x = p.ν * U_cos x ^ p.γ
```

because `Real.rpow` with arbitrary `0 < γ` is smooth only away from zero.

At line 1088, the local variable `r` is merely in a ball around `s` and is proved positive (`hr_pos' : 0 < r`).  The available hypothesis

```lean
_hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
  0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x
```

cannot be applied to this `r` unless the ball is also known to stay inside `Icc c T`.  For `s = T`, no ordinary `𝓝 s` ball stays inside `Iic T`, so this is not just a small missing `linarith`; it is a genuine quantifier issue.

So the proof below is the exact line-1088 proof **once you have** a local strict positivity fact for `r`.  The cleanest way is to add an upstream hypothesis such as

```lean
(hu₀_pos : PositiveInitialDatum intervalDomain u₀)
```

and derive `hpos_w` by

```lean
ShenWork.Paper2.BFormPositiveDatumNegPart.intervalFullSemigroupOperator_pos_of_positiveInitialDatum
```

which is already imported by `IntervalBFormNegPartStrictPosBarrier`.

If the theorem statement must remain unchanged, the current context is missing this strict-positive-time bridge.  `_hu₀_nonneg` alone only gives nonnegativity, not strict positivity, and is not enough for arbitrary real `γ > 0`.

## Drop-in proof for the line-1088 `sorry`, assuming `hpos_w`

Replace

```lean
      have hV_C4 : ContDiff ℝ 4 V_cos := by
        apply intervalResolverLiftR_contDiff_four
        sorry
```

with the following.  The first block constructs `hpos_w`; choose one of the two versions.

### Version A: if you add `hu₀_pos : PositiveInitialDatum intervalDomain u₀`

```lean
      have hV_C4 : ContDiff ℝ 4 V_cos := by
        apply intervalResolverLiftR_contDiff_four
        -- Goal:
        --   Summable (fun k => λ_k * |(intervalNeumannResolverSourceCoeff p w k).re|)
        set w := conjugatePicardIter p u₀ 0 r with hw_def

        -- Rewrite resolver-source coefficients as cosine coefficients of ν·lift(w)^γ.
        have hre_eq : ∀ k,
            (ShenWork.PDE.intervalNeumannResolverSourceCoeff p w k).re =
              cosineCoeffs (fun x => p.ν * intervalDomainLift w x ^ p.γ) k := by
          intro k
          simpa using
            ShenWork.IntervalDomainLogisticWeakH2Adapter.resolverSourceCoeff_re_eq_cosineCoeffs
              p w k
        simp_rw [hre_eq]

        -- Heat coefficients at positive time r have eigenvalue-weighted ℓ¹ summability.
        have hbc_sum : Summable (fun n =>
            unitIntervalCosineEigenvalue n *
              |Real.exp (-r * unitIntervalCosineEigenvalue n) * heatCoeff u₀ n|) :=
          ShenWork.IntervalSemigroupNeumann.heatCoeff_eigenvalue_summable
            hr_pos' _hu₀_bound

        -- Agreement of the heat seed with the cosine representative on [0,1].
        have hagree_w : Set.EqOn (intervalDomainLift w)
            (fun x => ∑' k, (Real.exp (-r * unitIntervalCosineEigenvalue k) *
              heatCoeff u₀ k) * cosineMode k x) (Set.Icc (0 : ℝ) 1) := by
          intro x hx
          simpa [w] using
            ShenWork.IntervalPicardIterateRepresentation.hagree_zero
              p u₀ hr_pos' _hu₀_cont _hu₀_bound hx

        -- Strict positivity of the positive-time heat seed.
        have hpos_w : ∀ x ∈ Set.Icc (0 : ℝ) 1,
            0 < intervalDomainLift w x := by
          intro x hx
          rw [hw_def]
          -- On [0,1], the subtype lift is the semigroup value.
          simp only [conjugatePicardIter, intervalDomainLift, dif_pos hx]
          exact ShenWork.Paper2.BFormPositiveDatumNegPart
            .intervalFullSemigroupOperator_pos_of_positiveInitialDatum
              hu₀_pos hr_pos' x

        -- First weak-H² Neumann certificate for ν·lift(w)^γ.
        have hf_H2 :
            ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann
              (fun x => p.ν * intervalDomainLift w x ^ p.γ) :=
          ShenWork.PDE.IntervalMildSourceDecayHelper
            .intervalWeakH2Neumann_of_eigenvalue_summable
              p.hν p.hγ hbc_sum hagree_w hpos_w

        -- Local cosine-mode parity helpers.
        have cosineMode_neg' : ∀ (k : ℕ) (x : ℝ),
            cosineMode k (-x) = cosineMode k x := by
          intro k x
          unfold cosineMode
          rw [show (k : ℝ) * Real.pi * (-x) =
              -((k : ℝ) * Real.pi * x) from by ring, Real.cos_neg]
        have cosineMode_add_two' : ∀ (k : ℕ) (x : ℝ),
            cosineMode k (x + 2) = cosineMode k x := by
          intro k x
          unfold cosineMode
          rw [show (k : ℝ) * Real.pi * (x + 2) =
                (k : ℝ) * Real.pi * x + ((k : ℤ) : ℝ) * (2 * Real.pi) from by
                push_cast; ring,
              Real.cos_add_int_mul_two_pi _ (k : ℤ)]

        -- U_cos is even and symmetric about 1.
        have hU_even : ∀ x, U_cos (-x) = U_cos x := by
          intro x
          simp only [hU_cos_def]
          exact tsum_congr (fun k => by congr 1; exact cosineMode_neg' k x)
        have hU_symm1 : ∀ x, U_cos (2 - x) = U_cos x := by
          intro x
          rw [show (2 : ℝ) - x = (-x) + 2 from by ring]
          simp only [hU_cos_def]
          rw [show (fun k => (Real.exp (-r * unitIntervalCosineEigenvalue k) *
                heatCoeff u₀ k) * cosineMode k ((-x) + 2)) =
              (fun k => (Real.exp (-r * unitIntervalCosineEigenvalue k) *
                heatCoeff u₀ k) * cosineMode k (-x)) from
              funext (fun k => by congr 1; exact cosineMode_add_two' k (-x))]
          exact hU_even x

        -- Build the second weak-H² certificate for hf_H2.secondDeriv.
        have hf''_H2 :
            ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann
              hf_H2.secondDeriv := by
          -- U_cos > 0 globally by period/even/reflection reduction to [0,1].
          have hU_period_fun : Function.Periodic U_cos 2 := by
            intro x
            show U_cos (x + 2) = U_cos x
            simp only [hU_cos_def]
            exact tsum_congr (fun k => by congr 1; exact cosineMode_add_two' k x)
          have hU_pos_all : ∀ x, 0 < U_cos x := by
            have hU_pos_Icc : ∀ y ∈ Icc (0 : ℝ) 1, 0 < U_cos y := by
              intro y hy
              rw [← hU_agree y hy]
              simpa [w] using hpos_w y hy
            intro x
            have hx_abs : U_cos x = U_cos |x| := by
              by_cases h : 0 ≤ x
              · rw [abs_of_nonneg h]
              · rw [abs_of_neg (not_le.mp h)]
                exact (hU_even x).symm
            rw [hx_abs]
            set n := ⌊|x| / 2⌋ with hn_def
            set rr := |x| - n * 2 with hrr_def
            have hrrV : U_cos |x| = U_cos rr :=
              (hU_period_fun.sub_int_mul_eq n).symm
            have hrr_lo : 0 ≤ rr := by
              have := Int.floor_le (|x| / 2)
              linarith
            have hrr_hi : rr < 2 := by
              have := Int.lt_floor_add_one (|x| / 2)
              linarith
            rw [hrrV]
            by_cases hrr1 : rr ≤ 1
            · exact hU_pos_Icc rr ⟨hrr_lo, hrr1⟩
            · push_neg at hrr1
              have : U_cos rr = U_cos (2 - rr) := (hU_symm1 rr).symm
              rw [this]
              exact hU_pos_Icc (2 - rr) ⟨by linarith, by linarith⟩

          -- g_smooth := ν * U_cos^γ is globally C⁴.
          have hU_ne : ∀ x, U_cos x ≠ 0 := fun x => ne_of_gt (hU_pos_all x)
          set g_smooth := fun x => p.ν * U_cos x ^ p.γ with hg_smooth_def
          have hg_C4 : ContDiff ℝ 4 g_smooth := by
            show ContDiff ℝ 4 (fun x => p.ν * U_cos x ^ p.γ)
            exact contDiff_const.mul (hU_C4.rpow_const_of_ne hU_ne)

          -- g_smooth inherits evenness and symmetry about 1.
          have hg_even : ∀ x, g_smooth (-x) = g_smooth x := by
            intro x
            simp only [hg_smooth_def, hU_even]
          have hg_symm1 : ∀ x, g_smooth (2 - x) = g_smooth x := by
            intro x
            simp only [hg_smooth_def, hU_symm1]

          -- C² regularity for g_smooth''.
          have hg_C3 : ContDiff ℝ 3 (deriv g_smooth) := hg_C4.deriv'
          have hg_C2_dd : ContDiff ℝ 2 (deriv (deriv g_smooth)) := hg_C3.deriv'
          have hg_C2_dd_on :
              ContDiffOn ℝ 2 (deriv (deriv g_smooth)) (Icc (0 : ℝ) 1) :=
            hg_C2_dd.contDiffOn

          -- Parity helpers.
          have deriv_even_odd : ∀ {g : ℝ → ℝ}, ContDiff ℝ 1 g →
              (∀ x, g (-x) = g x) → ∀ x, deriv g (-x) = -(deriv g x) := by
            intro g _hg heven x
            have h1 := deriv_comp_neg (f := g) (x := x)
            rw [show (fun x => g (-x)) = g from funext heven] at h1
            linarith
          have odd_zero : ∀ {g : ℝ → ℝ},
              (∀ x, g (-x) = -(g x)) → g 0 = 0 := by
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

          -- g even → g' odd → g'' even → g''' odd.
          have hg'_odd : ∀ x, deriv g_smooth (-x) = -(deriv g_smooth x) :=
            deriv_even_odd (hg_C4.of_le (by norm_num)) hg_even
          have hg''_even : ∀ x,
              deriv (deriv g_smooth) (-x) = deriv (deriv g_smooth) x :=
            deriv_odd_even (hg_C3.of_le (by norm_num)) hg'_odd
          have hg'''_odd : ∀ x,
              deriv (deriv (deriv g_smooth)) (-x) =
                -(deriv (deriv (deriv g_smooth)) x) :=
            deriv_even_odd (hg_C2_dd.of_le (by norm_num)) hg''_even

          -- Neumann data for g''' at endpoints.
          have hbc30 : deriv (deriv (deriv g_smooth)) 0 = 0 :=
            odd_zero hg'''_odd
          have hg'_antisymm1 : ∀ x,
              deriv g_smooth (2 - x) = -(deriv g_smooth x) := by
            intro x
            have h1 := deriv_comp_const_sub (f := g_smooth) (a := 2) (x := x)
            rw [show (fun x => g_smooth (2 - x)) = g_smooth from funext hg_symm1] at h1
            linarith
          have hg''_symm1 : ∀ x,
              deriv (deriv g_smooth) (2 - x) = deriv (deriv g_smooth) x := by
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

          -- Weak-H² certificate for g_smooth''.
          have h_smooth_H2 :
              ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann
                (deriv (deriv g_smooth)) :=
            ShenWork.PDE.IntervalMildSourceDecayHelper.intervalWeakH2Neumann_of_contDiffOn
              hg_C2_dd_on htend30 htend31 hbc30 hbc31

          -- Agreement of the lift source with g_smooth on [0,1].
          have h_src_Icc : ∀ x ∈ Icc (0 : ℝ) 1,
              (fun z => p.ν * intervalDomainLift w z ^ p.γ) x = g_smooth x := by
            intro x hx
            show p.ν * intervalDomainLift w x ^ p.γ = p.ν * U_cos x ^ p.γ
            rw [hU_agree x hx]
          have h_cos_int_eq : ∀ k : ℕ,
              (∫ x in (0 : ℝ)..1,
                  Real.cos ((k : ℝ) * Real.pi * x) *
                    (fun z => p.ν * intervalDomainLift w z ^ p.γ) x) =
                ∫ x in (0 : ℝ)..1,
                  Real.cos ((k : ℝ) * Real.pi * x) * g_smooth x :=
            fun k => intervalIntegral.integral_congr (fun x hx => by
              rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
              rw [h_src_Icc x hx])

          -- Depth-1 smooth IBP for g_smooth.
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
                  Real.cos ((k : ℝ) * Real.pi * x) *
                    deriv (deriv g_smooth) x) =
                -((k : ℝ) * Real.pi) ^ 2 *
                  ∫ x in (0 : ℝ)..1,
                    Real.cos ((k : ℝ) * Real.pi * x) * g_smooth x :=
            fun k =>
              ShenWork.IntervalEllipticCharacterization
                .intervalCosineLaplacianCoeff_eq_of_contDiffOn
                  k hg_C2_on hg'_tend0 hg'_tend1 hg'_bc0 hg'_bc1

          -- Transfer h_smooth_H2 from g_smooth'' to hf_H2.secondDeriv by the
          -- cosine-laplacian algebra.
          exact {
            secondDeriv := h_smooth_H2.secondDeriv
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

        -- Depth-2 weak-H² tower gives eigenvalue-weighted ℓ¹ summability.
        exact ShenWork.IntervalSourceDecayQuantitative
          .intervalWeakH4Neumann_eigenvalue_L1_summable
            hf_H2 hf''_H2
```

### Version B: if you keep the old theorem statement

With the exact current local context, replace the `hpos_w` block above by a new local hypothesis/lemma.  The missing lemma shape is:

```lean
have hpos_w : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    0 < intervalDomainLift w x := by
  -- Not derivable from `_hu₀_nonneg` alone.
  -- Need either `hu₀_pos : PositiveInitialDatum intervalDomain u₀`, or a theorem
  -- proving strict positivity of `S(r)u₀` from the already-carried `_hpos` window.
  sorry
```

I do **not** recommend hiding this as a local `sorry`: it is the real missing assumption.  The rest of the block is the same as the already-completed per-slice proof earlier in `IntervalConjugateLevel0BFormSourceOn.lean` (the `hV_data` / C⁴ branch inside `level0_chemDiv_envelope_summable`).

## Why the proof pattern is correct

1. `intervalResolverLiftR_contDiff_four` reduces resolver C⁴ to source eigenvalue-weighted ℓ¹ summability.
2. `resolverSourceCoeff_re_eq_cosineCoeffs` rewrites the resolver source coefficients to the cosine coefficients of `x ↦ p.ν * intervalDomainLift w x ^ p.γ`.
3. `intervalWeakH2Neumann_of_eigenvalue_summable` builds the first weak-H² certificate for that source from the heat cosine representation, eigenvalue-weighted summability of heat coefficients, agreement on `[0,1]`, and strict positivity.
4. The C⁴ smooth representative `g_smooth = p.ν * U_cos^p.γ` plus even/endpoint symmetry builds `IntervalWeakH2Neumann hf_H2.secondDeriv`.
5. `intervalWeakH4Neumann_eigenvalue_L1_summable hf_H2 hf''_H2` gives exactly the summability required by `intervalResolverLiftR_contDiff_four`.

## Minimal edit I recommend

Strengthen `level0_chemDiv_timeDerivData` with:

```lean
(hu₀_pos : PositiveInitialDatum intervalDomain u₀)
```

Then the proof above is the intended fill for line 1088.  If you do not want to add `hu₀_pos`, add a lemma deriving strict positive heat for all `r > 0` from the existing assumptions; the current repo has the forward theorem from `PositiveInitialDatum`, but I did not find a theorem deriving it from `_hu₀_nonneg` plus the window `_hpos`.
