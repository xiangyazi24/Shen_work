# Phase-0 / endpoint spec: deriv² of the zero-extension lift VANISHES at {0,1}

Target file (NEW, sole writer): ShenWork/PDE/IntervalLiftEndpointDeriv.lean

## Mathematical content (complete proof sketch — follow it)
For ANY f : intervalDomainPoint → ℝ, the zero-extension
`intervalDomainLift f` (IntervalDomain.lean:2750) is ≡ 0 on Iio 0 and on
Ioi 1. Claim: `deriv (deriv (intervalDomainLift f)) 0 = 0` and same at 1.

Proof at 0 (mirror at 1 with right replaced by left):
1. `g := deriv (intervalDomainLift f)` satisfies g = 0 on Iio 0:
   for x < 0 the lift is ≡0 on the nbhd Iio 0 of x, so
   HasDerivAt lift 0 x via (hasDerivAt_const x 0).congr_of_eventuallyEq
   (EqOn (Iio 0) + isOpen_Iio.mem_nhds) hence deriv = 0.
2. by_cases hdiff : DifferentiableAt ℝ g 0
   - ¬: deriv g 0 = 0 := deriv_zero_of_not_differentiableAt hdiff. Done.
   - yes: let D := deriv g 0, hD : HasDerivAt g D 0 := hdiff.hasDerivAt.
     (a) g 0 = 0: hD.continuousAt gives ContinuousAt g 0; the left filter
         𝓝[<](0:ℝ) is NeBot; g →[𝓝[<]0] g 0 (continuity restricted), but
         g =ᶠ[𝓝[<]0] 0 (EqOn Iio 0 ∈ 𝓝[<]0 via self_mem... use
         eventually_nhdsWithin_of... : Iio 0 ∈ 𝓝[<]0 = self), so the limit
         is also 0; tendsto_nhds_unique ⟹ g 0 = 0.
     (b) D = 0: hD.hasDerivWithinAt (s := Set.Iio 0) :
         HasDerivWithinAt g D (Iio 0) 0. Also
         (hasDerivWithinAt_const ...) : HasDerivWithinAt (fun _ => (0:ℝ)) 0 (Iio 0) 0,
         and g =ᶠ equals the const 0 on Iio 0 with g 0 = 0, so by
         HasDerivWithinAt.congr (or congr_of_eventuallyEq):
         HasDerivWithinAt g 0 (Iio 0) 0. Uniqueness: the slope/limit
         formulation — use `HasDerivWithinAt` unfolded:
         both give Tendsto (slope g 0) (𝓝[Iio 0 \ {0}]... — simplest robust
         route: hasDerivWithinAt_iff_tendsto_slope (Mathlib) at the two
         facts; 𝓝[Iio 0 \ {0}] 0 = 𝓝[Iio 0] 0 (0 ∉ Iio 0) is NeBot
         (nhdsWithin_Iio_self_neBot' or Filter.NeBot instance for
         𝓝[<](0:ℝ) — `nhdsWithin_Iio_self_neBot`); tendsto_nhds_unique ⟹ D = 0.
     Then deriv g 0 = D = 0.
3. Export the two endpoint lemmas in the EXACT shape consumed by
   ShenWork/Paper2/IntervalPicardUniformWiring.lean's hEnd0/hEnd1 residuals
   (READ that file first; if its residual shape is |deriv²| ≤ bound, provide
   the = 0 lemma + a corollary 0 ≤ bound form with a nonneg hypothesis on
   the bound).
4. BONUS (only if quick): the same argument gives deriv lift 0-related
   first-derivative facts; skip unless needed by the wiring file.

## Constraints
Standard: new file; scp + ssh uisai1 lake env lean loop (NEVER lake build;
oleans via lake env lean -o); 0 sorry/admit/axiom/native_decide; #print
axioms = 3 standard; commit ONLY your file "Phase-0: lift deriv2 vanishes at
endpoints (junk-value uniqueness argument)"; push uisai1 main (untracked-copy
dance). Pitfalls: renames (lt_or_ge / le_or_gt / Summable.tsum_le_tsum);
rw [defName]→simp only; HO-unification (g:=)(f:=); Mathlib name roulette on
slope lemmas — grep .lake/packages/mathlib for hasDerivWithinAt_iff_tendsto_slope
and nhdsWithin_Iio_self_neBot BEFORE using; if a name differs, adapt.
