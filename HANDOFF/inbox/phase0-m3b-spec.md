# Phase-0 / M3b spec: K1 discharge — time-C¹ data from the restart representation

Target file (NEW, sole writer): ShenWork/Paper2/IntervalPicardIterateTimeC1.lean

## Goal
Discharge M3's K1 hypothesis block (adot, hderiv, hadotcont, Mdot) from a
restart representation of the iterate slice. Concretely, GIVEN (abstract
profile form — state for a general w : ℝ → intervalDomainPoint → ℝ, then it
applies to picardIter):
 (R) ∀ σ in a window, Set.EqOn (intervalDomainLift (w σ))
       (fun x => ∑'k, localRestartCoeff a₀ a (σ − offset) k * cosineMode k x)
       (Icc 0 1)  — with a₀ bounded by M₀, src : DuhamelSourceTimeC1 a,
       0 < σ − offset on the window
     (this is HasTimeNeighborhoodSpectralAgreement-shape; READ
      ShenWork/PDE/IntervalMildTimeDerivContinuity.lean:46 and reuse its
      def if it composes better; localRestartCoeff is in
      ShenWork/PDE/IntervalSourceCoefficientTimeC1.lean:707)
 (K2) slice bounds: positivity floor 0 < m ≤ w σ x, sup |w| ≤ M, C² slices
      with Neumann endpoints (take what logisticSourceFun_hasDerivAt_time
      and cosineCoeffs_hasDerivAt_of_smooth_param actually need — read them)

DERIVE with EXPLICIT constants:
 (1) pointwise time derivative: ∀ σ in window, x ∈ Icc, HasDerivAt
       (fun r => intervalDomainLift (w r) x) (∂field σ x) σ
     with |∂field σ x| ≤ Mdot_u := M₀·eigExpWeight(σ−offset)-form +
       src.envelope-sums — use G4i restartCosineSeries_hasDerivAt_time
       (IntervalSourceCoefficientTimeC1.lean:719) for existence; for the
       bound, the derivative series is ∑(aₖ(σ') − λₖcₖ(σ'))cos, so
       |∂field| ≤ ∑'|aₖ| + ∑'λₖ|cₖ| ≤ (∑'envelope) +
       [homogeneous_eigenvalue_tsum_le (IntervalHomogeneousQuantBound) +
        duhamelSpectralCoeff_eigenvalue_tsum_tauQuarter_bound
        (IntervalDuhamelQuantGain) at τ = σ−offset]. All atoms proved.
 (2) joint continuity of ∂field on window×Icc:
     restartDerivField_continuousOn_joint
     (ShenWork/PDE/IntervalRestartDerivJointContinuity.lean).
 (3) the K1 package for the LOGISTIC source family: adot σ k :=
     cosineCoeffs (lift of ∂σ[L(w σ)]) k via chain rule
     logisticSourceFun_hasDerivAt_time (IntervalMildPicardRegularity.lean:605)
     + cosineCoeffs_hasDerivAt_of_smooth_param (same file :494), with
     |adot σ k| ≤ Mdot := 2·(a + b(1+α)M^α)·Mdot_u-form (coefficient ≤ 2·sup
     of the integrand; L'-bound |a − b(1+α)z^α| ≤ a + b(1+α)M^α on (0,M]).
     The OUTPUT shape must match M3's K1 fields exactly (READ
     ShenWork/Paper2/IntervalPicardIterateSourceC1.lean's
     picardIterate_source_duhamelSourceTimeC1 signature).

## Constraints
Standard (as previous specs): new file only; scp + lake env lean loop on
uisai1 (NEVER lake build; oleans via lake env lean -o); 0 sorry/admit/axiom/
native_decide; explicit constants, no existentials; named satisfiable
hypotheses if a sub-step genuinely walls (header justification + why the
real object satisfies it); #print axioms = 3 standard; commit ONLY your file:
"Phase-0 M3b: time-C1 data from restart representation (K1 discharge)",
push uisai1 main with the untracked-copy dance.

NOTE the profile/window bookkeeping: state everything on an explicit window
σ ∈ Set.Icc t₁ t₂ with offset < t₁ (so τ = σ−offset ≥ t₁−offset > 0 and all
weight constants are evaluated at τ ≥ t₁−offset — monotone bounds via the
antitone weights or just instantiate at the left endpoint if you prove
antitonicity; if antitonicity is painful, parameterize the bound by
τmin := t₁ − offset and use weight(τmin) ≥ weight(τ) ONLY IF PROVED, else
keep per-σ bounds — report what you chose).
