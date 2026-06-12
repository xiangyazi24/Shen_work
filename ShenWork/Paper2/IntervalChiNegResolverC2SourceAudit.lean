import ShenWork.PDE.IntervalChemDivFluxFactorFAC
import ShenWork.Paper2.IntervalResolverSpectralAgreementC2CoeffFromK1
import ShenWork.Paper2.IntervalClampedK1SourceCubicBootstrap
import ShenWork.Paper2.Statements

/-!
# chi0 < 0 resolver-C2 source audit

Survey result.

The FAC resolver-C2 consumer is
`CoupledChemDivFluxFactorFACInputs.resolver_package`.  It asks for
`ResolverHasSpectralAgreementC2Coeff U (coupledChemicalConcentration p u)`.
That record exposes, at each interior time, a local restart family `a` together
with `DuhamelSourceTimeC2Coeff a`.

The only committed C2-strength producer found in this tree is
`resolverHasSpectralAgreementC2Coeff_of_sourceFields`.  It packages K1
`LocalRestart` data, and its strengthened source package is
`DuhamelSourceTimeC2Coeff L.base.aC`.  In `LocalRestart`, `aC` is the
soft-clamped local source family; it agrees with the genuine source on the
active window, but the C2 coefficient envelopes are demanded for the clamped
family itself.

The restart branch is positively shifted: in the K1 local restart the target
time `σ` is represented from `τ = σ / 2`, so `σ - τ > 0`, and the represented
solution coefficients are `localRestartCoeff a₀ aC (σ - τ)`.  This gives the
expected heat factor on the homogeneous term.

However, `DuhamelSourceTimeC2Coeff` and hence `SourceC2CoeffFields` are attached
to the raw source family `aC`, not to `localRestartCoeff a₀ aC (·)`.  The source
fields explicitly demand summable envelopes for `λₖ |aC s k|` and
`λₖ² |aC s k|`, plus the corresponding `adot` fields.  The positive shifted
evaluation of the solution coefficients therefore does not by itself reduce
the current source obligation to merely bounded source coefficients.

`IsPaper2ClassicalSolution` supplies `D.classicalRegularity`.  On the interval,
that is spatial `ContDiffOn R 2` plus time differentiability/continuity and
closed-slab continuity.  It does not carry spatial order 3 or 4, nor any source
lambda-squared coefficient envelope.  The coupled chem-div source constructors
thread `IntervalWeakH2Neumann` and quadratic `C/(k*pi)^2` coefficient decay into
`DuhamelSourceTimeC1`; they do not upgrade it to `DuhamelSourceTimeC2Coeff`.

Verdict: the heat-factor route closes the model family whose coefficients are
already `exp (-ε λₖ)`-weighted, but not the actual clamped K1 source family.
The current resolver-C2 path is wired to the clamped K1 restart source, not to
an unclamped smooth classical-solution source.  Closing it requires either a
new C2 producer that exploits the positive Duhamel heat factor directly, or a
higher-regularity bootstrap producing the `sourceEigenEnvelope`,
`sourceEigenSqEnvelope`, and matching `adot` envelopes for the actual source
family used by the resolver-C2 package.
-/

noncomputable section

namespace ShenWork.Paper2.ChiNegResolverC2SourceAudit

open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)

abbrev resolverC2Agreement :=
  ShenWork.IntervalResolverJointC2.ResolverHasSpectralAgreementC2Coeff

abbrev facInputs :=
  ShenWork.IntervalCoupledRegularityBootstrap.CoupledChemDivFluxFactorFACInputs

abbrev k1SourceFields {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a) :=
  ShenWork.Paper2.PicardLimitK1C2Coeff.SourceC2CoeffFields src

abbrev paper2ClassicalSolution :=
  ShenWork.Paper2.IsPaper2ClassicalSolution

end ShenWork.Paper2.ChiNegResolverC2SourceAudit
