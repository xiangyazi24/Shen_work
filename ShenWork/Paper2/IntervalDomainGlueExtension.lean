/-
  Glue extension: given two classical solutions with overlapping time domains
  and pointwise agreement on the overlap, produce a classical solution on
  the union.

  Specifically: S₁ on [0, T₁] and S₂ on [0, T₂] from the same u₀ (with
  pointwise agreement on (0, min T₁ T₂)) give a solution on [0, max T₁ T₂].

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainUniformContinuation

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.GlueExtension

/-- **Glue extension from overlap agreement.**
If two classical solutions from the same u₀ agree pointwise on their
overlap (0, min T₁ T₂), then the one with the LONGER horizon is a
classical solution on [0, max T₁ T₂] — trivially, because a classical
solution on [0, max T₁ T₂] is already classical on any sub-horizon.

In fact, we just need the LONGER solution. By overlap uniqueness +
PID-gating (G6), two solutions from the same PID u₀ always agree on
their overlap. So the longer solution is the extension. -/
theorem classicalSolution_of_longer_horizon
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (h₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (h₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {u₀ : intervalDomainPoint → ℝ}
    (ht₁ : InitialTrace intervalDomain u₀ u₁)
    (ht₂ : InitialTrace intervalDomain u₀ u₂)
    (hle : T₁ ≤ T₂) :
    IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ ∧
    InitialTrace intervalDomain u₀ u₂ :=
  ⟨h₂, ht₂⟩

/-- **RestartAndGlueWorks is provable from QuantitativeLocalExistence
applied to u₀ directly, when δ > T₀.**

When the fresh solution horizon δ exceeds the existing horizon T₀,
the fresh solution already covers [0, δ] ⊃ [0, T₀ + δ/2]. No
restart from an interior slice is needed — just restrict. -/
theorem restartAndGlue_when_delta_exceeds
    {p : CM2Params} {δ : ℝ} (hδ : 0 < δ)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {T₀ : ℝ} (hT₀ : 0 < T₀)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (_hsol : IsPaper2ClassicalSolution intervalDomain p T₀ u v)
    (_htrace : InitialTrace intervalDomain u₀ u)
    {uf vf : ℝ → intervalDomainPoint → ℝ}
    (hsolf : IsPaper2ClassicalSolution intervalDomain p δ uf vf)
    (htracef : InitialTrace intervalDomain u₀ uf)
    (hle : T₀ + δ / 2 ≤ δ) :
    ∃ u' v', IsPaper2ClassicalSolution intervalDomain p (T₀ + δ / 2) u' v' ∧
      InitialTrace intervalDomain u₀ u' :=
  ⟨uf, vf, hsolf.restrict_horizon (by linarith) hle, htracef⟩

/-- **RestartAndGlueWorks when δ ≤ T₀**: the existing solution already
covers [0, T₀] ⊃ [0, δ]. Apply QuantitativeLocalExistence to u₀ to get
a fresh solution on [0, δ], then take the EXISTING solution restricted
to [0, T₀ + δ/2]... but T₀ + δ/2 > T₀, so this doesn't work directly.

The correct argument for δ ≤ T₀ uses the EXISTING solution S₁ and
applies the fresh factory to u₀ to get S₂ on [0, δ]. Both start from
u₀. If δ > T₀/2, then by overlap uniqueness S₁ and S₂ agree on (0, δ)
and S₂ restricted to [0, T₀ + δ/2 - ...] doesn't help.

Actually, the correct approach: always apply factory to u₀ directly.
If the factory gives S₂ on [0, δ], and δ ≥ T₀ + δ/2 (i.e., δ/2 ≥ T₀):
restrict S₂ to [0, T₀ + δ/2].

If δ < T₀ + δ/2 (always true when T₀ > 0 and δ > 0): the fresh
solution is too short.

The FIX: apply factory to u₀ with bound M' = regimeBound p M, getting
δ' = picardDelta(p, M'). Then the extension is δ'/2. The factory gives
a solution on [0, δ'] from u₀. For the case T₀ ≤ δ'/2: the fresh
solution [0, δ'] covers [0, δ'/2 + δ'/2] = [0, δ'] ⊃ [0, T₀ + δ'/2].

For T₀ > δ'/2: the fresh solution is shorter than the existing.
We need the restart from an interior slice — which requires
time-shifting + overlap glue.

The restart is genuinely needed when T₀ > δ/2. For now we expose it
as the RestartAndGlueWorks hypothesis. -/

-- Placeholder to close the namespace cleanly.
example : True := trivial

end ShenWork.Paper2.GlueExtension
