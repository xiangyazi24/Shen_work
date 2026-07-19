# Codex Brief — Supercritical χ>0 Long-Time Chain (mechanical clone)

Repo ~/Shen_work. Rules: 0 sorry, 0 axiom, NEW file only, verify with
`lake build ShenWork.Paper1.<Module>`. Do NOT commit. You may append ONE import line
to ShenWork.lean at the very end.

The mathematical layer is DONE and committed:
`ShenWork/Paper1/WholeLineChiPosSupercriticalCeiling.lean` provides, for the branch
`hsuper : p.m + p.γ - 1 < p.α` (NO smallness on χ > 0 needed):
- `wholeLineCauchyChiPosSupercriticalRate p = p.α - (p.m+p.γ-1)` (+ _pos)
- `wholeLineCauchyChiPosSupercriticalCeiling p C t` (+ _zero, _hasDerivAt, _base_le, _le, _restart)
- `chiPosSupercriticalCeiling_supersolution` : for B ≥ parameterCeiling,
    χ·B^(m+γ) + reactionFun α B + rate·(B − parameterCeiling) ≤ 0
- `supercriticalEffectiveReaction p s = χ·s^(m+γ) + reactionFun α s` and
  `supercriticalEffectiveReaction_sub_le` (one-sided Lipschitz with the SAME
  `effectiveReactionLip p A = 1 + (α+1)A^α`)
- atoms in `WholeLineChiPosSupercriticalAtoms.lean` (tangent n≥1, gap, scaled gap)

TASK: clone the committed CRITICAL chain
`ShenWork/Paper1/WholeLineCauchyChiPosLongTimeBound.lean` lines 216–884 into a new file
`ShenWork/Paper1/WholeLineChiPosSupercriticalLongTimeBound.lean`, replacing:
- ceiling `wholeLineCauchyChiPosCeiling` → `wholeLineCauchyChiPosSupercriticalCeiling`
- base `MChi p` → `wholeLineCauchyParameterCeiling p`
- rate `p.α` → `wholeLineCauchyChiPosSupercriticalRate p`
- scalar field: the critical file's `u*(1-(1-χ)u^α)` → `supercriticalEffectiveReaction p u`
  (equivalently keep the PDE hypothesis shape identical — the resolver-value term is
  handled by DISCARDING the favorable `-χ u^m v ≤ 0` and bounding the adverse part by
  `+χ u^{m+γ}`; the drift term treatment is unchanged)
- hypotheses `hχ_lt : χ < 1` and `halpha : α = m+γ-1` → `hsuper : m+γ-1 < α`
- the slab's `G r = Kreact * max (-r) 0 - p.α * max r 0` → same with the new rate

Deliver in order (each building green):
1. `wholeLineSlab_le_chiPosSupercriticalCeiling_of_positive_resolver_pde` (mirror of :216)
2. Ico / Icc mild-fixed-point wrappers (mirror of :515 / :651)
3. step ceiling + successor identity (mirror of :711–735)
4. segment induction + global pointwise bound (mirror of :736–848)
5. `wholeLineCauchyGlobal_uniformLimsupLe_parameterCeiling_of_chi_pos_supercritical`
   (mirror of :851; construct the ceiling regime internally as `Or.inr ⟨hχ.le, Or.inl hsuper⟩`)
6. a range-bound corollary mirroring `wholeLineCauchyGlobal_le_max_of_chi_pos`.

Report: per-item build status + which critical-file lemmas needed genuine adaptation
(as opposed to a name swap).
