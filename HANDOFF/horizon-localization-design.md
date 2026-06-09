# Horizon localization design — dissolving the global-quantifier sorrys (2026-06-09)

## The diagnosis (why 14 of the 21 remaining sorrys are unfillable AS TYPED)

The spectral restart machinery's interfaces quantify over ALL time:
- `DuhamelSourceTimeC1 a`: `hderiv : ∀ s n, HasDerivAt …` (all s ∈ ℝ),
  `henv_bound : ∀ s, 0 ≤ s → …`, `hderivBound : ∀ s, 0 ≤ s → …`
- `DuhamelSourceL1Cont a`: `hcont : ∀ n, Continuous (fun s => a s n)` (all ℝ)
- Ledger K1 fields (`hderivt`, `hadotcontt`, `hMdott`, + shifted family): global σ
- Ledger K2 fields (`hG1t`, `hG2t`): single uniform constant over ALL σ ∈ (0,T)

But a `GradientMildSolutionData D` constrains `D.u` ONLY on (0,T]. Worse:

1. **Arbitrary-D unfillability**: for σ ≤ 0 or σ > T, `D.u σ` is arbitrary; no
   global HasDerivAt/continuity/envelope can be produced. The Provider takes
   arbitrary D (the final theorem quantifies `∀ D`), so the K1 sorrys are
   structurally unfillable.
2. **Genuine falsity near 0**: for merely-continuous u₀, parabolic smoothing
   gives ‖∇u(σ)‖ ~ σ^{-1/2} → ∞. A single uniform G1 over σ ∈ (0,T) does not
   exist. `hG1t`/`hG2t`/`Mdott` as typed are UNSATISFIABLE — same class of
   vacuity as the old global-C² field (hC2t), one level deeper.

## The key structural fact (the unlock)

`HasTimeNeighborhoodSpectralAgreement` (IntervalMildTimeDerivContinuity.lean:46)
quantifies the source family EXISTENTIALLY, per t₀:

    exists_data : ∀ t₀ ∈ (0,T), ∃ a₀ M a (_ : DuhamelSourceTimeC1 a) offset, …

The witness family is OUR CHOICE. The restart integrals (`localRestartCoeff`)
only read the family on σ ∈ [0, s − offset], i.e. absolute times in
[offset, s] ⋐ (0,T). So:

## Design: C¹ soft-clamp witnesses

For each t₀, set τ = t₀/2, pick a C¹ clamp φ : ℝ → [c',d'] ⊂ (0,T) with
φ = id on [c,d] ⊇ [τ, (t₀+T)/2] (c' = τ/2, d' = (t₀+3T)/4). Witness family:

    aS' σ k := cosineCoeffs (logisticLifted p (u (φ(τ + σ)))) k

- `hderiv` at any σ ∈ ℝ: chain rule; outer derivative is the ledger's
  time-LOCALIZED K1 `hderivt` at φ(τ+σ) ∈ [c',d'] ⊂ (0,T); inner is ψ = φ'.
- `adot σ k = adott (φ(τ+σ)) k · ψ(τ+σ)`; `hadotcont` from ContinuousOn-(0,T)
  composed with φ (range inside); `derivBound = Mdott([c',d']) · 1`.
- envelope: per-slice decay machinery evaluated at φ(τ+σ) ∈ [c',d'] — needs K2
  bounds only on the compact [c',d'].
- Agreement transfer: for s near t₀, integration range absolute times ⊆ [τ,s]
  ⊆ [c,d] where φ = id ⇒ `localRestartCoeff a₀ aS' = localRestartCoeff a₀ aS`
  (canonical) by `intervalIntegral.integral_congr` ⇒ the restart identity from
  `picardLimitRestart_general` rewrites across.

**Bonus**: the shifted K1 family (`adotS`/`hderivS`/`hadotcontS`/`MdotS`/
`hMdotS` — 5 ledger fields) becomes DERIVED (chain rule), not carried. Delete.

## Ledger V2 (satisfiable retype)

Replace in `ReducedLimitRegularityInputs` (and mirror in
`LimitRegularityInputs`):
- K1: `hderivt`/`hadotcontt` restricted to σ ∈ (0,T); `hMdott` per-compact:
  `∀ a b, 0 < a → a ≤ b → b < T → ∃ Mdot, ∀ σ ∈ Icc a b, ∀ k, |adott σ k| ≤ Mdot`
- K2: `hG1t`/`hG2t` per-compact (∃ G1 per [a,b] ⋐ (0,T)); drop global G1 G2
  data fields.
- DELETE the 5 shifted-K1 fields.
- `hsrc0` (weak package, from-zero rep): continuity on ℝ obtained by plain
  min/max clamp at horizon T'' < T — needs canonical-family continuity only on
  [0,T''] (right-continuity at 0 via initial approach;
  `gradientMildSolutionData_initialApproach` is generic). The clamped family
  agrees with canonical on [0,T''] ⊇ every integration range used. Requires
  generalizing `picardLimitRestart_general` (and the weak limit engine entry
  points) to accept any family agreeing with canonical on the horizon — check
  its proof's actual consumption of hsrc0 first.

## Provability of the compact-localized producers (verified routes)

- K2 per-compact G1/G2: from the weak engine's envelope, σ-uniform on [a,b]:
  λ_k|bc σ k| ≤ M₀λ_k e^{−aλ_k} + env_k (monotone in σ), summable ⇒ term-wise
  differentiation of the cosine series; endpoints by the junk-deriv
  (`deriv_zero_of_not_differentiableAt`) trick already used for hN0t/hN1t.
  → agent: IntervalCompactSliceGradientBounds.lean
- Hvpos: resolver = Laplace transform of semigroup;
  `intervalFullSemigroupOperator_pos` (IntervalSemigroupConeAtoms.lean:191)
  gives strict integrand. → agent: IntervalResolverStrictPositivity.lean
- hpde_u: spectral series PDE algebra from `mildSolution_deriv_eq` +
  Laplacian-of-series + source inversion. → agent: IntervalDomainPdeUProducer.lean
- Clamp: ψ from `Real.smoothTransition` products, φ = c + ∫ψ, FTC.
  → agent: IntervalTimeSoftClamp.lean
- K1 producer (adott on (0,T)): F2 instantiation from G2.5 limit passage
  (IntervalMildPicardLimitRegularity) — the genuine remaining math; NOT in
  this wave.

## Execution order

1. (parallel agents, done first) clamp infra, Hvpos, hpde_u, K2 compact bounds.
2. `limitSource_duhamelSourceTimeC1_clamped` — localized variant of
   `limitSource_duhamelSourceTimeC1_of_representation` (mechanical edit:
   every σ becomes φ(τ+σ), data hypotheses restricted to [c',d']).
3. `Hu_of_restart_localized` — clamped-witness rebuild of `Hu_of_restart`.
4. Ledger V2 retype + LedgerSweep V2 adapters + Provider refill.
5. hsrc0: generalize `picardLimitRestart_general` horizon consumption; clamp
   the weak package.
6. K1 producer (F2) — separate campaign.
