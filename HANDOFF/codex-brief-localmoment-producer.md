# Codex Brief — the missing `WholeLineLocalMomentEnergyData` producer

Repo ~/Shen_work (HEAD 2ef5f95a). Rules: 0 sorry, 0 axiom, NEW files only,
build green per file, APPEND imports to ShenWork.lean. Do NOT commit.

## The exact gap

`WholeLineLocalMomentBound.lean` proves `UniformlyLocalLpBounded` CONDITIONALLY
on `WholeLineLocalMomentBoundData`, whose field
  `energyData : ∀ t ∈ Ioo 0 T, ∀ x₀, WholeLineLocalMomentEnergyData p P κ T t x₀ u v`
has no producer for the canonical solution. Until it has one, Prop 1.1's
residual window (1 ≤ χ) is not closed. This task is that producer.

## Architecture to mirror (do not invent a new one)

The repo already differentiates a WEIGHTED ENERGY along the canonical orbit, for
the moving-frame L² error with weight `exp (2ηx)`:
  `wholeLineCauchyGlobal_weightedEnergy_differentiableAt_positive_natural`
  (WholeLineWeightedRegularityGlobalEnergyDifferentiableNatural.lean:86)
which reduces, through the segment/restart bookkeeping
(`wholeLineCauchyGlobalSegment`, `...PreferredTranslatedDatum`,
`wholeLineCauchyGlobal_weightedEnergy_eventuallyEq_preferredTranslated`), to the
MILD-FIXED-POINT level producer
  `wholeLineCauchyBUCMildFixedPoint_weightedEnergy_differentiableAt_natural`.

Mirror that architecture for the functional
  `wholeLineLocalLpEnergy P κ u t x₀ = ∫ x, (u t x)^P * localizingWeightAt κ x₀ x`
(WholeLineLocalMoment.lean). Differences to handle:
* the integrand is `u^P ψ`, not `e^{2ηx}|u − U|²` — no wave, no subtraction, but
  a general real power `P > 1` (use `Real.rpow`, and the positivity of `u` on
  positive times to differentiate `u ↦ u^P`);
* the weight is `localizingWeight κ` with the committed package
  (`WholeLineLocalizingWeight.lean`, `WholeLineLocalizingWeightSecond.lean`):
  `0 < ψ ≤ 1`, `|ψ'| ≤ κψ`, `|ψ''| ≤ (κ+κ²)ψ`, `ψ ≤ exp(−κ|x|)` — the last one
  gives the domination needed for differentiation under the integral;
* `ψ` is integrable and bounded, so the dominating function is
  `C · exp(−κ|x|)` with `C` from the slab bound on `u` — much easier than the
  exponentially GROWING weight the L² chain had to handle.

## Deliverables

M1. The mild-fixed-point level statement: on a segment with a uniform slab bound
    `0 ≤ u ≤ M`, the map `t ↦ ∫ (u t x)^P ψ(x−x₀) dx` has a derivative given by
    differentiating under the integral, with the dominating function above.
M2. The IBP/energy-identity fields of `WholeLineLocalMomentEnergyData` for the
    canonical solution (the spatial integrations by parts against `ψ`, using the
    committed first/second derivative domination and the C² regularity of the
    canonical solution at positive times).
M3. `wholeLineCauchyGlobal_localMomentEnergyData` : the segment/restart assembly
    producing the field for every `t ∈ Ioo 0 T` and every `x₀`, then
    `wholeLineCauchyGlobal_uniformlyLocalLpBounded` by feeding
    `WholeLineLocalMomentBoundData`.

Report after M1 (it is the load-bearing analytic step). If a step cannot be
done, STOP there with the exact failing goal and land everything before it.
