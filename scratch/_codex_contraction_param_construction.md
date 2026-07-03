# Codex Spec: Contraction Parameter Construction

## Goal

Create ONE new file `ShenWork/Wiener/EWA/ContractionParameterChooser.lean`
that constructs the contraction parameters from datum bounds.

## What to prove

Given M > 0 (bound on initial data) and model parameters p,
construct ρ, Md, Mdv, R, δv, δ(small time) such that:

1. The EWA Picard operator `picardEWA` maps
   `closedBall (heatEWA u₀E) ρ → closedBall (heatEWA u₀E) ρ`
2. The contraction condition
   `|χ₀| * C₀ * √T * L_Q + L_G * T < 1` holds for T ≤ δ
3. The derivative/norm bounds hold on the ball:
   - `∀ u ∈ closedBall (...) ρ, ‖GWA.gDeriv u‖ ≤ Md`
   - `∀ u ∈ closedBall (...) ρ, ‖u‖ ≤ R`
   - `∀ u ∈ closedBall (...) ρ, ‖GWA.gDeriv (vdEWA ...)‖ ≤ Mdv`

## Approach

Look at `exists_uniform_EWA_lifespan` (ChiNegUniformLifespan.lean) — it
chooses δ given Lipschitz bounds. The missing piece is computing the
Lipschitz bounds from the ball radius.

The Lipschitz bounds are computed by:
- `chemFluxEWA_lipschitz` (FluxLipschitzGraded.lean:340) — gives L_Q from R, Md, δv, Mdv, etc.
- `growthEWA_lipschitz` (FluxLipschitzGraded.lean:180) — gives L_G from R, Md, α, a, b, etc.

The key: read `hLQ` and `hLG` equalities in `picardEWA_uncond_fixedPoint`
(SourceUncondFixedPoint.lean:65-80) — they give the EXACT formulas.

For the ball bounds (Md, R, Mdv):
- R should be heatEWA norm + ρ (by ball definition)
- Md should be gDeriv(heatEWA) + some margin (by triangle inequality on the ball)
- These are computed from the initial data's properties

## The theorem signature (draft)

```lean
theorem exists_contraction_tower_of_datum_bound
    (p : CM2Params) (hchi : p.χ₀ < 0)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hβ : 0 < p.β) (hμle1 : p.μ ≤ 1)
    {u₀ : ℝ → ℝ} (hu₀ : Continuous u₀)
    (hsumc : Summable (fun k => |cosineCoeffs u₀ k|))
    (hmem : MemW 1 (ofCosineCoeffs (cosineCoeffs u₀)))
    {M : ℝ} (hM : 0 < M)
    (hbd : ∀ n, |cosineCoeffs u₀ n| ≤ M)
    (η : ℝ) (hη : 0 < η) (hfloor : ∀ y, η ≤ u₀ y) :
    ∃ (δ ρ δv Md Mdv R L_Q L_G : ℝ)
      (hT : 0 < δ)
      (hδρ : 0 < η - ρ)
      (hheat : UniformFloor (heatEWA (T := δ)
        (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1)) η),
      -- self-map
      MapsTo
        (picardEWA p p.μ p.ν p.γ p.hμ (le_of_lt hT)
          (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1))
        (Metric.closedBall
          (heatEWA (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1)) ρ)
        (Metric.closedBall
          (heatEWA (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1)) ρ) ∧
      -- contraction
      (0 ≤ |p.χ₀| * (C₀ * Real.sqrt δ) * L_Q + L_G * δ) ∧
      (|p.χ₀| * (C₀ * Real.sqrt δ) * L_Q + L_G * δ < 1) ∧
      -- derivative/norm bounds
      (∀ u ∈ Metric.closedBall (heatEWA (T := δ)
          (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1)) ρ,
        ‖GWA.gDeriv u‖ ≤ Md) ∧
      -- ... more bounds ...
      True  -- placeholder, read the actual requirements
```

## CRITICAL: Read FIRST, then write

1. Read `picardEWA_uncond_fixedPoint` (SourceUncondFixedPoint.lean)
   to get the EXACT list of hypotheses
2. Read `chiNegStrong_EWA_fixedPoint_of_floor` (SourceChiNegUncondFix.lean:166)
   to see which hypotheses it passes through
3. Read `FluxLipschitzGraded.lean` for the Lipschitz constant formulas
4. Read `SourceFixedPoint.lean` and `SourceFixedPointAbs.lean` for
   the self-map and contraction proof patterns
5. Read `HeatFloor.lean` and `HeatFloorIcc.lean` for the floor bridge

## The construction pattern

1. Set ρ := η/2 (ball radius = half the floor)
2. Set R := ‖heatEWA u₀E‖ + ρ (norm bound on ball)
3. Set Md := ‖gDeriv(heatEWA u₀E)‖ + some_margin (derivative bound)
4. Compute L_Q, L_G from R, Md, Mdv, p using the explicit formulas
5. Choose δ via `exists_uniform_EWA_lifespan` with these bounds
6. Verify self-map via `picardEWA_selfMap_of_all` or similar

NOTE: The exact choice depends on the existing infrastructure. READ
the codebase before choosing values. The existing `SourceFixedPointAbs.lean`
has the abstract self-map conditions — study them.

## Verification

```bash
cd ~/repos/Shen_work
lake build ShenWork.Wiener.EWA.ContractionParameterChooser 2>&1 | tail -10
```

Must compile with `#print axioms` showing ONLY [propext, Classical.choice, Quot.sound].

## Constraints

- NO sorry, NO axiom, NO native_decide, NO admit
- Line length ≤ 100 characters
- Do NOT modify any existing files
- If the full construction is too complex, produce a STALL REPORT
  listing the exact missing pieces
