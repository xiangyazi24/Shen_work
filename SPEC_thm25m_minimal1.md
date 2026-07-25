# SPEC — Thm 2.5-M, minimal1 disjunct, general m (1 ≤ m < 2)

Branch: thm25m-wip (do NOT touch main). Goal: the χ₀>0 minimal-equilibrium
eventual global exponential stability, minimal1 disjunct, general m — the honest
bounded milestone. The UPPER BOX is already done on this branch (reuse
`exists_intervalDomainM_minimal_eventual_uniform_upper_bound`). Do NOT use the
χ₀≤0 Lyapunov package (it is χ₀≤0 only) or the strong-b>0 route (coeff ≤0 at b=0).

## Mirror templates (m=1, read for exact structure)
- ShenWork/Paper3/IntervalDomainMinimalEntropy.lean — `minimal1EntropyCoefficient`,
  `minimal1EntropyCoefficient_pos_of_chi_lt`, `intervalDomain_entropySlope_le_minimal1Coefficient`,
  `intervalDomain_entropyDiffusionChemotaxis_half_young`, `intervalDomain_minimal_weightedGradient_ge_l2`,
  `intervalDomain_minimal_powerDifference_integral_le`.
- ShenWork/Paper3/IntervalDomainMEntropyStrongDissipation.lean — the general-m
  entropy scaffold (`intervalDomainM_entropyDiffusionChemotaxis_young`, continuity
  scaffold, `strongMEntropyCoefficient`) to mirror for the HALF split.
- M-native base already exists: `intervalDomainM_entropySlope_le_of_classical`.
- Elliptic/Poincaré already M-compatible: `intervalDomain_classicalSlice_poincare`.

## New M-native lemmas (build in order, lake-verify EACH before next)
1. `intervalDomainM_entropyDiffusionChemotaxis_half_young`: pointwise
   `−c·A² + χ₀c·A·B ≤ −(c/2)·A² + (χ₀²c/2)·B²`, A² = weighted-gradient at weight
   `2−2m`, B² = signal W. Mirror `intervalDomainM_entropyDiffusionChemotaxis_young`
   (same continuity scaffold); change the final `nlinarith` square to `(A − χ₀·B)²`.
2. `intervalDomainM_minimal_weightedGradient_ge_l2` at weight `2−2m`: uses
   `U^(2−2m) ≥ uBar^(2−2m)` (from `0 < U ≤ uBar` and exponent `2−2m ≤ 0` for m≥1) +
   `intervalDomain_classicalSlice_poincare`.
3. `minimal1MEntropyCoefficient` (general-m) + `..._pos_of_chi_lt` from a general-m
   threshold `chiMinimal1FormulaM p p.m uStar uBar vLower` (m=1 hardcodes the `1`;
   the `c=(2m−1)·uStar^(2m−1)` and `uBar^(−2m)` factors change the radicand — derive
   them honestly from lemmas 1-2).
4. `intervalDomainM_entropySlope_le_minimal1MCoefficient`: assemble base
   (`intervalDomainM_entropySlope_le_of_classical`) + (1) + (2) + shared elliptic + power.
5. `intervalDomainM_minimal1_theta_le_L2` bridge: `chemotaxisThetaDissipation
   intervalDomain uStar p.α (u t) ≤ C(uStar,uBar,α)·(L2 slice)` (MVT-type, integrated
   over the box) — needed because `intervalDomainM_exists_late_supClose_of_thetaDissipation`
   wants exponent `p.α`, while the entropy route is L2 (exponent 1).
6. Late chain: (4)+(5) ⇒ `exists_late_dissipation_lt_of_nonnegative_energy`
   (need entropy-functional nonnegativity, mirror the strong nonneg lemma) ⇒
   `intervalDomainM_minimal1_exists_late_thetaDissipation_lt` ⇒
   `intervalDomainM_exists_late_supClose_of_thetaDissipation` ⇒ M weak-sup basin entry
   (`IntervalDomainMMinimalWeakSupBasinEntry`) ⇒ bootstrap
   (`intervalDomainM_minimal_eventualC1_of_uniformSup_of_massGap`) ⇒
   `intervalDomainM_eventuallyGloballyExponentiallyStableMinimal_minimal1M`.
7. Define `MinimalGlobalStabilityFormulaConditionM` (minimal1 disjunct, general-m:
   `0 < χ₀ ∧ χ₀ < chiMinimal1FormulaM p p.m uStar uBar vLower`) and prove
   `intervalDomainM_Theorem_2_5_minimal1_EventualGlobalStabilityFormula` (range 1≤m<2).

## Rules
- 0 sorry/0 axiom/0 admit/0 native_decide, clean-3. maxHeartbeats 1000000 as needed.
- CONFIRM every reused lemma name by grep before use; fully-qualify + import the
  defining file. (Prior agents guessed wrong names — do not.)
- HONESTY GATE: if a specific step needs a fact that truly doesn't exist for 1≤m<2
  after grep, STOP + report the exact missing fact. No sorry/axiom/assume/weaken.
- VERIFY MANDATORY: `lake build <module>` per new module, confirm "Build completed
  successfully" 0 errors before claiming that module done. Paste real output.
- If minimal1 fully lands, that is the milestone; minimal2 remains tracked.
