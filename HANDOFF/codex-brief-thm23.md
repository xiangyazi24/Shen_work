QUEUED for Codex#2 (Paper3, warm, AFTER Thm 2.2 lands — depends on Thm 2.2's local-stability basin).
TASK: Paper 3 Theorem 2.3-2.5 GLOBAL stability via the entropy/Lyapunov route. Full grind, no cap.

## Diagnosis (Q4577 + Fable, HANDOFF/FABLE-P3-ROADMAP.md):
- Interface issue: IntervalDomainStabilityChain.lean wrappers ask for a derivative inequality on
  chemotaxisThetaDissipation itself — STRONGER than the paper route. REPLACE (additively) with an integrated
  relative-entropy dissipation package + a sequential basin-entry lemma.
- The requested relative entropy is NOT the existing chemotaxisEntropyDensity (repo's h_m). Use the standard
  H(u)=∫[u ln(u/u*)−(u−u*)] (my ShenWork.Paper3.RelativeEntropy.relEntropy_integrand_nonneg proves H≥0 pointwise;
  log_mul_rpow_diff_nonneg gives the reaction-term dissipation sign; ShenWork.Paper3.WeightedYoung.weighted_young
  is the chemotaxis-absorption Young).
- Entropy half formalizable from IsPaper2ClassicalSolution API (carries C² slices, time derivs, joint continuity,
  u>0, v≥0, Neumann at all t∈(0,T)) — NO positive-time regularity gap. Needs: 1 new entropy time-Leibniz lemma
  + 1 new weighted-PDE-under-integral lemma + 2 already-landed spatial IBP engines.
- MISSING leaf: ∫₀¹|v_x|²≤C∫₀¹|u_x|² (single-solution) via a weighted cosine/sine Parseval multiplier estimate;
  sharp first-mode const (γνu*^{γ-1})²/(π²+μ)² from 1/(λ_k+μ)²≤1/(π²+μ)² (k≥1). static_v_grad_L2_le_Eu is the
  two-solution DIFFERENCE version (reuse its guts). Resolver modal rep: unitIntervalCosineHilbertBasis + the
  resolver representation. (ChatGPT Q4580 Parseval design pending — check /tmp/gpt_Q4580.md if landed.)
- Closing (NO LaSalle): integrated dissipation ⇒ D(tₙ)→0 + time-translate precompactness (1D Arzelà-Ascoli:
  |φ(x)−φ(y)|≤‖φ'‖_{L²}|x−y|^{1/2}) + zero-dissipation rigidity ⇒ enter basin ⇒ apply Thm 2.2 local exp (Codex#2's
  IntervalDomainSpectralSemigroupOrbitBoundCorrected). BUT D(tₙ)→0 alone ≠ basin entry: need coercivity D→basin-norm
  OR compactness+rigidity.
## Build additively (don't break IntervalDomainStabilityChain). Reuse my entropy/Young lemmas (Paper3/Interval-
## DomainRelativeEntropy.lean, IntervalDomainWeightedYoung.lean). Single-file lake env lean + #print axioms; commit
## each milestone; Paper3/* only (coordinate with Codex#2's Sectorial files — use NEW files for the entropy chain).
