# hDu threading design (R-src0F-3 + audit risk #2, 2026-06-10 ~12:30)

FINDING: both consumers of the universal ledger H already possess
D.u = picardLimit p u₀ D.T:
- PicardLimitRestartFrontier (ConeQuantBridge:121) carries it as a hypothesis;
  its sole instantiation uses gradientMildSolutionData_of_data E with rfl.
- hMildLocal_chi0_zero_of_inputs (MildLocalChi0:~298) constructs D via
  coneGradientMildSolutionData_exists and DISCARDS the fact:
  `obtain ⟨D, _hDT, _hDu⟩ := hD u₀ …` — the underscore is the smoking gun.

THE FIX (threading pass, blocks on the two in-flight Provider agents):
1. Retype H everywhere from `∀ u₀, PID → ∀ D, Inputs` to
   `∀ u₀, PID → ∀ D, D.u = picardLimit p u₀ D.T → Inputs`:
   - MildLocalChi0: hMildLocal_chi0_zero_of_inputs (pass the un-discarded hDu),
     paper2_theorem_1_1_chiZero_of_inputs
   - LedgerSweep: both _of_reduced_inputs + the adapter lambdas
   - Provider: reducedLimitRegularityInputs_of_picard gains
     (hDu : D.u = picardLimit p u₀ D.T); capstone's hPLF lambda uses its _hDu.
2. R-src0F-3 then closes: rewrite hDu, apply IntervalPicardLimitCoeffConv.
   picardIter_logisticCoeff_tendsto_limit (ALREADY PROVED).
3. This also fixes ChatGPT capstone-audit risk #2 (∀-D overclaim): the
   Provider honestly claims only the canonical Picard limit.

# R-src0F-2 design notes (the analytic core, dispatch after threading)
Need: n-uniform |coeffs(logistic(picardIter p u₀ n σ)) k| ≤ windowEnv(C a') k
for σ ∈ [a', T]. Ingredients to survey: IntervalPicardIterateC2Bound
(n-uniform M/G1/G2?), IntervalPicardIterateSourceC1 (per-iterate decay with
which constants?), the Picard invariant ball (sup bounds n-free by
construction). The envelope constant must depend only on (a', T, p, u₀-data).
