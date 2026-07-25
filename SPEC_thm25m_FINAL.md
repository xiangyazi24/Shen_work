# BUILD-READY SPEC — Paper 3 Theorem 2.5-M for 1 ≤ m < 2 (from ChatGPT Q1003)

## Scope (honest, pinned)
Thm 2.5-M (general-m minimal-equilibrium eventual global exponential stability) is
tractable for **1 ≤ m < 2** (subcritical flux). m=2 is critical (separate project),
m>2 supercritical (mass alone insufficient — do NOT attempt all-m).

## The exact obstruction
m=1 orbit-independent L^P bound closes via an exponent coincidence: cross-term
population exponent r = P+m−1; Young → 2r−P = P+2m−2; equals P iff m=1
(critical_energy_cross_young). Two explicit m=1 casts to remove:
- IntervalDomainMinimalEventualLp.lean L98-104: isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one
- IntervalDomainMinimalEventualHighLp.lean L57-64: isPaper2GlobalClassicalSolution_intervalDomainM_of_m_eq_one
  (+ classicalSolution_intervalDomain_of_m_eq_one back-cast)

## Build plan
1. NEW lemma (the only genuinely new analytic step): orbit-independent eventual L^P
   bound for the positive-χ₀ mass-constrained intervalDomainM equation, M-NATIVE
   (no legacy cast), via scalar_seed_agmon_absorb (1D GN/Agmon interpolation) with
   seed exponent p₀ = physical mass exponent. For 1≤m<2 the excess 2m−2 < 2 is
   absorbed by the Agmon/GN interpolation term (subcritical). Mirror the m=1
   IntervalDomainMinimalEventualLp chain (exists_minimal_critical_lp_damping_constant
   → exists_minimal_eventual_lp_power_bound → exists_minimal_eventual_high_lp_power_bound)
   but on intervalDomainM directly, carrying an explicit hm : 1 ≤ p.m ∧ p.m < 2.
2. REUSE (already general-m): final Lp→L∞ via solutionSlice_le_of_restart_affine_lp_general
   / boundedGlobal_of_lp_restarted_affine_general → orbit-independent uBar.
3. REUSE: signal floor vLower (benign given uBar), mass-constrained local bootstrap
   intervalDomainM_minimal_eventualC1_of_uniformSup_of_massGap, Stage B, χ≤0 branch.
4. ASSEMBLE: intervalDomainM_Theorem_2_5_EventualGlobalStabilityFormula (range 1≤m<2).

## Vehicle
Codex (out until 2026-07-28) or Claude authorization. When available: dispatch step 1
(the M-native L^P bound) first, verify clean-3 + lake build, then steps 2-4 assemble.
