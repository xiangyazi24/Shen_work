# DOCTRINE — Theorem 2.4 general-m (Fable#4, strong-logistic Lyapunov chain)

Owner: Fable#4.  Scope: Paper 3 Theorem 2.4 headline with NO `p.m = 1` gate,
on the paper-faithful domain `intervalDomainM` (flux `u^m ∇v/(1+v)^β`).
Fable#3 owns the Thm 2.2 small-data files (`IntervalDomainM{Faithful,MinimalFaithful}Theorem22`,
`IntervalDomainM{,Minimal}SmallDataGlobalExistence`, `IntervalDomainMWeakSupStageB`,
`IntervalDomainMMinimalWeakSupBasinEntry`, `IntervalDomainMinimalStrong{Bootstrap,Duhamel}GeneralM`) — do not touch.

## Target

`Theorem_2_4_EventualGlobalStabilityFormula intervalDomainM p intervalDomainMSectorialStabilityNorms M0`
(def in `EventualGlobalStability.lean:89`), i.e. for `0<a,0<b,0≤β,0<α,0<γ` and the 4-branch
`NonminimalGlobalStabilityFormulaCondition` (each branch carries `1 ≤ p.m` — the paper's own hypothesis):
`EventuallyGloballyExponentiallyStableNonminimal intervalDomainM p N eq.1 eq.2`
= global sup attraction ∧ orbitwise eventual exponential C¹ convergence.
Faithfulness: paper §7 proves Thm 2.4 for general m ≥ 1; chi formulas in `Statements.lean:2972+`
are already general-m (`(2m-1)`, `u*^(2γ-α+2m-2)`); no vacuity (branch hypotheses satisfiable, same as m=1 headline).

## Why the m=1 gate exists and how it falls

Legacy `intervalDomain` hardcodes the m=1 flux; the whole m=1 chain carries `hm : p.m = 1`
because the *equation* is the m=1 specialization. The faithful general-m equation is
`intervalDomainM` (differs only in `chemotaxisDiv`/`crossDiffusionEnergyTerm`; all other fields shared).
The entropy math generalizes through the *already committed, already general* Lp machinery:

KEY IDENTITY: the entropy test `h_m'(u) = 1 - (u*/u)^(2m-1)` is
`LpTest(1) - u*^(2m-1) · LpTest(2-2m)` where `LpTest(q)(U)=|U|^(q-2)U=U^(q-1)`.
m=1 used exponents (1,0); general m uses (1, 2-2m). Everything downstream is exponent-generic.

## Reused (committed; verified no hm, correct domain)

- `chemotaxisEntropyDensity/Integrand m` + FTC/chain rule + nonneg (`LyapunovFunction.lean`) — general-m already.
- Lp identity machinery on `intervalDomainM`, ANY real `pExp` (`Paper2/IntervalDomainMLpEnergy.lean`):
  `pdeIntegral`, `diffusion_ibp`, `diffusion_dissipation_eq` (`= (pExp-1)·G(pExp)`),
  `chemotaxis_ibp` (`-χ₀C(q) = χ₀(q-1)X(q)`, `X(q) = ∫U^(q+m-2)U_xV_x/(1+V)^β`).
- Time-Leibniz on `intervalDomainM` (`Paper2/IntervalDomainMLpTimeLeibniz.lean`): `timeDeriv_isGenuine`, `powerEnergy_hasDerivAt`.
- Elliptic weight estimate `intervalDomain_entropyElliptic_gradient_estimate_of_classical` (takes hsolM, no hm).
- Lemma A.6 `intervalDomain_powerDifference_integral_le_theta` (takes hsolM, no hm).
- Generic energy lemma `exists_late_dissipation_lt_of_nonnegative_energy` (`EntropyStrong1Dynamics.lean:22`).
- Arzelà–Ascoli tail slices `intervalDomainM_globalBounded_tailSlices_subseq` (`IntervalDomainGlobalTailHolderM.lean`).
- Time shift/trace/slice-datum on M: `classicalSolution_timeShiftM`, `timeShiftInitialTraceM`,
  `classicalSolution_slice_paperPositiveInitialDatumM` (`Paper2/IntervalDomainMContinuationExtension.lean`).
- Stage B general-m orbit bound: `intervalDomainM_weakSupEventualSpectralSemigroupOrbitBound_of_basinEntry`
  (`IntervalDomainStrongStageBGeneralM.lean`) + `intervalDomainMSupToStrongBasinEntry_proved`
  (`IntervalDomainMWeakSupBasinEntry.lean`) — both committed (Fable#3's *untracked* one-line composition is NOT imported).
- Formula ⟹ discrete linear stability: `NonminimalGlobalStabilityFormulaCondition.linearlyStable_unitInterval` (no hm).
- `intervalDomainMSectorialStabilityNorms` with `c1Distance = intervalDomainSectorialC1Distance` (`IntervalDomainMSectorial.lean`).

## The general-m math (paper (7.2)–(7.8))

slope F_m'(t) = pde(1) − u*^(2m-1)·pde(2−2m)
= −(2m−1)u*^(2m-1)·G(2−2m) + χ₀(2m−1)u*^(2m-1)·X(2−2m) + [L(1) − u*^(2m-1)L(2−2m)]
with G(2−2m)=∫U^(−2m)U_x², X(2−2m)=∫U^(−m)U_xV_x/(1+V)^β.

1. **Young** (new pointwise, exponents −2m/−m): −A²+χ₀AB ≤ χ₀²B²/4 with A=U^(−m)U_x, B=V_x(1+V)^(−β)
   ⟹ chemo+diffusion ≤ (2m−1)u*^(2m-1)·χ₀²/4·∫V_x²(1+V)^(−2β).
2. **Elliptic + A.6** (reused) ⟹ ≤ χ₀²ν²·C_{αγ}·(2m−1)·u*^(2γ−α+2m−2)/(16μ(1+β̃v*)) · θDissip(α).
3. **Logistic** (new pointwise, m ≥ 1): with a = b·u*^α,
   L(1) − u*^(2m-1)L(2−2m) = −b·∫(1−(u*/u)^(2m-1))·u·(u^α−u*^α) ≤ −b·θDissip(α),
   since (1−(u*/u)^(2m-1))·u − (u−u*) = u*·(1−(u*/u)^(2m-2)) has the sign of (u−u*) for m ≥ 1.
4. Coefficient `strongMEntropyCoefficient = b − χ₀²ν²C(2m−1)u*^(2γ−α+2m−2)/(16μ(1+β̃v*))`;
   positive ⟺ χ₀ < chiStrong1Formula (exact radicand match — the m=1 file's `rw [hm]` step simply disappears).

## Basin entry, general-m (replaces the m=1 Lipschitz route)

m=1 used a Lipschitz producer + static coercivity family lemma. For general m the committed
producer is Hölder-1/2 (`intervalDomainM_globalBounded_eventual_holder`); cleaner route:
suppose no late slice is ε-close; take tₙ ≥ max(T,n) with θDissip(u tₙ) < 1/(n+1)
(entropy dissipation + generic energy lemma); `tailSlices_subseq` extracts u t_{φ(n)} ⇉ g;
θDissip(g) = 0 (uniform-convergence integral limit + squeeze) ⟹ g ≡ u*
(`intervalDomainThetaDissipationIntegrand_eq_zero_iff` + integral positivity) ⟹ eventual slices ε-close. Contradiction.

## File plan (all NEW files; one-writer rule; cold-build clean-3 each)

Status legend: [ ] not started, [WIP], [DONE = cold-built clean-3 on uisai2].

1. [DONE] `IntervalDomainMEntropyTimeDerivative.lean` — F_m' Leibniz on intervalDomainM
   (port of the m=1 file; `chemotaxisEntropyDensity p.m`; `IntervalDomainM.timeDeriv_isGenuine`).
2. [DONE] `IntervalDomainMEntropySlopeIdentity.lean` — timeterm split (q=1, 2−2m), pde substitution,
   logistic pointwise ⟹ slope ≤ −(2m−1)u*^(2m-1)G + χ₀(2m−1)u*^(2m-1)X − b·θDissip.
3. [DONE] `IntervalDomainMEntropyStrongDissipation.lean` — Young (−2m/−m) + elliptic + A.6 + coefficient
   ⟹ `slope ≤ −strongMEntropyCoefficient · θDissip`; coefficient positivity from chiStrong1.
4. [DONE] `IntervalDomainMEntropyBasinEntry.lean` — late small-dissipation slices + AA contradiction ⟹ late supClose.
5. [ ] `IntervalDomainMEntropyStrong1Global.lean` — strong1 branch: orbit-bound restart at late slice
   ⟹ eventual C¹ + `EventuallyGloballyExponentiallyStableNonminimal intervalDomainM`.
6. [ ] strong2 branch (chiStrong2: signal floor / chiBar persistence) — analyze m=1 Strong2 chain first.
7. [ ] strong3/4 (rectangle log-gap; committed `PersistenceGeneralM*` groundwork) — port `RectangleGlobal` to M.
8. [ ] `IntervalDomainMTheorem24Eventual.lean` — headline
   `intervalDomainM_Theorem_2_4_EventualGlobalStabilityFormula (p) : Theorem_2_4_EventualGlobalStabilityFormula intervalDomainM p intervalDomainMSectorialStabilityNorms M0`, NO hm.

## Build discipline

Remote only (`rsync → uisai2:/dev/shm/lean/Shen_work-qc`, `lake build ShenWork.Paper3.<Mod>`);
`#print axioms` = `[propext, Classical.choice, Quot.sound]` per theorem; no sorry/axiom/native_decide.
