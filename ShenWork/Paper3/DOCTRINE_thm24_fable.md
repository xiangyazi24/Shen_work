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
5. [DONE] `IntervalDomainMEntropyStrong1Global.lean` — strong1 branch: orbit-bound restart at late slice
   ⟹ eventual C¹ + `EventuallyGloballyExponentiallyStableNonminimal intervalDomainM`.
6. [DONE] `IntervalDomainMEntropyStrong2Global.lean` — strong2: m=1 reverse bridge + legacy persistence;
   m>1 faithful Thm 2.1(3) floor with strict-threshold slack (floor slightly below vAB keeps coefficient positive).
7. [WIP] strong3/4 rectangle port to intervalDomainM.  Port map (m=1 sources → new M files):
   - The m=1 rectangle chain has NO hm hypotheses because the legacy domain hardcodes the m=1 flux;
     the port re-derives extremum slope bounds for the u^m flux.  KEY MATH: at a spatial max/min the
     flux divergence (u^m φ v_x)_x = u^m (φ v_x)_x + m u^{m-1} u_x φ v_x and u_x = 0 at interior
     extrema AND at Neumann endpoints, so only the factor u^{m-1} (= U^{m-1} at the argmax) threads
     through; chiStrong3Formula's u*^{m+γ-1} (vs u*^γ at m=1) already reflects it.  The extra
     X^{m-1} (X := U/u* ≥ 1) is absorbed by the scalar gap lemma
     X^b (X^a − Y^a) ≤ X^{a+b} − Y^{a+b} (for X ≥ 1 ≥ Y > 0; proof: difference = Y^a(X^b − Y^b) ≥ 0),
     consistent with the strengthened branch-3/4 exponent conditions α+1 ≥ m+γ+(β≠0)γ / α+1 ≥ m+2γ.
   - `IntervalDomainRectangleSignalBounds.lean` (197) → M version (v-equation identical; only the
     solution-predicate type changes).
   - `IntervalDomainRectangleInteriorSlopes.lean` (420) + `IntervalDomainRectangleBoundarySlopes.lean`
     (894) + `IntervalDomainRectangleExtremumSlopes.lean` (238) → M versions with the u^m flux
     (`intervalDomain_rectangle_max_slope_of_argmax` analogue: u_t ≤ U(a − bU^α + χ₀ U^{m-1}(ν(U^γ−L^γ)
     + β(Cν(U^γ−L^γ))²)) at the clamped max; dual for the min).
   - `IntervalDomainRectangleLogGap.lean` (1398): choice-space/Dini layer is PDE-light; port the
     hsol-taking lemmas (clampedLower_pos, choiceValue_mem_clamped, clampedUpper/Lower_logSlope, the
     `_with_weight` variants) to M; scalar lemmas reusable as-is.
   - `IntervalDomainRectangleGlobal.lean` (1103): strong3/4 decay coefficient + Dini contraction +
     logGap→sup conversion; port the hsol/orbit lemmas; scalar layer reusable.
   - χ₀ ≤ 0 sub-case of branches 3/4: m=1 used `intervalDomain_chiNonpos_uniform_u_converges`
     (`NegativeSensitivityMass{Floor,Convergence}` + `MaxDecay` chain, m=1-gated) — needs a general-m
     analogue on intervalDomainM (mass floor + max decay for u^m flux), OR reuse of the m>1 faithful
     persistence + a repulsive-entropy argument.  NOT yet scoped in detail.
   - Stage-B/eventual-C¹ part of branches 3/4 is DONE: from
     `GloballyAsymptoticallyStableNonminimal intervalDomainM` late supClose is immediate and
     `intervalDomainM_eventualC1_of_lateSupClose` applies.
8. [DONE scaffold] `IntervalDomainMTheorem24Eventual.lean` —
   `intervalDomainM_Theorem_2_4_EventualGlobalStabilityFormula_of_rectangle_frontiers`: the full
   four-branch headline with branches 1–2 discharged unconditionally and branches 3–4 as named
   frontier hypotheses (repo `of_frontiers` idiom).  Final headline = apply it to the two rectangle
   producers once file-7 lands; keep the name
   `intervalDomainM_Theorem_2_4_EventualGlobalStabilityFormula` for that final theorem
   `intervalDomainM_Theorem_2_4_EventualGlobalStabilityFormula (p) : Theorem_2_4_EventualGlobalStabilityFormula intervalDomainM p intervalDomainMSectorialStabilityNorms M0`, NO hm.

## Build discipline

Remote only (`rsync → uisai2:/dev/shm/lean/Shen_work-qc`, `lake build ShenWork.Paper3.<Mod>`);
`#print axioms` = `[propext, Classical.choice, Quot.sound]` per theorem; no sorry/axiom/native_decide.

## [2026-07-16 主循环补充] rectangle 港配方(已验证,Fable 17:10 照此快推)

Fable 系被 429 卡到 17:10 期间,主循环把 rectangle 港路端到端验通。三件已验 green:
- `IntervalDomainMRectangleInteriorSlopes.lean` — clean-3(4 slope 定理)。
- `IntervalDomainMRectangleSignalBounds.lean` — green。
- `IntervalDomainMRectangleBoundarySlopes.lean` — **`boundary_left_balance` 已写并 build green**(crux)。

**精确港配方(每个 m=1 rectangle 文件照此改)**:
1. **open 头**(关键,少了 `boundaryChemDivMReal` 会解析成 sorry):
   `open Set Filter Topology` / `open ShenWork.IntervalDomain ShenWork.PDE ShenWork.Paper2` /
   `open ShenWork.MinPersistenceAtoms ShenWork.MaxPrincipleAtoms` /
   `open ShenWork.Paper2.IntervalDomainMMinPersistence`
2. `IsPaper2ClassicalSolution intervalDomain` → `intervalDomainM`;PDE 里 `intervalDomain.timeDeriv/laplacian/chemotaxisDiv` → `intervalDomainM.*`(**timeDeriv 也要 M**,否则 rw 找不到)。
3. **内部极值点**:用 `chemDivM_at_critical`(需 `deriv U x=0`)把 `intervalDomainChemotaxisDivM` 分解成 `U^m·coeff`;scalar flux-coeff 引理已在 InteriorSlopes M 里(`rectangleM_fluxCoefficient_{lower,upper}_of_weight`)。
4. **端点(Neumann)**:`Cfun := boundaryChemDivMReal p (u t)(v t)`;`echem` 用 `show intervalDomainChemotaxisDivM ... xp = boundaryChemDivMReal ... x; unfold boundaryChemDivMReal; rw [dif_pos (Ioo_subset_Icc_self hx)]`。**精确端点极限**不要用 `boundaryChemDivM_left_limit_factor`(那个 g 是存在量词、只给 bound);要用 `classicalChemDivMPhysicalRep_continuousOn_Icc`(连续性)+ `boundaryChemDivMReal_eq_physicalRep_eventually`(近端点相等)+ 端点值 `classicalChemDivMPhysicalRep ... 0` 用 `deriv U 0=deriv V 0=0`(`hClosed.1.2.1`/`.2.2.1`)simp+ring 算出 = `CL = U0^m·(1+V0)^{-β}(μV0−νU0^γ)`。右端点对称(端点 1,`derivWithin_right_zero`,`nhdsWithin 1 (Iio 1)`)。
5. **conclusion prefactor** `χ₀·U·(...)` → `χ₀·U^m·(...)`;r-limit 符号引理 `Lemma31Closure.boundary_max_deriv2_rlimit_nonpos` / `boundary_min_deriv2_rlimit_nonneg` 原样复用(和 m=1 同)。
6. 剩余文件序:BoundarySlopes(right_balance + 8 wrapper)→ ExtremumSlopes(纯 dispatcher,拆 interior/left/right)→ LogGap(PDE-light,port hsol-taking 引理,scalar 层原样)→ Global(decay coeff + Dini + logGap→sup)→ χ₀≤0 子情形(需 general-m mass floor + max decay,未 scope)。

## [2026-07-16 Fable fork] rectangle LogGap+Global port DONE — Thm 2.4 general-m headline landed

- `IntervalDomainMRectangleLogGap.lean` — DONE clean-3. Reuses the domain-free clamped/choice defs from the m=1 file; 6 new M log-slope-bound defs carry the `U^(m-1)`/`L^(m-1)` chemotaxis prefactor; all ~28 hsol-lemmas ported (regularity-only ones byte-identical at `intervalDomainM`, the clampedUpper/Lower_logSlope + dini chain reshaped via `U^p.m = U·U^(p.m-1)`).
- `IntervalDomainMRectangleGlobal.lean` — DONE clean-3. Core m>1 math: `rpow_mul_gap_le_gap_add` (X^s(X^a−Y^a) ≤ X^(a+s)−Y^(a+s), X≥1≥Y>0) absorbs the extra `U^(m-1)`/`L^(m-1)` into a single α-gap; `intervalDomainM_strong3_decayCoefficient_pos_of_chi` uses `u*^(m+γ-1)`; `_le_strong3` combines Term1 (Gγ(X^(m-1)+Y^(m-1)) ≤ 2G_{m+γ-1} ≤ 2Gα, needs α+1≥m+γ) and Term2 (X^(m-1)Gγ² ≤ G_{2γ+m-1} ≤ Gα, needs α+1≥m+2γ for β≠0; Term2=0 for β=0). Structural antitone/tendsto/envelope/uniformConverges ported. strong4 uses a continuity-slack floor (floor<vABLower reached by faithful Thm 2.1(3), χ₀(1+floor)^(-β)<chiStrong3 by openness) + the M signal floor.
- Final headline: `intervalDomainM_Theorem_2_4_EventualGlobalStabilityFormula (p) (hchiNonpos) : Theorem_2_4_EventualGlobalStabilityFormula intervalDomainM p intervalDomainMSectorialStabilityNorms (unitIntervalNormalizedResolverGradientConstant p)`, #print axioms = [propext, Classical.choice, Quot.sound]. NO p.m=1. Branches 1–2 (entropy) + branches 3–4 for χ₀>0 fully unconditional.
- SCOPED FRONTIER (honest, not faked): the χ₀≤0 neutral/repulsive sub-case of the rectangle branches enters as the single hypothesis `hchiNonpos : ∀ ha hb, χ₀≤0 → GloballyAsymptoticallyStableNonminimal intervalDomainM p eq.1 eq.2`. Its faithful general-m proof needs the mass-floor (`NegativeSensitivityMassFloor`) + max-decay (`NegativeSensitivityMaxDecay`) chain rebuilt for the u^m flux — all m=1-gated today; the general-m mass ODE exists (`Paper2/IntervalDomainMMass.mass_derivative_eq_logistic`, chemotaxis drops at exponent 1 for any m) and the AA infra (`intervalDomainM_globalBounded_tailSlices_subseq`) can replace the m=1 Lipschitz static step, but it is net-new multi-lemma infrastructure, not a mechanical port.
