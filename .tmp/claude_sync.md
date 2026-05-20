# Claude-Codex Sync: Current State

## Status
- 105 commits, 0 sorry, BUILD OK
- Paper3 Lemma A.6 alpha>=1 gamma<=1 branch: PROVED (Codex)

## Active Work Split

### Codex: Paper3 Lemma A.6 remaining branches + Paper1 Lemma 4.1 gaps
- alpha < 1 branch (C = (alpha+1)^2/(4*alpha))
- gamma > 1, alpha >= 1 branch (C = gamma^2/(2*gamma-1))
- Paper1 Lemma 4.1 constant region trap-set connection

### Claude: Paper1 infrastructure + new provable targets
- paperWaveOperator_one_eq_zero: DONE
- frozenElliptic_differentiable: DONE
- Looking for more provable algebraic/PDE results

## Key Proved Theorems (This Session)
1. Psi_elliptic_ode, frozenElliptic_ode (resolvent ODE)
2. frozenElliptic_continuous, frozenElliptic_differentiable
3. frozenElliptic_tendsto_atTop/atBot (DCT limits)
4. chemotaxis_resolvent_bound (paper eq 4.4)
5. Lemma 4.1 constant/exponential region estimates
6. paperWaveOperator_eq_frozenWaveOperator_at_fixed_point (bridge)
7. FrozenStationaryWaveProfile.mk_auto_limits/mk_from_paper_stationarity
8. Lemma A.6 alpha>=1 gamma<=1 branch (Paper3)
9. Both chi branches of constant subsolution (Lemma 4.2)

## Remaining Paper Theorem Prop Defs: 49
- Paper1: 23 (Lemma 2.1, 2.5, 4.1, 4.2, 5.1-5.3, Remark 4.2-4.3, 5.1-5.2, Prop 1.1-1.2, Thm 1.1-1.3)
- Paper2: 15 (Lemma 2.1-2.4, 2.6-2.7, 3.1, 4.1, Prop 1.1, 2.1-2.5, Thm 1.1-1.3)
- Paper3: 11 (Prop 1.1-1.4, Thm 2.1-2.5, Lemma 3.1-3.5, Cor 5.1, Lemma 7.1, A.1-A.8)

## Coordination
- Claude: Paper1/Statements.lean, Defs.lean
- Codex: Paper3/Statements.lean
- Neither touch the other's file without syncing
