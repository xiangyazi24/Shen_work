# Shen Paper 1 — War Map (live headline floor-collapse)

Mode: **Blind Formalization** (agent owns the math end-to-end; user does not read PDE detail).
Judgment authority on faithfulness = agent, via 回归原著 (read paper1.pdf), not asking the user.

## Target (live headline)
`b1_chiNeg_existence_paper_clean_of_cubeApproxData` (WaveLemma42G1Discharge.lean) — χ≤0 traveling-wave
existence on the lower-pinned trap. The DIVERGENCE-form `b1_..._final/unconditional` (requires the FALSE
`Antitone R`) is LEGACY — NOT the live path. Live path = paper-expanded + cube-G1.

Faithfulness fact (settled from paper1.pdf): m,α,γ ≥ 1 **REAL** (not integers). CMParams(ℝ) faithful;
ℕ-exponent TravelingWaveODE route is an over-restriction → hrealize/hsmp must be proven DIRECTLY for real exp.

## Floor status (the headline's conditional inputs)

| Floor | Meaning | Status | Commit / line |
|---|---|---|---|
| G1 (hprinciple) | Schauder/Brouwer | ✅ cube route (unconditional, prior) | WaveLemma42G1Discharge |
| hflat | FrozenStationaryFlatAtLeft (U'→0,U''→0,flux'→0 at −∞) | ✅ DONE from trap+C³ | 5febb74 (stationaryCrossGreenData_of_trap) |
| hflat bridge | frozenWaveOp U U=0 ⟹ crossImplicitMap-fixed + Barbalat | ✅ DONE | 6955957 |
| hprodAll wiring | RouteA producer → PaperLowerRawStepProducer | ✅ DONE | b961f2b |
| hprodAll green-core | trap → PaperGreenStepInputRouteACore | ✅ assembly | 614b824 |
| hprodAll Banach machinery | crossImplicitStep_exists_unique wired + K<1 proven | ✅ DONE | f1c3aa5 |
| hprodAll per-step Schauder machinery | of_schauder constructs existence from principle+map data, compactness PROVEN, of_banach deleted | ✅ DONE | f076c50 |
| **hprodAll Schauder map data** | PaperStepSchauderMapData_of_trap; mapsTo (=faithfulness-audit's biggest content) via SUPER-SOLUTION COMPARISON not source-monotonicity (reaction non-monotone); ChatGPT consulting precise resolvent-comparison | 🔥 cx_pde mapsTo-super | /tmp/shen_pde_mapsto_super.md |
| hstationary | rotheLimit fixed ⟹ frozenWaveOp U U=0 | ✅ assembled, modulo uniform-bounds | 26cbe80 |
| hstationary uniform-bounds | PaperC2CompactUniformBounds from concrete green-core | ⬜ coupled to hpoint landing | — |
| hsmp / hrealize | §2.6b RESOLVED: stationaryStrongMaxPrinciple_of_rotheLimit_greenRepresentation — Green-rep THREADED from Rothe limit (hthread = construction input), DCT+limit-deriv proven, cron2-confirmed non-circular | ✅ DONE | df65097 |
| hstep / htail | PaperRotheSeqStepDependence / PaperRotheTailUniform | ⬜ gap mapped (clamp + step-layer K<1), secondary | — |
| hlim_neg | left limit=1 via monotone-limit + equilibrium L(1-L^α)=0 + lower-pin | 🔥 cx_r3 | /tmp/shen_r3_hlimneg.md |
| hcond/hD/hbarLip/scalars | concrete parameter conditions | ⬜ concrete, easy | — |

## Dependency (ASCII)
```
headline ─┬─ G1 ✅
          ├─ hflat ✅
          ├─ hprodAll ← [wiring✅ + green-core✅ + Banach-machinery✅ + hpoint🔥]
          ├─ hstationary ✅(← uniform-bounds⬜ ← concrete green-core after hpoint)
          ├─ hsmp/hrealize 🔥 (direct real-exp Hopf)
          ├─ hstep/htail ⬜ (secondary)
          └─ hcond/hD/scalars ⬜ (concrete)
```

## Workers
- cx_pde (/var/tmp/shen_cx_pde): WavePaperRouteA / WavePaperRotheProducer — hpoint now.
- cx_r3 (/var/tmp/shen_cx_r3): WaveTrapProps / WaveRotheStationary / StationaryFloor / TermConvergence — smp now.
- DISJOINT files. Sync repo HEAD → codex dir before any shared-file dispatch (dir-drift clobbered once, git-diff caught it).
- ac_cx_a3model (~/repos/AC-clone) is NOT ours.

## Discipline notes (this campaign)
- §2.2: count real sorry with proof-position regex, NOT `\bsorry\b` (Paper-2 false "9 sorries" was docstrings).
- §3.3: verify "Exists" is CONSTRUCTED not carried (caught cx_pde "no residual" overclaim — hpoint was carried).
- Deletion check: `git diff <commit>^ <commit>`, authoritative (comm/grep false-positived ≥2×).
- Hard analysis (max principle, mollify, tail decay, Banach contraction structure) DONE many commits ago;
  this phase is floor-collapse + reuse-existing-infra (WaveRotheStep Banach, WaveRotheTrunc clamp).
