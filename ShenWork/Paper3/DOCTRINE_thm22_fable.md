# DOCTRINE — general-m Theorem 2.2 headline (Fable#3)

Target: `Theorem_2_2_EventualExponentialStability intervalDomainM p unitIntervalNeumannSpectrum
intervalDomainMSectorialStabilityNorms (intervalDomainMSectorialPaper3Constants p M0 uBar vLower)`
with hypotheses exactly `(p : CM2Params) (M0 uBar vLower : ℝ)` — NO `hm : p.m = 1`.

m=1 model: `intervalDomain_Theorem_2_2_Eventual_concrete_unconditional`
(IntervalDomainMinimalFaithfulTheorem22.lean). Four branches:
(1) a>0,b>0 stable, (2) a>0,b>0 unstable [spectral only], (3) a=0,b=0 minimal stable
[mass-constrained], (4) minimal unstable [spectral only]. Mixed sign slices vacuous.

## Honest-smallness checkpoint (P*M ≤ 1)
Codex Route-A power factor `P = max 1 Lip_m` lives inside the WIP nonlinear-L2 /
smoothing files (weak restart window machinery). The headline shape is a LOCAL
stability statement: `∃ δ > 0 …` — δ is existential in the conclusion, exactly the
paper's Theorem 2.2 ("initial data sufficiently close"). The local smallness
threshold (P*M≤1-type conditions folded into basin delta / bootstrap radius
definitions like `paper3WeakSupBasinDeltaGeneralM`, `intervalDomainStrongBootstrapRadiusGeneralM`)
is DISCHARGED by choosing δ small, not carried as hypothesis. Verify at close: headline
carries zero side conditions beyond `p`.

## Inventory (checked, all clean-3 on main 8c47893d)

### Already proved, general-m, positive branch (a>0)
- basin entry unconditional: `intervalDomainMSupToStrongBasinEntry_proved (p)` (WIP BasinEntry)
- finite-horizon basin entry: `intervalDomainMSupToStrongBasinEntry_of_contraction_of_solution`
  (needs T-window + contraction hyps + 5T/4 < H)
- orbit bound from entry: `intervalDomainM_weakSupEventualSpectralSemigroupOrbitBound_of_basinEntry`
  (StageBGeneralM) → `IntervalDomainMWeakSupEventualSpectralSemigroupOrbitBound p` (needs 0<p.a inside)
- finite strong bootstrap: `intervalDomainX2SigmaDistance_restart_exponential_bound_before_generalM`
  (FiniteStrongBootstrapGeneralM)
- strip lemmas: `paper3SupClose_initial_positiveStrip_generalM`,
  `intervalDomainStrongBootstrapRadiusGeneralM_positiveStrip` (WIP MStrongPositiveStrip; strip lemma needs NO hgap)
- contraction window: `exists_intervalDomainMWeakSupContractionWindow_lt` (MWeakSupBootstrap)
- local existence factory (ALL exponents!): `intervalDomainM_thresholdLocalExistence_positiveStrip_allExponents`
  (Paper2/IntervalDomainMLocalExistenceAllExponents) — takes Continuous w + |w|≤M + c≤w
- continuation framework M (Paper2):
  - `ReachableClassicalHorizonM/ReachablePastM/finiteMaximalReachableHorizonM` etc. (MReachability/MBoundedReachability)
  - `reachablePastM_of_bounded_and_uniform_floor` (MMaximalContinuationAlternative) — all m>0,
    does the glue internally (piecewiseClassicalWorksM/timeShiftM inside)
  - `intervalMClassicalSolutionOverlapUniqueAt_of_paperPositive`
  - `realize_at_finiteMaximalReachableHorizonM_of_overlapUnique` (glued sol at max horizon)
  - `globalSolutionM_of_reachableArbitrarilyLong_of_overlapUniqueAt`
- initial-trace pointwise: `intervalDomainM_initialTrace_pointwise_abs_lt_of_classical` (MClassicalInitialOverlap)
- slice bounds: `solution_slice_abs_bddAbove` (MMass), `u_pos` (MLpTimeLeibniz),
  `solutionSlice_continuous` (MPhysicalRestart), `solution_lift_continuousOn_Icc`
- joint continuity: conjunct in classicalRegularity — projection `hsol.2.1.…` same as
  `intervalDomain_solution_jointContinuousOn` (P3MoserEnergyContinuity); M wrapper needed.
- constants/norms/sup-control: IntervalDomainMSectorial.lean (tracked) —
  `intervalDomainMSectorialPaper3Constants(_usesCriticalSpectrum)`, `intervalDomainMSectorialStabilityNorms(_supControlsXpSigmaDistance)`
- spectral gap from stability (a>0): `unitIntervalLinearSpectralGap_of_linearlyStable_of_a_pos` (domain-free)

### Missing (my build list)
- **File A `IntervalDomainMSmallDataGlobalExistence.lean`** (positive branch, a>0):
  1. `intervalDomainM_solution_jointContinuousOn` (projection wrapper)
  2. early-window strip: (0,tmid] bound+floor from datum strip + trace pointwise + compact slab
  3. `paper3_reachablePastM_of_finite_stable_bootstrap` — route: bounded+floor on (0,H)
     [(0,eta) trace / [a,tmid] slab / [T,H) strong ball] → `reachablePastM_of_bounded_and_uniform_floor`
     (NO manual gluing — simpler than m=1 template)
  4. `intervalDomainM_smallDataGlobalExistence_of_linearlyStable (p) (ha:0<p.a) (heq) (hstable) :
     ∃ delta>0, SmallDataGlobalExistence intervalDomainM p uStar delta`
     — m=1 template §539, with realize_at_finiteMaximalReachableHorizonM instead of manual glue.
- **File B `IntervalDomainMWeakSupStageB.lean`** (positive branch assembly):
  - `intervalDomainM_weakSupEventualSpectralSemigroupOrbitBound (p)` := StageB ∘ basinEntry_proved (NO hm!)
  - `intervalDomainM_eventualLocallyExponentiallyStableFromSup_unconditional (p) (ha) (heq) (hstable)`
    := orbit bound + File A existence (min of two deltas)
- **File C `IntervalDomainMFaithfulTheorem22.lean`** (positive-logistic headline):
  m=1 template IntervalDomainFaithfulTheorem22.lean, s/intervalDomain/intervalDomainM/,
  s/intervalDomainSectorialStabilityNorms/intervalDomainMSectorialStabilityNorms/, drop hm.
- **Minimal branch (a=0,b=0) — second battlefield** (m=1 chain to mirror):
  - mass conservation M: `intervalDomain_minimal_mass_eq_initial_before` analog
    (Neumann flux of u^m still integrates to 0; check IntervalDomainMMass.lean for existing mass lemmas)
  - mass-gap basin entry / bootstrap M: m=1 files IntervalDomainMinimal{WeakSupBasinEntry,FiniteStrongBootstrap,EventualConvergenceUpgrade,SmallDataGlobalExistence}; general-m
    analogs needed on top of the Codex weak-window machinery (mass-projected decay,
    `UnitIntervalLinearMassSpectralGap` is spectral/domain-free).
  - `intervalDomainM_eventualMassConstrainedLocallyExponentiallyStableFromSup_unconditional`
- **File Z `IntervalDomainMMinimalFaithfulTheorem22.lean`**: four-branch join = HEADLINE.

## Build discipline
- Remote only: rsync → uisai2:/dev/shm/lean/Shen_work-qc, `lake build ShenWork.<mod>`,
  per-file #print axioms in-file; clean-3 = [propext, Classical.choice, Quot.sound].
- New files only; never edit the 4 Codex WIP (now tracked @ 8c47893d) or Fable#2's Paper1 domain.

## Log
- 2026-07-16: WIP cluster cold-verified green (8861 jobs) + clean-3; checkpoint 8c47893d pushed by coordinator. DAG mapped (above). Starting File A.
- 2026-07-16 (same session): **HEADLINE CLOSED.** All 8 new files green + clean-3:
  - A `IntervalDomainMSmallDataGlobalExistence.lean` — positive-branch existence
    (`intervalDomainM_smallDataGlobalExistence_of_linearlyStable`); route =
    bounded+floor continuation (no manual gluing), early-window strip lemma new.
  - B `IntervalDomainMWeakSupStageB.lean` — orbit bound unconditional + eventual stability.
  - C `IntervalDomainMFaithfulTheorem22.lean` — positive-logistic four-branch capstone.
  - D `IntervalDomainMinimalStrongDuhamelGeneralM.lean` — mass Duhamel chain generalM
    (zero-mode of physical mass, integrand integrable, restart eq, quadratic, actual,
    L2-restart core).
  - E `IntervalDomainMinimalStrongBootstrapGeneralM.lean` — mass Stage-A bootstrap,
    finite `_before` + global, of_small/of_radius_le/public.
  - F `IntervalDomainMMinimalWeakSupBasinEntry.lean` — mass smoothing at window target,
    basin delta `_of_gap_pos` variants, finite + global mass basin entry.
  - G `IntervalDomainMMinimalSmallDataGlobalExistence.lean` — general-m mass conservation
    (mass ODE, no hm!), mass reachablePast, mass-constrained global existence
    (constant-equilibrium extension trick after Hmax mirrors m=1).
  - Z `IntervalDomainMMinimalFaithfulTheorem22.lean` — mass eventual stability +
    four-branch join. **HEADLINE: `intervalDomainM_Theorem_2_2_Eventual_concrete_unconditional
    (p : CM2Params) (M0 uBar vLower : ℝ)`** — zero hm, zero smallness, clean-3.
  Root gate (full lake build): all targets green EXCEPT `ShenWork.Paper1.Proposition12Assembly`
  — a PRE-EXISTING breakage on canonical main 8c47893d (type mismatch at :36:46 from the
  86cf883e datum-seam commit vs its NegativeBranch dependency), pure Paper1 import chain,
  independent of every Paper3 file (nothing imports my new files; Proposition12Assembly
  imports only Paper1). Paper1 = Fable#2's domain, not touched per orders.
  Honest-smallness audit: δ existential in conclusion (= paper's local stability);
  Route-A P*M≤1 thresholds live inside discharged basin-delta/bootstrap-radius defs.
