import ShenWork.Paper1.WaveLemma42ParamCore

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- The nonvacuous Route-A parameter floor: a per-step producer is required
only for frozen profiles in the monotone wave trap.

Fixed-step dependence, the uniform Rothe tail, stationarity, and the strong
maximum principle are deliberately not fields of this structure.  They remain
separate analytic hypotheses at the theorems that consume them. -/
structure PaperLowerRawRouteAParamProducerFloorOnTrap
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : Type where
  producer :
    ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperLowerRawStepProducerRouteAParamCore
        p c lam M κ κtilde D Λ hκ hM u

/-- Forget the source-box parameter layer on a trapped profile. -/
def PaperLowerRawRouteAParamProducerFloorOnTrap.toPaperProducer
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (h : PaperLowerRawRouteAParamProducerFloorOnTrap
      p c lam M κ κtilde D Λ hκ hM) :
    ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheStepProducer p c lam M κ Λ u :=
  fun u hu => paperLowerRawRouteAParamProducer (h.producer u hu)

/-- Fixed-step locally uniform dependence when the paper producer is available
only for trapped frozen profiles. -/
def PaperRotheSeqStepDependenceOnTrap
    (p : CMParams) (c lam M κ Λ : ℝ)
    (hprodTrap : ∀ v, InMonotoneWaveTrapSet κ M v →
      PaperRotheStepProducer p c lam M κ Λ v)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : Prop :=
  ∀ (seq : ℕ → ℝ → ℝ) (u : ℝ → ℝ),
    (hseq : ∀ n, InMonotoneWaveTrapSet κ M (seq n)) →
    (hu : InMonotoneWaveTrapSet κ M u) →
    LocallyUniformConverges seq u →
    ∀ k : ℕ,
      LocallyUniformConverges
        (fun n => rotheSeqOfPaper p c lam M κ Λ (seq n)
          (hprodTrap (seq n) (hseq n)) hκ hM k)
        (rotheSeqOfPaper p c lam M κ Λ u (hprodTrap u hu) hκ hM k)

/-- Uniform-in-profile convergence of the paper Rothe tail on the trapped
domain. -/
def PaperRotheTailUniformOnTrap
    (p : CMParams) (c lam M κ Λ : ℝ)
    (hprodTrap : ∀ v, InMonotoneWaveTrapSet κ M v →
      PaperRotheStepProducer p c lam M κ Λ v)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : Prop :=
  ∀ R > 0, ∀ ε > 0,
    ∃ K : ℕ, ∀ v : ℝ → ℝ,
      (hv : InMonotoneWaveTrapSet κ M v) →
      ∀ k : ℕ, K ≤ k → ∀ x ∈ Set.Icc (-R) R,
        |rotheSeqOfPaper p c lam M κ Λ v
            (hprodTrap v hv) hκ hM k x -
          rotheLimit (rotheSeqOfPaper p c lam M κ Λ v
            (hprodTrap v hv) hκ hM) x| < ε

/-- The paper implicit orbit when its producer is available only on the wave
trap.  Values outside the trap are irrelevant to the Schauder restriction, so
the upper barrier is used there, exactly as in `rotheSeqFromTrap`. -/
noncomputable def rotheSeqOfPaperFromTrap
    (p : CMParams) (c lam M κ Λ : ℝ)
    (hprodTrap : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheStepProducer p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) :
    (ℝ → ℝ) → ℕ → ℝ → ℝ :=
  fun u => by
    classical
    exact
      if hu : InMonotoneWaveTrapSet κ M u then
        rotheSeqOfPaper p c lam M κ Λ u (hprodTrap u hu) hκ hM
      else
        fun _ => upperBarrier κ M

@[simp] theorem rotheSeqOfPaperFromTrap_of_mem
    {p : CMParams} {c lam M κ Λ : ℝ}
    (hprodTrap : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheStepProducer p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    {u : ℝ → ℝ} (hu : InMonotoneWaveTrapSet κ M u) :
    rotheSeqOfPaperFromTrap p c lam M κ Λ hprodTrap hκ hM u =
      rotheSeqOfPaper p c lam M κ Λ u (hprodTrap u hu) hκ hM := by
  simp [rotheSeqOfPaperFromTrap, hu]

@[simp] theorem rotheSeqOfPaperFromTrap_of_not_mem
    {p : CMParams} {c lam M κ Λ : ℝ}
    (hprodTrap : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheStepProducer p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    {u : ℝ → ℝ} (hu : ¬ InMonotoneWaveTrapSet κ M u) :
    rotheSeqOfPaperFromTrap p c lam M κ Λ hprodTrap hκ hM u =
      fun _ => upperBarrier κ M := by
  simp [rotheSeqOfPaperFromTrap, hu]

/-- The usual paper-orbit compactness data, now from a producer quantified
only over trapped profiles. -/
theorem paperRotheOrbitData_fromTrap
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (hprodTrap : ∀ v, InMonotoneWaveTrapSet κ M v →
      PaperRotheStepProducer p c lam M κ Λ v)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hu : InMonotoneWaveTrapSet κ M u) :
    PaperRotheOrbitData p c lam M κ
      (rotheSeqOfPaperFromTrap p c lam M κ Λ hprodTrap hκ hM) u := by
  refine
    { iterate_cont := ?_
      anti_k := ?_
      anti_x := ?_
      nonneg := ?_
      le_M := ?_
      le_upperBarrier := ?_
      bddBelow := ?_
      equiLip := ?_
      limitLip := ?_ }
  · intro k
    rw [rotheSeqOfPaperFromTrap_of_mem hprodTrap hκ hM hu]
    exact rotheSeqOfPaper_cont (hprodTrap u hu) hκ hM k
  · intro x
    rw [rotheSeqOfPaperFromTrap_of_mem hprodTrap hκ hM hu]
    exact rotheSeqOfPaper_anti_k (hprodTrap u hu) hκ hM x
  · intro k
    rw [rotheSeqOfPaperFromTrap_of_mem hprodTrap hκ hM hu]
    exact rotheSeqOfPaper_anti_x (hprodTrap u hu) hκ hM k
  · intro k x
    rw [rotheSeqOfPaperFromTrap_of_mem hprodTrap hκ hM hu]
    exact rotheSeqOfPaper_nonneg (hprodTrap u hu) hκ hM k x
  · intro k x
    rw [rotheSeqOfPaperFromTrap_of_mem hprodTrap hκ hM hu]
    exact rotheSeqOfPaper_le_M (hprodTrap u hu) hκ hM k x
  · intro k x
    rw [rotheSeqOfPaperFromTrap_of_mem hprodTrap hκ hM hu]
    exact rotheSeqOfPaper_le_barrier (hprodTrap u hu) hκ hM k x
  · intro x
    rw [rotheSeqOfPaperFromTrap_of_mem hprodTrap hκ hM hu]
    exact rotheSeqOfPaper_bddBelow (hprodTrap u hu) hκ hM x
  · intro k x y
    rw [rotheSeqOfPaperFromTrap_of_mem hprodTrap hκ hM hu]
    exact rotheSeqOfPaper_equiLip (hprodTrap u hu) hκ hM
      hΛ0 hΛM hbarLip k x y
  · intro x y
    rw [rotheSeqOfPaperFromTrap_of_mem hprodTrap hκ hM hu]
    exact rotheSeqOfPaper_limitLip (hprodTrap u hu) hκ hM
      hΛ0 hΛM hbarLip x y

/-- Fixed-step dependence and a uniform Rothe tail imply continuity of the
trap-indexed paper limit map.  The two analytic inputs are direct theorem
hypotheses rather than fields hidden in the producer floor. -/
theorem paperRotheContinuousDependence_fromTrap
    {p : CMParams} {c lam M κ Λ : ℝ}
    (hprodTrap : ∀ v, InMonotoneWaveTrapSet κ M v →
      PaperRotheStepProducer p c lam M κ Λ v)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (hstep : PaperRotheSeqStepDependenceOnTrap
      p c lam M κ Λ hprodTrap hκ hM)
    (htail : PaperRotheTailUniformOnTrap
      p c lam M κ Λ hprodTrap hκ hM) :
    RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
      (rotheSeqOfPaperFromTrap p c lam M κ Λ hprodTrap hκ hM) := by
  intro seq u hseq hu hconv
  set Z : (ℝ → ℝ) → ℕ → ℝ → ℝ :=
    rotheSeqOfPaperFromTrap p c lam M κ Λ hprodTrap hκ hM with hZ
  set L : (ℝ → ℝ) → ℝ → ℝ := fun v => rotheLimit (Z v) with hL
  intro R hR ε hε
  obtain ⟨K, hK⟩ := htail R hR (ε / 3) (by linarith)
  have hstepK : LocallyUniformConverges (fun n => Z (seq n) K) (Z u K) := by
    have hstepK' := hstep seq u hseq hu hconv K
    simpa [hZ, rotheSeqOfPaperFromTrap, hseq, hu] using hstepK'
  filter_upwards [hstepK R hR (ε / 3) (by linarith)] with n hn
  intro x hx
  have htailn : |Z (seq n) K x - L (seq n) x| < ε / 3 := by
    have htailn' := hK (seq n) (hseq n) K (le_refl K) x hx
    simpa [hZ, hL, rotheSeqOfPaperFromTrap, hseq] using htailn'
  have htailu : |Z u K x - L u x| < ε / 3 := by
    have htailu' := hK u hu K (le_refl K) x hx
    simpa [hZ, hL, rotheSeqOfPaperFromTrap, hu] using htailu'
  have hmid : |Z (seq n) K x - Z u K x| < ε / 3 := hn x hx
  have hdecomp :
      L (seq n) x - L u x =
        -(Z (seq n) K x - L (seq n) x) +
          (Z (seq n) K x - Z u K x) +
          (Z u K x - L u x) := by
    ring
  calc
    |L (seq n) x - L u x| =
        |-(Z (seq n) K x - L (seq n) x) +
          (Z (seq n) K x - Z u K x) +
          (Z u K x - L u x)| := by rw [hdecomp]
    _ ≤ |-(Z (seq n) K x - L (seq n) x) +
          (Z (seq n) K x - Z u K x)| +
          |Z u K x - L u x| := abs_add_le _ _
    _ ≤ |-(Z (seq n) K x - L (seq n) x)| +
          |Z (seq n) K x - Z u K x| +
          |Z u K x - L u x| := by
        have htri := abs_add_le (-(Z (seq n) K x - L (seq n) x))
          (Z (seq n) K x - Z u K x)
        linarith
    _ = |Z (seq n) K x - L (seq n) x| +
          |Z (seq n) K x - Z u K x| +
          |Z u K x - L u x| := by rw [abs_neg]
    _ < ε := by linarith

/-- Lemma 4.2's raw lower pin is invariant under the trap-indexed paper orbit.
The per-step lower comparison data come from the existing parameter core; no
new analytic field is introduced. -/
theorem rotheSeqOfPaperFromTrap_lowerBarrierRaw_stepInvariant
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hfloor : PaperLowerRawRouteAParamProducerFloorOnTrap
      p c lam M κ κtilde D Λ hcond.hκ0.le
        (le_trans zero_le_one hcond.hM)) :
    RotheStepLowerInvariant κ M (lowerBarrierRaw κ κtilde D)
      (rotheSeqOfPaperFromTrap p c lam M κ Λ hfloor.toPaperProducer
        hcond.hκ0.le (le_trans zero_le_one hcond.hM)) := by
  refine rotheStepLowerInvariant_lowerBarrierRaw_of_paperStepData
    (lam := lam) (Λ := Λ) hcond hD hD_ge_one ?_
  intro u hu k hprev
  let core := hfloor.producer u hu.bare
  let prod := paperLowerRawRouteAParamProducer core
  have horbit :
      rotheSeqOfPaperFromTrap p c lam M κ Λ hfloor.toPaperProducer
          hcond.hκ0.le (le_trans zero_le_one hcond.hM) u =
        rotheSeqOfPaper p c lam M κ Λ u prod hcond.hκ0.le
          (le_trans zero_le_one hcond.hM) := by
    rw [rotheSeqOfPaperFromTrap_of_mem
      hfloor.toPaperProducer hcond.hκ0.le
        (le_trans zero_le_one hcond.hM) hu.bare]
  rw [horbit] at hprev
  obtain ⟨C_chem, La, Lb, haux⟩ := core.lowerRawAux hu k hprev
  refine ⟨C_chem, La, Lb, prod.hlam, ?_, ?_⟩
  · intro x
    rw [horbit]
    exact (rotheSeqOfPaper_stepFacts prod hcond.hκ0.le
      (le_trans zero_le_one hcond.hM) k).step_op x
  · rw [horbit]
    exact haux

/-- The corresponding lower bound for every iterate and its pointwise Rothe
limit. -/
theorem rotheSeqOfPaperFromTrap_lowerBarrierRaw_bound
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hfloor : PaperLowerRawRouteAParamProducerFloorOnTrap
      p c lam M κ κtilde D Λ hcond.hκ0.le
        (le_trans zero_le_one hcond.hM)) :
    RotheOrbitLowerBound κ M (lowerBarrierRaw κ κtilde D)
      (rotheSeqOfPaperFromTrap p c lam M κ Λ hfloor.toPaperProducer
        hcond.hκ0.le (le_trans zero_le_one hcond.hM)) :=
  rotheOrbitLowerBound_of_stepLowerInvariant
    (fun u hu => by
      rw [rotheSeqOfPaperFromTrap_of_mem hfloor.toPaperProducer
        hcond.hκ0.le (le_trans zero_le_one hcond.hM) hu.bare]
      exact rotheSeqOfPaper_lowerPinned_base
        (hfloor.toPaperProducer u hu.bare) hcond.hκ0.le
        (le_trans zero_le_one hcond.hM) hu)
    (rotheSeqOfPaperFromTrap_lowerBarrierRaw_stepInvariant
      hcond hD hD_ge_one hfloor)

/-- The positive-sensitivity version of the raw lower-pin invariant for the
same trap-indexed Route-A producer floor. -/
theorem rotheSeqOfPaperFromTrap_lowerBarrierRaw_positive_stepInvariant
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hfloor : PaperLowerRawRouteAParamProducerFloorOnTrap
      p c lam M κ κtilde D Λ hcond.hκ0.le
        (le_trans zero_le_one hcond.hM)) :
    RotheStepLowerInvariant κ M (lowerBarrierRaw κ κtilde D)
      (rotheSeqOfPaperFromTrap p c lam M κ Λ hfloor.toPaperProducer
        hcond.hκ0.le (le_trans zero_le_one hcond.hM)) := by
  refine rotheStepLowerInvariant_lowerBarrierRaw_of_positivePaperStepData
    (lam := lam) (Λ := Λ) hcond hD hD_ge_one ?_
  intro u hu k hprev
  let core := hfloor.producer u hu.bare
  let prod := paperLowerRawRouteAParamProducer core
  have horbit :
      rotheSeqOfPaperFromTrap p c lam M κ Λ hfloor.toPaperProducer
          hcond.hκ0.le (le_trans zero_le_one hcond.hM) u =
        rotheSeqOfPaper p c lam M κ Λ u prod hcond.hκ0.le
          (le_trans zero_le_one hcond.hM) := by
    rw [rotheSeqOfPaperFromTrap_of_mem
      hfloor.toPaperProducer hcond.hκ0.le
        (le_trans zero_le_one hcond.hM) hu.bare]
  rw [horbit] at hprev
  obtain ⟨C_chem, La, Lb, haux⟩ := core.lowerRawAux hu k hprev
  refine ⟨C_chem, La, Lb, prod.hlam, ?_, ?_⟩
  · intro x
    rw [horbit]
    exact (rotheSeqOfPaper_stepFacts prod hcond.hκ0.le
      (le_trans zero_le_one hcond.hM) k).step_op x
  · rw [horbit]
    exact haux

/-- The positive-sensitivity lower bound for every iterate and its pointwise
Rothe limit. -/
theorem rotheSeqOfPaperFromTrap_lowerBarrierRaw_positive_bound
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hfloor : PaperLowerRawRouteAParamProducerFloorOnTrap
      p c lam M κ κtilde D Λ hcond.hκ0.le
        (le_trans zero_le_one hcond.hM)) :
    RotheOrbitLowerBound κ M (lowerBarrierRaw κ κtilde D)
      (rotheSeqOfPaperFromTrap p c lam M κ Λ hfloor.toPaperProducer
        hcond.hκ0.le (le_trans zero_le_one hcond.hM)) :=
  rotheOrbitLowerBound_of_stepLowerInvariant
    (fun u hu => by
      rw [rotheSeqOfPaperFromTrap_of_mem hfloor.toPaperProducer
        hcond.hκ0.le (le_trans zero_le_one hcond.hM) hu.bare]
      exact rotheSeqOfPaper_lowerPinned_base
        (hfloor.toPaperProducer u hu.bare) hcond.hκ0.le
        (le_trans zero_le_one hcond.hM) hu)
    (rotheSeqOfPaperFromTrap_lowerBarrierRaw_positive_stepInvariant
      hcond hD hD_ge_one hfloor)

/-! ## Trap-indexed Route-A existence endpoint

The theorem below is an honest conditional endpoint: it constructs the
lower-pinned stationary wave through the existing Rothe, cube-approximation,
and Schauder assembly.  The analytic facts not yet produced by the repository
are exposed as direct hypotheses:

* fixed-step locally uniform dependence on the frozen profile;
* a uniform-in-profile tail for the discrete Rothe orbit;
* passage from a Rothe fixed point to the stationary equation;
* the stationary strong maximum principle (the existing ODE-realization route
  remains one way to produce it);
* flatness at the left endpoint for stationary lower-pinned profiles.

None of these facts is stored in the trap-indexed producer floor. -/

/-- The χ≤0 Route-A parameter core yields a paper wave once the remaining
analytic convergence and stationary frontiers are supplied on the trapped
domain. -/
theorem b1_chiNeg_existence_paper_routeA_paramCore_onTrap_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hfloor : PaperLowerRawRouteAParamProducerFloorOnTrap
      p c lam M κ κtilde D Λ hcond.hκ0.le
        (le_trans zero_le_one hcond.hM))
    (hstep :
      ∀ (seq : ℕ → ℝ → ℝ) (u : ℝ → ℝ),
        (hseq : ∀ n, InMonotoneWaveTrapSet κ M (seq n)) →
        (hu : InMonotoneWaveTrapSet κ M u) →
        LocallyUniformConverges seq u →
        ∀ k : ℕ,
          LocallyUniformConverges
            (fun n => rotheSeqOfPaper p c lam M κ Λ (seq n)
              (hfloor.toPaperProducer (seq n) (hseq n)) hcond.hκ0.le
                (le_trans zero_le_one hcond.hM) k)
            (rotheSeqOfPaper p c lam M κ Λ u
              (hfloor.toPaperProducer u hu) hcond.hκ0.le
                (le_trans zero_le_one hcond.hM) k))
    (htail :
      ∀ R > 0, ∀ ε > 0,
        ∃ K : ℕ, ∀ u : ℝ → ℝ,
          (hu : InMonotoneWaveTrapSet κ M u) →
          ∀ k : ℕ, K ≤ k → ∀ x ∈ Set.Icc (-R) R,
            |rotheSeqOfPaper p c lam M κ Λ u
                (hfloor.toPaperProducer u hu) hcond.hκ0.le
                  (le_trans zero_le_one hcond.hM) k x -
              rotheLimit (rotheSeqOfPaper p c lam M κ Λ u
                (hfloor.toPaperProducer u hu) hcond.hκ0.le
                  (le_trans zero_le_one hcond.hM)) x| < ε)
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        rotheLimit
          (rotheSeqOfPaperFromTrap p c lam M κ Λ hfloor.toPaperProducer
            hcond.hκ0.le (le_trans zero_le_one hcond.hM) U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hsmp : StationaryStrongMaxPrinciple p c κ M)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U := by
  let zseq :=
    rotheSeqOfPaperFromTrap p c lam M κ Λ hfloor.toPaperProducer
      hcond.hκ0.le (le_trans zero_le_one hcond.hM)
  have hM0 : 0 ≤ M := le_trans zero_le_one hcond.hM
  have hcpos : 0 < c := by
    rw [hcond.hc]
    have hinv : 0 < κ⁻¹ := inv_pos.mpr hcond.hκ0
    nlinarith [hcond.hκ0, hinv]
  have hdep :
      RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M) zseq := by
    simpa [zseq] using
      paperRotheContinuousDependence_fromTrap hfloor.toPaperProducer
        hcond.hκ0.le hM0 hstep htail
  have hlower :
      RotheOrbitLowerBound κ M (lowerBarrierRaw κ κtilde D) zseq := by
    simpa [zseq] using
      rotheSeqOfPaperFromTrap_lowerBarrierRaw_bound
        hcond hD hD_ge_one hfloor
  have hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheOrbitData p c lam M κ zseq u := by
    intro u hu
    simpa [zseq] using
      paperRotheOrbitData_fromTrap hfloor.toPaperProducer hcond.hκ0.le hM0
        hΛ0 hΛM hcond.upperBarrier_barLip hu
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hcond.hM
  have hgap_pos : 0 < κtilde - κ := sub_pos.mpr hcond.hgap
  have hDpos : 0 < D := D_pos_of_paperDMin_lt hcond hD
  have hExpM :
      Real.exp (-κ * lowerBarrierXPlus κ κtilde D) ≤ M :=
    lowerBarrierExpXPlus_le_one_of_one_le_D hcond.hκ0 hgap_pos
      hD_ge_one hcond.hM
  have hplat : InMonotoneWaveTrapSet κ M
      (lowerBarrierPlateau κ κtilde D) :=
    lowerBarrierPlateau_mem_InMonotoneWaveTrapSet_of_exp_xplus_le
      hcond.hκ0 hgap_pos hDpos hExpM
  have Happrox : LowerPinnedWaveCubeApproxData κ M
      (lowerBarrierRaw κ κtilde D) zseq :=
    lowerPinnedRawWaveCubeApproxData p c lam M κ κtilde D hMpos
      hcond.hκ0 hgap_pos hDpos hplat zseq (upperBarrier_isBddFun hM0)
      hdep hdata hlower
  obtain ⟨U, hU, hfix⟩ :=
    paperLowerPinnedSchauder_fixedPoint_of_cubeApproxData p c lam M κ
      (lowerBarrierRaw κ κtilde D) hM0 zseq (upperBarrier_isBddFun hM0)
      (helly_pointwise_selection M) hdep hdata hlower Happrox
  have hstat : ∀ x, frozenWaveOperator p c U U x = 0 :=
    hstationary U hU (by simpa [zseq] using hfix)
  have hnontriv : ProfileNontrivial U :=
    profileNontrivial_of_lowerBarrierRaw_tail_bound hcond hD
      (fun x _hx => hU.lower x)
  have hpos : ∀ x, 0 < U x :=
    hsmp U hU.bare hstat hnontriv
  have hlim_neg : Tendsto U atBot (𝓝 1) :=
    InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_nontrivial
      hU.bare hsmp hnontriv (hflat U hU hstat) hstat
  have hlim_pos : Tendsto U atTop (𝓝 0) :=
    hU.bare.tendsto_atTop_zero hcond.hκ0
  exact ⟨U, hU,
    FrozenStationaryWaveProfile.mk_auto_limits hcpos hpos
      hU.bare.trap.cunif_bdd hstat hlim_neg hlim_pos⟩

/-- The χ≥0 Route-A parameter core yields a paper wave under the same five
explicit analytic frontiers, with the positive-sensitivity lower comparison. -/
theorem b1_chiPos_existence_paper_routeA_paramCore_onTrap_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hfloor : PaperLowerRawRouteAParamProducerFloorOnTrap
      p c lam M κ κtilde D Λ hcond.hκ0.le
        (le_trans zero_le_one hcond.hM))
    (hstep :
      ∀ (seq : ℕ → ℝ → ℝ) (u : ℝ → ℝ),
        (hseq : ∀ n, InMonotoneWaveTrapSet κ M (seq n)) →
        (hu : InMonotoneWaveTrapSet κ M u) →
        LocallyUniformConverges seq u →
        ∀ k : ℕ,
          LocallyUniformConverges
            (fun n => rotheSeqOfPaper p c lam M κ Λ (seq n)
              (hfloor.toPaperProducer (seq n) (hseq n)) hcond.hκ0.le
                (le_trans zero_le_one hcond.hM) k)
            (rotheSeqOfPaper p c lam M κ Λ u
              (hfloor.toPaperProducer u hu) hcond.hκ0.le
                (le_trans zero_le_one hcond.hM) k))
    (htail :
      ∀ R > 0, ∀ ε > 0,
        ∃ K : ℕ, ∀ u : ℝ → ℝ,
          (hu : InMonotoneWaveTrapSet κ M u) →
          ∀ k : ℕ, K ≤ k → ∀ x ∈ Set.Icc (-R) R,
            |rotheSeqOfPaper p c lam M κ Λ u
                (hfloor.toPaperProducer u hu) hcond.hκ0.le
                  (le_trans zero_le_one hcond.hM) k x -
              rotheLimit (rotheSeqOfPaper p c lam M κ Λ u
                (hfloor.toPaperProducer u hu) hcond.hκ0.le
                  (le_trans zero_le_one hcond.hM)) x| < ε)
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        rotheLimit
          (rotheSeqOfPaperFromTrap p c lam M κ Λ hfloor.toPaperProducer
            hcond.hκ0.le (le_trans zero_le_one hcond.hM) U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hsmp : StationaryStrongMaxPrinciple p c κ M)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U := by
  let zseq :=
    rotheSeqOfPaperFromTrap p c lam M κ Λ hfloor.toPaperProducer
      hcond.hκ0.le (le_trans zero_le_one hcond.hM)
  have hM0 : 0 ≤ M := le_trans zero_le_one hcond.hM
  have hcpos : 0 < c := by
    rw [hcond.hc]
    have hinv : 0 < κ⁻¹ := inv_pos.mpr hcond.hκ0
    nlinarith [hcond.hκ0, hinv]
  have hdep :
      RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M) zseq := by
    simpa [zseq] using
      paperRotheContinuousDependence_fromTrap hfloor.toPaperProducer
        hcond.hκ0.le hM0 hstep htail
  have hlower :
      RotheOrbitLowerBound κ M (lowerBarrierRaw κ κtilde D) zseq := by
    simpa [zseq] using
      rotheSeqOfPaperFromTrap_lowerBarrierRaw_positive_bound
        hcond hD hD_ge_one hfloor
  have hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheOrbitData p c lam M κ zseq u := by
    intro u hu
    simpa [zseq] using
      paperRotheOrbitData_fromTrap hfloor.toPaperProducer hcond.hκ0.le hM0
        hΛ0 hΛM hcond.upperBarrier_barLip hu
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hcond.hM
  have hgap_pos : 0 < κtilde - κ := sub_pos.mpr hcond.hgap
  have hDpos : 0 < D := D_pos_of_positive_paperDMin_lt hcond hD
  have hExpM :
      Real.exp (-κ * lowerBarrierXPlus κ κtilde D) ≤ M :=
    lowerBarrierExpXPlus_le_one_of_one_le_D hcond.hκ0 hgap_pos
      hD_ge_one hcond.hM
  have hplat : InMonotoneWaveTrapSet κ M
      (lowerBarrierPlateau κ κtilde D) :=
    lowerBarrierPlateau_mem_InMonotoneWaveTrapSet_of_exp_xplus_le
      hcond.hκ0 hgap_pos hDpos hExpM
  have Happrox : LowerPinnedWaveCubeApproxData κ M
      (lowerBarrierRaw κ κtilde D) zseq :=
    lowerPinnedRawWaveCubeApproxData p c lam M κ κtilde D hMpos
      hcond.hκ0 hgap_pos hDpos hplat zseq (upperBarrier_isBddFun hM0)
      hdep hdata hlower
  obtain ⟨U, hU, hfix⟩ :=
    paperLowerPinnedSchauder_fixedPoint_of_cubeApproxData p c lam M κ
      (lowerBarrierRaw κ κtilde D) hM0 zseq (upperBarrier_isBddFun hM0)
      (helly_pointwise_selection M) hdep hdata hlower Happrox
  have hstat : ∀ x, frozenWaveOperator p c U U x = 0 :=
    hstationary U hU (by simpa [zseq] using hfix)
  have hnontriv : ProfileNontrivial U :=
    profileNontrivial_of_lowerBarrierRaw_positive_tail_bound hcond hD
      (fun x _hx => hU.lower x)
  have hpos : ∀ x, 0 < U x :=
    hsmp U hU.bare hstat hnontriv
  have hlim_neg : Tendsto U atBot (𝓝 1) :=
    InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_nontrivial
      hU.bare hsmp hnontriv (hflat U hU hstat) hstat
  have hlim_pos : Tendsto U atTop (𝓝 0) :=
    hU.bare.tendsto_atTop_zero hcond.hκ0
  exact ⟨U, hU,
    FrozenStationaryWaveProfile.mk_auto_limits hcpos hpos
      hU.bare.trap.cunif_bdd hstat hlim_neg hlim_pos⟩

/-! This sanity theorem checks that the counterexample which refuted the old
all-profile floor is outside the quantified domain of the new floor. -/

theorem exists_mem_monotoneWaveTrap (κ M : ℝ) (hM : 0 ≤ M) :
    ∃ u, InMonotoneWaveTrapSet κ M u :=
  ⟨fun _ => 0, InMonotoneWaveTrapSet.zero hM⟩

theorem negative_one_not_mem_monotoneWaveTrap
    (κ M : ℝ) :
    ¬ InMonotoneWaveTrapSet κ M (fun _ : ℝ => (-1 : ℝ)) := by
  intro hu
  have hnonneg := hu.nonneg 0
  norm_num at hnonneg

section AxiomAudit

#print axioms PaperLowerRawRouteAParamProducerFloorOnTrap.toPaperProducer
#print axioms PaperRotheSeqStepDependenceOnTrap
#print axioms PaperRotheTailUniformOnTrap
#print axioms rotheSeqOfPaperFromTrap_of_mem
#print axioms paperRotheOrbitData_fromTrap
#print axioms paperRotheContinuousDependence_fromTrap
#print axioms rotheSeqOfPaperFromTrap_lowerBarrierRaw_stepInvariant
#print axioms rotheSeqOfPaperFromTrap_lowerBarrierRaw_bound
#print axioms rotheSeqOfPaperFromTrap_lowerBarrierRaw_positive_stepInvariant
#print axioms rotheSeqOfPaperFromTrap_lowerBarrierRaw_positive_bound
#print axioms b1_chiNeg_existence_paper_routeA_paramCore_onTrap_of_cubeApproxData
#print axioms b1_chiPos_existence_paper_routeA_paramCore_onTrap_of_cubeApproxData
#print axioms exists_mem_monotoneWaveTrap
#print axioms negative_one_not_mem_monotoneWaveTrap

end AxiomAudit

end ShenWork.Paper1
