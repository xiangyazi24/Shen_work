import ShenWork.Paper1.WavePaperRouteA

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- Turn one Route-A Green output into the ordinary paper-step facts without
forgetting where the output came from.  This is the shared assembly used by the
analytic-preserving Rothe recursion below. -/
def paperRotheStepFacts_of_routeA_output
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z W : ℝ → ℝ}
    (hin : PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u)
    (hout : PaperStepOutputRouteACore p c lam M κ Λ u Z W) :
    PaperRotheStepFacts p c lam M κ Λ u Z W := by
  have hstep : ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x :=
    smooth_paperStep_step_op_of_core hin.hlam hout.analytic
  have hbasic :
      Continuous W ∧ Differentiable ℝ W ∧ ∀ x, |deriv W x| ≤ Λ :=
    smooth_paperStep_basic_regular_of_core hin.hlam hout.analytic
  have hnonneg : ∀ x, 0 ≤ W x := by
    have hle := paperStep_ge_lower
      (c := c) (lam := lam) hin.hlam hstep hout.lowerZero
    intro x
    exact hle x
  have hle_old : ∀ x, W x ≤ Z x :=
    paperStep_le_upper (c := c) (lam := lam) hin.hlam hstep hout.upperOld
  have hle_barrier : ∀ x, W x ≤ upperBarrier κ M x :=
    paperStep_le_upper
      (c := c) (lam := lam) hin.hlam hstep hout.upperBarrier
  exact
    { step_op := hstep
      cont := hbasic.1
      diff := hbasic.2.1
      contDiff2 := paperStep_contDiff_two_of_core hin.hlam hout.analytic
      deriv_le := hbasic.2.2
      nonneg := hnonneg
      le_barrier := hle_barrier
      le_old := hle_old
      anti := paperStep_antitone_of_trap_via_mollification hin.hlam hout.approx
      paperSuper :=
        paperWaveOperator_nonpos_of_implicitStep_le
          (p := p) (c := c) (lam := lam) hin.hlam hstep hle_old }

/-- Route-A Rothe recursion which retains the concrete Green output selected at
every successor.  The older `rotheSeqOfPaper` deliberately erased this payload;
this recursion is extensionally the same construction pattern but exposes the
source needed by the moving-index closed graph. -/
def paperRouteARotheStep
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ)
    (hin : PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) :
    ∀ _k : ℕ, {Z : ℝ → ℝ // PaperIterateBase p c κ M u Z}
  | 0 =>
      ⟨upperBarrier κ M,
        upperBarrier_paperIterateBase hκ hM hin.basePaperSuper⟩
  | k + 1 =>
      let prev := paperRouteARotheStep p c lam M κ Λ u hin hκ hM k
      let out := hin.produce_regular prev.1 prev.2
      ⟨out.1,
        (paperRotheStepFacts_of_routeA_output hin out.2).toBase⟩

/-- The Route-A paper orbit with its Green source selection retained. -/
def rotheSeqOfPaperRouteA
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ)
    (hin : PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : ℕ → ℝ → ℝ :=
  fun k => (paperRouteARotheStep p c lam M κ Λ u hin hκ hM k).1

/-- Totalize a trap-indexed Route-A Green orbit by the upper barrier outside
the Schauder domain. -/
def rotheSeqOfPaperRouteAFromTrap
    (p : CMParams) (c lam M κ Λ : ℝ)
    (hinput : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : (ℝ → ℝ) → ℕ → ℝ → ℝ :=
  fun u => by
    classical
    exact if hu : InMonotoneWaveTrapSet κ M u then
      rotheSeqOfPaperRouteA p c lam M κ Λ u (hinput u hu) hκ hM
    else fun _ => upperBarrier κ M

variable {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}

@[simp] theorem rotheSeqOfPaperRouteAFromTrap_eq
    (hinput : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (hu : InMonotoneWaveTrapSet κ M u) :
    rotheSeqOfPaperRouteAFromTrap p c lam M κ Λ hinput hκ hM u =
      rotheSeqOfPaperRouteA p c lam M κ Λ u (hinput u hu) hκ hM := by
  simp [rotheSeqOfPaperRouteAFromTrap, hu]

/-- The actual dependent Route-A output used for successor `k+1`. -/
def paperRouteARotheOutputAt
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ)
    (hin : PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (k : ℕ) :
    Σ' W : ℝ → ℝ, PaperStepOutputRouteACore p c lam M κ Λ u
      (rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM k) W :=
  let prev := paperRouteARotheStep p c lam M κ Λ u hin hκ hM k
  hin.produce_regular prev.1 prev.2

theorem rotheSeqOfPaperRouteA_base
    (hin : PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (k : ℕ) :
    PaperIterateBase p c κ M u
      (rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM k) :=
  (paperRouteARotheStep p c lam M κ Λ u hin hκ hM k).2

@[simp] theorem rotheSeqOfPaperRouteA_zero
    (hin : PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) :
    rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM 0 =
      upperBarrier κ M := rfl

theorem rotheSeqOfPaperRouteA_lowerPinned_base
    {φ : ℝ → ℝ}
    (hin : PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (hu : InLowerPinnedMonotoneTrap κ M φ u) :
    ∀ x, φ x ≤ rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM 0 x := by
  intro x
  rw [rotheSeqOfPaperRouteA_zero]
  exact le_trans (hu.lower x) (hu.bare.le_upperBarrier x)

theorem rotheSeqOfPaperRouteA_succ_eq_output
    (hin : PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (k : ℕ) :
    rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM (k + 1) =
      (paperRouteARotheOutputAt p c lam M κ Λ u hin hκ hM k).1 := by
  rfl

theorem rotheSeqOfPaperRouteA_stepFacts
    (hin : PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (k : ℕ) :
    PaperRotheStepFacts p c lam M κ Λ u
      (rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM k)
      (rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM (k + 1)) := by
  rw [rotheSeqOfPaperRouteA_succ_eq_output]
  exact paperRotheStepFacts_of_routeA_output hin
    (paperRouteARotheOutputAt p c lam M κ Λ u hin hκ hM k).2

def rotheSeqOfPaperRouteA_stepAnalytic
    (hin : PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (k : ℕ) :
    PaperStepAnalytic p c lam M κ Λ u
      (rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM k)
      (rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM (k + 1)) := by
  rw [rotheSeqOfPaperRouteA_succ_eq_output]
  exact paperStepAnalytic_of_core hin.hlam
    (paperRouteARotheOutputAt p c lam M κ Λ u hin hκ hM k).2.analytic

section RouteAOrbit

variable (hin : PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u)
  (hκ : 0 ≤ κ) (hM : 0 ≤ M)

theorem rotheSeqOfPaperRouteA_cont (k : ℕ) :
    Continuous (rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM k) :=
  (rotheSeqOfPaperRouteA_base hin hκ hM k).cont

theorem rotheSeqOfPaperRouteA_anti_x (k : ℕ) :
    Antitone (rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM k) :=
  (rotheSeqOfPaperRouteA_base hin hκ hM k).anti

theorem rotheSeqOfPaperRouteA_nonneg (k : ℕ) (x : ℝ) :
    0 ≤ rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM k x :=
  (rotheSeqOfPaperRouteA_base hin hκ hM k).nonneg x

theorem rotheSeqOfPaperRouteA_paperSuper (k : ℕ) (x : ℝ) :
    paperWaveOperator p c u
      (rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM k) x ≤ 0 :=
  (rotheSeqOfPaperRouteA_base hin hκ hM k).paperSuper x

theorem rotheSeqOfPaperRouteA_le_barrier (k : ℕ) (x : ℝ) :
    rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM k x ≤
      upperBarrier κ M x :=
  (rotheSeqOfPaperRouteA_base hin hκ hM k).le_barrier x

theorem rotheSeqOfPaperRouteA_le_M (k : ℕ) (x : ℝ) :
    rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM k x ≤ M :=
  le_trans (rotheSeqOfPaperRouteA_le_barrier hin hκ hM k x)
    (upperBarrier_le_M κ M x)

theorem rotheSeqOfPaperRouteA_succ_le (k : ℕ) (x : ℝ) :
    rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM (k + 1) x ≤
      rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM k x :=
  (rotheSeqOfPaperRouteA_stepFacts hin hκ hM k).le_old x

theorem rotheSeqOfPaperRouteA_anti_k (x : ℝ) :
    Antitone (fun k =>
      rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM k x) :=
  antitone_nat_of_succ_le (fun k =>
    rotheSeqOfPaperRouteA_succ_le hin hκ hM k x)

theorem rotheSeqOfPaperRouteA_bddBelow (x : ℝ) :
    BddBelow (Set.range (fun k =>
      rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM k x)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact rotheSeqOfPaperRouteA_nonneg hin hκ hM k x

theorem rotheSeqOfPaperRouteA_succ_lipschitz
    (hΛ : 0 ≤ Λ) (k : ℕ) :
    ∀ x y,
      |rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM (k + 1) x -
        rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM (k + 1) y| ≤
          Λ * |x - y| := by
  intro x y
  have hfacts := rotheSeqOfPaperRouteA_stepFacts hin hκ hM k
  have hLip : LipschitzWith (Real.toNNReal Λ)
      (rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM (k + 1)) :=
    crossImplicitStep_lipschitz hΛ hfacts.diff hfacts.deriv_le
  have h := hLip.dist_le_mul x y
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hΛ] at h
  exact h

theorem rotheSeqOfPaperRouteA_equiLip
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (k : ℕ) :
    ∀ x y,
      |rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM k x -
        rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM k y| ≤
          M * |x - y| := by
  cases k with
  | zero =>
      intro x y
      rw [rotheSeqOfPaperRouteA_zero]
      exact hbarLip x y
  | succ k =>
      intro x y
      exact le_trans
        (rotheSeqOfPaperRouteA_succ_lipschitz hin hκ hM hΛ0 k x y)
        (mul_le_mul_of_nonneg_right hΛM (abs_nonneg _))

/-- Uniform orbit modulus with the spatial constant independent of the
amplitude bound. -/
theorem rotheSeqOfPaperRouteA_equiLip_modulus
    {L : ℝ} (hΛ0 : 0 ≤ Λ) (hΛL : Λ ≤ L)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ L * |x - y|)
    (k : ℕ) :
    ∀ x y,
      |rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM k x -
        rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM k y| ≤
          L * |x - y| := by
  cases k with
  | zero =>
      intro x y
      rw [rotheSeqOfPaperRouteA_zero]
      exact hbarLip x y
  | succ k =>
      intro x y
      exact le_trans
        (rotheSeqOfPaperRouteA_succ_lipschitz hin hκ hM hΛ0 k x y)
        (mul_le_mul_of_nonneg_right hΛL (abs_nonneg _))

theorem rotheSeqOfPaperRouteA_limitLip
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (x y : ℝ) :
    |rotheLimit (rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM) x -
      rotheLimit (rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM) y| ≤
        M * |x - y| := by
  set z := rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM with hz
  have hax : Tendsto (fun k => z k x) atTop (𝓝 (rotheLimit z x)) :=
    rotheLimit_tendsto (rotheSeqOfPaperRouteA_anti_k hin hκ hM)
      (rotheSeqOfPaperRouteA_bddBelow hin hκ hM) x
  have hay : Tendsto (fun k => z k y) atTop (𝓝 (rotheLimit z y)) :=
    rotheLimit_tendsto (rotheSeqOfPaperRouteA_anti_k hin hκ hM)
      (rotheSeqOfPaperRouteA_bddBelow hin hκ hM) y
  have htend : Tendsto (fun k => |z k x - z k y|) atTop
      (𝓝 (|rotheLimit z x - rotheLimit z y|)) :=
    (hax.sub hay).abs
  refine le_of_tendsto htend ?_
  filter_upwards with k
  exact rotheSeqOfPaperRouteA_equiLip hin hκ hM hΛ0 hΛM hbarLip k x y

/-- The long-time limit inherits an independent uniform spatial modulus. -/
theorem rotheSeqOfPaperRouteA_limitLip_modulus
    {L : ℝ} (hΛ0 : 0 ≤ Λ) (hΛL : Λ ≤ L)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ L * |x - y|)
    (x y : ℝ) :
    |rotheLimit (rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM) x -
      rotheLimit (rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM) y| ≤
        L * |x - y| := by
  set z := rotheSeqOfPaperRouteA p c lam M κ Λ u hin hκ hM with hz
  have hax : Tendsto (fun k => z k x) atTop (nhds (rotheLimit z x)) :=
    rotheLimit_tendsto (rotheSeqOfPaperRouteA_anti_k hin hκ hM)
      (rotheSeqOfPaperRouteA_bddBelow hin hκ hM) x
  have hay : Tendsto (fun k => z k y) atTop (nhds (rotheLimit z y)) :=
    rotheLimit_tendsto (rotheSeqOfPaperRouteA_anti_k hin hκ hM)
      (rotheSeqOfPaperRouteA_bddBelow hin hκ hM) y
  have htend : Tendsto (fun k => |z k x - z k y|) atTop
      (nhds (|rotheLimit z x - rotheLimit z y|)) :=
    (hax.sub hay).abs
  refine le_of_tendsto htend ?_
  exact Eventually.of_forall fun k =>
    rotheSeqOfPaperRouteA_equiLip_modulus
      hin hκ hM hΛ0 hΛL hbarLip k x y

end RouteAOrbit

/-- Orbit compactness package for the analytic-preserving Route-A recursion. -/
theorem paperRouteARotheOrbitData_fromTrap
    (hinput : ∀ v, InMonotoneWaveTrapSet κ M v →
      PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ v)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hu : InMonotoneWaveTrapSet κ M u) :
    PaperRotheOrbitData p c lam M κ
      (rotheSeqOfPaperRouteAFromTrap p c lam M κ Λ hinput hκ hM) u := by
  let hin := hinput u hu
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
  · simpa only [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu] using
      rotheSeqOfPaperRouteA_cont hin hκ hM
  · simpa only [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu] using
      rotheSeqOfPaperRouteA_anti_k hin hκ hM
  · simpa only [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu] using
      rotheSeqOfPaperRouteA_anti_x hin hκ hM
  · simpa only [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu] using
      rotheSeqOfPaperRouteA_nonneg hin hκ hM
  · simpa only [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu] using
      rotheSeqOfPaperRouteA_le_M hin hκ hM
  · simpa only [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu] using
      rotheSeqOfPaperRouteA_le_barrier hin hκ hM
  · simpa only [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu] using
      rotheSeqOfPaperRouteA_bddBelow hin hκ hM
  · simpa only [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu] using
      rotheSeqOfPaperRouteA_equiLip hin hκ hM hΛ0 hΛM hbarLip
  · intro x y
    simpa only [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu] using
      rotheSeqOfPaperRouteA_limitLip hin hκ hM hΛ0 hΛM hbarLip x y

/-- Orbit compactness for Route A with a spatial modulus independent of the
amplitude. -/
theorem paperRouteARotheOrbitDataWithModulus_fromTrap
    {L : ℝ}
    (hinput : ∀ v, InMonotoneWaveTrapSet κ M v →
      PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ v)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hΛ0 : 0 ≤ Λ) (hΛL : Λ ≤ L)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ L * |x - y|)
    (hu : InMonotoneWaveTrapSet κ M u) :
    PaperRotheOrbitDataWithModulus p c lam M κ L
      (rotheSeqOfPaperRouteAFromTrap p c lam M κ Λ hinput hκ hM u) := by
  let hin := hinput u hu
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
  · simpa only [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu] using
      rotheSeqOfPaperRouteA_cont hin hκ hM
  · simpa only [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu] using
      rotheSeqOfPaperRouteA_anti_k hin hκ hM
  · simpa only [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu] using
      rotheSeqOfPaperRouteA_anti_x hin hκ hM
  · simpa only [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu] using
      rotheSeqOfPaperRouteA_nonneg hin hκ hM
  · simpa only [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu] using
      rotheSeqOfPaperRouteA_le_M hin hκ hM
  · simpa only [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu] using
      rotheSeqOfPaperRouteA_le_barrier hin hκ hM
  · simpa only [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu] using
      rotheSeqOfPaperRouteA_bddBelow hin hκ hM
  · simpa only [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu] using
      rotheSeqOfPaperRouteA_equiLip_modulus
        hin hκ hM hΛ0 hΛL hbarLip
  · intro x y
    simpa only [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu] using
      rotheSeqOfPaperRouteA_limitLip_modulus
        hin hκ hM hΛ0 hΛL hbarLip x y

section AxiomAudit

#print axioms paperRotheStepFacts_of_routeA_output
#print axioms rotheSeqOfPaperRouteA_stepFacts
#print axioms rotheSeqOfPaperRouteA_stepAnalytic
#print axioms paperRouteARotheOrbitData_fromTrap
#print axioms paperRouteARotheOrbitDataWithModulus_fromTrap

end AxiomAudit

end ShenWork.Paper1
