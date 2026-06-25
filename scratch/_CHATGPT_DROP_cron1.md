# Q446 / cron1: `hlogSrc` frontier for B-form `conjugatePicardLimit`

## Executive verdict

I do **not** find an existing K1/K2 tower for `conjugatePicardIter` analogous to the `picardIter` tower.  The repo has:

* the B-form Picard core (`conjugatePicardIter`, `conjugatePicardLimit`, ball/geometric/limit mild solution),
* windowed ball/source-control leaves for conjugate iterates,
* limit-side source-slice leaves (`hlogCont`, `hlogFourier`, etc.),
* the generic one-step `DuhamelSourceTimeC1On` recursion theorem,
* and the uniform-limit theorem for `DuhamelSourceTimeC1On`.

But I did **not** find conjugate-iterate versions of the K1/K2 data needed to instantiate the source recursion:

```lean
hagree        -- cosine representation of conjugatePicardIter level slices
hbsum         -- eigenvalue-weighted summability of that representation
hpos          -- strict positive lift on the closed slab
hG1 / hG2     -- spatial derivative / second-derivative bounds
hrestart      -- restart coefficient agreement
hprofile_joint -- joint continuity of the lifted profile on the closed slab
```

`ConjugateMildExistenceData` + `iter_ball_package` gives only the low-order fixed-point data: ball bound, nonnegativity, continuous spatial slices, and joint measurability on `(0,T]`.  It does **not** contain spectral representations, eigenvalue-weighted coefficient summability, derivative/Hessian bounds, restart representations, or joint continuity on closed time-space slabs.  So it is not enough to instantiate `sourceTimeC1On_succ_of_sourceTimeC1On` for `conjugatePicardIter`.

The gradient tower does not transfer automatically.  `picardIter` and `conjugatePicardIter` are different iterations: the gradient route uses `intervalGradientDuhamelMap`, whose chemotaxis leg is `∂ₓ S(t-s) Q`; the B-form route uses `intervalConjugateDuhamelMap`, whose chemotaxis leg is the conjugate kernel operator `B_N(t-s) Q = -∫ ∂ᵧK_N(t-s,x,y)Q(y)dy`.  I did not find a theorem equating the two iterate families, nor a wrapper theorem reducing `conjugatePicardIter` to `picardIter`.

Therefore: `hlogSrc` is still a genuine frontier.  The available recursion/limit machinery can be reused, but it needs a new B-form/conjugate iterate K1/K2 tower or a new direct route to source-time-`C¹` for the limit.

---

## 1. What `conjugatePicardIter` is

Definition in `ShenWork/Paper2/IntervalConjugatePicard.lean`:

```lean
/-- B-form Picard iteration:
`u₀(t,x) = S(t)u₀(x)`, `u_{n+1} = Φᴮ(u_n)`. -/
def conjugatePicardIter (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) :
    ℕ → (ℝ → intervalDomainPoint → ℝ)
  | 0 => fun t x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
  | n + 1 => fun t x =>
      intervalConjugateDuhamelMap p u₀ (conjugatePicardIter p u₀ n) t x

/-- Pointwise limit of the B-form Picard iterates on `(0,T]`; zero outside. -/
def conjugatePicardLimit (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (T : ℝ)
    (t : ℝ) (x : intervalDomainPoint) : ℝ :=
  if 0 < t ∧ t ≤ T then
    atTop.limUnder (fun n => conjugatePicardIter p u₀ n t x)
  else 0
```

The corresponding B-form map is in `IntervalConjugateDuhamelMap.lean`:

```lean
/-- The conjugate-kernel chemotaxis operator
`B_N(t)Q(x) = -∫₀¹ ∂ᵧK_N(t,x,y)Q(y)dy`. -/
def intervalConjugateKernelOperator (t : ℝ) (Q : ℝ → ℝ) (x : ℝ) : ℝ :=
  -∫ y, deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y * Q y
      ∂ intervalMeasure 1

/-- The B-form Picard map.  Compared with `intervalGradientDuhamelMap`, only the
chemotaxis leg changes: `∂ₓS(t-s)Q` is replaced by `B_N(t-s)Q`. -/
def intervalConjugateDuhamelMap (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) (x : intervalDomainPoint) : ℝ :=
  intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
    + (-p.χ₀) * (∫ s in (0:ℝ)..t,
        intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x.1)
    + ∫ s in (0:ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x.1
```

Compare with `intervalGradientDuhamelMap` in `IntervalGradientDuhamelMap.lean`:

```lean
/-- **The weak divergence-form mild map.**  `Φ(u₀,u)(t,x) = S(t)u₀(x) −
χ₀∫₀ᵗ∂ₓS(t−s)Q(u(s))(x)ds + ∫₀ᵗS(t−s)L(u(s))(x)ds`.  The chemotaxis term puts
`∂ₓ` on the semigroup (divergence form), so it integrates the C⁰ flux `Q`. -/
def intervalGradientDuhamelMap (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) (x : intervalDomainPoint) : ℝ :=
  intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
    + (-p.χ₀) * (∫ s in (0:ℝ)..t,
        deriv (fun z => intervalFullSemigroupOperator (t - s) (chemFluxLifted p (u s)) z) x.1)
    + ∫ s in (0:ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x.1
```

So the two iterations are not definitionally the same after level 0.

---

## 2. Relation between `picardIter` and `conjugatePicardIter`

Search result summary:

```text
conjugatePicardIter picardIter
```

finds references in docs / bank files / core files, but I did not find an equality theorem of the form:

```lean
conjugatePicardIter p u₀ n = picardIter p u₀ n
```

or a conditional equality under smoothness / Neumann / integration-by-parts assumptions.

The only overlap is level 0:

```lean
conjugatePicardIter p u₀ 0 t x
  = intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
```

and the gradient tower level-0 heat facts are likewise for the heat semigroup.  But for successors the maps differ:

```lean
picardIter successor      uses intervalGradientDuhamelMap
conjugatePicard successor uses intervalConjugateDuhamelMap
```

Analytically these chemotaxis legs may be related by kernel integration by parts under enough regularity/boundary hypotheses, but that bridge is not present as an iterate-family equality in the repo.

---

## 3. What the generic source recursion actually provides

`IntervalPicardSourceTimeC1OnRecursion.lean` contains a genuinely useful **one-step generic theorem**:

```lean
/-- Endpoint-inclusive successor source package.

The predecessor enters only through the shifted `src : DuhamelSourceTimeC1On a 0 W`.
All remaining assumptions are the satisfiable restart/field facts on the closed
window `[lo, hi]`: representation, positivity, sup/C2 bounds, coefficient-window
shift, and restart agreement. -/
noncomputable def sourceTimeC1On_succ_of_sourceTimeC1On
    {p : CM2Params}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {w : ℝ → intervalDomainPoint → ℝ}
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (hM₀ : 0 ≤ M₀)
    (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} {offset W lo hi aτ M G1 G2 : ℝ}
    (src : DuhamelSourceTimeC1On a 0 W)
    (hlohi : lo ≤ hi)
    (haτpos : 0 < aτ)
    (hshift : Set.MapsTo (fun s : ℝ => s - offset)
      (Set.Icc lo hi) (Set.Icc aτ W))
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ ∈ Set.Icc lo hi,
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ ∈ Set.Icc lo hi,
      Set.EqOn (intervalDomainLift (w σ))
        (fun x => ∑' n, bc σ n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ σ ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (w σ) x)
    (hub : ∀ σ ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (w σ) x ≤ M)
    (hG1 : ∀ σ ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (w σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (w σ))) x| ≤ G2)
    (hrestart : ∀ s ∈ Set.Icc lo hi, ∀ x : intervalDomainPoint,
      intervalDomainLift (w s) x.1 =
        ∑' n, localRestartCoeff a₀ a (s - offset) n * cosineMode n x.1)
    (hC2cont : ∀ s ∈ Set.Icc lo hi,
      ContinuousOn (intervalDomainLift (w s)) (Set.Icc (0 : ℝ) 1))
    (hprofile_joint : ContinuousOn
      (Function.uncurry (fun s x => intervalDomainLift (w s) x))
      (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1)) :
    DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (w s)) k) lo hi
```

This theorem can in principle be applied to `w := conjugatePicardIter p u₀ (n+1)` or `w := conjugatePicardIter p u₀ n`.  But all of the hard K1/K2 fields are inputs, not outputs.

The induction wrapper is **not** generic over the iterate family.  It is hardwired to `picardIter`:

```lean
/-- The level-`n` canonical source package on the positive window `[c,T]`. -/
abbrev LevelSourceTimeC1On
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (n : ℕ) (c T : ℝ) :=
  DuhamelSourceTimeC1On
    (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
    c T

/-- A level source package on every positive lower endpoint, all reaching `T`. -/
abbrev LevelSourceTimeC1OnUpTo
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ) (T : ℝ) :=
  ∀ c, 0 < c → c < T → LevelSourceTimeC1On p u₀ n c T

/-- The induction signature for producing all level source packages from a base
case and an endpoint-inclusive successor step. -/
noncomputable def sourceTimeC1On_all_windows_of_base_step
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {T : ℝ}
    (base : LevelSourceTimeC1OnUpTo p u₀ 0 T)
    (step : ∀ n,
      LevelSourceTimeC1OnUpTo p u₀ n T →
        LevelSourceTimeC1OnUpTo p u₀ (n + 1) T) :
    ∀ n, LevelSourceTimeC1OnUpTo p u₀ n T
```

So for B-form iterates you would need a parallel alias/induction wrapper:

```lean
abbrev ConjugateLevelSourceTimeC1On
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (n : ℕ) (c T : ℝ) :=
  DuhamelSourceTimeC1On
    (fun s k => cosineCoeffs
      (logisticLifted p (conjugatePicardIter p u₀ n s)) k)
    c T
```

and then an analogous `all_windows` induction, whose successor step is supplied by the generic one-step theorem above after building the B-form K1/K2 facts.

---

## 4. What exists for `conjugatePicardIter`

### 4.1 Ball/nonneg/continuous-slice package

`IntervalBankInfAndLogSrcWiring.lean` provides:

```lean
/-- The conjugate Picard iterates satisfy the ball / nonneg / continuous-slice /
joint-measurability package on the window `(0, D.T]`, replayed from the keystone
`ConjugateMildExistenceData`. -/
theorem iter_ball_package
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) (n : ℕ) :
    (∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
        |conjugatePicardIter p u₀ n t x| ≤ D.M) ∧
    (∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
        0 ≤ conjugatePicardIter p u₀ n t x) ∧
    HasContinuousSlices D.T (conjugatePicardIter p u₀ n) ∧
    HasJointMeasurability (conjugatePicardIter p u₀ n)
```

This is useful, but it is weaker than the K1/K2 input package.  In particular:

```text
HasContinuousSlices            ≠ joint ContinuousOn on closed slab
nonnegativity                  ≠ strict positivity on closed slab
ball bound                     ≠ derivative/Hessian bounds
joint measurability            ≠ source coefficient TimeC1On
```

### 4.2 Windowed source-control bounds

Same file provides windowed chem/logistic source bounds and integrability:

```lean
theorem iterChemFlux_windowBound
    (D : ConjugateMildExistenceData p u₀) (n : ℕ) :
    ∀ s, 0 < s → s ≤ D.T → ∀ y,
      |chemFluxLifted p (conjugatePicardIter p u₀ n s) y| ≤ iterCQ D

theorem iterLogistic_windowBound
    (D : ConjugateMildExistenceData p u₀) (n : ℕ) :
    ∀ s, 0 < s → s ≤ D.T → ∀ y,
      |logisticLifted p (conjugatePicardIter p u₀ n s) y| ≤ iterCL D

theorem iterChemFlux_integrable
    (D : ConjugateMildExistenceData p u₀) (n : ℕ) :
    ∀ s, 0 < s → s ≤ D.T →
      Integrable (chemFluxLifted p (conjugatePicardIter p u₀ n s)) (intervalMeasure 1)
```

Again: useful for Barrier B / Hinf, but not enough for source coefficient time-`C¹`.

### 4.3 Geometric convergence and limit regularity

The B-form Picard file proves the usual windowed convergence, boundedness, nonnegativity, and continuous-slice inheritance:

```lean
theorem conjugatePicardIter_pointwise_convergent ...
theorem conjugatePicardIter_pointwise_tail_bound ...
theorem conjugatePicardIter_uniform_convergence ...
theorem conjugatePicardLimit_bounded ...
theorem conjugatePicardLimit_nonneg ...
theorem conjugatePicardLimit_hasContinuousSlices ...
theorem conjugatePicardLimit_is_mildSolution ...
```

and the data structure has:

```lean
structure ConjugateMildExistenceData (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) where
  T : ℝ
  M : ℝ
  K : ℝ
  C₀ : ℝ
  hT : 0 < T
  hM : 0 < M
  hK : K < 1
  hK_nn : 0 ≤ K
  hC₀ : 0 ≤ C₀
  hbase_ball : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    |conjugatePicardIter p u₀ 0 t x| ≤ M
  hbase_nonneg : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    0 ≤ conjugatePicardIter p u₀ 0 t x
  hbase_cont : HasContinuousSlices T (conjugatePicardIter p u₀ 0)
  hmapsTo : ...
  hmapsTo_nn : ...
  hmapsTo_pos : ...
  hcont_preserved : ...
  hcontr : ...
  hbase_diff : ...
  hbase_meas : HasJointMeasurability (conjugatePicardIter p u₀ 0)
  hmeas_preserved : ∀ w, HasJointMeasurability w →
    HasJointMeasurability (fun t x => intervalConjugateDuhamelMap p u₀ w t x)
```

`hmapsTo_pos` can give strict positivity of successor outputs under ball/nonneg/continuous-slice assumptions, and `conjugateMildSolutionData_of_data` uses it to prove strict positivity of the **limit**:

```lean
hpos : ∀ t, 0 < t → t ≤ T → ∀ x, 0 < u t x
```

But this still does not supply representation / hbsum / G1 / G2 / restart agreement for the iterates.

### 4.4 PID inf-threshold positivity

`IntervalConjugatePicardInfThreshold.lean` proves strong positivity/lower-floor statements for iterates and the limit under additional PID + Hinf + smallness assumptions:

```lean
theorem conjugatePicardIter_ge_half_floor_of_PID
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (H : ConjugatePicardInfThresholdData p u₀ T)
    (hsmall :
      |p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * H.CQ)
        + T * H.CL ≤ paperPositiveFloor hu₀ / 2) :
    ∀ n t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      paperPositiveFloor hu₀ / 2 ≤ conjugatePicardIter p u₀ n t x

theorem conjugatePicardLimit_pos_of_PID
    ... :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 < conjugatePicardLimit p u₀ T t x
```

This helps with `hpos`, but it still depends on `Hinf` and does not provide the spectral or derivative pieces.

---

## 5. What exists for the limit, not the iterates

`IntervalBankSourceSliceLeaves.lean` proves some limit-side source-slice leaves for `conjugatePicardLimit`:

```lean
theorem conjugatePicardLimit_hasContinuousSlices_of_data
    (DB : ConjugateMildExistenceData p u₀) :
    HasContinuousSlices DB.T (conjugatePicardLimit p u₀ DB.T)

theorem coupledLogistic_constExtend_continuous_of_limit
    (DB : ConjugateMildExistenceData p u₀) :
    ∀ t, 0 < t → t < DB.T →
      Continuous
        (intervalDomainConstExtend
          (intervalLogisticSource p ((conjugatePicardLimit p u₀ DB.T) t)))

theorem coupledLogistic_fourierCoeff_summable_of_limit
    (DB : ConjugateMildExistenceData p u₀)
    (huPaper : PaperPositiveInitialDatum intervalDomain u₀)
    (Hinf : ConjugatePicardInfThresholdData p u₀ DB.T)
    (hsmall : ...)
    (HR : HasRestartCosineRepresentations DB.T (conjugatePicardLimit p u₀ DB.T)) :
    ∀ t, 0 < t → t < DB.T →
      Summable (fun n : ℤ => fourierCoeff ... n)
```

This is important, but it is not `DuhamelSourceTimeC1On` for the limit coefficients.  The file itself states that it supplies fields like `hlogCont`/`hlogFourier` and consumes a restart representation of the limit; it does not close `hlogSrc`.

The bank wiring file also explicitly says the top-level `hlogSrc` field is not fully landed:

```text
field 6 needs a restart-cosine representation + time-C¹ coefficient data for
`conjugatePicardLimit` that is not landed anywhere in the tree.
```

That matches the current search result.

---

## 6. Why `ConjugateMildExistenceData` + `iter_ball_package` is insufficient

To instantiate:

```lean
sourceTimeC1On_succ_of_sourceTimeC1On
```

for B-form iterates, you need at each closed window `[lo,hi]`:

```lean
hbsum : ∀ σ ∈ Set.Icc lo hi,
  Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|)

hagree : ∀ σ ∈ Set.Icc lo hi,
  Set.EqOn (intervalDomainLift (w σ))
    (fun x => ∑' n, bc σ n * cosineMode n x)
    (Set.Icc (0 : ℝ) 1)

hpos : ∀ σ ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
  0 < intervalDomainLift (w σ) x

hG1 : ∀ σ ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
  |deriv (intervalDomainLift (w σ)) x| ≤ G1

hG2 : ∀ σ ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
  |deriv (deriv (intervalDomainLift (w σ))) x| ≤ G2

hrestart : ∀ s ∈ Set.Icc lo hi, ∀ x : intervalDomainPoint,
  intervalDomainLift (w s) x.1 =
    ∑' n, localRestartCoeff a₀ a (s - offset) n * cosineMode n x.1

hC2cont : ∀ s ∈ Set.Icc lo hi,
  ContinuousOn (intervalDomainLift (w s)) (Set.Icc (0 : ℝ) 1)

hprofile_joint : ContinuousOn
  (Function.uncurry (fun s x => intervalDomainLift (w s) x))
  (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1)
```

`iter_ball_package` gives:

```lean
ball bound
nonnegativity
HasContinuousSlices
HasJointMeasurability
```

Only `hC2cont` is plausibly obtainable from `HasContinuousSlices`; even that is just continuity, not C².  The rest does not follow:

* `hagree` needs a cosine-series representation.
* `hbsum` needs eigenvalue-weighted summability of representation coefficients.
* `hG1`/`hG2` need spatial derivative/Hessian estimates.
* `hrestart` needs local restart coefficient synthesis.
* `hprofile_joint` needs joint continuity on compact slabs, not merely joint measurability plus per-slice continuity.
* `hpos` needs strict positivity, not just nonnegativity; it can be supplied by `hmapsTo_pos` for successors or by PID inf-threshold, but it is not part of `iter_ball_package`.

So the answer is no: these K1/K2 facts are not derivable from `ConjugateMildExistenceData + iter_ball_package` alone.

---

## 7. What the gradient tower has that B-form lacks

`IntervalPicardSourceTower.lean` is explicitly a `picardIter` tower.  Its carrier packages representation, G1/G2 profiles, per-window source packages, endpoint-inclusive source packages, and bounded source packages:

```lean
structure TowerLevel (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (M A₂ T : ℝ) (n : ℕ) where
  /-- Eigenvalue-weighted summability of the level-`n` representation coefficients. -/
  hrepr_sum : ∀ σ, 0 < σ → σ ≤ T →
    Summable (fun k => (λ_ k) * |iterateReprCoeff p u₀ n σ k|)
  /-- `[0,1]` agreement of the level-`n` slice with its representation series. -/
  hrepr_agree : ∀ σ, 0 < σ → σ ≤ T →
    Set.EqOn (intervalDomainLift (picardIter p u₀ n σ))
      (fun x => ∑' k, iterateReprCoeff p u₀ n σ k * cosineMode k x)
      (Set.Icc (0 : ℝ) 1)
  /-- Kernel G1-line: first-derivative sup bound along `G1profile p M`. -/
  hG1 : ∀ σ, 0 < σ → σ ≤ T → ∀ x : ℝ,
    |deriv (intervalDomainLift (picardIter p u₀ n σ)) x| ≤ G1profile p M σ
  /-- Coefficient G2-line: second-derivative sup bound along `G2profile A₂`. -/
  hG2 : ∀ σ, 0 < σ → σ ≤ T → ∀ x : ℝ,
    |deriv (deriv (intervalDomainLift (picardIter p u₀ n σ))) x| ≤ G2profile A₂ σ
  srcWin : ∀ lo hi, 0 < lo → lo ≤ hi → hi < T → SourceWin p u₀ n lo hi
  winAdot : ∀ lo hi, 0 < lo → lo ≤ hi → hi < T → WindowAdotLegs p u₀ n lo hi
  srcOn : LevelSourceTimeC1OnUpTo p u₀ n T
  srcBdd : DuhamelSourceBddOn (patchedSource p u₀ (picardIter p u₀ n)) T
```

This is exactly the missing K1/K2 material, but it is tied to `picardIter`, not `conjugatePicardIter`.  Its `TowerInputs` even includes a `χ₀ = 0` field:

```lean
/-- `χ₀ = 0` (the homogeneous-propagator regime). -/
hχ0 : p.χ₀ = 0
```

So it is not a general-χ/B-form iterate tower.

---

## 8. Can the existing limit theorem be used?

Yes, but only after the iterate source packages and coefficient convergence data have been produced.

`IntervalMildPicardLimitRegularityOn.lean` provides:

```lean
/-- `DuhamelSourceTimeC1On` passes to pointwise limits when the derivatives
converge uniformly on `Icc lo hi`, the coefficients share a common summable
envelope, and the derivative sequence is uniformly bounded. -/
def duhamelSourceTimeC1On_of_uniform_limit
    {a : ℝ → ℕ → ℝ} {aSeq : ℕ → ℝ → ℕ → ℝ}
    {lo hi : ℝ}
    (hconv : ∀ s ∈ Icc lo hi, ∀ k, Tendsto (fun n => aSeq n s k) atTop (nhds (a s k)))
    {adotSeq : ℕ → ℝ → ℕ → ℝ}
    (hderiv_each : ∀ n, ∀ s ∈ Icc lo hi, ∀ k,
      HasDerivWithinAt (fun r => aSeq n r k) (adotSeq n s k) (Icc lo hi) s)
    {adot : ℝ → ℕ → ℝ}
    (hadot_unif : ∀ k, TendstoUniformlyOn (fun n s => adotSeq n s k)
      (fun s => adot s k) atTop (Icc lo hi))
    (hadot_cont : ∀ k, ContinuousOn (fun s => adot s k) (Icc lo hi))
    {envelope : ℕ → ℝ}
    (henv_summable : Summable envelope)
    (henv_bound : ∀ n, ∀ s ∈ Icc lo hi, ∀ k, |aSeq n s k| ≤ envelope k)
    {D : ℝ}
    (hderiv_bound : ∀ n, ∀ s ∈ Icc lo hi, ∀ k, |adotSeq n s k| ≤ D) :
    DuhamelSourceTimeC1On a lo hi
```

This is a good endpoint.  But it requires uniform convergence of source coefficients and source-derivative coefficients, common envelopes, and derivative bounds.  Those are precisely what the missing conjugate iterate tower would have to provide.  It does not by itself manufacture K1/K2 facts from `ConjugateMildExistenceData`.

---

## 9. Recommended route to `hlogSrc`

A viable route is:

1. Define conjugate versions of the source package aliases:

```lean
abbrev ConjugateLevelSourceTimeC1On
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (n : ℕ) (c T : ℝ) :=
  DuhamelSourceTimeC1On
    (fun s k => cosineCoeffs (logisticLifted p (conjugatePicardIter p u₀ n s)) k)
    c T

abbrev ConjugateLevelSourceTimeC1OnUpTo
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ) (T : ℝ) :=
  ∀ c, 0 < c → c < T → ConjugateLevelSourceTimeC1On p u₀ n c T
```

2. Reuse / adapt the level-0 heat source theorem.  Level 0 is definitionally the same heat semigroup form, so the existing heat tools should be reusable with small wrappers.

3. Build a B-form successor tower for `conjugatePicardIter`.  This is the real work.  It must prove, for the successor slice, a B-form restart representation, eigenvalue-weighted summability, G1/G2 estimates, strict positivity, and joint continuity on closed slabs.

4. Apply `sourceTimeC1On_succ_of_sourceTimeC1On` with those B-form facts.

5. Use a conjugate analogue of `sourceTimeC1On_all_windows_of_base_step` to get all iterate source packages.

6. Prove the coefficient/uniform derivative convergence assumptions needed by `duhamelSourceTimeC1On_of_uniform_limit` and pass to `conjugatePicardLimit`.

Only after step 6 do you get:

```lean
DuhamelSourceTimeC1On
  (coupledLogisticSourceCoeffs p (conjugatePicardLimit p u₀ DB.T)) 0 DB.T
```

or more likely first on every `[c, DB.T]`, then extended/packaged as required by the bank API.

---

## Final answer

* The K1/K2 properties for `conjugatePicardIter` are **not already proved** in the repo, as far as the grep/read pass shows.
* `ConjugateMildExistenceData + iter_ball_package` gives ball/nonneg/continuous-slices/joint-measurability and source sup/integrability windows, but not representation/eigenvalue-summability/G1/G2/restart/joint-continuity.
* `picardIter` and `conjugatePicardIter` are not wrappers of one another; they use different Duhamel maps.  No equality bridge was found.
* The existing source-TimeC1On successor theorem is reusable, but its existing induction wrapper is `picardIter`-specific.  A conjugate/B-form source tower must be added or a different direct source-time-`C¹` route for the limit must be found.
* So `hlogSrc` remains a real production frontier, not a missing simple instantiation of the current tower.
