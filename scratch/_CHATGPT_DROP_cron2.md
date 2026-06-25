# Q455 (cron2): B-form iterate source tower after `hsrcBDirect`

## Executive verdict

I checked the current refactor in `IntervalBFormDirectClassical.lean`: `BFormBankedInputs` now asks for one direct field

```lean
hsrcBDirect : DuhamelSourceTimeC1On
  (bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T)) 0 DB.T
```

and `BFormBankedInputs.hsrcB` is just `B.hsrcBDirect`. This is the right target for the bank: it hides the split `logistic - χ₀ * chemDiv` from the final classical assembly.

But for the **iterate tower**, the existing successor

```lean
sourceTimeC1On_succ_of_sourceTimeC1On
```

still only produces the logistic half:

```lean
DuhamelSourceTimeC1On
  (fun s k => cosineCoeffs (logisticLifted p (w s)) k) lo hi
```

It cannot, by itself, produce the B-form source package at the next level. To get

```lean
DuhamelSourceTimeC1On
  (bFormSourceCoeffs p (conjugatePicardIter p u₀ n)) lo hi
```

at each finite level, the minimum sound architecture is **Option A**:

```text
logistic successor tower
+ parallel chemDiv source TimeC1On tower
+ existing bFormSource_duhamelSourceTimeC1On combiner
= B-form source TimeC1On tower
```

Option A is minimal because the existing B-form combiner is already landed:

```lean
bFormSource_duhamelSourceTimeC1On
  (hlog  : DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs p u) lo hi)
  (hchem : DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) lo hi)
```

The only missing half is the chem-div tower. You do **not** need to rewrite the logistic successor, and you do **not** need a new combined chain rule for the full B-form source.

Option B, a direct combined successor, is possible but not minimal: it still has to prove the full chem-div chain rule, source derivative field, weak-H²/decay, and uniform derivative bounds; it just buries them inside a larger theorem. It duplicates the already-landed logistic successor and loses modularity.

Option C, skipping the iterate tower and going directly to the limit via `duhamelSourceTimeC1On_of_uniform_limit`, is the highest-risk route. The geometric convergence of iterates gives value convergence, not convergence of the **time derivative coefficient fields** (`adotSeq`). The limit theorem needs `hadot_unif`, a common derivative bound, and a common summable envelope. Those are essentially the same regularity tower obligations, and they do not follow from the contraction/geometric estimate alone.

So the recommended path is:

```text
1. Keep using sourceTimeC1On_succ_of_sourceTimeC1On for logistic.
2. Build chemDivSourceTimeC1On_succ / chemDiv iterate tower in parallel.
3. Combine per level with bFormSource_duhamelSourceTimeC1On.
4. For the limit, pass the B-form source package by a uniform-limit theorem only after the finite tower carries uniform envelopes/adot convergence; otherwise carry a direct limit residual.
```

## Current bank target

Current `BFormBankedInputs` relevant excerpt:

```lean
structure BFormBankedInputs
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) where
  huPaper : PaperPositiveInitialDatum intervalDomain u₀
  Hinf : ConjugatePicardInfThresholdData p u₀ DB.T
  hsmall :
    |p.χ₀| * (heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt DB.T) * Hinf.CQ)
      + DB.T * Hinf.CL ≤ paperPositiveFloor huPaper / 2
  MInit : ℝ
  haInit : ∀ n,
    |cosineCoeffs (intervalDomainLift u₀) n| ≤ MInit
  hsrcBDirect : DuhamelSourceTimeC1On
    (bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T)) 0 DB.T
  hB_global : ∀ t, 0 < t → t ≤ DB.T →
    Set.EqOn
      (intervalDomainLift (conjugatePicardLimit p u₀ DB.T t))
      (fun x => ∑' n,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T))
          t n * cosineMode n x)
      (Set.Icc (0 : ℝ) 1)
  hlogCont : ∀ t, 0 < t → t < DB.T →
    Continuous
      (intervalDomainConstExtend
        (ShenWork.IntervalDomainExistence.intervalLogisticSource p
          ((conjugatePicardLimit p u₀ DB.T) t)))
  hlogFourier : ∀ t, 0 < t → t < DB.T →
    Summable (fun n : ℤ =>
      fourierCoeff
        (ShenWork.IntervalCosineInversion.reflCircle
          (intervalDomainConstExtend
            (ShenWork.IntervalDomainExistence.intervalLogisticSource p
              ((conjugatePicardLimit p u₀ DB.T) t)))) n)
  hchemIoo : ∀ t, 0 < t → t < DB.T →
    ChemDivCosineFourierDataIoo p
      ((conjugatePicardLimit p u₀ DB.T) t)
      (coupledChemicalConcentration p
        (conjugatePicardLimit p u₀ DB.T) t)
```

and:

```lean
def BFormBankedInputs.hsrcB
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBankedInputs p DB) :
    DuhamelSourceTimeC1On
      (bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T)) 0 DB.T :=
  B.hsrcBDirect
```

Thus the final bank no longer cares whether the source package came from `logistic + chemDiv`, a combined proof, or a direct limit proof. The architecture question is only about how to produce that field.

## Landed combiner: already enough once log + chem are available

`IntervalBFormSpectralHtime.lean` already has:

```lean
/-- The B-form total source coefficient family:
reaction coefficients minus `χ₀` times chem-div coefficients. -/
def bFormSourceCoeffs (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) : ℝ → ℕ → ℝ :=
  fun s n => coupledLogisticSourceCoeffs p u s n
    - p.χ₀ * coupledChemDivSourceCoeffs p u s n

/-- `DuhamelSourceTimeC1On` for the B-form total source, obtained by the committed
addition/scalar-closure of coefficient time-regularity on a window `[lo, hi]`. -/
noncomputable def bFormSource_duhamelSourceTimeC1On
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {lo hi : ℝ}
    (hlog : DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs p u) lo hi)
    (hchem : DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) lo hi) :
    DuhamelSourceTimeC1On (bFormSourceCoeffs p u) lo hi
```

This means Option A requires no new algebraic closure lemma. It only needs a source package for the chem-div half.

A useful tiny wrapper:

```lean
noncomputable def bFormSourceTimeC1On_of_parts
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {lo hi : ℝ}
    (hlog : DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs p u) lo hi)
    (hchem : DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) lo hi) :
    DuhamelSourceTimeC1On (bFormSourceCoeffs p u) lo hi :=
  ShenWork.IntervalBFormSpectral.bFormSource_duhamelSourceTimeC1On hlog hchem
```

## Option A — parallel chem-div tower + combine

### Verdict

Best option. It preserves the landed logistic successor and isolates the true missing analytic part: chem-div source time-regularity for finite B-form iterates.

### Existing logistic half

`sourceTimeC1On_succ_of_sourceTimeC1On` already gives the logistic successor. Its output is exactly:

```lean
DuhamelSourceTimeC1On
  (fun s k => cosineCoeffs (logisticLifted p (w s)) k) lo hi
```

For `w := conjugatePicardIter p u₀ (n+1)`, this is the same family as `coupledLogisticSourceCoeffs p (conjugatePicardIter p u₀ (n+1))`, modulo definitional rewriting.

### Minimal new theorem for the chem-div half

The missing parallel theorem should target:

```lean
noncomputable def chemDivSourceTimeC1On_succ
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {n : ℕ}
    {lo hi : ℝ}
    (R : ConjChemDivSuccData p u₀ n lo hi) :
    DuhamelSourceTimeC1On
      (coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ (n + 1))) lo hi := by
  -- through coupledChemDivSource_timeC1_of_fields / toOn / restrict
  sorry
```

The residual data structure should mirror the already landed chem-div source machinery, but specialized to finite iterates:

```lean
structure ConjChemDivSuccData
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (lo hi : ℝ) where
  /-- Globally or window-locally sufficient weak-H²/Neumann decay for each chem-div slice. -/
  Cchem : ℝ
  hCchem : 0 ≤ Cchem
  hH2 : ∀ s ∈ Set.Icc lo hi,
    ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann
      (coupledChemDivSourceLift p (conjugatePicardIter p u₀ (n + 1)) s)
  hdecay : ∀ s ∈ Set.Icc lo hi, ∀ k : ℕ, 1 ≤ k →
    |cosineCoeffs
      (coupledChemDivSourceLift p (conjugatePicardIter p u₀ (n + 1)) s) k|
      ≤ Cchem / ((k : ℝ) * Real.pi) ^ 2
  hzero : ∀ s ∈ Set.Icc lo hi,
    |cosineCoeffs
      (coupledChemDivSourceLift p (conjugatePicardIter p u₀ (n + 1)) s) 0| ≤ Cchem

  /-- Chain-rule and local slab data for differentiating the chem-div source in time. -/
  hchain : CoupledChemDivLocalChainRule p (conjugatePicardIter p u₀ (n + 1))

  /-- The derivative field for chem-div coefficients. -/
  hadotcont : ∀ k,
    ContinuousOn
      (fun s => coupledChemDivAdot p (conjugatePicardIter p u₀ (n + 1)) s k)
      (Set.Icc lo hi)
  MchemDot : ℝ
  hMdot : ∀ s ∈ Set.Icc lo hi, ∀ k,
    |coupledChemDivAdot p (conjugatePicardIter p u₀ (n + 1)) s k| ≤ MchemDot
```

There are two possible implementations:

1. Build a genuinely windowed chem-div constructor from this data.
2. If the existing global constructor is easier to reuse, strengthen the data to global/nonnegative-time fields and call:

```lean
coupledChemDivSource_timeC1_of_fields
```

then restrict with `.toOn`. This is heavier but likely much faster to land.

### Concrete missing lemmas for Option A

#### A1. Finite-iterate chem-div local chain rule

Existing structure:

```lean
structure CoupledChemDivLocalChainRule
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ,
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt
        (fun r => coupledChemDivSourceLift p u r x)
        (coupledChemDivTimeDerivativeLift p u s x) s) ∧
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

Missing finite-iterate theorem:

```lean
theorem coupledChemDivLocalChainRule_of_conjIter_succ_regular
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {n : ℕ}
    (R : ConjIterJointRegularityForChemDiv p u₀ (n + 1)) :
    CoupledChemDivLocalChainRule p (conjugatePicardIter p u₀ (n + 1)) := by
  sorry
```

What `ConjIterJointRegularityForChemDiv` must contain:

```lean
structure ConjIterJointRegularityForChemDiv
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (m : ℕ) where
  /-- Time derivative of u_m. -/
  du : ℝ → ℝ → ℝ
  /-- Time derivative of v_m = resolver(u_m). -/
  dv : ℝ → ℝ → ℝ
  /-- Joint spatial/time regularity of u_m on local slabs. -/
  u_joint_C2_timeC1 : Prop
  /-- Resolver time regularity and spatial derivatives. -/
  v_joint_C2_timeC1 : Prop
  /-- Positivity of 1+v for denominator. -/
  denom_pos : ∀ᶠ ... -- or local slab form
  /-- Chain rule identifying derivative of chem-div lift with coupledChemDivTimeDerivativeLift. -/
  chain_rule : Prop
```

This is the same real content as the residual in `IntervalChemDivWinDischarge.lean`.

#### A2. Finite-iterate chem-div weak-H²/decay

Existing `CoupledChemDivTimeC1Fields` needs:

```lean
hH2 : ∀ s, 0 ≤ s → IntervalWeakH2Neumann (coupledChemDivSourceLift p u s)
hdecay : ∀ s, 0 ≤ s → ∀ k : ℕ, 1 ≤ k →
  |cosineCoeffs (coupledChemDivSourceLift p u s) k| ≤ Cchem / ((k : ℝ) * Real.pi) ^ 2
hzero : ∀ s, 0 ≤ s →
  |cosineCoeffs (coupledChemDivSourceLift p u s) 0| ≤ Cchem
```

Missing finite-iterate/window theorem:

```lean
theorem conjIter_chemDivSource_weakH2_decay_on
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {n : ℕ} {lo hi : ℝ}
    (R : ConjIterSpatialRegularityForChemDiv p u₀ n lo hi) :
    ∃ Cchem ≥ 0,
      (∀ s ∈ Set.Icc lo hi,
        ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann
          (coupledChemDivSourceLift p (conjugatePicardIter p u₀ n) s)) ∧
      (∀ s ∈ Set.Icc lo hi, ∀ k : ℕ, 1 ≤ k →
        |cosineCoeffs
          (coupledChemDivSourceLift p (conjugatePicardIter p u₀ n) s) k|
          ≤ Cchem / ((k : ℝ) * Real.pi) ^ 2) ∧
      (∀ s ∈ Set.Icc lo hi,
        |cosineCoeffs
          (coupledChemDivSourceLift p (conjugatePicardIter p u₀ n) s) 0| ≤ Cchem) := by
  sorry
```

This likely needs space `C²`/Neumann regularity of the chem-div source itself, not merely of `u_n`.

#### A3. Finite-iterate chem-div `adot` continuity and uniform bound

Missing theorem:

```lean
theorem conjIter_coupledChemDivAdot_cont_bound_on
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {n : ℕ} {lo hi : ℝ}
    (R : ConjIterJointRegularityForChemDiv p u₀ n) :
    (∀ k, ContinuousOn
      (fun s => coupledChemDivAdot p (conjugatePicardIter p u₀ n) s k)
      (Set.Icc lo hi)) ∧
    ∃ Mdot, ∀ s ∈ Set.Icc lo hi, ∀ k,
      |coupledChemDivAdot p (conjugatePicardIter p u₀ n) s k| ≤ Mdot := by
  sorry
```

This is the coefficient derivative analogue of the logistic successor’s compact-bound argument. It is substantially harder because `coupledChemDivAdot` includes the resolver time derivative and spatial derivatives.

#### A4. Assemble chem-div `TimeC1On`

Once A1–A3 are landed, a constructor is straightforward:

```lean
noncomputable def coupledChemDivSource_timeC1On_of_fields_on
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {lo hi : ℝ}
    (F : CoupledChemDivTimeC1FieldsOn p u lo hi) :
    DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) lo hi := by
  -- windowed variant of coupledChemDivSource_timeC1_of_fields
  sorry
```

If avoiding a new windowed constructor, use a global version and `.toOn`:

```lean
noncomputable def coupledChemDivSource_timeC1On_of_fields_global
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {lo hi : ℝ}
    (F : CoupledChemDivTimeC1Fields p u) (hlo : 0 ≤ lo) :
    DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) lo hi :=
  ShenWork.IntervalDuhamelSourceTimeC1On.DuhamelSourceTimeC1.toOn
    (coupledChemDivSource_timeC1_of_fields F) lo hi hlo
```

### Option A final per-level theorem

```lean
noncomputable def bFormSourceTimeC1On_level_of_log_chem
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {n : ℕ} {lo hi : ℝ}
    (hlog : DuhamelSourceTimeC1On
      (coupledLogisticSourceCoeffs p (conjugatePicardIter p u₀ n)) lo hi)
    (hchem : DuhamelSourceTimeC1On
      (coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ n)) lo hi) :
    DuhamelSourceTimeC1On
      (bFormSourceCoeffs p (conjugatePicardIter p u₀ n)) lo hi :=
  bFormSource_duhamelSourceTimeC1On hlog hchem
```

## Option B — combined `bFormSourceTimeC1On_succ`

### Verdict

Technically possible, but not minimal. It only makes sense if you can prove a single physical derivative formula for the combined B-form source more easily than proving chem-div separately. In this repo, that is unlikely: the logistic half is already solved, while the chem-div half has a large existing structure and residual (`CoupledChemDivTimeC1Fields`, `CoupledChemDivLocalChainRule`, `ChemDivSolutionRegularityResidual`). A combined theorem would duplicate logistic work and still require all chem-div work.

### What the combined derivative would be

B-form source coefficients are coefficients of

```lean
logisticLifted p (u s) - p.χ₀ • coupledChemDivSourceLift p u s
```

So the time derivative candidate is:

```lean
bFormSourceAdot p u s k :=
  cosineCoeffs (logisticSourceTimeDerivativeLift p u s) k
    - p.χ₀ * coupledChemDivAdot p u s k
```

where the logistic derivative field is essentially the already landed `logisticSourceDot` from the restart representation route, while the chem-div derivative is `coupledChemDivAdot`.

Suggested definitions:

```lean
def bFormSourceDot
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (duLift : ℝ → ℝ → ℝ) (s x : ℝ) : ℝ :=
  -- schematic: logistic derivative minus chi times chem-div derivative lift
  duLift s x * (p.a - p.b * (1 + p.α) * (intervalDomainLift (u s) x) ^ p.α)
    - p.χ₀ * coupledChemDivTimeDerivativeLift p u s x

def bFormSourceAdot
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (duLift : ℝ → ℝ → ℝ) (s : ℝ) (k : ℕ) : ℝ :=
  cosineCoeffs (fun x => bFormSourceDot p u duLift s x) k
```

### Concrete missing lemmas for Option B

#### B1. Combined source coefficient derivative theorem

```lean
theorem bFormSourceCoeff_hasDerivWithinAt_of_combined_chain
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {lo hi : ℝ}
    (F : BFormCombinedTimeC1Fields p u lo hi)
    (s : ℝ) (hs : s ∈ Set.Icc lo hi) (k : ℕ) :
    HasDerivWithinAt
      (fun r => bFormSourceCoeffs p u r k)
      (bFormSourceAdot p u F.duLift s k)
      (Set.Icc lo hi) s := by
  sorry
```

This lemma requires both:

* the logistic coefficient chain rule already represented by `sourceTimeC1On_succ_of_sourceTimeC1On`, and
* the chem-div coefficient chain rule via `CoupledChemDivLocalChainRule`.

#### B2. Combined source value envelope

```lean
theorem bFormSourceCoeff_envelope_on
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {lo hi : ℝ}
    (F : BFormCombinedTimeC1Fields p u lo hi) :
    ∃ envelope : ℕ → ℝ,
      Summable envelope ∧
      ∀ s ∈ Set.Icc lo hi, ∀ k,
        |bFormSourceCoeffs p u s k| ≤ envelope k := by
  sorry
```

This combines the logistic envelope with chem-div weak-H²/decay envelope. The chem-div side is the hard part.

#### B3. Combined `adot` continuity and bound

```lean
theorem bFormSourceAdot_cont_bound_on
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {lo hi : ℝ}
    (F : BFormCombinedTimeC1Fields p u lo hi) :
    (∀ k, ContinuousOn (fun s => bFormSourceAdot p u F.duLift s k) (Set.Icc lo hi)) ∧
    ∃ Mdot, ∀ s ∈ Set.Icc lo hi, ∀ k,
      |bFormSourceAdot p u F.duLift s k| ≤ Mdot := by
  sorry
```

Again, this is no easier than combining the already solved logistic bound with the chem-div `coupledChemDivAdot` bound.

#### B4. Combined successor theorem

```lean
noncomputable def bFormSourceTimeC1On_succ
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {n : ℕ} {lo hi : ℝ}
    (F : BFormCombinedSuccData p u₀ n lo hi) :
    DuhamelSourceTimeC1On
      (bFormSourceCoeffs p (conjugatePicardIter p u₀ (n + 1))) lo hi := by
  -- call a generic DuhamelSourceTimeC1On constructor from coefficient derivative,
  -- envelope, and derivative bound.
  sorry
```

### Why Option B is not minimal

The combined theorem must prove all pieces Option A proves:

```text
logistic derivative + envelope + bound
chem-div derivative + weak-H²/decay + bound
addition/scalar closure
```

but without reusing the existing `sourceTimeC1On_succ_of_sourceTimeC1On` as cleanly. It may be useful as a final wrapper after Option A is built, but it should not be the core proof route.

## Option C — skip finite tower and prove limit directly

### Verdict

Not recommended as the first route. It looks shorter but shifts the burden into stronger uniform-limit hypotheses that are not supplied by geometric convergence.

The existing limit theorem is:

```lean
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

For Option C, set:

```lean
aSeq n s k := bFormSourceCoeffs p (conjugatePicardIter p u₀ n) s k

a s k := bFormSourceCoeffs p (conjugatePicardLimit p u₀ T) s k
```

### Concrete missing lemmas for Option C

#### C1. Coefficient convergence for B-form source

```lean
theorem bFormSourceCoeff_tendsto_of_conjugateIter
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T lo hi : ℝ}
    (Hinf : ConjugatePicardInfThresholdData p u₀ T)
    (hball : ∀ n s, 0 < s → s ≤ T → ∀ x,
      |conjugatePicardIter p u₀ n s x| ≤ M)
    (hregular : BFormSourceContinuityInU p M) :
    ∀ s ∈ Set.Icc lo hi, ∀ k,
      Tendsto
        (fun n => bFormSourceCoeffs p (conjugatePicardIter p u₀ n) s k)
        atTop
        (nhds (bFormSourceCoeffs p (conjugatePicardLimit p u₀ T) s k)) := by
  sorry
```

This requires Lipschitz/continuity of both:

* `u ↦ logisticLifted p u`, coefficientwise;
* `u ↦ coupledChemDivSourceLift p u`, coefficientwise, including resolver dependence.

The logistic part is plausible from value convergence and ball bounds. The chem-div part is not just value convergence: chem-div contains spatial derivatives of the resolver/flux.

#### C2. Per-iterate derivative identities

Even to use the limit theorem, every finite iterate must already have a derivative field:

```lean
theorem bFormSourceCoeff_hasDerivWithinAt_iter
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T lo hi : ℝ} (n : ℕ)
    (R : BFormIterSourceDerivativeData p u₀ n lo hi) :
    ∀ s ∈ Set.Icc lo hi, ∀ k,
      HasDerivWithinAt
        (fun r => bFormSourceCoeffs p (conjugatePicardIter p u₀ n) r k)
        (bFormIterAdot p u₀ n s k)
        (Set.Icc lo hi) s := by
  sorry
```

This is essentially the same finite-iterate source tower obligation. Option C cannot avoid it.

#### C3. Uniform convergence of derivative coefficients

This is the main blocker:

```lean
theorem bFormSourceAdot_tendstoUniformlyOn
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T lo hi : ℝ}
    (R : UniformBFormIterAdotConvergenceData p u₀ T lo hi) :
    ∀ k,
      TendstoUniformlyOn
        (fun n s => bFormIterAdot p u₀ n s k)
        (fun s => bFormLimitAdot p u₀ T s k)
        atTop
        (Set.Icc lo hi) := by
  sorry
```

Geometric convergence of iterates gives:

```lean
|u_{n+1}(t,x) - u_n(t,x)| ≤ K^n C₀
```

It does **not** give convergence of:

```lean
∂ₜ u_n,
∂ₓ u_n,
∂ₓₓ u_n,
∂ₜ resolver(u_n),
∂ₓ resolver(u_n),
∂ₜ chemDiv(u_n),
```

which are exactly the objects appearing in `bFormIterAdot`. This requires a stronger contraction in a regularity norm, or an independent restart/spectral derivative tower.

#### C4. Common envelope for all iterate source coefficients

```lean
theorem bFormSourceCoeff_uniform_summable_envelope
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T lo hi : ℝ}
    (R : UniformBFormSourceEnvelopeData p u₀ T lo hi) :
    ∃ envelope : ℕ → ℝ,
      Summable envelope ∧
      ∀ n s, s ∈ Set.Icc lo hi → ∀ k,
        |bFormSourceCoeffs p (conjugatePicardIter p u₀ n) s k| ≤ envelope k := by
  sorry
```

This requires uniform weak-H²/decay for the chem-div part plus uniform logistic source coefficient envelopes.

#### C5. Common derivative bound for all iterate `adot`s

```lean
theorem bFormSourceAdot_uniform_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T lo hi : ℝ}
    (R : UniformBFormIterAdotConvergenceData p u₀ T lo hi) :
    ∃ D, ∀ n s, s ∈ Set.Icc lo hi → ∀ k,
      |bFormIterAdot p u₀ n s k| ≤ D := by
  sorry
```

Again, this is derivative regularity, not a consequence of value contraction alone.

### Why Option C is risky

Option C still needs all finite-iterate derivative facts (`hderiv_each`) plus stronger uniform convergence of those derivative fields. It therefore does not actually skip the tower; it requires a stronger tower hidden behind `hadot_unif` and `hderiv_bound`.

## Minimal recommended infrastructure

### 1. Keep the existing logistic successor

No change:

```lean
sourceTimeC1On_succ_of_sourceTimeC1On
```

Use it as the logistic half of the B-form tower.

### 2. Add a chem-div finite-level source package API

```lean
abbrev ConjIterChemDivSourceTimeC1On
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (n : ℕ) (lo hi : ℝ) : Prop :=
  DuhamelSourceTimeC1On
    (coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ n)) lo hi

structure ConjIterChemDivTimeC1FieldsOn
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (n : ℕ) (lo hi : ℝ) where
  -- windowed version of CoupledChemDivTimeC1Fields specialized to conjugatePicardIter n
  Cchem : ℝ
  hCchem : 0 ≤ Cchem
  hH2 : ∀ s ∈ Set.Icc lo hi,
    ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann
      (coupledChemDivSourceLift p (conjugatePicardIter p u₀ n) s)
  hdecay : ∀ s ∈ Set.Icc lo hi, ∀ k : ℕ, 1 ≤ k →
    |cosineCoeffs (coupledChemDivSourceLift p (conjugatePicardIter p u₀ n) s) k|
      ≤ Cchem / ((k : ℝ) * Real.pi) ^ 2
  hzero : ∀ s ∈ Set.Icc lo hi,
    |cosineCoeffs (coupledChemDivSourceLift p (conjugatePicardIter p u₀ n) s) 0| ≤ Cchem
  hchain : CoupledChemDivLocalChainRule p (conjugatePicardIter p u₀ n)
  hadotcont : ∀ k, ContinuousOn
    (fun s => coupledChemDivAdot p (conjugatePicardIter p u₀ n) s k)
    (Set.Icc lo hi)
  MchemDot : ℝ
  hMdot : ∀ s ∈ Set.Icc lo hi, ∀ k,
    |coupledChemDivAdot p (conjugatePicardIter p u₀ n) s k| ≤ MchemDot
```

Then:

```lean
noncomputable def conjIterChemDivSource_timeC1On_of_fields
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {n : ℕ} {lo hi : ℝ}
    (F : ConjIterChemDivTimeC1FieldsOn p u₀ n lo hi) :
    ConjIterChemDivSourceTimeC1On p u₀ n lo hi := by
  -- windowed version of coupledChemDivSource_timeC1_of_fields
  sorry
```

### 3. Combine per-level parts

```lean
noncomputable def conjIterBFormSource_timeC1On_of_parts
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {n : ℕ} {lo hi : ℝ}
    (hlog : DuhamelSourceTimeC1On
      (coupledLogisticSourceCoeffs p (conjugatePicardIter p u₀ n)) lo hi)
    (hchem : DuhamelSourceTimeC1On
      (coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ n)) lo hi) :
    DuhamelSourceTimeC1On
      (bFormSourceCoeffs p (conjugatePicardIter p u₀ n)) lo hi :=
  bFormSource_duhamelSourceTimeC1On hlog hchem
```

### 4. Limit producer for `hsrcBDirect`

Once finite-level B-form source packages have uniform limit data, produce the bank field:

```lean
noncomputable def limit_bFormSourceTimeC1On_of_uniform_limit
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    (L : BFormSourceUniformLimitData p u₀ T 0 T) :
    DuhamelSourceTimeC1On
      (bFormSourceCoeffs p (conjugatePicardLimit p u₀ T)) 0 T :=
  ShenWork.IntervalMildPicardLimitRegularityOn.duhamelSourceTimeC1On_of_uniform_limit
    L.hconv L.hderiv_each L.hadot_unif L.hadot_cont
    L.henv_summable L.henv_bound L.hderiv_bound
```

But this requires a nontrivial `BFormSourceUniformLimitData` bundle with `hadot_unif`. If that bundle is not close, carry `hsrcBDirect` as the bank residual and work on Option A finite tower first.

## Final recommendation

Choose **Option A**.

The minimal missing infrastructure is **not** a new combined B-form successor. It is a chem-div source tower for finite B-form iterates, with these concrete missing lemmas:

1. finite-iterate `CoupledChemDivLocalChainRule`,
2. finite-iterate chem-div weak-H²/Neumann coefficient decay (`hH2`, `hdecay`, `hzero`),
3. finite-iterate `coupledChemDivAdot` continuity and uniform bound on windows,
4. a windowed constructor `coupledChemDivSource_timeC1On_of_fields_on` or a global-to-window wrapper,
5. per-level combiner using existing `bFormSource_duhamelSourceTimeC1On`,
6. for the limit only: uniform convergence of B-form source derivative coefficients (`hadot_unif`) plus common envelopes/bounds.

Option B is not minimal because it proves the same chem-div facts inside a combined theorem while duplicating the logistic successor. Option C is not a shortcut because `duhamelSourceTimeC1On_of_uniform_limit` requires derivative convergence and common derivative bounds that geometric iterate convergence does not provide.
