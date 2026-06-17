═══ BRIDGE cron | 4d973f36 | 8444 chars 1365 words 201 lines | 512s | prov=network | OK ═══
═══ BRIDGE cron | 4d973f36 | 8444 chars 1365 words 201 lines | 512s | prov=network | OK ═══
**Best Lean route:** add a **functional lower barrier** to the fixed-point set, not a uniform positive floor and not a degree argument.

Use a set like

```lean
def InPinnedTrap (κ M : ℝ) (φ : ℝ → ℝ) (U : ℝ → ℝ) : Prop :=
  InMonotoneWaveTrapSet κ M U ∧ ∀ x, φ x ≤ U x
```

with `φ = lowerBarrierPlateau κ κtilde D` or whatever lower solution your Rothe/Schauder map preserves. This excludes zero while still allowing decay to zero at `+∞`. The existing code already proves the key point: `lowerBarrierPlateau` is strictly positive at every finite `x` under `0 < κ`, `0 < κtilde - κ`, `0 < D`. fileciteturn37file0L7-L17 It is also bounded by the exponential upper barrier, so it is compatible with the trap geometry rather than being an impossible uniform floor. fileciteturn37file0L19-L35

### (a) Excluding zero

The cleanest formal mechanism is **(i) lower barrier**, provided you can prove invariance:

```lean
hT_floor :
  ∀ U, InPinnedTrap κ M φ U → InPinnedTrap κ M φ (Tmap U)
```

Then Schauder is applied to `InPinnedTrap κ M φ`, not to bare `InMonotoneWaveTrapSet κ M`. The fixed point satisfies

```lean
∀ x, φ x ≤ U x
```

and since `φ x > 0`, you immediately get

```lean
∀ x, 0 < U x
```

This fits the existing Lean diagnosis exactly. The trap itself only contains `0 ≤ U x` and `U x ≤ upperBarrier κ M x`; it does **not** contain strict positivity. fileciteturn38file0L52-L65 The repo already proves that strict positivity is not derivable from trap membership, because the zero profile is trapped. fileciteturn34file0L78-L87 It also proves that the left limit `U → 1` is not a trap consequence for the same reason. fileciteturn34file0L89-L101

A phase condition,

```lean
def PhaseTrap (κ M θ : ℝ) (U : ℝ → ℝ) : Prop :=
  InMonotoneWaveTrapSet κ M U ∧ U 0 = θ
```

is mathematically standard for traveling waves because translation invariance leaves the wave location undetermined, and one often pins it with a condition such as `U(0)=1/2`. citeturn106513search2 But in this Lean development it is less clean unless your map is explicitly phase-normalized. A raw elliptic/Rothe map will not preserve `U 0 = θ`; to force it you would need a shift operator, a crossing lemma, continuity of the selected shift, and proof that shifting does not break the anchored upper barrier `min(M, exp(-κx))`. That is much more geometry than adding `φ ≤ U`.

A degree/index argument is the least attractive route here. It would require a fixed-point index or degree theory around the zero branch. The current project is already carrying explicit Schauder principles because Mathlib lacks the general Schauder–Tychonoff theorem, Brouwer, KKM, and related topological infrastructure. fileciteturn44file0L17-L32 So degree would be a large new topological subsystem, not a small patch.

So the Lean-friendly hierarchy is:

```text
best:     lower barrier φ ≤ U, preserved by Tmap
okay:     phase condition U(0)=θ, only if Tmap is already phase-normalized
avoid:    degree/index
wrong:    uniform η ≤ U for all x
```

### (b) Strict positivity of a nontrivial solution

Yes: for a **1D moving-frame ODE**, the clean fact is the ODE uniqueness version of the strong maximum principle.

The lemma you want is not “trap implies positivity”; it should be something like:

```lean
theorem stationary_nonneg_nontrivial_pos
    (hstat : StationaryEq U)
    (hreg : enough_regular_for_ODE_uniqueness U)
    (hnonneg : ∀ x, 0 ≤ U x)
    (hnontriv : ∃ x, U x ≠ 0) :
    ∀ x, 0 < U x := by
  ...
```

The proof skeleton is:

```lean
by_contra hnot
obtain ⟨x0, hx0_zero⟩ : ∃ x0, U x0 = 0 := ...
have hderiv_zero : deriv U x0 = 0 :=
  derivative_zero_at_local_min hnonneg hx0_zero
-- Write the stationary equation as a first-order ODE system.
-- Initial data `(U x0, U' x0) = (0,0)` produce the zero solution.
-- Picard-Lindelöf uniqueness gives U ≡ 0, contradiction.
```

This is usually cleaner than formalizing a Hopf lemma. In 1D, Hopf/strong maximum principle is overkill; Cauchy uniqueness is a local theorem about an ODE system. Your repo already has a first-order traveling-wave ODE vector field and proves it is `ContDiffAt ℝ 1`, hence suitable for Picard–Lindelöf data. fileciteturn49file0L40-L50 fileciteturn49file0L160-L205

The minimal analytic assumptions are:

```lean
-- local ODE form
Y' = F Y

-- enough smoothness / local Lipschitz
ContDiff ℝ 1 F

-- zero invariance
F E0 = 0

-- identification of U with coordinate 0 of Y
U x = Y x 0
```

The existing `TravelingWaveODE` file already has the equilibrium `E0` and proves `vectorField p E0 = 0`. fileciteturn49file0L37-L50 fileciteturn49file0L64-L76

If you use the **lower-barrier trap**, you may not need this positivity lemma for the final `hpos`, because `φ_pos` plus `φ ≤ U` gives positivity immediately. The ODE-uniqueness lemma is still useful as a fallback for a phase-only construction: phase gives `U ≠ 0`, and uniqueness upgrades nonnegative nontrivial to strictly positive everywhere.

### (c) Getting `U(-∞)=1`

Your monotonicity pin is exactly right. The repo already has the right structure:

1. A monotone trapped profile has a finite left limit `L`, with `0 ≤ L ≤ M`. fileciteturn33file0L73-L97
2. If the profile is pinned positively at the left, then the left limit is positive. fileciteturn33file0L99-L104
3. If `reactionFun α L = 0` and `0 < L`, then `L = 1`. fileciteturn33file0L106-L134

You do **not** need pointwise positivity for the left pin. Nontriviality plus monotonicity is enough:

```lean
def NontrivialNonneg (U : ℝ → ℝ) : Prop :=
  ∃ x, 0 < U x

theorem InMonotoneWaveTrapSet.strictlyPositiveAtLeft_of_nontrivial
    {κ M : ℝ} {U : ℝ → ℝ}
    (hU : InMonotoneWaveTrapSet κ M U)
    (hnontriv : ∃ x, 0 < U x) :
    StrictlyPositiveAtLeft U := by
  rcases hnontriv with ⟨x0, hx0⟩
  refine ⟨U x0, hx0, ?_⟩
  refine eventually_atBot.2 ⟨x0, ?_⟩
  intro x hx
  -- x ≤ x0 and U antitone, so U x0 ≤ U x
  exact hU.antitone hx
```

Then define the left-limit theorem with nontriviality rather than a global floor:

```lean
theorem InMonotoneWaveTrapSet.tendsto_atBot_one_of_limit_root_and_nontrivial
    {κ M : ℝ} {U : ℝ → ℝ} (p : CMParams)
    (hU : InMonotoneWaveTrapSet κ M U)
    (hnontriv : ∃ x, 0 < U x)
    (hroot : ∀ L : ℝ, Tendsto U atBot (𝓝 L) → reactionFun p.α L = 0) :
    Tendsto U atBot (𝓝 1) := by
  rcases monotoneTrap_left_limit_exists hU with ⟨L, hlim, _hL0, _hLM⟩
  have hleft : StrictlyPositiveAtLeft U :=
    hU.strictlyPositiveAtLeft_of_nontrivial hnontriv
  have hL : 0 < L := hleft.limit_pos hlim
  have hα : 0 < p.α := lt_of_lt_of_le zero_lt_one p.hα
  exact tendsto_atBot_one_of_reaction_root_pin hα hlim hL (hroot L hlim)
```

This is the same proof pattern already in `WaveTrapProps`, except the input should be weakened from `∀ x, 0 < U x` or `PaperPositiveInitialDatum U` to `∃ x, 0 < U x`. The existing theorem `InMonotoneWaveTrapSet.tendsto_atBot_one_of_limit_root_and_pos` does this using pointwise positivity, and the “pin” step is isolated. fileciteturn33file0L147-L159

### Concrete recommendation

Patch the construction as follows.

First, define the pinned fixed-point class:

```lean
def InLowerPinnedMonotoneTrap
    (κ M : ℝ) (φ : ℝ → ℝ) (U : ℝ → ℝ) : Prop :=
  InMonotoneWaveTrapSet κ M U ∧ ∀ x, φ x ≤ U x
```

Then prove the self-map data for this class, not the bare trap:

```lean
hdata_pinned :
  FrozenStationaryMapSchauderData p c lam
    (InLowerPinnedMonotoneTrap κ M φ) Tmap
```

The only genuinely new field is lower-barrier invariance:

```lean
∀ U, InLowerPinnedMonotoneTrap κ M φ U →
  ∀ x, φ x ≤ Tmap U x
```

Then Schauder returns

```lean
∃ U, InLowerPinnedMonotoneTrap κ M φ U ∧ Tmap U = U
```

and zero is automatically impossible:

```lean
have hpos : ∀ x, 0 < U x :=
  fun x => lt_of_lt_of_le (φ_pos x) (hU.2 x)

have hnontriv : ∃ x, 0 < U x := ⟨0, hpos 0⟩
```

Finally, use the already-isolated left-limit root route:

```lean
have hlim_neg : Tendsto U atBot (𝓝 1) :=
  InMonotoneWaveTrapSet.tendsto_atBot_one_of_limit_root_and_nontrivial
    p hU.1 hnontriv hroot
```

In summary: **lower barrier in the Schauder domain** is the cleanest Lean-formalizable nontriviality mechanism. **ODE uniqueness** is the cleanest 1D route from nonnegative nontrivial stationary solution to strict positivity when no pointwise lower barrier is carried. And **nontriviality + monotonicity + reaction-root at the left limit** is the clean pin forcing `U(-∞)=1`.
