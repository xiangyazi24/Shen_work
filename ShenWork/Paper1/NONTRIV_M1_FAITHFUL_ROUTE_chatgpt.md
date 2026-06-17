═══ BRIDGE cron | 0224a6a2 | 12281 chars 1896 words 273 lines | 620s | prov=network | OK ═══
═══ BRIDGE cron | 0224a6a2 | 12281 chars 1896 words 273 lines | 620s | prov=network | OK ═══
The key correction is: **the paper does not exclude zero by a generic Schauder theorem on the bare trap.** It excludes zero because the actual fixed-point set/map carries additional nonzero structure. In the negative-sensitivity existence proof, that structure is a lower solution/trapping interval; in Lean, if that exact lower-solution lemma is not available, the next-best replacement is a **map-specific nontriviality pin**, not a generic “nontrivial Schauder principle.”

## 1. What happens at `m = 1`?

For the paper’s χ≤0 construction, the nontriviality mechanism is still a **sub-/super-solution trapping construction**, not phase, degree, or a phase-plane heteroclinic. The paper explicitly says it proves the χ≤0 theorem by modified super-/sub-solution arguments, including for the previously studied `m = α = γ = 1` case. citeturn883680view1

More concretely, the paper builds a lower-trapped set

```text
E_{κ,M} = { u ∈ C_b^unif(R) | U^-_{κ,κ~,D}(x) ≤ u(x) ≤ U^+_{κ,M}(x) }
```

and then a monotone subset `E'_{κ,M}`. citeturn883680view1 The fixed-point map is not “solve the frozen stationary equation from arbitrary zero-like data”; it is a parabolic long-time map starting from the upper barrier, and comparison gives

```text
U^-_{κ,κ~,D}(x) ≤ u(t,x; U^+_{κ,1}, u) ≤ U^+_{κ,1}(x).
```

citeturn201266view1 Then Schauder gives a fixed point in that already lower-pinned set. citeturn201266view2 After the fixed point is obtained, the lower bound persists:

```text
U^-_{κ,κ~,D}(x) ≤ U*(x) ≤ U^+_{κ,1}(x).
```

citeturn201266view2

So the zero function is excluded because it is **not in the paper’s actual fixed-point set**. It may be in the bare monotone trap `{0 ≤ U ≤ Ubar, antitone}`, but the paper’s `E'` has a nonzero lower bound.

Your `m=1` obstruction is real for the **particular plateau estimate**

```text
C(1 - C^α) ≥ |χ| C^m B₂
```

because at `m=1` small `C` does not separate reaction and chemotaxis orders. But the paper’s χ≤0 lower-solution proof is not just that crude plateau budget. It uses the χ≤0 sign structure and estimates for `V` and `V_x`; for the two-exponential lower solution it proves `A(U^-;u) ≥ 0` once `D` is large enough, and it also states that a sufficiently small constant `d` is a subsolution. citeturn787634view1turn883680view0 In particular, the paper allows constants depending on `|χ|` and on the speed/decay parameters; it does **not** require small `|χ|`. The theorem’s statement covers all `χ ≤ 0` for sufficiently large speed, with `m, α, γ ≥ 1`, and explicitly includes the `m=α=γ=1` lineage. citeturn584796view0

So the audit answer is:

```text
If the Lean lower-barrier proof fails at m=1, it means that lower barrier is not the paper’s actual subsolution lemma, or the frozen operator/sign has been over-abstracted. The paper’s faithful route is still lower-solution trapping, but the lemma must be the paper’s A(W;u) estimate, not the crude |V''| plateau budget.
```

## 2. What should be formalized in Lean?

### Do not formalize a generic “nontrivial Schauder on the bare trap”

Your repo already proves that this principle is false. It defines

```lean
LocalUniformNontrivialSchauderFixedPointPrinciple trap
```

as a Schauder principle that returns a fixed point with `ProfileNontrivial`, then refutes it on the bare monotone trap by the constant-zero self-map. fileciteturn109file0L65-L77 fileciteturn109file0L101-L143

That is exactly the right diagnosis: from bare trap invariance, local-uniform continuity, and compact range alone, zero cannot be excluded.

### Best faithful Lean route

Formalize the paper’s actual fixed-point set:

```lean
def InPaperLowerTrap
    (κ M : ℝ) (Uminus Uplus : ℝ → ℝ) (U : ℝ → ℝ) : Prop :=
  IsCUnifBdd U ∧
  (∀ x, Uminus x ≤ U x ∧ U x ≤ Uplus x) ∧
  Antitone U
```

Then prove the fixed-point data directly on this set:

```lean
hdata :
  FrozenStationaryMapSchauderData p c lam
    (InPaperLowerTrap κ M Uminus Uplus) Tmap
```

The crucial analytic lemma is not “global positive plateau subsolution from crude `B₂` bound”; it should mirror the paper’s Lemma 4.2:

```lean
theorem paper_lowerSolution_invariant_chi_nonpos
    (hχ : p.χ ≤ 0)
    (hspeed : c > cStar ...)
    (hD : D ≥ D_min ...)
    :
    ∀ u ∈ E',  -- frozen profile in the lower/upper order interval
      lowerSolution ≤ parabolicLongTimeMap u
```

The repo already has the abstract lower-pinned infrastructure:

```lean
def InLowerPinnedMonotoneTrap
    (κ M : ℝ) (φ : ℝ → ℝ) (U : ℝ → ℝ) : Prop :=
  InMonotoneWaveTrapSet κ M U ∧ ∀ x, φ x ≤ U x
```

and it proves that a positive lower pin gives nontriviality and pointwise positivity. fileciteturn109file0L145-L175 It also has a wrapper that turns a lower-pinned Schauder fixed point into a wave profile, with right limit from the upper barrier, positivity from the pin, and left limit from the stationary-flat/root argument. fileciteturn111file0L44-L83

So the cleanest faithful task is to replace the crude lower-barrier proof with a theorem matching the paper’s `U^-_{κ,κ~,D}` construction. The paper’s construction also fixes the wave’s phase implicitly by the exponential asymptotic/trap normalization at `+∞`; it is not adding a phase condition `U(0)=θ`.

### If the full lower-solution lemma is too hard

Use a **map-specific nontriviality theorem**, not a new Schauder principle. For example:

```lean
def MapProducesNontrivial
    (trap : (ℝ → ℝ) → Prop)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ) : Prop :=
  ∀ U, trap U → Tmap U = U → ProfileNontrivial U
```

or the stronger, easier-to-use variant:

```lean
def MapHasPointPin
    (trap : (ℝ → ℝ) → Prop)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ) : Prop :=
  ∃ x0 δ, 0 < δ ∧ ∀ U, trap U → δ ≤ Tmap U x0
```

Then ordinary Schauder plus `MapProducesNontrivial` gives a nontrivial fixed point:

```lean
theorem exists_self_frozen_stationary_nontrivial
    (hprinciple : LocalUniformSchauderFixedPointPrinciple trap)
    (hdata : FrozenStationaryMapSchauderData p c lam trap Tmap)
    (hGreen : ∀ U, trap U → Tmap U = U → GreenIdentity p c lam U)
    (hnontriv : ∀ U, trap U → Tmap U = U → ProfileNontrivial U) :
    ∃ U, trap U ∧ ProfileNontrivial U ∧
      (∀ x, frozenWaveOperator p c U U x = 0) := by
  obtain ⟨U, hU, hfix⟩ :=
    hprinciple Tmap hdata.invariant hdata.continuousOn hdata.compactRange
  have hstat :=
    FrozenStationaryMapSchauderData.exists_self_frozen_stationary
      hdata hprinciple hGreen
  -- or inline the existing proof
  exact ⟨U, hU, hnontriv U hU hfix, ...⟩
```

Then your existing strong maximum principle machinery closes the positivity gap. The repo defines `ProfileNontrivial`, `StationaryStrongMaxPrinciple`, and the ODE-uniqueness bridge; the theorem `stationaryStrongMaxPrinciple_of_odeUniqueness` turns “zero contact propagates to zero everywhere” into strict positivity for any nontrivial stationary trapped profile. fileciteturn106file0L65-L99 fileciteturn107file0L44-L83

This is probably the **least Lean pain** if you cannot yet formalize the exact lower solution: carry a theorem saying the *actual* map cannot have zero as a fixed point, then use the already-built SMP/root-pin layer. The existing wrapper

```lean
b1_chiNeg_existence_of_schauderData_stationary_nontrivial_rootPin
```

already expresses this idea, except it assumes the too-strong broad `LocalUniformNontrivialSchauderFixedPointPrinciple`; I would weaken it to ordinary Schauder plus `MapProducesNontrivial`. fileciteturn111file0L6-L42

## 3. How the options compare

### (a) Phase / anchoring condition

A phase condition like

```lean
U 0 = θ
```

does exclude zero. It is standard for translation-invariant traveling-wave problems; for example, classical traveling-wave ODE discussions use a condition such as `θ(0)=1/2` to fix the wave location. citeturn221239search4

But it is **not** what the paper appears to use. The paper instead anchors the wave through the upper/lower exponential asymptotic and obtains Schauder in that ordered set. citeturn883680view1 A phase-normalized Lean map would require:

```lean
def shift (a : ℝ) (U : ℝ → ℝ) : ℝ → ℝ := fun x => U (x + a)

def crossingShift (θ : ℝ) (U : ℝ → ℝ) : ℝ :=
  -- choose a with U a = θ

def normalizedMap U := shift (crossingShift θ (Tmap U)) (Tmap U)
```

Then you must prove:

```lean
∃ a, Tmap U a = θ
```

plus uniqueness or a canonical choice of `a`, continuity of the selected shift, compactness after shifting, and invariance of the anchored trap. The anchored exponential upper barrier `min(M,e^{-κx})` is not translation-invariant, so shifting can break the trap unless you redesign the trap with a free amplitude/phase parameter. That is a lot of new geometry.

So phase is viable, but not the shortest faithful path.

### (b) Degree / Leray–Schauder

This is not attractive in the current Lean codebase. You would need a fixed-point index or topological degree theory strong enough to isolate the zero branch. The repo already shows the generic nontrivial fixed-point principle is false on the bare trap, so a degree proof would have to use detailed map-specific structure anyway. fileciteturn109file0L101-L143

I would not choose this route.

### (c) Phase-plane / heteroclinic

If you actually prove a heteroclinic orbit from `E1` to `E0`, it is automatically nontrivial. But this is not a scalar 2D phase plane. With the elliptic chemical variable included, the moving-frame system is a 4D autonomous ODE in

```text
(U, U', V, V')
```

and the repo’s `TravelingWaveODE.vectorField` already reflects exactly that. It has equilibria

```lean
E1 = ![1,0,1,0]
E0 = ![0,0,0,0]
```

and proves both are equilibria. fileciteturn112file0L3-L42

For `m=1`, the vector field is smooth enough near zero, so the heteroclinic statement makes sense. But proving existence of the global connection is a major dynamical-systems/shooting/invariant-manifold theorem. It is not obviously easier than the paper’s parabolic/Schauder construction, and it is less faithful to the paper.

So: yes, a heteroclinic proof would solve nontriviality, but no, it is not the clean formal route unless you already have the invariant-manifold machinery.

### (d) Compact-interval positive pin

This is the best fallback if the full lower barrier is too hard. You do **not** need a global subsolution to get strict positivity; you only need:

```lean
ProfileNontrivial U := ∃ x, 0 < U x
```

Then the stationary strong maximum principle gives `∀ x, 0 < U x`, and your root-pin theorem gives `U(-∞)=1`.

A map-specific compact pin can be stated as:

```lean
def SchauderMapCompactPin
    (trap : (ℝ → ℝ) → Prop)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ) : Prop :=
  ∃ x0 δ, 0 < δ ∧ ∀ U, trap U → δ ≤ Tmap U x0
```

Then for a fixed point:

```lean
have hnontriv : ProfileNontrivial U :=
  ⟨x0, lt_of_lt_of_le hδ (by simpa [hfix] using hpin U hU)⟩
```

This is much lighter than preserving a global lower barrier. The analytic burden is proving that the actual `Tmap` sends every trapped input to something positive at one finite location. For the paper’s parabolic-long-time map from the upper barrier, this should come from comparison/persistence/stabilization, but it is still map-specific.

## Bottom-line recommendation

For **paper fidelity**, formalize the actual Shen construction:

```text
lower/upper order interval E'κ,M with U^- ≤ U ≤ U+
parabolic long-time map Tκ,M
comparison: U^- ≤ Tκ,M u ≤ U+
Schauder fixed point in E'κ,M
```

The paper’s nontriviality is not phase or degree; it is the lower bound in `E'κ,M`. The χ≤0 `m=1` case is covered because the constants `D`, `d`, and the speed threshold absorb `|χ|`; the proof is not based on a small-`C` separation of reaction order `C` versus chemotaxis order `C^m`. citeturn787634view1turn883680view1

For **least Lean pain right now**, replace the false broad nontrivial Schauder principle with a **map-specific nontriviality premise**:

```lean
∀ U, trap U → Tmap U = U → ProfileNontrivial U
```

or the stronger point pin

```lean
∃ x0 δ, 0 < δ ∧ ∀ U, trap U → δ ≤ Tmap U x0.
```

Then reuse the existing chain:

```text
ProfileNontrivial
→ StationaryStrongMaxPrinciple
→ ∀x, 0 < U x
→ monotone/root pin
→ U(-∞)=1.
```

That chain is already largely present in the repo. fileciteturn106file0L65-L99 fileciteturn107file0L44-L83
