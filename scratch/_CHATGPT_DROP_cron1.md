# ChatGPT git-drop (cron1)

## Q293 — χ₀<0 faithful EWA construction: lifespan `δ`, windowed source packages, and who supplies them

### Executive verdict

Yes: in the faithful obligation

```lean
ChiNegDatumUniformConstructionFaithful p
```

the lifespan `δ` is exactly the horizon of both

```lean
u_star : EWA δ 1
```

and

```lean
CoupledDuhamelReducedClassicalCore p δ u0 (realSlice u_star).
```

There is no second independent `T` at that level. If you instantiate

```lean
realSlice_reducedCore_wired
```

with `T := δ`, then its conclusion is exactly

```lean
CoupledDuhamelReducedClassicalCore p δ u0 (realSlice u_star).
```

Changing `realSlice_reducedCore_wired` from global

```lean
DuhamelSourceTimeC1 ...
```

to windowed

```lean
DuhamelSourceTimeC1On ... 0 T
```

is type-aligned with the faithful target: in the final per-datum call, `T` should be the same selected lifespan `δ`.

But the current architecture makes `realSlice_reducedCore_wired` a **consumer** of source time-regularity packages, not a producer. So the intended route is:

```text
caller / frontier producer builds hchemOn, hlogOn on [0, δ]
  → passes them into realSlice_reducedCore_wired (T := δ)
  → obtains CoupledDuhamelReducedClassicalCore p δ u0 (realSlice u_star)
  → supplies the body of ChiNegDatumUniformConstructionFaithful.
```

Not:

```text
realSlice_reducedCore_wired internally constructs hchemOn/hlogOn.
```

---

## 1. The faithful obligation already pins the horizon

The definition is:

```lean
def ChiNegDatumUniformConstructionFaithful (p : CM2Params) : Prop :=
  ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
    ∀ {u0 : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u0 →
      (∀ x, |u0 x| ≤ M) →
        ∃ u_star : EWA δ 1,
          CoupledDuhamelReducedClassicalCore p δ u0 (realSlice u_star)
```

So the selected `δ` is not just a contraction time; it is also the exact `T` index of the reduced core.

This also means that if your source packages are windowed, the natural target is:

```lean
hchemOn : DuhamelSourceTimeC1On
  (coupledChemDivSourceCoeffs p (realSlice u_star)) 0 δ

hlogOn : DuhamelSourceTimeC1On
  (coupledLogisticSourceCoeffs p (realSlice u_star)) 0 δ
```

or, inside a polymorphic theorem with implicit `{T}`, the same statements with `0 T`.

---

## 2. `realSlice_reducedCore_wired` is polymorphic in the same `T`

The current fetched signature is polymorphic in `{T : ℝ}` and returns:

```lean
CoupledDuhamelReducedClassicalCore p T u₀ (realSlice u_star)
```

with

```lean
u_star : EWA T 1
```

Thus, if the caller has

```lean
u_star : EWA δ 1
```

Lean will infer or accept

```lean
T := δ
```

and the conclusion becomes the required faithful body:

```lean
CoupledDuhamelReducedClassicalCore p δ u₀ (realSlice u_star)
```

### Naming trap: two different “δ” roles

Inside `realSlice_reducedCore_wired` there are local floor/contraction variables named `δ`, `δ'`, `ρ`, `ρ'`:

```lean
{u₀E : WA 1} {δ ρ : ℝ} (hδρ : 0 < δ - ρ)
...
{L_Q L_G δ' ρ' : ℝ} (hδ'pos : 0 < δ')
...
(hfloorδ : δ' = T) (hfloor : UniformFloor u_star δ')
```

These are not a second lifespan. They are floor/contraction parameters. The lifespan is the implicit theorem parameter `T`. In a clean caller, use names like:

```lean
δLife : ℝ
δFloor : ℝ
ρBall : ℝ
```

and instantiate:

```lean
T := δLife
hfloorδ : δFloor = δLife
```

The target core still lands on `δLife`.

---

## 3. What currently carries source time-C¹ into the reduced core?

In the fetched current version, `realSlice_reducedCore_wired` explicitly **takes** the source time-C¹ packages as inputs:

```lean
(hchem : DuhamelSourceTimeC1
  (coupledChemDivSourceCoeffs p (realSlice u_star)))
(hlog : DuhamelSourceTimeC1
  (coupledLogisticSourceCoeffs p (realSlice u_star)))
```

It does not construct them internally.

It uses them immediately to build the `pde_u` and classical-regularity feeder fields:

```lean
have htime := realSlice_htime_of_atoms p (realSlice u_star) u₀cos hu0bd hchem hlog hrealizes
...
have hsum_chem := realSlice_hsum_chem_of_atoms p (realSlice u_star) hchem (T := T)
have hsum_log := realSlice_hsum_log_of_atoms p (realSlice u_star) hlog (T := T)
...
have htimeDeriv := realSlice_timeDeriv_of_atoms p (realSlice u_star) u₀cos hu0bd hchem hlog hrealizes
have hdiffU := realSlice_diffU_of_atoms p (realSlice u_star) u₀cos hu0bd hchem hlog hrealizes
...
exact realSlice_reducedCore ... hchem hlog ...
```

So if you change `realSlice_reducedCore_wired` to use `DuhamelSourceTimeC1On`, the direct dependencies to update are not only the theorem signature but also the helper lemmas it calls:

```lean
realSlice_htime_of_atoms
realSlice_hsum_chem_of_atoms
realSlice_hsum_log_of_atoms
realSlice_timeDeriv_of_atoms
realSlice_diffU_of_atoms
realSlice_classicalRegularity
realSlice_reducedCore
```

or you need local adapter lemmas that derive the exact local/interior facts those helpers need from

```lean
DuhamelSourceTimeC1On ... 0 T.
```

The current helper stack is global-package-shaped. For example, `realSlice_htime_of_atoms` calls `fullSourceCoeff_timeDeriv_eq`, and that theorem currently requires global:

```lean
(hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
(hlog  : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u))
```

So the windowed refactor must propagate through the time-derivative bridge, or you must provide an On-to-local derivative bridge for every interior `t ∈ Ioo 0 T`.

---

## 4. Does `ChiNegDatumUniformConstructionFaithful` itself call `realSlice_reducedCore_wired`?

No. In the fetched repo, `ChiNegDatumUniformConstructionFaithful` is only a **Prop**. It does not construct `u_star` or call `realSlice_reducedCore_wired`.

The theorem

```lean
chiNeg_residual_of_datumUniformFaithful
```

uses the faithful construction by destructuring it:

```lean
obtain ⟨δ, hδ, hbody⟩ := hU M hM
...
obtain ⟨u_star, C⟩ := hbody hu0 hbd
```

Then it uses the supplied core `C`:

```lean
have hreg : RegularityBootstrap p δ u0 (realSlice u_star) :=
  regularityBootstrap_of_coupledDuhamel_reducedClassicalCore p C
```

and rebuilds the classical solution at exactly the same `δ`:

```lean
exact ⟨realSlice u_star, v,
  IsPaper2ClassicalSolution.of_components hδ hclassreg hpos hvnn hpde_u hpde_v hbc,
  htrace⟩
```

So the actual production of `u_star` and the call to `realSlice_reducedCore_wired` must happen in a future/frontier theorem that proves `ChiNegDatumUniformConstructionFaithful p`. That future theorem is where the windowed source packages should be produced and passed.

---

## 5. Answer to the caller/internal question

The correct architecture is **(a)**:

```text
caller of realSlice_reducedCore_wired produces the windowed source packages
from coupledChemDivSource_timeC1On_of_EWA / logistic On producers / residuals,
then passes them into realSlice_reducedCore_wired.
```

The current `realSlice_reducedCore_wired` is intentionally a wiring theorem. Its module doc says it “consumes every banked discharge” and re-emits the reduced core while carrying the irreducible residuals. It is not a producer of `hchem`/`hlog`; those are listed as the source time-C¹ frontier.

After your refactor, its role should remain the same:

```lean
(hchemOn : DuhamelSourceTimeC1On
  (coupledChemDivSourceCoeffs p (realSlice u_star)) 0 T)
(hlogOn : DuhamelSourceTimeC1On
  (coupledLogisticSourceCoeffs p (realSlice u_star)) 0 T)
```

are inputs, not internally synthesized fields.

---

## 6. What the future faithful producer should look like

The missing producer for the faithful construction should have this shape:

```lean
theorem chiNeg_datumUniformFaithful_of_frontier
    (p : CM2Params)
    -- regime / contraction / datum-uniform inputs
    (...)
    -- source package producers or residuals, now windowed
    (... produce hchemOn/hlogOn on [0, δLife] ...)
    -- all remaining reduced-core inputs
    : ChiNegDatumUniformConstructionFaithful p := by
  intro M hM
  obtain ⟨δLife, hδLife, fixedPointData⟩ := ...
  refine ⟨δLife, hδLife, ?_⟩
  intro u0 hu0 hbd
  obtain ⟨u_star, hfix, ...⟩ := fixedPointData u0 hu0 hbd

  have hchemOn : DuhamelSourceTimeC1On
      (coupledChemDivSourceCoeffs p (realSlice u_star)) 0 δLife := by
    -- from coupledChemDivSource_timeC1On_of_EWA or residual producer
    ...

  have hlogOn : DuhamelSourceTimeC1On
      (coupledLogisticSourceCoeffs p (realSlice u_star)) 0 δLife := by
    -- from logistic On producer
    ...

  have C : CoupledDuhamelReducedClassicalCore p δLife u0 (realSlice u_star) := by
    exact realSlice_reducedCore_wired
      (T := δLife)
      (p := p) (u_star := u_star) (u₀ := u0) ...
      hchemOn hlogOn ...

  exact ⟨u_star, C⟩
```

The important part is that `hchemOn` and `hlogOn` are built **before** the call to `realSlice_reducedCore_wired`, not inside it.

---

## 7. Refactor warning: On-package sufficiency

Changing only the final wired theorem signature from global to On will not be enough unless the downstream feeder lemmas are also made On-aware.

The easiest proof strategy is probably to add On variants/adapters for the few facts used at interior times:

```lean
fullSourceCoeff_hasDerivAt_time_on
realSlice_htime_of_atoms_on
realSlice_hsum_chem_of_atoms_on
realSlice_hsum_log_of_atoms_on
realSlice_timeDeriv_of_atoms_on
realSlice_diffU_of_atoms_on
realSlice_classicalRegularity_on
realSlice_reducedCore_on
```

For interior `t ∈ Ioo 0 T`, a window package on `[0,T]` contains exactly the local data needed near `t`. The endpoint issue at `0` should not matter for the PDE/classical-regularity uses, because they are on `Ioo 0 T`. Initial trace is handled separately by `htrace` and does not need source time-C¹ at `0`.

For pure summability of source cosine series at `t ∈ Ioo 0 T`, the window envelope is enough directly:

```lean
srcOn.henv_bound t htIcc n
srcOn.henv_summable
```

For time-derivative of Duhamel synthesis, use the On derivative lemmas rather than the global `DuhamelSourceTimeC1` ones.

---

## Final answer

1. **Yes, the lifespan matches.** `ChiNegDatumUniformConstructionFaithful` demands `u_star : EWA δ 1` and `CoupledDuhamelReducedClassicalCore p δ u0 (realSlice u_star)`. Instantiating `realSlice_reducedCore_wired` with `T := δ` gives exactly that target.

2. **The current reduced-core wiring consumes source time-C¹ packages; it does not produce them.** The caller/frontier theorem proving `ChiNegDatumUniformConstructionFaithful` must produce `hchemOn/hlogOn` and pass them into the wired theorem.

3. **The fetched current version still uses global `DuhamelSourceTimeC1`.** Refactoring to `DuhamelSourceTimeC1On ... 0 T` is type-aligned with the faithful target, but it must propagate through the helper lemmas that currently require global source packages.

4. **The future proof of the faithful construction should be a caller-side assembly:** select `δ`, build `u_star : EWA δ 1`, build source packages on `[0,δ]`, call `realSlice_reducedCore_wired (T := δ)`, and return `⟨u_star, C⟩`.
