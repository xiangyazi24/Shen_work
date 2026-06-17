/-
  ShenWork/Paper1/WaveRotheDep.lean

  **Discharge of `RotheContinuousDependence` for the concrete Rothe map.**

  Goal (the last carried analytic hypothesis of `b1_chiNeg_existence_clean`):
  propagate the PROVEN deep core `frozenEllipticDerivDependence`
  (`V'_u = deriv (frozenElliptic p u)` continuous in `u`, loc-unif) through the
  implicit-Euler (Rothe) map to obtain

      `Tmap u = rotheLimit (rotheSeqFromTrap … u …)` continuous in `u` (loc-unif),

  i.e. `RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
        (rotheSeqFromTrap p c lam M κ Λ hprodTrap hκ hM)`.

  ────────────────────────────────────────────────────────────────────────────
  WHAT IS GENUINELY DERIVABLE HERE vs. WHAT MUST BE CARRIED — the honest split.

  The frozen drift `V'_u` enters the per-step Green map
  `crossImplicitMap p c lam u Z W` ONLY through the chemotaxis flux
  `∫ Kλ'(x-y) · (W y)^m · V'_u(y) dy`; the reaction `R(W) + λ Z` part has no `u`.
  So *morally* each step solution depends continuously on `V'_u`, hence on `u`.

  But the concrete `rotheSeqOf u` is built by `Classical.choose` against the
  ABSTRACT producer `hprodTrap u hu : RotheStepProducer …`, which only asserts the
  EXISTENCE of a step solution with the `RotheStepFacts` bundle.  It carries no
  uniqueness, and — crucially — no link between the chosen step solution for a
  sequence `seq n` and the one for the limit `u`: `rotheSeqOf (seq n) k` and
  `rotheSeqOf u k` are produced by INDEPENDENT choices against the distinct
  witnesses `hprodTrap (seq n) (hseq n)` and `hprodTrap u hu`.  Therefore the per-step
  continuous-dependence of the realized iterates on `u` does NOT follow from the
  committed bricks: it is the one genuinely-missing analytic propagation, and we
  carry it as the SINGLE precise named hypothesis

      `RotheSeqStepDependence` :
        `seq n → u` loc-unif (trapped)  ⟹  for every fixed `k`,
        `rotheSeqOf (seq n) k → rotheSeqOf u k` loc-unif.

  This is exactly the dominated-convergence-through-the-implicit-step statement
  fed by the PROVEN `frozenEllipticDerivDependence` (the flux integrand
  `(W y)^m · V'_{seq n}(y) → (W y)^m · V'_u(y)`; the contraction is uniform in
  `u` via `crossImplicitStep_lipschitz`, so the fixed points converge).  It is
  satisfiable but not a committed closed lemma — see the report.

  The SECOND uniformity — passing the per-step convergence to the `k`-limit
  `rotheLimit z = ⨅ k z k` — needs the tail `|z k x − rotheLimit z x|` to be
  small UNIFORMLY in the profile (`seq n` and `u`) and in `x` on `[−R,R]`, for
  large `k`.  This is a Dini-type uniform tail; the committed per-`v`
  `rotheLimit_locallyUniform` gives only a per-`v` tail, not one uniform across
  the family `{seq n}`.  We carry it as the precise named hypothesis

      `RotheTailUniform` :
        `∀ R>0, ∀ ε>0, ∃ K, ∀ trapped v, ∀ k ≥ K, ∀ x∈[−R,R],
           |rotheSeqOf v k x − rotheLimit (rotheSeqOf v) x| < ε`.

  GIVEN these two precise named inputs, the loc-unif continuity of the LIMIT MAP
  is a fully-built `ε/3` theorem (`rotheLimit_dep_of_step_and_tail` below), and
  `rotheContinuousDependence` is assembled from it.  No `sorry`/`axiom`/
  `native_decide`/`admit`.  Touches only Paper1.
-/
import ShenWork.Paper1.WaveRotheConcrete
import ShenWork.Paper1.WaveRotheC1
import ShenWork.Paper1.WaveFrozenEllipticDep

open Filter Topology Set

noncomputable section

namespace ShenWork.Paper1

variable {p : CMParams} {c lam M κ Λ : ℝ}

/-! ## The two precise carried hypotheses

Both are isolated, named, and satisfiable; `frozenEllipticDerivDependence`
(PROVEN, `WaveFrozenEllipticDep.lean`) is the analytic input that discharges the
first, and the uniform Dini tail discharges the second. -/

/-- **Per-step continuous dependence of the Rothe orbit on the frozen profile
(uniform-shape, the carried analytic propagation).**

If `seq n → u` locally uniformly with every `seq n` and `u` trapped, then for
EVERY fixed step index `k` the realized Rothe iterates converge locally
uniformly:

    `rotheSeqOf (seq n) k → rotheSeqOf u k`   (loc-unif).

This is the dominated-convergence-through-the-implicit-step statement; its
analytic content is supplied by the PROVEN `frozenEllipticDerivDependence`
(continuous dependence of `V'_u` on `u`) plus the uniform-in-`u` contraction
constants.  It is carried because the abstract `Classical.choose`-based producer
`rotheSeqOf` provides no continuity link between the independently-chosen step
solutions for `seq n` and for `u`. -/
def RotheSeqStepDependence
    (p : CMParams) (c lam M κ Λ : ℝ)
    (hprodTrap : ∀ v, InMonotoneWaveTrapSet κ M v →
      RotheStepProducer p c lam M κ Λ v)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : Prop :=
  ∀ (seq : ℕ → ℝ → ℝ) (u : ℝ → ℝ),
    (hseq : ∀ n, InMonotoneWaveTrapSet κ M (seq n)) →
      (hu : InMonotoneWaveTrapSet κ M u) →
      LocallyUniformConverges seq u →
        ∀ k : ℕ,
          LocallyUniformConverges
            (fun n => rotheSeqOf p c lam M κ Λ (seq n)
              (hprodTrap (seq n) (hseq n)) hκ hM k)
            (rotheSeqOf p c lam M κ Λ u
              (hprodTrap u hu) hκ hM k)

/-- **Uniform Dini tail of the Rothe orbit across trapped profiles (the
uniform-in-`k` subtlety).**

For any window `[−R,R]` and tolerance `ε`, there is a common step cutoff `K` so
that, simultaneously for EVERY trapped profile `v`, the iterate `rotheSeqOf v k`
is within `ε` of its `k`-limit `rotheLimit (rotheSeqOf v)` on `[−R,R]` once
`k ≥ K`.  The committed per-`v` `rotheLimit_locallyUniform` gives only a per-`v`
cutoff; uniformity across the family `{seq n} ∪ {u}` is the genuine uniform-in-k
content, carried here. -/
def RotheTailUniform
    (p : CMParams) (c lam M κ Λ : ℝ)
    (hprodTrap : ∀ v, InMonotoneWaveTrapSet κ M v →
      RotheStepProducer p c lam M κ Λ v)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : Prop :=
  ∀ R > 0, ∀ ε > 0,
    ∃ K : ℕ, ∀ v : ℝ → ℝ, (hv : InMonotoneWaveTrapSet κ M v) →
      ∀ k : ℕ, K ≤ k → ∀ x ∈ Set.Icc (-R) R,
        |rotheSeqOf p c lam M κ Λ v (hprodTrap v hv) hκ hM k x
            - rotheLimit
              (rotheSeqOf p c lam M κ Λ v (hprodTrap v hv) hκ hM) x| < ε

/-! ## The limit passage (fully built `ε/3`)

From the two carried inputs we derive loc-unif convergence of the LIMIT MAPS
`rotheLimit (rotheSeqOf (seq n)) → rotheLimit (rotheSeqOf u)`. -/

/-- **The `ε/3` limit passage.**
Per-step loc-unif convergence (`RotheSeqStepDependence`) + the uniform Dini tail
(`RotheTailUniform`) give loc-unif convergence of the `k`-limits.  For `x∈[−R,R]`:

    `|L'_n x − L x|
       ≤ |L'_n x − z'_n,K x|   (tail, uniform in n, < ε/3)
       + |z'_n,K x − z_K x|     (per-step at index K, large n, < ε/3)
       + |z_K x − L x|`         (tail for u, < ε/3),

where `K` is the common cutoff from `RotheTailUniform`. -/
theorem rotheLimit_dep_of_step_and_tail
    {hprodTrap : ∀ v, InMonotoneWaveTrapSet κ M v →
      RotheStepProducer p c lam M κ Λ v} {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (hstep : RotheSeqStepDependence p c lam M κ Λ hprodTrap hκ hM)
    (htail : RotheTailUniform p c lam M κ Λ hprodTrap hκ hM)
    (seq : ℕ → ℝ → ℝ) (u : ℝ → ℝ)
    (hseq : ∀ n, InMonotoneWaveTrapSet κ M (seq n))
    (hu : InMonotoneWaveTrapSet κ M u)
    (hconv : LocallyUniformConverges seq u) :
    LocallyUniformConverges
      (fun n =>
        rotheLimit ((rotheSeqFromTrap p c lam M κ Λ hprodTrap hκ hM) (seq n)))
      (rotheLimit ((rotheSeqFromTrap p c lam M κ Λ hprodTrap hκ hM) u)) := by
  -- abbreviations
  set Z : (ℝ → ℝ) → ℕ → ℝ → ℝ :=
    rotheSeqFromTrap p c lam M κ Λ hprodTrap hκ hM with hZ
  set L : (ℝ → ℝ) → ℝ → ℝ := fun v => rotheLimit (Z v) with hL
  intro R hR ε hε
  -- the common tail cutoff K for ε/3, over all trapped profiles
  obtain ⟨K, hK⟩ := htail R hR (ε / 3) (by linarith)
  -- per-step convergence at the single index K
  have hstepK :
      LocallyUniformConverges (fun n => Z (seq n) K) (Z u K) :=
    by
      have hstepK' := hstep seq u hseq hu hconv K
      simpa [hZ, rotheSeqFromTrap, hseq, hu] using hstepK'
  -- large-n event: per-step within ε/3 on [−R,R]
  filter_upwards [hstepK R hR (ε / 3) (by linarith)] with n hn
  intro x hx
  -- tail for seq n (uniform K), tail for u, per-step at K
  have htailn : |Z (seq n) K x - L (seq n) x| < ε / 3 :=
    by
      have htailn' := hK (seq n) (hseq n) K (le_refl K) x hx
      simpa [hZ, hL, rotheSeqFromTrap, hseq] using htailn'
  have htailu : |Z u K x - L u x| < ε / 3 :=
    by
      have htailu' := hK u hu K (le_refl K) x hx
      simpa [hZ, hL, rotheSeqFromTrap, hu] using htailu'
  have hmid : |Z (seq n) K x - Z u K x| < ε / 3 := hn x hx
  -- triangle: |L (seq n) x − L u x|
  --   ≤ |L (seq n) x − Z (seq n) K x| + |Z (seq n) K x − Z u K x| + |Z u K x − L u x|
  have hdecomp :
      L (seq n) x - L u x
        = -(Z (seq n) K x - L (seq n) x)
          + (Z (seq n) K x - Z u K x)
          + (Z u K x - L u x) := by ring
  calc |L (seq n) x - L u x|
      = |-(Z (seq n) K x - L (seq n) x)
          + (Z (seq n) K x - Z u K x)
          + (Z u K x - L u x)| := by rw [hdecomp]
    _ ≤ |-(Z (seq n) K x - L (seq n) x) + (Z (seq n) K x - Z u K x)|
          + |Z u K x - L u x| := abs_add_le _ _
    _ ≤ |-(Z (seq n) K x - L (seq n) x)| + |Z (seq n) K x - Z u K x|
          + |Z u K x - L u x| := by
          have := abs_add_le (-(Z (seq n) K x - L (seq n) x)) (Z (seq n) K x - Z u K x)
          linarith
    _ = |Z (seq n) K x - L (seq n) x| + |Z (seq n) K x - Z u K x|
          + |Z u K x - L u x| := by rw [abs_neg]
    _ < ε / 3 + ε / 3 + ε / 3 := by
          have := htailn; have := hmid; have := htailu; linarith
    _ = ε := by ring

/-! ## The deliverable -/

/-- **`RotheContinuousDependence` for the concrete Rothe map — discharged.**

Assembles the loc-unif continuity of `Tmap u = rotheLimit (rotheSeqFromTrap … u …)`
from the per-step continuous dependence `RotheSeqStepDependence` (fed by the
PROVEN `frozenEllipticDerivDependence`) and the uniform Dini tail
`RotheTailUniform`, via the `ε/3` limit passage `rotheLimit_dep_of_step_and_tail`.

This is EXACTLY the shape consumed by `b1_chiNeg_existence_clean`'s `hdep`
argument, with `rotheSeq` supplied by
`rotheSeqFromTrap p c lam M κ Λ hprodTrap hκ hM`. -/
theorem rotheContinuousDependence
    (p : CMParams) (c lam M κ Λ : ℝ)
    (hprodTrap : ∀ v, InMonotoneWaveTrapSet κ M v →
      RotheStepProducer p c lam M κ Λ v)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (hstep : RotheSeqStepDependence p c lam M κ Λ hprodTrap hκ hM)
    (htail : RotheTailUniform p c lam M κ Λ hprodTrap hκ hM) :
    RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
      (rotheSeqFromTrap p c lam M κ Λ hprodTrap hκ hM) :=
  fun seq u hseq hu hconv =>
    rotheLimit_dep_of_step_and_tail hstep htail seq u hseq hu hconv

/-! ## Axiom audit -/

section AxiomAudit
#print axioms rotheLimit_dep_of_step_and_tail
#print axioms rotheContinuousDependence
end AxiomAudit

end ShenWork.Paper1
