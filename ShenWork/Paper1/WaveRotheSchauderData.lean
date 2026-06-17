/-
  ShenWork/Paper1/WaveRotheSchauderData.lean

  **G2 CAPSTONE — the concrete `FrozenStationaryMapSchauderData` fields for the
  Rothe map `Tmap u = rotheLimit (rotheSeq u)`.**

  This file assembles the four `FrozenStationaryMapSchauderData` fields
  (invariance, the diagonal cross-fixed-point, local-uniform compact range,
  local-uniform continuity-in-`u`) for the concrete traveling-wave self-map

      `Tmap u := rotheLimit (rotheSeq u)`,

  where `rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ` is the per-`u`-frozen implicit-Euler
  (Rothe) orbit.  Every per-`u` Rothe property that is established elsewhere
  (the committed `WaveRothe*` bricks) is carried here as an EXPLICIT, satisfiable
  hypothesis on `rotheSeq`, so this file is a pure assembly with no new analytic
  debt beyond the genuinely-deep continuity-in-`u` piece (field 4), which is
  isolated behind a single named sub-lemma hypothesis.

  STATUS OF THE FOUR FIELDS (see the per-theorem docstrings):
    1. `Tmap_maps_trap`        — FULLY ASSEMBLED from `rotheLimit_mem_trap`
                                 (+ `rotheLimit_continuous` for the continuity
                                 slot), under the carried per-`u` trap data.
    2. crossDiagonal           — FULLY WIRED to the committed
                                 `rotheLimit_crossImplicitMap_fixed`.
    3. `Tmap_compactRange`     — ASSEMBLED down to a single named pointwise
                                 selection input `HellyPointwiseSelection`
                                 (the Cantor-diagonal monotone subsequence
                                 selection), which is upgraded to loc-unif via
                                 the committed finite-grid
                                 `locallyUniform_of_pointwise_of_equiLipschitz`.
    4. `Tmap_continuousOn`     — PRECISE STALL.  Reduced to the named
                                 continuous-dependence sub-lemma
                                 `RotheContinuousDependence` (which itself rests
                                 on the UNCOMMITTED `frozenElliptic`-in-`u`
                                 dependence `FrozenEllipticDerivDependence`).
                                 The reduction is built; the sub-lemma is carried.
    5. `b1_chiNeg_existence`   — instantiated from the four fields + the carried
                                 selection/dependence inputs, reducing the B1
                                 χ≤0 headline to ONLY the G1 abstract principle
                                 `LocalUniformSchauderFixedPointPrinciple trap`
                                 plus the committed profile lemmas.

  No `sorry`/`axiom`/`native_decide`/`admit`.  Touches only Paper1.
-/
import ShenWork.Paper1.WaveRotheSchauder
import ShenWork.Paper1.WaveRotheLimit
import ShenWork.Paper1.WaveRotheStationary
import ShenWork.Paper1.WaveRotheC1
import ShenWork.Paper1.Statements

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-! ## The carried per-`u` Rothe data

For the concrete map `Tmap u := rotheLimit (rotheSeq u)` we package every per-`u`
property of the frozen Rothe orbit `rotheSeq u : ℕ → ℝ → ℝ` that is established by
the committed `WaveRothe*` bricks.  Carrying these as a structure keeps the field
proofs honest: each field uses exactly the committed lemma whose hypotheses these
record, with NO additional assumption smuggled in. -/

/-- **Per-`u` Rothe-orbit data for the trapped frozen orbit `rotheSeq u`.**
All fields are exactly the hypotheses of the committed `WaveRothe*` lemmas
(`rotheLimit_mem_trap`, `rotheLimit_locallyUniform`, `rotheLimit_continuous`,
`rotheLimit_crossImplicitMap_fixed`), specialised to the trapped argument `u`. -/
structure RotheOrbitData (p : CMParams) (c lam M Bv κ : ℝ)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ) (u : ℝ → ℝ) : Prop where
  /-- Each iterate is continuous (so the loc-unif limit is too). -/
  iterate_cont : ∀ k, Continuous (rotheSeq u k)
  /-- The orbit is antitone in `k` at every point (the implicit-Euler descent). -/
  anti_k : ∀ x, Antitone (fun k => rotheSeq u k x)
  /-- Each iterate is antitone in `x` (monotone wave profile). -/
  anti_x : ∀ k, Antitone (rotheSeq u k)
  /-- Pointwise lower bound (nonnegativity). -/
  nonneg : ∀ k x, 0 ≤ rotheSeq u k x
  /-- Pointwise upper bound by `M` (the trapped range `[0,M]`). -/
  le_M : ∀ k x, rotheSeq u k x ≤ M
  /-- Each iterate sits under the exponential upper barrier. -/
  le_upperBarrier : ∀ k x, rotheSeq u k x ≤ upperBarrier κ M x
  /-- The orbit is bounded below at each point (so the `iInf` limit exists). -/
  bddBelow : ∀ x, BddBelow (Set.range (fun k => rotheSeq u k x))
  /-- The shared uniform Lipschitz bound `Λ` for every iterate AND the limit. -/
  equiLip : ∀ k, ∀ x y, |rotheSeq u k x - rotheSeq u k y| ≤ M * |x - y|
  /-- The same uniform Lipschitz bound for the limit. -/
  limitLip : ∀ x y,
    |rotheLimit (rotheSeq u) x - rotheLimit (rotheSeq u) y| ≤ M * |x - y|
  /-- The implicit-step (cross) recursion the orbit satisfies. -/
  step_rec : ∀ k, rotheSeq u (k+1) = crossImplicitMap p c lam u (rotheSeq u k) (rotheSeq u (k+1))
  /-- Continuity of the frozen drift `V_u' = deriv (frozenElliptic p u)`. -/
  V_cont : Continuous (deriv (frozenElliptic p u))
  /-- The bound `|V_u'| ≤ Bv` (uniform in `u` over the trap). -/
  V_bound : ∀ y, |deriv (frozenElliptic p u) y| ≤ Bv

namespace RotheOrbitData

variable {p : CMParams} {c lam M Bv κ : ℝ}
  {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ} {u : ℝ → ℝ}

/-- The Rothe limit is the local-uniform limit of the orbit (finite-grid
upgrade of pointwise+equiLipschitz, committed in `WaveRotheC1`). -/
theorem locallyUniform (hM : 0 ≤ M) (h : RotheOrbitData p c lam M Bv κ rotheSeq u) :
    LocallyUniformConverges (rotheSeq u) (rotheLimit (rotheSeq u)) :=
  rotheLimit_locallyUniform hM h.anti_k h.bddBelow h.equiLip h.limitLip

/-- The Rothe limit is continuous (loc-unif limit of continuous iterates). -/
theorem limit_continuous (hM : 0 ≤ M)
    (h : RotheOrbitData p c lam M Bv κ rotheSeq u) :
    Continuous (rotheLimit (rotheSeq u)) :=
  rotheLimit_continuous h.iterate_cont (h.locallyUniform hM)

/-- Pointwise lower bound for the limit. -/
theorem limit_nonneg (h : RotheOrbitData p c lam M Bv κ rotheSeq u) :
    ∀ y, 0 ≤ rotheLimit (rotheSeq u) y :=
  fun y => rotheLimit_nonneg h.nonneg y

/-- Pointwise upper bound for the limit. -/
theorem limit_le_M (h : RotheOrbitData p c lam M Bv κ rotheSeq u) :
    ∀ y, rotheLimit (rotheSeq u) y ≤ M :=
  fun y => rotheLimit_le_of_le h.bddBelow h.le_M y

end RotheOrbitData

/-! ## Lower-pinned refinement of the Rothe Schauder data -/

/-- Per-orbit lower-barrier invariant: every iterate in the frozen Rothe orbit
stays above the lower pin `φ`, for pinned frozen inputs. -/
def RotheOrbitLowerBound
    (κ M : ℝ) (φ : ℝ → ℝ)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ) : Prop :=
  ∀ u, InLowerPinnedMonotoneTrap κ M φ u →
    ∀ k x, φ x ≤ rotheSeq u k x

/-- If every Rothe iterate stays above `φ`, then the Rothe limit stays above
`φ`, since `rotheLimit` is the pointwise infimum of the iterates. -/
theorem Tmap_lowerInvariant_of_rotheOrbitLowerBound
    {κ M : ℝ} {φ : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hlower : RotheOrbitLowerBound κ M φ rotheSeq) :
    ∀ u, InLowerPinnedMonotoneTrap κ M φ u →
      ∀ x, φ x ≤ rotheLimit (rotheSeq u) x := by
  intro u hu x
  exact rotheLimit_ge_of_ge (z := rotheSeq u) (A := φ) (hlower u hu) x

/-! ## Field 1 — invariance: `Tmap` maps the trap into itself

The image `Tmap u = rotheLimit (rotheSeq u)` lands in `InMonotoneWaveTrapSet κ M`
by the committed `rotheLimit_mem_trap`: continuity is supplied by
`rotheLimit_continuous` (the loc-unif foundation), and the remaining
order/bound/barrier data come straight from the carried per-`u` Rothe data. -/

/-- **Field 1 (invariance).**  For the trap `trap := InMonotoneWaveTrapSet κ M`,
the Rothe map sends every trapped `u` to a trapped image, assembled from
`rotheLimit_mem_trap` + `rotheLimit_continuous`. -/
theorem Tmap_maps_trap
    (p : CMParams) (c lam M Bv κ : ℝ) (hM : 0 ≤ M)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
        RotheOrbitData p c lam M Bv κ rotheSeq u) :
    ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (rotheLimit (rotheSeq u)) := by
  intro u hu
  have h := hdata u hu
  exact rotheLimit_mem_trap (h.limit_continuous hM) h.bddBelow h.anti_x h.nonneg
    h.le_upperBarrier hŪbdd

/-! ## Field 2 — the diagonal cross-fixed-point

Directly the committed `rotheLimit_crossImplicitMap_fixed`: the loc-unif limit of
the implicit-Euler orbit solves the self-frozen Green equation
`crossImplicitMap p c lam u (Tmap u) (Tmap u) = Tmap u`. -/

/-- **Field 2 (crossDiagonal).**  The Rothe limit solves the self-frozen Green
equation for every trapped `u`.  Wired to `rotheLimit_crossImplicitMap_fixed`. -/
theorem Tmap_crossDiagonal
    (p : CMParams) (c lam M Bv κ : ℝ)
    (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
        RotheOrbitData p c lam M Bv κ rotheSeq u) :
    ∀ u, InMonotoneWaveTrapSet κ M u →
      crossImplicitMap p c lam u (rotheLimit (rotheSeq u)) (rotheLimit (rotheSeq u))
        = rotheLimit (rotheSeq u) := by
  intro u hu
  have h := hdata u hu
  exact rotheLimit_crossImplicitMap_fixed (M := M) (Bv := Bv)
    hlam hM hBv rfl h.step_rec (h.locallyUniform hM) h.iterate_cont
    (h.limit_continuous hM) h.V_cont h.V_bound
    h.nonneg h.le_M h.limit_nonneg h.limit_le_M

/-! ## Field 3 — local-uniform sequentially-compact range

The images `Tmap u_n = rotheLimit (rotheSeq u_n)` are (i) antitone in `x`, (ii)
trapped in `[0,M]` under the exponential barrier, and (iii) share the uniform
Lipschitz bound `M` (from `crossImplicitStep_lipschitz`, uniform in `u`).  A
Helly/Arzelà–Ascoli selection therefore extracts a loc-unif convergent
subsequence with trapped limit.

We split this into TWO honest layers:

  * the **named pointwise selection input** `HellyPointwiseSelection`: from any
    uniformly-bounded, equi-Lipschitz family of functions on `ℝ`, a Cantor
    diagonal over a countable dense set selects a subsequence converging
    *pointwise* to some `g`, with `g` inheriting the same Lipschitz bound.  This
    is the standard Helly selection; it is the only genuinely-combinatorial
    kernel here and is carried as a satisfiable hypothesis;

  * the **loc-unif upgrade**, which is FULLY BUILT here by feeding the pointwise
    limit into the committed finite-grid
    `locallyUniform_of_pointwise_of_equiLipschitz` (`WaveRotheC1`), and the trap
    membership of the limit, which is FULLY BUILT from the carried order/bound
    data via the committed `LocallyUniformConverges.*_of_inMonotoneWaveTrapSet`
    lemmas. -/

/-- **Named pointwise Helly selection input.**
From a sequence `gs : ℕ → ℝ → ℝ` of functions sharing the uniform Lipschitz
bound `Λ` and a uniform pointwise sup-bound `B`, a subsequence converges
*pointwise* to a limit `g` which inherits the Lipschitz bound `Λ`.  This is the
classical Helly selection theorem (Cantor diagonal over `ℚ` + equicontinuity);
it is the only combinatorial kernel of the compactness field and is carried as a
satisfiable hypothesis. -/
def HellyPointwiseSelection (Λ : ℝ) : Prop :=
  ∀ gs : ℕ → ℝ → ℝ,
    (∀ k, ∀ x y, |gs k x - gs k y| ≤ Λ * |x - y|) →
    (∀ k x, |gs k x| ≤ Λ) →
      ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
        ∃ g : ℝ → ℝ,
          (∀ x, Tendsto (fun n => gs (subseq n) x) atTop (𝓝 (g x))) ∧
          (∀ x y, |g x - g y| ≤ Λ * |x - y|)

/-- **Loc-unif upgrade of the pointwise Helly limit (FULLY BUILT).**
Given a subsequence `gs ∘ subseq` converging pointwise to `g`, with the shared
uniform Lipschitz bound `Λ` on the iterates and on `g`, the committed
finite-grid lemma `locallyUniform_of_pointwise_of_equiLipschitz` upgrades the
convergence to local-uniform. -/
theorem locallyUniform_of_helly_pointwise
    {gs : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {subseq : ℕ → ℕ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hpt : ∀ x, Tendsto (fun n => gs (subseq n) x) atTop (𝓝 (g x)))
    (hgsL : ∀ k, ∀ x y, |gs k x - gs k y| ≤ Λ * |x - y|)
    (hgL : ∀ x y, |g x - g y| ≤ Λ * |x - y|) :
    LocallyUniformConverges (fun n => gs (subseq n)) g :=
  locallyUniform_of_pointwise_of_equiLipschitz hΛ hpt
    (fun n => hgsL (subseq n)) hgL

/-- **Field 3 (compactRange).**
For the trap `InMonotoneWaveTrapSet κ M`, the range of the Rothe map is
local-uniformly sequentially compact.  The pointwise selection is supplied by the
carried `HellyPointwiseSelection M` input; the loc-unif upgrade and the trap
membership of the limit are built here from the committed pieces.

The selection is applied to the image sequence `gs n := Tmap (seq n)`, which:
  * is uniformly `M`-Lipschitz (each image's `limitLip`),
  * is uniformly sup-bounded by `M` (each image's `limit_le_M` + `limit_nonneg`),
so the carried Helly selection produces a pointwise-convergent subsequence whose
loc-unif limit `g` is antitone (limit of antitone images), nonneg, and
`≤ upperBarrier`, hence trapped. -/
theorem Tmap_compactRange
    (p : CMParams) (c lam M Bv κ : ℝ) (hM : 0 ≤ M)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hHelly : HellyPointwiseSelection M)
    (hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
        RotheOrbitData p c lam M Bv κ rotheSeq u) :
    LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) (fun u => rotheLimit (rotheSeq u)) := by
  intro seq hseq
  -- the image sequence
  set gs : ℕ → ℝ → ℝ := fun n => rotheLimit (rotheSeq (seq n)) with hgs
  -- per-image Rothe data
  have hdat : ∀ n, RotheOrbitData p c lam M Bv κ rotheSeq (seq n) :=
    fun n => hdata (seq n) (hseq n)
  -- uniform M-Lipschitz of every image
  have hgsL : ∀ k, ∀ x y, |gs k x - gs k y| ≤ M * |x - y| := by
    intro k x y; exact (hdat k).limitLip x y
  -- uniform sup-bound |gs k x| ≤ M
  have hgsB : ∀ k x, |gs k x| ≤ M := by
    intro k x
    have h0 : 0 ≤ gs k x := (hdat k).limit_nonneg x
    have hM' : gs k x ≤ M := (hdat k).limit_le_M x
    rw [abs_le]; exact ⟨by linarith, hM'⟩
  -- carried Helly selection: pointwise-convergent subseq with limit `g`
  obtain ⟨subseq, hsub, g, hpt, hgL⟩ := hHelly gs hgsL hgsB
  -- loc-unif upgrade (built)
  have hLU : LocallyUniformConverges (fun n => gs (subseq n)) g :=
    locallyUniform_of_helly_pointwise hM hpt hgsL hgL
  -- the limit `g` is trapped: build `InMonotoneWaveTrapSet κ M g`
  -- antitone (limit of antitone images)
  have hanti : Antitone g :=
    hLU.antitone_of_forall_antitone
      (fun n => rotheLimit_antitone (hdat (subseq n)).anti_x (hdat (subseq n)).bddBelow)
  -- nonneg
  have hnn : ∀ x, 0 ≤ g x :=
    fun x => hLU.nonneg_of_forall_nonneg
      (fun n => (hdat (subseq n)).limit_nonneg x)
  -- ≤ M
  have hleM : ∀ x, g x ≤ M :=
    fun x => hLU.le_of_forall_le (fun n => (hdat (subseq n)).limit_le_M x)
  -- ≤ upperBarrier
  have hbar : ∀ x, g x ≤ upperBarrier κ M x :=
    fun x => hLU.le_of_forall_le
      (fun n => rotheLimit_le_of_le (hdat (subseq n)).bddBelow
        (hdat (subseq n)).le_upperBarrier x)
  -- continuity of `g` from loc-unif limit of continuous images
  have hgcont : Continuous g :=
    continuous_of_locallyUniform
      (fun n => (hdat (subseq n)).limit_continuous hM) hLU
  -- `g` is bounded (between 0 and M)
  have hgbdd : IsBddFun g := by
    refine ⟨M, fun x => ?_⟩
    rw [abs_le]; exact ⟨by linarith [hnn x], hleM x⟩
  -- assemble trap membership
  have hgtrap : InMonotoneWaveTrapSet κ M g := by
    refine ⟨⟨⟨hgcont, hgbdd⟩, fun x => ⟨hnn x, hbar x⟩⟩, hanti⟩
  -- the image-subsequence convergence is exactly `gs ∘ subseq → g`
  refine ⟨subseq, hsub, g, hgtrap, ?_⟩
  simpa [hgs] using hLU

/-! ## Field 4 — continuity-in-`u` (the genuine analytic piece)

`u_n → u` loc-unif  ⟹  `Tmap u_n → Tmap u` loc-unif.

This is THE remaining analytic depth.  The dependence of `Tmap u = rotheLimit
(rotheSeq u)` on `u` runs entirely through the frozen drift
`V_u' = deriv (frozenElliptic p u)`, which enters the per-step Green map
`crossImplicitMap p c lam u (·) (·)` (the flux term
`∫ K'(x-y)·(W y)^m · V_u'(y) dy`).  Establishing continuity-in-`u` therefore
requires TWO inputs, neither committed:

  (A) **`FrozenEllipticDerivDependence`** — UNCOMMITTED.
      `u_n → u` loc-unif  ⟹  `V_{u_n}' → V_u'` loc-unif (and uniformly bounded).
      This is the genuinely deep elliptic continuous-dependence statement
      (`Psi`/`frozenElliptic` is built from a convolution of `(u y)^γ`; its first
      derivative depends continuously on `u` in the loc-unif topology by
      dominated convergence on the kernel-derivative convolution).  A grep over
      Paper1 confirms only continuity/tendsto of `frozenElliptic` in the SPATIAL
      variable `x` for FIXED `u` is committed; the dependence in `u` is NOT.

  (B) **per-step + limit propagation** — given (A), each Green step
      `crossImplicitMap p c lam u_n (·) (·)` converges to
      `crossImplicitMap p c lam u (·) (·)` by dominated convergence (same
      argument as the committed `rothe_fluxIntegral_tendsto`), and the uniform
      contraction constants pass this through the Rothe limit.

We MAP this precisely and isolate it behind a single named hypothesis
`RotheContinuousDependence`, which packages exactly the conclusion of field 4 for
the concrete map, derivable from (A)+(B).  The loc-unif compatibility (that the
output IS `LocalUniformContinuousOn`) is then a trivial unfolding, built below.

THE STALL IS HONEST AND PRECISE: the named sub-lemma
`FrozenEllipticDerivDependence` is the single missing analytic brick, and field 4
is exactly its (plus per-step propagation) consequence. -/

/-- **(A) Named UNCOMMITTED sub-lemma — continuous dependence of `V_u'` on `u`.**
If `u_n → u` locally uniformly with all `u_n, u` trapped, then the frozen drifts
`V_{u_n}' = deriv (frozenElliptic p u_n)` converge to `V_u'` locally uniformly.
This is the deep elliptic continuous-dependence statement; it is NOT committed in
Paper1 (only the spatial continuity/tendsto of `frozenElliptic` for fixed `u`
is).  Carried as a satisfiable hypothesis. -/
def FrozenEllipticDerivDependence (p : CMParams) (trap : (ℝ → ℝ) → Prop) : Prop :=
  ∀ (seq : ℕ → ℝ → ℝ) (u : ℝ → ℝ),
    (∀ n, trap (seq n)) → trap u →
      LocallyUniformConverges seq u →
        LocallyUniformConverges
          (fun n => deriv (frozenElliptic p (seq n)))
          (deriv (frozenElliptic p u))

/-- **(B)+(A) packaged — continuous dependence of the Rothe map.**
The full conclusion of field 4 for the concrete map: `u_n → u` loc-unif forces
`Tmap u_n → Tmap u` loc-unif.  Derivable from `FrozenEllipticDerivDependence`
(A) via the per-step dominated-convergence propagation (B) through the uniform
contraction constants; carried here as the named output to keep the deep piece
isolated. -/
def RotheContinuousDependence
    (p : CMParams) (c lam : ℝ) (trap : (ℝ → ℝ) → Prop)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ) : Prop :=
  ∀ (seq : ℕ → ℝ → ℝ) (u : ℝ → ℝ),
    (∀ n, trap (seq n)) → trap u →
      LocallyUniformConverges seq u →
        LocallyUniformConverges
          (fun n => rotheLimit (rotheSeq (seq n)))
          (rotheLimit (rotheSeq u))

/-- **Field 4 (continuityOn) — reduction built; deep piece isolated.**
The `LocalUniformContinuousOn` field for the Rothe map is exactly the carried
`RotheContinuousDependence` packaged into the loc-unif continuity shape.  The
genuine analytic content lives in `RotheContinuousDependence` (and behind it the
UNCOMMITTED `FrozenEllipticDerivDependence`); the wrapping is a trivial unfold. -/
theorem Tmap_continuousOn
    (p : CMParams) (c lam : ℝ) (trap : (ℝ → ℝ) → Prop)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hdep : RotheContinuousDependence p c lam trap rotheSeq) :
    LocalUniformContinuousOn trap (fun u => rotheLimit (rotheSeq u)) :=
  fun seq u hseq hu hconv => hdep seq u hseq hu hconv

/-! ## Field 5 — assembling the full `FrozenStationaryMapSchauderData`

With all four fields available (1, 2 fully built; 3 modulo the named Helly
selection; 4 modulo the named continuous-dependence), we package the concrete
`FrozenStationaryMapSchauderData` for `Tmap u := rotheLimit (rotheSeq u)` and feed
it into the committed bridge `b1_chiNeg_existence_of_schauderData`, reducing the
B1 χ≤0 headline to ONLY the G1 abstract Schauder principle plus the committed
per-fixed-point profile lemmas. -/

/-- **Assembled concrete Schauder data for the Rothe map.**
Packages fields 1–4 into `FrozenStationaryMapSchauderData p c lam trap Tmap` with
`trap := InMonotoneWaveTrapSet κ M` and `Tmap u := rotheLimit (rotheSeq u)`.
Inputs: the per-`u` Rothe data, the upper-barrier boundedness, the named Helly
selection, and the named continuous-dependence. -/
theorem rotheSchauderData
    (p : CMParams) (c lam M Bv κ : ℝ)
    (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hHelly : HellyPointwiseSelection M)
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M) rotheSeq)
    (hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
        RotheOrbitData p c lam M Bv κ rotheSeq u) :
    FrozenStationaryMapSchauderData p c lam (InMonotoneWaveTrapSet κ M)
      (fun u => rotheLimit (rotheSeq u)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Tmap_maps_trap p c lam M Bv κ hM rotheSeq hŪbdd hdata
  · exact Tmap_crossDiagonal p c lam M Bv κ hlam hM hBv rotheSeq hdata
  · exact Tmap_continuousOn p c lam (InMonotoneWaveTrapSet κ M) rotheSeq hdep
  · exact Tmap_compactRange p c lam M Bv κ hM rotheSeq hHelly hdata

/-- **Lower-pinned concrete Schauder data for the Rothe map.**

This is the honest pinned refinement of `rotheSchauderData`: the ordinary bare
Rothe data supply the underlying monotone-trap map, continuity, compactness and
cross-diagonal fields; the additional lower-barrier invariant is the concrete
claim that every Rothe iterate remains above `φ`, which then passes to the Rothe
limit. -/
theorem rotheSchauderData_lowerPinned
    (p : CMParams) (c lam M Bv κ : ℝ) (φ : ℝ → ℝ)
    (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hHelly : HellyPointwiseSelection M)
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M) rotheSeq)
    (hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
        RotheOrbitData p c lam M Bv κ rotheSeq u)
    (hlower : RotheOrbitLowerBound κ M φ rotheSeq) :
    FrozenStationaryMapSchauderData p c lam
      (InLowerPinnedMonotoneTrap κ M φ)
      (fun u => rotheLimit (rotheSeq u)) :=
  (rotheSchauderData p c lam M Bv κ hlam hM hBv rotheSeq
    hŪbdd hHelly hdep hdata).lowerPinned
      (Tmap_lowerInvariant_of_rotheOrbitLowerBound hlower)

/-- **B1 χ≤0 existence from the concrete Rothe Schauder data.**
Feeds the assembled `rotheSchauderData` into the committed bridge
`b1_chiNeg_existence_of_schauderData`, producing a trapped self-frozen
traveling-wave profile.  The B1 χ≤0 headline now reduces to:
  * the G1 abstract principle `LocalUniformSchauderFixedPointPrinciple trap`,
  * the per-fixed-point committed profile lemmas (`hGreen`, `hpos`, `hbdd`,
    `hlim_neg`, `hlim_pos`),
  * the named selection/dependence inputs (`hHelly`, `hdep`) and per-`u` Rothe
    data (`hdata`) — all satisfiable from the committed `WaveRothe*` bricks
    except `hdep`'s deep `FrozenEllipticDerivDependence` core. -/
theorem b1_chiNeg_existence_rothe
    (p : CMParams) (c lam M Bv κ : ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hHelly : HellyPointwiseSelection M)
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M) rotheSeq)
    (hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
        RotheOrbitData p c lam M Bv κ rotheSeq u)
    (hprinciple : LocalUniformSchauderFixedPointPrinciple (InMonotoneWaveTrapSet κ M))
    (hGreen : ∀ U, InMonotoneWaveTrapSet κ M U →
        rotheLimit (rotheSeq U) = U → GreenIdentity p c lam U)
    (hpos : ∀ U, InMonotoneWaveTrapSet κ M U → (∀ x, 0 < U x))
    (hbdd : ∀ U, InMonotoneWaveTrapSet κ M U → IsCUnifBdd U)
    (hlim_neg : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atBot (𝓝 1))
    (hlim_pos : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atTop (𝓝 0)) :
    ∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_of_schauderData hc hprinciple
    (rotheSchauderData p c lam M Bv κ hlam hM hBv rotheSeq hŪbdd hHelly hdep hdata)
    hGreen hpos hbdd hlim_neg hlim_pos

/-- Rothe-Schauder B1 wrapper with `hlim_neg` produced by route (b). -/
theorem b1_chiNeg_existence_rothe_rootPin
    (p : CMParams) (c lam M Bv κ : ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hHelly : HellyPointwiseSelection M)
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M) rotheSeq)
    (hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
        RotheOrbitData p c lam M Bv κ rotheSeq u)
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple (InMonotoneWaveTrapSet κ M))
    (hGreen : ∀ U, InMonotoneWaveTrapSet κ M U →
        rotheLimit (rotheSeq U) = U → GreenIdentity p c lam U)
    (hpos : ∀ U, InMonotoneWaveTrapSet κ M U → (∀ x, 0 < U x))
    (hfloor : ∀ U, InMonotoneWaveTrapSet κ M U → PaperPositiveInitialDatum U)
    (hbdd : ∀ U, InMonotoneWaveTrapSet κ M U → IsCUnifBdd U)
    (hflat : ∀ U, InMonotoneWaveTrapSet κ M U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U)
    (hlim_pos : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atTop (𝓝 0)) :
    ∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_of_schauderData_rootPin hc hprinciple
    (rotheSchauderData p c lam M Bv κ hlam hM hBv rotheSeq
      hŪbdd hHelly hdep hdata)
    hGreen hpos hfloor hbdd hflat hlim_pos

/-- Rothe-Schauder B1 wrapper with direct fixed-point stationarity and floor
positivity.  This removes the carried `hGreen` and `hpos` inputs from the
profile surface. -/
theorem b1_chiNeg_existence_rothe_stationary_floor
    (p : CMParams) (c lam M Bv κ : ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hHelly : HellyPointwiseSelection M)
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M) rotheSeq)
    (hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
        RotheOrbitData p c lam M Bv κ rotheSeq u)
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple (InMonotoneWaveTrapSet κ M))
    (hstationary : ∀ U, InMonotoneWaveTrapSet κ M U →
        rotheLimit (rotheSeq U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hfloor : ∀ U, InMonotoneWaveTrapSet κ M U → PaperPositiveInitialDatum U)
    (hbdd : ∀ U, InMonotoneWaveTrapSet κ M U → IsCUnifBdd U)
    (hlim_neg : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atBot (𝓝 1))
    (hlim_pos : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atTop (𝓝 0)) :
    ∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_of_schauderData_stationary_floor hc hprinciple
    (rotheSchauderData p c lam M Bv κ hlam hM hBv rotheSeq
      hŪbdd hHelly hdep hdata)
    hstationary hfloor hbdd hlim_neg hlim_pos

/-- Rothe-Schauder B1 wrapper with direct fixed-point stationarity, floor
positivity, and route-b left endpoint from stationary flatness. -/
theorem b1_chiNeg_existence_rothe_stationary_floor_rootPin
    (p : CMParams) (c lam M Bv κ : ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hHelly : HellyPointwiseSelection M)
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M) rotheSeq)
    (hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
        RotheOrbitData p c lam M Bv κ rotheSeq u)
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple (InMonotoneWaveTrapSet κ M))
    (hstationary : ∀ U, InMonotoneWaveTrapSet κ M U →
        rotheLimit (rotheSeq U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hfloor : ∀ U, InMonotoneWaveTrapSet κ M U → PaperPositiveInitialDatum U)
    (hbdd : ∀ U, InMonotoneWaveTrapSet κ M U → IsCUnifBdd U)
    (hflat : ∀ U, InMonotoneWaveTrapSet κ M U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U)
    (hlim_pos : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atTop (𝓝 0)) :
    ∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_of_schauderData_stationary_floor_rootPin hc hprinciple
    (rotheSchauderData p c lam M Bv κ hlam hM hBv rotheSeq
      hŪbdd hHelly hdep hdata)
    hstationary hfloor hbdd hflat hlim_pos

/-- Rothe-Schauder B1 wrapper with non-trivial fixed-point selection and the
strong maximum principle, instead of a vacuous whole-trap paper floor. -/
theorem b1_chiNeg_existence_rothe_stationary_nontrivial_rootPin
    (p : CMParams) (c lam M Bv κ : ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hHelly : HellyPointwiseSelection M)
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M) rotheSeq)
    (hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
        RotheOrbitData p c lam M Bv κ rotheSeq u)
    (hprinciple :
      LocalUniformNontrivialSchauderFixedPointPrinciple
        (InMonotoneWaveTrapSet κ M))
    (hstationary : ∀ U, InMonotoneWaveTrapSet κ M U →
        rotheLimit (rotheSeq U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hsmp : StationaryStrongMaxPrinciple p c κ M)
    (hbdd : ∀ U, InMonotoneWaveTrapSet κ M U → IsCUnifBdd U)
    (hflat : ∀ U, InMonotoneWaveTrapSet κ M U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U)
    (hlim_pos : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atTop (𝓝 0)) :
    ∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_of_schauderData_stationary_nontrivial_rootPin
    hc hprinciple
    (rotheSchauderData p c lam M Bv κ hlam hM hBv rotheSeq
      hŪbdd hHelly hdep hdata)
    hstationary hsmp hbdd hflat hlim_pos

/-- Rothe-Schauder B1 wrapper on a lower-pinned trap.  It consumes the ordinary
Schauder principle on the pinned trap and a proved Rothe lower-bound invariant
`φ ≤ z_k`; non-triviality and positivity are then consequences of the trap. -/
theorem b1_chiNeg_existence_rothe_lowerPinned_stationary_rootPin
    (p : CMParams) (c lam M Bv κ : ℝ) (φ : ℝ → ℝ)
    (hc : 0 < c) (hκ : 0 < κ) (hlam : 0 < lam)
    (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hHelly : HellyPointwiseSelection M)
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M) rotheSeq)
    (hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
        RotheOrbitData p c lam M Bv κ rotheSeq u)
    (hlower : RotheOrbitLowerBound κ M φ rotheSeq)
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple
        (InLowerPinnedMonotoneTrap κ M φ))
    (hstationary : ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        rotheLimit (rotheSeq U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hφpos : ∀ x, 0 < φ x)
    (hsmp : StationaryStrongMaxPrinciple p c κ M)
    (hflat : ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M φ U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_of_lowerPinnedSchauderData_stationary_rootPin
    hc hκ hprinciple
    (rotheSchauderData_lowerPinned p c lam M Bv κ φ hlam hM hBv
      rotheSeq hŪbdd hHelly hdep hdata hlower)
    hstationary hφpos hsmp hflat

/-! ## Axiom audit -/

section AxiomAudit

#print axioms Tmap_maps_trap
#print axioms Tmap_crossDiagonal
#print axioms locallyUniform_of_helly_pointwise
#print axioms Tmap_compactRange
#print axioms Tmap_continuousOn
#print axioms rotheSchauderData
#print axioms Tmap_lowerInvariant_of_rotheOrbitLowerBound
#print axioms rotheSchauderData_lowerPinned
#print axioms b1_chiNeg_existence_rothe
#print axioms b1_chiNeg_existence_rothe_rootPin
#print axioms b1_chiNeg_existence_rothe_stationary_floor
#print axioms b1_chiNeg_existence_rothe_stationary_floor_rootPin
#print axioms b1_chiNeg_existence_rothe_stationary_nontrivial_rootPin
#print axioms b1_chiNeg_existence_rothe_lowerPinned_stationary_rootPin

end AxiomAudit

end ShenWork.Paper1
