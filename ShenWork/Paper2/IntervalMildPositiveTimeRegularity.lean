import ShenWork.Paper2.IntervalBFormSpectralProviderDischarge
import ShenWork.Paper2.IntervalCarrySeamGradientContinuousOn
import ShenWork.PDE.IntervalCosineSliceRegularity
import ShenWork.Paper2.IntervalCoeffLadderFull

/-!
# Positive-time spatial regularity of a conjugate mild solution (shared `(C1)`)

This is the shared spatial-regularity crux for the χ₀<0 branch: from the
generic `ConjugateMildSolutionData` fields (`S.hcont`, `S.hbound`, `S.hpos`)
together with the two source-side leaves

* `hsrcB` — the B-form source `DuhamelSourceTimeC1` package, and
* `hB_restart` — the restart cosine representation of `S.u` near each interior
  time,

each interior slice `S.u σ` is `C²` on `[0,1]` with vanishing Neumann endpoint
derivatives, and its cosine coefficients are eigenvalue-weighted `ℓ¹`-summable.

The whole content of this file is *wiring* over the committed engines: the
eigenvalue-weighted summability of the restart coefficients comes from
`localRestartCoeff_eigenvalue_summable` (parabolic gain, no pointwise ladder),
and the `C²`+Neumann conclusion from `intervalDomainCosineSlice_conjunct7_unconditional`.
The restart base coefficient bound is discharged directly from slice continuity
(`continuousOn_intervalDomainLift_of_hasContinuousSlices`) and `S.hbound`, so no
circular appeal to the slice's own cosine series is made.

Both the HSpectral producer and the Jensen strict-positivity supersolution
import this file: it reduces their common spatial-regularity need to the single
pair of source-side leaves `{hsrcB, hB_restart}` (facet `(C2)`, the source
ladder and Duhamel representation).
-/

open Set Filter Topology
open scoped Topology

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalConjugatePicard (ConjugateMildSolutionData)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalBFormSpectral (bFormSourceCoeffs)

noncomputable section

namespace ShenWork.Paper2.IntervalMildPositiveTimeRegularity

/-- The restart cosine representation of `S.u` near each interior time, in the
form consumed below.  This is facet `(C2b)` — the Duhamel representation leaf. -/
def RestartRepresentation
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀) : Prop :=
  ∀ t₀, 0 < t₀ → t₀ < S.T →
    ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
      S.u s y =
        ∑' n,
          localRestartCoeff
            (cosineCoeffs (intervalDomainLift (S.u (t₀ / 2))))
            (fun σ n => bFormSourceCoeffs p S.u (t₀ / 2 + σ) n)
            (s - t₀ / 2) n * cosineMode n y.1

/-- **Uniform positive lower bound on an interior slice.**  From strict
positivity (`S.hpos`) and continuity (`S.hcont`) of the slice on the compact
interval `[0,1]`, the slice is bounded below by a positive `δ`.  This is the
refinement needed for `u^γ` (Nemytskii) regularity: `∂ₓₓ(u^γ)` carries a factor
`u^{γ-2}` which blows up as `u → 0` for `γ ∈ [1,2)`, so pointwise `u > 0` is not
enough — a uniform floor `δ > 0` is required, and compactness supplies it. -/
theorem uniform_positive_lower_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    {σ : ℝ} (hσ : 0 < σ) (hσT : σ ≤ S.T) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, δ ≤ intervalDomainLift (S.u σ) x := by
  have hcontOn :
      ContinuousOn (intervalDomainLift (S.u σ)) (Set.Icc (0 : ℝ) 1) :=
    ShenWork.Paper2.IntervalCarrySeamGradientContinuousOn.continuousOn_intervalDomainLift_of_hasContinuousSlices
      S.hcont hσ hσT
  have hne : (Set.Icc (0 : ℝ) 1).Nonempty := ⟨0, by norm_num⟩
  obtain ⟨x₀, hx₀mem, hx₀min⟩ :=
    isCompact_Icc.exists_isMinOn hne hcontOn
  refine ⟨intervalDomainLift (S.u σ) x₀, ?_, ?_⟩
  · rw [intervalDomainLift, dif_pos hx₀mem]
    exact S.hpos σ hσ hσT ⟨x₀, hx₀mem⟩
  · intro x hx
    exact hx₀min hx

/-- **THE single open leaf of the generic-`S` source ladder `hsrcB`.**

Per interior time and space point, the mild solution's slice has a time
derivative that is continuous and, on each compact interior window, uniformly
bounded.  Everything else in `hsrcB` (the B-form source `DuhamelSourceTimeC1`)
is reuse: the spatial ℓ¹/decay envelope is the already-solved representation-fed
weak-H² adapters (`logisticSource_/powerSource_duhamelSourceTimeC1_of_representation`,
`IntervalResolverPowerDecay`), and the source time-`C¹` fields follow from this
leaf by the chain rule (`logisticReaction_comp_hasDerivAt` takes the slice
`HasDerivAt`; `CoupledChemDivLocalChainRule.exists_local_slab` takes `∂ₜu`, with
the resolver `∂ₜv` from `∂ₜu` by elliptic linearity).

Non-circular route (cq33): the coefficient Duhamel identity
`c_k(t) = e^{-νλ_k t} c_k(0) + ∫₀ᵗ e^{-νλ_k(t-s)} s_k(s) ds` is differentiable in
`t` with `∂ₜc_k(t) = -νλ_k c_k(t) + s_k(t)` by Leibniz/FTC — needing ONLY `s_k`
*continuous* in time (the kernel `e^{-νλ_k(t-s)}` is smooth, no `1/(t-s)`
singularity at the coefficient level).  Then
`∂ₜu(t,x) = ∑_k (-νλ_k c_k(t) + s_k(t)) cos(kπx)` converges by the eigenvalue-
weighted ℓ¹ (`∑ λ_k|c_k| < ∞`, from the solved spatial ladder) plus `s_k ∈ ℓ¹`.
So the base breaks the circularity at the *continuity* level (supplied by
`S.hcont`), not the differentiability level.  The `δ`-floor
(`uniform_positive_lower_bound`) supplies the `u^{γ-1}` factor in the chain rule.

Drop-in target for Codex/cq33. -/
def MildSolutionSliceHasDerivAtTime
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀) : Prop :=
  ∃ udot : ℝ → intervalDomainPoint → ℝ,
    (∀ t, 0 < t → t < S.T → ∀ x : intervalDomainPoint,
        HasDerivAt (fun r => S.u r x) (udot t x) t) ∧
    (∀ t, 0 < t → t < S.T → Continuous (udot t)) ∧
    (∀ c T' : ℝ, 0 < c → T' < S.T → ∃ B : ℝ, 0 ≤ B ∧
        ∀ t ∈ Set.Icc c T', ∀ x : intervalDomainPoint, |udot t x| ≤ B)

/-- **THE second open engine of `hsrcB` — the R-engine (spatial ladder).**

The source-from-solution envelope pass: from a solution-coefficient envelope of
order `m` (`|cosineCoeffs (lift (S.u σ)) k| ≤ C/k^m` on the window) it produces
the next B-form source envelope of order `m-1` (the `-1` is the flux `∂ₓ`).  This
is the single nonlinear engine of the spatial ladder `R` (the eigenvalue-ℓ¹
representation of `S.u`): with it, the finite pass induction
  base `WindowSourceEnvelope 0` (from `S.hbound`) → heat pass `+2`
  (`ladder_pass_gain_envelope`, reuse) → this source pass `-1` → …
reaches `WindowSourceEnvelope 2`, whence `R` follows by
`restartCoeff_eigenvalue_weighted_summable_of_pass2_envelope`, and then `L`
(`MildSolutionSliceHasDerivAtTime`) and all of `hsrcB` follow.

Content — the verified cq31 (Q4277) flux-regularity chain, checked against the
commit-`fe90ef7c` definitions:

* logistic `u(a − b u^α)`: smooth Nemytskii of `u`, preserves order ⟹ `H^m`
  coeffs `O(k^{-m})` — but at HIGH order the `u^α`/`u^γ` Moser step is FALSE for
  `u` that can vanish; it REQUIRES the positive floor.  So the Nemytskii lemma is
  `‖u^γ‖_{H^r} ≤ C(‖u‖_∞, δ, r) · ‖u‖_{H^r}` for `u ≥ δ > 0` (thread the
  committed `uniform_positive_lower_bound δ`).  Without `δ` it is false at high
  order — do not state it unrestricted.
* chem-div flux chain (each step verified):
  `u ∈ H^r  ⟹  R = R[u] ∈ H^{r+2}` (elliptic Neumann resolver, +2 gain)
  `⟹  R_x (1+R)^{-β} ∈ H^{r+1}` (composition; `1+R ≥ 1`, so `(1+R)^{-β}` smooth)
  `⟹  Q = u · R_x(1+R)^{-β} ∈ H^r` (Sobolev algebra `H^s·H^s ⊂ H^s`, `s>1/2`)
  `⟹  ∂ₓQ ∈ H^{r-1}`.
  Hence the source-from-solution map is exactly `WCE m → WSE (m-1)` (the `-1` is
  the flux `∂ₓ`), and Bessel turns `H^{r-1}` into cosine-coeff `O(k^{-(r-1)})`.
* Termination: the chemotaxis Duhamel then gains `+2` relative to `∂ₓQ`, NET `+1`
  per sharp pass (`H^{r-1} → H^{r+1}`).  Even the repo's landed conservative
  `any α<1` per-pass gain still crosses the `H^{s}` (`s>5/2`) threshold in
  finitely many passes — finite termination holds without the sharp `+1`.

LEAN ROUTE (cq36/Q4296 — use THIS, not an abstract H^r Sobolev/Moser/elliptic
stack, which Mathlib lacks turnkey and is a large detour).  Prove the coefficient
decay DIRECTLY by elementary interval integration-by-parts on the cosine
coefficient:
  `source_k = ∫₀¹ S(x) cos(kπx) dx`; integrate by parts twice — each IBP yields a
  `1/(kπ)` factor and the boundary terms VANISH by the Neumann conditions (odd
  derivatives `S', S'''` vanish at `0,1`), giving
  `source_k = −(1/(kπ)²) ∫₀¹ S''(x) cos(kπx) dx`, hence `|source_k| ≤ (C/k²)·sup|S''|`.
  So `WindowSourceEnvelope (m-1)` reduces to a POINTWISE derivative bound
  `sup|∂ₓ^{(m-1)} (source)|` — obtained from pointwise bounds on `u, R, Q`
  (the δ-floor supplies `u^{γ-2}`), NOT from abstract `H^r`.  Matches the repo's
  existing coefficient-decay lemmas (`cosineCoeffs_C2_neumann_quadratic_decay_of_bound`).
  The elliptic R-gain is just the cosine MULTIPLIER `R̂_k = f̂_k/(μ+νλ_k)`
  (cq38): dividing coefficients gives the `+2` gain for free, Neumann automatic.
So the crux = { pointwise derivative bounds on `u^γ, R, Q` (δ-floored for `u^{γ-2}`)
  + elementary IBP giving the `k`-decay }.  Coefficient-level and elementary.

Drop-in target for Codex/cq31 (Q4277) + cq36 (Q4296). -/
def SourceFromSolutionEnvelopePass
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀) : Type :=
  ∀ {m : ℕ} {c T' : ℝ}, 0 < c → T' < S.T → 1 ≤ m →
    ShenWork.Paper2.IntervalCoeffLadderFull.WindowCoefficientEnvelope m c T'
      (fun σ n => cosineCoeffs (intervalDomainLift (S.u σ)) n) →
    ShenWork.Paper2.IntervalCoeffLadderFull.WindowSourceEnvelope (m - 1) c T'
      (bFormSourceCoeffs p S.u)

/-- The restart base coefficients `cosineCoeffs (lift (S.u τ))` are bounded by
`2 * S.M`, directly from slice continuity and boundedness — no cosine-series
circularity. -/
theorem restartBase_coeff_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    {τ : ℝ} (hτ : 0 < τ) (hτT : τ < S.T) :
    ∀ k, |cosineCoeffs (intervalDomainLift (S.u τ)) k| ≤ 2 * S.M := by
  have hcontOn :
      ContinuousOn (intervalDomainLift (S.u τ)) (Set.Icc (0 : ℝ) 1) :=
    ShenWork.Paper2.IntervalCarrySeamGradientContinuousOn.continuousOn_intervalDomainLift_of_hasContinuousSlices
      S.hcont hτ hτT.le
  have hbdd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |intervalDomainLift (S.u τ) x| ≤ S.M := by
    intro x hx
    rw [intervalDomainLift, dif_pos hx]
    exact S.hbound τ hτ hτT.le ⟨x, hx⟩
  exact ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
    hcontOn S.hM.le hbdd

/-- **The ladder base: `WindowCoefficientEnvelope 0` for the solution coefficients.**

From bounded, continuous slices (`S.hbound`, `S.hcont`) the cosine coefficients
of `S.u` are uniformly bounded by `2 * S.M` on every interior window — the
order-`0` solution envelope that seeds the spatial ladder.  Unconditional; no
source stub, no `cq31` dependency.  (The first *smoothing* step `0 → 1` is the
separate free-part heat-smoothing lemma; this is just the honest starting
point.) -/
def windowCoefficientEnvelope_zero_of_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    {c T' : ℝ} (hc : 0 < c) (hT' : T' < S.T) :
    ShenWork.Paper2.IntervalCoeffLadderFull.WindowCoefficientEnvelope 0 c T'
      (fun σ n => cosineCoeffs (intervalDomainLift (S.u σ)) n) where
  env := fun _ => 2 * S.M
  C := 2 * S.M + 1
  hC := by have := S.hM.le; positivity
  henv := by
    intro s hs k
    have hs0 : 0 < s := lt_of_lt_of_le hc hs.1
    have hsT : s < S.T := lt_of_le_of_lt hs.2 hT'
    exact restartBase_coeff_bound S hs0 hsT k
  hdecay := by
    intro k _hk
    have := S.hM.le
    simp only [pow_zero, div_one]
    linarith

/-- The explicit interior-slice cosine coefficient of `S.u σ`: the restart
coefficient based at `σ/2` with the B-form source, evaluated at increment
`σ/2`.  Used as the realization witness below. -/
def restartSliceCoeff
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀) (σ : ℝ) : ℕ → ℝ :=
  localRestartCoeff
    (cosineCoeffs (intervalDomainLift (S.u (σ / 2))))
    (fun r n => bFormSourceCoeffs p S.u (σ / 2 + r) n)
    (σ - σ / 2)

/-- Eigenvalue-weighted `ℓ¹` summability of the explicit interior-slice
coefficients, wired from `hsrcB` (parabolic gain, no pointwise ladder). -/
theorem restartSliceCoeff_eigenvalueSummable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    (hsrcB : DuhamelSourceTimeC1 (bFormSourceCoeffs p S.u))
    {σ : ℝ} (hσ : 0 < σ) (hσT : σ < S.T) :
    Summable (fun n =>
      unitIntervalCosineEigenvalue n * |restartSliceCoeff S σ n|) := by
  set τ : ℝ := σ / 2 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hτT : τ < S.T := by rw [hτdef]; linarith
  have hσmτ : σ - τ = τ := by rw [hτdef]; ring
  set a₀ : ℕ → ℝ := cosineCoeffs (intervalDomainLift (S.u τ)) with ha₀def
  set a : ℝ → ℕ → ℝ := fun r n => bFormSourceCoeffs p S.u (τ + r) n with hadef
  have ha₀_bd : ∀ k, |a₀ k| ≤ 2 * S.M := restartBase_coeff_bound S hτpos hτT
  have srcShift : DuhamelSourceTimeC1 a := by
    simpa [a, add_comm] using
      ShenWork.IntervalDuhamelSourceShift.DuhamelSourceTimeC1.shift_nonneg
        hsrcB hτpos.le
  have hsum :
      Summable (fun n =>
        unitIntervalCosineEigenvalue n * |localRestartCoeff a₀ a (σ - τ) n|) := by
    rw [hσmτ]
    exact ShenWork.IntervalResolverSpectralJointC2Producer.localRestartCoeff_eigenvalue_summable
      (τ := τ) (M := 2 * S.M) (a₀ := a₀) (a := a) hτpos ha₀_bd srcShift
  simpa [restartSliceCoeff, a₀, a, τ, hτdef] using hsum

/-- The explicit interior-slice cosine realization, wired from `hB_restart`. -/
theorem restartSliceCoeff_realization
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    (hB_restart : RestartRepresentation S)
    {σ : ℝ} (hσ : 0 < σ) (hσT : σ < S.T) :
    Set.EqOn (intervalDomainLift (S.u σ))
      (fun x => ∑' n, restartSliceCoeff S σ n * cosineMode n x)
      (Set.Icc (0 : ℝ) 1) := by
  intro x hx
  have hrep := hB_restart σ hσ hσT
  have hrep_at : ∀ y : intervalDomainPoint,
      S.u σ y =
        ∑' n,
          localRestartCoeff
            (cosineCoeffs (intervalDomainLift (S.u (σ / 2))))
            (fun r n => bFormSourceCoeffs p S.u (σ / 2 + r) n)
            (σ - σ / 2) n * cosineMode n y.1 :=
    hrep.self_of_nhds
  have hval := hrep_at ⟨x, hx⟩
  rw [intervalDomainLift, dif_pos hx]
  simpa [restartSliceCoeff] using hval

/-- **Shared `(C1)` export.**  Each interior slice of a conjugate mild solution
is `C²` on `[0,1]` with vanishing Neumann endpoint derivatives, from the two
source-side leaves.  Imported by both the HSpectral producer and the Jensen
supersolution. -/
theorem mildSlice_contDiffOn_two_neumann
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    (hsrcB : DuhamelSourceTimeC1 (bFormSourceCoeffs p S.u))
    (hB_restart : RestartRepresentation S)
    {σ : ℝ} (hσ : 0 < σ) (hσT : σ < S.T) :
    ContDiffOn ℝ 2 (intervalDomainLift (S.u σ)) (Set.Icc (0 : ℝ) 1)
      ∧ deriv (intervalDomainLift (S.u σ)) 0 = 0
      ∧ deriv (intervalDomainLift (S.u σ)) 1 = 0 :=
  ShenWork.IntervalCosineSliceRegularity.intervalDomainCosineSlice_conjunct7_unconditional
    (restartSliceCoeff_eigenvalueSummable S hsrcB hσ hσT)
    (restartSliceCoeff_realization S hB_restart hσ hσT)

#print axioms mildSlice_contDiffOn_two_neumann

end ShenWork.Paper2.IntervalMildPositiveTimeRegularity
