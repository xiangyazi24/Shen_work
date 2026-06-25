/-
  ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean

  B-form source `DuhamelSourceTimeC1On` for the conjugate Picard level 0
  (the heat semigroup) on a positive window `[c, T]`.

  The B-form source is:
    `bFormSourceCoeffs p (conjugatePicardIter p u₀ 0) s k
      = coupledLogisticSourceCoeffs p (conjugatePicardIter p u₀ 0) s k
        - p.χ₀ * coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0) s k`

  The logistic leg is exactly `conjLogSourceTimeC1On_level0` (existing).
  The chemDiv leg is new: it exploits the exponential spatial regularity of the
  heat semigroup `S(t)u₀` for `t ≥ c > 0` to produce the `DuhamelSourceTimeC1On`
  package for the chemotaxis-divergence coefficients.

  The two legs are combined via `bFormSource_duhamelSourceTimeC1On`.

  No existing files are modified.
-/
import ShenWork.Paper2.IntervalConjugateIterSourceTower
import ShenWork.Paper2.IntervalBFormSpectralHtime
import ShenWork.Paper2.IntervalBFormNegPartStrictPosBarrier
import ShenWork.Paper2.IntervalChemDivSpatialC2

open MeasureTheory Set Filter
open scoped Topology
open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalDomain)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalConjugatePicard
  (conjugatePicardIter ConjugateMildExistenceData)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledLogisticSourceCoeffs coupledChemDivSourceCoeffs
   coupledChemDivSourceLift coupledChemicalConcentration)
open ShenWork.IntervalBFormSpectral (bFormSourceCoeffs bFormSource_duhamelSourceTimeC1On)
open ShenWork.Paper2.ConjugateIterSourceTower (conjLogSourceTimeC1On_level0)
open ShenWork.IntervalPicardLevel0SourceTimeC1On (heatCoeff)
open ShenWork.Paper2 (PaperPositiveInitialDatum PositiveInitialDatum)
open ShenWork.IntervalDomain (intervalDomain)

noncomputable section

namespace ShenWork.Paper2.ConjugateLevel0BFormSourceOn

/-! ## Section 1: Definitional equalities

`conjugatePicardIter p u₀ 0` is definitionally `picardIter p u₀ 0`, which is
`fun t x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1`.
The logistic and chemDiv coefficient families for the conjugate level 0 are
therefore definitionally equal to those for `picardIter p u₀ 0`. -/

theorem conjChemDivCoeffs_level0_eq (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (s : ℝ) (k : ℕ) :
    coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0) s k =
    coupledChemDivSourceCoeffs p (picardIter p u₀ 0) s k := by
  rfl

theorem conjLogCoeffs_level0_eq (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (s : ℝ) (k : ℕ) :
    coupledLogisticSourceCoeffs p (conjugatePicardIter p u₀ 0) s k =
    coupledLogisticSourceCoeffs p (picardIter p u₀ 0) s k := by
  rfl

theorem bFormSourceCoeffs_level0_eq (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (s : ℝ) (k : ℕ) :
    bFormSourceCoeffs p (conjugatePicardIter p u₀ 0) s k =
    bFormSourceCoeffs p (picardIter p u₀ 0) s k := by
  rfl

/-! ## Section 2: ChemDiv source `DuhamelSourceTimeC1On` for heat semigroup level 0

The chemotaxis-divergence source at level 0 is:
  `coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s`
    = `intervalDomainLift (intervalDomainChemotaxisDiv p (u₀_heat s)
        (coupledChemicalConcentration p u₀_heat s))`
where `u₀_heat = conjugatePicardIter p u₀ 0` is the heat semigroup.

For `s ≥ c > 0`, the heat semigroup has exponential coefficient decay
`|cosineCoeffs(S(s)u₀) k| ≤ M₀ · exp(-c · λ_k)`, which gives spatial C∞
regularity.  The chemDiv source inherits spatial C² regularity via the chain
rule through the Neumann resolver.

We package the resulting `DuhamelSourceTimeC1On` as a structure carrying
the sorry'd infrastructure lemmas. -/

/-- **Hypothesis bundle** for the level-0 chemDiv source time-C¹ windowed package.

These hypotheses are in principle derivable from:
  (a) the exponential spatial regularity of the heat semigroup on `[c,T]`,
  (b) the chain rule through the Neumann resolver,
  (c) the resulting weak-H² Neumann and coefficient-decay estimates.

Each field is a genuine mathematical fact about the heat semigroup level 0;
they are taken as hypotheses here because the derivation chain is long
(each needs 50+ lines of new infrastructure connecting heat semigroup
regularity to the chemDiv chain-rule output). -/
structure Level0ChemDivSourceData (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) (c T : ℝ) where
  /-- Summable envelope for `coupledChemDivSourceCoeffs` on `[c,T]`. -/
  envelope : ℕ → ℝ
  henv_summable : Summable envelope
  henv_bound : ∀ s ∈ Icc c T, ∀ n,
    |coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0) s n| ≤ envelope n
  /-- Time derivative of the chemDiv coefficients. -/
  adot : ℝ → ℕ → ℝ
  hderiv : ∀ s ∈ Icc c T, ∀ n,
    HasDerivWithinAt
      (fun r => coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0) r n)
      (adot s n) (Icc c T) s
  hadotcont : ∀ n, ContinuousOn (fun s => adot s n) (Icc c T)
  /-- Uniform bound on the time-derivative coefficients. -/
  derivBound : ℝ
  hderivBound : ∀ s ∈ Icc c T, ∀ n, |adot s n| ≤ derivBound

/-- Build `DuhamelSourceTimeC1On` for the chemDiv source at level 0 from the
hypothesis bundle. -/
noncomputable def chemDivSourceTimeC1On_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {c T : ℝ}
    (D : Level0ChemDivSourceData p u₀ c T) :
    DuhamelSourceTimeC1On
      (coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0)) c T where
  adot := D.adot
  hderiv := D.hderiv
  hadotcont := D.hadotcont
  envelope := D.envelope
  henv_summable := D.henv_summable
  henv_bound := D.henv_bound
  derivBound := D.derivBound
  hderivBound := D.hderivBound

/-! ## Section 3: Constructing `Level0ChemDivSourceData` from heat semigroup regularity

The heat semigroup `S(t)u₀` on `[c,T]` with `c > 0` has:
  - Exponential coefficient decay: `|cosineCoeffs(S(s)u₀) k| ≤ M₀ · exp(-c·λ_k)`
  - Spatial C∞ regularity (all spatial derivatives have exponential coefficient decay)
  - The chemDiv source `∇·(u·χ(v)·∇v)` at each time slice is C² with Neumann BCs
  - The time derivative of the chemDiv coefficients exists and is continuous

The construction below sorry's the individual regularity estimates.  Each sorry
represents a substantial but straightforward derivation from the heat semigroup's
known regularity properties. -/

/-- Summable envelope for the chemDiv source coefficients of the heat semigroup
on a positive window.  The heat semigroup's exponential spatial decay gives
the chemDiv source (which involves products and compositions of C∞ functions)
a quadratic or better coefficient decay, yielding a summable envelope. -/
theorem level0_chemDiv_envelope_summable
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M M₀ : ℝ} (hc : 0 < c) (_hcT : c ≤ T)
    (_hu₀_cont : Continuous u₀)
    (_hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (_hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
    (_hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M) :
    ∃ (envelope : ℕ → ℝ),
      Summable envelope ∧
      ∀ s ∈ Icc c T, ∀ n,
        |coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0) s n| ≤ envelope n := by
  -- ── Sub-goal 1: per-slice weak-H² Neumann data with uniform second-derivative bound ──
  -- Chain: heat semigroup C⁴ (heatSemigroup_contDiff_four) → resolver C⁴ (sorry) →
  -- chemDivSource_weakH2_of_cosineRep → IntervalWeakH2Neumann per slice.
  -- The uniform L¹(|f''|) bound over [c,T] uses compactness + continuity of s ↦ f''_s.
  -- Each step is >20 lines of new infrastructure; sorry'd as a block.
  have hH2 : ∃ (B : ℝ), 0 ≤ B ∧
      ∀ s ∈ Icc c T,
        ∃ (h2 : ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann
          (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s)),
        (∫ x in (0 : ℝ)..1, |h2.secondDeriv x|) ≤ B := by
    sorry
    -- Proof sketch (>20 lines each):
    -- For each s ∈ [c,T] with c > 0:
    --   U_cos s := fun x => ∑' k, (exp(-s*λ_k) * heatCoeff u₀ k) * cosineMode k x
    --   ContDiff ℝ 4 (U_cos s) — from heatSemigroup_contDiff_four (s > 0)
    --   Even/symm1 of U_cos s — from cosineMode_neg/cosineMode_add_two via tsum_congr
    --   V_cos s := resolver cosine series — ContDiff ℝ 4, even, symm1 (sorry)
    --   chemDivSource_weakH2_of_cosineRep → IntervalWeakH2Neumann
    --   Uniform B from compactness of [c,T] and continuity of the second-derivative norm
  -- ── Sub-goal 2: uniform sup bound on the chemDiv source slices ──
  -- The chemDiv source is a continuous function on [0,1] for each s ∈ [c,T], and
  -- is uniformly bounded because u and v are uniformly bounded.
  have hSup : ∃ (Msup : ℝ), 0 ≤ Msup ∧
      (∀ s ∈ Icc c T,
        ContinuousOn (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s)
          (Icc (0 : ℝ) 1)) ∧
      (∀ s ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
        |coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s x| ≤ Msup) := by
    sorry
    -- Proof sketch (>20 lines): u bounded by M, v bounded (resolver of bounded u),
    -- so the chemDiv source = deriv(u · v' / (1+v)^β) is bounded on [0,1] × [c,T]
    -- by a constant depending on M, the C² norms, and p.β.
  -- ── Extract the data ──
  obtain ⟨B, hBnn, hH2_data⟩ := hH2
  obtain ⟨Msup, hMsupnn, hcont_slices, hsup_slices⟩ := hSup
  -- ── Build the envelope ──
  -- For k = 0: |c₀| ≤ 2 * Msup (from cosine coefficient of bounded continuous function)
  -- For k ≥ 1: |cₖ| ≤ 2B / (kπ)² ≤ Cenv / (kπ)² (from weak-H² quadratic decay)
  -- Unified constant: Cenv = 2 * max B Msup ≥ both 2B and 2Msup.
  -- Envelope: Cenv · reciprocalSquareTerm (max 1 k)
  --   k=0: Cenv · 1/1² = Cenv ≥ 2Msup ≥ |c₀|
  --   k≥1: Cenv · 1/k² ≥ Cenv/(kπ)² ≥ 2B/(kπ)² ≥ |cₖ|     (since 1/k² ≥ 1/(kπ)²)
  -- Summability: Cenv · reciprocalSquareTerm is summable by reciprocalSquareTerm_summable.
  -- But reciprocalSquareTerm 0 = 1/0² = ... undefined. Let me use max 1 k instead.
  --
  -- Simpler approach: Use ∑ 1/k² convergence starting from k=1, plus a finite value at k=0.
  -- Define envelope k = Cenv * (1 / ((max 1 k : ℝ) ^ 2)).
  -- At k=0: envelope 0 = Cenv * (1/1) = Cenv ≥ 2Msup.
  -- At k≥1: envelope k = Cenv/k² ≥ Cenv/(kπ)² ≥ 2B/(kπ)² (since π² ≥ 1).
  -- Summable: dominated by Cenv · 1/k² (the 1/(max 1 k)² series).
  set Cenv := 2 * max B Msup with hCenv_def
  have hCenv_nn : 0 ≤ Cenv := by positivity
  have hCenv_ge_2B : 2 * B ≤ Cenv := by
    simp only [hCenv_def]; exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
  have hCenv_ge_2Msup : 2 * Msup ≤ Cenv := by
    simp only [hCenv_def]; exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
  -- The envelope: Cenv / (max 1 k)²
  refine ⟨fun k => Cenv / (max 1 (k : ℝ)) ^ 2, ?_, ?_⟩
  · -- ── Summability of the envelope ──
    -- Split: envelope = (indicator at 0) + (tail for k ≥ 1).
    -- At k=0: Cenv/(max 1 0)² = Cenv/1 = Cenv.
    -- At k≥1: Cenv/(max 1 k)² = Cenv/k².
    -- The k=0 indicator is summable (single nonzero term).
    -- The k≥1 tail is summable by comparison with reciprocalSquareTerm.
    have hsplit : (fun k => Cenv / (max 1 (k : ℝ)) ^ 2) =
        (fun k => if k = 0 then Cenv else 0) +
        (fun k => if k = 0 then 0 else Cenv / (k : ℝ) ^ 2) := by
      ext k; simp only [Pi.add_apply]
      by_cases hk : k = 0
      · subst hk; simp
      · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
        simp [hk, max_eq_right hk1]
    rw [hsplit]
    apply Summable.add
    · -- Single-term at k=0
      apply summable_of_ne_finset_zero (s := {0})
      intro k hk; simp [Finset.mem_singleton] at hk; simp [hk]
    · -- Tail for k ≥ 1: dominated by Cenv * reciprocalSquareTerm
      apply Summable.of_nonneg_of_le
        (fun k => by split_ifs <;> positivity)
        (fun k => ?_)
        (ShenWork.IntervalDomainRegularityBootstrap.reciprocalSquareTerm_summable.mul_left Cenv)
      by_cases hk : k = 0
      · simp [hk]; positivity
      · simp only [hk, ite_false,
            ShenWork.IntervalDomainRegularityBootstrap.reciprocalSquareTerm, mul_one_div,
            le_refl]
  · -- ── Uniform bound on coefficients ──
    intro s hs n
    obtain ⟨h2s, hBs⟩ := hH2_data s hs
    by_cases hn : n = 0
    · -- Case k = 0: |c₀| ≤ 2 * Msup ≤ Cenv = Cenv / (max 1 0)²
      subst hn
      simp only [Nat.cast_zero, max_eq_left (by norm_num : (0 : ℝ) ≤ 1), one_pow, div_one]
      have h0 := ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
        (hcont_slices s hs) hMsupnn (hsup_slices s hs) 0
      exact le_trans h0 hCenv_ge_2Msup
    · -- Case k ≥ 1: |cₖ| ≤ 2B/(kπ)² ≤ Cenv/(kπ)² ≤ Cenv/k²
      have hk : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
      have hmax_eq : max 1 (n : ℝ) = (n : ℝ) :=
        max_eq_right (by exact_mod_cast hk : (1 : ℝ) ≤ (n : ℝ))
      simp only [hmax_eq]
      have hdecay :=
        ShenWork.IntervalSourceDecayQuantitative.intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound
          h2s hBs n hk
      calc |ShenWork.IntervalNeumannFullKernel.cosineCoeffs
              (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s) n|
          ≤ 2 * B / ((n : ℝ) * Real.pi) ^ 2 := hdecay
        _ ≤ Cenv / ((n : ℝ) * Real.pi) ^ 2 := by
            gcongr; exact hCenv_ge_2B
        _ ≤ Cenv / (n : ℝ) ^ 2 := by
            apply div_le_div_of_nonneg_left hCenv_nn (by positivity)
            have hpi_ge_one : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
            exact pow_le_pow_left₀ (le_of_lt hn_pos)
              (le_mul_of_one_le_right (le_of_lt hn_pos) hpi_ge_one) 2

/-- Time-derivative and continuity data for the chemDiv coefficients of the
heat semigroup on a positive window.  The time derivative is computed by the
chain rule: the heat semigroup evolves as ∂ₜu = Δu, so ∂ₜ(chemDiv source)
can be expressed in terms of the spatial derivatives (which are well-controlled
on the positive window). -/
theorem level0_chemDiv_timeDerivData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M M₀ : ℝ} (hc : 0 < c) (_hcT : c ≤ T)
    (_hu₀_cont : Continuous u₀)
    (_hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (_hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
    (_hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M) :
    ∃ (adot : ℝ → ℕ → ℝ) (Mdot : ℝ),
      (∀ s ∈ Icc c T, ∀ n,
        HasDerivWithinAt
          (fun r => coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0) r n)
          (adot s n) (Icc c T) s) ∧
      (∀ n, ContinuousOn (fun s => adot s n) (Icc c T)) ∧
      (∀ s ∈ Icc c T, ∀ n, |adot s n| ≤ Mdot) := by
  -- The time derivative of coupledChemDivSourceCoeffs is computed via the
  -- chain rule.  Since u = S(t)u₀ satisfies ∂ₜu = Δu (the heat equation),
  -- and the chemDiv source is a smooth functional of u and its spatial
  -- derivatives, the time derivative ∂ₜ(chemDiv source coefficients) exists
  -- and is continuous on [c,T] with c > 0.
  --
  -- The uniform bound follows from the uniform bounds on u, ∂ₓu, ∂²ₓu,
  -- ∂ₜu, and ∂ₜ∂ₓu on the compact set [c,T] × [0,1], all of which are
  -- available from the heat semigroup's explicit cosine-series representation.
  sorry

/-- Construct `Level0ChemDivSourceData` from the basic heat semigroup hypotheses.
This combines the envelope and time-derivative data. -/
noncomputable def level0ChemDivSourceData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M M₀ : ℝ} (hc : 0 < c) (hcT : c ≤ T)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
    (hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M) :
    Level0ChemDivSourceData p u₀ c T := by
  sorry
  -- Blocked on chemDiv C² regularity infrastructure (IntervalChemDivSpatialC2.lean).
  -- Chain: heat semigroup C⁴ → resolver C⁴ → flux C³ → chemDiv C² → H² → decay → envelope
  --        + chain rule for time derivatives → adot + continuity + bound

/-! ## Section 4: The logistic source `DuhamelSourceTimeC1On` for level 0

This is an alias for the existing `conjLogSourceTimeC1On_level0`.
We restate it here in terms of `coupledLogisticSourceCoeffs` (which is
definitionally equal to the cosine-coefficient family of `logisticLifted`). -/

/-- The logistic source `DuhamelSourceTimeC1On` for conjugate level 0, restated
in terms of `coupledLogisticSourceCoeffs`.  Definitionally equal to
`conjLogSourceTimeC1On_level0` since
`cosineCoeffs (logisticLifted p (conjugatePicardIter p u₀ 0 s)) k
  = coupledLogisticSourceCoeffs p (conjugatePicardIter p u₀ 0) s k`. -/
noncomputable def level0_logisticSource_timeC1On
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M G1 G2 Udot M₀ : ℝ}
    (hc : 0 < c) (hcT : c < T)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
    (hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M)
    (hG1 : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (conjugatePicardIter p u₀ 0 σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (conjugatePicardIter p u₀ 0 σ))) x| ≤ G2)
    (hUdot : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondValue
        σ (heatCoeff u₀) x| ≤ Udot) :
    DuhamelSourceTimeC1On
      (coupledLogisticSourceCoeffs p (conjugatePicardIter p u₀ 0)) c T :=
  -- `logisticLifted p (conjugatePicardIter p u₀ 0 s)` is definitionally
  -- `coupledLogisticSourceLift p (conjugatePicardIter p u₀ 0) s`, so
  -- `cosineCoeffs (logisticLifted …) k = coupledLogisticSourceCoeffs …` def-eq.
  conjLogSourceTimeC1On_level0 p hc hcT hα ha hb hu₀_cont hu₀_bound
    hpos hub hG1 hG2 hUdot

/-! ## Section 5: The B-form source `DuhamelSourceTimeC1On` for level 0

Combine the logistic and chemDiv legs via `bFormSource_duhamelSourceTimeC1On`. -/

/-- **Main theorem.**  The B-form source coefficients of the heat semigroup
(conjugate Picard level 0) satisfy `DuhamelSourceTimeC1On` on a positive
window `[c, T]`.

**Logistic leg:** Discharged from `conjLogSourceTimeC1On_level0` (existing,
no sorry).

**ChemDiv leg:** Discharged from `Level0ChemDivSourceData` which collects
the summable envelope and time-derivative data for the chemDiv coefficients.
The data is constructed via `level0ChemDivSourceData`, which sorry's
`level0_chemDiv_envelope_summable` and `level0_chemDiv_timeDerivData`.

**Sorry summary:**
  - `level0_chemDiv_envelope_summable`: needs ~100 lines wiring heat semigroup
    exponential spatial decay through the chemDiv chain rule to produce a
    summable `(kπ)⁻²`-type envelope.  The mathematical argument is:
    S(s)u₀ is C∞ for s > 0 ⟹ chemDiv source is weak-H² Neumann ⟹
    coefficient decay ≤ C/(kπ)² ⟹ summable.
  - `level0_chemDiv_timeDerivData`: needs ~100 lines wiring the heat equation
    ∂ₜu = Δu through the chain rule for the chemDiv functional to produce
    the time-derivative coefficients adot, their continuity, and uniform bound.
    The mathematical argument is: ∂ₜ(chemDiv(S(t)u₀)) = chain-rule with ∂ₜu = Δu,
    all spatial derivatives bounded on [c,T]×[0,1]. -/
noncomputable def level0_bFormSource_duhamelSourceTimeC1On
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M G1 G2 Udot M₀ : ℝ}
    (hc : 0 < c) (hcT : c < T)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
    (hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M)
    (hG1 : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (conjugatePicardIter p u₀ 0 σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (conjugatePicardIter p u₀ 0 σ))) x| ≤ G2)
    (hUdot : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondValue
        σ (heatCoeff u₀) x| ≤ Udot)
    (chemData : Level0ChemDivSourceData p u₀ c T) :
    DuhamelSourceTimeC1On
      (bFormSourceCoeffs p (conjugatePicardIter p u₀ 0)) c T :=
  bFormSource_duhamelSourceTimeC1On
    (level0_logisticSource_timeC1On p hc hcT hα ha hb hu₀_cont hu₀_bound
      hpos hub hG1 hG2 hUdot)
    (chemDivSourceTimeC1On_of_data chemData)

/-- **Self-contained variant** that constructs `Level0ChemDivSourceData`
internally from the basic heat semigroup hypotheses.  Uses sorry. -/
noncomputable def level0_bFormSource_duhamelSourceTimeC1On_auto
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M G1 G2 Udot M₀ : ℝ}
    (hc : 0 < c) (hcT : c < T)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
    (hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M)
    (hG1 : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (conjugatePicardIter p u₀ 0 σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (conjugatePicardIter p u₀ 0 σ))) x| ≤ G2)
    (hUdot : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondValue
        σ (heatCoeff u₀) x| ≤ Udot) :
    DuhamelSourceTimeC1On
      (bFormSourceCoeffs p (conjugatePicardIter p u₀ 0)) c T :=
  level0_bFormSource_duhamelSourceTimeC1On p hc hcT hα ha hb hu₀_cont hu₀_bound
    hpos hub hG1 hG2 hUdot
    (level0ChemDivSourceData p hc hcT.le hu₀_cont hu₀_bound hpos hub)

/-! ## Section 6: ConjugateMildExistenceData + PaperPositiveInitialDatum interface

The final consumer typically has `ConjugateMildExistenceData p u₀` (which
carries the ball/positivity/continuity data for the Picard iterates) and
`PaperPositiveInitialDatum` (which carries the initial datum regularity).
We provide a convenience wrapper that extracts the necessary hypotheses
from these structures. -/

/-- Extract the heat-semigroup positivity on `[c,T]` from
`ConjugateMildExistenceData` for level 0. -/
theorem level0_heat_pos_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (_D : ConjugateMildExistenceData p u₀)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {c : ℝ} (hc : 0 < c) (_hcT : c ≤ _D.T) :
    ∀ σ ∈ Icc c _D.T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x := by
  intro σ hσ x hx
  have hσpos : 0 < σ := lt_of_lt_of_le hc hσ.1
  simp only [intervalDomainLift, dif_pos hx, conjugatePicardIter]
  exact ShenWork.Paper2.BFormPositiveDatumNegPart.intervalFullSemigroupOperator_pos_of_positiveInitialDatum
    hu₀ hσpos x

/-- Extract the heat-semigroup sup bound on `[c,T]` from
`ConjugateMildExistenceData` for level 0. -/
theorem level0_heat_sup_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀)
    {c : ℝ} (hc : 0 < c) (hcT : c ≤ D.T) :
    ∀ σ ∈ Icc c D.T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ D.M := by
  intro σ hσ x hx
  -- D.hbase_ball gives |conjugatePicardIter p u₀ 0 t x| ≤ D.M for 0 < t ≤ D.T.
  -- The lift on Icc 0 1 equals the subtype value, so the bound transfers.
  have hσpos : 0 < σ := lt_of_lt_of_le hc hσ.1
  have hσT : σ ≤ D.T := hσ.2
  simp only [intervalDomainLift, dif_pos hx]
  have hball := D.hbase_ball σ hσpos hσT ⟨x, hx⟩
  exact le_of_abs_le hball

end ShenWork.Paper2.ConjugateLevel0BFormSourceOn
