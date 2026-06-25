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
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
import ShenWork.PDE.IntervalChemDivTimeDerivative

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
open ShenWork.Paper2.HeatSemigroupHighRegularity (heatSemigroup_contDiff_four)
open ShenWork.Paper2.ChemDivSpatialC2 (chemDivSource_weakH2_of_cosineRep)
open ShenWork.CosineSpectrum (cosineMode)

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
  -- ── Sub-goal 1: per-slice weak-H² Neumann data with uniform L¹(|f''|) bound ──
  -- Chain: heat semigroup C⁴ (heatSemigroup_contDiff_four) → resolver C⁴ (sorry) →
  -- chemDivSource_weakH2_of_cosineRep → IntervalWeakH2Neumann per slice.
  -- The uniform L¹(|f''|) bound over [c,T] uses compactness + continuity of s ↦ f''_s.
  -- Each step is >20 lines of new infrastructure; sorry'd as a block.
  have hH2 : ∃ (B : ℝ), 0 ≤ B ∧
      ∀ s ∈ Icc c T,
        ∃ (h2 : ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann
          (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s)),
        (∫ x in (0 : ℝ)..1, |h2.secondDeriv x|) ≤ B := by
    -- Per-slice H2 via chemDivSource_weakH2_of_cosineRep.
    -- U_cos s := heat semigroup cosine series (C⁴ from heatSemigroup_contDiff_four).
    -- V_cos s := resolver cosine series (C⁴ sorry — only C² available in codebase).
    -- The per-slice H2 is well-typed; the uniform L¹ bound is sorry'd.
    --
    -- Step 1: For each s ∈ [c,T], produce IntervalWeakH2Neumann per slice.
    have hH2_per_slice : ∀ s ∈ Icc c T,
        ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann
          (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s) := by
      intro s hs
      have hs_pos : 0 < s := lt_of_lt_of_le hc hs.1
      -- U_cos: the heat semigroup cosine series is C⁴ for s > 0
      set U_cos := fun x => ∑' k,
        (Real.exp (-s * unitIntervalCosineEigenvalue k) * heatCoeff u₀ k) *
          cosineMode k x with hU_cos_def
      have hU_C4 : ContDiff ℝ 4 U_cos :=
        heatSemigroup_contDiff_four _hu₀_bound hs_pos
      -- U_cos agrees with intervalDomainLift (conjugatePicardIter p u₀ 0 s) on [0,1]
      have hU_agree : ∀ x ∈ Icc (0 : ℝ) 1,
          intervalDomainLift (conjugatePicardIter p u₀ 0 s) x = U_cos x := by
        intro x hx
        simp only [intervalDomainLift, dif_pos hx, conjugatePicardIter]
        sorry -- spectral bridge: intervalFullSemigroupOperator = cosineHeatValue on [0,1]
        -- Route: intervalFullSemigroupOperator_eq_cosineHeatValue_Icc (needs Continuous f)
        -- + cosineHeatSynthesis_eq_cosineHeatValue (tsum reorder)
      -- Inline helpers for cosineMode parity (cosineMode k x = cos(kπx))
      have cosineMode_neg' : ∀ (k : ℕ) (x : ℝ),
          cosineMode k (-x) = cosineMode k x := by
        intro k x; unfold cosineMode
        rw [show (k : ℝ) * Real.pi * (-x) = -((k : ℝ) * Real.pi * x) from by ring,
          Real.cos_neg]
      have cosineMode_add_two' : ∀ (k : ℕ) (x : ℝ),
          cosineMode k (x + 2) = cosineMode k x := by
        intro k x; unfold cosineMode
        rw [show (k : ℝ) * Real.pi * (x + 2)
              = (k : ℝ) * Real.pi * x + ((k : ℤ) : ℝ) * (2 * Real.pi) from by
            push_cast; ring,
          Real.cos_add_int_mul_two_pi _ (k : ℤ)]
      -- U_cos is even: cosineMode k (-x) = cosineMode k x
      have hU_even : ∀ x, U_cos (-x) = U_cos x := by
        intro x; simp only [hU_cos_def]
        exact tsum_congr (fun k => by congr 1; exact cosineMode_neg' k x)
      -- U_cos is symmetric about x=1: U_cos(2-x) = U_cos(x)
      have hU_symm1 : ∀ x, U_cos (2 - x) = U_cos x := by
        intro x
        rw [show (2 : ℝ) - x = (-x) + 2 from by ring]
        simp only [hU_cos_def]
        rw [show (fun k => (Real.exp (-s * unitIntervalCosineEigenvalue k) *
              heatCoeff u₀ k) * cosineMode k ((-x) + 2)) =
            (fun k => (Real.exp (-s * unitIntervalCosineEigenvalue k) *
              heatCoeff u₀ k) * cosineMode k (-x)) from
          funext (fun k => by congr 1; exact cosineMode_add_two' k (-x))]
        exact hU_even x
      -- V_cos: resolver cosine series — C⁴, even, symm1, agrees on [0,1]
      -- SORRY: resolver C⁴ requires elliptic gain from H^σ with σ > 4.5; only C² proved.
      have hV_data : ∃ V_cos : ℝ → ℝ,
          ContDiff ℝ 4 V_cos ∧
          (∀ x, (0 : ℝ) < 1 + V_cos x) ∧
          (∀ x ∈ Icc (0 : ℝ) 1,
            intervalDomainLift (coupledChemicalConcentration p
              (conjugatePicardIter p u₀ 0) s) x = V_cos x) ∧
          (∀ x, V_cos (-x) = V_cos x) ∧
          (∀ x, V_cos (2 - x) = V_cos x) := by
        sorry
        -- Proof sketch: V_cos = resolverValue p.μ (cosineCoeffs (lift (u s))) x.
        -- Even/symm1: from resolverValue_even, resolverValue_add_two.
        -- C⁴: resolver gain is +2 (elliptic regularity); u ∈ H^{4+ε} for s > 0
        --   → v ∈ H^{6+ε} → C⁴.  Needs MemHSigma σ with σ > 4.5 for the source,
        --   which follows from the exponential coefficient decay of the heat semigroup.
        --   Infrastructure gap: only resolverValue_contDiff_two (C²) is proved.
        -- Agreement: from the committed resolver spectral bridge on [0,1].
        -- Positivity: from resolverValue_nonneg (u ≥ 0 on [c,T]) + resolver structure.
      let V_cos := hV_data.choose
      have hV := hV_data.choose_spec
      exact chemDivSource_weakH2_of_cosineRep hU_C4 hV.1 hV.2.1
        hU_agree hV.2.2.1 hU_even hV.2.2.2.1 hU_symm1 hV.2.2.2.2
    -- Step 2: Uniform L¹(|f''|) bound over [c,T].
    -- From compactness of [c,T] and continuity of the second-derivative norm.
    have hL1_uniform : ∃ (B : ℝ), 0 ≤ B ∧ ∀ s (hs : s ∈ Icc c T),
        (∫ x in (0 : ℝ)..1, |(hH2_per_slice s hs).secondDeriv x|) ≤ B := by
      sorry
      -- Proof sketch: for each s, (hH2_per_slice s hs).secondDeriv is the
      -- classical second derivative of the chemDiv source (deriv²(flux) for the
      -- cosine representative). On the compact set [c,T], the second derivative
      -- is jointly continuous in (s,x), hence the L¹ norm is continuous in s on
      -- [c,T], hence bounded on the compact set.
    obtain ⟨B, hBnn, hL1⟩ := hL1_uniform
    exact ⟨B, hBnn, fun s hs => ⟨hH2_per_slice s hs, hL1 s hs⟩⟩
  -- ── Sub-goal 2: uniform sup bound and continuity of chemDiv source slices ──
  have hSup : ∃ (Msup : ℝ), 0 ≤ Msup ∧
      (∀ s ∈ Icc c T,
        ContinuousOn (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s)
          (Icc (0 : ℝ) 1)) ∧
      (∀ s ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
        |coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s x| ≤ Msup) := by
    sorry
    -- Proof sketch (>20 lines): u bounded by M, v bounded (resolver of bounded u),
    -- chemDiv source = deriv(u · v' / (1+v)^β) bounded on [0,1] × [c,T].
  -- ── Extract and build envelope ──
  obtain ⟨B, hBnn, hH2_data⟩ := hH2
  obtain ⟨Msup, hMsupnn, hcont_slices, hsup_slices⟩ := hSup
  -- Envelope: Cenv / (max 1 k)² where Cenv = 2 · max B Msup.
  -- k=0: Cenv ≥ 2Msup ≥ |c₀| (from cosineCoeffs_abs_le_of_continuous_bounded).
  -- k≥1: Cenv/k² ≥ Cenv/(kπ)² ≥ 2B/(kπ)² ≥ |cₖ| (from H² quadratic decay, π≥1).
  set Cenv := 2 * max B Msup with hCenv_def
  have hCenv_nn : 0 ≤ Cenv := mul_nonneg (by norm_num) (hBnn.trans (le_max_left _ _))
  have hCenv_ge_2B : 2 * B ≤ Cenv := by
    simp only [hCenv_def]; exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
  have hCenv_ge_2Msup : 2 * Msup ≤ Cenv := by
    simp only [hCenv_def]; exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
  -- Summability: Cenv / (max 1 k)² is summable (bounded by Cenv/k² for k≥1).
  -- Coefficient bound: mode 0 from sup bound, mode k≥1 from H² quadratic decay.
  -- The complete calculation uses hH2_data for quadratic decay and
  -- hcont_slices/hsup_slices for the zeroth mode.
  exact ⟨fun k => Cenv / (max 1 (k : ℝ)) ^ 2,
    by
      sorry, -- Summability of Cenv/(max 1 k)²: comparison with 1/k² series
    fun s hs n => by
      obtain ⟨h2s, hBs⟩ := hH2_data s hs
      by_cases hn : n = 0
      · -- mode 0: |c₀| ≤ 2·Msup ≤ Cenv = Cenv/(max 1 0)²
        subst hn; simp only [Nat.cast_zero, max_eq_left
          (by norm_num : (0 : ℝ) ≤ 1), one_pow, div_one]
        open ShenWork.IntervalMildPicardRegularity in
        exact le_trans
          (cosineCoeffs_abs_le_of_continuous_bounded
            (hcont_slices s hs) hMsupnn
            (hsup_slices s hs) 0)
          hCenv_ge_2Msup
      · -- mode k≥1: |cₖ| ≤ 2B/(kπ)² ≤ Cenv/(kπ)² ≤ Cenv/k²
        have hk : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        have hn_pos : (0 : ℝ) < (n : ℝ) := by
          exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
        simp only [max_eq_right (show (1 : ℝ) ≤ (n : ℝ) by
          exact_mod_cast hk)]
        open ShenWork.IntervalSourceDecayQuantitative in
        calc |cosineCoeffs (coupledChemDivSourceLift
                p (conjugatePicardIter p u₀ 0) s) n|
            ≤ 2 * B / ((n : ℝ) * Real.pi) ^ 2 :=
              intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound
                h2s hBs n hk
          _ ≤ Cenv / ((n : ℝ) * Real.pi) ^ 2 := by
              gcongr
          _ ≤ Cenv / (n : ℝ) ^ 2 := by
              apply div_le_div_of_nonneg_left hCenv_nn
                (by positivity)
              exact pow_le_pow_left₀ (le_of_lt hn_pos)
                (le_mul_of_one_le_right (le_of_lt hn_pos)
                  (by linarith [Real.pi_gt_three]))
                2⟩

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
  -- Canonical adot: the cosine coefficients of the pointwise chain-rule field
  -- coupledChemDivTimeDerivativeLift p (conjugatePicardIter p u₀ 0) s.
  -- The chain rule for ∂ₜ(∇·(u·χ(v)·∇v)) uses ∂ₜu = Δu (the heat equation).
  --
  -- Step 1: CoupledChemDivLocalChainRule for the heat semigroup trajectory.
  -- This is the pointwise chain rule + local dominated-convergence slab.
  -- SORRY: needs ~60 lines connecting the heat equation ∂ₜu = Δu through
  -- the composed chemDiv functional to produce the local HasDerivAt slab.
  have hchain : ShenWork.IntervalCoupledRegularityBootstrap.CoupledChemDivLocalChainRule
      p (conjugatePicardIter p u₀ 0) := by
    sorry
    -- The heat semigroup u(s,x) = S(s)u₀(x) satisfies ∂ₜu = Δu with
    -- smooth spatial dependence for s > 0.  The resolver v = Γ_μ(u) inherits
    -- time differentiability from the spectral route.  The chemDiv source
    -- F(s,x) = ∂ₓ(u·∂ₓv/(1+v)^β) is a smooth composition, so ∂ₜF exists
    -- and equals the chain-rule expression coupledChemDivTimeDerivativeLift.
    -- The local slab hypothesis (HasDerivAt on a ball + joint continuity of
    -- the derivative field) follows from the joint smoothness of the heat
    -- semigroup on (0,∞)×[0,1].
  -- Step 2: Joint continuity of the chain-rule field on [c,T]×[0,1].
  -- SORRY: needs ~40 lines from the resolver time-regularity route.
  have hjointcont : ContinuousOn
      (Function.uncurry (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivTimeDerivativeLift
        p (conjugatePicardIter p u₀ 0)))
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
    sorry
    -- From coupledChemicalTimeDerivative_jointContinuousOn_closed and the
    -- composition chain for the chemDiv time derivative.  The heat semigroup
    -- trajectory and its time/spatial derivatives are jointly continuous on
    -- (0,∞) × ℝ, hence on the compact slab [c,T] × [0,1] with c > 0.
  -- Step 3: HasDerivWithinAt from the chain rule (HasDerivAt → HasDerivWithinAt).
  set adot := ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivAdot
    p (conjugatePicardIter p u₀ 0) with hadot_def
  have hderiv_global : ∀ s n,
      HasDerivAt
        (fun r => coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0) r n)
        (adot s n) s := by
    intro s n
    -- Inline the chain-rule → cosineCoeffs HasDerivAt step
    -- (reproduces coupledChemDivCoeff_hasDerivAt_of_chainRule from ChemDivAdot.lean)
    rcases hchain.exists_local_slab s with ⟨δ, hδ, hf_cont, hdiff, hcont_deriv⟩
    simpa only [coupledChemDivSourceCoeffs, hadot_def,
      ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivAdot] using
      ShenWork.IntervalMildPicardRegularity.cosineCoeffs_hasDerivAt_of_smooth_param
        (f := coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0))
        (f' := ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivTimeDerivativeLift
          p (conjugatePicardIter p u₀ 0))
        (τ := s) (δ := δ) (n := n) hδ hf_cont hdiff hcont_deriv
  have hderiv : ∀ s ∈ Icc c T, ∀ n,
      HasDerivWithinAt
        (fun r => coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0) r n)
        (adot s n) (Icc c T) s := by
    intro s _ n
    exact (hderiv_global s n).hasDerivWithinAt
  -- Step 4: ContinuousOn of adot from joint continuity.
  have hadotcont : ∀ n, ContinuousOn (fun s => adot s n) (Icc c T) := by
    intro n
    open ShenWork.IntervalDomainPositiveWindowK1OnEndpoint in
    open ShenWork.IntervalCoupledRegularityBootstrap in
    have key :=
      cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
        (f := coupledChemDivTimeDerivativeLift
          p (conjugatePicardIter p u₀ 0))
        (c := c) (T := T) n hjointcont
    open ShenWork.IntervalCoupledRegularityBootstrap in
    simpa only [hadot_def, coupledChemDivAdot] using key
  -- Step 5: Uniform bound on |adot s n| ≤ Mdot for all n.
  -- GENUINE RESIDUAL: a uniform-in-n bound on the time-derivative coefficients.
  -- Per-mode smoothness gives per-n bounds on [c,T] but NOT a uniform constant.
  -- The uniform bound needs the time-derivative field to have a summable
  -- cosine-coefficient envelope (the EWA-T-3 time-chain brick).
  have hMdot : ∃ (Mdot : ℝ), ∀ s ∈ Icc c T, ∀ n, |adot s n| ≤ Mdot := by
    sorry
    -- For the heat semigroup at level 0, the time derivative field
    -- coupledChemDivTimeDerivativeLift is smooth on [c,T]×[0,1] (c > 0).
    -- Its cosine coefficients decay like 1/k² (quadratic, from the H²
    -- regularity of the time derivative field), giving summability and hence
    -- a uniform bound.  But this requires H² of ∂ₜ(chemDiv source), which
    -- in turn requires ∂ₜ∂²ₓ(chemDiv source) — two more spatial derivatives
    -- plus one time derivative of the chemDiv functional.
  obtain ⟨Mdot, hMdot⟩ := hMdot
  exact ⟨adot, Mdot, hderiv, hadotcont, hMdot⟩

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
    Level0ChemDivSourceData p u₀ c T :=
  -- Wire envelope data from level0_chemDiv_envelope_summable
  let envData := level0_chemDiv_envelope_summable p hc hcT hu₀_cont hu₀_bound hpos hub
  let env := envData.choose
  let henv := envData.choose_spec
  -- Wire time-derivative data from level0_chemDiv_timeDerivData
  let tdData := level0_chemDiv_timeDerivData p hc hcT hu₀_cont hu₀_bound hpos hub
  let adot := tdData.choose
  let tdRest := tdData.choose_spec
  let Mdot := tdRest.choose
  let htd := tdRest.choose_spec
  {
    envelope := env
    henv_summable := henv.1
    henv_bound := henv.2
    adot := adot
    hderiv := htd.1
    hadotcont := htd.2.1
    derivBound := Mdot
    hderivBound := htd.2.2
  }

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
