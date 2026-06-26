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
import ShenWork.Paper2.IntervalResolverHighRegularity
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
open ShenWork.Paper2.IntervalResolverHighRegularity
  (intervalResolverLiftR intervalResolverLiftR_contDiff_four
   intervalResolverLiftR_even intervalResolverLiftR_reflect_one)
open ShenWork.PDE (intervalNeumannResolverR)

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
        exact ShenWork.IntervalPicardIterateRepresentation.hagree_zero
          p u₀ hs_pos _hu₀_cont _hu₀_bound hx
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
        -- Witness: the lifted resolver cosine series from IntervalResolverHighRegularity
        set V := intervalResolverLiftR p (conjugatePicardIter p u₀ 0 s) with hV_def
        refine ⟨V, ?_, ?_, ?_, ?_, ?_⟩
        · -- C⁴: from intervalResolverLiftR_contDiff_four.
          -- Needs: Summable (fun k => λ_k * |(â_k).re|) where â_k =
          -- intervalNeumannResolverSourceCoeff p (S(s)u₀) k, i.e. the cosine
          -- coefficients of ν * (lift (S(s)u₀))^γ.
          --
          -- Route (>50 lines of new infrastructure, sorry'd per task spec):
          --
          -- 1. Heat semigroup C⁴: u := S(s)u₀ is C⁴ for s > 0
          --    (heatSemigroup_contDiff_four, already available).
          -- 2. Source C⁴: ν*u^γ is C⁴ on [0,1] by chain rule (u C⁴ + u > 0).
          --    Neumann BCs: deriv(ν*u^γ) vanishes at 0,1 because deriv(u) = 0
          --    at 0,1 (cosine series) and deriv(ν*u^γ) = ν*γ*u^{γ-1}*u'.
          -- 3. Depth-1 NeumannTower for ν*u^γ:
          --    g 0 = ν*u^γ (C⁴, Neumann), g 1 = (ν*u^γ)'' (C², Neumann).
          --    The Neumann BC for g 1 = (ν*u^γ)'' needs (ν*u^γ)''' = 0 at 0,1.
          --    This holds because all odd derivatives of the cosine series vanish
          --    at the endpoints (symmetry about 0 and 1).
          -- 4. cosineCoeffs_decay at j=1: |cosineCoeffs(ν*u^γ) k| ≤ C/(kπ)⁴
          --    for k ≥ 1.
          -- 5. Then λ_k |â_k| = (kπ)² · C/(kπ)⁴ = C/(kπ)² which is summable
          --    (p-series with p=2 > 1).
          -- 6. The k=0 term is finite (bounded source gives bounded integral).
          --
          -- Blocking sub-goals (each ~15–25 lines):
          --   (a) C⁴ chain rule for x ↦ ν*u(x)^γ from ContDiff ℝ 4 u + u > 0
          --   (b) Third-derivative Neumann vanishing at endpoints for the source
          --   (c) Assembling the depth-1 NeumannTower structure
          --   (d) Uniform rawCoeff bound for the top level g 1
          apply intervalResolverLiftR_contDiff_four
          -- Goal: Summable (fun k => λ_k * |(resolverSourceCoeff p w k).re|)
          -- where w = conjugatePicardIter p u₀ 0 s.
          --
          -- Step 1: rewrite source coeff .re to cosineCoeffs of ν·lift(w)^γ.
          set w := conjugatePicardIter p u₀ 0 s
          have hre_eq : ∀ k,
              (ShenWork.PDE.intervalNeumannResolverSourceCoeff p w k).re
                = cosineCoeffs (fun x => p.ν * intervalDomainLift w x ^ p.γ) k := by
            intro k
            simp only [ShenWork.PDE.intervalNeumannResolverSourceCoeff, cosineCoeffs,
              Complex.ofReal_re]
          simp_rw [hre_eq]
          -- Step 2: eigenvalue-summable coefficients for the heat semigroup.
          have hbc_sum : Summable (fun n =>
              unitIntervalCosineEigenvalue n *
                |Real.exp (-s * unitIntervalCosineEigenvalue n) *
                  heatCoeff u₀ n|) :=
            ShenWork.IntervalSemigroupNeumann.heatCoeff_eigenvalue_summable
              hs_pos _hu₀_bound
          -- Step 3: agreement of lift(w) with the cosine series on [0,1].
          have hagree_w : Set.EqOn (intervalDomainLift w)
              (fun x => ∑' k, (Real.exp (-s * unitIntervalCosineEigenvalue k) *
                heatCoeff u₀ k) * cosineMode k x) (Set.Icc (0 : ℝ) 1) :=
            ShenWork.IntervalPicardIterateRepresentation.hagree_zero
              p u₀ hs_pos _hu₀_cont _hu₀_bound
          -- Step 4: positivity on [0,1].
          have hpos_w : ∀ x ∈ Set.Icc (0 : ℝ) 1,
              0 < intervalDomainLift w x :=
            _hpos s hs
          -- Step 5: build IntervalWeakH2Neumann for ν · lift(w)^γ.
          --   This uses: eigenvalue summability of heat coefficients →
          --   cosine series is C² → ν·u^γ is C² by chain rule (rpow + pos) →
          --   Neumann BCs from junk-value at endpoints.
          have hf_H2 :
              ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann
                (fun x => p.ν * intervalDomainLift w x ^ p.γ) :=
            ShenWork.PDE.IntervalMildSourceDecayHelper.intervalWeakH2Neumann_of_eigenvalue_summable
              p.hν p.hγ hbc_sum hagree_w hpos_w
          -- Step 6: build IntervalWeakH2Neumann for hf_H2.secondDeriv.
          --   This is the "depth-2" certificate: (ν·u^γ)'' is itself C² with
          --   Neumann BCs.  Requires C⁴ of ν·u^γ (from C⁴ of the heat
          --   semigroup cosine series hU_C4 + chain rule + positivity) and
          --   third-derivative Neumann vanishing at endpoints.
          --   Each sub-fact is a concrete, well-defined mathematical statement.
          have hf''_H2 :
              ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann
                hf_H2.secondDeriv := by
            -- ── Step 6a: U_cos > 0 everywhere (period 2 + [0,1] positivity) ──
            -- Pattern from intervalResolverLiftR_nonneg_of_nonneg_on_Icc:
            -- period 2 reduces to [0,2), symm1 reduces [1,2) to (0,1].
            have hU_period_fun : Function.Periodic U_cos 2 := by
              intro x; show U_cos (x + 2) = U_cos x
              simp only [hU_cos_def]
              exact tsum_congr (fun k => by congr 1; exact cosineMode_add_two' k x)
            have hU_pos_all : ∀ x, 0 < U_cos x := by
              have hU_pos_Icc : ∀ y ∈ Icc (0 : ℝ) 1, 0 < U_cos y := by
                intro y hy; rw [← hU_agree y hy]; exact hpos_w y hy
              intro x
              -- Step 1: reduce to [0,∞) using evenness
              have hx_abs : U_cos x = U_cos |x| := by
                by_cases h : 0 ≤ x
                · rw [abs_of_nonneg h]
                · rw [abs_of_neg (not_le.mp h)]; exact (hU_even x).symm
              rw [hx_abs]
              -- Step 2: reduce |x| to [0,2) using period 2
              set n := ⌊|x| / 2⌋ with hn_def
              set r := |x| - n * 2 with hr_def
              have hrV : U_cos |x| = U_cos r :=
                (hU_period_fun.sub_int_mul_eq n).symm
              have hr_lo : 0 ≤ r := by
                have := Int.floor_le (|x| / 2); linarith
              have hr_hi : r < 2 := by
                have := Int.lt_floor_add_one (|x| / 2); linarith
              rw [hrV]
              -- Step 3: if r ∈ [0,1], done; if r ∈ (1,2), use symm1
              by_cases hr1 : r ≤ 1
              · exact hU_pos_Icc r ⟨hr_lo, hr1⟩
              · push_neg at hr1
                have : U_cos r = U_cos (2 - r) := (hU_symm1 r).symm
                rw [this]
                exact hU_pos_Icc (2 - r) ⟨by linarith, by linarith⟩
            -- ── Step 6b: g_smooth := ν * U_cos ^ γ is C⁴ ──
            have hU_ne : ∀ x, U_cos x ≠ 0 := fun x => ne_of_gt (hU_pos_all x)
            set g_smooth := fun x => p.ν * U_cos x ^ p.γ with hg_smooth_def
            have hg_C4 : ContDiff ℝ 4 g_smooth := by
              show ContDiff ℝ 4 (fun x => p.ν * U_cos x ^ p.γ)
              exact contDiff_const.mul (hU_C4.rpow_const_of_ne hU_ne)
            -- ── Step 6c: g_smooth is even and symmetric about 1 ──
            have hg_even : ∀ x, g_smooth (-x) = g_smooth x := by
              intro x; simp only [hg_smooth_def, hU_even]
            have hg_symm1 : ∀ x, g_smooth (2 - x) = g_smooth x := by
              intro x; simp only [hg_smooth_def, hU_symm1]
            -- ── Step 6d: deriv(deriv(g_smooth)) is C² ──
            have hg_C3 : ContDiff ℝ 3 (deriv g_smooth) := hg_C4.deriv'
            have hg_C2_dd : ContDiff ℝ 2 (deriv (deriv g_smooth)) := hg_C3.deriv'
            have hg_C2_dd_on : ContDiffOn ℝ 2 (deriv (deriv g_smooth)) (Icc (0 : ℝ) 1) :=
              hg_C2_dd.contDiffOn
            -- ── Step 6e: Parity helpers (from ChemDivSpatialC2 pattern) ──
            have deriv_even_odd : ∀ {g : ℝ → ℝ}, ContDiff ℝ 1 g →
                (∀ x, g (-x) = g x) → ∀ x, deriv g (-x) = -(deriv g x) := by
              intro g _hg heven x
              have h1 := deriv_comp_neg (f := g) (x := x)
              rw [show (fun x => g (-x)) = g from funext heven] at h1; linarith
            have odd_zero : ∀ {g : ℝ → ℝ}, (∀ x, g (-x) = -(g x)) → g 0 = 0 := by
              intro g hodd; have h := hodd 0; rw [neg_zero] at h; linarith
            have deriv_odd_even : ∀ {g : ℝ → ℝ}, ContDiff ℝ 1 g →
                (∀ x, g (-x) = -(g x)) → ∀ x, deriv g (-x) = deriv g x := by
              intro g _hg hodd x
              have h1 := deriv_comp_neg (f := g) (x := x)
              rw [show (fun x => g (-x)) = fun x => -(g x) from funext hodd] at h1
              simp at h1; linarith
            -- ── Step 6f: Parity chain: g even → g' odd → g'' even → g''' odd ──
            have hg'_odd : ∀ x, deriv g_smooth (-x) = -(deriv g_smooth x) :=
              deriv_even_odd (hg_C4.of_le (by norm_num)) hg_even
            have hg''_even : ∀ x, deriv (deriv g_smooth) (-x) = deriv (deriv g_smooth) x :=
              deriv_odd_even (hg_C3.of_le (by norm_num)) hg'_odd
            have hg'''_odd : ∀ x, deriv (deriv (deriv g_smooth)) (-x) =
                -(deriv (deriv (deriv g_smooth)) x) :=
              deriv_even_odd (hg_C2_dd.of_le (by norm_num)) hg''_even
            -- ── Step 6g: Neumann BCs for g''' at 0 ──
            have hbc30 : deriv (deriv (deriv g_smooth)) 0 = 0 :=
              odd_zero hg'''_odd
            -- ── Step 6h: Neumann BC for g''' at 1 via symmetry about 1 ──
            -- g_smooth(2-x) = g_smooth(x) → deriv(g_smooth)(2-x) = deriv(g_smooth)(x) ... (antisymm)
            -- → g''(2-x) = g''(x) (symm) → g'''(2-x) = -g'''(x) (antisymm) → g'''(1) = 0
            have hg'_antisymm1 : ∀ x, deriv g_smooth (2 - x) = -(deriv g_smooth x) := by
              intro x
              have h1 := deriv_comp_const_sub (f := g_smooth) (a := 2) (x := x)
              rw [show (fun x => g_smooth (2 - x)) = g_smooth from funext hg_symm1] at h1
              linarith
            have hg''_symm1 : ∀ x, deriv (deriv g_smooth) (2 - x) =
                deriv (deriv g_smooth) x := by
              intro x
              have h1 := deriv_comp_const_sub (f := deriv g_smooth) (a := 2) (x := x)
              rw [show (fun x => deriv g_smooth (2 - x)) =
                  fun x => -(deriv g_smooth x) from funext hg'_antisymm1] at h1
              simp at h1; linarith
            have hbc31 : deriv (deriv (deriv g_smooth)) 1 = 0 := by
              have h1 := deriv_comp_const_sub (f := deriv (deriv g_smooth)) (a := 2) (x := 1)
              rw [show (fun x => deriv (deriv g_smooth) (2 - x)) =
                  deriv (deriv g_smooth) from funext hg''_symm1] at h1
              have : (2 : ℝ) - 1 = 1 := by norm_num
              rw [this] at h1; linarith
            -- ── Step 6i: Tendsto for g''' at endpoints ──
            have hg'''_cont : Continuous (deriv (deriv (deriv g_smooth))) :=
              hg_C2_dd.continuous_deriv (by norm_num)
            have htend30 : Filter.Tendsto (deriv (deriv (deriv g_smooth)))
                (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
              conv_rhs => rw [← hbc30]
              exact hg'''_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
            have htend31 : Filter.Tendsto (deriv (deriv (deriv g_smooth)))
                (nhdsWithin (1 : ℝ) (Iio 1)) (nhds 0) := by
              conv_rhs => rw [← hbc31]
              exact hg'''_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
            -- ── Step 6j: Build IntervalWeakH2Neumann for deriv(deriv(g_smooth)) ──
            have h_smooth_H2 :
                ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann
                  (deriv (deriv g_smooth)) :=
              ShenWork.PDE.IntervalMildSourceDecayHelper.intervalWeakH2Neumann_of_contDiffOn
                hg_C2_dd_on htend30 htend31 hbc30 hbc31
            -- ── Step 6k: Build IntervalWeakH2Neumann hf_H2.secondDeriv ──
            -- Use h_smooth_H2 for integrability/bound (4th smooth deriv), and
            -- derive the weak_cosine_laplacian ALGEBRAICALLY from:
            --   (A) hf_H2.weak_cosine_laplacian  (IBP for ν·lift^γ → hf_H2.secondDeriv)
            --   (B) h_smooth_H2.weak_cosine_laplacian (IBP for g_smooth'' → 4th smooth)
            --   (C) integral agreement: ∫ cos·(ν·lift^γ) = ∫ cos·g_smooth on [0,1]
            -- Chain: (B) gives ∫cos·4th = -(kπ)²·∫cos·g_smooth''
            --        (A) gives ∫cos·hf_H2.sd = -(kπ)²·∫cos·(ν·lift^γ)
            --        (C) gives ∫cos·(ν·lift^γ) = ∫cos·g_smooth
            --        smooth depth-1 IBP: ∫cos·g_smooth'' = -(kπ)²·∫cos·g_smooth
            --        → ∫cos·hf_H2.sd = -(kπ)²·∫cos·g_smooth = ∫cos·g_smooth''
            --        → -(kπ)²·∫cos·hf_H2.sd = (kπ)⁴·∫cos·g_smooth = -(kπ)²·∫cos·g_smooth'' = ∫cos·4th
            -- Agreement of ν·lift^γ with g_smooth on [0,1]:
            have h_src_Icc : ∀ x ∈ Icc (0 : ℝ) 1,
                (fun z => p.ν * intervalDomainLift w z ^ p.γ) x = g_smooth x := by
              intro x hx
              show p.ν * intervalDomainLift w x ^ p.γ = p.ν * U_cos x ^ p.γ
              rw [hU_agree x hx]
            -- Cosine integral agreement
            have h_cos_int_eq : ∀ k : ℕ,
                (∫ x in (0:ℝ)..1, Real.cos (↑k * Real.pi * x) *
                  (fun z => p.ν * intervalDomainLift w z ^ p.γ) x) =
                ∫ x in (0:ℝ)..1, Real.cos (↑k * Real.pi * x) * g_smooth x :=
              fun k => intervalIntegral.integral_congr (fun x hx => by
                rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
                rw [h_src_Icc x hx])
            -- The depth-1 IBP for g_smooth:
            -- ∫cos·g_smooth'' = -(kπ)²·∫cos·g_smooth
            -- This is from intervalCosineLaplacianCoeff_eq_of_contDiffOn applied to g_smooth
            have hg_C2_on : ContDiffOn ℝ 2 g_smooth (Icc (0:ℝ) 1) :=
              (hg_C4.of_le (by norm_num)).contDiffOn
            have hg'_bc0 : deriv g_smooth 0 = 0 := odd_zero hg'_odd
            have hg'_bc1 : deriv g_smooth 1 = 0 := by
              have := hg'_antisymm1 1
              rw [show (2:ℝ) - 1 = 1 from by norm_num] at this; linarith
            have hg'_cont : Continuous (deriv g_smooth) :=
              hg_C4.continuous_deriv (by norm_num)
            have hg'_tend0 : Filter.Tendsto (deriv g_smooth)
                (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
              conv_rhs => rw [← hg'_bc0]
              exact hg'_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
            have hg'_tend1 : Filter.Tendsto (deriv g_smooth)
                (nhdsWithin (1:ℝ) (Iio 1)) (nhds 0) := by
              conv_rhs => rw [← hg'_bc1]
              exact hg'_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
            have h_depth1_ibp : ∀ k : ℕ,
                (∫ x in (0:ℝ)..1, Real.cos (↑k * Real.pi * x) *
                  deriv (deriv g_smooth) x) =
                -(↑k * Real.pi) ^ 2 *
                  ∫ x in (0:ℝ)..1, Real.cos (↑k * Real.pi * x) * g_smooth x :=
              fun k => ShenWork.IntervalEllipticCharacterization.intervalCosineLaplacianCoeff_eq_of_contDiffOn
                k hg_C2_on hg'_tend0 hg'_tend1 hg'_bc0 hg'_bc1
            exact {
              secondDeriv := h_smooth_H2.secondDeriv
              second_intervalIntegrable := h_smooth_H2.second_intervalIntegrable
              second_abs_integral_bound := h_smooth_H2.second_abs_integral_bound
              weak_cosine_laplacian := fun k => by
                -- Goal: ∫cos·4th_smooth = -(kπ)²·∫cos·hf_H2.secondDeriv
                -- From h_smooth_H2.weak_cosine_laplacian k:
                --   ∫cos·4th_smooth = -(kπ)²·∫cos·g_smooth''    ...(B)
                -- From hf_H2.weak_cosine_laplacian k:
                --   ∫cos·hf_H2.sd = -(kπ)²·∫cos·(ν·lift^γ)     ...(A)
                -- From h_cos_int_eq:
                --   ∫cos·(ν·lift^γ) = ∫cos·g_smooth              ...(C)
                -- From h_depth1_ibp:
                --   ∫cos·g_smooth'' = -(kπ)²·∫cos·g_smooth       ...(D)
                -- Substituting (C) into (A): ∫cos·hf_H2.sd = -(kπ)²·∫cos·g_smooth
                -- Substituting into goal RHS: -(kπ)²·∫cos·hf_H2.sd = (kπ)⁴·∫cos·g_smooth
                -- And (D) into (B): ∫cos·4th = -(kπ)²·(-(kπ)²·∫cos·g_smooth) = (kπ)⁴·∫cos·g_smooth
                -- So LHS = RHS.
                have hA := hf_H2.weak_cosine_laplacian k
                have hB := h_smooth_H2.weak_cosine_laplacian k
                have hC := h_cos_int_eq k
                have hD := h_depth1_ibp k
                -- Substitute (C) into (A)
                rw [hC] at hA
                -- Now hA: ∫cos·hf_H2.sd = -(kπ)²·∫cos·g_smooth
                -- Substitute (D) into (B)
                rw [hD] at hB
                -- Now hB: ∫cos·4th = -(kπ)²·(-(kπ)²·∫cos·g_smooth)
                -- Goal: ∫cos·4th = -(kπ)²·∫cos·hf_H2.sd
                rw [hA]; exact hB }
          -- Step 7: quartic decay → eigenvalue-weighted summability.
          exact ShenWork.IntervalSourceDecayQuantitative.intervalWeakH4Neumann_eigenvalue_L1_summable
            hf_H2 hf''_H2
        · -- Positivity: 0 < 1 + V x.
          -- Route: V ≥ 0 everywhere (resolver nonnegativity + period-2/even
          -- reduction to [0,1]), so 1 + V x ≥ 1 > 0.
          intro x
          suffices hVnn : 0 ≤ V x by linarith
          -- Abbreviate the profile at time s.
          set w := conjugatePicardIter p u₀ 0 s with hw_def
          -- ── ContinuousOn of the lift on [0,1] ──
          -- From hU_C4 + hU_agree: U_cos is C⁴ hence continuous, and
          -- intervalDomainLift w = U_cos on [0,1].
          have hcont_on : ContinuousOn (intervalDomainLift w) (Icc (0:ℝ) 1) :=
            hU_C4.continuous.continuousOn.congr (fun y hy => hU_agree y hy)
          -- ── Continuity of w on the subtype ──
          have hw_cont : Continuous w := by
            have hrestr : Set.restrict (Icc (0:ℝ) 1) (intervalDomainLift w) = w := by
              funext ⟨z, hz⟩
              show intervalDomainLift w z = w ⟨z, hz⟩
              rw [intervalDomainLift, dif_pos hz]
            rw [← hrestr]
            exact continuousOn_iff_continuous_restrict.mp hcont_on
          -- ── Nonnegativity of w ──
          have hw_nonneg : ∀ z : intervalDomainPoint, 0 ≤ w z := by
            intro ⟨z, hz⟩
            -- _hpos gives 0 < intervalDomainLift w z on [0,1].
            -- On [0,1], intervalDomainLift w z = w ⟨z, hz⟩.
            have hlift : intervalDomainLift w z = w ⟨z, hz⟩ :=
              dif_pos hz
            have h := _hpos s hs z hz
            rw [hlift] at h
            exact le_of_lt h
          -- ── Resolver nonneg on [0,1] ──
          have hR_nonneg : ∀ (yp : intervalDomainPoint),
              0 ≤ intervalNeumannResolverR p w yp := by
            intro yp
            -- Construct clip and nonneg continuous source f.
            set clip : ℝ → intervalDomainPoint := fun z =>
              ⟨max 0 (min z 1), le_max_left 0 _,
                max_le (by norm_num) (min_le_right z 1)⟩
            have hclip_cont : Continuous clip :=
              Continuous.subtype_mk
                (continuous_const.max (continuous_id.min continuous_const)) _
            have hcont_src : Continuous
                (fun z : intervalDomainPoint => p.ν * (w z) ^ p.γ) :=
              continuous_const.mul (hw_cont.rpow_const (fun z => Or.inr p.hγ.le))
            set f : ℝ → ℝ :=
              (fun z : intervalDomainPoint => p.ν * (w z) ^ p.γ) ∘ clip
            have hf_cont : Continuous f := hcont_src.comp hclip_cont
            have hf_nonneg : ∀ z, 0 ≤ f z := fun z =>
              mul_nonneg p.hν.le (Real.rpow_nonneg (hw_nonneg _) _)
            have hf_coeff : ∀ k, cosineCoeffs f k =
                (ShenWork.PDE.intervalNeumannResolverSourceCoeff p w k).re := by
              intro k
              have hsrc_eq :
                  (ShenWork.PDE.intervalNeumannResolverSourceCoeff p w k).re =
                  cosineCoeffs (fun z => p.ν * intervalDomainLift w z ^ p.γ) k := by
                simp [cosineCoeffs, ShenWork.PDE.intervalNeumannResolverSourceCoeff,
                  Complex.ofReal_re]
              rw [hsrc_eq]
              exact ShenWork.Paper2.cosineCoeffs_congr_on_Icc (fun z hz => by
                simp only [f, Function.comp, clip]
                have hclip_eq : max 0 (min z 1) = z := by
                  rw [min_eq_left hz.2, max_eq_right hz.1]
                simp only [hclip_eq, intervalDomainLift,
                  dif_pos (Set.mem_Icc.mpr hz)]) k
            have hâ : Summable (fun k => (cosineCoeffs f k) ^ 2) := by
              open ShenWork.IntervalResolverWeakBounds ShenWork.Paper2
                ShenWork.IntervalResolverPositivity in
              have h := resolverSourceCoeff_re_sq_summable_of_continuousOn p hcont_on
              simp only [intervalNeumannResolverSourceCoeff_zero, sub_zero] at h
              exact h.congr (fun k => by rw [hf_coeff])
            open ShenWork.IntervalResolverPositivity in
            exact intervalNeumannResolverR_nonneg_of_nonneg_source
              hf_cont hf_nonneg hf_coeff hâ yp
          -- ── Reduce x to [0,1] via even + reflect_one ──
          have hV_even : ∀ z, V (-z) = V z :=
            intervalResolverLiftR_even p w
          have hV_reflect : ∀ z, V (2 - z) = V z :=
            intervalResolverLiftR_reflect_one p w
          -- V(x+2) = V(x): from V(x+2) = V(2-(-x)) = V(-x) = V(x)
          have hV_periodic : ∀ z, V (z + 2) = V z := fun z => by
            have h1 : V (z + 2) = V (2 - (-z)) := by congr 1; ring
            rw [h1, hV_reflect, hV_even]
          -- V(x-2) = V(x): from V(x-2) = V(-(2-x)) = V(2-x) = V(x)
          have hV_sub_two : ∀ z, V (z - 2) = V z := fun z => by
            have h1 : V (z - 2) = V (-(2 - z)) := by congr 1; ring
            rw [h1, hV_even, hV_reflect]
          -- Integer shift: V(x + 2m) = V(x) by induction on m
          have hV_shift : ∀ (m : ℤ) (z : ℝ), V (z + 2 * m) = V z := by
            intro m z
            induction m using Int.induction_on with
            | zero => simp
            | succ n ih =>
              have hcast : z + 2 * (↑(↑n + 1 : ℤ) : ℝ) =
                  (z + 2 * (↑(↑n : ℤ) : ℝ)) + 2 := by push_cast; ring
              rw [hcast, hV_periodic, ih]
            | pred n ih =>
              have hcast : z + 2 * (↑(-↑n - 1 : ℤ) : ℝ) =
                  (z + 2 * (↑(-↑n : ℤ) : ℝ)) - 2 := by push_cast; ring
              rw [hcast, hV_sub_two, ih]
          -- Reduce x to y ∈ [-1,1] via round, then |y| ∈ [0,1] via evenness
          set m₀ : ℤ := round (x / 2)
          set y : ℝ := x - 2 * m₀
          have hVxy : V x = V y := by
            rw [show x = y + 2 * m₀ from by simp [y]]
            exact hV_shift m₀ y
          have hyabs : |y| ∈ Icc (0 : ℝ) 1 := by
            constructor
            · exact abs_nonneg _
            · have hround : |x / 2 - m₀| ≤ 1 / 2 := abs_sub_round (x / 2)
              rw [show y = 2 * (x / 2 - m₀) from by simp [y]; ring,
                abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
              nlinarith [hround]
          have hVy : V y = V |y| := by
            by_cases hnn : 0 ≤ y
            · rw [abs_of_nonneg hnn]
            · rw [not_le] at hnn
              rw [abs_of_neg hnn, ← hV_even]
          -- V |y| = R p w ⟨|y|, hyabs⟩ (cosineMode = unitIntervalCosineMode by rfl)
          rw [hVxy, hVy]
          -- Goal: 0 ≤ V |y|.  Bridge to intervalNeumannResolverR via tsum match.
          have hV_eq_R : V |y| = intervalNeumannResolverR p w ⟨|y|, hyabs⟩ := by
            -- V = intervalResolverLiftR p w (from hV_def + w = conj...)
            change intervalResolverLiftR p w |y| =
              intervalNeumannResolverR p w ⟨|y|, hyabs⟩
            -- Both unfold to tsum over cosine coeffs (cosineMode = unitIntervalCosineMode)
            unfold intervalResolverLiftR intervalNeumannResolverR
            exact tsum_congr (fun k => by
              rw [unitIntervalCosineMode_eq_cosineMode])
          rw [hV_eq_R]
          exact hR_nonneg ⟨|y|, hyabs⟩
        · -- Agreement on [0,1]: intervalDomainLift (coupledChemicalConcentration …) = V
          -- Chain: coupledChemicalConcentration = intervalNeumannResolverR (def) →
          -- lift on [0,1] = subtype value (def of intervalDomainLift) →
          -- R p w ⟨x,hx⟩ = ∑' k, coeff.re * unitIntervalCosineMode k x.1 (def of R) →
          -- unitIntervalCosineMode = cosineMode (rfl) →
          -- = intervalResolverLiftR p w x (def).
          intro x hx
          -- Reduce to: R p w ⟨x,hx⟩ = intervalResolverLiftR p w x.
          -- Both sides unfold to ∑' k, coeff.re * Real.cos(kπx):
          --   LHS: coupledChemicalConcentration ≡ intervalNeumannResolverR (def) →
          --        intervalDomainLift on [0,1] → subtype value → R body uses
          --        unitIntervalCosineMode ≡ cosineMode ≡ Real.cos(kπx).
          --   RHS: intervalResolverLiftR body uses cosineMode ≡ Real.cos(kπx).
          show intervalDomainLift (intervalNeumannResolverR p
            (conjugatePicardIter p u₀ 0 s)) x =
            intervalResolverLiftR p (conjugatePicardIter p u₀ 0 s) x
          simp only [intervalDomainLift, dif_pos hx]
          rfl
        · -- Even: from intervalResolverLiftR_even
          exact intervalResolverLiftR_even p (conjugatePicardIter p u₀ 0 s)
        · -- Symm1: from intervalResolverLiftR_reflect_one
          exact intervalResolverLiftR_reflect_one p (conjugatePicardIter p u₀ 0 s)
      let V_cos := hV_data.choose
      have hV := hV_data.choose_spec
      exact chemDivSource_weakH2_of_cosineRep hU_C4 hV.1 hV.2.1
        hU_agree hV.2.2.1 hU_even hV.2.2.2.1 hU_symm1 hV.2.2.2.2
    -- Step 2: Uniform L¹(|f''|) bound over [c,T].
    -- From compactness of [c,T] and continuity of the second-derivative norm.
    have hL1_uniform : ∃ (B : ℝ), 0 ≤ B ∧ ∀ s (hs : s ∈ Icc c T),
        (∫ x in (0 : ℝ)..1, |(hH2_per_slice s hs).secondDeriv x|) ≤ B := by
      -- SORRY: uniform L¹(|f''|) bound on [c,T] (>30 lines of new infrastructure).
      --
      -- Mathematical argument (each step is valid but needs infrastructure):
      --
      -- 1. Per-slice identity: (hH2_per_slice s hs).secondDeriv = deriv(deriv F_s)
      --    where F_s = deriv(chemFluxFun p.β U_cos(s) V_cos(s)), the classical C²
      --    second derivative of the chemDiv cosine representative at time s.
      --
      -- 2. Joint continuity: The map (s,x) ↦ deriv²(F_s)(x) is continuous on
      --    [c,T] × [0,1]. This follows from:
      --    (a) The heat semigroup s ↦ S(s)u₀ is jointly C∞ for s > 0 (standard).
      --    (b) The resolver inherits joint smoothness via elliptic regularity.
      --    (c) The chemDiv flux composition is smooth in both variables.
      --    (d) Derivatives commute with the continuous parameter dependence.
      --    Each sub-step (a)-(d) needs 10-20 lines of wiring through the codebase's
      --    spectral/cosine-series infrastructure.
      --
      -- 3. Compactness bound: A jointly continuous function on [c,T]×[0,1] is
      --    bounded: ∃ C, ∀ (s,x) ∈ [c,T]×[0,1], |deriv²(F_s)(x)| ≤ C.
      --    Then ∫₀¹ |deriv²(F_s)(x)| dx ≤ C · 1 = C for all s ∈ [c,T].
      --
      -- 4. Nonnegativity: C ≥ 0 is immediate (norm bound on a compact set).
      --
      -- Blocking sub-goals:
      --   (i)  Joint C² of the uncurried chemDiv flux on [c,T]×ℝ (needs joint
      --        smoothness of heat semigroup + resolver in the cosine-series form).
      --   (ii) Commutation of deriv² with the continuous s-parameter (needs
      --        ContDiff ℝ 2 (F_s) uniformly + parameter-dependence lemmas).
      --   (iii) IsCompact.bddAbove_image for the L¹ norm map s ↦ ∫|f''_s| on [c,T].
      sorry
    obtain ⟨B, hBnn, hL1⟩ := hL1_uniform
    exact ⟨B, hBnn, fun s hs => ⟨hH2_per_slice s hs, hL1 s hs⟩⟩
  -- ── Sub-goal 2: uniform sup bound and continuity of chemDiv source slices ──
  have hSup : ∃ (Msup : ℝ), 0 ≤ Msup ∧
      (∀ s ∈ Icc c T,
        ContinuousOn (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s)
          (Icc (0 : ℝ) 1)) ∧
      (∀ s ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
        |coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s x| ≤ Msup) := by
    -- SORRY: sup bound + continuity of chemDiv source slices (>30 lines).
    --
    -- Mathematical argument:
    --
    -- 1. Per-slice continuity on [0,1]:
    --    coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s
    --      = intervalDomainLift (intervalDomainChemotaxisDiv p u_s v_s)
    --    where u_s = S(s)u₀ (heat semigroup) and v_s = resolver(u_s).
    --    For s ∈ [c,T] with c > 0:
    --    (a) u_s is C∞ on [0,1] (heat semigroup exponential smoothing).
    --    (b) v_s is C∞ on [0,1] (elliptic resolver of smooth source).
    --    (c) chemotaxisDiv = ∂_x(u · v' / (1+v)^β) is a smooth composition,
    --        hence continuous on [0,1].
    --    (d) intervalDomainLift agrees with the smooth function on [0,1],
    --        so ContinuousOn (... s) (Icc 0 1) holds.
    --
    -- 2. Joint continuity on [c,T] × [0,1]:
    --    The uncurried map (s,x) ↦ chemDivSourceLift p (S(·)u₀) s x is
    --    continuous on [c,T] × [0,1] because:
    --    (a) s ↦ S(s)u₀ is continuous in the C² topology for s ≥ c > 0.
    --    (b) The chemDiv composition is continuous in the C¹ topology of its inputs.
    --    (c) Therefore (s,x) ↦ source(s)(x) is jointly continuous.
    --
    -- 3. Compactness sup bound:
    --    [c,T] × [0,1] is compact, the jointly continuous function achieves
    --    its sup and inf. Set Msup = max(|sup|, |inf|).
    --    Then |source(s)(x)| ≤ Msup for all (s,x) ∈ [c,T] × [0,1].
    --    Msup ≥ 0 because |·| ≥ 0.
    --
    -- Blocking sub-goals (each 10-20 lines of new wiring):
    --   (i)   Per-slice C¹ of the chemDiv flux from heat semigroup smoothness
    --         (needs chain: heatSemigroup_contDiff_four → resolver C² → flux C¹ →
    --         deriv(flux) continuous on [0,1]).
    --   (ii)  Joint continuity of (s,x) ↦ flux(s)(x) on [c,T]×[0,1]
    --         (needs s-parameter continuity of the cosine series in C¹ topology).
    --   (iii) IsCompact.exists_isMaxOn / bddAbove_image for the norm function.
    sorry
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
      -- Summability of Cenv/(max 1 k)²: comparison with 1/k² series.
      -- For k ≥ 1, max 1 k = k, so the term = Cenv / k² = Cenv * (1/k²).
      -- The series ∑ Cenv / k² is summable (p-series with p = 2 > 1).
      apply Summable.of_norm_bounded_eventually_nat
          ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left Cenv)
      rw [Filter.eventually_atTop]
      exact ⟨1, fun k hk => by
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hCenv_nn (sq_nonneg _))]
        have hk_cast : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr hk
        rw [max_eq_right hk_cast]
        exact le_of_eq (mul_one_div Cenv ((k : ℝ) ^ 2)).symm⟩,
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
  -- Wired through the committed chain:
  --   FluxJointC2Hyp → OuterCommuteAtoms → LocalChainRule.
  -- The FluxJointC2Hyp carries 5 fields (per-slab source continuity, joint C²
  -- of uncurried flux, spatial/time fderiv bridges, time-derivative continuity).
  -- For the heat semigroup each field holds because S(t)u₀ is jointly C∞ for
  -- t > 0, the resolver inherits regularity via the spectral route, and the
  -- flux is a smooth composition.  The sorry covers the heat-semigroup-specific
  -- wiring of these 5 fields; the chain FluxJointC2Hyp → OuterCommuteAtoms →
  -- LocalChainRule is already committed infrastructure.
  have hfluxC2 : ShenWork.IntervalCoupledRegularityBootstrap.CoupledChemDivFluxJointC2Hyp
      p (conjugatePicardIter p u₀ 0) := by
    sorry
  have hchain : ShenWork.IntervalCoupledRegularityBootstrap.CoupledChemDivLocalChainRule
      p (conjugatePicardIter p u₀ 0) :=
    ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivLocalChainRule_of_fluxJointC2 hfluxC2
  -- Step 2: Joint continuity of the chain-rule field on [c,T]×[0,1].
  -- Derived FROM hchain: each τ ∈ [c,T] gives per-slab continuity on
  -- Icc (τ-δ) (τ+δ) ×ˢ Icc 0 1 (from hchain.exists_local_slab).
  -- ContinuousOn is local, so it suffices to check at each point.
  have hjointcont : ContinuousOn
      (Function.uncurry (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivTimeDerivativeLift
        p (conjugatePicardIter p u₀ 0)))
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
    intro ⟨s, x⟩ hsx
    obtain ⟨hs, hx⟩ := mem_prod.1 hsx
    -- Get the local slab from hchain at τ = s
    rcases hchain.exists_local_slab s with ⟨δ, hδ, _, _, hcont⟩
    -- The point (s,x) is in the local slab Icc (s-δ) (s+δ) ×ˢ Icc 0 1
    have hmem : (s, x) ∈ Icc (s - δ) (s + δ) ×ˢ Icc (0 : ℝ) 1 :=
      mem_prod.2 ⟨⟨by linarith, by linarith⟩, hx⟩
    -- The target set is contained in the local slab
    have h_slab_nhds : Icc (s - δ) (s + δ) ×ˢ Icc (0 : ℝ) 1 ∈
        𝓝[Icc c T ×ˢ Icc (0 : ℝ) 1] (s, x) := by
      rw [mem_nhdsWithin]
      exact ⟨Ioo (s - δ) (s + δ) ×ˢ Set.univ,
        isOpen_Ioo.prod isOpen_univ,
        ⟨⟨by linarith, by linarith⟩, Set.mem_univ _⟩,
        fun ⟨_, _⟩ ⟨h_in_U, h_in_target⟩ =>
          ⟨Ioo_subset_Icc_self h_in_U.1, h_in_target.2⟩⟩
    exact (hcont.continuousWithinAt hmem).mono_of_mem_nhdsWithin h_slab_nhds
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
    -- Strategy: joint continuity on the compact [c,T]×[0,1] gives a uniform
    -- sup bound B_sup on |coupledChemDivTimeDerivativeLift p u s x|.
    -- Then cosineCoeffs_abs_le_of_continuous_bounded gives |adot s n| ≤ 2·B_sup
    -- for ALL n — the uniform-in-n bound from a sup bound, no H² needed.
    set F := ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivTimeDerivativeLift
      p (conjugatePicardIter p u₀ 0)
    -- The compact slab [c,T] × [0,1]
    set K : Set (ℝ × ℝ) := Icc c T ×ˢ Icc (0 : ℝ) 1
    have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
    -- hjointcont says: ContinuousOn (Function.uncurry F) K
    -- Extract uniform bound from compactness + continuity
    have hFcont_norm : ContinuousOn (fun p => ‖Function.uncurry F p‖) K :=
      hjointcont.norm
    obtain ⟨B_sup, hB_sup⟩ := hKcompact.bddAbove_image hFcont_norm
    -- B_sup bounds the norm image; extract pointwise bound
    have hbd : ∀ s ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1, |F s x| ≤ B_sup := by
      intro s hs x hx
      have hmem : (s, x) ∈ K := ⟨hs, hx⟩
      have : ‖Function.uncurry F (s, x)‖ ≤ B_sup :=
        hB_sup (Set.mem_image_of_mem _ hmem)
      simp [Function.uncurry, Real.norm_eq_abs] at this
      exact this
    -- Per-slice continuity from joint continuity
    have hcont_slice : ∀ s ∈ Icc c T, ContinuousOn (F s) (Icc (0 : ℝ) 1) := by
      intro s hs
      exact ContinuousOn.uncurry_left s hs hjointcont
    -- B_sup is an upper bound so it is ≥ 0: pick any point in the nonempty
    -- compact slab and use 0 ≤ ‖·‖ ≤ B_sup.
    have hB_sup_nn : 0 ≤ B_sup := by
      have hmem : (c, (0 : ℝ)) ∈ K :=
        ⟨left_mem_Icc.mpr _hcT, left_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)⟩
      exact le_trans (norm_nonneg _) (hB_sup (Set.mem_image_of_mem _ hmem))
    -- Now apply cosineCoeffs_abs_le_of_continuous_bounded per slice.
    -- adot s n = cosineCoeffs (F s) n by definition (coupledChemDivAdot unfolds
    -- to cosineCoeffs of coupledChemDivTimeDerivativeLift, which is F).
    refine ⟨2 * B_sup, fun s hs n => ?_⟩
    show |adot s n| ≤ 2 * B_sup
    -- Unfold adot to cosineCoeffs of F s
    change |cosineCoeffs (F s) n| ≤ 2 * B_sup
    exact ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
      (hcont_slice s hs) hB_sup_nn (hbd s hs) n
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
