/-
  ShenWork/Paper2/IntervalPicardIterateSourceC1.lean

  Phase-0 / M3 — the iterate source **time-`C¹`** induction step (`χ₀ = 0`).

  Goal.  Discharge M1's hypothesis `H2` at the next level: produce the
  `DuhamelSourceTimeC1` structure for the logistic source coefficient family of
  the `n`-th Picard iterate slice,

      DuhamelSourceTimeC1
        (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)

  which is exactly the shape consumed by
  `ShenWork.IntervalPicardIterateRestart.picardIterateRestart_cosineIdentity` as
  its `hsrc0`.  No time window is needed: the `DuhamelSourceTimeC1` structure is
  a *global* object (its envelope/derivative bounds are keyed to `0 ≤ s`),
  matching M1's hypothesis verbatim, so M3 composes with M1 with no windowing.

  ## Strategy

  With `g σ := intervalDomainLift (picardIter p u₀ n σ)` the *profile* family,
  `logisticLifted p (picardIter p u₀ n σ)` agrees on `[0,1]` with
  `logisticSourceFun p.a p.b p.α (g σ)`
  (`logisticLifted_eq_logisticSourceFun_on_Icc`), so by `cosineCoeffs_congr_on_Icc`
  the two coefficient families are *literally equal* (`source_family_eq`).  We
  therefore build the structure for the `logisticSourceFun` family — the
  assembled `logisticSource_duhamelSourceTimeC1` does this from profile-level
  data — and transport along the equality.

  ## Explicit quantitative outputs

  * **Envelope.**  The decay constant `C := iterateSourceEnvelopeConst` is the
    explicit `max` of the `2·B_log` quadratic-decay numerator
    (`logisticSourceFun_cosineCoeff_quadratic_decay_explicit`) and the explicit
    zeroth-coefficient sup bound `M·(a + b·M^α)` (`logisticSourceFun_abs_le_of_bound`
    ⟶ `cosineCoeffs_zero_abs_le_of_bound`).  The resulting
    `DuhamelSourceTimeC1.envelope` is the ℓ¹ profile `k ↦ C` at `k = 0` and
    `k ↦ C/(kπ)²` for `k ≥ 1`, summable by the `p`-series.
  * **derivBound `= Mdot`.**  The uniform `ℓ∞` bound on the source-coefficient
    time-derivative `adot σ k = cosineCoeffs (∂_σ L(uₙ σ)) k`.  With the
    coefficient `L¹` bound `|cosineCoeffs g k| ≤ 2·sup_{[0,1]}|g|`
    (`cosineCoeffs_abs_le_of_continuous_bounded`), `Mdot = 2·sup|∂_σ L|`.

  ## Hypotheses (the M2-uniform / `K1`–`K2` outputs; each satisfiable)

  Spatial regularity of `g` (`K2`): `C²` slices `hC2`, positivity floor `hpos`
  (`g σ x > 0`; needed for the `rpow` chain rule), sup bound `hub` (`M`), gradient
  bound `hG1` (`G1`), Hessian bound `hG2` (`G2`), Neumann endpoints `hN0/hN1`.
  Structural constants `hα ha hb` (`1 ≤ α`, `0 ≤ a`, `0 ≤ b`, the `CM2Params`
  data).  Source-coefficient time-`C¹` data (`K1`'s `G4i`
  `restartCosineSeries_hasDerivAt_time` ⟶ chain-rule
  `logisticSourceFun_hasDerivAt_time` ⟶ time-Leibniz
  `cosineCoeffs_hasDerivAt_of_smooth_param` output): `adot`, `hderiv`,
  `hadotcont`, explicit uniform bound `Mdot`/`hMdot`.

  Satisfiability (non-vacuity).  For `n = 0` the iterate slice is the heat
  semigroup value of the `C²`/Neumann datum: `C^∞`, strictly positive when the
  datum is, with the stated spatial bounds, and time-`C¹` source coefficients by
  the same `G4i`/time-Leibniz chain (the semigroup IS a restart series with
  trivial source).  The whole hypothesis bundle is therefore simultaneously
  realised; for `n+1` the same follows from the spatial bootstrap
  (`picardIterateHasC2Slices`) and `restartDerivField_continuousOn_joint`.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalPicardIterateRestart
import ShenWork.PDE.IntervalLogisticSourceQuantBound

open MeasureTheory Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalMildPicardRegularity
  (logisticSourceFun logisticSource_duhamelSourceTimeC1
   logisticSourceFun_abs_le_of_bound logisticLifted_eq_logisticSourceFun_on_Icc
   cosineCoeffs_zero_abs_le_of_bound)
open ShenWork.IntervalLogisticSourceQuantBound
  (B_log B_log_nonneg logisticSourceFun_cosineCoeff_quadratic_decay_explicit)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)

noncomputable section

namespace ShenWork.IntervalPicardIterateSourceC1

/-! ## Step 0 — the two source families coincide. -/

/-- The coefficient family of the lifted logistic source equals the coefficient
family of the scalar logistic source applied to the lifted profile. -/
theorem source_family_eq
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ) :
    (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
      = fun s k => cosineCoeffs
          (logisticSourceFun p.a p.b p.α
            (intervalDomainLift (picardIter p u₀ n s))) k := by
  funext s k
  exact cosineCoeffs_congr_on_Icc
    (logisticLifted_eq_logisticSourceFun_on_Icc p (picardIter p u₀ n s)) k

/-! ## Step 1 — the explicit envelope constant. -/

/-- The explicit envelope constant: the larger of twice the logistic `W^{2,1}`
bound (`2·B_log`, the `k ≥ 1` quadratic-decay numerator) and the explicit
zeroth-coefficient sup bound `M·(a + b·M^α)`.  Both arguments are explicit in
the slice data `(M, G1, G2)`. -/
def iterateSourceEnvelopeConst (a b α M G1 G2 : ℝ) : ℝ :=
  max (2 * B_log a b α M G1 G2) (M * (a + b * M ^ α))

/-! ## Step 2 — main assembly. -/

/-- **M3 — iterate source time-`C¹` step.**

For `p : CM2Params` and a Picard iterate level `n`, the logistic-source
coefficient family of the iterate slice is `DuhamelSourceTimeC1`, with EXPLICIT
envelope keyed to `iterateSourceEnvelopeConst p.a p.b p.α M G1 G2` and EXPLICIT
`derivBound = Mdot`.

The conclusion is *literally* the `hsrc0` hypothesis of M1's
`picardIterateRestart_cosineIdentity`, so this discharges its `H2` at level `n`.

(`DuhamelSourceTimeC1` is data, so this is a `noncomputable def`, mirroring the
upstream `logisticSource_duhamelSourceTimeC1`.) -/
noncomputable def picardIterate_source_duhamelSourceTimeC1
    (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    -- structural constants
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    -- K2 spatial slice bounds (profile g σ = lift (picardIter p u₀ n σ))
    {M G1 G2 : ℝ}
    (hC2 : ∀ σ, ContDiff ℝ 2 (intervalDomainLift (picardIter p u₀ n σ)))
    (hpos : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ n σ) x)
    (hub : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (picardIter p u₀ n σ) x ≤ M)
    (hG1 : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (picardIter p u₀ n σ)) x| ≤ G1)
    (hG2 : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (picardIter p u₀ n σ))) x| ≤ G2)
    (hN0 : ∀ σ, deriv (intervalDomainLift (picardIter p u₀ n σ)) 0 = 0)
    (hN1 : ∀ σ, deriv (intervalDomainLift (picardIter p u₀ n σ)) 1 = 0)
    -- K1 source-coefficient time-C¹ data
    (adot : ℝ → ℕ → ℝ)
    (hderiv : ∀ σ k, HasDerivAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α
          (intervalDomainLift (picardIter p u₀ n r))) k) (adot σ k) σ)
    (hadotcont : ∀ k, Continuous (fun σ => adot σ k))
    {Mdot : ℝ}
    (hMdot : ∀ σ, 0 ≤ σ → ∀ k, |adot σ k| ≤ Mdot) :
    DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k) := by
  -- profile abbreviation
  set g : ℝ → ℝ → ℝ := fun σ => intervalDomainLift (picardIter p u₀ n σ) with hg
  -- explicit envelope constant and its nonnegativity
  set C : ℝ := iterateSourceEnvelopeConst p.a p.b p.α M G1 G2 with hCdef
  have hG1nn : 0 ≤ G1 :=
    le_trans (abs_nonneg _) (hG1 0 0 (by constructor <;> norm_num))
  have hG2nn : 0 ≤ G2 :=
    le_trans (abs_nonneg _) (hG2 0 0 (by constructor <;> norm_num))
  have hMnn : 0 ≤ M := by
    have h1 := hub 0 0 (by constructor <;> norm_num)
    have h2 := hpos 0 0 (by constructor <;> norm_num)
    linarith
  have hBnn : 0 ≤ B_log p.a p.b p.α M G1 G2 :=
    B_log_nonneg hα ha hb hMnn hG1nn hG2nn
  have hαpos : 0 < p.α := lt_of_lt_of_le one_pos hα
  have hMa_nn : 0 ≤ M * (p.a + p.b * M ^ p.α) := by positivity
  have hCnn : 0 ≤ C := by
    rw [hCdef, iterateSourceEnvelopeConst]
    exact le_trans (by linarith : (0:ℝ) ≤ 2 * B_log p.a p.b p.α M G1 G2)
      (le_max_left _ _)
  have h2B_le_C : 2 * B_log p.a p.b p.α M G1 G2 ≤ C := by
    rw [hCdef, iterateSourceEnvelopeConst]; exact le_max_left _ _
  have hMa_le_C : M * (p.a + p.b * M ^ p.α) ≤ C := by
    rw [hCdef, iterateSourceEnvelopeConst]; exact le_max_right _ _
  -- (hdecay) explicit 2·B_log/(kπ)² decay of the source coefficients, k ≥ 1
  have hdecay : ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (logisticSourceFun p.a p.b p.α (g σ)) k|
        ≤ C / ((k : ℝ) * Real.pi) ^ 2 := by
    intro σ _ k hk
    refine le_trans
      (logisticSourceFun_cosineCoeff_quadratic_decay_explicit
        (hC2 σ) hα ha hb (hpos σ) (hub σ) (hG1 σ) (hG2 σ) (hN0 σ) (hN1 σ) k hk)
      ?_
    have hden : 0 < ((k : ℝ) * Real.pi) ^ 2 := by
      have hkpos : (0:ℝ) < (k : ℝ) := by
        exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
      positivity
    gcongr
  -- (ha0) zeroth coefficient bound via the explicit source sup bound
  have ha0 : ∀ σ, 0 ≤ σ →
      |cosineCoeffs (logisticSourceFun p.a p.b p.α (g σ)) 0| ≤ C := by
    intro σ _
    have hsup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |logisticSourceFun p.a p.b p.α (g σ) x| ≤ M * (p.a + p.b * M ^ p.α) :=
      logisticSourceFun_abs_le_of_bound (B := M) hMnn hαpos ha hb
        (fun x hx => by rw [abs_of_pos (hpos σ x hx)]; exact hub σ x hx)
        (hpos σ)
    have hgc : Continuous (g σ) := (hC2 σ).continuous
    have hcont : ContinuousOn (logisticSourceFun p.a p.b p.α (g σ))
        (Set.Icc (0 : ℝ) 1) := by
      have hpos' : ∀ x, x ∈ Set.Icc (0:ℝ) 1 → g σ x ≠ 0 :=
        fun x hx => ne_of_gt (hpos σ x hx)
      unfold logisticSourceFun
      apply ContinuousOn.mul hgc.continuousOn
      apply ContinuousOn.sub continuousOn_const
      apply ContinuousOn.mul continuousOn_const
      exact ContinuousOn.rpow_const hgc.continuousOn
        (fun x hx => Or.inl (hpos' x hx))
    exact le_trans
      (cosineCoeffs_zero_abs_le_of_bound hMa_nn hcont hsup) hMa_le_C
  -- assemble the DuhamelSourceTimeC1 for the logisticSourceFun family
  have hsrc :
      DuhamelSourceTimeC1
        (fun σ k => cosineCoeffs (logisticSourceFun p.a p.b p.α (g σ)) k) :=
    logisticSource_duhamelSourceTimeC1 (p := p) (g := g)
      hC2 hpos hN0 hN1 hCnn hdecay ha0 hderiv hadotcont hMdot
  -- transport to the lifted-logistic source family (literally equal)
  have hfam : (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
      = fun σ k => cosineCoeffs (logisticSourceFun p.a p.b p.α (g σ)) k :=
    source_family_eq p u₀ n
  rw [hfam]
  exact hsrc

-- #print axioms picardIterate_source_duhamelSourceTimeC1

end ShenWork.IntervalPicardIterateSourceC1
