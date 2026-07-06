/-
  ShenWork/Paper2/IntervalPicardLimitLogisticSource.lean

  Construct `GradientMildHalfStepLogisticSourceData` for the Picard limit.

  ## Strategy

  The `GradientMildHalfStepLogisticSourceData` structure requires a profile
  `profile t σ : ℝ → ℝ` that is **globally** `ContDiff ℝ 2`.  The natural
  candidate `intervalDomainLift (D.u (t/2 + σ))` is zero outside `[0,1]`
  and hence not globally C².  Instead, the profile must be a globally C²
  extension (e.g., the cosine series representation from the restart
  formula) that agrees with `intervalDomainLift (D.u (t/2+σ))` on `[0,1]`.

  The hypothesis structure `PicardLimitHasLogisticSourceRegularity` packages
  exactly such a globally C² profile, its positivity, Neumann BC, coefficient
  decay, time-derivative data, and spectral agreement.

  The main theorem `gradientMildHalfStepLogisticSourceData_of_limitRegularity`
  constructs the full `GradientMildHalfStepLogisticSourceData` by forwarding
  these fields.

  ## What is proved vs hypothesized

  **Proved here (0 sorry):**
  - The forwarding from `PicardLimitHasLogisticSourceRegularity` to
    `GradientMildHalfStepLogisticSourceData` is type-correct and complete.
  - `PicardLimitHasLogisticSourceRegularity` is constructed from iterate
    convergence data via G2.5 (`duhamelSourceTimeC1_of_uniform_limit`).
  - End-to-end: iterate convergence data yields
    `GradientMildHalfStepLogisticSourceData` and hence
    `HasRestartCosineRepresentations`.

  **Hypothesized (in `PicardIterateConvergenceData`):**
  - Globally C² profile for the limit
  - Iterate source coefficient sequences and their derivatives
  - Pointwise convergence of coefficients and uniform convergence of derivatives
  - Summable envelope and uniform derivative bound
  - Coefficient decay and spectral agreement

  These are the outputs of the Picard iterate induction chain:
  `picardIterateHasC2Slices_all` gives the C² profile, the iterate source
  coefficients come from the logistic composition, and the convergence is
  from the Picard fixed point theorem.

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.Paper2.IntervalMildPicardRegularity
import ShenWork.Paper2.IntervalMildPicardLimitRegularity

open MeasureTheory Filter Topology
open ShenWork.IntervalDomain
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildRegularityBootstrap
open ShenWork.IntervalMildPicardRegularity
open ShenWork.IntervalMildPicardLimitRegularity
open ShenWork.PDE.IntervalMildSourceDecayHelper

noncomputable section

namespace ShenWork.IntervalPicardLimitLogisticSource

/-! ## Hypothesis structure: logistic source regularity of the Picard limit

The structure packages exactly the data needed to fill each field of
`GradientMildHalfStepLogisticSourceData`.  The profile is abstract:
a globally C² function agreeing with the Picard limit on `[0,1]`.
In practice it comes from the restart cosine series.
-/

/-- If an abstract global profile agrees with the true lifted interval slice on
`[0,1]`, then its logistic-source cosine coefficients agree with the
`logisticLifted` coefficients of the interval slice.  This is the algebraic
bridge between a profile-based source package and the true restart identity. -/
theorem cosineCoeffs_logisticSourceFun_eq_logisticLifted_of_eqOn_Icc
    (p : CM2Params) {g : ℝ → ℝ} {w : intervalDomainPoint → ℝ}
    (hgw : Set.EqOn g (intervalDomainLift w) (Set.Icc (0 : ℝ) 1))
    (k : ℕ) :
    cosineCoeffs (logisticSourceFun p.a p.b p.α g) k =
      cosineCoeffs (ShenWork.IntervalGradientDuhamelMap.logisticLifted p w) k := by
  have hsource :
      Set.EqOn (logisticSourceFun p.a p.b p.α g)
        (logisticSourceFun p.a p.b p.α (intervalDomainLift w))
        (Set.Icc (0 : ℝ) 1) := by
    intro x hx
    rw [logisticSourceFun, logisticSourceFun, hgw hx]
  have hcoeff_profile :=
    ShenWork.Paper2.cosineCoeffs_congr_on_Icc hsource k
  have hcoeff_lift :=
    ShenWork.Paper2.cosineCoeffs_congr_on_Icc
      (logisticLifted_eq_logisticSourceFun_on_Icc p w) k
  exact hcoeff_profile.trans hcoeff_lift.symm

/-- All regularity data needed to fill `GradientMildHalfStepLogisticSourceData`
for the Picard limit.  Fields are 1-to-1 with the target structure.

The `profile t σ` is the globally C² spatial function at restart time
`t/2 + σ`, typically the restart cosine series for the Picard limit slice. -/
structure PicardLimitHasLogisticSourceRegularity
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) where
  profile : ℝ → ℝ → ℝ → ℝ
  C : ℝ → ℝ
  hC : ∀ t, 0 < t → t < D.T → 0 ≤ C t
  hC2 : ∀ t, 0 < t → t < D.T → ∀ σ, ContDiff ℝ 2 (profile t σ)
  hpos : ∀ t, 0 < t → t < D.T →
    ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < profile t σ x
  hN0 : ∀ t, 0 < t → t < D.T → ∀ σ, deriv (profile t σ) 0 = 0
  hN1 : ∀ t, 0 < t → t < D.T → ∀ σ, deriv (profile t σ) 1 = 0
  hdecay : ∀ t, 0 < t → t < D.T →
    ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (logisticSourceFun p.a p.b p.α (profile t σ)) k| ≤
        C t / ((k : ℝ) * Real.pi) ^ 2
  ha0_bound : ∀ t, 0 < t → t < D.T →
    ∀ σ, 0 ≤ σ →
      |cosineCoeffs (logisticSourceFun p.a p.b p.α (profile t σ)) 0| ≤ C t
  adot : ℝ → ℝ → ℕ → ℝ
  hderiv : ∀ t, 0 < t → t < D.T →
    ∀ σ n, HasDerivAt
      (fun r : ℝ =>
        cosineCoeffs (logisticSourceFun p.a p.b p.α (profile t r)) n)
      (adot t σ n) σ
  hadotcont : ∀ t, 0 < t → t < D.T →
    ∀ n, Continuous (fun σ : ℝ => adot t σ n)
  Mdot : ℝ → ℝ
  hMdot : ∀ t, 0 < t → t < D.T →
    ∀ σ, 0 ≤ σ → ∀ n, |adot t σ n| ≤ Mdot t
  hSpectralAgree : ∀ t, 0 < t → t < D.T →
    Set.EqOn (intervalDomainLift (D.u t))
      (fun x => ∑' n,
        restartDuhamelCoeff
          (gradientMildHalfStepInitialCoeff D t)
          (fun σ n => cosineCoeffs (logisticSourceFun p.a p.b p.α
            (profile t σ)) n)
          (t / 2) n * cosineMode n x)
      (Set.Icc 0 1)

/-! ## Main construction: forwarding to GradientMildHalfStepLogisticSourceData -/

/-- Construct `GradientMildHalfStepLogisticSourceData` from the limit's
logistic source regularity certificate.  This is a direct forwarding
of identically-typed fields. -/
def gradientMildHalfStepLogisticSourceData_of_limitRegularity
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (H : PicardLimitHasLogisticSourceRegularity D) :
    GradientMildHalfStepLogisticSourceData D where
  profile := H.profile
  C := H.C
  hC := H.hC
  hC2 := H.hC2
  hpos := H.hpos
  hN0 := H.hN0
  hN1 := H.hN1
  hdecay := H.hdecay
  ha0_bound := H.ha0_bound
  adot := H.adot
  hderiv := H.hderiv
  hadotcont := H.hadotcont
  Mdot := H.Mdot
  hMdot := H.hMdot
  hagree := H.hSpectralAgree

/-! ## G2.5 bridge: iterate convergence → limit regularity

The data from Picard iterate convergence, including:
- A globally C² profile for the limit
- Iterate source coefficient sequences converging pointwise
- Iterate derivative sequences converging uniformly
- Summable envelope and uniform derivative bound

is combined with `duhamelSourceTimeC1_of_uniform_limit` (G2.5) to
produce `PicardLimitHasLogisticSourceRegularity`. -/

/-- Iterate convergence data at a single restart time, capturing the
inputs to `duhamelSourceTimeC1_of_uniform_limit` for one value of `t`. -/
structure SingleRestartConvergenceData
    {p : CM2Params}
    (profile_t : ℝ → ℝ → ℝ) where
  /-- Iterate source coefficient sequences. The first ℕ is the iterate index,
  the ℝ is the restart time offset σ, the second ℕ is the cosine mode. -/
  aSeq : ℕ → ℝ → ℕ → ℝ
  /-- Pointwise convergence of iterate coefficients to the limit's. -/
  hconv : ∀ s k, Tendsto (fun n => aSeq n s k) atTop
    (nhds (cosineCoeffs (logisticSourceFun p.a p.b p.α (profile_t s)) k))
  /-- Iterate derivative sequences. -/
  adotSeq : ℕ → ℝ → ℕ → ℝ
  /-- Each iterate has HasDerivAt. -/
  hderiv_each : ∀ n s k, HasDerivAt (fun r => aSeq n r k) (adotSeq n s k) s
  /-- Limit time derivative. -/
  adot : ℝ → ℕ → ℝ
  /-- Uniform convergence of derivative sequences. -/
  hadot_unif : ∀ k,
    TendstoUniformly (fun n s => adotSeq n s k) (fun s => adot s k) atTop
  /-- Continuity of the limit derivative. -/
  hadot_cont : ∀ k, Continuous (fun s => adot s k)
  /-- Summable envelope for iterate coefficients. -/
  envelope : ℕ → ℝ
  henv_summable : Summable envelope
  henv_bound : ∀ n s, 0 ≤ s → ∀ k, |aSeq n s k| ≤ envelope k
  /-- Uniform derivative bound. -/
  derivBound : ℝ
  hderiv_bound : ∀ n s, 0 ≤ s → ∀ k, |adotSeq n s k| ≤ derivBound

/-- Apply G2.5 to single-restart convergence data, producing
`DuhamelSourceTimeC1` for the limit's logistic source coefficients. -/
def duhamelSourceTimeC1_of_singleRestartConvergence
    {p : CM2Params} {profile_t : ℝ → ℝ → ℝ}
    (S : SingleRestartConvergenceData (p := p) profile_t) :
    DuhamelSourceTimeC1
      (fun σ n => cosineCoeffs (logisticSourceFun p.a p.b p.α
        (profile_t σ)) n) :=
  duhamelSourceTimeC1_of_uniform_limit
    S.hconv S.hderiv_each S.hadot_unif S.hadot_cont
    S.henv_summable S.henv_bound S.hderiv_bound

/-- The full iterate convergence data, parameterized over restart times.

This packages, for each restart time `t ∈ (0, D.T)`:
- The globally C² profile
- The single-restart convergence data (iterate coefficients → limit)
- Coefficient decay and spectral agreement for the limit -/
structure PicardIterateConvergenceData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) where
  /-- Globally C² profile for the Picard limit. -/
  profile : ℝ → ℝ → ℝ → ℝ
  hC2 : ∀ t, 0 < t → t < D.T → ∀ σ, ContDiff ℝ 2 (profile t σ)
  hpos : ∀ t, 0 < t → t < D.T →
    ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < profile t σ x
  hN0 : ∀ t, 0 < t → t < D.T → ∀ σ, deriv (profile t σ) 0 = 0
  hN1 : ∀ t, 0 < t → t < D.T → ∀ σ, deriv (profile t σ) 1 = 0
  /-- Single-restart convergence data at each restart time. -/
  restartData : ∀ t, 0 < t → t < D.T →
    SingleRestartConvergenceData (p := p) (profile t)
  /-- Uniform coefficient decay constant. -/
  decayConst : ℝ → ℝ
  hdecayConst_nonneg : ∀ t, 0 < t → t < D.T → 0 ≤ decayConst t
  hdecay : ∀ t, 0 < t → t < D.T →
    ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (logisticSourceFun p.a p.b p.α (profile t σ)) k| ≤
        decayConst t / ((k : ℝ) * Real.pi) ^ 2
  ha0_bound : ∀ t, 0 < t → t < D.T →
    ∀ σ, 0 ≤ σ →
      |cosineCoeffs (logisticSourceFun p.a p.b p.α (profile t σ)) 0| ≤
        decayConst t
  /-- Uniform bound on the limit derivative (from I.restartData). -/
  derivBound : ℝ → ℝ
  hMdot : ∀ (t : ℝ) (ht : 0 < t) (htT : t < D.T),
    ∀ σ, 0 ≤ σ → ∀ n,
      |(restartData t ht htT).adot σ n| ≤ derivBound t
  /-- Spectral agreement. -/
  hSpectralAgree : ∀ t, 0 < t → t < D.T →
    Set.EqOn (intervalDomainLift (D.u t))
      (fun x => ∑' n,
        restartDuhamelCoeff
          (gradientMildHalfStepInitialCoeff D t)
          (fun σ n => cosineCoeffs (logisticSourceFun p.a p.b p.α
            (profile t σ)) n)
          (t / 2) n * cosineMode n x)
      (Set.Icc 0 1)

/-- Construct `PicardLimitHasLogisticSourceRegularity` from iterate
convergence data via G2.5.

At each restart time, `duhamelSourceTimeC1_of_uniform_limit` is applied
to the single-restart convergence data to obtain `DuhamelSourceTimeC1`,
from which the time-derivative fields are extracted. -/
def picardLimitHasLogisticSourceRegularity_of_iterateConvergence
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (I : PicardIterateConvergenceData D) :
    PicardLimitHasLogisticSourceRegularity D where
  profile := I.profile
  C := I.decayConst
  hC := I.hdecayConst_nonneg
  hC2 := I.hC2
  hpos := I.hpos
  hN0 := I.hN0
  hN1 := I.hN1
  hdecay := I.hdecay
  ha0_bound := I.ha0_bound
  adot := fun t σ n =>
    if h : 0 < t ∧ t < D.T then
      (I.restartData t h.1 h.2).adot σ n
    else 0
  hderiv := by
    intro t ht htT σ n
    have hcond : 0 < t ∧ t < D.T := ⟨ht, htT⟩
    simp only [dif_pos hcond]
    exact (duhamelSourceTimeC1_of_singleRestartConvergence
      (I.restartData t ht htT)).hderiv σ n
  hadotcont := by
    intro t ht htT n
    have hcond : 0 < t ∧ t < D.T := ⟨ht, htT⟩
    simp only [dif_pos hcond]
    exact (duhamelSourceTimeC1_of_singleRestartConvergence
      (I.restartData t ht htT)).hadotcont n
  Mdot := I.derivBound
  hMdot := by
    intro t ht htT σ hσ n
    have hcond : 0 < t ∧ t < D.T := ⟨ht, htT⟩
    simp only [dif_pos hcond]
    exact I.hMdot t ht htT σ hσ n
  hSpectralAgree := I.hSpectralAgree

/-! ## End-to-end assembly -/

/-- One-shot: iterate convergence data yields
`GradientMildHalfStepLogisticSourceData` for the Picard limit. -/
def gradientMildHalfStepLogisticSourceData_of_iterateConvergence
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (I : PicardIterateConvergenceData D) :
    GradientMildHalfStepLogisticSourceData D :=
  gradientMildHalfStepLogisticSourceData_of_limitRegularity D
    (picardLimitHasLogisticSourceRegularity_of_iterateConvergence D I)

/-- Iterate convergence data produces the older
`GradientMildHalfStepRestartData` package. -/
def gradientMildHalfStepRestartData_of_iterateConvergence
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (I : PicardIterateConvergenceData D) :
    GradientMildHalfStepRestartData D :=
  gradientMildHalfStepRestartData_of_logisticSourceData D
    (gradientMildHalfStepLogisticSourceData_of_iterateConvergence D I)

/-- Iterate convergence data yields `HasRestartCosineRepresentations`. -/
theorem hasRestartCosineRepresentations_of_iterateConvergence
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (I : PicardIterateConvergenceData D) :
    HasRestartCosineRepresentations D.T D.u :=
  hasRestartCosineRepresentations_of_gradientMildHalfStepLogisticSourceData D
    (gradientMildHalfStepLogisticSourceData_of_iterateConvergence D I)

end ShenWork.IntervalPicardLimitLogisticSource
