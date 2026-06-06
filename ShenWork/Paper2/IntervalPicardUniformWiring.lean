/-
  ShenWork/Paper2/IntervalPicardUniformWiring.lean

  Phase-0 wiring — discharging the field hypotheses of `UniformWiring`
  (ShenWork/Paper2/IntervalPicardIterateUniform.lean, M-final) from satisfiable
  inputs, bridging the landed atoms (M1 restart identity, M2-uniform C² bound,
  the homogeneous spectral bound, the M-gate-3 power-law weight, and the kernel
  G1 atoms) to the per-level facts the carrier needs.

  ## What this module discharges (honest-partial, header-justified boundaries)

  The three `UniformWiring` field hypotheses are `hG2base`, `hG2step`, `hG1all`,
  each quantified over `∀ x : ℝ` on a `deriv`/`deriv∘deriv` of the *zero-extended*
  lift `intervalDomainLift (picardIter …)`.  The cosine-series atoms (the spectral
  identity and `iterate_abs_deriv2_le`) only describe the slice on the unit
  interval, and a `deriv` transports across an `EqOn` agreement only on an OPEN
  set (`Filter.EventuallyEq.deriv_eq`).  Hence the `∀ x : ℝ` field splits into:

    * **interior** `x ∈ Ioo 0 1` — derivatives agree with the cosine series
      (open-set `EventuallyEq`), and the series bound applies.  PROVED here.
    * **exterior** `x ∉ Icc 0 1` — the lift is locally `0` (the complement of the
      closed `Icc` is open), so `deriv (deriv lift) x = 0 ≤ profile`.  PROVED here
      (`lift_deriv2_eq_zero_of_not_mem`).
    * **two endpoints** `x ∈ {0,1}` — the zero-extension makes the lift jump at
      the boundary, so the SECOND derivative there is a genuine one-sided object
      NOT controlled by the (interior) series bound.  This is the single honest
      residual; it is carried as a NAMED, satisfiable two-point hypothesis
      (`hEnd0`/`hEnd1`) on each of the two G2 discharges.

  Accordingly:

    * `hG2base` — DISCHARGED on interior ∪ exterior; full `∀ x` produced from the
      two-point endpoint hypothesis.  The interior bound is GENUINELY PROVED:
      `picardIter p u₀ 0 t` is the homogeneous heat value, its lift equals the
      damped cosine series on `Icc` (spectral identity
      `intervalFullSemigroupOperator_eq_cosineHeatValue_Icc` +
      `heatValue_eq_cosineSeries`), whose `∂ₓ²` is bounded by `2M·eigExpWeight t`
      (`cosineSeries_abs_deriv2_le_eig_tsum` + `homogeneous_eigenvalue_tsum_le`),
      and the GATE absorbs it into `A₂/t²` (`g2_step_closes`, via antitonicity
      `eigExpWeight t ≤ eigExpWeight (t/2)`).
    * `hG2step` — DISCHARGED on interior ∪ exterior; full `∀ x` produced from the
      two-point endpoint hypothesis.  The interior bound is the M2-uniform
      `iterate_abs_deriv2_le` (UNCONDITIONAL on the restart series) bridged to the
      lift by M1's `picardIterateRestart_cosineIdentity`.
    * `hG1all` — DISCHARGED from the per-level kernel atom prerequisites (the
      χ₀ = 0 derivative-split identity + the two atoms' honest integrability
      inputs), via M-final's own `g1_kernel_bound`.  These prerequisites are the
      honest regularity inputs of T1/Atom D (their docstrings flag them as such),
      carried here as named satisfiable hypotheses.

  The corollary `uniformWiring_of_inputs` assembles a `UniformWiring` from the
  three discharges' inputs (hence `picardIterateUniformData_all`), making explicit
  exactly which residual inputs remain (the endpoint two-point facts and the
  per-level kernel atom prerequisites).

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardIterateUniform
import ShenWork.PDE.IntervalFullKernelSpectralClean

open MeasureTheory Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalHomogeneousQuantBound (eigExpWeight homogeneous_eigenvalue_tsum_le)
open ShenWork.IntervalPicardIterateTimeC1 (duhamelGainConst duhamelGainConst_nonneg
  eigExpWeight_antitone)
open ShenWork.IntervalPicardIterateSourceC1 (iterateSourceEnvelopeConst)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalFullKernelSpectralClean (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc)
open ShenWork.IntervalPicardIterateRestart (heatValue_eq_cosineSeries)
open ShenWork.IntervalPicardIterateC2Bound (cosineSeries_abs_deriv2_le_eig_tsum
  iterate_abs_deriv2_le restartIterateCoeff hom_eig_summable)
open ShenWork.IntervalPicardIterateUniform (CL G1profile G2profile Benv homWeightBound
  GateCondition g2_step_closes g1_kernel_bound UniformWiring PicardIterateUniformData
  picardIterateUniformData_all)

noncomputable section

namespace ShenWork.IntervalPicardUniformWiring

/-! ## §0 — Geometry of the zero-extended lift: exterior and endpoint helpers. -/

/-- The complement of `Icc 0 1` is open and the lift vanishes there, so the lift
is `EventuallyEq 0` near any exterior point.  Consequently both its first and
second derivatives vanish at such a point. -/
theorem lift_deriv2_eq_zero_of_not_mem
    (f : intervalDomainPoint → ℝ) {x : ℝ} (hx : x ∉ Set.Icc (0 : ℝ) 1) :
    deriv (deriv (intervalDomainLift f)) x = 0 := by
  -- the lift agrees with the constant `0` on the open complement of `Icc 0 1`.
  have hopen : IsOpen (Set.Icc (0 : ℝ) 1)ᶜ := isOpen_compl_iff.2 isClosed_Icc
  have hmem : (Set.Icc (0 : ℝ) 1)ᶜ ∈ nhds x := hopen.mem_nhds hx
  -- lift =ᶠ 0 near x ⇒ deriv lift =ᶠ deriv 0 = 0 near x ⇒ deriv (deriv lift) x = 0.
  have hEq0 : intervalDomainLift f =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hmem] with z hz
    have hzn : z ∉ Set.Icc (0 : ℝ) 1 := hz
    simp [intervalDomainLift, hzn]
  -- first derivative is eventually 0 near x.
  have hderiv_eq : deriv (intervalDomainLift f) =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hmem] with z hz
    have hzmem : (Set.Icc (0 : ℝ) 1)ᶜ ∈ nhds z := hopen.mem_nhds hz
    have hEqz : intervalDomainLift f =ᶠ[nhds z] (fun _ => (0 : ℝ)) := by
      filter_upwards [hzmem] with w hw
      have hwn : w ∉ Set.Icc (0 : ℝ) 1 := hw
      simp [intervalDomainLift, hwn]
    rw [hEqz.deriv_eq]; simp
  rw [hderiv_eq.deriv_eq]; simp

/-- **Interior G2 transport.**  If the lift agrees, on the open interior
`Ioo 0 1`, with a function `g` whose second derivative is bounded by `B` at `x`,
then `|deriv (deriv lift) x| ≤ B` for `x ∈ Ioo 0 1`.  (Both `deriv`s transport via
`Filter.EventuallyEq.deriv_eq` on the open set.) -/
theorem lift_deriv2_abs_le_of_eqOn_Ioo
    {f : intervalDomainPoint → ℝ} {g : ℝ → ℝ}
    (hEq : Set.EqOn (intervalDomainLift f) g (Set.Ioo (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) {B : ℝ}
    (hg : |deriv (deriv g) x| ≤ B) :
    |deriv (deriv (intervalDomainLift f)) x| ≤ B := by
  -- agreement on the open `Ioo 0 1` ⇒ `EventuallyEq` at every interior point ⇒
  -- the first derivatives agree on a neighbourhood ⇒ second derivatives agree.
  have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhds x := isOpen_Ioo.mem_nhds hx
  have hEqf : intervalDomainLift f =ᶠ[nhds x] g :=
    Filter.eventuallyEq_of_mem hmem hEq
  have hd1 : deriv (intervalDomainLift f) =ᶠ[nhds x] deriv g := by
    -- agreement is local around every point of the open `Ioo`, so first derivs agree there.
    filter_upwards [hmem] with z hz
    have hmemz : Set.Ioo (0 : ℝ) 1 ∈ nhds z := isOpen_Ioo.mem_nhds hz
    exact (Filter.eventuallyEq_of_mem hmemz hEq).deriv_eq
  rw [hd1.deriv_eq]
  exact hg

/-! ## §1 — `hG2base` discharge.

`picardIter p u₀ 0 t` is the homogeneous heat value `S(t)(lift u₀)`.  On `Ioo 0 1`
its lift equals the damped cosine series, whose `∂ₓ²` is `≤ 2M·eigExpWeight t`,
which the GATE absorbs into `A₂/t²`.  Carried endpoint facts: the two-point
second-derivative bound at `x ∈ {0,1}`. -/

/-- **G2 base — interior bound.**  For `x ∈ Ioo 0 1` and `0 < t`, with `0 ≤ M`,
`Continuous (lift u₀)`, and `|cosineCoeffs(lift u₀) k| ≤ 2M`, the second spatial
derivative of `lift(picardIter p u₀ 0 t)` at `x` is bounded by `2M·eigExpWeight t`. -/
theorem hG2base_interior_bound
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {t M : ℝ}
    (ht : 0 < t) (hu₀_cont : Continuous (intervalDomainLift u₀))
    (hcoeff : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ 2 * M)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    |deriv (deriv (intervalDomainLift (picardIter p u₀ 0 t))) x|
      ≤ 2 * M * eigExpWeight t := by
  -- the damped-coefficient `b`-sequence of the cosine series.
  set b : ℕ → ℝ := fun k =>
    Real.exp (-t * unitIntervalCosineEigenvalue k) * cosineCoeffs (intervalDomainLift u₀) k
    with hb_def
  have hsum : Summable (fun k => unitIntervalCosineEigenvalue k * |b k|) :=
    hom_eig_summable ht hcoeff
  -- on `Ioo 0 1`, the lift equals the damped cosine series.
  have hEq : Set.EqOn (intervalDomainLift (picardIter p u₀ 0 t))
      (fun z => ∑' k, b k * cosineMode k z) (Set.Ioo (0 : ℝ) 1) := by
    intro z hz
    have hzIcc : z ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hz
    -- lift value on Icc is the propagator value (picardIter 0 def).
    have hval : intervalDomainLift (picardIter p u₀ 0 t) z
        = intervalFullSemigroupOperator t (intervalDomainLift u₀) z := by
      simp only [intervalDomainLift, dif_pos hzIcc, picardIter]
    rw [hval, intervalFullSemigroupOperator_eq_cosineHeatValue_Icc ht hu₀_cont hcoeff hzIcc,
      heatValue_eq_cosineSeries]
  -- the series' second derivative bound by the λ-weighted ℓ¹ sum ≤ 2M·eigExpWeight t.
  have hser : |deriv (deriv (fun z => ∑' k, b k * cosineMode k z)) x|
      ≤ 2 * M * eigExpWeight t :=
    (cosineSeries_abs_deriv2_le_eig_tsum hsum x).trans
      (homogeneous_eigenvalue_tsum_le (M := 2 * M) ht hcoeff)
  exact lift_deriv2_abs_le_of_eqOn_Ioo hEq hx hser

/-- **G2 base — interior ∪ exterior absorbed into `A₂/t²`.**  Combines the
interior homogeneous bound with `eigExpWeight t ≤ eigExpWeight (t/2)` (antitone)
and `g2_step_closes` (the GATE) to land `≤ G2profile A₂ t` at every NON-endpoint
`x` (`x ∈ Ioo 0 1 ∪ (Icc 0 1)ᶜ`). -/
theorem hG2base_offEndpoints
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {M A₂ T t : ℝ}
    (hMnn : 0 ≤ M) (hgate : GateCondition p M A₂ T)
    (ht : 0 < t) (htT : t ≤ T)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    (hcoeff : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ 2 * M)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1 ∨ x ∉ Set.Icc (0 : ℝ) 1) :
    |deriv (deriv (intervalDomainLift (picardIter p u₀ 0 t))) x| ≤ G2profile A₂ t := by
  rcases hx with hxIoo | hxExt
  · -- interior: homogeneous bound, antitone, then the gate via g2_step_closes.
    have hint := hG2base_interior_bound p u₀ ht hu₀_cont hcoeff hxIoo
    have hτ : 0 < t / 2 := by positivity
    have hanti : eigExpWeight t ≤ eigExpWeight (t / 2) :=
      eigExpWeight_antitone hτ (by linarith)
    -- |val| ≤ 2M·eigExpWeight t ≤ 2M·eigExpWeight (t/2) ≤ (2M)·E₂(t/2) + Cgain·(…)·Benv.
    have hBenv_nn : 0 ≤ Benv p M A₂ t := by
      unfold Benv iterateSourceEnvelopeConst
      refine le_trans ?_ (le_max_right _ _)
      have hpow : 0 ≤ M ^ p.α := Real.rpow_nonneg hMnn _
      have : 0 ≤ p.a + p.b * M ^ p.α := by
        have := mul_nonneg p.hb hpow; have := p.ha; linarith
      exact mul_nonneg hMnn this
    have hgain_nn : 0 ≤ duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t :=
      mul_nonneg (mul_nonneg duhamelGainConst_nonneg (Real.rpow_nonneg hτ.le _)) hBenv_nn
    have hval : |deriv (deriv (intervalDomainLift (picardIter p u₀ 0 t))) x|
        ≤ (2 * M) * eigExpWeight (t / 2)
          + duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t := by
      have h2Mnn : 0 ≤ 2 * M := by linarith
      calc |deriv (deriv (intervalDomainLift (picardIter p u₀ 0 t))) x|
          ≤ 2 * M * eigExpWeight t := hint
        _ ≤ 2 * M * eigExpWeight (t / 2) := by
            exact mul_le_mul_of_nonneg_left hanti h2Mnn
        _ ≤ (2 * M) * eigExpWeight (t / 2)
              + duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t := by linarith
    exact g2_step_closes hMnn ht htT (le_refl (2 * M)) hgate hval
  · -- exterior: second derivative is 0, and G2profile ≥ 0.
    rw [lift_deriv2_eq_zero_of_not_mem _ hxExt, abs_zero]
    have hA₂nn : 0 ≤ A₂ := by
      -- A₂ ≥ 0 from the gate at t (LHS ≥ 0): homWeightBound + nonneg ≤ A₂/t².
      have hτ : 0 < t / 2 := by positivity
      have hgt := hgate t ht htT
      have hhom_nn : 0 ≤ homWeightBound M t := by
        unfold homWeightBound
        have h1 : 0 ≤ 4 / (Real.exp 1 * Real.pi ^ 2) := by positivity
        have h2 : (0:ℝ) < (t / 2) ^ 2 := by positivity
        have h2Mnn : 0 ≤ 2 * M := by linarith
        exact mul_nonneg h2Mnn (div_nonneg h1 h2.le)
      have hBenv_nn : 0 ≤ Benv p M A₂ t := by
        unfold Benv iterateSourceEnvelopeConst
        refine le_trans ?_ (le_max_right _ _)
        have hpow : 0 ≤ M ^ p.α := Real.rpow_nonneg hMnn _
        have : 0 ≤ p.a + p.b * M ^ p.α := by
          have := mul_nonneg p.hb hpow; have := p.ha; linarith
        exact mul_nonneg hMnn this
      have hgain_nn : 0 ≤ duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t :=
        mul_nonneg (mul_nonneg duhamelGainConst_nonneg (Real.rpow_nonneg hτ.le _)) hBenv_nn
      have hquot_nn : 0 ≤ A₂ / t ^ 2 := le_trans (by linarith) hgt
      have ht2 : (0:ℝ) < t ^ 2 := by positivity
      by_contra hneg
      rw [not_le] at hneg
      have : A₂ / t ^ 2 < 0 := div_neg_of_neg_of_pos hneg ht2
      linarith
    unfold G2profile
    positivity

/-- **`hG2base` discharge (full `∀ x`).**  The off-endpoint discharge plus the two
named, satisfiable endpoint facts `hEnd0`/`hEnd1` produce exactly the `hG2base`
field of `UniformWiring`.  The endpoint facts are the one-sided second-derivative
bounds at `x ∈ {0,1}` — the single honest residual of the zero-extension. -/
theorem hG2base_field
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {M A₂ T : ℝ}
    (hMnn : 0 ≤ M) (hgate : GateCondition p M A₂ T)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    (hcoeff : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ 2 * M)
    (hEnd0 : ∀ t, 0 < t → t ≤ T →
      |deriv (deriv (intervalDomainLift (picardIter p u₀ 0 t))) 0| ≤ G2profile A₂ t)
    (hEnd1 : ∀ t, 0 < t → t ≤ T →
      |deriv (deriv (intervalDomainLift (picardIter p u₀ 0 t))) 1| ≤ G2profile A₂ t) :
    ∀ t, 0 < t → t ≤ T → ∀ x : ℝ,
      |deriv (deriv (intervalDomainLift (picardIter p u₀ 0 t))) x| ≤ G2profile A₂ t := by
  intro t ht htT x
  by_cases hxIcc : x ∈ Set.Icc (0 : ℝ) 1
  · -- in `Icc`: interior or one of the two endpoints.
    rcases eq_or_lt_of_le hxIcc.1 with hx0 | hx0
    · subst hx0; exact hEnd0 t ht htT
    rcases eq_or_lt_of_le hxIcc.2 with hx1 | hx1
    · subst hx1; exact hEnd1 t ht htT
    · exact hG2base_offEndpoints p u₀ hMnn hgate ht htT hu₀_cont hcoeff (Or.inl ⟨hx0, hx1⟩)
  · exact hG2base_offEndpoints p u₀ hMnn hgate ht htT hu₀_cont hcoeff (Or.inr hxIcc)

/-! ## §2 — `hG2step` discharge.

For `n+1`, M1's `picardIterateRestart_cosineIdentity` identifies `lift(uₙ₊₁(t))`
with the restart cosine series `∑'ₖ restartIterateCoeff p u₀ n t k · cosineMode k x`
on `Icc 0 1`, and M2-uniform's `iterate_abs_deriv2_le` bounds that series'
`∂ₓ²` by `M₁·eigExpWeight(t/2) + Cgain·(t/2)^{1/4}·Benv(t)` (UNCONDITIONAL on the
series).  The interior transport gives the field budget; endpoints are carried. -/

/-- **G2 step — interior bound.**  For `x ∈ Ioo 0 1`, `0 < t`, `p.χ₀ = 0`, the
half-step coefficient bound `M₁`, the source `DuhamelSourceTimeC1` package, the
quadratic decay and the source continuity, the second spatial derivative of the
actual lift `lift(picardIter p u₀ (n+1) t)` is bounded by the M2-uniform budget
`M₁·eigExpWeight(t/2) + Cgain·(t/2)^{1/4}·Benv(t)`. -/
theorem hG2step_interior_bound
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    {t M A₂ M₁ : ℝ} (ht : 0 < t)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k))
    (hL_cont : ∀ s, 0 < s → s ≤ t →
      Continuous (logisticLifted p (picardIter p u₀ n s)))
    (hM₁ : ∀ k,
      |cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (t / 2))) k| ≤ M₁)
    (srcσ : DuhamelSourceTimeC1
      (fun σ k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k))
    (hdecay : ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k|
        ≤ 2 * Benv p M A₂ t / ((k : ℝ) * Real.pi) ^ 2)
    (hσcont : ∀ k, Continuous
      (fun σ => cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k))
    (hBenv : 0 ≤ Benv p M A₂ t)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    |deriv (deriv (intervalDomainLift (picardIter p u₀ (n + 1) t))) x|
      ≤ M₁ * eigExpWeight (t / 2)
        + duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t := by
  -- M1: lift(uₙ₊₁(t)) = restart series on Icc 0 1.
  have hM1 := ShenWork.IntervalPicardIterateRestart.picardIterateRestart_cosineIdentity
    p hχ0 u₀ n hu₀_cont hu₀_bound hsrc0 ht hL_cont
  -- restrict the EqOn to the open Ioo, and rewrite the series via restartIterateCoeff.
  have hEq : Set.EqOn (intervalDomainLift (picardIter p u₀ (n + 1) t))
      (fun z => ∑' k, restartIterateCoeff p u₀ n t k * cosineMode k z)
      (Set.Ioo (0 : ℝ) 1) := by
    intro z hz
    have hzIcc : z ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hz
    have := hM1 hzIcc
    simpa only [restartIterateCoeff] using this
  -- M2-uniform: the series' ∂ₓ² is bounded by the budget.
  have hser := iterate_abs_deriv2_le p u₀ n ht hBenv hM₁ srcσ hdecay hσcont x
  -- the M2 constant is `duhamelGainConst` (definitional equality).
  have hser' : |deriv (deriv (fun z => ∑' k, restartIterateCoeff p u₀ n t k * cosineMode k z)) x|
      ≤ M₁ * eigExpWeight (t / 2)
        + duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t := by
    have hc : duhamelGainConst
        = 2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) / Real.pi ^ ((3 : ℝ) / 2) := rfl
    rw [hc]; exact hser
  exact lift_deriv2_abs_le_of_eqOn_Ioo hEq hx hser'

/-- **`hG2step` discharge (interior + exterior, endpoint carried).**  For every
`n` and `t ∈ (0,T]`, produces the `∃ M₁ ≤ 2M ∧ …` budget shape required by the
`hG2step` field, at every `x : ℝ`, given the per-level M1/M2 inputs (half-step
bound `M₁ ≤ 2M`, source package, decay, continuity) and the two named endpoint
budget facts `hEnd0`/`hEnd1`. -/
theorem hG2step_field
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (u₀ : intervalDomainPoint → ℝ) {M A₂ T : ℝ}
    (hMnn : 0 ≤ M)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    -- per-level interior inputs.  The two `DuhamelSourceTimeC1` packages are
    -- `Type`-valued (carry data), so are passed as standalone hypotheses rather
    -- than bundled in a `∧`-chain; the half-step bound `M₁ n t ≤ 2M`, the source
    -- decay/continuity, and per-slice continuity are the remaining Prop inputs.
    (M₁ : ℕ → ℝ → ℝ)
    (hM₁le : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → M₁ n t ≤ 2 * M)
    (hsrc0 : ∀ (n : ℕ), DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k))
    (hL_cont : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
      ∀ s, 0 < s → s ≤ t → Continuous (logisticLifted p (picardIter p u₀ n s)))
    (hM₁ : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
      ∀ k, |cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (t / 2))) k| ≤ M₁ n t)
    (srcσ : ∀ (n : ℕ) (t : ℝ), DuhamelSourceTimeC1
      (fun σ k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k))
    (hdecay : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
      ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k →
        |cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k|
          ≤ 2 * Benv p M A₂ t / ((k : ℝ) * Real.pi) ^ 2)
    (hσcont : ∀ (n : ℕ) (t : ℝ), ∀ k, Continuous
      (fun σ => cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k))
    -- the two named endpoint budgets (the zero-extension residual):
    (hEnd0 : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∃ M₁' : ℝ, M₁' ≤ 2 * M ∧
      |deriv (deriv (intervalDomainLift (picardIter p u₀ (n + 1) t))) 0|
        ≤ M₁' * eigExpWeight (t / 2)
          + duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t)
    (hEnd1 : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∃ M₁' : ℝ, M₁' ≤ 2 * M ∧
      |deriv (deriv (intervalDomainLift (picardIter p u₀ (n + 1) t))) 1|
        ≤ M₁' * eigExpWeight (t / 2)
          + duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t) :
    ∀ n : ℕ, ∀ t, 0 < t → t ≤ T → ∀ x : ℝ,
      ∃ M₁' : ℝ, M₁' ≤ 2 * M ∧
        |deriv (deriv (intervalDomainLift (picardIter p u₀ (n + 1) t))) x|
          ≤ M₁' * eigExpWeight (t / 2)
            + duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t := by
  intro n t ht htT x
  -- `Benv` is monotone-free here: the field uses `Benv … t`; nonnegativity at `t`
  -- comes from the structural form of `iterateSourceEnvelopeConst` (max with a
  -- nonneg term), independent of `T`.
  have hBenv_t : 0 ≤ Benv p M A₂ t := by
    unfold Benv iterateSourceEnvelopeConst
    refine le_trans ?_ (le_max_right _ _)
    have hpow : 0 ≤ M ^ p.α := Real.rpow_nonneg hMnn _
    have : 0 ≤ p.a + p.b * M ^ p.α := by
      have := mul_nonneg p.hb hpow; have := p.ha; linarith
    exact mul_nonneg hMnn this
  by_cases hxIcc : x ∈ Set.Icc (0 : ℝ) 1
  · rcases eq_or_lt_of_le hxIcc.1 with hx0 | hx0
    · subst hx0; exact hEnd0 n t ht htT
    rcases eq_or_lt_of_le hxIcc.2 with hx1 | hx1
    · subst hx1; exact hEnd1 n t ht htT
    · -- interior
      refine ⟨M₁ n t, hM₁le n t ht htT, ?_⟩
      exact hG2step_interior_bound p hχ0 u₀ n ht hu₀_cont hu₀_bound (hsrc0 n)
        (hL_cont n t ht htT) (hM₁ n t ht htT) (srcσ n t) (hdecay n t ht htT)
        (hσcont n t) hBenv_t ⟨hx0, hx1⟩
  · -- exterior: second derivative is 0; any nonneg budget works (take M₁' = 0).
    refine ⟨0, by linarith, ?_⟩
    rw [lift_deriv2_eq_zero_of_not_mem _ hxIcc, abs_zero]
    have hgain_nn : 0 ≤ duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t := by
      have hτ : 0 < t / 2 := by positivity
      exact mul_nonneg (mul_nonneg duhamelGainConst_nonneg (Real.rpow_nonneg hτ.le _)) hBenv_t
    simpa using hgain_nn

/-! ## §3 — `hG1all` discharge.

M-final's `g1_kernel_bound` bounds `|∂ₓ(value)|` by `G1profile` once the spatial
derivative splits as `∂ₓS(t)(lift u₀) + ∫₀ᵗ ∂ₓS(t−s)Lₙ(s)`, with `|lift u₀| ≤ M`,
`sup|Lₙ| ≤ CL`, and the two atoms' honest integrability prerequisites.  We package
the per-level discharge from exactly those named inputs. -/

/-- **`hG1all` discharge.**  Given, for every level `n` and `t ∈ (0,T]`, the
χ₀ = 0 derivative-split identity for `deriv (lift(picardIter p u₀ n t))` together
with the named regularity prerequisites of the two kernel atoms (T1 measurability,
Atom D integrability), the datum bound `|lift u₀| ≤ M`, and the `n`-free logistic
ball bound `sup|Lₙ| ≤ CL p M`, the kernel G1-line holds at every `x : ℝ`. -/
theorem hG1all_field
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {M T : ℝ} (hMnn : 0 ≤ M)
    {u₀lift : ℝ → ℝ} (hf_meas : AEStronglyMeasurable u₀lift (intervalMeasure 1))
    (hu₀ : ∀ y, |u₀lift y| ≤ M)
    -- per-level kernel inputs: the source family `Lₙ`, its integrability and sup,
    -- the gradient-integrand interval-integrability, and the derivative-split:
    (Lfam : ℕ → ℝ → ℝ → ℝ)
    (hq_int : ∀ (n : ℕ), ∀ s, Integrable (Lfam n s) (intervalMeasure 1))
    (hL : ∀ (n : ℕ), ∀ s y, |Lfam n s y| ≤ CL p M)
    (hg_int : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : ℝ,
      IntervalIntegrable
        (fun s : ℝ => deriv
          (fun z : ℝ => intervalFullSemigroupOperator (t - s) (Lfam n s) z) x) volume 0 t)
    (hsplit : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : ℝ,
      deriv (intervalDomainLift (picardIter p u₀ n t)) x
        = deriv (fun z : ℝ => intervalFullSemigroupOperator t u₀lift z) x
          + ∫ s in (0:ℝ)..t, deriv
              (fun z : ℝ => intervalFullSemigroupOperator (t - s) (Lfam n s) z) x) :
    ∀ n : ℕ, ∀ t, 0 < t → t ≤ T → ∀ x : ℝ,
      |deriv (intervalDomainLift (picardIter p u₀ n t)) x| ≤ G1profile p M t := by
  intro n t ht htT x
  exact g1_kernel_bound p ht htT hMnn hf_meas hu₀ (hq_int n) (hL n) x (hg_int n t ht htT x)
    (hsplit n t ht htT x)

/-! ## §4 — Assembly: `UniformWiring` from the discharged inputs.

Combining the three field discharges produces a `UniformWiring`, and hence
`picardIterateUniformData_all`.  The remaining inputs are exactly the named
satisfiable residuals (endpoint two-point facts for G2, per-level kernel atom
prerequisites for G1) — collected here as the corollary's hypotheses. -/

/-- **`UniformWiring` from discharged inputs.**  Assembles the carrier's wiring
bundle from: the gate/datum data, the G1 kernel inputs (`hG1all_field`), the G2
base inputs (`hG2base_field`), and the G2 step inputs (`hG2step_field`).  The two
G2 discharges carry their named endpoint residuals; the G1 discharge carries the
per-level kernel-atom prerequisites. -/
theorem uniformWiring_of_inputs
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (u₀ : intervalDomainPoint → ℝ) {M A₂ T : ℝ}
    (hMnn : 0 ≤ M) (hT1 : T ≤ 1) (hgate : GateCondition p M A₂ T)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hcoeff : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ 2 * M)
    -- G1 kernel inputs:
    {u₀lift : ℝ → ℝ} (hf_meas : AEStronglyMeasurable u₀lift (intervalMeasure 1))
    (hu₀L : ∀ y, |u₀lift y| ≤ M)
    (Lfam : ℕ → ℝ → ℝ → ℝ)
    (hq_int : ∀ (n : ℕ), ∀ s, Integrable (Lfam n s) (intervalMeasure 1))
    (hL : ∀ (n : ℕ), ∀ s y, |Lfam n s y| ≤ CL p M)
    (hg_int : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : ℝ,
      IntervalIntegrable
        (fun s : ℝ => deriv
          (fun z : ℝ => intervalFullSemigroupOperator (t - s) (Lfam n s) z) x) volume 0 t)
    (hsplit : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : ℝ,
      deriv (intervalDomainLift (picardIter p u₀ n t)) x
        = deriv (fun z : ℝ => intervalFullSemigroupOperator t u₀lift z) x
          + ∫ s in (0:ℝ)..t, deriv
              (fun z : ℝ => intervalFullSemigroupOperator (t - s) (Lfam n s) z) x)
    -- G2 base endpoint residuals:
    (hBaseEnd0 : ∀ t, 0 < t → t ≤ T →
      |deriv (deriv (intervalDomainLift (picardIter p u₀ 0 t))) 0| ≤ G2profile A₂ t)
    (hBaseEnd1 : ∀ t, 0 < t → t ≤ T →
      |deriv (deriv (intervalDomainLift (picardIter p u₀ 0 t))) 1| ≤ G2profile A₂ t)
    -- G2 step per-level interior inputs (Type-valued `DuhamelSourceTimeC1`
    -- packages passed as functions) + endpoint residuals:
    (M₁ : ℕ → ℝ → ℝ)
    (hM₁le : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → M₁ n t ≤ 2 * M)
    (hsrc0 : ∀ (n : ℕ), DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k))
    (hL_cont : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
      ∀ s, 0 < s → s ≤ t → Continuous (logisticLifted p (picardIter p u₀ n s)))
    (hM₁ : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
      ∀ k, |cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (t / 2))) k| ≤ M₁ n t)
    (srcσ : ∀ (n : ℕ) (t : ℝ), DuhamelSourceTimeC1
      (fun σ k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k))
    (hdecay : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
      ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k →
        |cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k|
          ≤ 2 * Benv p M A₂ t / ((k : ℝ) * Real.pi) ^ 2)
    (hσcont : ∀ (n : ℕ) (t : ℝ), ∀ k, Continuous
      (fun σ => cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k))
    (hStepEnd0 : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∃ M₁' : ℝ, M₁' ≤ 2 * M ∧
      |deriv (deriv (intervalDomainLift (picardIter p u₀ (n + 1) t))) 0|
        ≤ M₁' * eigExpWeight (t / 2)
          + duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t)
    (hStepEnd1 : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∃ M₁' : ℝ, M₁' ≤ 2 * M ∧
      |deriv (deriv (intervalDomainLift (picardIter p u₀ (n + 1) t))) 1|
        ≤ M₁' * eigExpWeight (t / 2)
          + duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t) :
    UniformWiring p u₀ M A₂ T :=
  { hMnn := hMnn
    hT1 := hT1
    hgate := hgate
    hG1all := hG1all_field p u₀ hMnn hf_meas hu₀L Lfam hq_int hL hg_int hsplit
    hG2base := hG2base_field p u₀ hMnn hgate hu₀_cont hcoeff hBaseEnd0 hBaseEnd1
    hG2step := hG2step_field p hχ0 u₀ hMnn hu₀_cont hu₀_bound M₁ hM₁le hsrc0 hL_cont hM₁
      srcσ hdecay hσcont hStepEnd0 hStepEnd1 }

end ShenWork.IntervalPicardUniformWiring
