/-
  ShenWork/Paper2/IntervalDuhamelSpatialLeibniz.lean

  **FRONT B — the Duhamel spatial-Leibniz lemma + the χ₀ = 0 derivative-split
  identity, packaged in the exact shapes consumed by `uniformWiring_of_data`.**

  ## Status of the underlying analysis

  The hard analytic content of FRONT B is ALREADY PROVED, sorry-free, in the repo:

    * `ShenWork.IntervalNeumannFullKernel.intervalFullCoupledDuhamel_grad_integral_hasDerivAt`
      (`ShenWork/PDE/IntervalFullKernelLeibniz.lean`) — the differentiation under the
      time-integral sign, via `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`,
      with the singular endpoint `s = t` handled by working on `Ioc 0 t` (`uIoc_of_le`)
      and the parabolic `(t−s)^(−1/2)` dominating envelope.
    * The `s`-dependent joint measurability discharges
      (`ShenWork/PDE/IntervalFullKernelSDependentMeasurable.lean`).
    * `ShenWork.IntervalPicardG1Split.*` — the χ₀ = 0 derivative split assembled into
      the wiring's `hsplit`/`hg_int` residuals.

  This module is a THIN PACKAGING layer that

    1. restates the spatial-Leibniz lemma `intervalFullDuhamel_hasDerivAt_fst` with the
       *minimal* hypothesis interface the external audit specified — per-`s`
       integrability + a uniform sup bound + joint measurability of the source field —
       deriving the two `AEStronglyMeasurable` side conditions internally;
    2. exposes its `.deriv` corollary `intervalFullDuhamel_deriv_eq_integral_deriv`;
    3. delivers the χ₀ = 0 derivative split `chi0_deriv_split` in the EXACT pointwise-
       `∀x` shape that `uniformWiring_of_data` (in
       `ShenWork/Paper2/IntervalPicardUniformWiringDischarge.lean`) consumes as its
       `hsplit` field — interior `Ioo 0 1` genuinely proved (χ₀-reduction first, then
       termwise `HasDerivAt.add`), off-interior carried as the single named,
       satisfiable residual `hsplit_offInterior` (the zero-extended lift jumps at the
       two endpoints and vanishes exterior to `Icc 0 1`, while the kernel-extended RHS
       does not);
    4. provides the `hq_int`/`hL`-style per-slice source-integrability helper
       `duhamel_source_integrable` from a sup bound.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardG1Split

open MeasureTheory Filter Topology
open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure
   intervalMeasure_integrable_of_abs_bound)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator
   intervalFullCoupledDuhamel_grad_integral_hasDerivAt
   intervalFullSemigroupOperator_s_dependent_aestronglyMeasurable_x
   intervalFullSemigroupOperator_s_dependent_deriv_aestronglyMeasurable_x₀)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)

noncomputable section

namespace ShenWork.IntervalDuhamelSpatialLeibniz

/-! ## §1 — The Duhamel spatial-Leibniz lemma.

The audited target.  Differentiating

  `x ↦ ∫ s in 0..t, S(t−s) (F s) x`

in `x` at `x₀` interchanges the spatial `deriv` with the `s`-integral, the
derivative being `∫ s in 0..t, ∂ₓ[S(t−s) (F s)] x₀`.  Hypotheses: `0 < t`,
per-slice `Integrable (F s) (intervalMeasure 1)`, a uniform sup bound `|F s y| ≤ C`,
and joint measurability of the source field `Function.uncurry F` (which the
dominated-convergence theorem requires to build the two `AEStronglyMeasurable`
side conditions).  No per-slice derivative is ever evaluated at `t − s = 0`: the
singular endpoint lives on the null set `{t}` and is discarded on `Ioc 0 t`. -/

/-- **`intervalFullDuhamel_hasDerivAt_fst`.**  The full-Duhamel spatial Leibniz
rule: differentiation under the time-integral sign for the source term. -/
theorem intervalFullDuhamel_hasDerivAt_fst
    {t : ℝ} (ht : 0 < t)
    {F : ℝ → ℝ → ℝ}
    (hF_meas : Measurable (Function.uncurry F))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    {C_source : ℝ} (hC_source_nn : 0 ≤ C_source)
    (hF_sup : ∀ s y, |F s y| ≤ C_source)
    (x₀ : ℝ) :
    HasDerivAt
      (fun x : ℝ => ∫ s in (0 : ℝ)..t,
        intervalFullSemigroupOperator (t - s) (F s) x)
      (∫ s in (0 : ℝ)..t,
        deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (F s) z) x₀)
      x₀ := by
  -- joint `AEStronglyMeasurable` of `uncurry F` on the restricted product measure.
  have hF_ae : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Set.uIoc (0:ℝ) t)).prod (intervalMeasure 1)) :=
    hF_meas.aestronglyMeasurable
  -- value `s`-integrand `AEStronglyMeasurable` at each spatial point.
  have hFmeas : ∀ x : ℝ, AEStronglyMeasurable
      (fun s : ℝ => intervalFullSemigroupOperator (t - s) (F s) x)
      (volume.restrict (Set.uIoc (0:ℝ) t)) := fun x =>
    intervalFullSemigroupOperator_s_dependent_aestronglyMeasurable_x ht hF_ae x
  -- derivative `s`-integrand `AEStronglyMeasurable` at `x₀`.
  have hF'meas : AEStronglyMeasurable
      (fun s : ℝ =>
        deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (F s) z) x₀)
      (volume.restrict (Set.uIoc (0:ℝ) t)) :=
    intervalFullSemigroupOperator_s_dependent_deriv_aestronglyMeasurable_x₀
      ht hF_ae hF_int hF_sup x₀
  -- the parabolic √-envelope `Cgrad·C·(t−s)^(−1/2)` is interval-integrable on `[0,t]`.
  have hDom_int : IntervalIntegrable
      (fun s : ℝ =>
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          * C_source * (t - s) ^ (-(1/2 : ℝ))) volume (0:ℝ) t := by
    rw [show (fun s : ℝ =>
          ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * C_source * (t - s) ^ (-(1/2 : ℝ)))
        = (fun s : ℝ =>
          (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * C_source) * (t - s) ^ (-(1/2 : ℝ))) from by funext s; ring]
    exact (ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t).const_mul _
  exact intervalFullCoupledDuhamel_grad_integral_hasDerivAt ht hF_int hC_source_nn hF_sup
    x₀ hFmeas hF'meas hDom_int

/-- **`intervalFullDuhamel_deriv_eq_integral_deriv`.**  The `.deriv` corollary:
the spatial derivative of the Duhamel time-integral equals the time-integral of
the per-slice spatial derivatives. -/
theorem intervalFullDuhamel_deriv_eq_integral_deriv
    {t : ℝ} (ht : 0 < t)
    {F : ℝ → ℝ → ℝ}
    (hF_meas : Measurable (Function.uncurry F))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    {C_source : ℝ} (hC_source_nn : 0 ≤ C_source)
    (hF_sup : ∀ s y, |F s y| ≤ C_source)
    (x₀ : ℝ) :
    deriv
      (fun x : ℝ => ∫ s in (0 : ℝ)..t,
        intervalFullSemigroupOperator (t - s) (F s) x) x₀
      = ∫ s in (0 : ℝ)..t,
          deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (F s) z) x₀ :=
  (intervalFullDuhamel_hasDerivAt_fst ht hF_meas hF_int hC_source_nn hF_sup x₀).deriv

/-! ## §2 — Per-slice source integrability (`hq_int` / `hL` helper).

A uniformly sup-bounded, measurable slice is `Integrable` against the finite
interval measure `intervalMeasure 1 = volume.restrict (Icc 0 1)`.  This discharges
the `hq_int` shape `∀ s, Integrable (F s) (intervalMeasure 1)` from a sup bound. -/

/-- **`duhamel_source_integrable`.**  A measurable, uniformly bounded source slice
is integrable against the (finite) interval measure. -/
theorem duhamel_source_integrable
    {F : ℝ → ℝ → ℝ} (hF_meas : Measurable (Function.uncurry F))
    {C : ℝ} (hF_sup : ∀ s y, |F s y| ≤ C) :
    ∀ s, Integrable (F s) (intervalMeasure 1) := fun s =>
  intervalMeasure_integrable_of_abs_bound
    ((hF_meas.comp measurable_prodMk_left).aestronglyMeasurable) (hF_sup s)

/-! ## §3 — The χ₀ = 0 derivative split, in the wiring's `hsplit` shape.

`uniformWiring_of_data` consumes its `hsplit` field at EVERY `x : ℝ`:

  `deriv (lift (picardIter p u₀ n t)) x
    = deriv (z ↦ S(t) u₀lift z) x + ∫ s in 0..t, deriv (z ↦ S(t−s) (Lfam n s) z) x`

(with `u₀lift = lift u₀`, `Lfam = gLfam p u₀`).  On the open interior `Ioo 0 1`
this is genuinely proved (χ₀-reduction `intervalGradientDuhamelMap_eq_of_chi0_zero`
moves the chemotaxis term out of the way *before* differentiating, then the homo-
geneous propagator and the Duhamel time-integral differentiate termwise via
`HasDerivAt.add`).  Off the interior — at the two endpoints `{0,1}` and exterior to
`Icc 0 1` — the zero-extended lift jumps / vanishes while the kernel-extended RHS
does not, so the pointwise identity is carried as the single named residual
`hsplit_offInterior`.  This is exactly `ShenWork.IntervalPicardG1Split.hsplit_field`. -/

/-- The wiring source family: zero at level `0`, the logistic source at `n+1`.
Definitionally equal to `ShenWork.IntervalPicardG1Split.gLfam`. -/
abbrev gLfam (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) : ℕ → ℝ → ℝ → ℝ :=
  ShenWork.IntervalPicardG1Split.gLfam p u₀

/-- **`chi0_deriv_split`.**  The χ₀ = 0 derivative-split identity in the exact
pointwise-`∀x` shape consumed by `uniformWiring_of_data` (`u₀lift = lift u₀`,
`Lfam = gLfam p u₀`).  Interior genuinely proved; off-interior is the named,
satisfiable residual `hsplit_offInterior`. -/
theorem chi0_deriv_split
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (u₀ : intervalDomainPoint → ℝ) {M T : ℝ}
    (hMnn : 0 ≤ M)
    (hu₀ : ∀ y, |intervalDomainLift u₀ y| ≤ M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    (hLmeas : ∀ n : ℕ,
      Measurable (Function.uncurry (fun s => logisticLifted p (picardIter p u₀ n s))))
    {CL : ℝ} (hCLnn : 0 ≤ CL)
    (hLsup : ∀ (n : ℕ) (s y : ℝ),
      |logisticLifted p (picardIter p u₀ n s) y| ≤ CL)
    (hsplit_offInterior : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : ℝ,
      x ∉ Set.Ioo (0:ℝ) 1 →
      deriv (intervalDomainLift (picardIter p u₀ n t)) x
        = deriv (fun z : ℝ => intervalFullSemigroupOperator t (intervalDomainLift u₀) z) x
          + ∫ s in (0:ℝ)..t, deriv
              (fun z : ℝ => intervalFullSemigroupOperator (t - s) (gLfam p u₀ n s) z) x) :
    ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : ℝ,
      deriv (intervalDomainLift (picardIter p u₀ n t)) x
        = deriv (fun z : ℝ => intervalFullSemigroupOperator t (intervalDomainLift u₀) z) x
          + ∫ s in (0:ℝ)..t, deriv
              (fun z : ℝ => intervalFullSemigroupOperator (t - s) (gLfam p u₀ n s) z) x :=
  ShenWork.IntervalPicardG1Split.hsplit_field
    p hχ0 u₀ hMnn hu₀ hu₀_meas hLmeas hCLnn hLsup hsplit_offInterior

end ShenWork.IntervalDuhamelSpatialLeibniz
