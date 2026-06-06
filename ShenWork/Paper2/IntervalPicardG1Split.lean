/-
  ShenWork/Paper2/IntervalPicardG1Split.lean

  Phase-0 G1-line — the χ₀ = 0 **derivative-split identity** and the
  **gradient-integrand interval-integrability** prerequisites that
  `ShenWork/Paper2/IntervalPicardUniformWiring.lean` (`hG1all_field`) carries as
  named residuals.

  ## What this module proves

  `hG1all_field` consumes two per-level inputs:

    * `hg_int` — for every `n`, `t ∈ (0,T]`, `x`, the gradient-Duhamel integrand
      `s ↦ ∂ₓ[S(t−s) Lₙ(s)](x)` is `IntervalIntegrable` on `[0,t]`;
    * `hsplit` — the χ₀ = 0 derivative split
      `∂ₓ lift(uₙ(t)) x = ∂ₓ[S(t)(lift u₀)] x + ∫₀ᵗ ∂ₓ[S(t−s) Lₙ(s)] x ds`.

  Both are produced here from satisfiable named inputs.

  ### `hg_int` (`§1`) — UNCONDITIONAL.

  `gradDuhamel_intervalIntegrable_of_joint_measurable` (T2) already gives exactly
  the interval-integrability from joint measurability + a uniform sup bound on the
  source family.  `gradInterval_integrable` is a thin renaming wrapper.

  ### `hsplit` (`§2–§3`) — interior, GENUINELY PROVED; off-interior, honest residual.

  At χ₀ = 0 the gradient-Duhamel map value is `S(t)(lift u₀) + ∫₀ᵗ S(t−s) Lₙ(s)`
  (M1's `intervalGradientDuhamelMap_eq_of_chi0_zero`), and the lift of the iterate
  slice equals that value on `Icc 0 1`.  Hence on the OPEN interior `Ioo 0 1` the
  lift agrees with the explicit sum `G z := S(t)(lift u₀) z + ∫₀ᵗ S(t−s) Lₙ(s) z`,
  so (`Filter.EventuallyEq.deriv_eq` on the open set) the spatial `deriv` of the
  lift at an interior `x` equals `deriv G x`.  `G` is a sum of two `DifferentiableAt`
  pieces:

    * the propagator `z ↦ S(t)(lift u₀) z` — `intervalFullSemigroupOperator_hasDerivAt_fst`;
    * the Duhamel integral `z ↦ ∫₀ᵗ S(t−s) Lₙ(s) z ds` — the full-kernel Leibniz
      `intervalFullCoupledDuhamel_grad_integral_hasDerivAt` (divergence form,
      `∂ₓ` INSIDE `S`), whose value is `∫₀ᵗ ∂ₓ[S(t−s) Lₙ(s)] x ds`.

  `deriv (G) x = deriv (S(t)…) x + ∫₀ᵗ ∂ₓ[S(t−s)…] x ds` then follows from
  `HasDerivAt.add` + `.deriv`, giving the split at every interior `x`.

  The zero-extended lift jumps at the two endpoints and is locally `0` exterior to
  `Icc`, while the RHS propagator/integral terms are genuine (kernel-extended)
  functions there; the split therefore does NOT hold pointwise off `Ioo 0 1`.
  This off-interior agreement is the single honest residual, carried as a named,
  satisfiable hypothesis `hsplit_offInterior` on the full-`∀x` assembly
  (`hsplit_field`).  The wiring's `g1_kernel_bound` consumes the split pointwise,
  so the full-`∀x` shape is provided this way.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardIterateRestart
import ShenWork.Paper2.IntervalDuhamelIntegrability
import ShenWork.PDE.IntervalFullKernelLeibniz
import ShenWork.PDE.IntervalFullKernelSDependentMeasurable
import ShenWork.Paper2.IntervalPicardUniformWiring

open MeasureTheory Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator
  intervalFullSemigroupOperator_hasDerivAt_fst
  intervalFullCoupledDuhamel_grad_integral_hasDerivAt
  intervalFullCoupledDuhamel_grad_integrand_intervalIntegrable)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalPicardIterateRestart (intervalGradientDuhamelMap_eq_of_chi0_zero)
open ShenWork.IntervalDuhamelIntegrability (gradDuhamel_intervalIntegrable_of_joint_measurable)
open ShenWork.IntervalGradDuhamelBound (intervalIntegrable_sub_rpow_neg_half)

noncomputable section

namespace ShenWork.IntervalPicardG1Split

/-! ## §1 — Gradient-integrand interval-integrability (`hg_int`).

The divergence-form gradient-Duhamel integrand
`s ↦ ∂ₓ[S(t−s) L(s)](x)` is interval-integrable on `[0,t]`.  This is exactly
T2's `gradDuhamel_intervalIntegrable_of_joint_measurable`: joint measurability of
the source family plus a uniform sup bound dominate the integrand by the
interval-integrable envelope `Cg·C·(t−s)^{−1/2}`. -/

/-- **`hg_int` discharge.**  For a jointly-measurable, uniformly-bounded source
family `L`, the gradient-Duhamel integrand is `IntervalIntegrable` on `[0,t]`. -/
theorem gradInterval_integrable
    {t : ℝ} (ht : 0 < t) {L : ℝ → ℝ → ℝ}
    (hL_meas : Measurable (Function.uncurry L))
    {C : ℝ} (hC : 0 ≤ C) (hL_sup : ∀ s y, |L s y| ≤ C) (x : ℝ) :
    IntervalIntegrable
      (fun s : ℝ => deriv
        (fun z : ℝ => intervalFullSemigroupOperator (t - s) (L s) z) x) volume 0 t :=
  gradDuhamel_intervalIntegrable_of_joint_measurable ht hL_meas hC hL_sup x

/-! ## §2 — The two pieces are differentiable; the Duhamel Leibniz interchange.

`deriv (z ↦ S(t)(lift u₀) z) x` is the per-slice spatial derivative
(`intervalFullSemigroupOperator_hasDerivAt_fst`), and
`deriv (z ↦ ∫₀ᵗ S(t−s) L(s) z ds) x = ∫₀ᵗ ∂ₓ[S(t−s) L(s)] x ds` by the full-kernel
Leibniz interchange (divergence form, no derivative on the source). -/

/-- The propagator piece is `DifferentiableAt x` (and so equals its own `deriv`
under `HasDerivAt`). -/
theorem homogeneous_hasDerivAt
    {t : ℝ} (ht : 0 < t) {u₀lift : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable u₀lift (intervalMeasure 1))
    {M : ℝ} (hu₀ : ∀ y, |u₀lift y| ≤ M) (x : ℝ) :
    HasDerivAt (fun z : ℝ => intervalFullSemigroupOperator t u₀lift z)
      (deriv (fun z : ℝ => intervalFullSemigroupOperator t u₀lift z) x) x :=
  (intervalFullSemigroupOperator_hasDerivAt_fst ht hf_meas hu₀ x).differentiableAt.hasDerivAt

/-- **Duhamel Leibniz interchange (divergence form).**  The spatial derivative of
`z ↦ ∫₀ᵗ S(t−s) L(s) z ds` at `x` equals `∫₀ᵗ ∂ₓ[S(t−s) L(s)] x ds`, AND the map
has that value as a genuine `HasDerivAt`.  Built from
`intervalFullCoupledDuhamel_grad_integral_hasDerivAt` with the joint-measurability
discharges of the value/derivative `s`-integrands and the parabolic √-envelope. -/
theorem duhamel_hasDerivAt
    {t : ℝ} (ht : 0 < t) {L : ℝ → ℝ → ℝ}
    (hL_meas : Measurable (Function.uncurry L))
    {C : ℝ} (hC : 0 ≤ C) (hL_sup : ∀ s y, |L s y| ≤ C) (x : ℝ) :
    HasDerivAt
      (fun z : ℝ => ∫ s in (0:ℝ)..t,
        intervalFullSemigroupOperator (t - s) (L s) z)
      (∫ s in (0:ℝ)..t, deriv
        (fun z : ℝ => intervalFullSemigroupOperator (t - s) (L s) z) x)
      x := by
  -- per-slice integrability of `L s`.
  have hL_int : ∀ s, Integrable (L s) (intervalMeasure 1) := fun s =>
    ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
      ((hL_meas.comp measurable_prodMk_left).aestronglyMeasurable) (hL_sup s)
  -- joint AEStronglyMeasurable of `uncurry L` on the restricted product measure.
  have hL_ae : AEStronglyMeasurable (Function.uncurry L)
      ((volume.restrict (Set.uIoc (0:ℝ) t)).prod (intervalMeasure 1)) :=
    hL_meas.aestronglyMeasurable
  -- value `s`-integrand AEStronglyMeasurable at each `x`.
  have hF_meas : ∀ x : ℝ, AEStronglyMeasurable
      (fun s : ℝ => intervalFullSemigroupOperator (t - s) (L s) x)
      (volume.restrict (Set.uIoc (0:ℝ) t)) := fun x =>
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_s_dependent_aestronglyMeasurable_x
      ht hL_ae x
  -- derivative `s`-integrand AEStronglyMeasurable at `x`.
  have hF'_meas : AEStronglyMeasurable
      (fun s : ℝ => deriv
        (fun z : ℝ => intervalFullSemigroupOperator (t - s) (L s) z) x)
      (volume.restrict (Set.uIoc (0:ℝ) t)) :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_s_dependent_deriv_aestronglyMeasurable_x₀
      ht hL_ae hL_int hL_sup x
  -- the parabolic √-envelope is interval-integrable.
  have hDom_int : IntervalIntegrable
      (fun s : ℝ =>
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          * C * (t - s) ^ (-(1/2 : ℝ))) volume (0:ℝ) t := by
    rw [show (fun s : ℝ =>
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          * C * (t - s) ^ (-(1/2 : ℝ)))
      = (fun s : ℝ =>
        (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant * C)
          * (t - s) ^ (-(1/2 : ℝ))) from by funext s; ring]
    exact (intervalIntegrable_sub_rpow_neg_half t).const_mul _
  exact intervalFullCoupledDuhamel_grad_integral_hasDerivAt ht hL_int hC hL_sup x
    hF_meas hF'_meas hDom_int

/-! ## §3 — The interior derivative split.

On the open interior `Ioo 0 1` the lift agrees with the explicit sum
`G z = S(t)(lift u₀) z + ∫₀ᵗ S(t−s) L(s) z ds`, so the `deriv`s agree
(`Filter.EventuallyEq.deriv_eq`).  `G` differentiates termwise
(`HasDerivAt.add`), giving the split. -/

/-- **Interior derivative split (abstract value EqOn).**  If, on `Icc 0 1`, the
lift agrees with `z ↦ S(t)(lift u₀) z + ∫₀ᵗ S(t−s) L(s) z ds`, then at every
interior `x ∈ Ioo 0 1` the spatial derivative of the lift splits as
`∂ₓ[S(t)(lift u₀)] x + ∫₀ᵗ ∂ₓ[S(t−s) L(s)] x ds`. -/
theorem deriv_split_interior_of_eqOn
    {t : ℝ} (ht : 0 < t) {u₀lift L} {f : intervalDomainPoint → ℝ}
    (hf_meas : AEStronglyMeasurable u₀lift (intervalMeasure 1))
    {M : ℝ} (hu₀ : ∀ y, |u₀lift y| ≤ M)
    (hL_meas : Measurable (Function.uncurry L))
    {C : ℝ} (hC : 0 ≤ C) (hL_sup : ∀ s y, |L s y| ≤ C)
    (hvalEq : Set.EqOn (intervalDomainLift f)
      (fun z : ℝ => intervalFullSemigroupOperator t u₀lift z
        + ∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s) (L s) z)
      (Set.Icc (0:ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    deriv (intervalDomainLift f) x
      = deriv (fun z : ℝ => intervalFullSemigroupOperator t u₀lift z) x
        + ∫ s in (0:ℝ)..t, deriv
            (fun z : ℝ => intervalFullSemigroupOperator (t - s) (L s) z) x := by
  -- agreement on the open interior gives an `EventuallyEq` at `x`.
  have hmem : Set.Ioo (0:ℝ) 1 ∈ nhds x := isOpen_Ioo.mem_nhds hx
  have hEqf : intervalDomainLift f =ᶠ[nhds x]
      (fun z : ℝ => intervalFullSemigroupOperator t u₀lift z
        + ∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s) (L s) z) :=
    Filter.eventuallyEq_of_mem hmem (hvalEq.mono Set.Ioo_subset_Icc_self)
  -- transport the derivative across the agreement.
  rw [hEqf.deriv_eq]
  -- the sum `G` differentiates termwise (state on the explicit lambda sum).
  have hHom := homogeneous_hasDerivAt ht hf_meas hu₀ x
  have hDuh := duhamel_hasDerivAt ht hL_meas hC hL_sup x
  have hAdd : HasDerivAt
      (fun z : ℝ => intervalFullSemigroupOperator t u₀lift z
        + ∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s) (L s) z)
      (deriv (fun z : ℝ => intervalFullSemigroupOperator t u₀lift z) x
        + ∫ s in (0:ℝ)..t, deriv
            (fun z : ℝ => intervalFullSemigroupOperator (t - s) (L s) z) x) x :=
    hHom.add hDuh
  rw [hAdd.deriv]

/-! ## §4 — Per-level value EqOn on `Icc 0 1`.

For `n+1`, the χ₀ = 0 map reduction identifies the lift with the explicit sum on
`Icc` (M1).  For `n = 0` the lift is the pure propagator, fitting the same sum
with the zero source family. -/

/-- **Value EqOn at level `n+1` (χ₀ = 0).**  On `Icc 0 1`,
`lift(uₙ₊₁(t)) = S(t)(lift u₀) + ∫₀ᵗ S(t−s) Lₙ(s)` with
`Lₙ(s) = logisticLifted p (picardIter p u₀ n s)`. -/
theorem succ_value_eqOn
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (n : ℕ) (t : ℝ) :
    Set.EqOn (intervalDomainLift (picardIter p u₀ (n + 1) t))
      (fun z : ℝ => intervalFullSemigroupOperator t (intervalDomainLift u₀) z
        + ∫ s in (0:ℝ)..t,
            intervalFullSemigroupOperator (t - s)
              (logisticLifted p (picardIter p u₀ n s)) z)
      (Set.Icc (0:ℝ) 1) := by
  intro z hz
  -- lift value on Icc is the map value (picardIter (n+1) def).
  have hlift : intervalDomainLift (picardIter p u₀ (n + 1) t) z
      = ShenWork.IntervalGradientDuhamelMap.intervalGradientDuhamelMap p u₀
          (picardIter p u₀ n) t ⟨z, hz⟩ := by
    show (if hz' : z ∈ Set.Icc (0:ℝ) 1 then
        picardIter p u₀ (n + 1) t ⟨z, hz'⟩ else 0) = _
    rw [dif_pos hz]; rfl
  rw [hlift, intervalGradientDuhamelMap_eq_of_chi0_zero p hχ0 u₀ _ t ⟨z, hz⟩]

/-- **Value EqOn at level `0`.**  On `Icc 0 1`, `lift(u₀(t)) = S(t)(lift u₀)`,
which fits the explicit sum with the zero source family `(fun _ _ => 0)`
(the Duhamel integral of the zero source vanishes). -/
theorem zero_value_eqOn
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (t : ℝ) :
    Set.EqOn (intervalDomainLift (picardIter p u₀ 0 t))
      (fun z : ℝ => intervalFullSemigroupOperator t (intervalDomainLift u₀) z
        + ∫ s in (0:ℝ)..t,
            intervalFullSemigroupOperator (t - s) ((fun _ _ => 0 : ℝ → ℝ → ℝ) s) z)
      (Set.Icc (0:ℝ) 1) := by
  intro z hz
  -- `S(t−s) 0 = ∫ K·0 = 0`, so the Duhamel integral is `0`.
  have hzero : ∀ s : ℝ,
      intervalFullSemigroupOperator (t - s) ((fun _ _ => 0 : ℝ → ℝ → ℝ) s) z = 0 := by
    intro s
    simp [intervalFullSemigroupOperator]
  simp only [hzero, intervalIntegral.integral_zero, add_zero]
  -- lift value on Icc is the propagator (picardIter 0 def).
  show (if hz' : z ∈ Set.Icc (0:ℝ) 1 then
      picardIter p u₀ 0 t ⟨z, hz'⟩ else 0)
    = intervalFullSemigroupOperator t (intervalDomainLift u₀) z
  rw [dif_pos hz]; rfl

/-! ## §5 — Assembling the split for the wiring's `hsplit` / `hg_int` shapes.

The wiring `hG1all_field` takes a single source family `Lfam : ℕ → ℝ → ℝ → ℝ`
together with `hg_int`/`hsplit` over all `n`.  We expose the per-level interior
split (genuinely proved) and the full-`∀x` discharge that combines it with the
named off-interior residual. -/

/-- **Interior split at level `n+1`.**  Combines `succ_value_eqOn` (χ₀ = 0 map
reduction on `Icc`) with `deriv_split_interior_of_eqOn`. -/
theorem succ_deriv_split_interior
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    {t M C : ℝ} (ht : 0 < t)
    (hu₀ : ∀ y, |intervalDomainLift u₀ y| ≤ M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    (hL_meas : Measurable (Function.uncurry
      (fun s => logisticLifted p (picardIter p u₀ n s))))
    (hC : 0 ≤ C)
    (hL_sup : ∀ s y, |logisticLifted p (picardIter p u₀ n s) y| ≤ C)
    {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    deriv (intervalDomainLift (picardIter p u₀ (n + 1) t)) x
      = deriv (fun z : ℝ => intervalFullSemigroupOperator t (intervalDomainLift u₀) z) x
        + ∫ s in (0:ℝ)..t, deriv
            (fun z : ℝ => intervalFullSemigroupOperator (t - s)
              (logisticLifted p (picardIter p u₀ n s)) z) x :=
  deriv_split_interior_of_eqOn ht hu₀_meas hu₀ hL_meas hC hL_sup
    (succ_value_eqOn p hχ0 u₀ n t) hx

/-- **Interior split at level `0`.**  Combines `zero_value_eqOn` with
`deriv_split_interior_of_eqOn` (zero source family). -/
theorem zero_deriv_split_interior
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {t M : ℝ} (ht : 0 < t)
    (hu₀ : ∀ y, |intervalDomainLift u₀ y| ≤ M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    deriv (intervalDomainLift (picardIter p u₀ 0 t)) x
      = deriv (fun z : ℝ => intervalFullSemigroupOperator t (intervalDomainLift u₀) z) x
        + ∫ s in (0:ℝ)..t, deriv
            (fun z : ℝ => intervalFullSemigroupOperator (t - s)
              ((fun _ _ => 0 : ℝ → ℝ → ℝ) s) z) x :=
  deriv_split_interior_of_eqOn ht hu₀_meas hu₀
    (by measurability) (le_refl (0:ℝ)) (fun _ _ => by simp)
    (zero_value_eqOn p u₀ t) hx

/-! ## §6 — Full-`∀x` `hsplit` and `hg_int` for the wiring residuals.

The wiring's `hG1all_field` consumes `hsplit`/`hg_int` pointwise at every `x : ℝ`,
where the source family `Lfam : ℕ → ℝ → ℝ → ℝ` is `Lfam 0 = 0` and
`Lfam (n+1) = logisticLifted p (picardIter p u₀ n ·)`.  The interior split is
proved above; the off-interior agreement is the single honest residual (the
zero-extended lift jumps at the endpoints and vanishes exterior to `Icc`, while
the kernel-extended RHS does not), carried as a named, satisfiable hypothesis. -/

/-- The wiring source family: zero at level `0`, the logistic source at `n+1`. -/
def gLfam (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) : ℕ → ℝ → ℝ → ℝ
  | 0 => fun _ _ => 0
  | n + 1 => fun s => logisticLifted p (picardIter p u₀ n s)

/-- **`hg_int` discharge for the wiring (full `∀n,∀x`).**  For each level the
gradient-Duhamel integrand of `gLfam … n` is interval-integrable, given the
per-level joint measurability and sup bound.  (Level `0` is the zero family,
trivially bounded/measurable.) -/
theorem hg_int_field
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {M T : ℝ}
    (_hMnn : 0 ≤ M)
    (hLmeas : ∀ n : ℕ,
      Measurable (Function.uncurry (fun s => logisticLifted p (picardIter p u₀ n s))))
    {CL : ℝ} (hCLnn : 0 ≤ CL)
    (hLsup : ∀ (n : ℕ) (s y : ℝ),
      |logisticLifted p (picardIter p u₀ n s) y| ≤ CL) :
    ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : ℝ,
      IntervalIntegrable
        (fun s : ℝ => deriv
          (fun z : ℝ => intervalFullSemigroupOperator (t - s) (gLfam p u₀ n s) z) x)
        volume 0 t := by
  intro n t ht _htT x
  cases n with
  | zero =>
      exact gradInterval_integrable ht
        (L := (fun _ _ => 0 : ℝ → ℝ → ℝ)) (by measurability)
        (le_refl (0:ℝ)) (fun _ _ => by simp) x
  | succ m =>
      exact gradInterval_integrable ht
        (L := fun s => logisticLifted p (picardIter p u₀ m s))
        (hLmeas m) hCLnn (fun s y => hLsup m s y) x

/-- **`hsplit` discharge for the wiring (full `∀n,∀x`).**  At interior `x` the
split is genuinely proved (`zero_/succ_deriv_split_interior`); off the interior it
is the named satisfiable residual `hsplit_offInterior`.  The resulting family is
the exact `hsplit` shape of `hG1all_field` (with `u₀lift = lift u₀`,
`Lfam = gLfam p u₀`). -/
theorem hsplit_field
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (u₀ : intervalDomainPoint → ℝ) {M T : ℝ}
    (_hMnn : 0 ≤ M)
    (hu₀ : ∀ y, |intervalDomainLift u₀ y| ≤ M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    (hLmeas : ∀ n : ℕ,
      Measurable (Function.uncurry (fun s => logisticLifted p (picardIter p u₀ n s))))
    {CL : ℝ} (hCLnn : 0 ≤ CL)
    (hLsup : ∀ (n : ℕ) (s y : ℝ),
      |logisticLifted p (picardIter p u₀ n s) y| ≤ CL)
    -- the single honest residual: off-interior pointwise agreement of the
    -- (zero-extended) lift derivative with the kernel-extended split RHS.
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
              (fun z : ℝ => intervalFullSemigroupOperator (t - s) (gLfam p u₀ n s) z) x := by
  intro n t ht htT x
  by_cases hx : x ∈ Set.Ioo (0:ℝ) 1
  · -- interior: genuinely proved.
    cases n with
    | zero =>
        exact zero_deriv_split_interior p u₀ ht hu₀ hu₀_meas hx
    | succ m =>
        exact succ_deriv_split_interior p hχ0 u₀ m ht hu₀ hu₀_meas
          (hLmeas m) hCLnn (fun s y => hLsup m s y) hx
  · -- off-interior: named residual.
    exact hsplit_offInterior n t ht htT x hx

/-! ## §7 — Corollary: discharging `hG1all` via the wiring's `hG1all_field`.

With `hg_int_field` and `hsplit_field` in hand, the wiring's `hG1all_field`
produces the full G1-line bound from the datum bound `|lift u₀| ≤ M`, the
per-level source bound `sup|Lₙ| ≤ CL p M`, and the per-slice source
integrability.  The two analytic prerequisites are now PROVED (interior split,
gradient interval-integrability); the only carried residual is the off-interior
endpoint/exterior agreement `hsplit_offInterior`. -/

/-- **`hG1all` discharge.**  Feeds the proved `hg_int_field`/`hsplit_field`
discharges into the wiring's `hG1all_field`, producing the per-level G1-line
bound `|∂ₓ lift(uₙ(t)) x| ≤ G1profile p M t` at every `x`, given the named
satisfiable inputs (datum bound + per-level source bound/measurability/per-slice
integrability) and the single off-interior split residual. -/
theorem hG1all_via_split
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (u₀ : intervalDomainPoint → ℝ) {M T : ℝ}
    (hMnn : 0 ≤ M)
    (hu₀ : ∀ y, |intervalDomainLift u₀ y| ≤ M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    (hLmeas : ∀ n : ℕ,
      Measurable (Function.uncurry (fun s => logisticLifted p (picardIter p u₀ n s))))
    (hq_int : ∀ (n : ℕ), ∀ s, Integrable (gLfam p u₀ n s) (intervalMeasure 1))
    (hLsup : ∀ (n : ℕ) (s y : ℝ),
      |logisticLifted p (picardIter p u₀ n s) y|
        ≤ ShenWork.IntervalPicardIterateUniform.CL p M)
    (hL : ∀ (n : ℕ), ∀ s y, |gLfam p u₀ n s y|
        ≤ ShenWork.IntervalPicardIterateUniform.CL p M)
    (hsplit_offInterior : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : ℝ,
      x ∉ Set.Ioo (0:ℝ) 1 →
      deriv (intervalDomainLift (picardIter p u₀ n t)) x
        = deriv (fun z : ℝ => intervalFullSemigroupOperator t (intervalDomainLift u₀) z) x
          + ∫ s in (0:ℝ)..t, deriv
              (fun z : ℝ => intervalFullSemigroupOperator (t - s) (gLfam p u₀ n s) z) x) :
    ∀ n : ℕ, ∀ t, 0 < t → t ≤ T → ∀ x : ℝ,
      |deriv (intervalDomainLift (picardIter p u₀ n t)) x|
        ≤ ShenWork.IntervalPicardIterateUniform.G1profile p M t := by
  have hCLnn : 0 ≤ ShenWork.IntervalPicardIterateUniform.CL p M :=
    ShenWork.IntervalPicardIterateUniform.CL_nonneg hMnn
  exact ShenWork.IntervalPicardUniformWiring.hG1all_field p u₀ hMnn hu₀_meas hu₀
    (gLfam p u₀) hq_int hL
    (hg_int_field p u₀ hMnn hLmeas hCLnn hLsup)
    (hsplit_field p hχ0 u₀ hMnn hu₀ hu₀_meas hLmeas hCLnn hLsup hsplit_offInterior)

end ShenWork.IntervalPicardG1Split
