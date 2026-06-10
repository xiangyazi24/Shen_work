/-
  ShenWork/Paper2/IntervalPicardG1All.lean

  **The kernel-G1 line, all levels — `hG1all` derived from the cone (hand-written).**

  Closes the `hG1all` leg of `TowerConeAnalyticResidual`.  The previously-reported
  blocker — the split machinery demands a GLOBAL all-`s` source sup
  `∀ s y, |L s y| ≤ CL p M`, while the cone ball controls only `s ∈ (0,T]` — is
  dissolved by the **windowed source family**

      wSrc (n+1) s y := if 0 < s ∧ s ≤ T then logisticLifted p (uₙ(s)) y else 0,

  which satisfies the global sup by construction, agrees with the canonical
  family on the integration range `Ioc 0 t` (`t ≤ T`), and therefore satisfies
  the same value `EqOn` (Duhamel integral congruence) — so the existing interior
  split + `g1_kernel_bound` apply verbatim, with NO rebuild of the kernel
  interchange chain.

  Inputs (all cone-supplied or derived herein):
  * joint measurability of every iterate — proved here by induction
    (`picardIter_hasJointMeasurability_all`): base = the propagator's joint
    measurability; step = the value-Duhamel preservation (χ₀ = 0), replicating
    the cone-construction pattern with the public primed lemmas;
  * the n-uniform subtype ball on `(0,T]` (cone `hball`) — windowed sup;
  * `∀ z, |lift u₀ z| ≤ M` — derived from the mild initial approach
    (`u₀_lift_abs_le`): `|u₀| ≤ |u₀ − Φ(s)| + |D.u s| < ε + M` for small `s`;
  * integrability of the window slices — sections of the joint measurability
    plus the window bound (NO slice-continuity input needed).

  Pointwise structure over `x : ℝ`: interior via the (windowed) split +
  `g1_kernel_bound`; endpoints via `deriv_lift_eq_zero_at_left/right`;
  exterior via `deriv_lift_eq_zero_on_Iio/Ioi`; off-interior the bound is
  `0 ≤ G1profile`.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardG1Split
import ShenWork.Paper2.IntervalCompactSliceGradientBounds
import ShenWork.Paper2.IntervalMildPicardConeData

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted intervalGradientDuhamelMap)
open ShenWork.IntervalMildPicard (picardIter HasJointMeasurability
  GradientMildSolutionData)
open ShenWork.IntervalMildPicardThreshold
  (logisticLifted_joint_measurable' intervalDomainLift_measurable_of_continuous'
   intervalFullSemigroupOperator_joint_measurable'
   variable_interval_integral_measurable'
   intervalFullSemigroupOperator_s_param_joint_measurable'
   gradientMildSolutionData_initialApproach)
open ShenWork.IntervalDomain (intervalMeasure_integrable_of_abs_bound)
open ShenWork.IntervalPicardIterateUniform (CL CL_nonneg G1profile g1_kernel_bound)
open ShenWork.IntervalPicardG1Split
  (gradInterval_integrable deriv_split_interior_of_eqOn succ_value_eqOn
   zero_value_eqOn)
open ShenWork.Paper2.CompactSliceGradientBounds
  (deriv_lift_eq_zero_at_left deriv_lift_eq_zero_at_right
   deriv_lift_eq_zero_on_Iio deriv_lift_eq_zero_on_Ioi)

noncomputable section

namespace ShenWork.IntervalPicardG1All

/-! ## §1 — Joint measurability of every Picard iterate (χ₀ = 0). -/

/-- **Joint measurability of all iterates.**  Base: the lifted level-0 slice is the
propagator value, ite-decomposed over `Icc`.  Step: the χ₀ = 0 value-Duhamel map
preserves joint measurability (the public primed measurability atoms). -/
theorem picardIter_hasJointMeasurability_all
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (u₀ : intervalDomainPoint → ℝ)
    (hu₀_cont : Continuous u₀) :
    ∀ n : ℕ, HasJointMeasurability (picardIter p u₀ n) := by
  have hSg_meas : Measurable (fun q : ℝ × ℝ =>
      intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2) :=
    intervalFullSemigroupOperator_joint_measurable'
      (intervalDomainLift_measurable_of_continuous' hu₀_cont)
  intro n
  induction n with
  | zero =>
    have hfield :
        (fun q : ℝ × ℝ => intervalDomainLift (picardIter p u₀ 0 q.1) q.2) =
          fun q : ℝ × ℝ =>
            if q.2 ∈ Set.Icc (0 : ℝ) 1 then
              intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2
            else 0 := by
      funext q
      by_cases hy : q.2 ∈ Set.Icc (0 : ℝ) 1
      · simp [intervalDomainLift, hy]; rfl
      · simp [intervalDomainLift, hy]
    show Measurable (fun q : ℝ × ℝ =>
      intervalDomainLift (picardIter p u₀ 0 q.1) q.2)
    rw [hfield]
    exact Measurable.ite (measurableSet_Icc.preimage measurable_snd)
      hSg_meas measurable_const
  | succ n ih =>
    have hL_meas :
        Measurable (Function.uncurry
          (fun s y => logisticLifted p (picardIter p u₀ n s) y)) := by
      simpa [Function.uncurry] using logisticLifted_joint_measurable' ih
    have hVal_integrand : Measurable (fun r : (ℝ × ℝ) × ℝ =>
        intervalFullSemigroupOperator (r.1.1 - r.2)
          (logisticLifted p (picardIter p u₀ n r.2)) r.1.2) :=
      intervalFullSemigroupOperator_s_param_joint_measurable' hL_meas
    have hVal : Measurable (fun q : ℝ × ℝ =>
        ∫ s in (0 : ℝ)..q.1,
          intervalFullSemigroupOperator (q.1 - s)
            (logisticLifted p (picardIter p u₀ n s)) q.2) :=
      variable_interval_integral_measurable' hVal_integrand
    have hinside : Measurable (fun q : ℝ × ℝ =>
        intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2
          + ∫ s in (0 : ℝ)..q.1,
            intervalFullSemigroupOperator (q.1 - s)
              (logisticLifted p (picardIter p u₀ n s)) q.2) :=
      hSg_meas.add hVal
    have hfield :
        (fun q : ℝ × ℝ =>
          intervalDomainLift (picardIter p u₀ (n + 1) q.1) q.2) =
          fun q : ℝ × ℝ =>
            if q.2 ∈ Set.Icc (0 : ℝ) 1 then
              intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2
                + ∫ s in (0 : ℝ)..q.1,
                  intervalFullSemigroupOperator (q.1 - s)
                    (logisticLifted p (picardIter p u₀ n s)) q.2
            else 0 := by
      funext q
      by_cases hy : q.2 ∈ Set.Icc (0 : ℝ) 1
      · simp [picardIter, intervalDomainLift, intervalGradientDuhamelMap, hy, hχ0]
      · simp [intervalDomainLift, hy]
    show Measurable (fun q : ℝ × ℝ =>
      intervalDomainLift (picardIter p u₀ (n + 1) q.1) q.2)
    rw [hfield]
    exact Measurable.ite (measurableSet_Icc.preimage measurable_snd)
      hinside measurable_const

/-! ## §2 — The datum sup bound from the mild initial approach. -/

/-- **`∀ z, |lift u₀ z| ≤ M` from the cone.**  For every subtype point,
`|u₀ y| ≤ |u₀ y − Φ(s) y| + |D.u s y| < ε + M` for small `s > 0` (mild identity +
initial approach + the limit ball); conclude by `ε → 0`.  Off `Icc` the lift is `0`. -/
theorem u₀_lift_abs_le
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hu₀_cont : Continuous u₀)
    (D : GradientMildSolutionData p u₀)
    (hDball : ∀ s, 0 < s → s ≤ D.T → ∀ y : intervalDomainPoint, |D.u s y| ≤ M) :
    ∀ z : ℝ, |intervalDomainLift u₀ z| ≤ M := by
  have hsub : ∀ y : intervalDomainPoint, |u₀ y| ≤ M := by
    intro y
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ :=
      gradientMildSolutionData_initialApproach p hu₀_cont D ε hε
    set s : ℝ := min (δ / 2) D.T with hs_def
    have hspos : 0 < s := lt_min (by linarith) D.hT
    have hsδ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hsT : s ≤ D.T := min_le_right _ _
    have happrox : |intervalGradientDuhamelMap p u₀ D.u s y - u₀ y| < ε :=
      hδ s hspos hsδ y
    have hmild : D.u s y = intervalGradientDuhamelMap p u₀ D.u s y :=
      D.hmild s hspos hsT y
    have hball := hDball s hspos hsT y
    have hdecomp : u₀ y
        = D.u s y - (intervalGradientDuhamelMap p u₀ D.u s y - u₀ y) := by
      rw [hmild]; ring
    rw [hdecomp, sub_eq_add_neg]
    have htri := abs_add_le (D.u s y)
      (-(intervalGradientDuhamelMap p u₀ D.u s y - u₀ y))
    rw [abs_neg] at htri
    exact le_trans htri (by linarith [happrox.le])
  intro z
  by_cases hz : z ∈ Set.Icc (0 : ℝ) 1
  · simpa [intervalDomainLift, hz] using hsub ⟨z, hz⟩
  · simpa [intervalDomainLift, hz] using hM

/-! ## §3 — The windowed source family and its facts. -/

/-- The windowed wiring source family: zero at level `0`; at level `n+1` the
canonical logistic source, time-windowed to `(0, T]`. -/
def wSrc (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (T : ℝ) :
    ℕ → ℝ → ℝ → ℝ
  | 0 => fun _ _ => 0
  | n + 1 => fun s y =>
      if 0 < s ∧ s ≤ T then logisticLifted p (picardIter p u₀ n s) y else 0

/-- Global sup of the windowed family: the window is covered by the cone ball
(`|logisticLifted| ≤ CL p M` via the logistic value bound), the exterior is `0`. -/
theorem wSrc_sup
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {M T : ℝ} (hM : 0 < M)
    (hball : ∀ (n : ℕ) (s : ℝ), 0 < s → s ≤ T → ∀ y : intervalDomainPoint,
      |picardIter p u₀ n s y| ≤ M) :
    ∀ (n : ℕ) (s y : ℝ), |wSrc p u₀ T n s y| ≤ CL p M := by
  have hCL : 0 ≤ CL p M := CL_nonneg hM.le
  intro n s y
  cases n with
  | zero => simpa [wSrc] using hCL
  | succ n =>
    show |if 0 < s ∧ s ≤ T then logisticLifted p (picardIter p u₀ n s) y else 0|
      ≤ CL p M
    by_cases hs : 0 < s ∧ s ≤ T
    · rw [if_pos hs]
      have := ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound
        p hM (fun z => hball n s hs.1 hs.2 z) y
      simpa [CL, logisticLifted] using this
    · rw [if_neg hs]; simpa using hCL

/-- Joint measurability of the windowed family (ite over a measurable time set). -/
theorem wSrc_meas
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (u₀ : intervalDomainPoint → ℝ)
    (hu₀_cont : Continuous u₀) (T : ℝ) :
    ∀ n : ℕ, Measurable (Function.uncurry (wSrc p u₀ T n)) := by
  intro n
  cases n with
  | zero =>
    show Measurable (Function.uncurry (fun _ _ => (0:ℝ)))
    exact measurable_const
  | succ n =>
    have hL_meas :
        Measurable (Function.uncurry
          (fun s y => logisticLifted p (picardIter p u₀ n s) y)) := by
      simpa [Function.uncurry] using
        logisticLifted_joint_measurable'
          (picardIter_hasJointMeasurability_all p hχ0 u₀ hu₀_cont n)
    have hset : MeasurableSet {q : ℝ × ℝ | 0 < q.1 ∧ q.1 ≤ T} := by
      have : {q : ℝ × ℝ | 0 < q.1 ∧ q.1 ≤ T}
          = (fun q : ℝ × ℝ => q.1) ⁻¹' (Set.Ioc (0:ℝ) T) := by
        ext q; simp [Set.mem_Ioc]
      rw [this]
      exact measurableSet_Ioc.preimage measurable_fst
    show Measurable (fun q : ℝ × ℝ =>
      if 0 < q.1 ∧ q.1 ≤ T then logisticLifted p (picardIter p u₀ n q.1) q.2 else 0)
    exact Measurable.ite hset hL_meas measurable_const

/-- Per-slice integrability of the windowed family (sections of the joint
measurability + the global window bound). -/
theorem wSrc_integrable
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (u₀ : intervalDomainPoint → ℝ)
    (hu₀_cont : Continuous u₀) {M T : ℝ} (hM : 0 < M)
    (hball : ∀ (n : ℕ) (s : ℝ), 0 < s → s ≤ T → ∀ y : intervalDomainPoint,
      |picardIter p u₀ n s y| ≤ M) :
    ∀ (n : ℕ) (s : ℝ), Integrable (wSrc p u₀ T n s) (intervalMeasure 1) := by
  intro n s
  have hsec : Measurable (wSrc p u₀ T n s) :=
    (wSrc_meas p hχ0 u₀ hu₀_cont T n).comp measurable_prodMk_left
  exact intervalMeasure_integrable_of_abs_bound
    hsec.aestronglyMeasurable (fun y => wSrc_sup p u₀ hM hball n s y)

/-- **Value `EqOn` for the windowed family.**  The canonical per-level value
identity transfers to `wSrc` because the Duhamel integrand only reads
`s ∈ Ioc 0 t ⊆ (0, T]`, where the two families coincide. -/
theorem wSrc_value_eqOn
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (u₀ : intervalDomainPoint → ℝ)
    {T t : ℝ} (ht : 0 < t) (htT : t ≤ T) (n : ℕ) :
    Set.EqOn (intervalDomainLift (picardIter p u₀ n t))
      (fun z : ℝ => intervalFullSemigroupOperator t (intervalDomainLift u₀) z
        + ∫ s in (0:ℝ)..t,
            intervalFullSemigroupOperator (t - s) (wSrc p u₀ T n s) z)
      (Set.Icc (0:ℝ) 1) := by
  cases n with
  | zero =>
    intro z hz
    exact zero_value_eqOn p u₀ t hz
  | succ n =>
    intro z hz
    have hsucc := succ_value_eqOn p hχ0 u₀ n t hz
    have hcongr : (∫ s in (0:ℝ)..t,
        intervalFullSemigroupOperator (t - s) (wSrc p u₀ T (n + 1) s) z)
        = ∫ s in (0:ℝ)..t,
            intervalFullSemigroupOperator (t - s)
              (logisticLifted p (picardIter p u₀ n s)) z := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with s
      intro hs
      rw [Set.uIoc_of_le ht.le] at hs
      have hwin : 0 < s ∧ s ≤ T := ⟨hs.1, le_trans hs.2 htT⟩
      have hfun : wSrc p u₀ T (n + 1) s
          = logisticLifted p (picardIter p u₀ n s) := by
        funext y
        show (if 0 < s ∧ s ≤ T then logisticLifted p (picardIter p u₀ n s) y else 0)
          = logisticLifted p (picardIter p u₀ n s) y
        rw [if_pos hwin]
      rw [hfun]
    show intervalDomainLift (picardIter p u₀ (n + 1) t) z
        = intervalFullSemigroupOperator t (intervalDomainLift u₀) z
          + ∫ s in (0:ℝ)..t,
              intervalFullSemigroupOperator (t - s) (wSrc p u₀ T (n + 1) s) z
    rw [hcongr]
    exact hsucc

/-! ## §4 — The assembled `hG1all`. -/

/-- `0 ≤ G1profile` (both kernel summands are products of nonnegatives). -/
theorem G1profile_nonneg (p : CM2Params) {M t : ℝ} (hM : 0 ≤ M) (ht : 0 < t) :
    0 ≤ G1profile p M t := by
  have hCg : 0 ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
  have hCL : 0 ≤ CL p M := CL_nonneg hM
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  unfold G1profile
  have h1 : 0 ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
      / Real.sqrt t * M := by positivity
  have h2 : 0 ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
      * (2 * Real.sqrt t) * CL p M := by positivity
  linarith

/-- **The kernel-G1 line, all levels, cone-supplied.**  For every iterate level and
`0 < σ ≤ T`, the lifted spatial derivative is bounded by `G1profile p M σ` at every
real `x`: interior via the windowed split + `g1_kernel_bound`; endpoints and
exterior via the junk-derivative mechanism. -/
theorem hG1all_of_cone
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (u₀ : intervalDomainPoint → ℝ)
    {M T : ℝ} (hM : 0 < M)
    (hu₀_cont : Continuous u₀)
    (hu₀_sup : ∀ z : ℝ, |intervalDomainLift u₀ z| ≤ M)
    (hball : ∀ (n : ℕ) (s : ℝ), 0 < s → s ≤ T → ∀ y : intervalDomainPoint,
      |picardIter p u₀ n s y| ≤ M) :
    ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ T → ∀ x : ℝ,
      |deriv (intervalDomainLift (picardIter p u₀ n σ)) x| ≤ G1profile p M σ := by
  intro n σ hσ hσT x
  have hprof : 0 ≤ G1profile p M σ := G1profile_nonneg p hM.le hσ
  -- off-interior: the junk-derivative mechanism gives `deriv = 0`.
  rcases lt_or_ge x 0 with hx0 | hx0
  · rw [deriv_lift_eq_zero_on_Iio (picardIter p u₀ n) σ hx0]
    simpa using hprof
  rcases lt_or_ge 1 x with hx1 | hx1
  · rw [deriv_lift_eq_zero_on_Ioi (picardIter p u₀ n) σ hx1]
    simpa using hprof
  rcases eq_or_lt_of_le hx0 with hx0e | hx0lt
  · rw [← hx0e, deriv_lift_eq_zero_at_left (picardIter p u₀ n) σ]
    simpa using hprof
  rcases eq_or_lt_of_le hx1 with hx1e | hx1lt
  · rw [hx1e, deriv_lift_eq_zero_at_right (picardIter p u₀ n) σ]
    simpa using hprof
  -- interior: the windowed split feeds the kernel bound.
  have hxIoo : x ∈ Set.Ioo (0:ℝ) 1 := ⟨hx0lt, hx1lt⟩
  have hf_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1) :=
    (intervalDomainLift_measurable_of_continuous' hu₀_cont).aestronglyMeasurable
  have hL_meas := wSrc_meas p hχ0 u₀ hu₀_cont T n
  have hL_sup := fun s y => wSrc_sup p u₀ hM hball n s y
  have hq_int := fun s => wSrc_integrable p hχ0 u₀ hu₀_cont hM hball n s
  have hCL : 0 ≤ CL p M := CL_nonneg hM.le
  have hg_int := gradInterval_integrable hσ hL_meas hCL hL_sup x
  have hsplit := deriv_split_interior_of_eqOn hσ hf_meas hu₀_sup hL_meas hCL hL_sup
    (wSrc_value_eqOn p hχ0 u₀ hσ hσT n) hxIoo
  exact g1_kernel_bound p hσ hσT hM.le hf_meas hu₀_sup hq_int hL_sup x hg_int hsplit

end ShenWork.IntervalPicardG1All
