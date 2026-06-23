/-
  ShenWork/Paper2/IntervalConjugateSourceBridge.lean

  B-form (conjugate) analogue of the gradient mild → term-sum bridge and of the
  χ₀-general cosine-coefficient decomposition.

  * TASK A (`conjugateMildSolution_lift_eq_threeTermMap_on_Icc`): for the
    established conjugate mild solution `conjugatePicardLimit`, its lifted time
    slice agrees on `[0,1]` with the real-variable three-term Duhamel map of
    `intervalConjugateDuhamelMap` (semigroup + B-kernel chemotaxis + logistic).
    This is pure wiring: the established mild property (2) + the definitional
    unfolding of `intervalConjugateDuhamelMap` (1, essentially `rfl`).

  * TASK B (`conjugateSlice_cosineCoeff_decomp`): applies the χ₀-general
    decomposition `gradientSolution_cosineCoeff_decomp_chi` with `χ₀ := p.χ₀`,
    `hmap` from Task A, the per-τ chemotaxis identity supplied by the B-kernel
    cosine-series lemma `intervalConjugateKernelOperator_cosineSeries`, and the
    per-τ logistic identity supplied by the full-semigroup diagonalization
    `cosineCoeffs_intervalFullSemigroupOperator_diag`.  The Fubini swaps and the
    spatial continuity of the two time integrals are carried as explicit
    hypotheses, mirroring the gradient decomposition interface.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New names only.
-/
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalConjugateCosineSeries
import ShenWork.Paper2.IntervalBootstrapDecomp
import ShenWork.Paper2.IntervalGradientCoeffDuhamel
import ShenWork.Paper2.IntervalPicardIterateRestart
import ShenWork.PDE.IntervalSemigroupAtZero

noncomputable section

namespace ShenWork.Paper2.IntervalConjugateSourceBridge

open MeasureTheory
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugatePicard
open ShenWork.Paper2.HSigmaScale (lam)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.IntervalBootstrapDecomp (gradientSolution_cosineCoeff_decomp_chi)
open ShenWork.IntervalConjugateCosineSeries (intervalConjugateKernelOperator_cosineSeries
  intervalSineInner)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalPicardIterateRestart (cosineCoeffs_of_l1_cosineSeries)
open ShenWork.Paper2.IntervalGradientCoeffDuhamel
  (cosineCoeffs_intervalFullSemigroupOperator_diag)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (rpow_half_lam_eq_kpi sineCoeffs_pos)
open Real

/-! ## TASK A — conjugate mild solution lift = three-term map on `[0,1]` -/

/-- The subtype-valued conjugate Duhamel map is exactly the real-variable
three-term map evaluated at the subtype coordinate (definitional). -/
theorem intervalConjugateDuhamelMap_eq_threeTermMap
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) (x : intervalDomainPoint) :
    intervalConjugateDuhamelMap p u₀ u t x =
      (intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
        + (-p.χ₀) * (∫ s in (0 : ℝ)..t,
            intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x.1)
        + ∫ s in (0 : ℝ)..t,
            intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x.1) :=
  rfl

/-- **TASK A.**  For the established conjugate mild solution, the lifted time
slice agrees on `[0,1]` with the real-variable three-term Duhamel map.  Mirrors
`gradientMildSolution_lift_eq_gradientMildMapTermSum_on_Icc`. -/
theorem conjugateMildSolution_lift_eq_threeTermMap_on_Icc
    (p : CM2Params) {T : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hmild : IntervalConjugateMildSolution p T u₀ u)
    {t : ℝ} (ht0 : 0 < t) (htT : t ≤ T) :
    Set.EqOn (intervalDomainLift (u t))
      (fun x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x
        + (-p.χ₀) * (∫ s in (0 : ℝ)..t,
            intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x)
        + ∫ s in (0 : ℝ)..t,
            intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x)
      (Set.Icc (0 : ℝ) 1) := by
  intro x hx
  calc
    intervalDomainLift (u t) x = u t ⟨x, hx⟩ := by
      simp [intervalDomainLift, hx]
    _ = intervalConjugateDuhamelMap p u₀ u t ⟨x, hx⟩ := hmild t ht0 htT ⟨x, hx⟩
    _ = _ := intervalConjugateDuhamelMap_eq_threeTermMap p u₀ u t ⟨x, hx⟩

/-! ## Degenerate-time vanishing of the two source legs -/

/-- The free-space heat kernel vanishes for non-positive time (`√` of a
non-positive argument is `0`). -/
theorem heatKernel_nonpos {τ : ℝ} (hτ : τ ≤ 0) (x : ℝ) : heatKernel τ x = 0 := by
  unfold heatKernel
  have : Real.sqrt (4 * Real.pi * τ) = 0 :=
    Real.sqrt_eq_zero_of_nonpos (by nlinarith [Real.pi_pos])
  rw [this]; simp

/-- The periodised Neumann kernel vanishes for non-positive time. -/
theorem intervalNeumannFullKernel_nonpos {τ : ℝ} (hτ : τ ≤ 0) (x y : ℝ) :
    ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel τ x y = 0 := by
  unfold ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel
  simp [heatKernel_nonpos hτ]

/-- The B-kernel chemotaxis operator vanishes for non-positive time. -/
theorem intervalConjugateKernelOperator_nonpos {τ : ℝ} (hτ : τ ≤ 0)
    (g : ℝ → ℝ) (x : ℝ) : intervalConjugateKernelOperator τ g x = 0 := by
  unfold intervalConjugateKernelOperator
  have h : ∀ y : ℝ, deriv (fun y' : ℝ =>
      ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel τ x y') y * g y = 0 := by
    intro y
    have hk : (fun y' : ℝ =>
        ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel τ x y') = fun _ => 0 :=
      funext fun y' => intervalNeumannFullKernel_nonpos hτ x y'
    rw [hk]; simp
  simp only [h]; simp

/-- The full semigroup propagator vanishes for non-positive time. -/
theorem intervalFullSemigroupOperator_nonpos {τ : ℝ} (hτ : τ ≤ 0)
    (f : ℝ → ℝ) (x : ℝ) : intervalFullSemigroupOperator τ f x = 0 := by
  unfold intervalFullSemigroupOperator
  have h : ∀ y : ℝ,
      ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel τ x y * f y = 0 := by
    intro y; rw [intervalNeumannFullKernel_nonpos hτ x y]; simp
  simp only [h]; simp

/-- `cosineCoeffs` of the zero function vanishes. -/
theorem cosineCoeffs_zero_fun (k : ℕ) : cosineCoeffs (fun _ : ℝ => (0 : ℝ)) k = 0 := by
  rw [ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral]; simp

/-- `sineCoeffs` of the zero function vanishes. -/
theorem sineCoeffs_zero_fun (k : ℕ) : sineCoeffs (fun _ : ℝ => (0 : ℝ)) k = 0 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · simp [sineCoeffs, hk]
  · rw [sineCoeffs_pos hk.ne']; simp

/-! ## Per-τ kernel identities (positive elapsed time) -/

/-- Uniform `2C` bound on the sine pairing of a function bounded by `C` on `[0,1]`. -/
theorem intervalSineInner_abs_le {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ}
    (hC : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖g x‖ ≤ C) (hC0 : 0 ≤ C) (n : ℕ) :
    |intervalSineInner g n| ≤ 2 * C := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp only [intervalSineInner, if_pos hn, abs_zero]; positivity
  · rw [intervalSineInner, if_neg hn.ne', abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc |∫ y in (0 : ℝ)..1, Real.sin ((n : ℝ)*Real.pi*y) * g y|
        ≤ ∫ y in (0 : ℝ)..1, |Real.sin ((n : ℝ)*Real.pi*y) * g y| :=
          intervalIntegral.abs_integral_le_integral_abs (by norm_num)
      _ ≤ ∫ _y in (0 : ℝ)..1, C := by
          apply intervalIntegral.integral_mono_on (by norm_num)
          · exact ((Real.continuous_sin.comp (by fun_prop)).mul
              hg).abs.intervalIntegrable 0 1
          · exact intervalIntegrable_const
          · intro y hy
            rw [abs_mul]
            calc |Real.sin ((n : ℝ)*Real.pi*y)| * |g y| ≤ 1 * C :=
                  mul_le_mul (Real.abs_sin_le_one _) (hC y hy) (abs_nonneg _) zero_le_one
              _ = C := one_mul C
      _ = C := by simp

/-- Summability of the B-kernel cosine-series coefficients (positive time). -/
theorem conjugateKernel_coeff_summable {τ : ℝ} (hτ : 0 < τ) {g : ℝ → ℝ}
    (hg : Continuous g) :
    Summable (fun n : ℕ => |Real.exp (-τ * unitIntervalCosineEigenvalue n) *
        (((n : ℝ) * Real.pi) * intervalSineInner g n)|) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (hg.continuousOn (s := Set.Icc (0 : ℝ) 1))
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (g 0)) (hC 0 ⟨le_refl 0, by norm_num⟩)
  have hsi := intervalSineInner_abs_le hg hC hC0
  have hmaj : Summable (fun n : ℕ => (2 * C) * (((n : ℝ) * Real.pi) *
      Real.exp (-τ * unitIntervalCosineEigenvalue n))) := by
    have hbase : Summable (fun n : ℕ =>
        Real.pi * ((n : ℝ) ^ 1 * Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ)))) :=
      (Real.summable_pow_mul_exp_neg_nat_mul 1 (by positivity)).mul_left Real.pi
    have hkey : Summable (fun n : ℕ =>
        ((n : ℝ) * Real.pi) * Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by
      refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hbase
      have hnle : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · simp [hn]
        · exact le_self_pow₀ (Nat.one_le_cast.2 hn) (by norm_num)
      calc ((n : ℝ) * Real.pi) * Real.exp (-τ * unitIntervalCosineEigenvalue n)
          = Real.pi * ((n : ℝ) ^ 1 *
              Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ) ^ 2)) := by
              simp only [unitIntervalCosineEigenvalue]; ring_nf
        _ ≤ Real.pi * ((n : ℝ) ^ 1 *
              Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ))) := by
              apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply Real.exp_le_exp_of_le
              nlinarith [mul_le_mul_of_nonneg_left hnle
                (by positivity : (0 : ℝ) ≤ τ * Real.pi ^ 2)]
    exact hkey.mul_left (2 * C)
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) hmaj
  rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _), abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) * Real.pi),
    show (2 * C) * (((n : ℝ) * Real.pi) *
      Real.exp (-τ * unitIntervalCosineEigenvalue n))
      = Real.exp (-τ * unitIntervalCosineEigenvalue n) *
        (((n : ℝ) * Real.pi) * (2 * C)) by ring]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  exact mul_le_mul_of_nonneg_left (hsi n) (by positivity)

/-- **Per-τ B-kernel cosine identity (positive elapsed time).**  Mirrors the
gradient `cosineCoeffs_semigroup_deriv_eq_diag_sqrtLambda_sineCoeff`. -/
theorem conjugateKernel_cosineCoeff {τ : ℝ} (hτ : 0 < τ) {g : ℝ → ℝ}
    (hg : Continuous g) (k : ℕ) :
    cosineCoeffs (fun x => intervalConjugateKernelOperator τ g x) k
      = Real.exp (-(1 * lam k * τ)) * ((lam k) ^ (1/2 : ℝ) * sineCoeffs g k) := by
  have hseries : (fun x => intervalConjugateKernelOperator τ g x)
      = fun x => ∑' n : ℕ,
          (Real.exp (-τ * unitIntervalCosineEigenvalue n) *
            (((n : ℝ) * Real.pi) * intervalSineInner g n)) * cosineMode n x :=
    funext fun x => intervalConjugateKernelOperator_cosineSeries hτ hg x
  rw [hseries, cosineCoeffs_of_l1_cosineSeries (conjugateKernel_coeff_summable hτ hg) k]
  have hsi : intervalSineInner g k = sineCoeffs g k := by
    unfold intervalSineInner sineCoeffs; rfl
  rw [(rfl : unitIntervalCosineEigenvalue k = lam k), hsi,
    (rpow_half_lam_eq_kpi k).symm, show (-τ * lam k) = (-(1 * lam k * τ)) by ring]

/-- **Per-τ logistic semigroup cosine identity (positive elapsed time, `k ≠ 0`).**
The `√λ`-stripped logistic source `Fl k s = cosineCoeffs (...) k / √λ_k`. -/
theorem conjugateLog_cosineCoeff {τ : ℝ} (hτ : 0 < τ) {f : ℝ → ℝ}
    (hf : Continuous f) {M : ℝ} (hM : ∀ j, |cosineCoeffs f j| ≤ M)
    {k : ℕ} (hk : k ≠ 0) :
    cosineCoeffs (fun x => intervalFullSemigroupOperator τ f x) k
      = (lam k) ^ (1/2 : ℝ) * Real.exp (-(1 * lam k * τ)) *
          (cosineCoeffs f k / (lam k) ^ (1/2 : ℝ)) := by
  rw [cosineCoeffs_intervalFullSemigroupOperator_diag hτ hf hM k]
  have hpos : (0 : ℝ) < (lam k) ^ (1/2 : ℝ) := by
    rw [rpow_half_lam_eq_kpi k]
    have : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    positivity
  rw [show (-τ * lam k) = (-(1 * lam k * τ)) by ring]
  field_simp

/-! ## TASK B — the conjugate per-mode kernel decomposition -/

/-- **TASK B — the conjugate-slice cosine-coefficient decomposition.**

For the established conjugate mild solution `u`, the `k`-th cosine coefficient
(`k ≠ 0`) of the lifted slice decomposes as the heat diagonal plus the two engine
coefficients, exactly the shape `gradientSolution_memHSigma_succ_wired` consumes
with `χc = p.χ₀`, `χL = -1`.

The chemotaxis/logistic sources are the elapsed-time-aware families
`Qsrc s = if s < t then chemFluxLifted p (u s) else 0` and
`Flsrc k s = if s < t then cosineCoeffs (logisticLifted p (u s)) k / √λ_k else 0`;
the `s = t` (and `s > t`) guard records that both source legs of the Duhamel map
vanish at non-positive elapsed time, which is exactly where the positive-time
per-τ identities cannot reach.  The Fubini swaps and the spatial continuity of the
two time integrals are carried as explicit hypotheses, mirroring the gradient
decomposition interface. -/
theorem conjugateSlice_cosineCoeff_decomp
    (p : CM2Params) {T : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hmild : IntervalConjugateMildSolution p T u₀ u)
    {t : ℝ} (ht0 : 0 < t) (htT : t ≤ T) {k : ℕ} (hk : k ≠ 0)
    -- continuity of the flux/logistic slices along the trajectory (s < t)
    (hQcont : ∀ s, s < t → Continuous (chemFluxLifted p (u s)))
    (hLcont : ∀ s, s < t → Continuous (logisticLifted p (u s)))
    {Ml : ℝ} (hLM : ∀ s, s < t → ∀ j,
      |cosineCoeffs (logisticLifted p (u s)) j| ≤ Ml)
    -- spatial continuity of the three map summands (carried, as in the gradient interface)
    (hheat_cont : Continuous
      (fun x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x))
    (hchemI_cont : Continuous (fun x => ∫ s in (0 : ℝ)..t,
      intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x))
    (hlogI_cont : Continuous (fun x => ∫ s in (0 : ℝ)..t,
      intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x))
    -- heat diagonalization for the homogeneous propagator
    (hpt_heat : cosineCoeffs
      (fun x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x) k
        = Real.exp (-(t * lam k)) * cosineCoeffs (intervalDomainLift u₀) k)
    -- Fubini swaps (cosineCoeffs ↔ time integral), as in the gradient decomp
    (hswap_chem : cosineCoeffs (fun x => ∫ s in (0 : ℝ)..t,
        intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x) k
      = ∫ s in (0 : ℝ)..t, cosineCoeffs
        (fun x => intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x) k)
    (hswap_log : cosineCoeffs (fun x => ∫ s in (0 : ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x) k
      = ∫ s in (0 : ℝ)..t, cosineCoeffs
        (fun x => intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x) k) :
    cosineCoeffs (intervalDomainLift (u t)) k
      = Real.exp (-(t * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
        + (-p.χ₀) * duhamelEnergyCoeff 1
            (fun j s => sineCoeffs
              (if s < t then chemFluxLifted p (u s) else fun _ => 0) j) t k
        + duhamelEnergyCoeff 1
            (fun j s => if s < t
              then cosineCoeffs (logisticLifted p (u s)) j / (lam j) ^ (1/2 : ℝ)
              else 0) t k := by
  -- the per-τ chemotaxis identity, endpoint-aware
  have hpt_chem : ∀ s, cosineCoeffs
      (fun x => intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x) k
      = Real.exp (-(1 * lam k * (t - s))) * ((lam k) ^ (1/2 : ℝ)
          * sineCoeffs (if s < t then chemFluxLifted p (u s) else fun _ => 0) k) := by
    intro s
    by_cases hs : s < t
    · rw [if_pos hs]
      exact conjugateKernel_cosineCoeff (by linarith) (hQcont s hs) k
    · rw [if_neg hs]
      have hts : t - s ≤ 0 := by linarith [not_lt.1 hs]
      rw [show (fun x => intervalConjugateKernelOperator (t - s)
            (chemFluxLifted p (u s)) x) = fun _ => (0 : ℝ) from
        funext fun x => intervalConjugateKernelOperator_nonpos hts _ x,
        cosineCoeffs_zero_fun, sineCoeffs_zero_fun]; ring
  -- the per-τ logistic identity, endpoint-aware
  have hpt_log : ∀ s, cosineCoeffs
      (fun x => intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x) k
      = (lam k) ^ (1/2 : ℝ) * Real.exp (-(1 * lam k * (t - s)))
          * (if s < t then cosineCoeffs (logisticLifted p (u s)) k / (lam k) ^ (1/2 : ℝ)
              else 0) := by
    intro s
    by_cases hs : s < t
    · rw [if_pos hs]
      exact conjugateLog_cosineCoeff (by linarith) (hLcont s hs) (hLM s hs) hk
    · rw [if_neg hs]
      have hts : t - s ≤ 0 := by linarith [not_lt.1 hs]
      rw [show (fun x => intervalFullSemigroupOperator (t - s)
            (logisticLifted p (u s)) x) = fun _ => (0 : ℝ) from
        funext fun x => intervalFullSemigroupOperator_nonpos hts _ x,
        cosineCoeffs_zero_fun]; ring
  -- feed Task A's three-term EqOn + the per-τ identities through decomp_chi
  exact gradientSolution_cosineCoeff_decomp_chi (χ₀ := p.χ₀) k
    (conjugateMildSolution_lift_eq_threeTermMap_on_Icc p hmild ht0 htT)
    hheat_cont hchemI_cont hlogI_cont hpt_heat hswap_chem hpt_chem hswap_log hpt_log

end ShenWork.Paper2.IntervalConjugateSourceBridge
