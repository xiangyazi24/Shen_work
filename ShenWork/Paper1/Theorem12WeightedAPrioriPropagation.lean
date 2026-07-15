import ShenWork.Paper1.Theorem12WeightedResolverEta
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open Filter MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Crude weighted-energy propagation

This file isolates the non-circular exhaustion step in the weighted a-priori
argument.  A bound for the energy on every compact spatial window implies
integrability on the whole line; no whole-line integral is used before its
integrability has been established.
-/

/-- The moving-frame weighted error density. -/
def movingFrameWeightedErrorDensity
    (eta c : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ)
    (t x : ℝ) : ℝ :=
  Real.exp (2 * eta * x) * |coMovingPath c u t x - U x| ^ 2

theorem movingFrameWeightedErrorDensity_nonneg
    (eta c : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ)
    (t x : ℝ) :
    0 ≤ movingFrameWeightedErrorDensity eta c u U t x := by
  exact mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)

theorem movingFrameWeightedErrorDensity_continuous
    {eta c t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hu : PaperCUnifBdd (coMovingPath c u t))
    (hU : PaperCUnifBdd U) :
    Continuous (movingFrameWeightedErrorDensity eta c u U t) := by
  unfold movingFrameWeightedErrorDensity
  exact
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      ((hu.1.continuous.sub hU.1.continuous).abs.pow 2)

/-- Every canonical global slice remains in the paper's genuine BUC class
after translation to the moving frame. -/
theorem wholeLineCauchyGlobal_coMoving_slice_paperCUnifBdd
    (p : CMParams) (u0 : WholeLineBUC) (c t : ℝ) :
    PaperCUnifBdd (coMovingPath c (wholeLineCauchyGlobalU p u0) t) := by
  have hs : UniformContinuous (wholeLineCauchyGlobalU p u0 t) :=
    (wholeLineCauchyGlobalBUC p u0 t).2
  have hshift : UniformContinuous (fun x : ℝ => x + c * t) :=
    uniformContinuous_id.add uniformContinuous_const
  refine ⟨hs.comp hshift, ?_⟩
  exact (wholeLineCauchyGlobal_coMoving_slice_isCUnifBdd p u0 c t).2

/-- The symmetric compact intervals exhaust the whole real line. -/
theorem movingFrameEnergy_Icc_aecover :
    AECover (volume : Measure ℝ) atTop
      (fun n : ℕ => Set.Icc (-(n : ℝ)) (n : ℝ)) := by
  apply aecover_Icc
  · exact tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  · exact tendsto_natCast_atTop_atTop

/-- Finite-time scalar Grönwall estimate with an arbitrary growth constant.
No sign condition on `C` is required. -/
theorem scalarEnergy_crude_exponential_bound
    {E : ℝ → ℝ} {C t : ℝ} (ht : 0 ≤ t)
    (hcont : ContinuousOn E (Set.Icc 0 t))
    (hderiv : ∀ s ∈ Set.Ico (0 : ℝ) t,
      HasDerivWithinAt E (deriv E s) (Set.Ici s) s)
    (hgrowth : ∀ s ∈ Set.Ico (0 : ℝ) t,
      deriv E s ≤ C * E s) :
    E t ≤ E 0 * Real.exp (C * t) := by
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) t,
      deriv E s ≤ C * E s + 0 := by
    intro s hs
    simpa using hgrowth s hs
  have hgronwall := le_gronwallBound_of_liminf_deriv_right_le
    (f := E) (f' := fun s => deriv E s)
    (δ := E 0) (K := C) (ε := 0) (a := 0) (b := t)
    hcont (fun s hs r hr => (hderiv s hs).liminf_right_slope_le hr)
    (le_refl _) hbound t ⟨ht, le_rfl⟩
  have hformula : gronwallBound (E 0) C 0 (t - 0) =
      E 0 * Real.exp (C * (t - 0)) := by
    rw [gronwallBound_ε0]
  rw [hformula] at hgronwall
  simpa using hgronwall

/-- A homogeneous scalar growth estimate cannot create energy from a zero
initial value.  This is the obstruction met by a genuinely compact spatial
cutoff: a perturbation initially outside the cutoff may enter it at positive
time, whereas `E' \le C E` would force the localized energy to stay zero. -/
theorem scalarEnergy_eq_zero_of_zero_initial
    {E : ℝ → ℝ} {C t : ℝ} (ht : 0 ≤ t)
    (hzero : E 0 = 0) (hnonneg : ∀ s, 0 ≤ E s)
    (hcont : ContinuousOn E (Set.Icc 0 t))
    (hderiv : ∀ s ∈ Set.Ico (0 : ℝ) t,
      HasDerivWithinAt E (deriv E s) (Set.Ici s) s)
    (hgrowth : ∀ s ∈ Set.Ico (0 : ℝ) t,
      deriv E s ≤ C * E s) :
    E t = 0 := by
  have hle := scalarEnergy_crude_exponential_bound ht hcont hderiv hgrowth
  rw [hzero, zero_mul] at hle
  exact le_antisymm hle (hnonneg t)

/-- A nonnegative cutoff which vanishes to the right cannot have its spatial
derivative bounded by a fixed multiple of itself unless it is identically
zero.  Thus the boundary term from integration by parts for a nontrivial
compact cutoff cannot be absorbed into that same cutoff energy with a
cutoff-radius-uniform constant.

This is a purely scalar consequence of Grönwall, recorded here because it is
the exact obstruction to replacing the positive-time whole-line resolver
estimate by a compactly supported homogeneous estimate. -/
theorem compactCutoff_eq_zero_of_logDerivative_bound
    {chi : ℝ → ℝ} {K R : ℝ}
    (hchi_nonneg : ∀ x, 0 ≤ chi x)
    (hchi_cont : Continuous chi)
    (hchi_deriv : ∀ x, HasDerivAt chi (deriv chi x) x)
    (hlog : ∀ x, |deriv chi x| ≤ K * chi x)
    (hsupport : ∀ x, R ≤ x → chi x = 0) :
    chi = 0 := by
  funext x
  by_cases hx : R ≤ x
  · simpa using hsupport x hx
  · let E : ℝ → ℝ := fun s => chi (R - s)
    let T : ℝ := R - x
    have hxR : x ≤ R := (lt_of_not_ge hx).le
    have hT : 0 ≤ T := by
      simpa [T] using sub_nonneg.mpr hxR
    have hcont : ContinuousOn E (Set.Icc 0 T) :=
      (hchi_cont.comp (continuous_const.sub continuous_id)).continuousOn
    have hEat (s : ℝ) :
        HasDerivAt E (-deriv chi (R - s)) s := by
      have hinner : HasDerivAt (fun r : ℝ => R - r) (-1) s := by
        simpa using (hasDerivAt_const s R).sub (hasDerivAt_id s)
      dsimp only [E]
      simpa using (hchi_deriv (R - s)).comp s hinner
    have hderiv : ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt E (deriv E s) (Set.Ici s) s := by
      intro s _hs
      have hs := hEat s
      rw [hs.deriv]
      exact hs.hasDerivWithinAt
    have hgrowth : ∀ s ∈ Set.Ico (0 : ℝ) T,
        deriv E s ≤ K * E s := by
      intro s _hs
      have hs := hEat s
      rw [hs.deriv]
      calc
        -deriv chi (R - s) ≤ |deriv chi (R - s)| := neg_le_abs _
        _ ≤ K * chi (R - s) := hlog (R - s)
        _ = K * E s := rfl
    have hbound := scalarEnergy_crude_exponential_bound
      hT hcont hderiv hgrowth
    have hEzero : E 0 = 0 := by
      dsimp only [E]
      simpa using hsupport R le_rfl
    have hET : E T = chi x := by
      dsimp only [E, T]
      congr 1
      ring
    rw [hET, hEzero, zero_mul] at hbound
    exact le_antisymm hbound (hchi_nonneg x)

/-- An exhaustion by honest finite cutoff energies produces the compact-window
estimate consumed by
`movingFrameWeightedError_propagation_of_crudeIccEstimate`.

`cutoffEnergy n` may be any smooth spatially localized energy.  The PDE layer
has to prove its continuity, right derivative, growth inequality, initial
comparison, and domination of the `n`th symmetric window.
-/
theorem movingFrameWeightedError_Icc_bound_of_cutoffEnergy
    {eta c C : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (cutoffEnergy : ℕ → ℝ → ℝ)
    (hinitial : ∀ n,
      cutoffEnergy n 0 ≤
        ∫ x, movingFrameWeightedErrorDensity eta c u U 0 x)
    (hcont : ∀ n T, 0 ≤ T →
      ContinuousOn (cutoffEnergy n) (Set.Icc 0 T))
    (hderiv : ∀ n T, 0 ≤ T → ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (cutoffEnergy n)
        (deriv (cutoffEnergy n) s) (Set.Ici s) s)
    (hgrowth : ∀ n s, 0 ≤ s →
      deriv (cutoffEnergy n) s ≤ C * cutoffEnergy n s)
    (hwindow : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
      ∫ x in Set.Icc (-(n : ℝ)) (n : ℝ),
          movingFrameWeightedErrorDensity eta c u U t x ≤
        cutoffEnergy n t) :
    ∀ t, 0 ≤ t → ∀ n : ℕ,
      ∫ x in Set.Icc (-(n : ℝ)) (n : ℝ),
        movingFrameWeightedErrorDensity eta c u U t x ≤
          (∫ x, movingFrameWeightedErrorDensity eta c u U 0 x) *
            Real.exp (C * t) := by
  intro t ht n
  have hscalar : cutoffEnergy n t ≤
      cutoffEnergy n 0 * Real.exp (C * t) := by
    apply scalarEnergy_crude_exponential_bound ht (hcont n t ht)
      (hderiv n t ht)
    intro s hs
    exact hgrowth n s hs.1
  calc
    (∫ x in Set.Icc (-(n : ℝ)) (n : ℝ),
        movingFrameWeightedErrorDensity eta c u U t x) ≤
        cutoffEnergy n t := hwindow n t ht
    _ ≤ cutoffEnergy n 0 * Real.exp (C * t) := hscalar
    _ ≤ (∫ x, movingFrameWeightedErrorDensity eta c u U 0 x) *
          Real.exp (C * t) :=
      mul_le_mul_of_nonneg_right (hinitial n) (Real.exp_nonneg _)

/-- A uniform finite-window energy bound gives whole-line integrability.

The right side is deliberately an arbitrary finite real number.  In the
PDE application it is the initial energy times `exp (C * t)`.
-/
theorem movingFrameWeightedError_integrable_of_Icc_energy_bound
    {eta c t B : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hu : PaperCUnifBdd (coMovingPath c u t))
    (hU : PaperCUnifBdd U)
    (hbound : ∀ n : ℕ,
      ∫ x in Set.Icc (-(n : ℝ)) (n : ℝ),
        movingFrameWeightedErrorDensity eta c u U t x ≤ B) :
    Integrable (movingFrameWeightedErrorDensity eta c u U t) := by
  let phi : ℕ → Set ℝ := fun n => Set.Icc (-(n : ℝ)) (n : ℝ)
  have hcontinuous :
      Continuous (movingFrameWeightedErrorDensity eta c u U t) :=
    movingFrameWeightedErrorDensity_continuous hu hU
  have hlocal : ∀ n, IntegrableOn
      (movingFrameWeightedErrorDensity eta c u U t) (phi n) volume := by
    intro n
    exact hcontinuous.integrableOn_Icc
  have hnonneg : ∀ᵐ x : ℝ ∂volume,
      0 ≤ movingFrameWeightedErrorDensity eta c u U t x :=
    Filter.Eventually.of_forall fun x =>
      movingFrameWeightedErrorDensity_nonneg eta c u U t x
  apply movingFrameEnergy_Icc_aecover.integrable_of_integral_bounded_of_nonneg_ae
    B hlocal hnonneg
  exact Filter.Eventually.of_forall hbound

/-- The same exhaustion argument also recovers the global energy estimate
after integrability has been proved. -/
theorem movingFrameWeightedError_integral_le_of_Icc_energy_bound
    {eta c t B : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hu : PaperCUnifBdd (coMovingPath c u t))
    (hU : PaperCUnifBdd U)
    (hbound : ∀ n : ℕ,
      ∫ x in Set.Icc (-(n : ℝ)) (n : ℝ),
        movingFrameWeightedErrorDensity eta c u U t x ≤ B) :
    (∫ x, movingFrameWeightedErrorDensity eta c u U t x) ≤ B := by
  have hint : Integrable (movingFrameWeightedErrorDensity eta c u U t) :=
    movingFrameWeightedError_integrable_of_Icc_energy_bound hu hU hbound
  have htendsto := movingFrameEnergy_Icc_aecover.integral_tendsto_of_countably_generated
    hint
  apply le_of_tendsto htendsto
  exact Filter.Eventually.of_forall hbound

/-- Abstract crude propagation from a finite-window a-priori estimate.

Unlike a hypothesis asserting integrability at positive times, `hcrude`
only bounds ordinary integrals on compact windows, where continuity already
guarantees integrability.  Thus this statement is suitable for the cutoff
energy estimate produced directly from the PDE.
-/
theorem movingFrameWeightedError_propagation_of_crudeIccEstimate
    {eta c C : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hU : PaperCUnifBdd U)
    (hu : ∀ t, PaperCUnifBdd (coMovingPath c u t))
    (hseed : Integrable (movingFrameWeightedErrorDensity eta c u U 0))
    (hcrude : ∀ t, 0 < t → ∀ n : ℕ,
      ∫ x in Set.Icc (-(n : ℝ)) (n : ℝ),
        movingFrameWeightedErrorDensity eta c u U t x ≤
          (∫ x, movingFrameWeightedErrorDensity eta c u U 0 x) *
            Real.exp (C * t)) :
    ∀ t, 0 ≤ t →
      Integrable (movingFrameWeightedErrorDensity eta c u U t) ∧
      (∫ x, movingFrameWeightedErrorDensity eta c u U t x) ≤
        (∫ x, movingFrameWeightedErrorDensity eta c u U 0 x) *
          Real.exp (C * t) := by
  intro t ht
  rcases ht.eq_or_lt with rfl | ht
  · refine ⟨hseed, ?_⟩
    simp
  · have hwindow := hcrude t ht
    exact ⟨movingFrameWeightedError_integrable_of_Icc_energy_bound
        (hu t) hU hwindow,
      movingFrameWeightedError_integral_le_of_Icc_energy_bound
        (hu t) hU hwindow⟩

/-- Specialization of the cutoff-energy bridge to the canonical global Cauchy
solution and its already-proved time-zero weighted seed.

The spatial cutoff and its PDE estimate remain explicit parameters.  In
particular, this theorem does not assume weighted integrability, or even a
whole-line weighted-energy bound, at a positive time.
-/
theorem wholeLineCauchyGlobal_weightedError_propagation_of_cutoffEnergy
    (p : CMParams) (u0 : WholeLineBUC) (eta c C M : ℝ) (U : ℝ → ℝ)
    (hU : PaperCUnifBdd U)
    (hclose : WeightedL2InitialCloseness eta u0.1 U)
    (hceiling : ∀ t, 0 ≤ t → ∀ x,
      coMovingPath c (wholeLineCauchyGlobalU p u0) t x ∈
        Set.Icc (0 : ℝ) M)
    (cutoffEnergy : ℕ → ℝ → ℝ)
    (hinitial : ∀ n,
      cutoffEnergy n 0 ≤
        ∫ x, movingFrameWeightedErrorDensity eta c
          (wholeLineCauchyGlobalU p u0) U 0 x)
    (hcont : ∀ n T, 0 ≤ T →
      ContinuousOn (cutoffEnergy n) (Set.Icc 0 T))
    (hderiv : ∀ n T, 0 ≤ T → ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (cutoffEnergy n)
        (deriv (cutoffEnergy n) s) (Set.Ici s) s)
    (hgrowth : ∀ n s, 0 ≤ s →
      (∀ x, coMovingPath c (wholeLineCauchyGlobalU p u0) s x ∈
        Set.Icc (0 : ℝ) M) →
      deriv (cutoffEnergy n) s ≤ C * cutoffEnergy n s)
    (hwindow : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
      ∫ x in Set.Icc (-(n : ℝ)) (n : ℝ),
          movingFrameWeightedErrorDensity eta c
            (wholeLineCauchyGlobalU p u0) U t x ≤
        cutoffEnergy n t) :
    ∀ t, 0 ≤ t →
      Integrable (fun x => Real.exp (2 * eta * x) *
        |coMovingPath c (wholeLineCauchyGlobalU p u0) t x - U x| ^ 2) ∧
      (∫ x, Real.exp (2 * eta * x) *
        |coMovingPath c (wholeLineCauchyGlobalU p u0) t x - U x| ^ 2) ≤
        (∫ x, Real.exp (2 * eta * x) *
          |coMovingPath c (wholeLineCauchyGlobalU p u0) 0 x - U x| ^ 2) *
          Real.exp (C * t) := by
  have hseed : Integrable (movingFrameWeightedErrorDensity eta c
      (wholeLineCauchyGlobalU p u0) U 0) := by
    change Integrable (fun x => Real.exp (2 * eta * x) *
      |coMovingPath c (wholeLineCauchyGlobalU p u0) 0 x - U x| ^ 2)
    exact wholeLineCauchyGlobal_weightedInitialCloseness
      p u0 eta c U hclose
  have hIcc := movingFrameWeightedError_Icc_bound_of_cutoffEnergy
    cutoffEnergy hinitial hcont hderiv
    (fun n s hs => hgrowth n s hs (hceiling s hs)) hwindow
  have hprop := movingFrameWeightedError_propagation_of_crudeIccEstimate hU
    (fun t => wholeLineCauchyGlobal_coMoving_slice_paperCUnifBdd p u0 c t)
    hseed (fun t _ht n => hIcc t (le_of_lt _ht) n)
  intro t ht
  exact hprop t ht

section Theorem12WeightedAPrioriPropagationAxiomAudit

#print axioms scalarEnergy_crude_exponential_bound
#print axioms scalarEnergy_eq_zero_of_zero_initial
#print axioms compactCutoff_eq_zero_of_logDerivative_bound
#print axioms movingFrameWeightedError_Icc_bound_of_cutoffEnergy
#print axioms movingFrameWeightedError_integrable_of_Icc_energy_bound
#print axioms movingFrameWeightedError_integral_le_of_Icc_energy_bound
#print axioms movingFrameWeightedError_propagation_of_crudeIccEstimate
#print axioms wholeLineCauchyGlobal_coMoving_slice_paperCUnifBdd
#print axioms
  wholeLineCauchyGlobal_weightedError_propagation_of_cutoffEnergy

end Theorem12WeightedAPrioriPropagationAxiomAudit

end ShenWork.Paper1
