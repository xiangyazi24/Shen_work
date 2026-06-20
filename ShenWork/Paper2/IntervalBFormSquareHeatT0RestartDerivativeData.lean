import ShenWork.Paper2.IntervalBFormSquareHeatT0Restart
import ShenWork.PDE.IntervalDuhamelRepresentation
import ShenWork.PDE.IntervalFullKernelSpectralClean
import ShenWork.PDE.IntervalFullSemigroupNeumann
import ShenWork.PDE.IntervalSemigroupNeumann

open Filter Topology Set

open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData conjugatePicardLimit)

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- Positive-time time differentiability of the full interval semigroup at all
closed interval points, transported from the cosine spectral form. -/
private theorem intervalFullSemigroupOperator_time_hasDerivAt_laplacian_Icc
    {σ x : ℝ} (hσ : 0 < σ) {f : ℝ → ℝ} (hf : Continuous f)
    {K : ℝ} (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun r : ℝ => intervalFullSemigroupOperator r f x)
      (ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianValue
        σ (cosineCoeffs f) x) σ := by
  have hcos :
      HasDerivAt
        (fun r : ℝ => unitIntervalCosineHeatValue r (cosineCoeffs f) x)
        (ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianValue
          σ (cosineCoeffs f) x) σ :=
    ShenWork.RegularityBootstrap.unitIntervalCosineHeatValue_hasTimeDerivAt_of_l2
      (t := σ) (x := x) hσ hl2
  refine hcos.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hσ] with r hr
  exact
    ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
      (t := r) hr (f := f) hf (M := K) hK hx

private theorem intervalFullSemigroupOperator_time_shift_hasDerivAt_laplacian
    {τ s x : ℝ} (hτs : 0 < τ + s) {f : ℝ → ℝ} (hf : Continuous f)
    {K : ℝ} (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun r : ℝ => intervalFullSemigroupOperator (τ + r) f x)
      (ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianValue
        (τ + s) (cosineCoeffs f) x) s := by
  have hbase :=
    intervalFullSemigroupOperator_time_hasDerivAt_laplacian_Icc
      (σ := τ + s) (x := x) hτs hf hK hl2 hx
  have hshift : HasDerivAt (fun r : ℝ => τ + r) (1 : ℝ) s := by
    simpa using (hasDerivAt_const (x := s) (c := τ)).add (hasDerivAt_id s)
  simpa using hbase.comp s hshift

private theorem intervalFullSemigroupOperator_time_shift_hasDerivAt_deriv
    {τ s x : ℝ} (hτs : 0 < τ + s) {f : ℝ → ℝ} (hf : Continuous f)
    {K : ℝ} (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun r : ℝ => intervalFullSemigroupOperator (τ + r) f x)
      (deriv (fun r : ℝ => intervalFullSemigroupOperator (τ + r) f x) s) s := by
  have h :=
    intervalFullSemigroupOperator_time_shift_hasDerivAt_laplacian
      (τ := τ) (s := s) (x := x) hτs hf hK hl2 hx
  simpa [h.deriv] using h

private theorem intervalFullSemigroupOperator_space_hasDerivAt_deriv
    {t x : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f)
    {K : ℝ} (hK : ∀ n, |cosineCoeffs f n| ≤ K) :
    HasDerivAt (fun y : ℝ => intervalFullSemigroupOperator t f y)
      (deriv (fun y : ℝ => intervalFullSemigroupOperator t f y) x) x := by
  have hC2 :
      ContDiff ℝ 2 (fun y : ℝ => intervalFullSemigroupOperator t f y) :=
    ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_contDiff_two_clean
      ht hf hK
  exact ((hC2.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)) x).hasDerivAt

private theorem intervalFullSemigroupOperator_space_second_hasDerivAt_deriv
    {t x : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f)
    {K : ℝ} (hK : ∀ n, |cosineCoeffs f n| ≤ K) :
    HasDerivAt
      (fun y : ℝ =>
        deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) y)
      (deriv (fun y : ℝ =>
        deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) y) x) x := by
  have hC2 :
      ContDiff ℝ 2 (fun y : ℝ => intervalFullSemigroupOperator t f y) :=
    ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_contDiff_two_clean
      ht hf hK
  have hD : ContDiff ℝ 1
      (deriv (fun y : ℝ => intervalFullSemigroupOperator t f y)) :=
    hC2.deriv' (n := 1)
  exact ((hD.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)) x).hasDerivAt

private theorem intervalFullSemigroupOperator_secondDeriv_eq_laplacian_Ioo
    {t x : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f)
    {K : ℝ} (_hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (fun y : ℝ =>
        deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) y) x =
      ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianValue
        t (cosineCoeffs f) x := by
  let H : ℝ → ℝ := fun z => intervalFullSemigroupOperator t f z
  let G : ℝ → ℝ := fun z => unitIntervalCosineHeatValue t (cosineCoeffs f) z
  have hcos :
      HasDerivAt (fun y : ℝ => deriv G y)
        (ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianValue
          t (cosineCoeffs f) x) x := by
    simpa [G] using
      (ShenWork.RegularityBootstrap.unitIntervalCosineHeatValue_hasSecondSpatialDerivAt_of_l2
        (t := t) (x := x) ht (a := cosineCoeffs f) hl2)
  have hEqOn : Set.EqOn H G (Set.Ioo (0 : ℝ) 1) := by
    intro y hy
    exact
      ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_eq_cosineHeatValue_clean
        (t := t) ht (f := f) hf hy
  have hderivEqOn : Set.EqOn (deriv H) (deriv G) (Set.Ioo (0 : ℝ) 1) := by
    intro y hy
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Ioo hy) hEqOn)
  have hsem :
      HasDerivAt (fun y : ℝ => deriv H y)
        (ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianValue
          t (cosineCoeffs f) x) x := by
    refine hcos.congr_of_eventuallyEq ?_
    filter_upwards [IsOpen.mem_nhds isOpen_Ioo hx] with y hy
    exact hderivEqOn hy
  simpa [H] using hsem.deriv

private theorem intervalFullSemigroupOperator_shift_heat_eq
    {τ s x : ℝ} (hτs : 0 < τ + s) {f : ℝ → ℝ} (hf : Continuous f)
    {K : ℝ} (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (fun r : ℝ => intervalFullSemigroupOperator (τ + r) f x) s =
      deriv (fun y : ℝ =>
        deriv (fun z : ℝ => intervalFullSemigroupOperator (τ + s) f z) y) x := by
  have htime :=
    intervalFullSemigroupOperator_time_shift_hasDerivAt_laplacian
      (τ := τ) (s := s) (x := x) hτs hf hK hl2
      (Set.Ioo_subset_Icc_self hx)
  have hspace :=
    intervalFullSemigroupOperator_secondDeriv_eq_laplacian_Ioo
      (t := τ + s) (x := x) hτs hf hK hl2 hx
  rw [htime.deriv, hspace]

private theorem squareHeatRestart_semigroup_continuousOn
    {L τ : ℝ} (hτ : 0 < τ) {f : ℝ → ℝ} (hf : Continuous f)
    {K : ℝ} (hK : ∀ n, |cosineCoeffs f n| ≤ K) :
    ContinuousOn
      (fun p : ℝ × ℝ => intervalFullSemigroupOperator (τ + p.1) f p.2)
      (Set.Icc (0 : ℝ) L ×ˢ Set.Icc (0 : ℝ) 1) := by
  let Φ : ℝ × ℝ → ℝ × ℝ := fun p => (τ + p.1, p.2)
  have hcos :
      ContinuousOn
        (fun q : ℝ × ℝ =>
          unitIntervalCosineHeatValue q.1 (cosineCoeffs f) q.2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.univ) :=
    ShenWork.IntervalSemigroupNeumann.unitIntervalCosineHeatValue_continuousOn_Ioi_prod
      hK
  have hΦ : Continuous Φ := by
    fun_prop
  have hcomp :
      ContinuousOn
        (fun p : ℝ × ℝ =>
          unitIntervalCosineHeatValue (τ + p.1) (cosineCoeffs f) p.2)
        (Set.Icc (0 : ℝ) L ×ˢ Set.Icc (0 : ℝ) 1) := by
    refine hcos.comp hΦ.continuousOn ?_
    intro p hp
    have htpos : 0 < τ + p.1 := add_pos_of_pos_of_nonneg hτ hp.1.1
    exact ⟨htpos, Set.mem_univ _⟩
  refine hcomp.congr ?_
  intro p hp
  exact
    (ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
      (t := τ + p.1) (add_pos_of_pos_of_nonneg hτ hp.1.1)
      (f := f) hf (M := K) hK hp.2)

private theorem restartedSquareHeatBarrier_continuousOn_rect_of_semigroup
    {L τ M : ℝ} (hτ : 0 < τ) {f : ℝ → ℝ} (hf : Continuous f)
    {K : ℝ} (hK : ∀ n, |cosineCoeffs f n| ≤ K) :
    ContinuousOn
      (fun p : ℝ × ℝ => restartedSquareHeatBarrier τ M f p.1 p.2)
      (Set.Icc (0 : ℝ) L ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hS := squareHeatRestart_semigroup_continuousOn
    (L := L) (τ := τ) hτ hf hK
  have hE : ContinuousOn
      (fun p : ℝ × ℝ => Real.exp (-M * (τ + p.1)))
      (Set.Icc (0 : ℝ) L ×ˢ Set.Icc (0 : ℝ) 1) := by
    fun_prop
  have hsq : ContinuousOn
      (fun p : ℝ × ℝ =>
        (intervalFullSemigroupOperator (τ + p.1) f p.2) ^ 2)
      (Set.Icc (0 : ℝ) L ×ˢ Set.Icc (0 : ℝ) 1) :=
    hS.pow 2
  refine (hE.mul hsq).congr ?_
  intro p hp
  simp [restartedSquareHeatBarrier, restartTimeShift, squareHeatBarrier]

private theorem restartedSquareHeatBarrier_bounded_of_continuousOn
    {L τ M : ℝ} {f : ℝ → ℝ}
    (_hL : 0 ≤ L)
    (hcont :
      ContinuousOn
        (fun p : ℝ × ℝ => restartedSquareHeatBarrier τ M f p.1 p.2)
        (Set.Icc (0 : ℝ) L ×ˢ Set.Icc (0 : ℝ) 1)) :
    BoundedOnIntervalStrip L (restartedSquareHeatBarrier τ M f) := by
  let Kset : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) L ×ˢ Set.Icc (0 : ℝ) 1
  have hKcompact : IsCompact Kset := isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hKcompact.bddAbove_image hcont.norm
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro t ht x hx
  have hp : (t, x) ∈ Kset := ⟨ht, hx⟩
  have hnorm : ‖restartedSquareHeatBarrier τ M f t x‖ ≤ B :=
    hB (Set.mem_image_of_mem _ hp)
  have habs : |restartedSquareHeatBarrier τ M f t x| ≤ B := by
    simpa [Real.norm_eq_abs] using hnorm
  exact habs.trans (le_max_left B 0)

/-- Assemble the positive-time derivative package for the restarted squared heat
barrier from the spectral/time semigroup differentiability and the spatial
semigroup regularity tree. -/
theorem squareHeatRestartDerivativeData_of_semigroup
    {L τ M : ℝ} {f : ℝ → ℝ}
    (hτ : 0 < τ) (hf : Continuous f)
    {K : ℝ} (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2) :
    SquareHeatRestartDerivativeData L τ M f where
  continuousOn_rect :=
    restartedSquareHeatBarrier_continuousOn_rect_of_semigroup
      (L := L) (τ := τ) (M := M) hτ hf hK
  time_hasDerivAt := by
    intro s x hs0 _hsL hx
    exact
      intervalFullSemigroupOperator_time_shift_hasDerivAt_deriv
        (τ := τ) (s := s) (x := x)
        (by linarith [hτ, hs0]) hf hK hl2 hx
  space_hasDerivAt := by
    intro s x hs0 _hsL _hx
    exact
      intervalFullSemigroupOperator_space_hasDerivAt_deriv
        (t := τ + s) (x := x) (by linarith [hτ, hs0]) hf hK
  space_second_hasDerivAt := by
    intro s x hs0 _hsL _hx
    exact
      intervalFullSemigroupOperator_space_second_hasDerivAt_deriv
        (t := τ + s) (x := x) (by linarith [hτ, hs0]) hf hK
  heat_eq := by
    intro s x hs0 _hsL hx
    exact
      intervalFullSemigroupOperator_shift_heat_eq
        (τ := τ) (s := s) (x := x)
        (by linarith [hτ, hs0]) hf hK hl2 hx
  neumann := by
    intro s _hs0 _hsL
    constructor
    · exact ShenWork.intervalFullSemigroupOperator_deriv_at_zero_eq_zero
        (τ + s) f
    · exact ShenWork.intervalFullSemigroupOperator_deriv_at_one_eq_zero
        (τ + s) f
  bounded := by
    have hcont :=
      restartedSquareHeatBarrier_continuousOn_rect_of_semigroup
        (L := L) (τ := τ) (M := M) hτ hf hK
    by_cases hL : 0 ≤ L
    · exact restartedSquareHeatBarrier_bounded_of_continuousOn hL hcont
    · refine ⟨0, le_rfl, ?_⟩
      intro t ht _x _hx
      exfalso
      exact hL (le_trans ht.1 ht.2)

/-- The restart strip package with derivative data discharged by the tree
semigroup regularity lemmas. -/
def squareHeatRestartStripData_of_semigroup
    {L τ A D M : ℝ} {f : ℝ → ℝ} {B C u : ℝ → ℝ → ℝ}
    (hτ : 0 < τ) (hf : Continuous f)
    {K : ℝ} (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2)
    (hL : 0 < L)
    (hcoeff :
      NeumannLinearDriftCoefficientsRegular L
        (restartTimeShift τ B) (restartTimeShift τ C))
    (hsuper :
      IsClassicalNeumannLinearDriftSuperSolution L
        (restartTimeShift τ B) (restartTimeShift τ C)
        (restartTimeShift τ u))
    (hM : A ^ 2 / 2 + D ≤ M)
    (hB_bound :
      ∀ s x, 0 < s → s < L → x ∈ Set.Ioo (0 : ℝ) 1 →
        |B (τ + s) x| ≤ A)
    (hC_neg_bound :
      ∀ s x, 0 < s → s < L → x ∈ Set.Ioo (0 : ℝ) 1 →
        -C (τ + s) x ≤ D)
    (hinitial :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        squareHeatBarrier M f τ x ≤ u τ x) :
    SquareHeatRestartStripData L τ A D M f B C u :=
  squareHeatRestartStripData_of_derivativeData
    (squareHeatRestartDerivativeData_of_semigroup
      (L := L) (τ := τ) (M := M) hτ hf hK hl2)
    hL hcoeff hsuper hM hB_bound hC_neg_bound hinitial

/-- Strict positivity through the positive-time restart route, with each restart
strip's derivative package assembled from the semigroup derivative lemmas. -/
theorem bform_strictPos_via_t0_restart_semigroup
    {p : CM2Params} {u₀ : ShenWork.IntervalDomain.intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    {A D M : ℝ} {f : ℝ → ℝ} {drift react : ℝ → ℝ → ℝ}
    (hseed : SquareHeatSeed (ShenWork.IntervalDomain.intervalDomainLift u₀) f)
    (hf : Continuous f)
    {K : ℝ} (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2)
    (hrestart :
      ∀ t, 0 < t → t < DB.T →
        ∃ τ, 0 < τ ∧ τ < t ∧
          0 < DB.T - τ ∧
          NeumannLinearDriftCoefficientsRegular (DB.T - τ)
            (restartTimeShift τ drift) (restartTimeShift τ react) ∧
          IsClassicalNeumannLinearDriftSuperSolution (DB.T - τ)
            (restartTimeShift τ drift) (restartTimeShift τ react)
            (restartTimeShift τ (bformConjugatePicardLift p DB)) ∧
          A ^ 2 / 2 + D ≤ M ∧
          (∀ s x, 0 < s → s < DB.T - τ → x ∈ Set.Ioo (0 : ℝ) 1 →
            |drift (τ + s) x| ≤ A) ∧
          (∀ s x, 0 < s → s < DB.T - τ → x ∈ Set.Ioo (0 : ℝ) 1 →
            -react (τ + s) x ≤ D) ∧
          (∀ x ∈ Set.Icc (0 : ℝ) 1,
            squareHeatBarrier M f τ x ≤ bformConjugatePicardLift p DB τ x)) :
    ∀ t x, 0 < t → t < DB.T →
      0 < conjugatePicardLimit p u₀ DB.T t x :=
  bform_strictPos_via_t0_restart hseed (fun t ht0 htT => by
    rcases hrestart t ht0 htT with
      ⟨τ, hτ0, hτt, hL, hcoeff, hsuper, hM, hB, hC, hinitial⟩
    refine ⟨τ, hτ0, hτt, ?_⟩
    exact
      squareHeatRestartStripData_of_semigroup
        (L := DB.T - τ) (τ := τ) (A := A) (D := D) (M := M)
        (f := f) (B := drift) (C := react)
        (u := bformConjugatePicardLift p DB)
        hτ0 hf hK hl2 hL hcoeff hsuper hM hB hC hinitial)

end ShenWork.Paper2.BFormPositiveDatumNegPart
