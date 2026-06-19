import ShenWork.PaperOne.WholeLineWeakStationaryLimit
import ShenWork.PaperOne.WholeLineProfileRegularity
import ShenWork.PaperOne.WeakRegularity1D
import Mathlib.Tactic

open Filter MeasureTheory Set Topology Real
open scoped Topology Convolution

noncomputable section

namespace ShenWork.PaperOne

/-!
Regularity of a whole-line profile from the weak stationary identity.

This file is intentionally additive: it does not modify the banked weak-limit
or elliptic-regularity files.  The first lemmas bridge the custom weak test
records used by the long-time limit to the compactly supported smooth tests
used by `WeakRegularity1D`.
-/

/-- Distributional equality `U' = g` on the real line. -/
def WeakFirstDerivEq (U g : ℝ → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
    -(∫ x, U x * deriv φ x) = ∫ x, g x * φ x

/-- Divergence-form weak equation `U'' - F' + R = 0`, equivalently
`∫ U φ'' + ∫ F φ' + ∫ R φ = 0`. -/
def WeakSecondDivergenceEq (U F R : ℝ → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
    (∫ x, U x * iteratedDeriv 2 φ x)
      + (∫ x, F x * deriv φ x)
      + (∫ x, R x * φ x) = 0

lemma exists_supportRadius_of_hasCompactSupport {φ : ℝ → ℝ}
    (hφ : HasCompactSupport φ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : ℝ, R < |x| → φ x = 0 := by
  have hbounded : Bornology.IsBounded (tsupport φ) :=
    (Metric.isCompact_iff_isClosed_bounded.mp hφ).2
  rcases (Metric.isBounded_iff_subset_ball (α := ℝ) (c := 0)).mp hbounded with
    ⟨r, hr⟩
  refine ⟨max r 0, le_max_right r 0, ?_⟩
  intro x hx
  exact image_eq_zero_of_notMem_tsupport (f := φ) (x := x) (by
    intro hx_support
    have hx_ball := hr hx_support
    have hx_dist : dist x (0 : ℝ) = |x| := by simp
    have hr_le : r ≤ max r 0 := le_max_left r 0
    rw [Metric.mem_ball, hx_dist] at hx_ball
    linarith)

def smoothCompactSupport_to_weakTest
    (φ : ℝ → ℝ)
    (_hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    WholeLineWeakTestFunction :=
  let R0 := Classical.choose (exists_supportRadius_of_hasCompactSupport hφc)
  let R1 := Classical.choose
    (exists_supportRadius_of_hasCompactSupport (hasCompactSupport_deriv hφc))
  let R2 := Classical.choose
    (exists_supportRadius_of_hasCompactSupport
      (hasCompactSupport_iteratedDeriv_two hφc))
  let R := max R0 (max R1 R2)
  have hR0 := Classical.choose_spec (exists_supportRadius_of_hasCompactSupport hφc)
  have hR1 := Classical.choose_spec
    (exists_supportRadius_of_hasCompactSupport (hasCompactSupport_deriv hφc))
  have hR2 := Classical.choose_spec
    (exists_supportRadius_of_hasCompactSupport
      (hasCompactSupport_iteratedDeriv_two hφc))
  { phi := φ
    phi' := deriv φ
    phi'' := iteratedDeriv 2 φ
    supportRadius := R
    supportRadius_nonneg := le_trans hR0.1 (le_max_left R0 (max R1 R2))
    phi_zero_of_radius := by
      intro x hx
      exact hR0.2 x (lt_of_le_of_lt (le_max_left R0 (max R1 R2)) hx)
    phi'_zero_of_radius := by
      intro x hx
      exact hR1.2 x
        (lt_of_le_of_lt
          (le_trans (le_max_left R1 R2) (le_max_right R0 (max R1 R2))) hx)
    phi''_zero_of_radius := by
      intro x hx
      exact hR2.2 x
        (lt_of_le_of_lt
          (le_trans (le_max_right R1 R2) (le_max_right R0 (max R1 R2))) hx) }

theorem wholeLineWeakStationary_smooth_integral_zero
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hweak : WholeLineWeakStationary p c U)
    (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    (∫ x : ℝ,
        U x * iteratedDeriv 2 φ x
          - c * U x * deriv φ x
          + p.χ * wholeLineFlux p U x * deriv φ x
          + wholeLineReaction p U x * φ x) = 0 := by
  simpa [wholeLineStationaryWeakFunctional, wholeLineDivergenceWeakIntegrand,
    smoothCompactSupport_to_weakTest] using
    hweak (smoothCompactSupport_to_weakTest φ hφ hφc)

theorem weakFirstDerivEq_of_contDiff_one
    {A g : ℝ → ℝ}
    (hA : ContDiff ℝ 1 A)
    (hA1 : ∀ x, deriv A x = g x) :
    WeakFirstDerivEq A g := by
  intro φ hφ hφc
  have hA_diff : Differentiable ℝ A := hA.differentiable (by norm_num)
  have hA_cont : Continuous A := hA.continuous
  have hA_deriv_cont : Continuous (deriv A) :=
    ContDiff.continuous_deriv_one hA
  have hφ_diff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφ_cont : Continuous φ := hφ.continuous
  have hφ_deriv_cont : Continuous (deriv φ) := by
    simpa [iteratedDeriv_one] using
      hφ.continuous_iteratedDeriv 1 (by norm_num)
  have hφ_deriv_comp : HasCompactSupport (deriv φ) := hφc.deriv
  have hAφ'_int : Integrable (fun x : ℝ => A x * deriv φ x) :=
    Continuous.mul_integrable_of_hasCompactSupport_right
      hA_cont hφ_deriv_cont hφ_deriv_comp
  have hA'φ_int : Integrable (fun x : ℝ => deriv A x * φ x) :=
    Continuous.mul_integrable_of_hasCompactSupport_right
      hA_deriv_cont hφ_cont hφc
  have hAφ_comp : HasCompactSupport (fun x : ℝ => A x * φ x) :=
    hφc.mul_left
  have hA_hasDeriv :
      ∀ x ∈ tsupport φ, HasDerivAt A (deriv A x) x := by
    intro x _hx
    exact (hA_diff x).hasDerivAt
  have hφ_hasDeriv :
      ∀ x ∈ tsupport A, HasDerivAt φ (deriv φ x) x := by
    intro x _hx
    exact (hφ_diff x).hasDerivAt
  have hIBP_raw := MeasureTheory.integral_mul_deriv_eq_deriv_mul
    (A := ℝ) (u := A) (v := φ) (u' := deriv A) (v' := deriv φ)
    (a' := (0 : ℝ)) (b' := (0 : ℝ))
    hA_hasDeriv hφ_hasDeriv
    (by simpa [Pi.mul_def] using hAφ'_int)
    (by simpa [Pi.mul_def] using hA'φ_int)
    (by simpa [Pi.mul_def] using
      HasCompactSupport.tendsto_zero_atBot hAφ_comp)
    (by simpa [Pi.mul_def] using
      HasCompactSupport.tendsto_zero_atTop hAφ_comp)
  have hIBP :
      (∫ x : ℝ, A x * deriv φ x) =
        -∫ x : ℝ, deriv A x * φ x := by
    simpa [Pi.mul_def] using hIBP_raw
  calc
    -(∫ x : ℝ, A x * deriv φ x)
        = ∫ x : ℝ, deriv A x * φ x := by rw [hIBP]; simp
    _ = ∫ x : ℝ, g x * φ x := by
      congr 1
      ext x
      rw [hA1 x]

theorem right_convolution_deriv_eq
    {H ρ : ℝ → ℝ}
    (hHloc : LocallyIntegrable H volume)
    (hρc : HasCompactSupport ρ)
    (hρsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) :
    ∀ x, deriv
        (H ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x =
      (H ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] deriv ρ) x := by
  have hρC1 : ContDiff ℝ 1 ρ := hρsmooth.of_le (by norm_num)
  intro x
  exact (hρc.hasDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ) hHloc hρC1 x).deriv

theorem weak_right_convolution_deriv_zero
    {H ρ : ℝ → ℝ}
    (hρc : HasCompactSupport ρ)
    (hρsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hweak : WeakFirstDerivEq H (fun _ => 0)) :
    ∀ x, (H ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] deriv ρ) x = 0 := by
  intro x
  let ψ : ℝ → ℝ := fun t => ρ (x - t)
  have hψsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := by
    dsimp [ψ]
    exact hρsmooth.comp (by fun_prop)
  have hψcompact : HasCompactSupport ψ := by
    dsimp [ψ]
    simpa [Function.comp_def] using
      hρc.comp_isClosedEmbedding (g := fun t : ℝ => x - t)
        (Homeomorph.subLeft x).isClosedEmbedding
  have hψ_deriv :
      deriv ψ = fun t : ℝ => -deriv ρ (x - t) := by
    dsimp [ψ]
    ext t
    simpa using deriv_comp_const_sub ρ x t
  have hzero : (∫ t : ℝ, H t * deriv ρ (x - t)) = 0 := by
    have hweakx := hweak ψ hψsmooth hψcompact
    have hneg :
        (∫ t : ℝ, -(H t * deriv ρ (x - t))) = 0 := by
      simpa [hψ_deriv] using hweakx
    have hnegInt :
        -(∫ t : ℝ, H t * deriv ρ (x - t)) = 0 := by
      rw [← integral_neg]
      exact hneg
    exact neg_eq_zero.mp hnegInt
  rw [convolution_lsmul]
  simpa using hzero

theorem constant_of_continuous_weakFirstDerivEq_zero
    {H : ℝ → ℝ}
    (hH : Continuous H)
    (hweak : WeakFirstDerivEq H (fun _ => 0)) :
    ∃ a : ℝ, ∀ x, H x = a := by
  let M : ℕ → ℝ → ℝ :=
    fun n => H ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (mollifierSeq n).normed volume
  have hHloc : LocallyIntegrable H volume := hH.locallyIntegrable
  have hM_const : ∀ n x, M n x = M n 0 := by
    intro n x
    have hρc : HasCompactSupport ((mollifierSeq n).normed volume) :=
      (mollifierSeq n).hasCompactSupport_normed
    have hρsmooth :
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          ((mollifierSeq n).normed volume) :=
      (mollifierSeq n).contDiff_normed
    have hρC1 : ContDiff ℝ 1 ((mollifierSeq n).normed volume) :=
      hρsmooth.of_le (by norm_num)
    have hM_diff : Differentiable ℝ (M n) := by
      intro y
      dsimp [M]
      exact (hρc.hasDerivAt_convolution_right
        (ContinuousLinearMap.lsmul ℝ ℝ) hHloc hρC1 y).differentiableAt
    have hM_deriv_zero : ∀ y, deriv (M n) y = 0 := by
      intro y
      dsimp [M]
      calc
        deriv
            (H ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              (mollifierSeq n).normed volume) y
            =
          (H ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            deriv ((mollifierSeq n).normed volume)) y :=
              right_convolution_deriv_eq hHloc hρc hρsmooth y
        _ = 0 :=
              weak_right_convolution_deriv_zero hρc hρsmooth hweak y
    exact is_const_of_deriv_eq_zero hM_diff hM_deriv_zero x 0
  have hM_tendsto : ∀ x, Tendsto (fun n => M n x) atTop (𝓝 (H x)) := by
    intro x
    have hleft :=
      ContDiffBump.convolution_tendsto_right_of_continuous
        (μ := volume) (φ := mollifierSeq) mollifierSeq_rOut_tendsto hH x
    have hseq :
        (fun n => M n x) =
          fun n =>
            (((mollifierSeq n).normed volume
              ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] H) x) := by
      ext n
      dsimp [M]
      exact right_mollifier_eq_left ((mollifierSeq n).normed volume) H x
    rw [hseq]
    exact hleft
  refine ⟨H 0, ?_⟩
  intro x
  have hleft : Tendsto (fun n => M n 0) atTop (𝓝 (H x)) := by
    have hx := hM_tendsto x
    have hconst :
        (fun n => M n x) = fun n => M n 0 := by
      ext n
      exact hM_const n x
    simpa [hconst] using hx
  have hright : Tendsto (fun n => M n 0) atTop (𝓝 (H 0)) :=
    hM_tendsto 0
  exact tendsto_nhds_unique hleft hright

theorem firstPrimitive_contDiff_one {g : ℝ → ℝ} (hg : Continuous g) :
    ContDiff ℝ 1 (firstPrimitive g) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (firstPrimitive_hasDerivAt hg x).differentiableAt, ?_⟩
  have hder : deriv (firstPrimitive g) = g := funext (deriv_firstPrimitive hg)
  rw [hder]
  exact hg

theorem contDiff_one_of_weak_first_deriv_eq_continuous
    {U g : ℝ → ℝ}
    (hU : Continuous U)
    (hg : Continuous g)
    (hweak : WeakFirstDerivEq U g) :
    ContDiff ℝ 1 U ∧ ∀ x, deriv U x = g x := by
  let A : ℝ → ℝ := firstPrimitive g
  let H : ℝ → ℝ := fun x => U x - A x
  have hA_C1 : ContDiff ℝ 1 A := by
    simpa [A] using firstPrimitive_contDiff_one hg
  have hA_cont : Continuous A := hA_C1.continuous
  have hA_weak : WeakFirstDerivEq A g := by
    apply weakFirstDerivEq_of_contDiff_one hA_C1
    intro x
    simpa [A] using deriv_firstPrimitive hg x
  have hH_cont : Continuous H := hU.sub hA_cont
  have hH_weak : WeakFirstDerivEq H (fun _ => 0) := by
    intro φ hφ hφc
    have hφ_deriv_cont : Continuous (deriv φ) := by
      simpa [iteratedDeriv_one] using
        hφ.continuous_iteratedDeriv 1 (by norm_num)
    have hφ_deriv_comp : HasCompactSupport (deriv φ) := hφc.deriv
    have hU_int : Integrable (fun x : ℝ => U x * deriv φ x) :=
      Continuous.mul_integrable_of_hasCompactSupport_right
        hU hφ_deriv_cont hφ_deriv_comp
    have hA_int : Integrable (fun x : ℝ => A x * deriv φ x) :=
      Continuous.mul_integrable_of_hasCompactSupport_right
        hA_cont hφ_deriv_cont hφ_deriv_comp
    have hsub :
        (∫ x : ℝ, H x * deriv φ x) =
          (∫ x : ℝ, U x * deriv φ x) -
            ∫ x : ℝ, A x * deriv φ x := by
      rw [← integral_sub hU_int hA_int]
      congr 1
      ext x
      simp [H, A, sub_mul]
    have hsame :
        -(∫ x : ℝ, U x * deriv φ x) =
          -(∫ x : ℝ, A x * deriv φ x) := by
      rw [hweak φ hφ hφc, hA_weak φ hφ hφc]
    calc
      -(∫ x : ℝ, H x * deriv φ x)
          = -((∫ x : ℝ, U x * deriv φ x) -
              ∫ x : ℝ, A x * deriv φ x) := by rw [hsub]
      _ = 0 := by linarith
      _ = ∫ x : ℝ, (fun _ : ℝ => 0) x * φ x := by simp
  rcases constant_of_continuous_weakFirstDerivEq_zero hH_cont hH_weak with
    ⟨a, hH_const⟩
  have hU_eq : U = fun x : ℝ => A x + a := by
    ext x
    have hx := hH_const x
    dsimp [H] at hx
    dsimp [A]
    linarith
  constructor
  · rw [hU_eq]
    exact hA_C1.add contDiff_const
  · intro x
    rw [hU_eq]
    exact ((firstPrimitive_hasDerivAt hg x).add_const a).deriv

theorem firstPrimitive_second_pairing
    {F : ℝ → ℝ} (hF : Continuous F)
    {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    (∫ x : ℝ, firstPrimitive F x * iteratedDeriv 2 φ x) =
      -(∫ x : ℝ, F x * deriv φ x) := by
  have hA_C1 : ContDiff ℝ 1 (firstPrimitive F) :=
    firstPrimitive_contDiff_one hF
  have hA_weak : WeakFirstDerivEq (firstPrimitive F) F := by
    apply weakFirstDerivEq_of_contDiff_one hA_C1
    intro x
    exact deriv_firstPrimitive hF x
  have hφ_deriv_smooth :
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv φ) := by
    apply ContDiff.deriv'
    simpa using hφ
  have hweak := hA_weak (deriv φ) hφ_deriv_smooth hφc.deriv
  have hweak' :
      -(∫ x : ℝ, firstPrimitive F x * iteratedDeriv 2 φ x) =
        ∫ x : ℝ, F x * deriv φ x := by
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using hweak
  linarith

theorem contDiff_one_of_weak_second_divergence_eq_continuous
    {U F R : ℝ → ℝ}
    (hU : Continuous U)
    (hF : Continuous F)
    (hR : Continuous R)
    (hweak : WeakSecondDivergenceEq U F R) :
    ContDiff ℝ 1 U := by
  let A : ℝ → ℝ := firstPrimitive F
  let B : ℝ → ℝ := secondPrimitive R
  let H : ℝ → ℝ := fun x => U x - A x + B x
  have hA_C1 : ContDiff ℝ 1 A := by
    simpa [A] using firstPrimitive_contDiff_one hF
  have hA_cont : Continuous A := hA_C1.continuous
  have hB_C2 : ContDiff ℝ 2 B := by
    simpa [B] using secondPrimitive_contDiff_two hR
  have hB_cont : Continuous B := hB_C2.continuous
  have hB_weak : WeakSecondDerivEq B R := by
    apply weakSecondDerivEq_of_contDiff_two hB_C2
    intro x
    simpa [B] using secondPrimitive_second_deriv_eq hR x
  have hH_cont : Continuous H := (hU.sub hA_cont).add hB_cont
  have hH_weak : WeakSecondDerivEq H (fun _ => 0) := by
    intro φ hφ hφc
    have hφ_two_cont : Continuous (iteratedDeriv 2 φ) :=
      hφ.continuous_iteratedDeriv 2 (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ (((⊤ : ℕ∞) : WithTop ℕ∞))
        exact WithTop.coe_le_coe.2 le_top)
    have hφ_two_comp : HasCompactSupport (iteratedDeriv 2 φ) :=
      hasCompactSupport_iteratedDeriv_two hφc
    have hU_int : Integrable (fun x : ℝ => U x * iteratedDeriv 2 φ x) :=
      Continuous.mul_integrable_of_hasCompactSupport_right
        hU hφ_two_cont hφ_two_comp
    have hA_int : Integrable (fun x : ℝ => A x * iteratedDeriv 2 φ x) :=
      Continuous.mul_integrable_of_hasCompactSupport_right
        hA_cont hφ_two_cont hφ_two_comp
    have hB_int : Integrable (fun x : ℝ => B x * iteratedDeriv 2 φ x) :=
      Continuous.mul_integrable_of_hasCompactSupport_right
        hB_cont hφ_two_cont hφ_two_comp
    have hH_split :
        (∫ x : ℝ, H x * iteratedDeriv 2 φ x) =
          ((∫ x : ℝ, U x * iteratedDeriv 2 φ x) -
            ∫ x : ℝ, A x * iteratedDeriv 2 φ x)
            + ∫ x : ℝ, B x * iteratedDeriv 2 φ x := by
      calc
        (∫ x : ℝ, H x * iteratedDeriv 2 φ x)
            =
          ∫ x : ℝ,
            (U x * iteratedDeriv 2 φ x - A x * iteratedDeriv 2 φ x)
              + B x * iteratedDeriv 2 φ x := by
              congr 1
              ext x
              simp [H, A, B, sub_mul, add_mul]
        _ =
          (∫ x : ℝ, U x * iteratedDeriv 2 φ x - A x * iteratedDeriv 2 φ x)
            + ∫ x : ℝ, B x * iteratedDeriv 2 φ x := by
              simpa [sub_eq_add_neg, add_assoc] using
                (integral_add (μ := volume)
                  (f := fun x : ℝ =>
                    U x * iteratedDeriv 2 φ x - A x * iteratedDeriv 2 φ x)
                  (g := fun x : ℝ => B x * iteratedDeriv 2 φ x)
                  (hU_int.sub hA_int) hB_int)
        _ =
          ((∫ x : ℝ, U x * iteratedDeriv 2 φ x) -
            ∫ x : ℝ, A x * iteratedDeriv 2 φ x)
            + ∫ x : ℝ, B x * iteratedDeriv 2 φ x := by
              rw [integral_sub hU_int hA_int]
    have hA_pair :
        (∫ x : ℝ, A x * iteratedDeriv 2 φ x) =
          -(∫ x : ℝ, F x * deriv φ x) := by
      simpa [A] using firstPrimitive_second_pairing hF hφ hφc
    have hB_pair :
        (∫ x : ℝ, B x * iteratedDeriv 2 φ x) =
          ∫ x : ℝ, R x * φ x := by
      exact hB_weak φ hφ hφc
    calc
      (∫ x : ℝ, H x * iteratedDeriv 2 φ x)
          = ((∫ x : ℝ, U x * iteratedDeriv 2 φ x) -
              ∫ x : ℝ, A x * iteratedDeriv 2 φ x)
              + ∫ x : ℝ, B x * iteratedDeriv 2 φ x := hH_split
      _ = ((∫ x : ℝ, U x * iteratedDeriv 2 φ x) -
              (-(∫ x : ℝ, F x * deriv φ x)))
              + ∫ x : ℝ, R x * φ x := by rw [hA_pair, hB_pair]
      _ = (∫ x : ℝ, (fun _ : ℝ => 0) x * φ x) := by
        have hw := hweak φ hφ hφc
        simp
        linarith
  rcases affine_of_continuous_weakSecondDerivEq_zero hH_cont hH_weak with
    ⟨a, b, hH_aff⟩
  have hU_eq : U = fun x : ℝ => A x - B x + (a + b * x) := by
    ext x
    have hx := hH_aff x
    dsimp [H] at hx
    dsimp [A, B]
    linarith
  rw [hU_eq]
  exact (hA_C1.sub (hB_C2.of_le (by norm_num))).add
    ((affine_contDiff_two a b).of_le (by norm_num))

def wholeLineStationaryFluxCoeff
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : ℝ → ℝ :=
  fun x => -c * U x + p.χ * wholeLineFlux p U x

theorem wholeLineStationaryFluxCoeff_continuous_constantBarrier
    (p : CMParams) (c : ℝ) {M : ℝ} {U : ℝ → ℝ}
    (hU : ShenWork.Paper1.InConstantBarrierTrap M U) :
    Continuous (wholeLineStationaryFluxCoeff p c U) := by
  have hflux :
      Continuous (wholeLineFlux p U) :=
    ShenWork.Paper1.wholeLineFlux_continuous_constantBarrier p hU
  simpa [wholeLineStationaryFluxCoeff] using
    ((continuous_const.mul hU.1.1).add (continuous_const.mul hflux))

theorem weakSecondDivergenceEq_of_wholeLineWeakStationary
    {p : CMParams} {c M : ℝ} {U : ℝ → ℝ}
    (hU : ShenWork.Paper1.InConstantBarrierTrap M U)
    (hweak : WholeLineWeakStationary p c U) :
    WeakSecondDivergenceEq U
      (wholeLineStationaryFluxCoeff p c U) (wholeLineReaction p U) := by
  intro φ hφ hφc
  have hφ_cont : Continuous φ := hφ.continuous
  have hφ_deriv_cont : Continuous (deriv φ) := by
    simpa [iteratedDeriv_one] using
      hφ.continuous_iteratedDeriv 1 (by norm_num)
  have hφ_two_cont : Continuous (iteratedDeriv 2 φ) :=
    hφ.continuous_iteratedDeriv 2 (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ (((⊤ : ℕ∞) : WithTop ℕ∞))
      exact WithTop.coe_le_coe.2 le_top)
  have hφ_deriv_comp : HasCompactSupport (deriv φ) := hφc.deriv
  have hφ_two_comp : HasCompactSupport (iteratedDeriv 2 φ) :=
    hasCompactSupport_iteratedDeriv_two hφc
  have hF_cont : Continuous (wholeLineStationaryFluxCoeff p c U) :=
    wholeLineStationaryFluxCoeff_continuous_constantBarrier p c hU
  have hR_cont : Continuous (wholeLineReaction p U) :=
    ShenWork.Paper1.wholeLineReaction_continuous_constantBarrier p hU
  have hU_int : Integrable (fun x : ℝ => U x * iteratedDeriv 2 φ x) :=
    Continuous.mul_integrable_of_hasCompactSupport_right
      hU.1.1 hφ_two_cont hφ_two_comp
  have hF_int :
      Integrable
        (fun x : ℝ => wholeLineStationaryFluxCoeff p c U x * deriv φ x) :=
    Continuous.mul_integrable_of_hasCompactSupport_right
      hF_cont hφ_deriv_cont hφ_deriv_comp
  have hR_int : Integrable (fun x : ℝ => wholeLineReaction p U x * φ x) :=
    Continuous.mul_integrable_of_hasCompactSupport_right hR_cont hφ_cont hφc
  have hsingle :
      (∫ x : ℝ,
          U x * iteratedDeriv 2 φ x
            + wholeLineStationaryFluxCoeff p c U x * deriv φ x
            + wholeLineReaction p U x * φ x) = 0 := by
    have h0 := wholeLineWeakStationary_smooth_integral_zero hweak φ hφ hφc
    rw [← h0]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp [wholeLineStationaryFluxCoeff]
      ring
  have hsplit :
      (∫ x : ℝ,
          U x * iteratedDeriv 2 φ x
            + wholeLineStationaryFluxCoeff p c U x * deriv φ x
            + wholeLineReaction p U x * φ x)
        =
        (∫ x : ℝ, U x * iteratedDeriv 2 φ x)
          + (∫ x : ℝ, wholeLineStationaryFluxCoeff p c U x * deriv φ x)
          + (∫ x : ℝ, wholeLineReaction p U x * φ x) := by
    calc
      (∫ x : ℝ,
          U x * iteratedDeriv 2 φ x
            + wholeLineStationaryFluxCoeff p c U x * deriv φ x
            + wholeLineReaction p U x * φ x)
          =
        (∫ x : ℝ,
          (U x * iteratedDeriv 2 φ x
            + wholeLineStationaryFluxCoeff p c U x * deriv φ x)
            + wholeLineReaction p U x * φ x) := by rfl
      _ =
        (∫ x : ℝ,
          U x * iteratedDeriv 2 φ x
            + wholeLineStationaryFluxCoeff p c U x * deriv φ x)
          + (∫ x : ℝ, wholeLineReaction p U x * φ x) := by
            exact integral_add (hU_int.add hF_int) hR_int
      _ =
        ((∫ x : ℝ, U x * iteratedDeriv 2 φ x)
          + (∫ x : ℝ, wholeLineStationaryFluxCoeff p c U x * deriv φ x))
          + (∫ x : ℝ, wholeLineReaction p U x * φ x) := by
            rw [integral_add hU_int hF_int]
      _ =
        (∫ x : ℝ, U x * iteratedDeriv 2 φ x)
          + (∫ x : ℝ, wholeLineStationaryFluxCoeff p c U x * deriv φ x)
          + (∫ x : ℝ, wholeLineReaction p U x * φ x) := by ring
  simpa [hsplit] using hsingle

theorem wholeLine_profile_contDiff_one_from_weak
    {p : CMParams} {c M : ℝ} {U : ℝ → ℝ}
    (hU : ShenWork.Paper1.InConstantBarrierTrap M U)
    (hweak : WholeLineWeakStationary p c U) :
    ContDiff ℝ 1 U := by
  exact contDiff_one_of_weak_second_divergence_eq_continuous
    hU.1.1
    (wholeLineStationaryFluxCoeff_continuous_constantBarrier p c hU)
    (ShenWork.Paper1.wholeLineReaction_continuous_constantBarrier p hU)
    (weakSecondDivergenceEq_of_wholeLineWeakStationary hU hweak)

theorem rpow_const_contDiff_one_of_contDiff_one
    {U : ℝ → ℝ} {a : ℝ}
    (ha : 1 ≤ a)
    (hU1 : ContDiff ℝ 1 U) :
    ContDiff ℝ 1 (fun x : ℝ => (U x) ^ a) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨?_, ?_⟩
  · intro x
    exact (((contDiff_one_iff_deriv.mp hU1).1 x).hasDerivAt.rpow_const
      (Or.inr ha)).differentiableAt
  · have hder :
        deriv (fun x : ℝ => (U x) ^ a) =
          fun x : ℝ => deriv U x * a * (U x) ^ (a - 1) := by
      funext x
      exact (((contDiff_one_iff_deriv.mp hU1).1 x).hasDerivAt.rpow_const
        (Or.inr ha)).deriv
    rw [hder]
    have hpow : Continuous (fun x : ℝ => (U x) ^ (a - 1)) :=
      hU1.continuous.rpow_const (fun _ => Or.inr (sub_nonneg.mpr ha))
    exact (((ContDiff.continuous_deriv_one hU1).mul continuous_const).mul hpow)

theorem wholeLineFlux_contDiff_one_of_profile_contDiff_one
    (p : CMParams) {U : ℝ → ℝ}
    (hU_bdd : IsCUnifBdd U)
    (hU_nonneg : ∀ x, 0 ≤ U x)
    (hU1 : ContDiff ℝ 1 U) :
    ContDiff ℝ 1 (wholeLineFlux p U) := by
  have hpow : ContDiff ℝ 1 (fun x : ℝ => (U x) ^ p.m) :=
    rpow_const_contDiff_one_of_contDiff_one p.hm hU1
  have hV2 : ContDiff ℝ 2 (frozenSignal p.γ U) :=
    frozenSignal_contDiff_two p hU_bdd hU_nonneg
  have hVd1 : ContDiff ℝ 1 (deriv (frozenSignal p.γ U)) := by
    apply ContDiff.deriv'
    simpa using hV2
  simpa [wholeLineFlux, frozenSignal] using hpow.mul hVd1

theorem wholeLineStationaryFluxCoeff_contDiff_one
    (p : CMParams) (c : ℝ) {U : ℝ → ℝ}
    (hU_bdd : IsCUnifBdd U)
    (hU_nonneg : ∀ x, 0 ≤ U x)
    (hU1 : ContDiff ℝ 1 U) :
    ContDiff ℝ 1 (wholeLineStationaryFluxCoeff p c U) := by
  have hflux1 : ContDiff ℝ 1 (wholeLineFlux p U) :=
    wholeLineFlux_contDiff_one_of_profile_contDiff_one p hU_bdd hU_nonneg hU1
  simpa [wholeLineStationaryFluxCoeff] using
    ((contDiff_const.mul hU1).add (contDiff_const.mul hflux1))

theorem weakSecondDerivEq_of_weakSecondDivergence_of_contDiff_one
    {U F R : ℝ → ℝ}
    (hF1 : ContDiff ℝ 1 F)
    (hR : Continuous R)
    (hweak : WeakSecondDivergenceEq U F R) :
    WeakSecondDerivEq U (fun x => deriv F x - R x) := by
  intro φ hφ hφc
  have hφ_cont : Continuous φ := hφ.continuous
  have hF_deriv_cont : Continuous (deriv F) :=
    ContDiff.continuous_deriv_one hF1
  have hF_deriv_int : Integrable (fun x : ℝ => deriv F x * φ x) :=
    Continuous.mul_integrable_of_hasCompactSupport_right
      hF_deriv_cont hφ_cont hφc
  have hR_int : Integrable (fun x : ℝ => R x * φ x) :=
    Continuous.mul_integrable_of_hasCompactSupport_right hR hφ_cont hφc
  have hF_weak : WeakFirstDerivEq F (deriv F) :=
    weakFirstDerivEq_of_contDiff_one hF1 (fun _ => rfl)
  have hF_pair :
      -(∫ x : ℝ, F x * deriv φ x) =
        ∫ x : ℝ, deriv F x * φ x :=
    hF_weak φ hφ hφc
  have hmain :
      (∫ x : ℝ, U x * iteratedDeriv 2 φ x) =
        (∫ x : ℝ, deriv F x * φ x) -
          ∫ x : ℝ, R x * φ x := by
    have hw := hweak φ hφ hφc
    linarith
  calc
    (∫ x : ℝ, U x * iteratedDeriv 2 φ x)
        = (∫ x : ℝ, deriv F x * φ x) -
            ∫ x : ℝ, R x * φ x := hmain
    _ = ∫ x : ℝ, (deriv F x - R x) * φ x := by
      rw [← integral_sub hF_deriv_int hR_int]
      congr 1
      ext x
      ring

theorem wholeLine_profile_contDiff_two_from_weak
    {p : CMParams} {c M : ℝ} {U : ℝ → ℝ}
    (hU : ShenWork.Paper1.InConstantBarrierTrap M U)
    (hweak : WholeLineWeakStationary p c U) :
    ContDiff ℝ 2 U ∧
      ∀ x,
        iteratedDeriv 2 U x =
          deriv (wholeLineStationaryFluxCoeff p c U) x
            - wholeLineReaction p U x := by
  have hU1 : ContDiff ℝ 1 U :=
    wholeLine_profile_contDiff_one_from_weak hU hweak
  have hF1 :
      ContDiff ℝ 1 (wholeLineStationaryFluxCoeff p c U) :=
    wholeLineStationaryFluxCoeff_contDiff_one p c hU.1
      (fun x => (hU.2 x).1) hU1
  have hR_cont : Continuous (wholeLineReaction p U) :=
    ShenWork.Paper1.wholeLineReaction_continuous_constantBarrier p hU
  have hsource_cont :
      Continuous
        (fun x : ℝ =>
          deriv (wholeLineStationaryFluxCoeff p c U) x - wholeLineReaction p U x) :=
    (ContDiff.continuous_deriv_one hF1).sub hR_cont
  have hweakDiv :
      WeakSecondDivergenceEq U
        (wholeLineStationaryFluxCoeff p c U) (wholeLineReaction p U) :=
    weakSecondDivergenceEq_of_wholeLineWeakStationary hU hweak
  exact contDiff_two_of_weak_second_deriv_eq_continuous hU.1.1
    hsource_cont
    (weakSecondDerivEq_of_weakSecondDivergence_of_contDiff_one
      hF1 hR_cont hweakDiv)

theorem wholeLineStationaryFluxCoeff_deriv
    (p : CMParams) (c : ℝ) {U : ℝ → ℝ}
    (hU_bdd : IsCUnifBdd U)
    (hU_nonneg : ∀ x, 0 ≤ U x)
    (hU1 : ContDiff ℝ 1 U) :
    ∀ x,
      deriv (wholeLineStationaryFluxCoeff p c U) x =
        -c * deriv U x + p.χ * deriv (wholeLineFlux p U) x := by
  have hflux1 : ContDiff ℝ 1 (wholeLineFlux p U) :=
    wholeLineFlux_contDiff_one_of_profile_contDiff_one p hU_bdd hU_nonneg hU1
  intro x
  have hUdiff : DifferentiableAt ℝ U x :=
    (contDiff_one_iff_deriv.mp hU1).1 x
  have hfluxdiff : DifferentiableAt ℝ (wholeLineFlux p U) x :=
    (contDiff_one_iff_deriv.mp hflux1).1 x
  have hder :=
    ((hUdiff.hasDerivAt.const_mul (-c)).add
      (hfluxdiff.hasDerivAt.const_mul p.χ)).deriv
  change
    deriv (fun y : ℝ => -c * U y + p.χ * wholeLineFlux p U y) x =
      -c * deriv U x + p.χ * deriv (wholeLineFlux p U) x
  convert hder using 1

theorem wholeLine_divergence_stationary_from_weak
    {p : CMParams} {c M : ℝ} {U : ℝ → ℝ}
    (hU : ShenWork.Paper1.InConstantBarrierTrap M U)
    (hweak : WholeLineWeakStationary p c U) :
    wholeLineDivergenceStationaryEquation p c U := by
  have hC2 := wholeLine_profile_contDiff_two_from_weak hU hweak
  have hU1 : ContDiff ℝ 1 U := hC2.1.of_le (by norm_num)
  have hF_deriv :=
    wholeLineStationaryFluxCoeff_deriv p c hU.1 (fun x => (hU.2 x).1) hU1
  intro x
  have hEq := hC2.2 x
  rw [hF_deriv x] at hEq
  unfold wholeLineDivergenceStationaryOperator
  change
    iteratedDeriv 2 U x + c * deriv U x
      - p.χ * deriv (wholeLineFlux p U) x
      + wholeLineReaction p U x = 0
  linarith

theorem wholeLine_profile_regularity_from_weak
    {p : CMParams} {c M : ℝ} {U : ℝ → ℝ}
    (hU : ShenWork.Paper1.InConstantBarrierTrap M U)
    (hweak : WholeLineWeakStationary p c U) :
    WholeLineProfileRegularityData p U (frozenSignal p.γ U)
      (deriv U) (iteratedDeriv 2 U) := by
  have hC2 := (wholeLine_profile_contDiff_two_from_weak hU hweak).1
  refine
    { U_bdd := hU.1
      U_nonneg := fun x => (hU.2 x).1
      signal_eq := rfl
      gradientDuhamel_hasDerivAt := ?_
      gradientDuhamel_continuous := ?_
      secondDuhamel_hasDerivAt_after_resolvent := ?_
      secondDuhamel_continuous_after_resolvent := ?_ }
  · intro x
    exact ((hC2.differentiable (by norm_num)) x).hasDerivAt
  · exact hC2.continuous_deriv (by norm_num)
  · intro _hVxx x
    have hdiff : Differentiable ℝ (deriv U) :=
      hC2.differentiable_deriv_two
    have hhas := (hdiff x).hasDerivAt
    convert hhas using 1
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one]
  · intro _hVxx
    exact hC2.continuous_iteratedDeriv 2 (by norm_num)

theorem fixedPoint_profile_regularity_from_weak
    {p : CMParams} {c M : ℝ} {U : ℝ → ℝ}
    (hU : ShenWork.Paper1.InConstantBarrierTrap M U)
    (hweak : WholeLineWeakStationary p c U) :
    ∃ Ux Uxx : ℝ → ℝ,
      WholeLineProfileRegularityData p U (frozenSignal p.γ U) Ux Uxx :=
  ⟨deriv U, iteratedDeriv 2 U, wholeLine_profile_regularity_from_weak hU hweak⟩

section AxiomAudit

#print axioms contDiff_one_of_weak_first_deriv_eq_continuous
#print axioms contDiff_one_of_weak_second_divergence_eq_continuous
#print axioms weakSecondDivergenceEq_of_wholeLineWeakStationary
#print axioms wholeLine_profile_contDiff_one_from_weak
#print axioms wholeLine_profile_contDiff_two_from_weak
#print axioms wholeLine_divergence_stationary_from_weak
#print axioms wholeLine_profile_regularity_from_weak
#print axioms fixedPoint_profile_regularity_from_weak

end AxiomAudit

end ShenWork.PaperOne
