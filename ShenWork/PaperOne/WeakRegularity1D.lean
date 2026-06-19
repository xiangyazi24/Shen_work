import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open Filter MeasureTheory Set
open scoped Topology Convolution

noncomputable section

namespace ShenWork.PaperOne

/-- Distributional equality `U'' = g` on the real line, tested against compactly
supported smooth scalar functions.

In Mathlib, bare `⊤ : WithTop ℕ∞` denotes the analytic level `C^ω`; the
smooth level used by `ContDiffBump` is `((⊤ : ℕ∞) : WithTop ℕ∞)`. -/
def WeakSecondDerivEq (U g : ℝ → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
    ∫ x, U x * iteratedDeriv 2 φ x = ∫ x, g x * φ x

/-- The twice-integrated primitive anchored at `0`. -/
def secondPrimitive (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..x, ∫ r in (0 : ℝ)..s, g r

/-- The once-integrated primitive anchored at `0`. -/
def firstPrimitive (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..x, g r

theorem firstPrimitive_hasDerivAt {g : ℝ → ℝ} (hg : Continuous g) (x : ℝ) :
    HasDerivAt (firstPrimitive g) (g x) x := by
  simpa [firstPrimitive] using
    intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable (0 : ℝ) x)
      (hg.stronglyMeasurableAtFilter volume (𝓝 x))
      hg.continuousAt

theorem deriv_firstPrimitive {g : ℝ → ℝ} (hg : Continuous g) (x : ℝ) :
    deriv (firstPrimitive g) x = g x :=
  (firstPrimitive_hasDerivAt hg x).deriv

theorem firstPrimitive_continuous {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous (firstPrimitive g) :=
  continuous_iff_continuousAt.mpr fun x =>
    (firstPrimitive_hasDerivAt hg x).continuousAt

theorem secondPrimitive_hasDerivAt {g : ℝ → ℝ} (hg : Continuous g) (x : ℝ) :
    HasDerivAt (secondPrimitive g) (firstPrimitive g x) x := by
  have hF : Continuous (firstPrimitive g) := firstPrimitive_continuous hg
  simpa [secondPrimitive, firstPrimitive] using
    intervalIntegral.integral_hasDerivAt_right
      (hF.intervalIntegrable (0 : ℝ) x)
      (hF.stronglyMeasurableAtFilter volume (𝓝 x))
      hF.continuousAt

theorem deriv_secondPrimitive {g : ℝ → ℝ} (hg : Continuous g) (x : ℝ) :
    deriv (secondPrimitive g) x = firstPrimitive g x :=
  (secondPrimitive_hasDerivAt hg x).deriv

theorem secondPrimitive_contDiff_two {g : ℝ → ℝ} (hg : Continuous g) :
    ContDiff ℝ 2 (secondPrimitive g) := by
  have hF1 : ContDiff ℝ 1 (firstPrimitive g) := by
    refine (contDiff_one_iff_deriv (𝕜 := ℝ) (f := firstPrimitive g)).2 ?_
    refine ⟨fun x => (firstPrimitive_hasDerivAt hg x).differentiableAt, ?_⟩
    have hder : deriv (firstPrimitive g) = g := funext (deriv_firstPrimitive hg)
    rw [hder]
    exact hg
  refine (contDiff_succ_iff_deriv (𝕜 := ℝ) (n := 1)
    (f := secondPrimitive g)).2 ?_
  refine ⟨fun x => (secondPrimitive_hasDerivAt hg x).differentiableAt, ?_, ?_⟩
  · intro h
    norm_num at h
  · have hder : deriv (secondPrimitive g) = firstPrimitive g :=
      funext (deriv_secondPrimitive hg)
    rw [hder]
    exact hF1

theorem secondPrimitive_second_deriv_eq {g : ℝ → ℝ} (hg : Continuous g) (x : ℝ) :
    iteratedDeriv 2 (secondPrimitive g) x = g x := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  have hder : deriv (secondPrimitive g) = firstPrimitive g :=
    funext (deriv_secondPrimitive hg)
  rw [hder]
  exact deriv_firstPrimitive hg x

theorem hasCompactSupport_deriv {φ : ℝ → ℝ} (hφ : HasCompactSupport φ) :
    HasCompactSupport (deriv φ) :=
  hφ.deriv

theorem hasCompactSupport_iteratedDeriv_two {φ : ℝ → ℝ} (hφ : HasCompactSupport φ) :
    HasCompactSupport (iteratedDeriv 2 φ) := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  exact hφ.deriv.deriv

theorem HasCompactSupport.tendsto_zero_atBot {f : ℝ → ℝ} (hf : HasCompactSupport f) :
    Tendsto f atBot (𝓝 0) :=
  hf.is_zero_at_infty.mono_left atBot_le_cocompact

theorem HasCompactSupport.tendsto_zero_atTop {f : ℝ → ℝ} (hf : HasCompactSupport f) :
    Tendsto f atTop (𝓝 0) :=
  hf.is_zero_at_infty.mono_left atTop_le_cocompact

theorem Continuous.mul_integrable_of_hasCompactSupport_right
    {f k : ℝ → ℝ} (hf : Continuous f) (hk : Continuous k)
    (hk_comp : HasCompactSupport k) :
    Integrable (fun x : ℝ => f x * k x) :=
  (hf.mul hk).integrable_of_hasCompactSupport hk_comp.mul_left

theorem affine_contDiff_two (a b : ℝ) :
    ContDiff ℝ 2 (fun x : ℝ => a + b * x) := by
  fun_prop

theorem affine_iteratedDeriv_two (a b x : ℝ) :
    iteratedDeriv 2 (fun y : ℝ => a + b * y) x = 0 := by
  have h1 : deriv (fun y : ℝ => a + b * y) = fun _ : ℝ => b := by
    ext y
    simpa using (hasDerivAt_const_mul (x := y) b).deriv
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one, h1]
  simp

theorem affine_of_contDiff_two_second_deriv_zero
    {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F)
    (hF₂ : ∀ x, iteratedDeriv 2 F x = 0) :
    ∃ a b : ℝ, ∀ x, F x = a + b * x := by
  let b : ℝ := deriv F 0
  have hF_diff : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hF_deriv_diff : Differentiable ℝ (deriv F) := hF.differentiable_deriv_two
  have hderiv_deriv_zero : ∀ x, deriv (deriv F) x = 0 := by
    intro x
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using hF₂ x
  have hderiv_const : ∀ x, deriv F x = b := by
    intro x
    exact is_const_of_deriv_eq_zero hF_deriv_diff hderiv_deriv_zero x 0
  let G : ℝ → ℝ := fun x => F x - b * x
  have hG_hasDeriv : ∀ x, HasDerivAt G 0 x := by
    intro x
    have h :=
      ((hF_diff x).hasDerivAt.sub (hasDerivAt_const_mul (x := x) b))
    have h' : HasDerivAt G (deriv F x - b) x := by
      simpa [G] using h
    convert h' using 1
    rw [hderiv_const x]
    ring
  have hG_diff : Differentiable ℝ G := fun x => (hG_hasDeriv x).differentiableAt
  have hG_deriv_zero : ∀ x, deriv G x = 0 := fun x => (hG_hasDeriv x).deriv
  refine ⟨F 0, b, ?_⟩
  intro x
  have hconst : G x = G 0 :=
    is_const_of_deriv_eq_zero hG_diff hG_deriv_zero x 0
  dsimp [G, b] at hconst ⊢
  linarith

theorem right_convolution_second_deriv_eq
    {H ρ : ℝ → ℝ}
    (hHloc : LocallyIntegrable H volume)
    (hρc : HasCompactSupport ρ)
    (hρsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) :
    ∀ x, iteratedDeriv 2
        (H ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x =
      (H ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] iteratedDeriv 2 ρ) x := by
  have hρC1 : ContDiff ℝ 1 ρ := hρsmooth.of_le (by norm_num)
  have hρC2succ : ContDiff ℝ ((1 : ℕ∞) + 1) ρ :=
    hρsmooth.of_le (by exact_mod_cast le_top)
  have hρderivC1 : ContDiff ℝ 1 (deriv ρ) :=
    ContDiff.deriv' (𝕜 := ℝ) (n := 1) hρC2succ
  have hder1 :
      deriv (H ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) =
        H ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] deriv ρ := by
    ext x
    exact (hρc.hasDerivAt_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hHloc hρC1 x).deriv
  have hder2 :
      deriv (H ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] deriv ρ) =
        H ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] deriv (deriv ρ) := by
    ext x
    exact (hρc.deriv.hasDerivAt_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hHloc hρderivC1 x).deriv
  intro x
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one, hder1, hder2]
  congr 1
  ext y
  rw [iteratedDeriv_succ, iteratedDeriv_one]

theorem weak_right_convolution_second_deriv_zero
    {H ρ : ℝ → ℝ}
    (hρc : HasCompactSupport ρ)
    (hρsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hweak : WeakSecondDerivEq H (fun _ => 0)) :
    ∀ x, (H ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      iteratedDeriv 2 ρ) x = 0 := by
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
  have hψ₂ :
      iteratedDeriv 2 ψ = fun t : ℝ => iteratedDeriv 2 ρ (x - t) := by
    dsimp [ψ]
    ext t
    have h := congrFun (iteratedDeriv_comp_const_sub 2 ρ x) t
    simpa using h
  have hzero : (∫ t : ℝ, H t * iteratedDeriv 2 ρ (x - t)) = 0 := by
    have hweakx := hweak ψ hψsmooth hψcompact
    simpa [hψ₂] using hweakx
  rw [convolution_lsmul]
  simpa using hzero

def mollifierSeq (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := (1 : ℝ) / ((n : ℝ) + 1)
  rOut := (2 : ℝ) / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hden : 0 < (n : ℝ) + 1 := by positivity
    exact div_lt_div_of_pos_right (by norm_num : (1 : ℝ) < 2) hden

theorem mollifierSeq_rOut_tendsto :
    Tendsto (fun n => (mollifierSeq n).rOut) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => (2 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0)
  simpa [div_eq_mul_inv, one_div] using
    (tendsto_const_nhds (x := (2 : ℝ))).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem right_mollifier_eq_left (ρ H : ℝ → ℝ) (x : ℝ) :
    (H ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x =
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] H) x := by
  rw [convolution_lsmul, convolution_lsmul_swap]
  congr 1
  ext t
  simp [mul_comm]

theorem pinned_affine_of_affine {F : ℝ → ℝ}
    (hF : ∃ a b : ℝ, ∀ x, F x = a + b * x) :
    ∀ x, F x = F 0 + (F 1 - F 0) * x := by
  rcases hF with ⟨a, b, hF⟩
  intro x
  rw [hF x, hF 0, hF 1]
  ring

theorem weakSecondDerivEq_of_contDiff_two
    {A g : ℝ → ℝ}
    (hA : ContDiff ℝ 2 A)
    (hA2 : ∀ x, iteratedDeriv 2 A x = g x) :
    WeakSecondDerivEq A g := by
  intro φ hφ hφc
  have hA_diff : Differentiable ℝ A := hA.differentiable (by norm_num)
  have hA_deriv_diff : Differentiable ℝ (deriv A) := hA.differentiable_deriv_two
  have hA_cont : Continuous A := hA.continuous
  have hA_deriv_cont : Continuous (deriv A) := hA.continuous_deriv (by norm_num)
  have hA_two_cont : Continuous (iteratedDeriv 2 A) :=
    hA.continuous_iteratedDeriv 2 (by norm_num)
  have hφ_diff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφ_deriv_diff : Differentiable ℝ (deriv φ) :=
    by simpa [iteratedDeriv_one] using
      hφ.differentiable_iteratedDeriv 1 (by norm_num)
  have hφ_cont : Continuous φ := hφ.continuous
  have hφ_deriv_cont : Continuous (deriv φ) :=
    by simpa [iteratedDeriv_one] using
      hφ.continuous_iteratedDeriv 1 (by norm_num)
  have hφ_two_cont : Continuous (iteratedDeriv 2 φ) :=
    hφ.continuous_iteratedDeriv 2 (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ (((⊤ : ℕ∞) : WithTop ℕ∞))
      exact WithTop.coe_le_coe.2 le_top)
  have hφ_deriv_comp : HasCompactSupport (deriv φ) := hφc.deriv
  have hφ_two_comp : HasCompactSupport (iteratedDeriv 2 φ) :=
    hasCompactSupport_iteratedDeriv_two hφc
  have hAφ₂_int : Integrable (fun x : ℝ => A x * iteratedDeriv 2 φ x) :=
    Continuous.mul_integrable_of_hasCompactSupport_right
      hA_cont hφ_two_cont hφ_two_comp
  have hA'φ'_int : Integrable (fun x : ℝ => deriv A x * deriv φ x) :=
    Continuous.mul_integrable_of_hasCompactSupport_right hA_deriv_cont
      hφ_deriv_cont hφ_deriv_comp
  have hA''φ_int : Integrable (fun x : ℝ => iteratedDeriv 2 A x * φ x) :=
    Continuous.mul_integrable_of_hasCompactSupport_right hA_two_cont hφ_cont hφc
  have hAφ'_comp : HasCompactSupport (fun x : ℝ => A x * deriv φ x) :=
    hφ_deriv_comp.mul_left
  have hA'φ_comp : HasCompactSupport (fun x : ℝ => deriv A x * φ x) :=
    hφc.mul_left
  have hA_hasDeriv :
      ∀ x ∈ tsupport (deriv φ), HasDerivAt A (deriv A x) x := by
    intro x _hx
    exact (hA_diff x).hasDerivAt
  have hφ'_hasDeriv :
      ∀ x ∈ tsupport A, HasDerivAt (deriv φ) (iteratedDeriv 2 φ x) x := by
    intro x _hx
    have h := (hφ_deriv_diff x).hasDerivAt
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using h
  have hA'_hasDeriv :
      ∀ x ∈ tsupport φ, HasDerivAt (deriv A) (iteratedDeriv 2 A x) x := by
    intro x _hx
    have h := (hA_deriv_diff x).hasDerivAt
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using h
  have hφ_hasDeriv :
      ∀ x ∈ tsupport (deriv A), HasDerivAt φ (deriv φ x) x := by
    intro x _hx
    exact (hφ_diff x).hasDerivAt
  have hIBP₁_raw := MeasureTheory.integral_mul_deriv_eq_deriv_mul
    (A := ℝ) (u := A) (v := deriv φ) (u' := deriv A)
    (v' := fun x : ℝ => iteratedDeriv 2 φ x)
    (a' := (0 : ℝ)) (b' := (0 : ℝ))
    hA_hasDeriv hφ'_hasDeriv
    (by simpa [Pi.mul_def] using hAφ₂_int)
    (by simpa [Pi.mul_def] using hA'φ'_int)
    (by simpa [Pi.mul_def] using
      HasCompactSupport.tendsto_zero_atBot hAφ'_comp)
    (by simpa [Pi.mul_def] using
      HasCompactSupport.tendsto_zero_atTop hAφ'_comp)
  have hIBP₁ :
      (∫ x : ℝ, A x * iteratedDeriv 2 φ x) =
        -∫ x : ℝ, deriv A x * deriv φ x := by
    simpa [Pi.mul_def] using hIBP₁_raw
  have hIBP₂_raw := MeasureTheory.integral_mul_deriv_eq_deriv_mul
    (A := ℝ) (u := deriv A) (v := φ)
    (u' := fun x : ℝ => iteratedDeriv 2 A x) (v' := deriv φ)
    (a' := (0 : ℝ)) (b' := (0 : ℝ))
    hA'_hasDeriv hφ_hasDeriv
    (by simpa [Pi.mul_def] using hA'φ'_int)
    (by simpa [Pi.mul_def] using hA''φ_int)
    (by simpa [Pi.mul_def] using
      HasCompactSupport.tendsto_zero_atBot hA'φ_comp)
    (by simpa [Pi.mul_def] using
      HasCompactSupport.tendsto_zero_atTop hA'φ_comp)
  have hIBP₂ :
      (∫ x : ℝ, deriv A x * deriv φ x) =
        -∫ x : ℝ, iteratedDeriv 2 A x * φ x := by
    simpa [Pi.mul_def] using hIBP₂_raw
  calc
    (∫ x : ℝ, A x * iteratedDeriv 2 φ x)
        = -∫ x : ℝ, deriv A x * deriv φ x := hIBP₁
    _ = ∫ x : ℝ, iteratedDeriv 2 A x * φ x := by
      rw [hIBP₂]
      simp
    _ = ∫ x : ℝ, g x * φ x := by
      congr 1
      ext x
      rw [hA2 x]

theorem affine_of_continuous_weakSecondDerivEq_zero
    {H : ℝ → ℝ}
    (hH : Continuous H)
    (hweak : WeakSecondDerivEq H (fun _ => 0)) :
    ∃ a b : ℝ, ∀ x, H x = a + b * x := by
  let M : ℕ → ℝ → ℝ :=
    fun n => H ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (mollifierSeq n).normed volume
  have hHloc : LocallyIntegrable H volume := hH.locallyIntegrable
  have hM_pinned :
      ∀ n x, M n x = M n 0 + (M n 1 - M n 0) * x := by
    intro n x
    have hρc : HasCompactSupport ((mollifierSeq n).normed volume) :=
      (mollifierSeq n).hasCompactSupport_normed
    have hρsmooth :
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          ((mollifierSeq n).normed volume) :=
      (mollifierSeq n).contDiff_normed
    have hM_C2 : ContDiff ℝ 2 (M n) := by
      have hM_smooth :
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (M n) := by
        dsimp [M]
        exact hρc.contDiff_convolution_right
          (ContinuousLinearMap.lsmul ℝ ℝ) hHloc hρsmooth
      exact hM_smooth.of_le (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ (((⊤ : ℕ∞) : WithTop ℕ∞))
        exact WithTop.coe_le_coe.2 le_top)
    have hM₂ : ∀ y, iteratedDeriv 2 (M n) y = 0 := by
      intro y
      dsimp [M]
      calc
        iteratedDeriv 2
            (H ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              (mollifierSeq n).normed volume) y
            =
          (H ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            iteratedDeriv 2 ((mollifierSeq n).normed volume)) y :=
              right_convolution_second_deriv_eq hHloc hρc hρsmooth y
        _ = 0 :=
              weak_right_convolution_second_deriv_zero hρc hρsmooth hweak y
    exact pinned_affine_of_affine
      (affine_of_contDiff_two_second_deriv_zero hM_C2 hM₂) x
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
  refine ⟨H 0, H 1 - H 0, ?_⟩
  intro x
  have hleft : Tendsto
      (fun n => M n 0 + (M n 1 - M n 0) * x) atTop (𝓝 (H x)) := by
    have hx := hM_tendsto x
    have hpinned :
        (fun n => M n x) =
          fun n => M n 0 + (M n 1 - M n 0) * x := by
      ext n
      exact hM_pinned n x
    simpa [hpinned] using hx
  have hright : Tendsto
      (fun n => M n 0 + (M n 1 - M n 0) * x) atTop
      (𝓝 (H 0 + (H 1 - H 0) * x)) := by
    exact (hM_tendsto 0).add
      (((hM_tendsto 1).sub (hM_tendsto 0)).mul tendsto_const_nhds)
  exact tendsto_nhds_unique hleft hright

theorem contDiff_two_of_weak_second_deriv_eq_continuous
    {U g : ℝ → ℝ}
    (hU : Continuous U)
    (hg : Continuous g)
    (hweak : WeakSecondDerivEq U g) :
    ContDiff ℝ 2 U ∧ ∀ x, iteratedDeriv 2 U x = g x := by
  let A : ℝ → ℝ := secondPrimitive g
  let H : ℝ → ℝ := fun x => U x - A x
  have hA_C2 : ContDiff ℝ 2 A := by
    simpa [A] using secondPrimitive_contDiff_two hg
  have hA_cont : Continuous A := hA_C2.continuous
  have hA_weak : WeakSecondDerivEq A g := by
    apply weakSecondDerivEq_of_contDiff_two hA_C2
    intro x
    simpa [A] using secondPrimitive_second_deriv_eq hg x
  have hH_cont : Continuous H := hU.sub hA_cont
  have hH_weak : WeakSecondDerivEq H (fun _ => 0) := by
    intro φ hφ hφc
    have hφ_two_cont : Continuous (iteratedDeriv 2 φ) :=
      hφ.continuous_iteratedDeriv 2 (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ (((⊤ : ℕ∞) : WithTop ℕ∞))
        exact WithTop.coe_le_coe.2 le_top)
    have hφ_two_comp : HasCompactSupport (iteratedDeriv 2 φ) :=
      hasCompactSupport_iteratedDeriv_two hφc
    have hU_int : Integrable (fun x : ℝ => U x * iteratedDeriv 2 φ x) :=
      Continuous.mul_integrable_of_hasCompactSupport_right hU hφ_two_cont hφ_two_comp
    have hA_int : Integrable (fun x : ℝ => A x * iteratedDeriv 2 φ x) :=
      Continuous.mul_integrable_of_hasCompactSupport_right hA_cont hφ_two_cont hφ_two_comp
    calc
      (∫ x : ℝ, H x * iteratedDeriv 2 φ x)
          = (∫ x : ℝ, U x * iteratedDeriv 2 φ x) -
              ∫ x : ℝ, A x * iteratedDeriv 2 φ x := by
            rw [← integral_sub hU_int hA_int]
            congr 1
            ext x
            simp [H, A, sub_mul]
      _ = (∫ x : ℝ, g x * φ x) - ∫ x : ℝ, g x * φ x := by
            rw [hweak φ hφ hφc, hA_weak φ hφ hφc]
      _ = ∫ x : ℝ, (fun _ : ℝ => 0) x * φ x := by
            simp
  rcases affine_of_continuous_weakSecondDerivEq_zero hH_cont hH_weak with
    ⟨a, b, hH_aff⟩
  have hU_eq : U = fun x : ℝ => A x + (a + b * x) := by
    ext x
    have hx := hH_aff x
    dsimp [H] at hx
    dsimp [A]
    linarith
  constructor
  · rw [hU_eq]
    exact hA_C2.add (affine_contDiff_two a b)
  · intro x
    rw [hU_eq]
    have hlin :
        iteratedDeriv 2 (fun y : ℝ => A y + (a + b * y)) x =
          iteratedDeriv 2 A x +
            iteratedDeriv 2 (fun y : ℝ => a + b * y) x := by
      exact iteratedDeriv_fun_add hA_C2.contDiffAt
        (affine_contDiff_two a b).contDiffAt
    rw [hlin, affine_iteratedDeriv_two, add_zero]
    simpa [A] using secondPrimitive_second_deriv_eq hg x

#print axioms secondPrimitive_contDiff_two
#print axioms secondPrimitive_second_deriv_eq
#print axioms weakSecondDerivEq_of_contDiff_two
#print axioms affine_of_continuous_weakSecondDerivEq_zero
#print axioms contDiff_two_of_weak_second_deriv_eq_continuous

end ShenWork.PaperOne
