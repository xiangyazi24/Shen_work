import ShenWork.PaperOne.WholeLineMildMapContinuity
import ShenWork.PaperOne.WholeLineMildMap
import ShenWork.Paper1.WaveFrozenEllipticDep
import ShenWork.Paper1.WaveRotheClose
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-! Concrete profile-level pieces for the whole-line mild map. -/

def wholeLineProfileChemDuhamel (p : CMParams) (t : ℝ)
    (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s in Set.Icc (0 : ℝ) t,
    ShenWork.PaperOne.wholeLineHeatGradOp (t - s)
      (ShenWork.PaperOne.wholeLineFlux p U) x

def wholeLineProfileReactionDuhamel (p : CMParams) (t : ℝ)
    (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s in Set.Icc (0 : ℝ) t,
    ShenWork.PaperOne.wholeLineHeatOp (t - s)
      (ShenWork.PaperOne.wholeLineReaction p U) x

def wholeLineProfileMildMap (p : CMParams) (u0 : ℝ → ℝ) (t : ℝ)
    (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  ShenWork.PaperOne.wholeLineMildMap p u0 (fun _ => U) t x

theorem wholeLineProfileMildMap_decomp
    (p : CMParams) (u0 : ℝ → ℝ) (t : ℝ) (U : ℝ → ℝ) (x : ℝ) :
    wholeLineProfileMildMap p u0 t U x =
      ShenWork.PaperOne.wholeLineHeatOp t u0 x
        + (-p.χ) * wholeLineProfileChemDuhamel p t U x
        + wholeLineProfileReactionDuhamel p t U x := by
  unfold wholeLineProfileMildMap ShenWork.PaperOne.wholeLineMildMap
  unfold ShenWork.PaperOne.wholeLineFluxDuhamel
  unfold ShenWork.PaperOne.wholeLineReactionDuhamel
  unfold wholeLineProfileChemDuhamel wholeLineProfileReactionDuhamel
  ring

theorem wholeLineMildMap_continuous_of_terms
    {trap : (ℝ → ℝ) → Prop} {χ : ℝ}
    {wholeLineMildMap : (ℝ → ℝ) → ℝ → ℝ}
    {semigroupTerm : ℝ → ℝ}
    {chemDuhamel reactionDuhamel : (ℝ → ℝ) → ℝ → ℝ}
    (hdecomp : ∀ U x, wholeLineMildMap U x =
      semigroupTerm x + (-χ) * chemDuhamel U x + reactionDuhamel U x)
    (hchem : LocalUniformContinuousOn trap chemDuhamel)
    (hreaction : LocalUniformContinuousOn trap reactionDuhamel) :
    LocalUniformContinuousOn trap wholeLineMildMap :=
  wholeLineMildMap_continuous_in_U hdecomp hchem hreaction

theorem wholeLineProfileMildMap_continuous_of_duhamel_terms
    {trap : (ℝ → ℝ) → Prop} (p : CMParams) (u0 : ℝ → ℝ) (t : ℝ)
    (hchem : LocalUniformContinuousOn trap (wholeLineProfileChemDuhamel p t))
    (hreaction :
      LocalUniformContinuousOn trap (wholeLineProfileReactionDuhamel p t)) :
    LocalUniformContinuousOn trap (wholeLineProfileMildMap p u0 t) :=
  wholeLineMildMap_continuous_of_terms
    (χ := p.χ)
    (wholeLineMildMap := wholeLineProfileMildMap p u0 t)
    (semigroupTerm := fun x => ShenWork.PaperOne.wholeLineHeatOp t u0 x)
    (chemDuhamel := wholeLineProfileChemDuhamel p t)
    (reactionDuhamel := wholeLineProfileReactionDuhamel p t)
    (wholeLineProfileMildMap_decomp p u0 t) hchem hreaction

/-! Pointwise DCT bricks for the whole-line heat kernels. -/

theorem wholeLineHeatOp_tendsto_of_source_tendsto_of_uniform_bound
    {τ : ℝ} (hτ : 0 < τ) {Rs : ℕ → ℝ → ℝ} {R : ℝ → ℝ} {B : ℝ}
    (hRs_cont : ∀ n, Continuous (Rs n))
    (_hR_cont : Continuous R)
    (hRs_bound : ∀ n y, |Rs n y| ≤ B)
    (hR_bound : ∀ y, |R y| ≤ B)
    (hRs_lim : ∀ y, Tendsto (fun n : ℕ => Rs n y) atTop (𝓝 (R y)))
    (x : ℝ) :
    Tendsto (fun n : ℕ => ShenWork.PaperOne.wholeLineHeatOp τ (Rs n) x)
      atTop (𝓝 (ShenWork.PaperOne.wholeLineHeatOp τ R x)) := by
  let F : ℕ → ℝ → ℝ := fun n y => heatKernel τ (x - y) * Rs n y
  let G : ℝ → ℝ := fun y => heatKernel τ (x - y) * R y
  let bound : ℝ → ℝ := fun y => heatKernel τ (x - y) * B
  have hB_nonneg : 0 ≤ B := le_trans (abs_nonneg (R 0)) (hR_bound 0)
  have hbound_int : Integrable bound := by
    simpa [bound] using (heatKernel_translated_integrable hτ x).mul_const B
  have hF_meas :
      ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable (F n) volume := by
    refine Eventually.of_forall ?_
    intro n
    have hK : Continuous fun y : ℝ => heatKernel τ (x - y) := by
      unfold heatKernel
      fun_prop
    exact (hK.mul (hRs_cont n)).aestronglyMeasurable
  have h_bound :
      ∀ᶠ n : ℕ in atTop, ∀ᵐ y ∂volume, ‖F n y‖ ≤ bound y := by
    refine Eventually.of_forall ?_
    intro n
    refine Eventually.of_forall ?_
    intro y
    dsimp [F, bound]
    rw [abs_mul, abs_of_nonneg (heatKernel_nonneg hτ (x - y))]
    exact mul_le_mul_of_nonneg_left (hRs_bound n y)
      (heatKernel_nonneg hτ (x - y))
  have h_lim :
      ∀ᵐ y ∂volume, Tendsto (fun n : ℕ => F n y) atTop (𝓝 (G y)) := by
    refine Eventually.of_forall ?_
    intro y
    exact (hRs_lim y).const_mul (heatKernel τ (x - y))
  have hHeat :
      Tendsto (fun n : ℕ => heatSemigroup τ (Rs n) x)
        atTop (𝓝 (heatSemigroup τ R x)) := by
    have hInt :
        Tendsto (fun n : ℕ => ∫ y, F n y) atTop (𝓝 (∫ y, G y)) :=
      MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (μ := volume) (l := atTop) (F := F) (f := G)
        bound hF_meas h_bound hbound_int h_lim
    simpa [heatSemigroup, F, G] using hInt
  simpa [ShenWork.PaperOne.wholeLineHeatOp, modifiedSemigroup] using
    hHeat.const_mul (Real.exp (-τ))

theorem wholeLineHeatGradOp_tendsto_of_source_tendsto_of_uniform_bound
    {τ : ℝ} (hτ : 0 < τ) {Rs : ℕ → ℝ → ℝ} {R : ℝ → ℝ} {B : ℝ}
    (hRs_cont : ∀ n, Continuous (Rs n))
    (_hR_cont : Continuous R)
    (hRs_bound : ∀ n y, |Rs n y| ≤ B)
    (hR_bound : ∀ y, |R y| ≤ B)
    (hRs_lim : ∀ y, Tendsto (fun n : ℕ => Rs n y) atTop (𝓝 (R y)))
    (x : ℝ) :
    Tendsto (fun n : ℕ => ShenWork.PaperOne.wholeLineHeatGradOp τ (Rs n) x)
      atTop (𝓝 (ShenWork.PaperOne.wholeLineHeatGradOp τ R x)) := by
  let K : ℝ → ℝ := fun y =>
    Real.exp (-τ) * deriv (fun z : ℝ => heatKernel τ (z - y)) x
  let F : ℕ → ℝ → ℝ := fun n y => K y * Rs n y
  let G : ℝ → ℝ := fun y => K y * R y
  let bound : ℝ → ℝ := fun y => |K y| * B
  have hB_nonneg : 0 ≤ B := le_trans (abs_nonneg (R 0)) (hR_bound 0)
  have hbound_int : Integrable bound := by
    have hK :
        Integrable (fun y : ℝ =>
          |Real.exp (-τ) * deriv (fun z : ℝ => heatKernel τ (z - y)) x|) :=
      modifiedHeatKernel_deriv_abs_translated_integrable hτ x
    simpa [K, bound] using hK.mul_const B
  have hF_meas :
      ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable (F n) volume := by
    refine Eventually.of_forall ?_
    intro n
    have hK_meas : AEStronglyMeasurable K volume := by
      simpa [K] using
        (modifiedHeatKernel_deriv_translated_integrable hτ x).aestronglyMeasurable
    exact hK_meas.mul (hRs_cont n).aestronglyMeasurable
  have h_bound :
      ∀ᶠ n : ℕ in atTop, ∀ᵐ y ∂volume, ‖F n y‖ ≤ bound y := by
    refine Eventually.of_forall ?_
    intro n
    refine Eventually.of_forall ?_
    intro y
    dsimp [F, bound]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hRs_bound n y) (abs_nonneg (K y))
  have h_lim :
      ∀ᵐ y ∂volume, Tendsto (fun n : ℕ => F n y) atTop (𝓝 (G y)) := by
    refine Eventually.of_forall ?_
    intro y
    exact (hRs_lim y).const_mul (K y)
  have hInt :
      Tendsto (fun n : ℕ => ∫ y, F n y) atTop (𝓝 (∫ y, G y)) :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := atTop) (F := F) (f := G)
      bound hF_meas h_bound hbound_int h_lim
  simpa [ShenWork.PaperOne.wholeLineHeatGradOp, K, F, G, mul_assoc] using hInt

theorem heatKernel_eq_zero_of_nonpos {τ : ℝ} (hτ : τ ≤ 0) (z : ℝ) :
    heatKernel τ z = 0 := by
  unfold heatKernel
  have hprod : 4 * Real.pi * τ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 4 * Real.pi) hτ
  have hsqrt : Real.sqrt (4 * Real.pi * τ) = 0 :=
    Real.sqrt_eq_zero'.mpr hprod
  rw [hsqrt]
  ring

theorem wholeLineHeatOp_eq_zero_of_nonpos {τ : ℝ} (hτ : τ ≤ 0)
    (f : ℝ → ℝ) (x : ℝ) :
    ShenWork.PaperOne.wholeLineHeatOp τ f x = 0 := by
  unfold ShenWork.PaperOne.wholeLineHeatOp modifiedSemigroup heatSemigroup
  have hzero :
      (fun y : ℝ => heatKernel τ (x - y) * f y) = fun _ : ℝ => 0 := by
    funext y
    rw [heatKernel_eq_zero_of_nonpos hτ (x - y)]
    ring
  rw [hzero]
  simp

theorem wholeLineHeatGradOp_eq_zero_of_nonpos {τ : ℝ} (hτ : τ ≤ 0)
    (f : ℝ → ℝ) (x : ℝ) :
    ShenWork.PaperOne.wholeLineHeatGradOp τ f x = 0 := by
  unfold ShenWork.PaperOne.wholeLineHeatGradOp
  have hzero :
      (fun y : ℝ =>
        Real.exp (-τ) *
          (deriv (fun z : ℝ => heatKernel τ (z - y)) x * f y))
        = fun _ : ℝ => 0 := by
    funext y
    have hconst :
        (fun z : ℝ => heatKernel τ (z - y)) = fun _ : ℝ => 0 := by
      funext z
      exact heatKernel_eq_zero_of_nonpos hτ (z - y)
    rw [hconst, deriv_const]
    ring
  rw [hzero]
  simp

theorem wholeLineHeatOp_abs_le_of_uniform_bound
    {τ B : ℝ} (hτ : 0 ≤ τ) (hB : 0 ≤ B) {f : ℝ → ℝ}
    (hf_cont : Continuous f) (hf_bound : ∀ y, |f y| ≤ B) (x : ℝ) :
    |ShenWork.PaperOne.wholeLineHeatOp τ f x| ≤ B := by
  by_cases hτpos : 0 < τ
  · have h :=
      modifiedSemigroup_Linfty_bound (f := f) (M := B)
        hf_bound hτpos hB hf_cont.aestronglyMeasurable x
    have hexp_le_one : Real.exp (-τ) ≤ 1 := by
      exact Real.exp_le_one_iff.mpr (by linarith)
    calc
      |ShenWork.PaperOne.wholeLineHeatOp τ f x|
          ≤ Real.exp (-τ) * B := by
            simpa [ShenWork.PaperOne.wholeLineHeatOp] using h
      _ ≤ 1 * B := mul_le_mul_of_nonneg_right hexp_le_one hB
      _ = B := by ring
  · have hτle : τ ≤ 0 := le_of_not_gt hτpos
    have hτ0 : τ = 0 := le_antisymm hτle hτ
    rw [hτ0, wholeLineHeatOp_eq_zero_of_nonpos le_rfl]
    simpa using hB

theorem wholeLineHeatGradOp_abs_le_of_uniform_bound
    {τ B : ℝ} (hτ : 0 < τ) (hB : 0 ≤ B) {f : ℝ → ℝ}
    (hf_bound : ∀ y, |f y| ≤ B) (x : ℝ) :
    |ShenWork.PaperOne.wholeLineHeatGradOp τ f x| ≤
      Real.exp (-τ) * ((2 / Real.sqrt (4 * Real.pi * τ)) * B) := by
  simpa [ShenWork.PaperOne.wholeLineHeatGradOp] using
    modifiedHeatKernel_deriv_convolution_bounded_abs_le
      (t := τ) (M := B) hτ hB (f := f) hf_bound x

/-! Source-level continuity bricks. -/

def wholeLineReactionSourceBound (p : CMParams) (M : ℝ) : ℝ :=
  M * (1 + M ^ p.α)

def wholeLineFluxSourceBound (p : CMParams) (M : ℝ) : ℝ :=
  M ^ p.m * M ^ p.γ

theorem wholeLineReactionSourceBound_nonneg
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ wholeLineReactionSourceBound p M := by
  unfold wholeLineReactionSourceBound
  positivity

theorem wholeLineFluxSourceBound_nonneg
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ wholeLineFluxSourceBound p M := by
  unfold wholeLineFluxSourceBound
  exact mul_nonneg (Real.rpow_nonneg hM p.m) (Real.rpow_nonneg hM p.γ)

theorem wholeLineReaction_continuous_constantBarrier
    (p : CMParams) {M : ℝ} {U : ℝ → ℝ}
    (hU : InConstantBarrierTrap M U) :
    Continuous (ShenWork.PaperOne.wholeLineReaction p U) := by
  unfold ShenWork.PaperOne.wholeLineReaction
  exact hU.1.1.mul
    (continuous_const.sub
      ((Real.continuous_rpow_const (by linarith [p.hα])).comp hU.1.1))

theorem wholeLineReaction_abs_bound_constantBarrier
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) {U : ℝ → ℝ}
    (hU : InConstantBarrierTrap M U) :
    ∀ x, |ShenWork.PaperOne.wholeLineReaction p U x|
      ≤ wholeLineReactionSourceBound p M := by
  intro x
  have hUx0 : 0 ≤ U x := (hU.2 x).1
  have hUxM : U x ≤ M := (hU.2 x).2
  have hpow0 : 0 ≤ (U x) ^ p.α := Real.rpow_nonneg hUx0 p.α
  have hpowM : (U x) ^ p.α ≤ M ^ p.α :=
    Real.rpow_le_rpow hUx0 hUxM (by linarith [p.hα])
  have hUabs : |U x| ≤ M := by
    rw [abs_of_nonneg hUx0]
    exact hUxM
  have hfac : |1 - (U x) ^ p.α| ≤ 1 + M ^ p.α := by
    calc
      |1 - (U x) ^ p.α| = |(1 : ℝ) + -((U x) ^ p.α)| := by ring_nf
      _ ≤ |(1 : ℝ)| + |-((U x) ^ p.α)| := abs_add_le _ _
      _ = 1 + (U x) ^ p.α := by rw [abs_one, abs_neg, abs_of_nonneg hpow0]
      _ ≤ 1 + M ^ p.α := add_le_add le_rfl hpowM
  unfold ShenWork.PaperOne.wholeLineReaction wholeLineReactionSourceBound
  rw [abs_mul]
  exact mul_le_mul hUabs hfac (abs_nonneg _) hM

theorem wholeLineFlux_continuous_constantBarrier
    (p : CMParams) {M : ℝ} {U : ℝ → ℝ}
    (hU : InConstantBarrierTrap M U) :
    Continuous (ShenWork.PaperOne.wholeLineFlux p U) := by
  have hpow : Continuous fun x : ℝ => (U x) ^ p.m :=
    (Real.continuous_rpow_const (by linarith [p.hm])).comp hU.1.1
  have hderiv :
      Continuous fun x : ℝ =>
        deriv (wholeLineResolvent (fun y => (U y) ^ p.γ)) x := by
    have hfun :
        (fun x : ℝ =>
          deriv (wholeLineResolvent (fun y => (U y) ^ p.γ)) x)
        = fun x : ℝ => deriv (frozenElliptic p U) x := by
      funext x
      congr 1
      funext z
      rw [wholeLineResolvent_eq_Psi]
      rfl
    rw [hfun]
    exact frozenElliptic_deriv_continuous p hU.1 (fun x => (hU.2 x).1)
  simpa [ShenWork.PaperOne.wholeLineFlux] using hpow.mul hderiv

theorem wholeLineFlux_abs_bound_constantBarrier
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) {U : ℝ → ℝ}
    (hU : InConstantBarrierTrap M U) :
    ∀ x, |ShenWork.PaperOne.wholeLineFlux p U x|
      ≤ wholeLineFluxSourceBound p M := by
  have hMm : 0 ≤ M ^ p.m := Real.rpow_nonneg hM p.m
  have hMγ : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM p.γ
  have hsource_cont : Continuous fun y => (U y) ^ p.γ :=
    (Real.continuous_rpow_const (by linarith [p.hγ])).comp hU.1.1
  have hsource_bound : ∀ y, |(U y) ^ p.γ| ≤ M ^ p.γ := by
    intro y
    rw [abs_of_nonneg (Real.rpow_nonneg (hU.2 y).1 p.γ)]
    exact Real.rpow_le_rpow (hU.2 y).1 (hU.2 y).2 (by linarith [p.hγ])
  have hderiv_bound :
      ∀ x,
        |deriv (wholeLineResolvent (fun y => (U y) ^ p.γ)) x| ≤ M ^ p.γ :=
    wholeLineResolventDeriv_sup_le hMγ hsource_cont hsource_bound
  intro x
  have hpow_bound : |(U x) ^ p.m| ≤ M ^ p.m := by
    rw [abs_of_nonneg (Real.rpow_nonneg (hU.2 x).1 p.m)]
    exact Real.rpow_le_rpow (hU.2 x).1 (hU.2 x).2 (by linarith [p.hm])
  unfold ShenWork.PaperOne.wholeLineFlux wholeLineFluxSourceBound
  rw [abs_mul]
  exact mul_le_mul hpow_bound (hderiv_bound x) (abs_nonneg _) hMm

theorem locallyUniformConverges_mul_global_bound
    {fs gs : ℕ → ℝ → ℝ} {f g : ℝ → ℝ} {Bf Bg : ℝ}
    (hf : LocallyUniformConverges fs f)
    (hg : LocallyUniformConverges gs g)
    (hBf0 : 0 ≤ Bf) (hBg0 : 0 ≤ Bg)
    (hfb : ∀ x, |f x| ≤ Bf) (hgb : ∀ x, |g x| ≤ Bg) :
    LocallyUniformConverges (fun n x => fs n x * gs n x)
      (fun x => f x * g x) := by
  intro R hR ε hε
  let δ : ℝ := ε / (2 * (Bg + Bf + 1))
  have hden : 0 < 2 * (Bg + Bf + 1) := by nlinarith
  have hδ : 0 < δ := div_pos hε hden
  filter_upwards [hf R hR δ hδ, hg R hR δ hδ, hg R hR 1 zero_lt_one]
    with n hfn hgn hg1
  intro x hx
  have hgs_bound : |gs n x| ≤ Bg + 1 := by
    calc
      |gs n x| = |g x + (gs n x - g x)| := by ring_nf
      _ ≤ |g x| + |gs n x - g x| := abs_add_le _ _
      _ ≤ Bg + 1 := by linarith [hgb x, (hg1 x hx).le]
  have hmain :
      |fs n x * gs n x - f x * g x|
        ≤ |fs n x - f x| * |gs n x|
          + |f x| * |gs n x - g x| := by
    calc
      |fs n x * gs n x - f x * g x|
          = |(fs n x - f x) * gs n x
              + f x * (gs n x - g x)| := by ring_nf
      _ ≤ |(fs n x - f x) * gs n x|
            + |f x * (gs n x - g x)| := abs_add_le _ _
      _ = |fs n x - f x| * |gs n x|
            + |f x| * |gs n x - g x| := by rw [abs_mul, abs_mul]
  have hterm₁ :
      |fs n x - f x| * |gs n x| ≤ δ * (Bg + 1) :=
    mul_le_mul (hfn x hx).le hgs_bound (abs_nonneg _) hδ.le
  have hterm₂ : |f x| * |gs n x - g x| ≤ Bf * δ :=
    mul_le_mul (hfb x) (hgn x hx).le (abs_nonneg _) hBf0
  calc
    |fs n x * gs n x - f x * g x|
        ≤ |fs n x - f x| * |gs n x|
          + |f x| * |gs n x - g x| := hmain
    _ ≤ δ * (Bg + 1) + Bf * δ := add_le_add hterm₁ hterm₂
    _ = δ * (Bg + Bf + 1) := by ring
    _ < ε := by
      unfold δ
      have hpos : 0 < Bg + Bf + 1 := by nlinarith
      field_simp [ne_of_gt hden]
      nlinarith

theorem wholeLinePower_source_locallyUniform_constantBarrier
    {a M : ℝ} (ha : 1 ≤ a) (hM : 0 ≤ M)
    {seq : ℕ → ℝ → ℝ} {u : ℝ → ℝ}
    (hseq : ∀ n, InConstantBarrierTrap M (seq n))
    (hu : InConstantBarrierTrap M u)
    (hconv : LocallyUniformConverges seq u) :
    LocallyUniformConverges (fun n x => (seq n x) ^ a)
      (fun x => (u x) ^ a) := by
  intro R hR ε hε
  set L := rpowLip a M with hL
  have hL0 : 0 ≤ L := by
    simpa [hL] using rpowLip_nonneg ha hM
  let δ : ℝ := ε / (L + 1)
  have hden : 0 < L + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have hLip := rpow_m_lipschitz_on_Icc (m := a) (M := M) ha hM
  filter_upwards [hconv R hR δ hδ] with n hn
  intro x hx
  have hdist := hLip
    (Set.mem_Icc.mpr ⟨(hseq n).2 x |>.1, (hseq n).2 x |>.2⟩)
    (Set.mem_Icc.mpr ⟨(hu.2 x).1, (hu.2 x).2⟩)
  rw [edist_dist, edist_dist] at hdist
  have hd :
      dist ((seq n x) ^ a) ((u x) ^ a)
        ≤ (Real.toNNReal L : ℝ) * dist (seq n x) (u x) := by
    rw [← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at hdist
    exact hdist
  rw [Real.coe_toNNReal _ hL0] at hd
  rw [Real.dist_eq, Real.dist_eq] at hd
  calc
    |(seq n x) ^ a - (u x) ^ a| ≤ L * |seq n x - u x| := hd
    _ ≤ L * δ := mul_le_mul_of_nonneg_left (hn x hx).le hL0
    _ < ε := by
      unfold δ
      have hLt : L < L + 1 := by linarith
      calc
        L * (ε / (L + 1)) < (L + 1) * (ε / (L + 1)) :=
          mul_lt_mul_of_pos_right hLt hδ
        _ = ε := by field_simp [ne_of_gt hden]

theorem wholeLineReaction_source_locallyUniform_constantBarrier
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M)
    {seq : ℕ → ℝ → ℝ} {u : ℝ → ℝ}
    (hseq : ∀ n, InConstantBarrierTrap M (seq n))
    (hu : InConstantBarrierTrap M u)
    (hconv : LocallyUniformConverges seq u) :
    LocallyUniformConverges
      (fun n x => ShenWork.PaperOne.wholeLineReaction p (seq n) x)
      (fun x => ShenWork.PaperOne.wholeLineReaction p u x) := by
  intro R hR ε hε
  set L := reactionLip p.α M with hL
  have hL0 : 0 ≤ L := by
    simpa [hL] using reactionLip_nonneg p.hα hM
  let δ : ℝ := ε / (L + 1)
  have hden : 0 < L + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have hLip := reaction_lipschitz_on_Icc (a := p.α) (M := M) p.hα hM
  filter_upwards [hconv R hR δ hδ] with n hn
  intro x hx
  have hdist := hLip
    (Set.mem_Icc.mpr ⟨(hseq n).2 x |>.1, (hseq n).2 x |>.2⟩)
    (Set.mem_Icc.mpr ⟨(hu.2 x).1, (hu.2 x).2⟩)
  rw [edist_dist, edist_dist] at hdist
  have hd :
      dist (reactionFun p.α (seq n x)) (reactionFun p.α (u x))
        ≤ (Real.toNNReal L : ℝ) * dist (seq n x) (u x) := by
    rw [← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at hdist
    exact hdist
  rw [Real.coe_toNNReal _ hL0] at hd
  rw [Real.dist_eq, Real.dist_eq] at hd
  calc
    |ShenWork.PaperOne.wholeLineReaction p (seq n) x
        - ShenWork.PaperOne.wholeLineReaction p u x|
        = |reactionFun p.α (seq n x) - reactionFun p.α (u x)| := by
            rfl
    _ ≤ L * |seq n x - u x| := hd
    _ ≤ L * δ := mul_le_mul_of_nonneg_left (hn x hx).le hL0
    _ < ε := by
      unfold δ
      have hLt : L < L + 1 := by linarith
      calc
        L * (ε / (L + 1)) < (L + 1) * (ε / (L + 1)) :=
          mul_lt_mul_of_pos_right hLt hδ
        _ = ε := by field_simp [ne_of_gt hden]

theorem frozenEllipticDerivDependence_constantBarrier
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) :
    FrozenEllipticDerivDependence p (InConstantBarrierTrap M) := by
  intro seq u hseq hu hconv
  have hu_cunif : IsCUnifBdd u := hu.1
  have hu_nn : ∀ x, 0 ≤ u x := fun x => (hu.2 x).1
  have hu_le : ∀ x, u x ≤ M := fun x => (hu.2 x).2
  have hsn_cunif : ∀ n, IsCUnifBdd (seq n) := fun n => (hseq n).1
  have hsn_nn : ∀ n x, 0 ≤ seq n x := fun n x => ((hseq n).2 x).1
  have hsn_le : ∀ n x, seq n x ≤ M := fun n x => ((hseq n).2 x).2
  have hγ1 : (1 : ℝ) ≤ p.γ := p.hγ
  set L := rpowLip p.γ M with hL
  have hL0 : 0 ≤ L := rpowLip_nonneg hγ1 hM
  intro R hR ε hε
  set K : ℝ := 2 * M ^ p.γ * Real.exp R with hK
  have hK0 : 0 ≤ K := by positivity
  have hexp0 :
      Tendsto (fun R' : ℝ => Real.exp (-R')) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have htail_small :
      ∀ᶠ R' : ℝ in atTop, K * Real.exp (-R') < ε / 2 := by
    have hKtail :
        Tendsto (fun R' : ℝ => K * Real.exp (-R')) atTop (𝓝 0) := by
      simpa using hexp0.const_mul K
    exact hKtail.eventually (eventually_lt_nhds (by linarith))
  obtain ⟨R', htailR', hR'ge⟩ :=
    (htail_small.and (eventually_ge_atTop R)).exists
  have hRR' : R ≤ R' := hR'ge
  have hR'0 : 0 < R' := lt_of_lt_of_le hR hRR'
  have hLp1 : (0 : ℝ) < L + 1 := by linarith
  set s0 : ℝ := ε / (2 * (L + 1)) with hs0def
  have hs0pos : 0 < s0 := by
    rw [hs0def]
    positivity
  filter_upwards [hconv R' hR'0 s0 hs0pos] with n hn
  intro x hx
  have hs_bd : ∀ y ∈ Set.Icc (-R') R', |seq n y - u y| ≤ s0 :=
    fun y hy => le_of_lt (hn y hy)
  have habs := frozenElliptic_deriv_diff_abs_le p
    (hsn_cunif n) (hsn_nn n) hu_cunif hu_nn x
  have hsplit := deriv_diff_integral_split_le p
    (M := M) (R := R) (R' := R') (s := s0)
    hM (hsn_nn n) (hsn_le n) hu_nn hu_le hs_bd hR hRR' hx
    (hsn_cunif n) hu_cunif
  have hchain :
      |deriv (frozenElliptic p (seq n)) x
          - deriv (frozenElliptic p u) x|
        ≤ L * s0 + K * Real.exp (-R') := by
    refine le_trans habs ?_
    have h2 :
        (1 : ℝ) / 2 * (∫ y, Real.exp (-|x - y|)
          * |(seq n y) ^ p.γ - (u y) ^ p.γ|)
          ≤ 1 / 2 * (2 * (L * s0)
            + 4 * (M ^ p.γ * (Real.exp R * Real.exp (-R')))) :=
      mul_le_mul_of_nonneg_left hsplit (by norm_num)
    refine le_trans h2 (le_of_eq ?_)
    rw [hK]
    ring
  have hinner_le : L * s0 ≤ ε / 2 := by
    have hstep : L * s0 ≤ (L + 1) * s0 :=
      mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hs0pos)
    have heq : (L + 1) * s0 = ε / 2 := by
      rw [hs0def]
      field_simp [ne_of_gt hLp1]
    linarith
  calc
    |deriv (frozenElliptic p (seq n)) x
        - deriv (frozenElliptic p u) x|
      ≤ L * s0 + K * Real.exp (-R') := hchain
    _ < ε / 2 + ε / 2 := by linarith [hinner_le, htailR']
    _ = ε := by ring

theorem wholeLineResolventDeriv_source_locallyUniform_constantBarrier
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M)
    {seq : ℕ → ℝ → ℝ} {u : ℝ → ℝ}
    (hseq : ∀ n, InConstantBarrierTrap M (seq n))
    (hu : InConstantBarrierTrap M u)
    (hconv : LocallyUniformConverges seq u) :
    LocallyUniformConverges
      (fun n x =>
        deriv (wholeLineResolvent
          (fun y => (seq n y) ^ p.γ)) x)
      (fun x =>
        deriv (wholeLineResolvent
          (fun y => (u y) ^ p.γ)) x) := by
  have h := frozenEllipticDerivDependence_constantBarrier p hM
    seq u hseq hu hconv
  have hseqfun :
      (fun n x =>
        deriv (wholeLineResolvent
          (fun y => (seq n y) ^ p.γ)) x)
      = fun n x => deriv (frozenElliptic p (seq n)) x := by
    funext n x
    congr 1
    funext z
    rw [wholeLineResolvent_eq_Psi]
    rfl
  have hufun :
      (fun x =>
        deriv (wholeLineResolvent
          (fun y => (u y) ^ p.γ)) x)
      = fun x => deriv (frozenElliptic p u) x := by
    funext x
    congr 1
    funext z
    rw [wholeLineResolvent_eq_Psi]
    rfl
  simpa [hseqfun, hufun] using h

theorem wholeLineFlux_source_locallyUniform_constantBarrier
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M)
    {seq : ℕ → ℝ → ℝ} {u : ℝ → ℝ}
    (hseq : ∀ n, InConstantBarrierTrap M (seq n))
    (hu : InConstantBarrierTrap M u)
    (hconv : LocallyUniformConverges seq u) :
    LocallyUniformConverges
      (fun n x => ShenWork.PaperOne.wholeLineFlux p (seq n) x)
      (fun x => ShenWork.PaperOne.wholeLineFlux p u x) := by
  have hm := wholeLinePower_source_locallyUniform_constantBarrier
    (a := p.m) p.hm hM hseq hu hconv
  have hd := wholeLineResolventDeriv_source_locallyUniform_constantBarrier
    p hM hseq hu hconv
  have hMm : 0 ≤ M ^ p.m := Real.rpow_nonneg hM p.m
  have hMγ : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM p.γ
  have hpow_bound : ∀ x, |(u x) ^ p.m| ≤ M ^ p.m := by
    intro x
    rw [abs_of_nonneg (Real.rpow_nonneg (hu.2 x).1 p.m)]
    exact Real.rpow_le_rpow (hu.2 x).1 (hu.2 x).2 (by linarith [p.hm])
  have hsource_cont : Continuous fun y => (u y) ^ p.γ :=
    (Real.continuous_rpow_const (by linarith [p.hγ])).comp hu.1.1
  have hsource_bound : ∀ y, |(u y) ^ p.γ| ≤ M ^ p.γ := by
    intro y
    rw [abs_of_nonneg (Real.rpow_nonneg (hu.2 y).1 p.γ)]
    exact Real.rpow_le_rpow (hu.2 y).1 (hu.2 y).2 (by linarith [p.hγ])
  have hderiv_bound :
      ∀ x,
        |deriv (wholeLineResolvent
          (fun y => (u y) ^ p.γ)) x| ≤ M ^ p.γ :=
    wholeLineResolventDeriv_sup_le
      hMγ hsource_cont hsource_bound
  have hprod := locallyUniformConverges_mul_global_bound
    hm hd hMm hMγ hpow_bound hderiv_bound
  simpa [ShenWork.PaperOne.wholeLineFlux] using hprod

def wholeLineReactionDuhamelTermContinuity
    (p : CMParams) (M t : ℝ) : Prop :=
  LocalUniformContinuousOn (InConstantBarrierTrap M)
    (wholeLineProfileReactionDuhamel p t)

def wholeLineChemDuhamelTermContinuity
    (p : CMParams) (M t : ℝ) : Prop :=
  LocalUniformContinuousOn (InConstantBarrierTrap M)
    (wholeLineProfileChemDuhamel p t)

theorem wholeLineProfileMildMap_continuous_of_concrete_term_props
    (p : CMParams) (u0 : ℝ → ℝ) {M t : ℝ}
    (hchem : wholeLineChemDuhamelTermContinuity p M t)
    (hreaction : wholeLineReactionDuhamelTermContinuity p M t) :
    LocalUniformContinuousOn (InConstantBarrierTrap M)
      (wholeLineProfileMildMap p u0 t) :=
  wholeLineProfileMildMap_continuous_of_duhamel_terms p u0 t hchem hreaction

#print axioms wholeLineReaction_source_locallyUniform_constantBarrier
#print axioms wholeLineResolventDeriv_source_locallyUniform_constantBarrier
#print axioms wholeLineFlux_source_locallyUniform_constantBarrier
#print axioms wholeLineProfileMildMap_continuous_of_concrete_term_props

end ShenWork.Paper1
