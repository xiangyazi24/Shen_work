/-
  # `ShenWork.Paper2.ChemMildDifferentiableOn`

  P2-T11 step (ii), the **endpoint extension** of the chemotaxis-leg interchange.

  The committed `chemLeg_interior_hasDerivAt` (`ChemMildInterchange.lean:248`) gives
  `HasDerivAt (chemLitLeg t₀ Q) (chemLitLeg₂ t₀ Q x₀) x₀` only for interior
  `x₀ ∈ Set.Ioo 0 1`.  The global-`ℝ` differentiability is unavailable (the chemotaxis
  leg's spectral coefficients do not decay), but the downstream cosine-coefficient IBP
  only integrates over `[0,1]`, so we only need

      `DifferentiableOn ℝ (chemLitLeg t₀ Q) (Set.Icc 0 1)`.

  The route:

  * `chemLitLeg₂_continuousOn_Icc` — the second-order leg is **continuous on `[0,1]`**
    by continuity-under-the-interval-integral (`continuousWithinAt_of_dominated_interval`)
    with the brick-3 integrable dominator and per-slice second-derivative continuity
    (`ContDiff ℝ 2`).
  * `chemLitLeg_continuousOn_Icc` — the first-order leg is continuous on `[0,1]`, same
    mechanism with the `(t₀−s)^{−1/2}` gradient dominator.
  * `chemLeg_differentiableOn_Icc` — combine the interior `HasDerivAt` with
    Mathlib's `hasDerivWithinAt_Ici/Iic_of_tendsto_deriv` at the endpoints.

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.Paper2.ChemMildInterchange
import ShenWork.PDE.IntervalSemigroupNeumann

open MeasureTheory Filter Topology Set
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator cosineCoeffs weightedHeatHessConst weightedHeatHessConst_nonneg
   neumannHeatSecondDeriv_Ctheta_to_Linfty
   intervalFullSemigroupOperator_s_dependent_deriv_aestronglyMeasurable_x₀
   intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t)
open ShenWork.IntervalDomain (intervalMeasure)

namespace ShenWork.Paper2

open ShenWork.IntervalFullKernelInterchange
open ShenWork.IntervalResolverPositivity (intervalNeumannFullKernel_cosineKernel_identity)

/-! ## Per-slice continuity of the leg integrands on `ℝ` -/

/-- For `0 < τ`, continuous slice `f` with bounded cosine coefficients, the **second**
spatial derivative `x ↦ ∂ₓₓ S(τ) f x` is continuous on `ℝ` (`ContDiff ℝ 2 ⟹
continuous iterated derivative). -/
theorem secondDeriv_semigroup_continuous
    {τ : ℝ} (hτ : 0 < τ) {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs f n| ≤ M) :
    Continuous (fun x : ℝ =>
      deriv (fun z : ℝ => deriv (fun w : ℝ => intervalFullSemigroupOperator τ f w) z) x) := by
  have hC2 : ContDiff ℝ 2 (fun x => intervalFullSemigroupOperator τ f x) :=
    intervalFullSemigroupOperator_contDiff_two_unconditional
      τ hτ f hf hM (fun x => intervalNeumannFullKernel_cosineKernel_identity hτ x)
  -- `deriv (S τ f)` is `ContDiff ℝ 1`, hence its derivative is continuous.
  have hC1 : ContDiff ℝ 1 (deriv (fun x => intervalFullSemigroupOperator τ f x)) := by
    have : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
    exact (this ▸ hC2).deriv'
  have hcont : Continuous (deriv (deriv (fun x => intervalFullSemigroupOperator τ f x))) :=
    hC1.continuous_deriv (le_refl 1)
  exact hcont

/-- For `0 < τ`, the **first** spatial derivative `x ↦ ∂ₓ S(τ) f x` is continuous on `ℝ`. -/
theorem firstDeriv_semigroup_continuous
    {τ : ℝ} (hτ : 0 < τ) {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs f n| ≤ M) :
    Continuous (fun x : ℝ =>
      deriv (fun z : ℝ => intervalFullSemigroupOperator τ f z) x) := by
  have hC2 : ContDiff ℝ 2 (fun x => intervalFullSemigroupOperator τ f x) :=
    intervalFullSemigroupOperator_contDiff_two_unconditional
      τ hτ f hf hM (fun x => intervalNeumannFullKernel_cosineKernel_identity hτ x)
  have hle : (1 : WithTop ℕ∞) ≤ 2 := by norm_num
  exact hC2.continuous_deriv hle

/-! ## Continuity of the leg integrals on `[0,1]` (dominated convergence in `x`) -/

/-- **`chemLitLeg₂_continuousWithinAt_Icc`.**  The second-order chemotaxis leg
`chemLitLeg₂ t₀ Q` is continuous-within-`[0,1]` at every `x₀ ∈ [0,1]`.

PROOF: `continuousWithinAt_of_dominated_interval` with the brick-3 dominator
`bound s = weightedHeatHessConst θ · (t₀−s)^{−1+θ/2} · HQ` (integrable on `[0,t₀]`).
The per-slice integrand is continuous in `x` on all of `ℝ` (`secondDeriv_semigroup_continuous`,
from `ContDiff ℝ 2`); the bound holds for `x ∈ [0,1]` via
`neumannHeatSecondDeriv_Ctheta_to_Linfty`; a.e.-measurability per `x` is the committed
`intervalFullSemigroupOperator_s_dependent_secondDeriv_aestronglyMeasurable_x₀`. -/
theorem chemLitLeg₂_continuousWithinAt_Icc {t₀ θ CQ HQ : ℝ} {Q : ℝ → ℝ → ℝ}
    (ht₀ : 0 < t₀) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hHQ_nn : 0 ≤ HQ)
    (hQmeas : Measurable (Function.uncurry Q))
    (hQint : ∀ s, Integrable (Q s) (intervalMeasure 1))
    (hQbdd : ∀ s y, |Q s y| ≤ CQ)
    {M : ℝ} (hQcont : ∀ s ∈ Set.Ioo (0:ℝ) t₀, Continuous (Q s))
    (hQcoeff : ∀ s ∈ Set.Ioo (0:ℝ) t₀, ∀ n, |cosineCoeffs (Q s) n| ≤ M)
    (hQholder : ∀ s ∈ Set.Ioo (0:ℝ) t₀, ∀ a b, a ∈ Set.Icc (0:ℝ) 1 →
      b ∈ Set.Icc (0:ℝ) 1 → |Q s a - Q s b| ≤ HQ * |a - b| ^ θ)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0:ℝ) 1) :
    ContinuousWithinAt (chemLitLeg₂ t₀ Q) (Set.Icc (0:ℝ) 1) x₀ := by
  classical
  have hQ_ae : AEStronglyMeasurable (Function.uncurry Q)
      ((volume.restrict (Set.uIoc (0:ℝ) t₀)).prod (intervalMeasure 1)) :=
    hQmeas.aestronglyMeasurable
  -- the brick-3 dominator.
  set bound : ℝ → ℝ := fun s => weightedHeatHessConst θ * (t₀ - s) ^ (-1 + θ / 2 : ℝ) * HQ
    with hbound_def
  have hbound_int : IntervalIntegrable bound volume 0 t₀ := by
    have hr : (-1 : ℝ) < -1 + θ / 2 := by linarith
    have hcomp : IntervalIntegrable (fun s : ℝ => s ^ (-1 + θ / 2 : ℝ)) volume 0 t₀ :=
      intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t₀) hr
    have hshift := hcomp.comp_sub_left t₀
    simp only [sub_zero, sub_self] at hshift
    have h0 : IntervalIntegrable (fun s : ℝ => (t₀ - s) ^ (-1 + θ / 2 : ℝ)) volume 0 t₀ :=
      hshift.symm
    have h1 := (h0.const_mul (weightedHeatHessConst θ)).mul_const HQ
    exact h1.congr (fun s _ => by rw [hbound_def])
  -- a.e. `s ∈ Ι 0 t₀` is in `Ioo 0 t₀` (drop the endpoint `t₀`).
  have hae_ne_t : ∀ᵐ s ∂volume, s ≠ t₀ := by
    have heq : {s : ℝ | ¬ s ≠ t₀} = {t₀} := by ext s; simp [eq_comm]
    rw [MeasureTheory.ae_iff, heq]; exact Real.volume_singleton
  refine intervalIntegral.continuousWithinAt_of_dominated_interval
    (bound := bound) ?hF_meas ?h_bound hbound_int ?h_cont
  case hF_meas =>
    exact Filter.Eventually.of_forall (fun x =>
      intervalFullSemigroupOperator_s_dependent_secondDeriv_aestronglyMeasurable_x₀
        ht₀ hQ_ae hQint hQbdd x)
  case h_bound =>
    filter_upwards [self_mem_nhdsWithin] with x hxIcc
    filter_upwards [hae_ne_t] with s hsne hs_mem
    rw [Set.uIoc_of_le ht₀.le, Set.mem_Ioc] at hs_mem
    have hsIoo : s ∈ Set.Ioo (0:ℝ) t₀ := ⟨hs_mem.1, lt_of_le_of_ne hs_mem.2 hsne⟩
    have hts : 0 < t₀ - s := sub_pos.mpr hsIoo.2
    have hQ_ae_meas : AEStronglyMeasurable (Q s) (intervalMeasure 1) :=
      (hQint s).aestronglyMeasurable
    have hbrick := neumannHeatSecondDeriv_Ctheta_to_Linfty hts hθ0 hθ1 hQ_ae_meas
      (hQbdd s) hHQ_nn (hQholder s hsIoo) hxIcc
    rw [Real.norm_eq_abs, hbound_def]
    exact hbrick
  case h_cont =>
    filter_upwards [hae_ne_t] with s hsne hs_mem
    rw [Set.uIoc_of_le ht₀.le, Set.mem_Ioc] at hs_mem
    have hsIoo : s ∈ Set.Ioo (0:ℝ) t₀ := ⟨hs_mem.1, lt_of_le_of_ne hs_mem.2 hsne⟩
    have hts : 0 < t₀ - s := sub_pos.mpr hsIoo.2
    exact (secondDeriv_semigroup_continuous hts (hQcont s hsIoo)
      (hQcoeff s hsIoo)).continuousWithinAt

/-- **`chemLitLeg_continuousAt`.**  The first-order chemotaxis leg `chemLitLeg t₀ Q` is
continuous on `ℝ` (so in particular at the endpoints `{0,1}`).  Here the gradient sup
bound `(1/√π)·CQ·(t₀−s)^{−1/2}` is GLOBAL in `x`
(`intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t`), so the parameter
continuity holds at every `x₀` (no `[0,1]` restriction needed). -/
theorem chemLitLeg_continuousAt {t₀ CQ : ℝ} {Q : ℝ → ℝ → ℝ}
    (ht₀ : 0 < t₀)
    (hQmeas : Measurable (Function.uncurry Q))
    (hQint : ∀ s, Integrable (Q s) (intervalMeasure 1))
    (hQbdd : ∀ s y, |Q s y| ≤ CQ)
    {M : ℝ} (hQcont : ∀ s ∈ Set.Ioo (0:ℝ) t₀, Continuous (Q s))
    (hQcoeff : ∀ s ∈ Set.Ioo (0:ℝ) t₀, ∀ n, |cosineCoeffs (Q s) n| ≤ M)
    (x₀ : ℝ) :
    ContinuousAt (chemLitLeg t₀ Q) x₀ := by
  classical
  have hQ_ae : AEStronglyMeasurable (Function.uncurry Q)
      ((volume.restrict (Set.uIoc (0:ℝ) t₀)).prod (intervalMeasure 1)) :=
    hQmeas.aestronglyMeasurable
  -- the first-order gradient dominator `bound s = (1/√π)·CQ·(t₀−s)^{−1/2}`.
  set bound : ℝ → ℝ := fun s =>
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
      * (t₀ - s) ^ (-(1 / 2) : ℝ) * CQ with hbound_def
  have hbound_int : IntervalIntegrable bound volume 0 t₀ := by
    have hbase : IntervalIntegrable
        (fun s : ℝ => (t₀ - s) ^ (-(1 / 2) : ℝ)) volume 0 t₀ :=
      ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t₀
    have h1 := (hbase.const_mul
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant).mul_const CQ
    exact h1.congr (fun s _ => by rw [hbound_def])
  have hae_ne_t : ∀ᵐ s ∂volume, s ≠ t₀ := by
    have heq : {s : ℝ | ¬ s ≠ t₀} = {t₀} := by ext s; simp [eq_comm]
    rw [MeasureTheory.ae_iff, heq]; exact Real.volume_singleton
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := bound) ?hF_meas ?h_bound hbound_int ?h_cont
  case hF_meas =>
    exact Filter.Eventually.of_forall (fun x =>
      intervalFullSemigroupOperator_s_dependent_deriv_aestronglyMeasurable_x₀
        ht₀ hQ_ae hQint hQbdd x)
  case h_bound =>
    refine Filter.Eventually.of_forall (fun x => ?_)
    filter_upwards [hae_ne_t] with s hsne hs_mem
    rw [Set.uIoc_of_le ht₀.le, Set.mem_Ioc] at hs_mem
    have hsIoo : s ∈ Set.Ioo (0:ℝ) t₀ := ⟨hs_mem.1, lt_of_le_of_ne hs_mem.2 hsne⟩
    have hts : 0 < t₀ - s := sub_pos.mpr hsIoo.2
    have hQ_ae_meas : AEStronglyMeasurable (Q s) (intervalMeasure 1) :=
      (hQint s).aestronglyMeasurable
    have hbd := intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t
      hts hQ_ae_meas (hQbdd s) x
    rw [Real.norm_eq_abs, hbound_def]
    exact hbd
  case h_cont =>
    filter_upwards [hae_ne_t] with s hsne hs_mem
    rw [Set.uIoc_of_le ht₀.le, Set.mem_Ioc] at hs_mem
    have hsIoo : s ∈ Set.Ioo (0:ℝ) t₀ := ⟨hs_mem.1, lt_of_le_of_ne hs_mem.2 hsne⟩
    have hts : 0 < t₀ - s := sub_pos.mpr hsIoo.2
    exact (firstDeriv_semigroup_continuous hts (hQcont s hsIoo)
      (hQcoeff s hsIoo)).continuousAt

/-! ## The endpoint-extended `HasDerivWithinAt` on `[0,1]` -/

/-- Bundled hypotheses for the chemotaxis-leg `[0,1]` differentiability: the per-slice flux
family `Q` is jointly measurable, per-slice integrable, uniformly sup-bounded, per-slice
continuous with uniformly bounded cosine coefficients, and uniformly `θ`-Hölder on `[0,1]`. -/
structure ChemLegData (t₀ θ CQ HQ M : ℝ) (Q : ℝ → ℝ → ℝ) : Prop where
  ht₀ : 0 < t₀
  hθ0 : 0 < θ
  hθ1 : θ < 1
  hHQ_nn : 0 ≤ HQ
  hQmeas : Measurable (Function.uncurry Q)
  hQint : ∀ s, Integrable (Q s) (intervalMeasure 1)
  hCQ_nn : 0 ≤ CQ
  hQbdd : ∀ s y, |Q s y| ≤ CQ
  hQcont : ∀ s ∈ Set.Ioo (0:ℝ) t₀, Continuous (Q s)
  hQcoeff : ∀ s ∈ Set.Ioo (0:ℝ) t₀, ∀ n, |cosineCoeffs (Q s) n| ≤ M
  hQholder : ∀ s ∈ Set.Ioo (0:ℝ) t₀, ∀ a b, a ∈ Set.Icc (0:ℝ) 1 →
    b ∈ Set.Icc (0:ℝ) 1 → |Q s a - Q s b| ≤ HQ * |a - b| ^ θ

/-- **`chemLeg_hasDerivWithinAt_Icc` — the endpoint-extended interchange on `[0,1]`.**

At every `x₀ ∈ [0,1]`, `HasDerivWithinAt (chemLitLeg t₀ Q) (chemLitLeg₂ t₀ Q x₀)
(Set.Icc 0 1) x₀`.  Interior points: from `chemLeg_interior_hasDerivAt`.  Endpoints:
`hasDerivWithinAt_Ici/Iic_of_tendsto_deriv` (`Mathlib/Analysis/Calculus/FDeriv/Extend.lean`)
with `chemLitLeg` continuous (`chemLitLeg_continuousAt`), the interior derivative equal to
the continuous `chemLitLeg₂` (`chemLitLeg₂_continuousWithinAt_Icc`), then `.mono` to `Icc`. -/
theorem chemLeg_hasDerivWithinAt_Icc {t₀ θ CQ HQ M : ℝ} {Q : ℝ → ℝ → ℝ}
    (hd : ChemLegData t₀ θ CQ HQ M Q) {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0:ℝ) 1) :
    HasDerivWithinAt (chemLitLeg t₀ Q) (chemLitLeg₂ t₀ Q x₀) (Set.Icc (0:ℝ) 1) x₀ := by
  obtain ⟨ht₀, hθ0, hθ1, hHQ_nn, hQmeas, hQint, hCQ_nn, hQbdd, hQcont, hQcoeff, hQholder⟩ := hd
  -- interior `HasDerivAt` (the committed interchange).
  have hint : ∀ y ∈ Set.Ioo (0:ℝ) 1,
      HasDerivAt (chemLitLeg t₀ Q) (chemLitLeg₂ t₀ Q y) y := fun y hy =>
    chemLeg_interior_hasDerivAt ht₀ hθ0 hθ1 hHQ_nn hQmeas hQint hCQ_nn hQbdd hQholder hy
  -- on `Ioo 0 1`, `deriv (chemLitLeg) = chemLitLeg₂`.
  have hderiv_int : ∀ y ∈ Set.Ioo (0:ℝ) 1,
      deriv (chemLitLeg t₀ Q) y = chemLitLeg₂ t₀ Q y := fun y hy => (hint y hy).deriv
  -- `DifferentiableOn (chemLitLeg) (Ioo 0 1)` (interior, for the Extend lemmas).
  have hdiffOn : DifferentiableOn ℝ (chemLitLeg t₀ Q) (Set.Ioo (0:ℝ) 1) :=
    fun y hy => (hint y hy).differentiableAt.differentiableWithinAt
  -- `chemLitLeg` continuous everywhere (global gradient dominator).
  have hcontLeg : ∀ z : ℝ, ContinuousAt (chemLitLeg t₀ Q) z := fun z =>
    chemLitLeg_continuousAt ht₀ hQmeas hQint hQbdd hQcont hQcoeff z
  -- `chemLitLeg₂` continuous-within-`[0,1]` (used for the derivative limit).
  have hcont₂ : ∀ z ∈ Set.Icc (0:ℝ) 1,
      ContinuousWithinAt (chemLitLeg₂ t₀ Q) (Set.Icc (0:ℝ) 1) z := fun z hz =>
    chemLitLeg₂_continuousWithinAt_Icc ht₀ hθ0 hθ1 hHQ_nn hQmeas hQint hQbdd
      hQcont hQcoeff hQholder hz
  -- helper: `Ioo 0 1 ∈ 𝓝[>] 0` and `∈ 𝓝[<] 1`.
  have hIoo_right : Set.Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT (by norm_num)
  have hIoo_left : Set.Ioo (0:ℝ) 1 ∈ 𝓝[<] (1:ℝ) := Ioo_mem_nhdsLT (by norm_num)
  have h0Icc : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
  have h1Icc : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
  rcases eq_or_ne x₀ 0 with hx0 | hx0
  · -- left endpoint `x₀ = 0`.
    subst hx0
    -- `𝓝[>]0 ≤ 𝓝[Icc 0 1] 0`, since `Icc 0 1 ∈ 𝓝[>]0`.
    have hIccR : Set.Icc (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) :=
      Filter.mem_of_superset hIoo_right Set.Ioo_subset_Icc_self
    have hle : 𝓝[>] (0:ℝ) ≤ 𝓝[Set.Icc (0:ℝ) 1] (0:ℝ) :=
      (nhdsWithin_le_iff).mpr hIccR
    have hlim₂ : Tendsto (chemLitLeg₂ t₀ Q) (𝓝[>] (0:ℝ)) (𝓝 (chemLitLeg₂ t₀ Q 0)) :=
      (hcont₂ 0 h0Icc).tendsto.mono_left hle
    -- `deriv (chemLitLeg) =ᶠ[𝓝[>]0] chemLitLeg₂`.
    have hderivEq : (fun y => deriv (chemLitLeg t₀ Q) y)
        =ᶠ[𝓝[>] (0:ℝ)] chemLitLeg₂ t₀ Q := by
      filter_upwards [hIoo_right] with y hy using hderiv_int y hy
    have hlim : Tendsto (fun y => deriv (chemLitLeg t₀ Q) y) (𝓝[>] (0:ℝ))
        (𝓝 (chemLitLeg₂ t₀ Q 0)) := hlim₂.congr' hderivEq.symm
    have hcw : ContinuousWithinAt (chemLitLeg t₀ Q) (Set.Ioo (0:ℝ) 1) 0 :=
      (hcontLeg 0).continuousWithinAt
    have hIci : HasDerivWithinAt (chemLitLeg t₀ Q) (chemLitLeg₂ t₀ Q 0) (Set.Ici (0:ℝ)) 0 :=
      hasDerivWithinAt_Ici_of_tendsto_deriv hdiffOn hcw hIoo_right hlim
    exact hIci.mono (fun y hy => hy.1)
  · rcases eq_or_ne x₀ 1 with hx1 | hx1
    · -- right endpoint `x₀ = 1`.
      subst hx1
      have hIccL : Set.Icc (0:ℝ) 1 ∈ 𝓝[<] (1:ℝ) :=
        Filter.mem_of_superset hIoo_left Set.Ioo_subset_Icc_self
      have hle : 𝓝[<] (1:ℝ) ≤ 𝓝[Set.Icc (0:ℝ) 1] (1:ℝ) :=
        (nhdsWithin_le_iff).mpr hIccL
      have hlim₂ : Tendsto (chemLitLeg₂ t₀ Q) (𝓝[<] (1:ℝ)) (𝓝 (chemLitLeg₂ t₀ Q 1)) :=
        (hcont₂ 1 h1Icc).tendsto.mono_left hle
      have hderivEq : (fun y => deriv (chemLitLeg t₀ Q) y)
          =ᶠ[𝓝[<] (1:ℝ)] chemLitLeg₂ t₀ Q := by
        filter_upwards [hIoo_left] with y hy using hderiv_int y hy
      have hlim : Tendsto (fun y => deriv (chemLitLeg t₀ Q) y) (𝓝[<] (1:ℝ))
          (𝓝 (chemLitLeg₂ t₀ Q 1)) := hlim₂.congr' hderivEq.symm
      have hcw : ContinuousWithinAt (chemLitLeg t₀ Q) (Set.Ioo (0:ℝ) 1) 1 :=
        (hcontLeg 1).continuousWithinAt
      have hIic : HasDerivWithinAt (chemLitLeg t₀ Q) (chemLitLeg₂ t₀ Q 1) (Set.Iic (1:ℝ)) 1 :=
        hasDerivWithinAt_Iic_of_tendsto_deriv hdiffOn hcw hIoo_left hlim
      exact hIic.mono (fun y hy => hy.2)
    · -- interior point.
      have hyIoo : x₀ ∈ Set.Ioo (0:ℝ) 1 :=
        ⟨lt_of_le_of_ne hx₀.1 (Ne.symm hx0), lt_of_le_of_ne hx₀.2 hx1⟩
      exact (hint x₀ hyIoo).hasDerivWithinAt

/-- **`chemLeg_differentiableOn_Icc`.**  `chemLitLeg t₀ Q` is differentiable on `[0,1]`. -/
theorem chemLeg_differentiableOn_Icc {t₀ θ CQ HQ M : ℝ} {Q : ℝ → ℝ → ℝ}
    (hd : ChemLegData t₀ θ CQ HQ M Q) :
    DifferentiableOn ℝ (chemLitLeg t₀ Q) (Set.Icc (0:ℝ) 1) :=
  fun x₀ hx₀ => (chemLeg_hasDerivWithinAt_Icc hd hx₀).differentiableWithinAt

/-- **`chemLeg_derivWithin_eq_Icc`.**  On `[0,1]` the `derivWithin` of the chemotaxis leg is
the integrated second-derivative leg `chemLitLeg₂` (the `∂ₓ ∫ = ∫ ∂ₓₓ` identity, endpoint
inclusive). -/
theorem chemLeg_derivWithin_eq_Icc {t₀ θ CQ HQ M : ℝ} {Q : ℝ → ℝ → ℝ}
    (hd : ChemLegData t₀ θ CQ HQ M Q) {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0:ℝ) 1) :
    derivWithin (chemLitLeg t₀ Q) (Set.Icc (0:ℝ) 1) x₀ = chemLitLeg₂ t₀ Q x₀ :=
  (chemLeg_hasDerivWithinAt_Icc hd hx₀).derivWithin
    ((uniqueDiffOn_Icc (by norm_num : (0:ℝ) < 1)) x₀ hx₀)

/-- **`chemLeg_derivWithin_continuousOn_Icc`.**  The `derivWithin` of the chemotaxis leg is
continuous on `[0,1]` (it equals the continuous `chemLitLeg₂` there). -/
theorem chemLeg_derivWithin_continuousOn_Icc {t₀ θ CQ HQ M : ℝ} {Q : ℝ → ℝ → ℝ}
    (hd : ChemLegData t₀ θ CQ HQ M Q) :
    ContinuousOn (derivWithin (chemLitLeg t₀ Q) (Set.Icc (0:ℝ) 1)) (Set.Icc (0:ℝ) 1) := by
  have hcont₂ : ContinuousOn (chemLitLeg₂ t₀ Q) (Set.Icc (0:ℝ) 1) := fun z hz =>
    chemLitLeg₂_continuousWithinAt_Icc hd.ht₀ hd.hθ0 hd.hθ1 hd.hHQ_nn hd.hQmeas hd.hQint
      hd.hQbdd hd.hQcont hd.hQcoeff hd.hQholder hz
  exact hcont₂.congr (fun z hz => chemLeg_derivWithin_eq_Icc hd hz)

end ShenWork.Paper2
