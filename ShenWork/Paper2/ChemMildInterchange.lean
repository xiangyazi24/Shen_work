/-
  ShenWork/Paper2/ChemMildInterchange.lean

  **P2-T11 step (ii) — the chemotaxis-leg deriv-under-the-time-integral INTERCHANGE.**

  The chemotaxis leg of the divergence-form mild map (`intervalGradientDuhamelMap`) is

    `chemLitLeg t₀ Q x = ∫₀^{t₀} ∂ₓ[S(t₀−s) Q(s)](x) ds`
                       = ∫₀^{t₀} deriv (z ↦ S(t₀−s)(Q s) z) x ds.

  Differentiating this once more in `x` (the `∂ₓ ∫ = ∫ ∂ₓ` Leibniz interchange) yields the
  SECOND-order integrand `∂ₓₓ S(t₀−s)Q(s)(x)`:

    `∂ₓ chemLitLeg t₀ Q x = ∫₀^{t₀} deriv (z ↦ deriv (w ↦ S(t₀−s)(Q s) w) z) x ds`.

  ## What is proved here (axiom-clean, 0 sorry)

  * `secondDeriv_intervalNeumannFullKernel_fst_s_dependent_measurable` — the `(s,y)`-joint
    measurability of the full-kernel SECOND spatial derivative (lattice `tsum`, mirroring the
    committed first-derivative `deriv_intervalNeumannFullKernel_fst_s_dependent_measurable`).
  * `intervalFullSemigroupOperator_s_dependent_secondDeriv_aestronglyMeasurable_x₀` — the
    `hF'_meas` discharge for the second-order DUI: `s ↦ ∂ₓₓ S(t−s)(F s)(x₀)` is
    `AEStronglyMeasurable` on `volume.restrict (uIoc 0 t)`, via Fubini on the
    `∂ₓₓK·F` integrand (using the committed second-order semigroup DUI
    `intervalFullSemigroupOperator_hasDerivAt_deriv_fst`).
  * `chemLeg_interior_hasDerivAt` — **the INTERIOR interchange**: at an interior point
    `x₀ ∈ (0,1)`, `chemLitLeg t₀ Q` is differentiable with derivative the second-order leg.
    PROOF: `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` over
    `s = ball x₀ ε` (with `ε ≤ dist(x₀,{0,1})`, so the ball is inside `(0,1)`), the
    per-slice `x`-derivative supplied by the committed second-order semigroup DUI, and the
    DOMINATOR the brick-3 `C^θ→L∞` Hessian bound `weightedHeatHessConst θ·(t₀−s)^{−1+θ/2}·HQ`,
    integrable on `[0,t₀]` since `−1+θ/2 > −1`.

  ## Honest scope of the interchange (audit honesty — read before extending)

  The interchange is proved on the OPEN interior `(0,1)`, NOT globally on `ℝ`.  This is forced
  by the analysis, not a shortcut: the only `s`-integrable dominator for `∂ₓₓ S(t₀−s)Q(s)` is
  the brick-3 `(t₀−s)^{−1+θ/2}` rate produced by the `C^θ` cancellation, and that Schauder
  estimate (`neumannHeatSecondDeriv_Ctheta_to_Linfty`) is an `[0,1]`-ONLY bound.  The raw
  kernel Hessian bound that holds globally in `x` is `(t₀−s)^{−1}`, which is NOT integrable on
  `[0,t₀]`.  Hence the dominated-convergence DUI closes the interchange precisely at interior
  points (where `ball x₀ ε ⊆ (0,1)`), and a GLOBAL `∀x, HasDerivAt` is genuinely unavailable
  by an integrable-dominator argument.  This interior interchange is the real analytic content;
  it is exactly the `DifferentiatedMildSlice.hasDeriv`/`deriv_split` representation specialised
  to the chemotaxis leg of the concrete mild solution.

  No `sorry`/`admit`/custom `axiom`/`native_decide`.  New file only.
-/
import ShenWork.Paper2.ChemMildC1eta
import ShenWork.Paper2.IntervalDuhamelSpatialLeibniz

open MeasureTheory
open ShenWork.IntervalDomain (intervalMeasure intervalSet intervalMeasure_univ_lt_top)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator intervalNeumannFullKernel
   heatKernel_of_nonpos weightedHeatHessConst weightedHeatHessConst_nonneg
   neumannHeatSecondDeriv_Ctheta_to_Linfty intervalFullSemigroupOperator_hasDerivAt_deriv_fst
   measurable_tsum_int_of_summable latticeGaussianHessSummable deriv_deriv_heatKernel
   intervalFullSemigroupOperator_hasDerivAt_fst
   intervalFullSemigroupOperator_s_dependent_deriv_aestronglyMeasurable_x₀
   intervalFullCoupledDuhamel_grad_integrand_intervalIntegrable
   hasDerivAt_deriv_intervalNeumannFullKernel_fst)

noncomputable section

namespace ShenWork.Paper2

/-! ## §1 — Global closed form + joint measurability of the kernel SECOND derivative -/

/-- The heat-kernel second `x`-derivative as a GLOBAL closed form (all `t`, not just
`t>0`).  For `t ≤ 0` the kernel is identically zero so both sides vanish; for `t>0` this
is the committed `deriv_deriv_heatKernel`. -/
theorem deriv_deriv_heatKernel_global (t x : ℝ) :
    deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) x =
      (1 / (2 * t)) * (x ^ 2 / (2 * t) - 1) * heatKernel t x := by
  rcases lt_or_ge 0 t with ht | ht
  · exact deriv_deriv_heatKernel ht x
  · have hzero : (fun z : ℝ => heatKernel t z) = fun _ : ℝ => (0 : ℝ) := by
      funext z; exact heatKernel_of_nonpos ht z
    have h1 : (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) = fun _ : ℝ => (0 : ℝ) := by
      funext u; rw [hzero, deriv_const]
    rw [h1, deriv_const, heatKernel_of_nonpos ht x, mul_zero]

/-- The `(s,y)`-dependent heat-kernel second spatial derivative
`(s,y) ↦ deriv (u ↦ deriv (z ↦ heatKernel (t−s) z) u) (p (s,y))` is jointly measurable for
any measurable affine argument `p` (via the global closed form). -/
theorem measurable_secondDeriv_heatKernel_comp {p : ℝ × ℝ → ℝ} (hp : Measurable p) (t : ℝ) :
    Measurable (fun w : ℝ × ℝ =>
      deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel (t - w.1) z) u) (p w)) := by
  have heq : (fun w : ℝ × ℝ =>
        deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel (t - w.1) z) u) (p w))
      = fun w : ℝ × ℝ =>
        (1 / (2 * (t - w.1))) * ((p w) ^ 2 / (2 * (t - w.1)) - 1)
          * heatKernel (t - w.1) (p w) := by
    funext w; exact deriv_deriv_heatKernel_global (t - w.1) (p w)
  rw [heq]
  unfold heatKernel
  fun_prop

/-- **Joint measurability of the full-kernel SECOND spatial derivative in `(s,y)`.**
For fixed `x₀`, `(s,y) ↦ (∑ₖ ∂²heat(t−s, x₀−y+2k)) + (∑ₖ ∂²heat(t−s, x₀+y+2k))` is
`Measurable`.  By `hasDerivAt_deriv_intervalNeumannFullKernel_fst`, for `t−s>0` this equals
`deriv (z ↦ deriv (w ↦ K_full(t−s, w, y)) z) x₀` (the second `x`-derivative).  Mirrors the
committed `deriv_intervalNeumannFullKernel_fst_s_dependent_measurable`. -/
theorem secondDeriv_intervalNeumannFullKernel_fst_s_dependent_measurable (t x₀ : ℝ) :
    Measurable (fun w : ℝ × ℝ =>
      (∑' k : ℤ, deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel (t - w.1) z) u)
          (x₀ - w.2 + 2 * (k : ℝ)))
        + (∑' k : ℤ, deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel (t - w.1) z) u)
          (x₀ + w.2 + 2 * (k : ℝ)))) := by
  set g₁ : ℤ → ℝ × ℝ → ℝ :=
    fun k w => deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel (t - w.1) z) u)
      (x₀ - w.2 + 2 * (k : ℝ)) with hg₁_def
  set g₂ : ℤ → ℝ × ℝ → ℝ :=
    fun k w => deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel (t - w.1) z) u)
      (x₀ + w.2 + 2 * (k : ℝ)) with hg₂_def
  have hg₁_meas : ∀ k, Measurable (g₁ k) := fun k =>
    measurable_secondDeriv_heatKernel_comp (by fun_prop) t
  have hg₂_meas : ∀ k, Measurable (g₂ k) := fun k =>
    measurable_secondDeriv_heatKernel_comp (by fun_prop) t
  -- summability of the lattice second-derivative series (Gaussian Hessian majorant for
  -- `t−s>0`; all-zero for `t−s ≤ 0`).
  have hsum_aux : ∀ (z : ℝ) (w : ℝ × ℝ),
      Summable (fun k : ℤ =>
        deriv (fun u : ℝ => deriv (fun v : ℝ => heatKernel (t - w.1) v) u)
          (z + 2 * (k : ℝ))) := by
    intro z w
    rcases lt_or_ge 0 (t - w.1) with hτ | hτ
    · exact latticeGaussianHessSummable hτ z
    · have hz : (fun k : ℤ =>
          deriv (fun u : ℝ => deriv (fun v : ℝ => heatKernel (t - w.1) v) u)
            (z + 2 * (k : ℝ))) = fun _ : ℤ => (0 : ℝ) := by
        funext k
        have hzero : (fun v : ℝ => heatKernel (t - w.1) v) = fun _ : ℝ => (0 : ℝ) := by
          funext v; exact heatKernel_of_nonpos hτ v
        have h1 : (fun u : ℝ => deriv (fun v : ℝ => heatKernel (t - w.1) v) u)
            = fun _ : ℝ => (0 : ℝ) := by funext u; rw [hzero, deriv_const]
        rw [h1, deriv_const]
      rw [hz]; exact summable_zero
  have hg₁_sum : ∀ w, Summable (fun k : ℤ => g₁ k w) := fun w => hsum_aux (x₀ - w.2) w
  have hg₂_sum : ∀ w, Summable (fun k : ℤ => g₂ k w) := fun w => hsum_aux (x₀ + w.2) w
  exact (measurable_tsum_int_of_summable hg₁_meas hg₁_sum).add
    (measurable_tsum_int_of_summable hg₂_meas hg₂_sum)

/-! ## §2 — `hF'_meas` for the SECOND-order time-integral DUI -/

/-- **Full-kernel second-order `hF'_meas` discharge.**  For `t>0`, joint measurability and
per-slice integrability/boundedness of `F`, the map
`s ↦ deriv (z ↦ deriv (w ↦ S(t−s)(F s) w) z) x₀` is `AEStronglyMeasurable` on
`volume.restrict (uIoc 0 t)`.  The operator second derivative is realised as the parametric
integral against the full-kernel SECOND spatial derivative via the committed second-order
semigroup DUI `intervalFullSemigroupOperator_hasDerivAt_deriv_fst`, whose `(s,y)`-joint
measurability is `secondDeriv_intervalNeumannFullKernel_fst_s_dependent_measurable`; Fubini
concludes.  Mirrors the committed first-order
`intervalFullSemigroupOperator_s_dependent_deriv_aestronglyMeasurable_x₀`. -/
theorem intervalFullSemigroupOperator_s_dependent_secondDeriv_aestronglyMeasurable_x₀
    {t : ℝ} (ht : 0 < t) {F : ℝ → ℝ → ℝ}
    (hF_ae : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    {C_source : ℝ} (hF_sup : ∀ s, ∀ y : ℝ, |F s y| ≤ C_source) (x₀ : ℝ) :
    AEStronglyMeasurable
      (fun s : ℝ =>
        deriv (fun z : ℝ => deriv (fun w : ℝ => intervalFullSemigroupOperator (t - s) (F s) w) z)
          x₀)
      (volume.restrict (Set.uIoc (0 : ℝ) t)) := by
  -- the closed-form parametric-integral surrogate `D2(s)` against the kernel Hessian.
  set Kd2 : ℝ × ℝ → ℝ :=
    fun w =>
      (∑' k : ℤ, deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel (t - w.1) z) u)
          (x₀ - w.2 + 2 * (k : ℝ)))
        + (∑' k : ℤ, deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel (t - w.1) z) u)
          (x₀ + w.2 + 2 * (k : ℝ))) with hKd2_def
  have hKd2_meas := secondDeriv_intervalNeumannFullKernel_fst_s_dependent_measurable t x₀
  set D2 : ℝ → ℝ := fun s => ∫ y, Kd2 (s, y) * F s y ∂(intervalMeasure 1) with hD2_def
  have hD2_aestrong : AEStronglyMeasurable D2 (volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    have hint_ae : AEStronglyMeasurable (fun w : ℝ × ℝ => Kd2 w * F w.1 w.2)
        ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)) :=
      hKd2_meas.aestronglyMeasurable.mul hF_ae
    exact MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := volume.restrict (Set.uIoc (0 : ℝ) t)) (ν := intervalMeasure 1)
      (f := fun w : ℝ × ℝ => Kd2 w * F w.1 w.2) hint_ae
  refine hD2_aestrong.congr ?_
  have huIoc_eq : Set.uIoc (0 : ℝ) t = Set.Ioc (0 : ℝ) t := Set.uIoc_of_le ht.le
  have hae_lt_t : ∀ᵐ s ∂(volume.restrict (Set.uIoc 0 t)), s < t := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
    have hae_ne_t : ∀ᵐ s ∂volume, s ≠ t := by
      have heq : {s : ℝ | ¬ s ≠ t} = {t} := by ext s; simp [eq_comm]
      rw [MeasureTheory.ae_iff, heq]; exact Real.volume_singleton
    filter_upwards [hae_ne_t] with s hsne hs
    rw [huIoc_eq] at hs
    exact lt_of_le_of_ne hs.2 hsne
  filter_upwards [hae_lt_t] with s hst
  have htms_pos : 0 < t - s := sub_pos.mpr hst
  -- operator second derivative = ∫ y, ∂ₓₓK_full(t−s, x₀, y) · F s y.
  have hOp2 :
      deriv (fun z : ℝ => deriv (fun w : ℝ => intervalFullSemigroupOperator (t - s) (F s) w) z) x₀
        = ∫ y, deriv (fun z : ℝ =>
            deriv (fun w : ℝ => intervalNeumannFullKernel (t - s) w y) z) x₀ * F s y
          ∂(intervalMeasure 1) :=
    (intervalFullSemigroupOperator_hasDerivAt_deriv_fst (t := t - s) htms_pos
      (f := F s) (hF_int s).aestronglyMeasurable (Cf := C_source) (hF_sup s) x₀).deriv
  rw [hOp2]
  -- identify the kernel Hessian with `Kd2 (s, ·)` via the lattice closed form.
  have hKfun : ∀ y : ℝ,
      deriv (fun z : ℝ => deriv (fun w : ℝ => intervalNeumannFullKernel (t - s) w y) z) x₀
        = Kd2 (s, y) := fun y =>
    (hasDerivAt_deriv_intervalNeumannFullKernel_fst
      htms_pos x₀ y).deriv
  simp only [hD2_def]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with y
  rw [hKfun y]

/-! ## §3 — The chemotaxis-leg INTERIOR interchange (`∂ₓ ∫ = ∫ ∂ₓₓ`) -/

/-- The concrete clamped-free chemotaxis Duhamel leg (literal form): the time integral of
the FIRST `x`-derivative of the propagator applied to the per-slice flux family `Q`. -/
noncomputable def chemLitLeg (t₀ : ℝ) (Q : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun x => ∫ s in (0:ℝ)..t₀,
    deriv (fun z : ℝ => intervalFullSemigroupOperator (t₀ - s) (Q s) z) x

/-- The literal second-order chemotaxis leg: the time integral of the SECOND `x`-derivative
of the propagator applied to `Q`.  This is `∂ₓ chemLitLeg` on the interior. -/
noncomputable def chemLitLeg₂ (t₀ : ℝ) (Q : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun x => ∫ s in (0:ℝ)..t₀,
    deriv (fun z : ℝ =>
      deriv (fun w : ℝ => intervalFullSemigroupOperator (t₀ - s) (Q s) w) z) x

/-- **`chemLeg_interior_hasDerivAt` — the chemotaxis-leg deriv-under-the-time-integral
INTERCHANGE, at an interior point.**

For a per-slice flux family `Q` (jointly measurable, uniformly sup-bounded `|Q s y| ≤ CQ`,
per-slice integrable, uniformly `θ`-Hölder on `[0,1]` with `[Q s]_θ ≤ HQ`, `s ∈ (0,t₀)`) and
an interior point `x₀ ∈ (0,1)`, the literal chemotaxis Duhamel leg `chemLitLeg t₀ Q` is
differentiable at `x₀` with derivative the literal second-order leg `chemLitLeg₂ t₀ Q x₀`:

  `HasDerivAt (chemLitLeg t₀ Q) (chemLitLeg₂ t₀ Q x₀) x₀`.

PROOF: `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` on
`s = ball x₀ ε`, `ε = min x₀ (1−x₀)/2` (so `ball x₀ ε ⊆ (0,1)`); the per-slice `x`-derivative
is the committed second-order semigroup DUI
`intervalFullSemigroupOperator_hasDerivAt_deriv_fst`; the DOMINATOR is the brick-3 `C^θ→L∞`
Hessian bound `weightedHeatHessConst θ · (t₀−s)^{−1+θ/2} · HQ`, integrable on `[0,t₀]` since
`−1+θ/2 > −1` (`brick4_time_integrand_integrable`-style).  The bound is valid only on `[0,1]`,
which is why `x` ranges over the interior ball — the global interchange is genuinely
unavailable (see file header). -/
theorem chemLeg_interior_hasDerivAt {t₀ θ CQ HQ : ℝ} {Q : ℝ → ℝ → ℝ}
    (ht₀ : 0 < t₀) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hHQ_nn : 0 ≤ HQ)
    (hQmeas : Measurable (Function.uncurry Q))
    (hQint : ∀ s, Integrable (Q s) (intervalMeasure 1))
    (hCQ_nn : 0 ≤ CQ) (hQbdd : ∀ s y, |Q s y| ≤ CQ)
    (hQholder : ∀ s ∈ Set.Ioo (0:ℝ) t₀, ∀ a b, a ∈ Set.Icc (0:ℝ) 1 →
      b ∈ Set.Icc (0:ℝ) 1 → |Q s a - Q s b| ≤ HQ * |a - b| ^ θ)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo (0:ℝ) 1) :
    HasDerivAt (chemLitLeg t₀ Q) (chemLitLeg₂ t₀ Q x₀) x₀ := by
  classical
  -- joint AEStronglyMeasurability of `uncurry Q` on the restricted product measure.
  have hQ_ae : AEStronglyMeasurable (Function.uncurry Q)
      ((volume.restrict (Set.uIoc (0:ℝ) t₀)).prod (intervalMeasure 1)) :=
    hQmeas.aestronglyMeasurable
  -- interior radius: a ball around `x₀` inside `(0,1)`.
  set ε : ℝ := min x₀ (1 - x₀) / 2 with hε_def
  have hx₀0 : 0 < x₀ := hx₀.1
  have hx₀1 : x₀ < 1 := hx₀.2
  have hmin_pos : 0 < min x₀ (1 - x₀) := lt_min hx₀0 (by linarith)
  have hε_pos : 0 < ε := by rw [hε_def]; positivity
  have hball_sub : Metric.ball x₀ ε ⊆ Set.Ioo (0:ℝ) 1 := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq] at hx
    have hlt : |x - x₀| < ε := hx
    have hεle1 : ε ≤ x₀ := by
      rw [hε_def]; have : min x₀ (1 - x₀) ≤ x₀ := min_le_left _ _; linarith
    have hεle2 : ε ≤ 1 - x₀ := by
      rw [hε_def]; have : min x₀ (1 - x₀) ≤ 1 - x₀ := min_le_right _ _; linarith
    rw [abs_lt] at hlt
    exact ⟨by linarith [hlt.1], by linarith [hlt.2]⟩
  -- first-order leg-integrand integrability (`hF_int`).
  have hF'_meas_first : ∀ x : ℝ, AEStronglyMeasurable
      (fun s : ℝ => deriv (fun z : ℝ => intervalFullSemigroupOperator (t₀ - s) (Q s) z) x)
      (volume.restrict (Set.uIoc (0:ℝ) t₀)) := fun x =>
    intervalFullSemigroupOperator_s_dependent_deriv_aestronglyMeasurable_x₀
      ht₀ hQ_ae hQint hQbdd x
  have hDom_int_first : IntervalIntegrable
      (fun s : ℝ => ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
        * CQ * (t₀ - s) ^ (-(1/2 : ℝ))) volume (0:ℝ) t₀ := by
    rw [show (fun s : ℝ => ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          * CQ * (t₀ - s) ^ (-(1/2 : ℝ)))
        = (fun s : ℝ => (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          * CQ) * (t₀ - s) ^ (-(1/2 : ℝ))) from by funext s; ring]
    exact (ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t₀).const_mul _
  have hF_int : IntervalIntegrable
      (fun s : ℝ => deriv (fun z : ℝ => intervalFullSemigroupOperator (t₀ - s) (Q s) z) x₀)
      volume 0 t₀ :=
    intervalFullCoupledDuhamel_grad_integrand_intervalIntegrable
      ht₀ hQint hCQ_nn hQbdd x₀ (hF'_meas_first x₀) hDom_int_first
  -- second-order leg-integrand a.e.-measurability (`hF'_meas`).
  have hF'_meas : AEStronglyMeasurable
      (fun s : ℝ => deriv (fun z : ℝ =>
        deriv (fun w : ℝ => intervalFullSemigroupOperator (t₀ - s) (Q s) w) z) x₀)
      (volume.restrict (Set.uIoc (0:ℝ) t₀)) :=
    intervalFullSemigroupOperator_s_dependent_secondDeriv_aestronglyMeasurable_x₀
      ht₀ hQ_ae hQint hQbdd x₀
  -- the brick-3 dominator `bound s = weightedHeatHessConst θ · (t₀−s)^{−1+θ/2} · HQ`.
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
  -- apply Mathlib's interval-integral DUI.
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0:ℝ)) (b := t₀)
    (F := fun x s => deriv (fun z : ℝ => intervalFullSemigroupOperator (t₀ - s) (Q s) z) x)
    (F' := fun x s => deriv (fun z : ℝ =>
        deriv (fun w : ℝ => intervalFullSemigroupOperator (t₀ - s) (Q s) w) z) x)
    (x₀ := x₀) (bound := bound)
    (Metric.ball_mem_nhds x₀ hε_pos)
    ?hF_meas hF_int hF'_meas ?h_bound hbound_int ?h_diff).2
  case hF_meas =>
    exact Filter.Eventually.of_forall (fun x => hF'_meas_first x)
  case h_bound =>
    have huIoc_eq : Set.uIoc (0:ℝ) t₀ = Set.Ioc (0:ℝ) t₀ := Set.uIoc_of_le ht₀.le
    have hae_ne_t : ∀ᵐ s ∂volume, s ≠ t₀ := by
      have heq : {s : ℝ | ¬ s ≠ t₀} = {t₀} := by ext s; simp [eq_comm]
      rw [MeasureTheory.ae_iff, heq]; exact Real.volume_singleton
    filter_upwards [hae_ne_t] with s hsne hs_mem x hx
    rw [Set.uIoc_of_le ht₀.le, Set.mem_Ioc] at hs_mem
    have hsIoo : s ∈ Set.Ioo (0:ℝ) t₀ :=
      ⟨hs_mem.1, lt_of_le_of_ne hs_mem.2 hsne⟩
    have hts : 0 < t₀ - s := sub_pos.mpr hsIoo.2
    have hxIcc : x ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self (hball_sub hx)
    have hQ_ae_meas : AEStronglyMeasurable (Q s) (intervalMeasure 1) :=
      (hQint s).aestronglyMeasurable
    have hbrick := neumannHeatSecondDeriv_Ctheta_to_Linfty hts hθ0 hθ1 hQ_ae_meas
      (hQbdd s) hHQ_nn (hQholder s hsIoo) hxIcc
    rw [Real.norm_eq_abs, hbound_def]
    exact hbrick
  case h_diff =>
    have huIoc_eq : Set.uIoc (0:ℝ) t₀ = Set.Ioc (0:ℝ) t₀ := Set.uIoc_of_le ht₀.le
    have hae_ne_t : ∀ᵐ s ∂volume, s ≠ t₀ := by
      have heq : {s : ℝ | ¬ s ≠ t₀} = {t₀} := by ext s; simp [eq_comm]
      rw [MeasureTheory.ae_iff, heq]; exact Real.volume_singleton
    filter_upwards [hae_ne_t] with s hsne hs_mem x _hx
    rw [Set.uIoc_of_le ht₀.le, Set.mem_Ioc] at hs_mem
    have hts : 0 < t₀ - s := sub_pos.mpr (lt_of_le_of_ne hs_mem.2 hsne)
    have h := intervalFullSemigroupOperator_hasDerivAt_deriv_fst (t := t₀ - s) hts
      (f := Q s) (hQint s).aestronglyMeasurable (Cf := CQ) (hQbdd s) x
    rw [h.deriv]; exact h

/-- **`chemLeg_interior_deriv_eq` — the `.deriv` corollary of the interior interchange.**
At an interior point `x₀ ∈ (0,1)`, the spatial derivative of the chemotaxis Duhamel leg
equals the integrated second-derivative leg (the genuine `∂ₓ ∫ = ∫ ∂ₓₓ` identity):

  `deriv (chemLitLeg t₀ Q) x₀ = chemLitLeg₂ t₀ Q x₀`.

This is the directly reusable interchange identity; it grounds the INTERIOR of the
`DifferentiatedMildSlice.hasDeriv`/`deriv_split` representation for the concrete mild
chemotaxis leg.  The GLOBAL `∀x` extension (the single remaining gap) requires the cosine
spectral representative + a reflection-Hölder extension across the Neumann reflection
points `{0,1}`; see file header for why no global integrable dominator exists. -/
theorem chemLeg_interior_deriv_eq {t₀ θ CQ HQ : ℝ} {Q : ℝ → ℝ → ℝ}
    (ht₀ : 0 < t₀) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hHQ_nn : 0 ≤ HQ)
    (hQmeas : Measurable (Function.uncurry Q))
    (hQint : ∀ s, Integrable (Q s) (intervalMeasure 1))
    (hCQ_nn : 0 ≤ CQ) (hQbdd : ∀ s y, |Q s y| ≤ CQ)
    (hQholder : ∀ s ∈ Set.Ioo (0:ℝ) t₀, ∀ a b, a ∈ Set.Icc (0:ℝ) 1 →
      b ∈ Set.Icc (0:ℝ) 1 → |Q s a - Q s b| ≤ HQ * |a - b| ^ θ)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo (0:ℝ) 1) :
    deriv (chemLitLeg t₀ Q) x₀ = chemLitLeg₂ t₀ Q x₀ :=
  (chemLeg_interior_hasDerivAt ht₀ hθ0 hθ1 hHQ_nn hQmeas hQint hCQ_nn hQbdd hQholder hx₀).deriv

end ShenWork.Paper2
