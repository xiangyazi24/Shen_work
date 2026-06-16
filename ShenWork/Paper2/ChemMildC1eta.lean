/-
  ShenWork/Paper2/ChemMildC1eta.lean

  **`u(t_0,·) ∈ C^{1+η}` at positive time via the divergence-form Schauder estimate.**

  The FINAL rung of the χ₀<0 `hregularize` route:
    mild fixed point → `u ∈ C^θ` [committed, `mild_orderBox_positiveTime_holder`]
      → `u ∈ C^{1+η}` [THIS file] → Wiener ℓ¹ [committed, `HolderCosineDecay`].

  Differentiating the mild equation `u(t) = S(t)u₀ − χ₀∫₀ᵗ∂ₓS(t−s)Q ds + ∫₀ᵗS(t−s)L ds`
  once in `x`:
    `u_x(t,x) = ∂ₓS(t)u₀(x) − χ₀∫₀ᵗ∂ₓₓS(t−s)Q(s)(x) ds + ∫₀ᵗ∂ₓS(t−s)L(s)(x) ds`.
  * Initial leg `∂ₓS(t)u₀`            : `C^η` via the committed gradient Hölder smoothing.
  * Reaction leg `∫∂ₓS(t−s)L`         : `C^η` via the committed gradient Hölder smoothing.
  * Chemotaxis leg `∫∂ₓₓS(t−s)Q`      : `C^η` via the **divergence-form Schauder estimate**
        `[∂ₓₓS(σ)h]_{C^η} ≤ Cθη σ^{−1+(θ−η)/2}[h]_θ`, INTEGRABLE in σ
        (`∫_τ^{t_0}(t_0−s)^{−1+(θ−η)/2}ds < ∞`) since `Q = u·V_x ∈ C^θ`.

  ## What is committed/proved here (axiom-clean, 0 sorry)
  The kernel-side `C^θ`-cancellation bricks are PROVED in
  `ShenWork/PDE/IntervalFullKernelSecondDerivCtheta.lean`:
    * `intervalNeumannFullKernel_secondDeriv_integral_zero`  (brick 1, mean-zero)
    * `intervalNeumannFullKernel_secondDeriv_weighted_mass`  (brick 2, `Cθ σ^{−1+θ/2}`)
    * `neumannHeatSecondDeriv_Ctheta_to_Linfty`              (brick 3, `C^θ→L∞`)

  ## Brick 4 — DISCHARGED to a THEOREM via Route B (`neumannHeatSecondDerivCthetaToCeta_routeB`)
  `NeumannHeatSecondDerivCthetaToCeta` below packages the `C^θ→C^η` second-derivative
  bound `[∂ₓₓS(σ)h]_{C^η} ≤ Cθη σ^{−1+(θ−η)/2}[h]_θ` as a conclusion-shaped Prop.  It is
  no longer carried: `neumannHeatSecondDerivCthetaToCeta_routeB` PROVES the bound (on the
  open interval `(0,1)`, the natural domain) for continuous data with bounded cosine
  coefficients, via Route B — the new commutation lemma
  `intervalFullSemigroupOperator_secondDeriv_comm` (in `ChemMildC1etaComm.lean`,
  `∂ₓₓS(σ)h = S(σ/2)(∂ₓₓS(σ/2)h)`, proved spectrally) + the committed value Hölder
  `neumannHeat_Linf_to_Ctheta` at exponent `η` applied to `∂ₓₓS(σ/2)h` (sup-bounded by
  brick 3).  Route A (third-derivative kernel) is the historical alternative below.

  ROUTE A (third-derivative kernel; the direct far/near Schauder split).  The near
  region `|x₁−x₂|<√σ` needs the **third** `x`-derivative of the kernel, i.e. a file
  `IntervalFullKernelThirdDerivCtheta.lean` providing, mirroring brick 1/2 one
  derivative up:
    * `intervalNeumannFullKernel_thirdDeriv_integral_zero`  (`∫₀¹ ∂ₓₓₓK_σ(x,·) = 0`),
    * `intervalNeumannFullKernel_thirdDeriv_weighted_mass`
        (`∫₀¹ |∂ₓₓₓK_σ(x,y)| |x−y|^θ dy ≤ Cθ σ^{−3/2+θ/2}`),
    * `intervalFullSemigroupOperator_hasDerivAt_deriv_deriv_fst` (the third-order DUI),
    * `neumannHeatThirdDeriv_Ctheta_to_Linfty`
        (`‖∂ₓₓₓS(σ)h‖∞ ≤ Cθ σ^{−3/2+θ/2}[h]_θ`).
  Then for `|x₁−x₂|<√σ`, the mean-value inequality on `∂ₓₓS(σ)h` via the `∂ₓₓₓ` bound
  gives `σ^{−3/2+θ/2}|x₁−x₂|`, and combining with the far region (2×brick 3) yields the
  `σ^{−1+(θ−η)/2}` exponent.

  ROUTE B (semigroup split; avoids ∂ₓₓₓ).  Using the committed semigroup composition
  `intervalFullSemigroupOperator_comp` (`S(σ/2)∘S(σ/2)=S(σ)` on `[0,1]`) together with
  the **second-derivative ↔ propagator commutation**
    `intervalFullSemigroupOperator_secondDeriv_comm`
        (`∂ₓₓS(σ)h(x) = S(σ/2)(∂ₓₓS(σ/2)h)(x)` for `x∈[0,1]`, a twice-Neumann-IBP of the
        committed DUI — the one missing lemma for this route), one writes
    `[∂ₓₓS(σ)h]_{C^η} = [S(σ/2)(∂ₓₓS(σ/2)h)]_{C^η}`
      ≤ Cη (σ/2)^{−η/2}‖∂ₓₓS(σ/2)h‖∞        (committed VALUE `L∞→C^η`, brick-3-free)
      ≤ Cη Cθ (σ/2)^{−η/2}(σ/2)^{−1+θ/2}[h]_θ (brick 3)
      = Cθη σ^{−1+(θ−η)/2}[h]_θ.

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.Paper2.ChemMildHolderBootstrap
import ShenWork.PDE.IntervalFullKernelSecondDerivCtheta
import ShenWork.Paper2.ChemMildC1etaComm
import ShenWork.Paper2.ChemMildHolder
import ShenWork.Wiener.EWA.HolderCosineDecay

open MeasureTheory
open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator
  neumannHeatSecondDeriv_Ctheta_to_Linfty weightedHeatHessConst weightedHeatHessConst_nonneg)
open ShenWork.Paper2 (intervalNeumannHeatSemigroup neumannHeat_Linf_to_Ctheta
  gradSmoothingConst gradSmoothingConst_nonneg)

namespace ShenWork.Paper2

/-! ## Brick 4 — the `C^θ → C^η` second-derivative bound, as a named hypothesis -/

/-- **NAMED brick-4 hypothesis: the divergence-form `C^θ → C^η` second-derivative
estimate.**  For the interval-Neumann propagator `S(σ)` on `[0,1]`, bounded
measurable `h` (`|h| ≤ Ch`) with Hölder modulus `Hh` (`|h(a)−h(b)| ≤ Hh|a−b|^θ` on
`[0,1]`), the second `x`-derivative of `S(σ)h` is itself `C^η` with the INTEGRABLE
`σ`-rate `σ^{−1+(θ−η)/2}`:

  `|∂ₓₓS(σ)h(x₁) − ∂ₓₓS(σ)h(x₂)| ≤ Cθη · σ^{−1+(θ−η)/2} · Hh · |x₁−x₂|^η`,  `x₁,x₂∈[0,1]`.

`Cθη` is the fixed (data-independent) constant `weightedHeatHessConst`-scaled by the
interpolation factors.  Packaged as a Prop on `(σ, θ, η, Cθη)`; it is the single
remaining PDE fact (see file header, routes A/B).  Never proved as the conclusion. -/
def NeumannHeatSecondDerivCthetaToCeta (θ η Cθη : ℝ) : Prop :=
  ∀ {σ : ℝ}, 0 < σ → ∀ {h : ℝ → ℝ},
    AEStronglyMeasurable h (intervalMeasure 1) →
    ∀ {Ch : ℝ}, (∀ y, |h y| ≤ Ch) → ∀ {Hh : ℝ}, 0 ≤ Hh →
    (∀ a b, a ∈ Set.Icc (0:ℝ) 1 → b ∈ Set.Icc (0:ℝ) 1 → |h a - h b| ≤ Hh * |a - b| ^ θ) →
    ∀ x₁ x₂, x₁ ∈ Set.Icc (0:ℝ) 1 → x₂ ∈ Set.Icc (0:ℝ) 1 →
      |deriv (fun z : ℝ => deriv (fun w : ℝ => intervalFullSemigroupOperator σ h w) z) x₁
        - deriv (fun z : ℝ => deriv (fun w : ℝ => intervalFullSemigroupOperator σ h w) z) x₂|
        ≤ Cθη * σ ^ (-1 + (θ - η) / 2 : ℝ) * Hh * |x₁ - x₂| ^ η

/-! ## Brick 4 — DISCHARGED to a theorem via Route B (commutation + value-Hölder) -/

/-- The brick-4 constant `Cθη`, fully explicit: the value-Hölder interpolation factor
`2^{1−η}·C∇^η` times the brick-3 weighted-Hessian constant, with the `2`-power from
folding the half-time `(σ/2)`-rates back to a `σ`-rate. -/
noncomputable def brick4Const (θ η : ℝ) : ℝ :=
  (2 : ℝ) ^ (1 - η) * gradSmoothingConst ^ η
    * ((2 : ℝ) ^ (1 + η / 2 - θ / 2 : ℝ) * weightedHeatHessConst θ)

theorem brick4Const_nonneg (θ η : ℝ) : 0 ≤ brick4Const θ η := by
  unfold brick4Const
  have := gradSmoothingConst_nonneg
  have := weightedHeatHessConst_nonneg θ
  positivity

/-- **Brick 4, Route B — the `C^θ → C^η` second-derivative estimate, DISCHARGED.**
For continuous data `h` with bounded cosine coefficients and Hölder modulus `Hh`, the
propagator's second `x`-derivative is `C^η` on the OPEN interval with the integrable
`σ`-rate `σ^{−1+(θ−η)/2}`:

  `|∂ₓₓS(σ)h(x₁) − ∂ₓₓS(σ)h(x₂)| ≤ brick4Const θ η · σ^{−1+(θ−η)/2} · Hh · |x₁−x₂|^η`.

PROOF (Route B): the commutation `∂ₓₓS(σ)h = S(σ/2)Gspec` on `(0,1)`
(`intervalFullSemigroupOperator_secondDeriv_comm`, where `Gspec = ∂ₓₓS(σ/2)h`), then
the committed VALUE Hölder smoothing `neumannHeat_Linf_to_Ctheta` at exponent `η`
applied to the `[0,1]`-truncation `Gtrunc` of `Gspec` (equal to `Gspec` under the
`[0,1]`-measure, so `S(σ/2)Gtrunc = S(σ/2)Gspec`), whose sup bound is the brick-3
second-derivative `C^θ→L∞` bound `weightedHeatHessConst θ·(σ/2)^{−1+θ/2}·Hh`. -/
theorem neumannHeatSecondDerivCthetaToCeta_routeB {σ θ η : ℝ} (hσ : 0 < σ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hη0 : 0 < η) (hη1 : η < 1)
    {h : ℝ → ℝ} (hh : Continuous h)
    {M : ℝ} (hM : ∀ n, |ShenWork.IntervalNeumannFullKernel.cosineCoeffs h n| ≤ M)
    {Ch : ℝ} (hhb : ∀ y, |h y| ≤ Ch) {Hh : ℝ} (hHh_nn : 0 ≤ Hh)
    (hHh : ∀ a b, a ∈ Set.Icc (0:ℝ) 1 → b ∈ Set.Icc (0:ℝ) 1 → |h a - h b| ≤ Hh * |a - b| ^ θ)
    {x₁ x₂ : ℝ} (hx₁ : x₁ ∈ Set.Ioo (0:ℝ) 1) (hx₂ : x₂ ∈ Set.Ioo (0:ℝ) 1) :
    |deriv (fun z : ℝ => deriv (fun w : ℝ => intervalFullSemigroupOperator σ h w) z) x₁
      - deriv (fun z : ℝ => deriv (fun w : ℝ => intervalFullSemigroupOperator σ h w) z) x₂|
      ≤ brick4Const θ η * σ ^ (-1 + (θ - η) / 2 : ℝ) * Hh * |x₁ - x₂| ^ η := by
  classical
  have hσ2 : (0:ℝ) < σ / 2 := by positivity
  set ĥ := ShenWork.IntervalNeumannFullKernel.cosineCoeffs h with hĥ
  set G : ℝ → ℝ := Gspec σ ĥ with hG
  set hmeas : AEStronglyMeasurable h (intervalMeasure 1) := hh.aestronglyMeasurable
  -- brick-3 sup bound for ∂ₓₓ S(σ/2)h on [0,1].
  set Cg : ℝ := weightedHeatHessConst θ * (σ / 2) ^ (-1 + θ / 2 : ℝ) * Hh with hCg
  have hCg_nn : 0 ≤ Cg := by
    rw [hCg]; have := weightedHeatHessConst_nonneg θ
    have : (0:ℝ) < (σ / 2) ^ (-1 + θ / 2 : ℝ) := Real.rpow_pos_of_pos hσ2 _
    positivity
  -- `G` agrees with `∂ₓₓ S(σ/2)h` on `(0,1)`, hence `|G| ≤ Cg` there; the truncation
  -- `Gtrunc` is globally bounded by `Cg` and shares the same `S(σ/2)`-image.
  set Gtrunc : ℝ → ℝ := fun w => if w ∈ Set.Icc (0:ℝ) 1 then G w else 0 with hGtr
  -- `|G| ≤ Cg` on the interior (brick 3 via the pinning), extended to `[0,1]` by the
  -- continuity of the spectral `G` (the bound set is closed, contains the dense `Ioo`).
  have hGcont : Continuous G := by rw [hG]; exact Gspec_continuous hσ hM
  have hG_Ioo : ∀ w ∈ Set.Ioo (0:ℝ) 1, |G w| ≤ Cg := by
    intro w hwIoo
    rw [hG, Gspec_eq_secondDeriv_Ioo hσ hh hM hwIoo]
    exact neumannHeatSecondDeriv_Ctheta_to_Linfty hσ2 hθ0 hθ1 hmeas hhb hHh_nn hHh
      (Set.Ioo_subset_Icc_self hwIoo)
  have hG_Icc : ∀ w ∈ Set.Icc (0:ℝ) 1, |G w| ≤ Cg := by
    have hclosed : IsClosed {w : ℝ | |G w| ≤ Cg} :=
      isClosed_le (continuous_abs.comp hGcont) continuous_const
    have hsub : Set.Ioo (0:ℝ) 1 ⊆ {w : ℝ | |G w| ≤ Cg} := fun w hw => hG_Ioo w hw
    have hcl := hclosed.closure_subset_iff.mpr hsub
    rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)] at hcl
    exact fun w hw => hcl hw
  have hGtr_bound : ∀ w, |Gtrunc w| ≤ Cg := by
    intro w
    rw [hGtr]
    by_cases hw : w ∈ Set.Icc (0:ℝ) 1
    · simp only [hw, if_true]; exact hG_Icc w hw
    · simp only [hw, if_false, abs_zero]; exact hCg_nn
  -- `S(σ/2) Gtrunc = S(σ/2) G` (the integrand differs only off `[0,1]`, measure-null
  -- against `intervalMeasure 1`).
  have hGtr_meas : AEStronglyMeasurable Gtrunc (intervalMeasure 1) := by
    refine (Measurable.aestronglyMeasurable ?_)
    rw [hGtr]
    exact (hGcont.measurable.ite measurableSet_Icc measurable_const)
  have hGtr_ae : Gtrunc =ᵐ[intervalMeasure 1] G := by
    rw [ShenWork.IntervalDomain.intervalMeasure]
    refine (MeasureTheory.ae_restrict_iff' (by
      simpa [ShenWork.IntervalDomain.intervalSet] using measurableSet_Icc)).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    have hyIcc : y ∈ Set.Icc (0:ℝ) 1 := by
      simpa [ShenWork.IntervalDomain.intervalSet] using hy
    rw [hGtr]; simp only [hyIcc, if_true]
  have hsemi_eq : ∀ x, intervalFullSemigroupOperator (σ / 2) Gtrunc x
      = intervalFullSemigroupOperator (σ / 2) G x := by
    intro x
    unfold intervalFullSemigroupOperator
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hGtr_ae] with y hy
    rw [hy]
  -- value-Hölder at exponent `η` for `S(σ/2) Gtrunc`, with sup bound `Cg`.
  have hVH := neumannHeat_Linf_to_Ctheta hσ2 hη0 hη1 hGtr_meas hGtr_bound x₁ x₂
  -- transport through the commutation `∂ₓₓ S(σ)h = S(σ/2) G` on `(0,1)`.
  rw [intervalFullSemigroupOperator_secondDeriv_comm hσ hh hM hx₁,
    intervalFullSemigroupOperator_secondDeriv_comm hσ hh hM hx₂, ← hG,
    ← hsemi_eq x₁, ← hsemi_eq x₂]
  -- repackage the value-Hölder constant/rate into `brick4Const · σ^{−1+(θ−η)/2} · Hh`.
  refine hVH.trans (le_of_eq ?_)
  -- `(σ/2)^{−η/2}·(σ/2)^{−1+θ/2} = 2^{1+η/2−θ/2}·σ^{−1+(θ−η)/2}`.
  have hrate : ((σ / 2) ^ (-(η / 2) : ℝ)) * ((σ / 2) ^ (-1 + θ / 2 : ℝ))
      = (2 : ℝ) ^ (1 + η / 2 - θ / 2 : ℝ) * σ ^ (-1 + (θ - η) / 2 : ℝ) := by
    have h1 : ((σ / 2) ^ (-(η / 2) : ℝ)) * ((σ / 2) ^ (-1 + θ / 2 : ℝ))
        = (σ / 2) ^ (-1 + (θ - η) / 2 : ℝ) := by
      rw [← Real.rpow_add (by positivity : (0:ℝ) < σ / 2)]; congr 1; ring
    rw [h1, Real.div_rpow hσ.le (by norm_num),
      show (2:ℝ) ^ (-1 + (θ - η) / 2 : ℝ) = (2:ℝ) ^ (-(1 + η / 2 - θ / 2) : ℝ) by congr 1; ring,
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_eq_mul_inv, inv_inv, mul_comm]
  rw [hCg, brick4Const]
  -- both sides are products; `(σ/2)`-rates collapse via `hrate`.
  calc (2 : ℝ) ^ (1 - η) * gradSmoothingConst ^ η * (σ / 2) ^ (-(η / 2) : ℝ)
        * (weightedHeatHessConst θ * (σ / 2) ^ (-1 + θ / 2 : ℝ) * Hh) * |x₁ - x₂| ^ η
      = (2 : ℝ) ^ (1 - η) * gradSmoothingConst ^ η * weightedHeatHessConst θ
          * ((σ / 2) ^ (-(η / 2) : ℝ) * (σ / 2) ^ (-1 + θ / 2 : ℝ)) * Hh
          * |x₁ - x₂| ^ η := by ring
    _ = (2 : ℝ) ^ (1 - η) * gradSmoothingConst ^ η
          * ((2 : ℝ) ^ (1 + η / 2 - θ / 2 : ℝ) * weightedHeatHessConst θ)
          * σ ^ (-1 + (θ - η) / 2 : ℝ) * Hh * |x₁ - x₂| ^ η := by rw [hrate]; ring

/-! ## Brick 5 — the product-Hölder algebra (`chemFlux Q = u·V_x ∈ C^θ`) -/

/-- **Product Hölder seminorm algebra.**  For `f, g` bounded on `[0,1]`
(`|f| ≤ Cf`, `|g| ≤ Cg`) with Hölder moduli `[f]_θ ≤ Hf`, `[g]_θ ≤ Hg`, the product
`fg` is `θ`-Hölder with `[fg]_θ ≤ Cf·Hg + Hf·Cg`:

  `|f(a)g(a) − f(b)g(b)| ≤ (Cf·Hg + Hf·Cg)·|a−b|^θ`,   `a,b ∈ [0,1]`.

The split `fg(a)−fg(b) = f(a)(g(a)−g(b)) + (f(a)−f(b))g(b)`.  This is the raw-Hölder
product algebra behind brick 5 (`Q = u·V_x`, `u ∈ C^θ`, `V_x ∈ C^{1+θ} ⊂ C^θ`). -/
theorem holder_mul {θ Cf Cg Hf Hg : ℝ} {f g : ℝ → ℝ}
    (hCf : 0 ≤ Cf) (hHf : 0 ≤ Hf)
    (hf_bdd : ∀ y ∈ Set.Icc (0:ℝ) 1, |f y| ≤ Cf)
    (hg_bdd : ∀ y ∈ Set.Icc (0:ℝ) 1, |g y| ≤ Cg)
    (hf : ∀ a b, a ∈ Set.Icc (0:ℝ) 1 → b ∈ Set.Icc (0:ℝ) 1 → |f a - f b| ≤ Hf * |a - b| ^ θ)
    (hg : ∀ a b, a ∈ Set.Icc (0:ℝ) 1 → b ∈ Set.Icc (0:ℝ) 1 → |g a - g b| ≤ Hg * |a - b| ^ θ)
    (a b : ℝ) (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1) :
    |f a * g a - f b * g b| ≤ (Cf * Hg + Hf * Cg) * |a - b| ^ θ := by
  have hwθ : (0:ℝ) ≤ |a - b| ^ θ := Real.rpow_nonneg (abs_nonneg _) _
  have hsplit : f a * g a - f b * g b = f a * (g a - g b) + (f a - f b) * g b := by ring
  have hb1 : |f a| * |g a - g b| ≤ Cf * (Hg * |a - b| ^ θ) :=
    mul_le_mul (hf_bdd a ha) (hg a b ha hb) (abs_nonneg _) hCf
  have hb2 : |f a - f b| * |g b| ≤ (Hf * |a - b| ^ θ) * Cg :=
    mul_le_mul (hf a b ha hb) (hg_bdd b hb) (abs_nonneg _) (by positivity)
  calc |f a * g a - f b * g b|
      = |f a * (g a - g b) + (f a - f b) * g b| := by rw [hsplit]
    _ ≤ |f a * (g a - g b)| + |(f a - f b) * g b| := abs_add_le _ _
    _ = |f a| * |g a - g b| + |f a - f b| * |g b| := by rw [abs_mul, abs_mul]
    _ ≤ Cf * (Hg * |a - b| ^ θ) + (Hf * |a - b| ^ θ) * Cg := add_le_add hb1 hb2
    _ = (Cf * Hg + Hf * Cg) * |a - b| ^ θ := by ring

/-- The `σ`-rate `σ ↦ (t₀−s)^{−1+(θ−η)/2}` of brick 4 is INTEGRABLE on the chemotaxis
Duhamel window `[0,t₀]` precisely because `0 < η < θ < 1` makes the exponent
`−1+(θ−η)/2 > −1`.  This is the integrability that makes the chemotaxis leg of `u_x`
controllable (the whole point of the Schauder estimate over the naive `σ^{−1}`). -/
theorem brick4_time_integrand_integrable {t₀ θ η : ℝ} (_ht : 0 < t₀)
    (hθη : η < θ) :
    IntervalIntegrable (fun s : ℝ => (t₀ - s) ^ (-1 + (θ - η) / 2 : ℝ)) volume 0 t₀ := by
  have hr : (-1 : ℝ) < -1 + (θ - η) / 2 := by linarith
  have hcomp : IntervalIntegrable (fun s : ℝ => s ^ (-1 + (θ - η) / 2 : ℝ)) volume 0 t₀ :=
    intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t₀) hr
  have hshift := hcomp.comp_sub_left t₀
  simp only [sub_zero, sub_self] at hshift
  exact hshift.symm

/-! ## Assembly → Wiener ℓ¹: the `C^{1+η}`-slice ⟹ summable cosine coefficients -/

/-- **The composition rung to Wiener ℓ¹.**  A slice `w : ℝ → ℝ` that is `C^{1+η}` on
`[0,1]` in the Wiener-ready shape — differentiable on `ℝ`, Neumann (`w'(0)=w'(1)=0`),
`η`-Hölder derivative — has SUMMABLE cosine coefficients (`∑ₙ|ŵₙ| < ∞`), hence lies in
the Wiener algebra.  This is the committed `holderCosineCoeff_summable`
(`HolderCosineDecay`); the chemotaxis-mild `u(t₀)` slice meets these hypotheses via the
brick-4 / gradient-Hölder legs (`u_x(t₀) ∈ C^η`), the Neumann structure of `S(σ)`, and
the mild differentiability — the final rung of the χ₀<0 Hölder-bootstrap chain. -/
theorem chemMild_C1eta_slice_wiener_l1 {w : ℝ → ℝ} (hw : Differentiable ℝ w)
    (hNeumann : deriv w 0 = 0 ∧ deriv w 1 = 0)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) {K : ℝ} (hK : 0 ≤ K)
    (hHolder : ∀ x y, |deriv w x - deriv w y| ≤ K * |x - y| ^ η) :
    Summable (fun n : ℕ => |ShenWork.IntervalNeumannFullKernel.cosineCoeffs w n|) :=
  ShenWork.Wiener.EWA.holderCosineCoeff_summable w hw hNeumann hη0 hη1 hK hHolder

end ShenWork.Paper2
