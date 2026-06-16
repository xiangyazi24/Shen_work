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
import ShenWork.Paper2.IntervalDomainL2StaticVDifference
import ShenWork.Wiener.EWA.HolderCosineDecay

open MeasureTheory
open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator
  neumannHeatSecondDeriv_Ctheta_to_Linfty weightedHeatHessConst weightedHeatHessConst_nonneg
  cosineCoeffs)
open ShenWork.IntervalDomainRegularityBootstrap (unitIntervalCosineHeatSecondValue
  unitIntervalCosineHeatSecondValue_continuous)
open ShenWork.Paper2 (intervalNeumannHeatSemigroup neumannHeat_Linf_to_Ctheta
  gradSmoothingConst gradSmoothingConst_nonneg
  intervalFullSemigroupOperator_secondDeriv_eq_secondValue_Ioo)
open ShenWork.IntervalMildPicardRegularity (cosineCoeffs_abs_le_of_continuous_bounded)

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

/-! ## RESIDUAL 1 — `Ioo → Icc` upgrade of brick 4 (spectral continuity closure) -/

/-- The propagator's second `x`-derivative `∂ₓₓS(σ)h`, written as the spectral second
value `unitIntervalCosineHeatSecondValue σ ĥ` — a globally `C²` cosine series, hence
CONTINUOUS on all of `ℝ` (incl. the endpoints `0,1`).  On the OPEN interior the two
agree (`intervalFullSemigroupOperator_secondDeriv_eq_secondValue_Ioo`); this spectral
form is the endpoint-robust representative used to close the `Icc` estimate. -/
theorem neumannHeatSecondValue_continuous {σ : ℝ} (hσ : 0 < σ) {h : ℝ → ℝ}
    {M : ℝ} (hM : ∀ n, |cosineCoeffs h n| ≤ M) :
    Continuous (fun x : ℝ => unitIntervalCosineHeatSecondValue σ (cosineCoeffs h) x) :=
  unitIntervalCosineHeatSecondValue_continuous hσ hM

/-- A real-valued Hölder bound on `[0,1]` gives continuity on `[0,1]`. -/
theorem holderBound_continuousOn_Icc {θ H : ℝ} (hθ0 : 0 < θ) (hH_nn : 0 ≤ H)
    {h : ℝ → ℝ}
    (hHolder : ∀ a b, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      |h a - h b| ≤ H * |a - b| ^ θ) :
    ContinuousOn h (Set.Icc (0 : ℝ) 1) := by
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  set A : ℝ := H + 1 with hA
  have hApos : 0 < A := by rw [hA]; linarith
  set δ : ℝ := ((ε / A) ^ (1 / θ : ℝ)) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    exact Real.rpow_pos_of_pos (by positivity) _
  refine ⟨δ, hδpos, ?_⟩
  intro a ha hab
  rw [Real.dist_eq]
  have hdist_nonneg : 0 ≤ |a - b| := abs_nonneg _
  have hdist_lt : |a - b| < δ := by simpa [Real.dist_eq] using hab
  have hpow_lt : |a - b| ^ θ < ε / A := by
    have hpow := Real.rpow_lt_rpow hdist_nonneg hdist_lt hθ0
    have hcollapse : δ ^ θ = ε / A := by
      rw [hδ]
      rw [show (1 / θ : ℝ) = θ⁻¹ by rw [one_div]]
      have hθne : θ ≠ 0 := ne_of_gt hθ0
      rw [Real.rpow_inv_rpow (by positivity : 0 ≤ ε / A) hθne]
    rwa [hcollapse] at hpow
  have hle : |h a - h b| ≤ H * |a - b| ^ θ := hHolder a b ha hb
  have hmul_le : H * |a - b| ^ θ ≤ A * |a - b| ^ θ := by
    gcongr
    rw [hA]
    linarith
  have hmul_lt : A * |a - b| ^ θ < ε := by
    have := mul_lt_mul_of_pos_left hpow_lt hApos
    rwa [mul_div_cancel₀ ε (ne_of_gt hApos)] at this
  exact lt_of_le_of_lt (hle.trans hmul_le) hmul_lt

/-- The full Neumann semigroup only sees source values on `[0,1]`. -/
theorem intervalFullSemigroupOperator_congr_on_Icc {t : ℝ} {f g : ℝ → ℝ}
    (hfg : ∀ y ∈ Set.Icc (0 : ℝ) 1, f y = g y) (x : ℝ) :
    intervalFullSemigroupOperator t f x = intervalFullSemigroupOperator t g x := by
  unfold intervalFullSemigroupOperator
  refine MeasureTheory.integral_congr_ae ?_
  rw [ShenWork.IntervalDomain.intervalMeasure]
  refine (MeasureTheory.ae_restrict_iff' (by
    simp [ShenWork.IntervalDomain.intervalSet])).mpr ?_
  refine Filter.Eventually.of_forall (fun y hy => ?_)
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [ShenWork.IntervalDomain.intervalSet] using hy
  simp [hfg y hyIcc]

/-- The literal second derivative of the propagator equals the spectral second value
on the closed interval. -/
theorem intervalFullSemigroupOperator_secondDeriv_eq_secondValue_Icc
    {σ : ℝ} (hσ : 0 < σ) {h : ℝ → ℝ} (hh : Continuous h) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs h n| ≤ M) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    deriv (fun z : ℝ => deriv
        (fun w : ℝ => intervalFullSemigroupOperator σ h w) z) x
      = unitIntervalCosineHeatSecondValue σ (cosineCoeffs h) x := by
  set S : ℝ → ℝ := fun w => intervalFullSemigroupOperator σ h w with hS
  set F : ℝ → ℝ := fun w => unitIntervalCosineHeatSecondValue σ (cosineCoeffs h) w with hF
  have hS2 : ContDiff ℝ 2 S := by
    rw [hS]
    exact ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_contDiff_two_clean
      hσ hh hM
  have hSderiv : ContDiff ℝ 1 (deriv S) := by
    simpa using (hS2.deriv' : ContDiff ℝ 1 (deriv S))
  have hLcont : Continuous (fun w : ℝ => deriv (fun z : ℝ => deriv S z) w) :=
    hSderiv.continuous_deriv (by norm_num : (1 : WithTop ℕ∞) ≤ 1)
  have hFcont : Continuous F := by
    rw [hF]
    exact neumannHeatSecondValue_continuous hσ hM
  have hEqOn : Set.EqOn
      (fun w : ℝ => deriv (fun z : ℝ => deriv S z) w) F
      (Set.Ioo (0 : ℝ) 1) := by
    intro y hy
    rw [hS, hF]
    exact intervalFullSemigroupOperator_secondDeriv_eq_secondValue_Ioo hσ hh hM hy
  have hclos := hEqOn.closure hLcont hFcont
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hclos
  simpa [hS, hF] using hclos hx

/-- **Brick 4, Route B — the `C^θ → C^η` second-derivative estimate on the CLOSED
interval `Icc 0 1`.**  Stated on the spectral second value
`F := unitIntervalCosineHeatSecondValue σ ĥ` (which equals `∂ₓₓS(σ)h` on the interior,
`neumannHeatSecondValue_eq_secondDeriv_Ioo` below):

  `|F x₁ − F x₂| ≤ brick4Const θ η · σ^{−1+(θ−η)/2} · Hh · |x₁−x₂|^η`,  `x₁,x₂∈[0,1]`.

PROOF: `F` is continuous on `ℝ` (`neumannHeatSecondValue_continuous`), the RHS is
continuous in `(x₁,x₂)`, and the `Ioo` inequality (`neumannHeatSecondDerivCthetaToCeta_routeB`
transported through the interior pinning) holds on the dense `Ioo×Ioo`.  The bound set
`{p | |F p.1 − F p.2| ≤ RHS p.1 p.2}` is closed and contains `Ioo×Ioo`, hence contains
its closure `Icc×Icc = closure (Ioo×Ioo)`. -/
theorem neumannHeatSecondDerivCthetaToCeta_routeB_Icc {σ θ η : ℝ} (hσ : 0 < σ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hη0 : 0 < η) (hη1 : η < 1)
    {h : ℝ → ℝ} (hh : Continuous h)
    {M : ℝ} (hM : ∀ n, |ShenWork.IntervalNeumannFullKernel.cosineCoeffs h n| ≤ M)
    {Ch : ℝ} (hhb : ∀ y, |h y| ≤ Ch) {Hh : ℝ} (hHh_nn : 0 ≤ Hh)
    (hHh : ∀ a b, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      |h a - h b| ≤ Hh * |a - b| ^ θ)
    {x₁ x₂ : ℝ} (hx₁ : x₁ ∈ Set.Icc (0 : ℝ) 1)
    (hx₂ : x₂ ∈ Set.Icc (0 : ℝ) 1) :
    |unitIntervalCosineHeatSecondValue σ (cosineCoeffs h) x₁
      - unitIntervalCosineHeatSecondValue σ (cosineCoeffs h) x₂|
      ≤ brick4Const θ η * σ ^ (-1 + (θ - η) / 2 : ℝ) * Hh * |x₁ - x₂| ^ η := by
  classical
  set F : ℝ → ℝ := fun x => unitIntervalCosineHeatSecondValue σ (cosineCoeffs h) x with hF
  set R : ℝ × ℝ → ℝ := fun p =>
    brick4Const θ η * σ ^ (-1 + (θ - η) / 2 : ℝ) * Hh * |p.1 - p.2| ^ η with hR
  -- both sides as continuous functions on `ℝ × ℝ`
  have hFcont : Continuous F := neumannHeatSecondValue_continuous hσ hM
  have hLHS : Continuous (fun p : ℝ × ℝ => |F p.1 - F p.2|) :=
    (continuous_abs.comp ((hFcont.comp continuous_fst).sub (hFcont.comp continuous_snd)))
  have hRHS : Continuous R := by
    rw [hR]
    exact continuous_const.mul
      ((continuous_fst.sub continuous_snd).abs.rpow_const (fun _ => Or.inr hη0.le))
  -- the bound set is closed and contains the open square `Ioo × Ioo`
  set Sset : Set (ℝ × ℝ) := {p | |F p.1 - F p.2| ≤ R p} with hSset
  have hclosed : IsClosed Sset := isClosed_le hLHS hRHS
  have hsub : Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1 ⊆ Sset := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    have hFa : F a = deriv (fun z : ℝ =>
        deriv (fun w : ℝ => intervalFullSemigroupOperator σ h w) z) a :=
      (intervalFullSemigroupOperator_secondDeriv_eq_secondValue_Ioo hσ hh hM ha).symm
    have hFb : F b = deriv (fun z : ℝ =>
        deriv (fun w : ℝ => intervalFullSemigroupOperator σ h w) z) b :=
      (intervalFullSemigroupOperator_secondDeriv_eq_secondValue_Ioo hσ hh hM hb).symm
    change |F a - F b| ≤ R (a, b)
    rw [hFa, hFb, hR]
    exact neumannHeatSecondDerivCthetaToCeta_routeB hσ hθ0 hθ1 hη0 hη1 hh hM hhb hHh_nn hHh ha hb
  -- close the inequality on `Icc × Icc = closure (Ioo × Ioo)`
  have hmem : (x₁, x₂) ∈ Sset := by
    have hclo : (x₁, x₂) ∈ closure (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) := by
      rw [closure_prod_eq, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
      exact ⟨hx₁, hx₂⟩
    exact (hclosed.closure_subset_iff.mpr hsub) hclo
  exact hmem

/-- **Brick 4, Route B — literal closed-interval form.**  This is the same estimate
as `neumannHeatSecondDerivCthetaToCeta_routeB_Icc`, transported through the closed
pinning between the literal second derivative and the spectral second value. -/
theorem neumannHeatSecondDerivCthetaToCeta_routeB_literal_Icc {σ θ η : ℝ}
    (hσ : 0 < σ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hη0 : 0 < η)
    (hη1 : η < 1) {h : ℝ → ℝ} (hh : Continuous h)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs h n| ≤ M)
    {Ch : ℝ} (hhb : ∀ y, |h y| ≤ Ch) {Hh : ℝ} (hHh_nn : 0 ≤ Hh)
    (hHh : ∀ a b, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      |h a - h b| ≤ Hh * |a - b| ^ θ)
    {x₁ x₂ : ℝ} (hx₁ : x₁ ∈ Set.Icc (0 : ℝ) 1)
    (hx₂ : x₂ ∈ Set.Icc (0 : ℝ) 1) :
    |deriv (fun z : ℝ => deriv
          (fun w : ℝ => intervalFullSemigroupOperator σ h w) z) x₁
        - deriv (fun z : ℝ => deriv
          (fun w : ℝ => intervalFullSemigroupOperator σ h w) z) x₂|
      ≤ brick4Const θ η * σ ^ (-1 + (θ - η) / 2 : ℝ) * Hh
        * |x₁ - x₂| ^ η := by
  rw [intervalFullSemigroupOperator_secondDeriv_eq_secondValue_Icc hσ hh hM hx₁,
    intervalFullSemigroupOperator_secondDeriv_eq_secondValue_Icc hσ hh hM hx₂]
  exact neumannHeatSecondDerivCthetaToCeta_routeB_Icc hσ hθ0 hθ1 hη0 hη1
    hh hM hhb hHh_nn hHh hx₁ hx₂

/-- **Brick 4 exact witness.**  The conclusion-shaped Schauder hypothesis is
discharged with the explicit Route-B constant `brick4Const θ η`.  The source in the
packaged hypothesis is only measurable and bounded; the proof replaces it by its
continuous clamped representative on `[0,1]`, which has the same propagator. -/
theorem neumannHeatSecondDeriv_Ctheta_to_Ceta {θ η : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hη0 : 0 < η) (hη1 : η < 1) :
    NeumannHeatSecondDerivCthetaToCeta θ η (brick4Const θ η) := by
  classical
  intro σ hσ h _hmeas Ch hhb Hh hHh_nn hHh x₁ x₂ hx₁ hx₂
  set hc : ℝ → ℝ := fun x => h (clamp01 x) with hhc_def
  have hcontOn : ContinuousOn h (Set.Icc (0 : ℝ) 1) :=
    holderBound_continuousOn_Icc hθ0 hHh_nn hHh
  have hhc_cont : Continuous hc := by
    have hmaps : Set.MapsTo clamp01 Set.univ (Set.Icc (0 : ℝ) 1) :=
      fun x _ => clamp01_mem x
    have hcomp : ContinuousOn hc Set.univ := by
      rw [hhc_def]
      exact hcontOn.comp clamp01_continuous.continuousOn hmaps
    exact continuousOn_univ.mp hcomp
  have hhc_eq : ∀ x ∈ Set.Icc (0 : ℝ) 1, hc x = h x := by
    intro x hx
    rw [hhc_def]
    change h (clamp01 x) = h x
    rw [clamp01_eq_self hx]
  have hS_eq : (fun w : ℝ => intervalFullSemigroupOperator σ h w)
      = fun w : ℝ => intervalFullSemigroupOperator σ hc w := by
    funext w
    exact intervalFullSemigroupOperator_congr_on_Icc
      (fun y hy => (hhc_eq y hy).symm) w
  have hCh_nn : 0 ≤ Ch := le_trans (abs_nonneg (h 0)) (hhb 0)
  have hhc_bound : ∀ y, |hc y| ≤ Ch := by
    intro y
    rw [hhc_def]
    exact hhb (clamp01 y)
  have hM : ∀ n, |cosineCoeffs hc n| ≤ 2 * Ch :=
    cosineCoeffs_abs_le_of_continuous_bounded hhc_cont.continuousOn hCh_nn
      (fun y _hy => hhc_bound y)
  have hhc_holder : ∀ a b, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      |hc a - hc b| ≤ Hh * |a - b| ^ θ := by
    intro a b ha hb
    rw [hhc_eq a ha, hhc_eq b hb]
    exact hHh a b ha hb
  rw [hS_eq]
  exact neumannHeatSecondDerivCthetaToCeta_routeB_literal_Icc hσ hθ0 hθ1 hη0
    hη1 hhc_cont hM hhc_bound hHh_nn hhc_holder hx₁ hx₂

/-- `∂ₓₓS(σ)h` (literal second derivative) equals the spectral second value `F` on the
OPEN interior, packaging the pinning for downstream chemotaxis-leg integrands. -/
theorem neumannHeatSecondValue_eq_secondDeriv_Ioo {σ : ℝ} (hσ : 0 < σ) {h : ℝ → ℝ}
    (hh : Continuous h) {M : ℝ} (hM : ∀ n, |cosineCoeffs h n| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (fun z : ℝ => deriv (fun w : ℝ => intervalFullSemigroupOperator σ h w) z) x
      = unitIntervalCosineHeatSecondValue σ (cosineCoeffs h) x :=
  intervalFullSemigroupOperator_secondDeriv_eq_secondValue_Ioo hσ hh hM hx

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

/-! ## DISCHARGE of the chemotaxis-leg Hölder: `chemLeg_holder_of_brick4`

The chemotaxis Duhamel leg
  `chemLeg(x) = ∫₀^{t₀} (∂ₓₓ S(t₀−s) Q(s))(x) ds`
is the integral over `[0,t₀]` of the brick-4 second-derivative integrand, applied to the
chemotaxis flux `Q(s) = chemFluxLifted u(s)`.  We DISCHARGE its `η`-Hölder bound by
applying brick 4 (Route B, `neumannHeatSecondDerivCthetaToCeta_routeB_Icc`) per slice and
integrating with the integral-Minkowski core `holder_of_duhamel_integral`, the brick-4 time
integrand `(t₀−s)^{−1+(θ−η)/2}` being integrable (`brick4_time_integrand_integrable`).

The leg integrand is taken in the spectral second-value form
`F s x = unitIntervalCosineHeatSecondValue (t₀−s) (cosineCoeffs (Q s)) (clamp01 x)`, equal to
`∂ₓₓS(t₀−s)Q(s)` on `(0,1)` (`neumannHeatSecondValue_eq_secondDeriv_Ioo`); the `clamp01`
makes the bound GLOBAL in `x` (the brick is on `[0,1]`, and `clamp01` is `1`-Lipschitz, so
the `Icc` modulus transports to all of `ℝ` with the same constant — exactly the global shape
the downstream `holderCosineCoeff_summable` needs).  The per-slice integrability of the leg
integrand is the only carried datum (representation well-definedness of the Duhamel integral
defining `chemLeg`), NOT a Hölder/Neumann/bound conclusion. -/

/-- `clamp01` is `1`-Lipschitz: `|clamp01 x − clamp01 y| ≤ |x − y|`.  Used to transport the
brick-4 `Icc`-Hölder of the second-derivative integrand to a GLOBAL Hölder of the clamped
integrand. -/
theorem clamp01_abs_sub_le (x y : ℝ) : |clamp01 x - clamp01 y| ≤ |x - y| := by
  have hlip : LipschitzWith 1 clamp01 :=
    ((LipschitzWith.id.const_min (1 : ℝ)).const_max (0 : ℝ))
  have := hlip.dist_le_mul x y
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using this

/-- **`chemLeg_holder_of_brick4` — the chemotaxis-leg Hölder bound, DISCHARGED.**

For a per-slice source family `Q : ℝ → ℝ → ℝ` whose slices `Q s` are continuous with
uniformly bounded cosine coefficients (`|ĉₙ(Q s)| ≤ M`), uniformly sup-bounded
(`|Q s y| ≤ CQ`) and uniformly `θ`-Hölder on `[0,1]` (`[Q s]_θ ≤ HQ`), the clamped
chemotaxis Duhamel leg
  `chemLeg(x) = ∫₀^{t₀} unitIntervalCosineHeatSecondValue (t₀−s) (ĉ(Q s)) (clamp01 x) ds`
is GLOBALLY `η`-Hölder with constant
  `Achem = ∫₀^{t₀} brick4Const θ η · (t₀−s)^{−1+(θ−η)/2} · HQ ds`:

  `|chemLeg x₁ − chemLeg x₂| ≤ Achem · |x₁ − x₂|^η`,   `x₁,x₂ ∈ ℝ`.

PROOF: per slice, brick 4 (Route B, `neumannHeatSecondDerivCthetaToCeta_routeB_Icc`) bounds
the integrand difference at `clamp01 x₁, clamp01 x₂ ∈ [0,1]`; `clamp01` `1`-Lipschitz turns
`|clamp01 x₁ − clamp01 x₂|^η ≤ |x₁ − x₂|^η` into the global modulus; integrate with
`holder_of_duhamel_integral`, the time integrand integrable by `brick4_time_integrand_integrable`.
The per-slice integrability of the leg integrand (`hG_int`/`hH_int`) is the representation
datum (the Duhamel integral defining `chemLeg` is well-defined). -/
theorem chemLeg_holder_of_brick4 {t₀ θ η M CQ HQ : ℝ} {Q : ℝ → ℝ → ℝ}
    (ht₀ : 0 < t₀) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hη0 : 0 < η) (hη1 : η < 1) (hθη : η < θ)
    (hHQ_nn : 0 ≤ HQ)
    (hQcont : ∀ s ∈ Set.Ioo (0:ℝ) t₀, Continuous (Q s))
    (hQcoeff : ∀ s ∈ Set.Ioo (0:ℝ) t₀, ∀ n, |cosineCoeffs (Q s) n| ≤ M)
    (hQbdd : ∀ s ∈ Set.Ioo (0:ℝ) t₀, ∀ y, |Q s y| ≤ CQ)
    (hQholder : ∀ s ∈ Set.Ioo (0:ℝ) t₀, ∀ a b, a ∈ Set.Icc (0:ℝ) 1 →
      b ∈ Set.Icc (0:ℝ) 1 → |Q s a - Q s b| ≤ HQ * |a - b| ^ θ)
    (x₁ x₂ : ℝ)
    (hG_int : IntervalIntegrable
      (fun s => unitIntervalCosineHeatSecondValue (t₀ - s) (cosineCoeffs (Q s)) (clamp01 x₁))
      volume 0 t₀)
    (hH_int : IntervalIntegrable
      (fun s => unitIntervalCosineHeatSecondValue (t₀ - s) (cosineCoeffs (Q s)) (clamp01 x₂))
      volume 0 t₀) :
    |(∫ s in (0:ℝ)..t₀,
        unitIntervalCosineHeatSecondValue (t₀ - s) (cosineCoeffs (Q s)) (clamp01 x₁))
      - (∫ s in (0:ℝ)..t₀,
        unitIntervalCosineHeatSecondValue (t₀ - s) (cosineCoeffs (Q s)) (clamp01 x₂))|
      ≤ (∫ s in (0:ℝ)..t₀, brick4Const θ η * (t₀ - s) ^ (-1 + (θ - η) / 2 : ℝ) * HQ)
        * |x₁ - x₂| ^ η := by
  classical
  -- the time integrand `φ s = brick4Const · (t₀−s)^{−1+(θ−η)/2} · HQ` is integrable
  have hφ_int : IntervalIntegrable
      (fun s : ℝ => brick4Const θ η * (t₀ - s) ^ (-1 + (θ - η) / 2 : ℝ) * HQ) volume 0 t₀ := by
    have h0 := brick4_time_integrand_integrable (θ := θ) (η := η) ht₀ hθη
    have h1 := h0.const_mul (brick4Const θ η)
    have h2 := h1.mul_const HQ
    exact h2.congr (fun s _ => by ring)
  refine holder_of_duhamel_integral ht₀.le hG_int hH_int hφ_int ?_
  -- a.e. on `[0,t₀]`: the per-slice brick-4 bound transported through `clamp01`
  have hne : ∀ᵐ s ∂volume, s ≠ (0:ℝ) ∧ s ≠ t₀ := by
    have h0 : ∀ᵐ s ∂volume, s ≠ (0:ℝ) := by
      rw [ae_iff]; simp only [not_not, Set.setOf_eq_eq_singleton]; exact Real.volume_singleton
    have ht : ∀ᵐ s ∂volume, s ≠ t₀ := by
      rw [ae_iff]; simp only [not_not, Set.setOf_eq_eq_singleton]; exact Real.volume_singleton
    filter_upwards [h0, ht] with s hs0 hst using ⟨hs0, hst⟩
  refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
  filter_upwards [hne] with s hs hs_mem
  have hsIoo : s ∈ Set.Ioo (0:ℝ) t₀ :=
    ⟨lt_of_le_of_ne hs_mem.1 (Ne.symm hs.1), lt_of_le_of_ne hs_mem.2 hs.2⟩
  have hts : 0 < t₀ - s := sub_pos.mpr hsIoo.2
  -- brick 4 (Route B, Icc) on the clamped arguments
  have hbrick := neumannHeatSecondDerivCthetaToCeta_routeB_Icc hts hθ0 hθ1 hη0 hη1
    (hQcont s hsIoo) (hQcoeff s hsIoo) (hQbdd s hsIoo) hHQ_nn (hQholder s hsIoo)
    (clamp01_mem x₁) (clamp01_mem x₂)
  -- `|clamp01 x₁ − clamp01 x₂|^η ≤ |x₁ − x₂|^η` (clamp01 `1`-Lipschitz, `rpow` monotone)
  have hclamp : |clamp01 x₁ - clamp01 x₂| ^ η ≤ |x₁ - x₂| ^ η :=
    Real.rpow_le_rpow (abs_nonneg _) (clamp01_abs_sub_le x₁ x₂) hη0.le
  refine hbrick.trans ?_
  have hcoef_nn : 0 ≤ brick4Const θ η * (t₀ - s) ^ (-1 + (θ - η) / 2 : ℝ) * HQ := by
    have := brick4Const_nonneg θ η
    have : (0:ℝ) ≤ (t₀ - s) ^ (-1 + (θ - η) / 2 : ℝ) := (Real.rpow_pos_of_pos hts _).le
    positivity
  exact mul_le_mul_of_nonneg_left hclamp hcoef_nn

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
