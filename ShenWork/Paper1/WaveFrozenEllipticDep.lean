/-
  ShenWork/Paper1/WaveFrozenEllipticDep.lean

  The single genuinely-deep analytic brick of the B1 Rothe continuity-in-`u`
  field: continuous dependence of the frozen elliptic drift `V_u' =
  deriv (frozenElliptic p u)` on the profile `u`, in the locally-uniform
  topology.

  This discharges the carried hypothesis `FrozenEllipticDerivDependence`
  consumed (through `RotheContinuousDependence`) by `Tmap_continuousOn`
  in `WaveRotheSchauderData.lean`.

  ROUTE (dominated/ε-split on the convolution).  By the committed kernel
  representation (`frozenElliptic p u = Psi (u^γ) 1 1`), the Leibniz rule
  `hasDerivAt_integral_exp_neg_mul_abs_sub_general` (committed in
  `ShenWork.PDE.LeibnizRule`) gives the derivative kernel representation

      `V_u'(x) = deriv (frozenElliptic p u) x
               = ½ ∫_ℝ Dker(x,y) · (u y)^γ dy`,

  where `Dker(x,y) = if y ≤ x then -e^{-(x-y)} else e^{-(y-x)}`, so that
  `|Dker(x,y)| = e^{-|x-y|}` and `Dker(x,·) ∈ L¹` (the Green-kernel
  derivative).  Hence for two trapped profiles `u_n, u`,

      `V_{u_n}'(x) - V_u'(x) = ½ ∫_ℝ Dker(x,y) · ((u_n y)^γ - (u y)^γ) dy`,

  and, bounding `|(u_n y)^γ - (u y)^γ| ≤ L · |u_n y - u y|` (committed
  `rpow_m_lipschitz_on_Icc`, `L = γ M^{γ-1}`) and `|(·)^γ| ≤ M^γ` (trap),

      `|V_{u_n}'(x) - V_u'(x)|
         ≤ ½ ∫_ℝ e^{-|x-y|} · |(u_n y)^γ - (u y)^γ| dy.`

  Splitting the `y`-integral at `|y| ≤ R'` (where loc-unif convergence makes
  `sup_{[-R',R']} |u_n - u|` small) and `|y| > R'` (where the kernel tail
  `e^{-|x-y|}` is uniformly small for `x ∈ [-R,R]`, since both `(·)^γ ≤ M^γ`)
  yields `‖V_{u_n}' - V_u'‖_{[-R,R]} → 0`, i.e. local-uniform convergence.

  Only the committed kernel-representation pieces (`frozenElliptic = Psi(u^γ)`,
  `hasDerivAt_integral_exp_neg_mul_abs_sub_general`), the committed power
  Lipschitz bound, and the trap projections are used; the derivative kernel
  representation itself is DERIVED here (it is not separately committed).
-/
import ShenWork.Paper1.WaveEllipticMono
import ShenWork.Paper1.WaveRotheStep
import ShenWork.Paper1.WaveRotheSchauderData
import ShenWork.PDE.LeibnizRule

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-! ## The derivative kernel and its representation -/

/-- The Green-kernel derivative `∂_x e^{-|x-y|}`, equal to
`-e^{-(x-y)}` for `y ≤ x` and `e^{-(y-x)}` for `y > x`.  Its absolute value is
`e^{-|x-y|}`. -/
def frozenEllipticDerivKernel (x y : ℝ) : ℝ :=
  if y ≤ x then -Real.exp (-(x - y)) else Real.exp (-(y - x))

theorem frozenEllipticDerivKernel_abs_le (x y : ℝ) :
    |frozenEllipticDerivKernel x y| ≤ Real.exp (-|x - y|) := by
  unfold frozenEllipticDerivKernel
  by_cases hyx : y ≤ x
  · simp only [hyx, if_true]
    rw [abs_neg, abs_of_pos (Real.exp_pos _)]
    have : |x - y| = x - y := abs_of_nonneg (by linarith)
    rw [this]
  · simp only [hyx, if_false]
    rw [abs_of_pos (Real.exp_pos _)]
    have hxy : x < y := lt_of_not_ge hyx
    have : |x - y| = y - x := by rw [abs_of_neg (by linarith)]; ring
    rw [this]

/-- The derivative kernel representation of `frozenElliptic`.  Derived from the
committed Leibniz rule `hasDerivAt_integral_exp_neg_mul_abs_sub_general`
(specialised to `a = 1`) plus the committed kernel form
`frozenElliptic = Psi(u^γ) = ½ ∫ e^{-|x-y|} u^γ`. -/
theorem frozenElliptic_deriv_eq_kernel_integral
    (p : CMParams) {u : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ x, 0 ≤ u x) (x : ℝ) :
    deriv (frozenElliptic p u) x =
      1 / 2 * ∫ y, frozenEllipticDerivKernel x y * (u y) ^ p.γ := by
  have hg : IsCUnifBdd (fun y => (u y) ^ p.γ) :=
    rpow_cunif_bdd_of_nonneg p hu hu_nonneg
  -- frozenElliptic p u = (1/2) ∫ e^{-|·-y|} (u y)^γ
  have hfun :
      frozenElliptic p u =
        fun z => 1 / 2 * ∫ y, Real.exp (-(1 : ℝ) * |z - y|) * (u y) ^ p.γ := by
    funext z
    rw [frozenElliptic_eq_kernel_integral]
  -- Leibniz: derivative of the inner integral at x
  have hLeib :
      HasDerivAt
        (fun z => ∫ y, Real.exp (-(1 : ℝ) * |z - y|) * (u y) ^ p.γ)
        (∫ y,
          if y ≤ x then
            -(1 : ℝ) * Real.exp (-(1 : ℝ) * (x - y)) * (u y) ^ p.γ
          else (1 : ℝ) * Real.exp (-(1 : ℝ) * (y - x)) * (u y) ^ p.γ) x :=
    hasDerivAt_integral_exp_neg_mul_abs_sub_general (a := 1) one_pos hg x
  have hda :
      HasDerivAt (frozenElliptic p u)
        (1 / 2 * ∫ y,
          if y ≤ x then
            -(1 : ℝ) * Real.exp (-(1 : ℝ) * (x - y)) * (u y) ^ p.γ
          else (1 : ℝ) * Real.exp (-(1 : ℝ) * (y - x)) * (u y) ^ p.γ) x := by
    rw [hfun]
    exact hLeib.const_mul (1 / 2)
  rw [hda.deriv]
  congr 1
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun y => ?_)
  unfold frozenEllipticDerivKernel
  by_cases hyx : y ≤ x
  · simp only [hyx, if_true]
    have : -(1 : ℝ) * (x - y) = -(x - y) := by ring
    rw [this]; ring
  · simp only [hyx, if_false]
    have : -(1 : ℝ) * (y - x) = -(y - x) := by ring
    rw [this]; ring

/-! ## Integrability of the kernel against a bounded profile -/

theorem frozenEllipticDerivKernel_mul_integrable
    {g : ℝ → ℝ} (hg : IsCUnifBdd g) (x : ℝ) :
    Integrable (fun y => frozenEllipticDerivKernel x y * g y) := by
  rcases hg.2 with ⟨M, hM⟩
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (g 0)) (hM 0)
  -- dominate by e^{-|x-y|} * M  (constant profile M is cunif-bdd)
  have hMconst : IsCUnifBdd (fun _ : ℝ => M) :=
    ⟨continuous_const, ⟨|M|, fun _ => le_refl |M|⟩⟩
  have hdom : Integrable (fun y => Real.exp (-(1 : ℝ) * |x - y|) * M) := by
    have hbase :=
      Psi_kernel_integrable_of_isCUnifBdd (u := fun _ : ℝ => M) (l := 1) one_pos hMconst x
    simpa [Real.sqrt_one] using hbase
  have hmeas : AEStronglyMeasurable
      (fun y => frozenEllipticDerivKernel x y * g y) volume := by
    have hker : AEStronglyMeasurable (fun y => frozenEllipticDerivKernel x y) volume := by
      have hpiece : StronglyMeasurable
          ((Set.Iic x).piecewise
            (fun y : ℝ => -Real.exp (-(x - y)))
            (fun y : ℝ => Real.exp (-(y - x)))) :=
        StronglyMeasurable.piecewise measurableSet_Iic
          (by fun_prop : Continuous fun y : ℝ => -Real.exp (-(x - y))).stronglyMeasurable
          (by fun_prop : Continuous fun y : ℝ => Real.exp (-(y - x))).stronglyMeasurable
      refine hpiece.aestronglyMeasurable.congr ?_
      filter_upwards with y
      unfold frozenEllipticDerivKernel Set.piecewise
      simp only [Set.mem_Iic]
    exact hker.mul hg.1.aestronglyMeasurable
  refine Integrable.mono' hdom hmeas (Filter.Eventually.of_forall (fun y => ?_))
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |frozenEllipticDerivKernel x y| ≤ Real.exp (-(1 : ℝ) * |x - y|) := by
    have := frozenEllipticDerivKernel_abs_le x y
    have heq : Real.exp (-|x - y|) = Real.exp (-(1 : ℝ) * |x - y|) := by
      congr 1; ring
    rw [heq] at this; exact this
  have h2 : |g y| ≤ M := hM y
  exact mul_le_mul h1 h2 (abs_nonneg _) (Real.exp_nonneg _)

/-! ## Pointwise difference bound -/

/-- The derivative difference equals `½` times the kernel integrated against the
difference of the powers. -/
theorem frozenElliptic_deriv_diff_eq
    (p : CMParams) {u v : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ x, 0 ≤ u x)
    (hv : IsCUnifBdd v) (hv_nonneg : ∀ x, 0 ≤ v x) (x : ℝ) :
    deriv (frozenElliptic p u) x - deriv (frozenElliptic p v) x =
      1 / 2 * ∫ y, frozenEllipticDerivKernel x y *
        ((u y) ^ p.γ - (v y) ^ p.γ) := by
  rw [frozenElliptic_deriv_eq_kernel_integral p hu hu_nonneg,
      frozenElliptic_deriv_eq_kernel_integral p hv hv_nonneg]
  have hgu : IsCUnifBdd (fun y => (u y) ^ p.γ) :=
    rpow_cunif_bdd_of_nonneg p hu hu_nonneg
  have hgv : IsCUnifBdd (fun y => (v y) ^ p.γ) :=
    rpow_cunif_bdd_of_nonneg p hv hv_nonneg
  have hintu := frozenEllipticDerivKernel_mul_integrable hgu x
  have hintv := frozenEllipticDerivKernel_mul_integrable hgv x
  rw [← mul_sub, ← integral_sub hintu hintv]
  congr 1
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun y => ?_)
  ring

/-- The derivative difference is bounded by `½` times the convolution of the
kernel envelope `e^{-|x-y|}` against the pointwise difference of the powers. -/
theorem frozenElliptic_deriv_diff_abs_le
    (p : CMParams) {u v : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ x, 0 ≤ u x)
    (hv : IsCUnifBdd v) (hv_nonneg : ∀ x, 0 ≤ v x) (x : ℝ) :
    |deriv (frozenElliptic p u) x - deriv (frozenElliptic p v) x| ≤
      1 / 2 * ∫ y, Real.exp (-|x - y|) *
        |(u y) ^ p.γ - (v y) ^ p.γ| := by
  rw [frozenElliptic_deriv_diff_eq p hu hu_nonneg hv hv_nonneg]
  have hgu : IsCUnifBdd (fun y => (u y) ^ p.γ) :=
    rpow_cunif_bdd_of_nonneg p hu hu_nonneg
  have hgv : IsCUnifBdd (fun y => (v y) ^ p.γ) :=
    rpow_cunif_bdd_of_nonneg p hv hv_nonneg
  have hdiff_cunif : IsCUnifBdd (fun y => (u y) ^ p.γ - (v y) ^ p.γ) := by
    refine ⟨hgu.1.sub hgv.1, ?_⟩
    rcases hgu.2 with ⟨Mu, hMu⟩
    rcases hgv.2 with ⟨Mv, hMv⟩
    exact ⟨Mu + Mv, fun y => le_trans (abs_sub _ _) (add_le_add (hMu y) (hMv y))⟩
  rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1/2)
  have hint := frozenEllipticDerivKernel_mul_integrable hdiff_cunif x
  have habs_cunif : IsCUnifBdd (fun y => |(u y) ^ p.γ - (v y) ^ p.γ|) := by
    refine ⟨hdiff_cunif.1.abs, ?_⟩
    rcases hdiff_cunif.2 with ⟨B, hB⟩
    exact ⟨B, fun y => by rw [abs_abs]; exact hB y⟩
  have henv_int :
      Integrable (fun y => Real.exp (-|x - y|) *
        |(u y) ^ p.γ - (v y) ^ p.γ|) := by
    rcases habs_cunif.2 with ⟨B, hB⟩
    have hdom : Integrable (fun y => Real.exp (-(1:ℝ) * |x - y|) * B) := by
      have hBconst : IsCUnifBdd (fun _ : ℝ => B) :=
        ⟨continuous_const, ⟨|B|, fun _ => le_refl |B|⟩⟩
      simpa [Real.sqrt_one] using
        Psi_kernel_integrable_of_isCUnifBdd (u := fun _ : ℝ => B) (l := 1) one_pos hBconst x
    have hmeas : AEStronglyMeasurable
        (fun y => Real.exp (-|x - y|) * |(u y) ^ p.γ - (v y) ^ p.γ|) volume :=
      ((by fun_prop : Continuous fun y : ℝ =>
        Real.exp (-|x - y|)).aestronglyMeasurable).mul habs_cunif.1.aestronglyMeasurable
    refine Integrable.mono' hdom hmeas (Filter.Eventually.of_forall (fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hee : Real.exp (-|x - y|) = Real.exp (-(1:ℝ) * |x - y|) := by congr 1; ring
    rw [hee]
    have : |(u y) ^ p.γ - (v y) ^ p.γ| ≤ B := by have := hB y; rwa [abs_abs] at this
    exact mul_le_mul_of_nonneg_left this (Real.exp_nonneg _)
  calc |∫ y, frozenEllipticDerivKernel x y * ((u y) ^ p.γ - (v y) ^ p.γ)|
      = ‖∫ y, frozenEllipticDerivKernel x y * ((u y) ^ p.γ - (v y) ^ p.γ)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ y, ‖frozenEllipticDerivKernel x y * ((u y) ^ p.γ - (v y) ^ p.γ)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y, Real.exp (-|x - y|) * |(u y) ^ p.γ - (v y) ^ p.γ| := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun y => norm_nonneg _)
        · exact henv_int
        · refine Filter.Eventually.of_forall (fun y => ?_)
          simp only []
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right
            (frozenEllipticDerivKernel_abs_le x y) (abs_nonneg _)

/-- The kernel envelope integrates to `2` (translation-invariant). -/
theorem exp_neg_abs_sub_integral_eq (x : ℝ) :
    ∫ y, Real.exp (-|x - y|) = 2 := by
  have hP := Psi_const (c := 1) (by norm_num) x
  unfold Psi at hP
  rw [Real.sqrt_one] at hP
  -- hP : 1 / (2*1) * ∫ y, exp(-1*|x-y|)*1 = 1
  have hsimp : (fun y : ℝ => Real.exp (-1 * |x - y|) * (1 : ℝ))
             = fun y => Real.exp (-|x - y|) := by
    funext y; rw [mul_one]; congr 1; ring
  rw [hsimp] at hP
  have : (1 : ℝ) / (2 * 1) * ∫ y, Real.exp (-|x - y|) = 1 := hP
  linarith [this]

/-! ## Kernel tail estimates -/

/-- The kernel envelope `e^{-|x-y|}` is globally integrable in `y`. -/
theorem exp_neg_abs_sub_integrable (x : ℝ) :
    Integrable (fun y => Real.exp (-|x - y|)) := by
  have hconst : IsCUnifBdd (fun _ : ℝ => (1 : ℝ)) :=
    ⟨continuous_const, ⟨1, fun _ => by simp⟩⟩
  have hbase :=
    Psi_kernel_integrable_of_isCUnifBdd (u := fun _ : ℝ => (1 : ℝ)) (l := 1) one_pos hconst x
  have : (fun y : ℝ => Real.exp (-Real.sqrt 1 * |x - y|) * (1 : ℝ))
       = fun y : ℝ => Real.exp (-|x - y|) := by
    funext y; rw [Real.sqrt_one]; ring_nf
  rwa [this] at hbase

/-- Upper-tail bound: for `R' ≤ x`, `∫_{y > R'... }`... we instead bound the
right tail `∫_{y ≥ R'} e^{-|x-y|}` for `x ≤ R'`.  Here `x ≤ y` so
`|x-y| = y-x`, and `e^{-(y-x)} = e^{x}·e^{-y}`. -/
theorem exp_neg_abs_sub_Ici_le {x R' : ℝ} (hxR' : x ≤ R') :
    ∫ y in Ici R', Real.exp (-|x - y|) ≤ Real.exp x * Real.exp (-R') := by
  have hsub : ∫ y in Ici R', Real.exp (-|x - y|)
            = ∫ y in Ici R', Real.exp x * Real.exp (-1 * y) := by
    apply setIntegral_congr_fun measurableSet_Ici
    intro y hy
    have hyR' : R' ≤ y := hy
    have hxy : x ≤ y := le_trans hxR' hyR'
    show Real.exp (-|x - y|) = Real.exp x * Real.exp (-1 * y)
    have habs : |x - y| = y - x := by rw [abs_of_nonpos (by linarith)]; ring
    rw [habs, show -(y - x) = x + (-1) * y by ring, Real.exp_add]
  rw [hsub, integral_const_mul]
  have hIci : ∫ y in Ici R', Real.exp (-1 * y) = ∫ y in Ioi R', Real.exp (-1 * y) := by
    rw [← integral_Ici_eq_integral_Ioi]
  rw [hIci, integral_exp_mul_Ioi (a := -1) (by norm_num) R']
  rw [show (-Real.exp (-1 * R') / -1) = Real.exp (-R') by rw [neg_div_neg_eq, div_one]; ring_nf]

/-- Lower-tail bound: for `x ≤ R'`... symmetric, the left tail
`∫_{y ≤ -R'} e^{-|x-y|}` for `-R' ≤ x`.  Here `y ≤ x` so `|x-y| = x-y`,
`e^{-(x-y)} = e^{-x}·e^{y}`. -/
theorem exp_neg_abs_sub_Iic_le {x R' : ℝ} (hxR' : -R' ≤ x) :
    ∫ y in Iic (-R'), Real.exp (-|x - y|) ≤ Real.exp (-x) * Real.exp (-R') := by
  have hsub : ∫ y in Iic (-R'), Real.exp (-|x - y|)
            = ∫ y in Iic (-R'), Real.exp (-x) * Real.exp (1 * y) := by
    apply setIntegral_congr_fun measurableSet_Iic
    intro y hy
    have hyR' : y ≤ -R' := hy
    have hyx : y ≤ x := le_trans hyR' hxR'
    show Real.exp (-|x - y|) = Real.exp (-x) * Real.exp (1 * y)
    have habs : |x - y| = x - y := by rw [abs_of_nonneg (by linarith)]
    rw [habs, show -(x - y) = -x + 1 * y by ring, Real.exp_add]
  rw [hsub, integral_const_mul, integral_exp_mul_Iic (a := 1) (by norm_num) (-R')]
  rw [show Real.exp (1 * -R') / 1 = Real.exp (-R') by rw [div_one]; ring_nf]

/-! ## The ε-split integral bound -/

/-- Core ε-split estimate.  For trapped `u, v` (`0 ≤ · ≤ M`), any `R'`, any
local sup-bound `s` for `|u - v|` on `[-R', R']`, and any `x ∈ [-R, R]` with
`R ≤ R'`, the kernel-envelope integral against `|(u)^γ - (v)^γ|` is bounded by
the inner (loc-unif) term plus the kernel-tail term. -/
theorem deriv_diff_integral_split_le
    (p : CMParams) {u v : ℝ → ℝ} {M R R' s : ℝ}
    (hM : 0 ≤ M)
    (hu_nn : ∀ y, 0 ≤ u y) (hu_le : ∀ y, u y ≤ M)
    (hv_nn : ∀ y, 0 ≤ v y) (hv_le : ∀ y, v y ≤ M)
    (hs : ∀ y ∈ Set.Icc (-R') R', |u y - v y| ≤ s)
    (hR : 0 < R) (hRR' : R ≤ R') {x : ℝ} (hx : x ∈ Set.Icc (-R) R)
    (hu : IsCUnifBdd u) (hv : IsCUnifBdd v) :
    (∫ y, Real.exp (-|x - y|) * |(u y) ^ p.γ - (v y) ^ p.γ|) ≤
      2 * (rpowLip p.γ M * s) + 4 * (M ^ p.γ * (Real.exp R * Real.exp (-R'))) := by
  have hγ1 : (1 : ℝ) ≤ p.γ := by linarith [p.hγ]
  set L := rpowLip p.γ M with hL
  have hL0 : 0 ≤ L := rpowLip_nonneg hγ1 hM
  have hMγ0 : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM p.γ
  -- Lipschitz envelope for the power difference on the local ball, global Mγ bound elsewhere.
  have hLip := rpow_m_lipschitz_on_Icc (m := p.γ) (M := M) hγ1 hM
  -- pointwise: |(u y)^γ - (v y)^γ| ≤ L·s·𝟙[Icc] + 2 Mγ·(𝟙[Iic -R'] + 𝟙[Ici R'])  ... actually
  -- simpler: ≤ L·s + 2 Mγ·(indicator of complement of [-R',R']).
  -- We bound by  L*s  +  2 Mγ * (𝟙_{Iic (-R')} + 𝟙_{Ici R'}).
  have hMγ_bd : ∀ y, |(u y) ^ p.γ - (v y) ^ p.γ| ≤ 2 * M ^ p.γ := by
    intro y
    have hu' : (u y) ^ p.γ ≤ M ^ p.γ :=
      Real.rpow_le_rpow (hu_nn y) (hu_le y) (by linarith)
    have hv' : (v y) ^ p.γ ≤ M ^ p.γ :=
      Real.rpow_le_rpow (hv_nn y) (hv_le y) (by linarith)
    have hu0 : 0 ≤ (u y) ^ p.γ := Real.rpow_nonneg (hu_nn y) p.γ
    have hv0 : 0 ≤ (v y) ^ p.γ := Real.rpow_nonneg (hv_nn y) p.γ
    rw [abs_le]; constructor <;> nlinarith
  have hLip_bd : ∀ y ∈ Set.Icc (-R') R', |(u y) ^ p.γ - (v y) ^ p.γ| ≤ L * s := by
    intro y hy
    have hdist := hLip (Set.mem_Icc.mpr ⟨hu_nn y, hu_le y⟩)
      (Set.mem_Icc.mpr ⟨hv_nn y, hv_le y⟩)
    rw [edist_dist, edist_dist] at hdist
    -- LipschitzOnWith: dist (f a) (f b) ≤ K * dist a b
    have hd : dist ((u y) ^ p.γ) ((v y) ^ p.γ) ≤
        (Real.toNNReal L : ℝ) * dist (u y) (v y) := by
      have := hdist
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
      exact this
    rw [Real.coe_toNNReal _ hL0] at hd
    rw [Real.dist_eq, Real.dist_eq] at hd
    calc |(u y) ^ p.γ - (v y) ^ p.γ| ≤ L * |u y - v y| := hd
      _ ≤ L * s := mul_le_mul_of_nonneg_left (hs y hy) hL0
  -- Now the pointwise global envelope:
  -- |gγ y| ≤ L*s + 2Mγ * (indicator Iic(-R') + indicator Ici R')(y)
  have henvelope : ∀ y, |(u y) ^ p.γ - (v y) ^ p.γ| ≤
      L * s + 2 * M ^ p.γ *
        (Set.indicator (Iic (-R')) (fun _ => (1:ℝ)) y +
         Set.indicator (Ici R') (fun _ => (1:ℝ)) y) := by
    intro y
    have hR'pos : 0 < R' := lt_of_lt_of_le hR hRR'
    have hs0 : 0 ≤ s := le_trans (abs_nonneg _) (hs R' (by
      rw [Set.mem_Icc]; exact ⟨by linarith, le_refl R'⟩))
    have hLs0 : 0 ≤ L * s := mul_nonneg hL0 hs0
    have hind1nn : 0 ≤ Set.indicator (Iic (-R')) (fun _ => (1:ℝ)) y :=
      Set.indicator_nonneg (fun _ _ => by norm_num) y
    have hind2nn : 0 ≤ Set.indicator (Ici R') (fun _ => (1:ℝ)) y :=
      Set.indicator_nonneg (fun _ _ => by norm_num) y
    by_cases hyin : y ∈ Set.Icc (-R') R'
    · -- inside: Lipschitz bound, indicators only add nonneg slack
      have hlip := hLip_bd y hyin
      nlinarith [hlip, hind1nn, hind2nn, hMγ0]
    · -- outside: y < -R' or y > R'; one indicator is 1
      rw [Set.mem_Icc] at hyin; push_neg at hyin
      by_cases hylo : y ≤ -R'
      · have hind1 : Set.indicator (Iic (-R')) (fun _ => (1:ℝ)) y = 1 :=
          Set.indicator_of_mem (by rw [Set.mem_Iic]; exact hylo) _
        nlinarith [hMγ_bd y, hind1, hind2nn, hMγ0, hLs0]
      · push_neg at hylo
        have hyhi : R' ≤ y := le_of_lt (hyin (by linarith))
        have hind2 : Set.indicator (Ici R') (fun _ => (1:ℝ)) y = 1 :=
          Set.indicator_of_mem (by rw [Set.mem_Ici]; exact hyhi) _
        nlinarith [hMγ_bd y, hind2, hind1nn, hMγ0, hLs0]
  -- Integrate the envelope.
  set ind1 : ℝ → ℝ := Set.indicator (Iic (-R')) (fun _ => (1:ℝ)) with hind1def
  set ind2 : ℝ → ℝ := Set.indicator (Ici R') (fun _ => (1:ℝ)) with hind2def
  -- LHS integrand
  have henv_int :
      Integrable (fun y => Real.exp (-|x - y|) * |(u y) ^ p.γ - (v y) ^ p.γ|) := by
    have hgu : IsCUnifBdd (fun y => (u y) ^ p.γ) := rpow_cunif_bdd_of_nonneg p hu hu_nn
    have hgv : IsCUnifBdd (fun y => (v y) ^ p.γ) := rpow_cunif_bdd_of_nonneg p hv hv_nn
    have habs_cunif : IsCUnifBdd (fun y => |(u y) ^ p.γ - (v y) ^ p.γ|) := by
      refine ⟨(hgu.1.sub hgv.1).abs, ?_⟩
      rcases hgu.2 with ⟨Mu, hMu⟩; rcases hgv.2 with ⟨Mv, hMv⟩
      exact ⟨Mu + Mv, fun y => by
        rw [abs_abs]; exact le_trans (abs_sub _ _) (add_le_add (hMu y) (hMv y))⟩
    rcases habs_cunif.2 with ⟨B, hB⟩
    have hdom : Integrable (fun y => Real.exp (-(1:ℝ) * |x - y|) * B) := by
      have hBconst : IsCUnifBdd (fun _ : ℝ => B) := ⟨continuous_const, ⟨|B|, fun _ => le_refl |B|⟩⟩
      simpa [Real.sqrt_one] using
        Psi_kernel_integrable_of_isCUnifBdd (u := fun _ : ℝ => B) (l := 1) one_pos hBconst x
    refine Integrable.mono' hdom
      (((by fun_prop : Continuous fun y : ℝ => Real.exp (-|x - y|)).aestronglyMeasurable).mul
        habs_cunif.1.aestronglyMeasurable) (Filter.Eventually.of_forall (fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hee : Real.exp (-|x - y|) = Real.exp (-(1:ℝ) * |x - y|) := by congr 1; ring
    rw [hee]; exact mul_le_mul_of_nonneg_left (by have := hB y; rwa [abs_abs] at this) (Real.exp_nonneg _)
  -- RHS integrand pieces
  have hexp_int := exp_neg_abs_sub_integrable x
  have hkernel_nn : ∀ y, 0 ≤ Real.exp (-|x - y|) := fun y => (Real.exp_nonneg _)
  -- ∫ exp * ind_s = ∫_{s} exp
  have hsplit_ind1 :
      ∫ y, Real.exp (-|x - y|) * ind1 y = ∫ y in Iic (-R'), Real.exp (-|x - y|) := by
    rw [hind1def]
    rw [show (fun y => Real.exp (-|x - y|) * Set.indicator (Iic (-R')) (fun _ => (1:ℝ)) y)
          = Set.indicator (Iic (-R')) (fun y => Real.exp (-|x - y|)) from ?_]
    · rw [MeasureTheory.integral_indicator measurableSet_Iic]
    · funext y; by_cases hy : y ∈ Iic (-R')
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]; ring
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]; ring
  have hsplit_ind2 :
      ∫ y, Real.exp (-|x - y|) * ind2 y = ∫ y in Ici R', Real.exp (-|x - y|) := by
    rw [hind2def]
    rw [show (fun y => Real.exp (-|x - y|) * Set.indicator (Ici R') (fun _ => (1:ℝ)) y)
          = Set.indicator (Ici R') (fun y => Real.exp (-|x - y|)) from ?_]
    · rw [MeasureTheory.integral_indicator measurableSet_Ici]
    · funext y; by_cases hy : y ∈ Ici R'
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]; ring
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]; ring
  -- envelope integrability for the RHS
  have hind1_int : Integrable (fun y => Real.exp (-|x - y|) * ind1 y) := by
    rw [hind1def]
    have : (fun y => Real.exp (-|x - y|) * Set.indicator (Iic (-R')) (fun _ => (1:ℝ)) y)
         = Set.indicator (Iic (-R')) (fun y => Real.exp (-|x - y|)) := by
      funext y; by_cases hy : y ∈ Iic (-R')
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]; ring
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]; ring
    rw [this]
    exact hexp_int.indicator measurableSet_Iic
  have hind2_int : Integrable (fun y => Real.exp (-|x - y|) * ind2 y) := by
    rw [hind2def]
    have : (fun y => Real.exp (-|x - y|) * Set.indicator (Ici R') (fun _ => (1:ℝ)) y)
         = Set.indicator (Ici R') (fun y => Real.exp (-|x - y|)) := by
      funext y; by_cases hy : y ∈ Ici R'
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]; ring
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]; ring
    rw [this]
    exact hexp_int.indicator measurableSet_Ici
  set f0 : ℝ → ℝ := fun y => (L * s) * Real.exp (-|x - y|) with hf0
  set f1 : ℝ → ℝ := fun y => (2 * M ^ p.γ) * (Real.exp (-|x - y|) * ind1 y) with hf1
  set f2 : ℝ → ℝ := fun y => (2 * M ^ p.γ) * (Real.exp (-|x - y|) * ind2 y) with hf2
  have hf0_int : Integrable f0 := hexp_int.const_mul (L*s)
  have hf1_int : Integrable f1 := hind1_int.const_mul (2*M^p.γ)
  have hf2_int : Integrable f2 := hind2_int.const_mul (2*M^p.γ)
  have heq_rhs : (fun y => Real.exp (-|x - y|) * (L * s + 2 * M ^ p.γ * (ind1 y + ind2 y)))
      = (fun y => f0 y + f1 y + f2 y) := by
    funext y; simp only [hf0, hf1, hf2]; ring
  have hrhs_int :
      Integrable (fun y => Real.exp (-|x - y|) *
        (L * s + 2 * M ^ p.γ * (ind1 y + ind2 y))) := by
    rw [heq_rhs]; exact (hf0_int.add hf1_int).add hf2_int
  -- main chain
  have hmono :
      (∫ y, Real.exp (-|x - y|) * |(u y) ^ p.γ - (v y) ^ p.γ|) ≤
        ∫ y, Real.exp (-|x - y|) * (L * s + 2 * M ^ p.γ * (ind1 y + ind2 y)) := by
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun y => mul_nonneg (hkernel_nn y) (abs_nonneg _)))
      hrhs_int
    refine Filter.Eventually.of_forall (fun y => ?_)
    exact mul_le_mul_of_nonneg_left (henvelope y) (hkernel_nn y)
  refine le_trans hmono ?_
  -- evaluate RHS
  have hRHS_eq :
      (∫ y, Real.exp (-|x - y|) * (L * s + 2 * M ^ p.γ * (ind1 y + ind2 y)))
      = (L * s) * (∫ y, Real.exp (-|x - y|))
        + 2 * M ^ p.γ * (∫ y, Real.exp (-|x - y|) * ind1 y)
        + 2 * M ^ p.γ * (∫ y, Real.exp (-|x - y|) * ind2 y) := by
    rw [heq_rhs]
    rw [integral_add (f := fun y => f0 y + f1 y) (g := f2) (hf0_int.add hf1_int) hf2_int]
    rw [integral_add (f := f0) (g := f1) hf0_int hf1_int]
    simp only [hf0, hf1, hf2, integral_const_mul]
  rw [hRHS_eq, exp_neg_abs_sub_integral_eq, hsplit_ind1, hsplit_ind2]
  -- tail bounds
  have hxleR' : x ≤ R' := le_trans hx.2 hRR'
  have hnegR'le : -R' ≤ x := le_trans (by linarith [hRR'] : -R' ≤ -R) hx.1
  have htail1 := exp_neg_abs_sub_Iic_le hnegR'le
  have htail2 := exp_neg_abs_sub_Ici_le hxleR'
  have hMγ0' : 0 ≤ 2 * M ^ p.γ := by positivity
  have hexR : Real.exp (-x) ≤ Real.exp R := Real.exp_le_exp.mpr (by linarith [hx.1])
  have hexR2 : Real.exp x ≤ Real.exp R := Real.exp_le_exp.mpr (by linarith [hx.2])
  have heR0 : 0 ≤ Real.exp (-R') := Real.exp_nonneg _
  -- ∫_{Iic(-R')} exp ≤ e^{-x} e^{-R'} ≤ e^R e^{-R'}
  have ht1 : (∫ y in Iic (-R'), Real.exp (-|x - y|)) ≤ Real.exp R * Real.exp (-R') :=
    le_trans htail1 (mul_le_mul_of_nonneg_right hexR heR0)
  have ht2 : (∫ y in Ici R', Real.exp (-|x - y|)) ≤ Real.exp R * Real.exp (-R') :=
    le_trans htail2 (mul_le_mul_of_nonneg_right hexR2 heR0)
  nlinarith [mul_le_mul_of_nonneg_left ht1 hMγ0', mul_le_mul_of_nonneg_left ht2 hMγ0']

/-! ## The final loc-unif assembly -/

/-- **Continuous dependence of the frozen elliptic drift on the profile.**
For profiles in `InMonotoneWaveTrapSet κ M` (which supplies `0 ≤ u`, `u ≤ M`,
and `IsCUnifBdd u`), local-uniform convergence `seq n → u` forces local-uniform
convergence of the frozen drifts `deriv (frozenElliptic p (seq n)) →
deriv (frozenElliptic p u)`.

The ε-split: on `[-R,R]`, given `ε > 0`, choose `R'` so the kernel tail
`2 M^γ e^R e^{-R'} < ε/2`, then use loc-unif convergence on `[-R',R']` to make the
inner Lipschitz term `< ε/2`.  `deriv_diff_integral_split_le` supplies the
combined estimate. -/
theorem frozenEllipticDerivDependence (p : CMParams) {κ M : ℝ} (hM : 0 ≤ M) :
    FrozenEllipticDerivDependence p (InMonotoneWaveTrapSet κ M) := by
  intro seq u hseq hu hconv
  -- Extract trap data for u.
  have hu_cunif : IsCUnifBdd u := hu.1.1
  have hu_nn : ∀ x, 0 ≤ u x := fun x => (hu.1.2 x).1
  have hu_le : ∀ x, u x ≤ M := fun x =>
    le_trans (hu.1.2 x).2 (upperBarrier_le_M κ M x)
  -- Extract trap data for each seq n.
  have hsn_cunif : ∀ n, IsCUnifBdd (seq n) := fun n => (hseq n).1.1
  have hsn_nn : ∀ n x, 0 ≤ seq n x := fun n x => ((hseq n).1.2 x).1
  have hsn_le : ∀ n x, seq n x ≤ M := fun n x =>
    le_trans ((hseq n).1.2 x).2 (upperBarrier_le_M κ M x)
  -- The Lipschitz constant of `s ↦ s^γ` on `[0,M]`.
  have hγ1 : (1 : ℝ) ≤ p.γ := p.hγ
  set L := rpowLip p.γ M with hL
  have hL0 : 0 ≤ L := rpowLip_nonneg hγ1 hM
  have hMγ0 : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM p.γ
  -- Unfold the loc-unif conclusion.
  intro R hR ε hε
  -- (1) Choose R' ≥ R so the tail `2 M^γ e^R · e^{-R'} < ε/2`.
  set K : ℝ := 2 * M ^ p.γ * Real.exp R with hK
  have hK0 : 0 ≤ K := by positivity
  have hexp0 : Filter.Tendsto (fun R' : ℝ => Real.exp (-R')) Filter.atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp Filter.tendsto_neg_atTop_atBot
  have htail_small : ∀ᶠ R' : ℝ in Filter.atTop, K * Real.exp (-R') < ε / 2 := by
    have hKtail : Filter.Tendsto (fun R' : ℝ => K * Real.exp (-R')) Filter.atTop (𝓝 0) := by
      have := hexp0.const_mul K
      simpa using this
    exact hKtail.eventually (eventually_lt_nhds (by linarith))
  obtain ⟨R', htailR', hR'ge⟩ :=
    (htail_small.and (Filter.eventually_ge_atTop R)).exists
  -- (2) loc-unif convergence on `[-R',R']` with the inner tolerance `ε/(2(L+1))`.
  have hRR' : R ≤ R' := hR'ge
  have hR'0 : 0 < R' := lt_of_lt_of_le hR hRR'
  have hLp1 : (0 : ℝ) < L + 1 := by linarith
  set s0 : ℝ := ε / (2 * (L + 1)) with hs0def
  have hs0pos : 0 < s0 := by
    rw [hs0def]; positivity
  have hinner := hconv R' hR'0 s0 hs0pos
  -- (3) Combine: eventually in n, the split bound gives `< ε` on `[-R,R]`.
  filter_upwards [hinner] with n hn
  intro x hx
  -- The local sup bound `s = s0` for `|seq n - u|` on `[-R',R']`.
  have hs_bd : ∀ y ∈ Set.Icc (-R') R', |seq n y - u y| ≤ s0 := by
    intro y hy
    exact le_of_lt (hn y hy)
  -- Pointwise difference bound via `frozenElliptic_deriv_diff_abs_le`.
  have habs := frozenElliptic_deriv_diff_abs_le p
    (hsn_cunif n) (hsn_nn n) hu_cunif hu_nn x
  -- Split-integral estimate.
  have hsplit := deriv_diff_integral_split_le p (M := M) (R := R) (R' := R') (s := s0)
    hM (hsn_nn n) (hsn_le n) hu_nn hu_le hs_bd hR hRR' hx (hsn_cunif n) hu_cunif
  -- Chain: `|deriv diff| ≤ 1/2 · ∫ ≤ 1/2 · (2 L s0 + 4 M^γ e^R e^{-R'})
  --        = L s0 + 2 M^γ e^R e^{-R'} = L s0 + K e^{-R'}`.
  have hchain : |deriv (frozenElliptic p (seq n)) x - deriv (frozenElliptic p u) x|
      ≤ L * s0 + K * Real.exp (-R') := by
    refine le_trans habs ?_
    have h2 : (1 : ℝ) / 2 * (∫ y, Real.exp (-|x - y|) *
        |(seq n y) ^ p.γ - (u y) ^ p.γ|)
        ≤ 1 / 2 * (2 * (L * s0) + 4 * (M ^ p.γ * (Real.exp R * Real.exp (-R')))) :=
      mul_le_mul_of_nonneg_left hsplit (by norm_num)
    refine le_trans h2 (le_of_eq ?_)
    rw [hK]; ring
  -- Inner term `≤ ε/2`: `L s0 ≤ (L+1) s0 = ε/2`.
  have hinner_le : L * s0 ≤ ε / 2 := by
    have hstep : L * s0 ≤ (L + 1) * s0 :=
      mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hs0pos)
    have heq : (L + 1) * s0 = ε / 2 := by rw [hs0def]; field_simp
    linarith [hstep, heq.le, heq.ge]
  -- Tail strict.
  have htail_lt : K * Real.exp (-R') < ε / 2 := htailR'
  calc |deriv (frozenElliptic p (seq n)) x - deriv (frozenElliptic p u) x|
      ≤ L * s0 + K * Real.exp (-R') := hchain
    _ < ε / 2 + ε / 2 := by linarith [hinner_le, htail_lt]
    _ = ε := by ring

end ShenWork.Paper1
