/-
  ShenWork/Paper1/WaveEllipticMono.lean

  Traveling-wave endgame: the frozen elliptic field `V = frozenElliptic p U`
  has nonpositive derivative on a monotone wave trap.

  ROUTE (clean convolution-monotonicity, no integration by parts and no
  differentiation of `U`).  By definition

      `frozenElliptic p U x = Psi (U^γ) 1 1 x
                            = ½ ∫_ℝ e^{-|x-y|} (U y)^γ dy`.

  Translating `y ↦ x + t` (Lebesgue measure is translation invariant,
  `integral_add_left_eq_self`) gives

      `frozenElliptic p U x = ½ ∫_ℝ e^{-|t|} (U (x+t))^γ dt`.

  The kernel `e^{-|t|} ≥ 0` is fixed, and for `x₁ ≤ x₂` and every `t`,
  `x₁ + t ≤ x₂ + t`, so antitonicity of `U` (hence of `U^γ` on the nonneg
  range, `γ ≥ 1 > 0`) gives `(U (x₂+t))^γ ≤ (U (x₁+t))^γ` pointwise.
  Monotonicity of the integral (`MeasureTheory.integral_mono`) yields
  `frozenElliptic p U x₂ ≤ frozenElliptic p U x₁`, i.e. `frozenElliptic p U`
  is `Antitone`.  Finally `Antitone.deriv_nonpos` gives `V' x ≤ 0`.

  This uses only the committed kernel representation of `Psi`
  (`Psi`'s definition in `ShenWork.Defs`) and the trap projections
  `InMonotoneWaveTrapSet.nonneg` / `.antitone` from `Statements.lean`.
-/
import ShenWork.Paper1.Statements

open Filter Topology MeasureTheory Real

namespace ShenWork.Paper1

/-- The frozen elliptic field written as the (½-normalized) exponential
convolution of `U^γ` against the Green kernel `e^{-|x-y|}`. -/
theorem frozenElliptic_eq_kernel_integral
    (p : CMParams) (U : ℝ → ℝ) (x : ℝ) :
    frozenElliptic p U x =
      1 / 2 * ∫ y : ℝ, Real.exp (-1 * |x - y|) * (U y) ^ p.γ := by
  unfold frozenElliptic Psi
  rw [Real.sqrt_one]
  norm_num

/-- After the translation `y ↦ x + t`, the convolution becomes an integral of
the fixed kernel `e^{-|t|}` against the translated profile `(U (x+t))^γ`. -/
theorem frozenElliptic_eq_translated_integral
    (p : CMParams) {U : ℝ → ℝ}
    (hU_bdd : IsCUnifBdd U) (hU_nonneg : ∀ y, 0 ≤ U y) (x : ℝ) :
    frozenElliptic p U x =
      1 / 2 * ∫ t : ℝ, Real.exp (-1 * |t|) * (U (x + t)) ^ p.γ := by
  rw [frozenElliptic_eq_kernel_integral]
  congr 1
  -- translation invariance of the Lebesgue integral: ∫ F(x+t) dt = ∫ F y dy
  have htrans :
      (∫ t : ℝ, Real.exp (-1 * |x - (x + t)|) * (U (x + t)) ^ p.γ) =
        ∫ y : ℝ, Real.exp (-1 * |x - y|) * (U y) ^ p.γ :=
    integral_add_left_eq_self
      (fun y : ℝ => Real.exp (-1 * |x - y|) * (U y) ^ p.γ) x
  rw [← htrans]
  apply MeasureTheory.integral_congr_ae
  refine Filter.Eventually.of_forall (fun t => ?_)
  dsimp only
  have hsimp : |x - (x + t)| = |t| := by
    rw [show x - (x + t) = -t by ring, abs_neg]
  rw [hsimp]

/-- The integrand `t ↦ e^{-|t|} (U (x+t))^γ` is integrable. -/
theorem frozenElliptic_translated_integrand_integrable
    (p : CMParams) {U : ℝ → ℝ}
    (hU_bdd : IsCUnifBdd U) (hU_nonneg : ∀ y, 0 ≤ U y) (x : ℝ) :
    Integrable (fun t : ℝ => Real.exp (-1 * |t|) * (U (x + t)) ^ p.γ) := by
  -- It is the translate of the integrable kernel `e^{-|x-y|} (U y)^γ`.
  have hfg_bdd : IsCUnifBdd (fun y => (U y) ^ p.γ) :=
    rpow_cunif_bdd_of_nonneg p hU_bdd hU_nonneg
  have hbase :
      Integrable
        (fun y : ℝ => Real.exp (-Real.sqrt 1 * |x - y|) * (U y) ^ p.γ) :=
    Psi_kernel_integrable_of_isCUnifBdd (by norm_num) hfg_bdd x
  have hbase' :
      Integrable (fun y : ℝ => Real.exp (-1 * |x - y|) * (U y) ^ p.γ) := by
    simpa [Real.sqrt_one] using hbase
  have hshift :
      Integrable
        (fun t : ℝ => Real.exp (-1 * |x - (x + t)|) * (U (x + t)) ^ p.γ) :=
    (measurePreserving_add_left (μ := (volume : Measure ℝ)) x).integrable_comp_emb
      (MeasurableEquiv.addLeft x).measurableEmbedding |>.mpr hbase'
  refine hshift.congr (Filter.Eventually.of_forall (fun t => ?_))
  dsimp only
  have hsimp : |x - (x + t)| = |t| := by
    rw [show x - (x + t) = -t by ring, abs_neg]
  rw [hsimp]

/-- `(U ·)^γ` is antitone whenever `U` is antitone and nonnegative (`γ ≥ 0`). -/
theorem rpow_gamma_antitone
    (p : CMParams) {U : ℝ → ℝ}
    (hU_anti : Antitone U) (hU_nonneg : ∀ y, 0 ≤ U y) :
    Antitone (fun y => (U y) ^ p.γ) := by
  intro a b hab
  exact Real.rpow_le_rpow (hU_nonneg b) (hU_anti hab) (by linarith [p.hγ])

/-- The frozen elliptic field is antitone on a monotone wave trap. -/
theorem frozenElliptic_antitone_of_monotone_trap
    (p : CMParams) {κ M : ℝ} {U : ℝ → ℝ}
    (hU : InMonotoneWaveTrapSet κ M U) :
    Antitone (frozenElliptic p U) := by
  have hU_bdd : IsCUnifBdd U := hU.trap.cunif_bdd
  have hU_nonneg : ∀ y, 0 ≤ U y := fun y => hU.nonneg y
  have hU_anti : Antitone U := hU.antitone
  have hfanti : Antitone (fun y => (U y) ^ p.γ) :=
    rpow_gamma_antitone p hU_anti hU_nonneg
  intro x₁ x₂ hx
  rw [frozenElliptic_eq_translated_integral p hU_bdd hU_nonneg,
      frozenElliptic_eq_translated_integral p hU_bdd hU_nonneg]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply MeasureTheory.integral_mono
  · exact frozenElliptic_translated_integrand_integrable p hU_bdd hU_nonneg x₂
  · exact frozenElliptic_translated_integrand_integrable p hU_bdd hU_nonneg x₁
  intro t
  -- pointwise: kernel ≥ 0, and (U (x₂+t))^γ ≤ (U (x₁+t))^γ
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  exact hfanti (by linarith : x₁ + t ≤ x₂ + t)

/-- **Main theorem.**  On a monotone wave trap the frozen elliptic field's
derivative is nonpositive everywhere. -/
theorem frozenElliptic_deriv_nonpos_of_monotone_trap
    (p : CMParams) (κ M : ℝ) (U : ℝ → ℝ)
    (hU : InMonotoneWaveTrapSet κ M U) (x : ℝ) :
    deriv (frozenElliptic p U) x ≤ 0 :=
  (frozenElliptic_antitone_of_monotone_trap p hU).deriv_nonpos

end ShenWork.Paper1
