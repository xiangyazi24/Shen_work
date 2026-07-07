/-
  Windowed (`On`) analogues of the three discharge theorems from
  `IntervalBFormSpectralProviderDischarge.lean`.

  These take `DuhamelSourceTimeC1On aB 0 D.T` in place of the global
  `DuhamelSourceTimeC1 aB`.  Since `HasBFormSpectralPdeAgreement` packs a
  `DuhamelSourceTimeC1 a` witness inside its existential (which cannot be
  constructed from windowed data alone), the windowed theorems produce the
  PDE identity directly — bypassing the `HasBFormSpectralPdeAgreement`
  intermediate and using per-coefficient `HasDerivAt` lifted through
  `hasDerivAt_tsum_of_isPreconnected`.

  Key adaptations from the global-source proofs:

  * **Shift.**  `DuhamelSourceTimeC1.shift_nonneg` → windowed restriction
    of `DuhamelSourceTimeC1On` to a sub-interval + `shift_zero`.

  * **Eigenvalue summability.**  `localRestartCoeff_eigenvalue_summable` →
    triangle split via
    `restartHomogeneousCoeff_eigenvalue_summable + duhamelSpectralCoeff_eigenvalue_summable_on`.

  * **ContinuousOn.**  `(hsrcB.hderiv s k).continuousAt).continuousOn` →
    `HasDerivWithinAt.continuousWithinAt` from `DuhamelSourceTimeC1On.hderiv`.

  * **Time derivative.**  `restartCosineSeries_hasDerivAt_time` →
    per-coefficient `HasDerivAt` via `duhamelSpectralCoeff_hasDerivAt_of_on`
    on the shifted window, lifted to the tsum via
    `hasDerivAt_tsum_of_isPreconnected`.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.  New file only.
-/
import ShenWork.Paper2.IntervalBFormSpectralProvider
import ShenWork.Paper2.IntervalConjugatePicardInfThreshold
import ShenWork.Paper2.IntervalBFormRestart
import ShenWork.Paper2.IntervalBankChemSliceFix
import ShenWork.PDE.IntervalDuhamelSourceTimeC1On
import ShenWork.PDE.IntervalDuhamelSpectralDerivOn
import ShenWork.PDE.IntervalDuhamelSpectralEqCosineSeriesOn

open Filter Topology Set

noncomputable section

namespace ShenWork.IntervalConjugatePicard

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant)
open ShenWork.IntervalDuhamelClosedC2
  (DuhamelSourceTimeC1 duhamelSpectralCoeff
   cosineCoeff_summable_of_eigenvalue_summable)
open ShenWork.IntervalDuhamelSourceTimeC1On
  (DuhamelSourceTimeC1On duhamelSpectralCoeff_eigenvalue_summable_on)
open ShenWork.IntervalDuhamelSpectralDerivOn
  (duhamelSpectralCoeff_hasDerivAt_of_on)
open ShenWork.IntervalSourceCoefficientTimeC1
  (localRestartCoeff homogeneousCosineSeries_hasDerivAt_time)
open ShenWork.IntervalBFormSpectral
  (LogisticCosineFourierData ChemDivCosineFourierData)
open ShenWork.Paper2.BankChemSliceFix
  (ChemDivCosineFourierDataIoo
   coupledChemDiv_cosineSeries_summable_Ioo
   coupledChemDiv_cosineFourier_convergence_Ioo)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceCoeffs
   coupledLogisticSourceCoeffs)
open ShenWork.Paper2 (PaperPositiveInitialDatum)
open ShenWork.IntervalMildRegularityBootstrap
  (restartHomogeneousCoeff_eigenvalue_summable)
open ShenWork.IntervalDomainRegularityBootstrap
  (reciprocalSquareTerm reciprocalSquareTerm_summable)

/-! ## Windowed infrastructure helpers -/

/-- Per-mode eigenvalue-weighted summability from `DuhamelSourceTimeC1On`
(triangle split: homogeneous + Duhamel legs). -/
private theorem localRestartCoeff_eigenvalue_summable_of_on
    {τ M : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {W : ℝ}
    (hτ : 0 < τ) (hτW : τ ≤ W)
    (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC1On a 0 W) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n * |localRestartCoeff a₀ a τ n|) := by
  have hhom := restartHomogeneousCoeff_eigenvalue_summable hτ ha₀
  have hduh := duhamelSpectralCoeff_eigenvalue_summable_on src hτ hτW
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity)
      (abs_nonneg _)) (fun n => ?_) (hhom.add hduh)
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left
    (by simp only [localRestartCoeff]; exact abs_add_le _ _)
    (by unfold unitIntervalCosineEigenvalue; positivity)

/-- Per-mode `HasDerivAt` of `localRestartCoeff` at interior points of `(0, W)`
from `DuhamelSourceTimeC1On a 0 W`. -/
private theorem localRestartCoeff_hasDerivAt_of_on
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {W : ℝ}
    (src : DuhamelSourceTimeC1On a 0 W)
    {τ : ℝ} (hτ : 0 < τ) (hτW : τ < W) (n : ℕ) :
    HasDerivAt (fun r => localRestartCoeff a₀ a r n)
      (a τ n - unitIntervalCosineEigenvalue n * localRestartCoeff a₀ a τ n) τ := by
  set lam := unitIntervalCosineEigenvalue n
  have hhom : HasDerivAt
      (fun r : ℝ => Real.exp (-r * lam) * a₀ n)
      (-(lam * Real.exp (-τ * lam)) * a₀ n) τ := by
    have harg : HasDerivAt (fun r : ℝ => -r * lam) (-lam) τ := by
      simpa using (hasDerivAt_id τ).neg.mul_const lam
    exact (harg.exp.mul_const _).congr_deriv (by ring)
  have hduh : HasDerivAt
      (fun r => duhamelSpectralCoeff a r n)
      (a τ n - lam * duhamelSpectralCoeff a τ n) τ :=
    duhamelSpectralCoeff_hasDerivAt_of_on src hτ hτW n
  rw [show (fun r : ℝ => localRestartCoeff a₀ a r n) =
      fun r : ℝ =>
        Real.exp (-r * lam) * a₀ n +
          duhamelSpectralCoeff a r n
      from by ext r; simp [localRestartCoeff, lam]]
  convert hhom.add hduh using 1
  simp [localRestartCoeff, lam]; ring

set_option maxHeartbeats 0 in
/-- **Windowed restart cosine series `HasDerivAt`.**
For `0 < τ₀ < W`, the restart series `∑ localRestartCoeff a₀ a τ cos(nπx)` is
differentiable in `τ` at `τ₀`, with derivative
`∑ (a(τ₀,n) − λₙ localRestartCoeff(τ₀,n)) cos(nπx)`.
Splits localRestartCoeff = hom + Duhamel, then:
* hom leg: `homogeneousCosineSeries_hasDerivAt_time` (no source needed)
* Duhamel leg: `hasDerivAt_tsum_of_isPreconnected` with
  `duhamelSpectralCoeff_hasDerivAt_of_on` and the `env + derivBound/n²` majorant. -/
private theorem restartCosineSeries_hasDerivAt_time_of_on
    {a₀ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (ha₀ : ∀ n, |a₀ n| ≤ M)
    {a : ℝ → ℕ → ℝ} {W : ℝ}
    (src : DuhamelSourceTimeC1On a 0 W)
    {τ₀ : ℝ} (hτ₀ : 0 < τ₀) (hτ₀W : τ₀ < W) (x : ℝ) :
    HasDerivAt
      (fun τ => ∑' n, localRestartCoeff a₀ a τ n * cosineMode n x)
      (∑' n, (a τ₀ n - unitIntervalCosineEigenvalue n *
        localRestartCoeff a₀ a τ₀ n) * cosineMode n x) τ₀ := by
  have hcos_le : ∀ n, |cosineMode n x| ≤ 1 := fun n => by
    simp only [cosineMode]; exact Real.abs_cos_le_one _
  have ht₀2 : 0 < τ₀ / 2 := by linarith
  -- Summability helpers
  have hsum_hom_at : ∀ τ : ℝ, 0 < τ → Summable (fun n =>
      Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n * cosineMode n x) := by
    intro τ hτ
    refine Summable.of_norm_bounded
      (g := fun n => Real.exp (-τ * unitIntervalCosineEigenvalue n) * M)
      ((ShenWork.HeatKernelGradientEstimates.unitIntervalCosineHeatTrace_single_exp_summable
        hτ).mul_right M) (fun n => ?_)
    rw [Real.norm_eq_abs]
    have hassoc : Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n *
        cosineMode n x = Real.exp (-τ * unitIntervalCosineEigenvalue n) *
          (a₀ n * cosineMode n x) := by ring
    rw [hassoc, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    rw [abs_mul]
    calc |a₀ n| * |cosineMode n x|
        ≤ M * 1 := mul_le_mul (ha₀ n) (hcos_le n) (abs_nonneg _) hM
      _ = M := mul_one _
  have hsum_duh_at : ∀ τ : ℝ, 0 < τ → τ ≤ W → Summable (fun n =>
      duhamelSpectralCoeff a τ n * cosineMode n x) := by
    intro τ hτ hτW
    have ⟨_, habs⟩ := cosineCoeff_summable_of_eigenvalue_summable
      (duhamelSpectralCoeff_eigenvalue_summable_on src hτ hτW)
    exact Summable.of_norm (habs.of_nonneg_of_le (fun _ => abs_nonneg _) (fun n => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hcos_le n)))
  -- Split: localRestartCoeff = hom + Duhamel
  have hfun_eq : ∀ τ ∈ Ioo (0 : ℝ) W,
      ∑' n, localRestartCoeff a₀ a τ n * cosineMode n x =
      (∑' n, Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n * cosineMode n x) +
        (∑' n, duhamelSpectralCoeff a τ n * cosineMode n x) := by
    intro τ hτ
    rw [show (fun n => localRestartCoeff a₀ a τ n * cosineMode n x) =
        fun n => Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n * cosineMode n x +
          duhamelSpectralCoeff a τ n * cosineMode n x from funext (fun n => by
            simp only [localRestartCoeff]; ring)]
    exact (hsum_hom_at τ hτ.1).tsum_add (hsum_duh_at τ hτ.1 hτ.2.le)
  -- HasDerivAt of each piece
  have hd1 := homogeneousCosineSeries_hasDerivAt_time hM ha₀ hτ₀ x
  -- Duhamel leg: `hasDerivAt_tsum_of_isPreconnected` on `(c, W)` with
  -- the `env + derivBound · reciprocalSquareTerm` majorant (same as
  -- `SourceJointRegularityOn.duhamel_deriv_bound_on`).
  set c := τ₀ / 2 with hc_def
  have hc : 0 < c := by rw [hc_def]; linarith
  have hcW : c < W := by rw [hc_def]; linarith
  have hc_lt_τ₀ : c < τ₀ := by rw [hc_def]; linarith
  have hd2 : HasDerivAt
      (fun τ => ∑' n, duhamelSpectralCoeff a τ n * cosineMode n x)
      (∑' n, (a τ₀ n - unitIntervalCosineEigenvalue n *
        duhamelSpectralCoeff a τ₀ n) * cosineMode n x) τ₀ := by
    refine hasDerivAt_tsum_of_isPreconnected
      (src.henv_summable.add (reciprocalSquareTerm_summable.mul_left src.derivBound))
      isOpen_Ioo isPreconnected_Ioo
      (fun n τ hτ => (duhamelSpectralCoeff_hasDerivAt_of_on src
        (lt_trans hc hτ.1) hτ.2 n).mul_const _)
      (fun n τ hτ => ?_)
      ⟨hc_lt_τ₀, hτ₀W⟩
      (hsum_duh_at τ₀ hτ₀ hτ₀W.le)
      ⟨hc_lt_τ₀, hτ₀W⟩
    -- Bound: ‖(a(τ,n) - λ bₙ(τ)) · cos‖ ≤ env + derivBound · reciprocalSquareTerm
    -- Replicate the bound from `SourceJointRegularityOn.duhamel_deriv_bound_on`.
    rw [Real.norm_eq_abs, abs_mul]
    have hτ_pos : 0 < τ := lt_trans hc hτ.1
    have hτ_le : τ ≤ W := hτ.2.le
    have hdb_nn : 0 ≤ src.derivBound :=
      le_trans (abs_nonneg _) (src.hderivBound 0 ⟨le_rfl, by linarith⟩ 0)
    have hlam_nn : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue; positivity
    have hu_nn : 0 ≤ src.envelope n + src.derivBound * reciprocalSquareTerm n :=
      add_nonneg (le_trans (abs_nonneg _) (src.henv_bound 0 ⟨le_rfl, by linarith⟩ n))
        (mul_nonneg hdb_nn (by unfold reciprocalSquareTerm; positivity))
    -- The core bound (from duhamel_deriv_bound_on): for Duhamel coefficients,
    -- |a(τ,n) - λ bₙ(τ)| ≤ env(n) + derivBound · reciprocalSquareTerm(n)
    -- This uses the IBP formula.
    have hcore : |a τ n - unitIntervalCosineEigenvalue n *
        duhamelSpectralCoeff a τ n| ≤
        src.envelope n + src.derivBound * reciprocalSquareTerm n := by
      rcases Nat.eq_zero_or_pos n with hn0 | hn
      · subst hn0
        simp [unitIntervalCosineEigenvalue, reciprocalSquareTerm, sub_zero]
        exact src.henv_bound τ ⟨hτ_pos.le, hτ_le⟩ 0
      · have hlam_pos : 0 < unitIntervalCosineEigenvalue n := by
          unfold unitIntervalCosineEigenvalue
          have : (0 : ℝ) < n := Nat.cast_pos.2 hn
          positivity
        have hIBP := ShenWork.IntervalDuhamelSourceTimeC1On.duhamelCoeff_eigenvalue_mul_on
          (lo := 0) (hi := W) (t := τ) (lam := unitIntervalCosineEigenvalue n)
          (a := fun s => a s n) (adot := fun s => src.adot s n)
          (by linarith) hτ_pos.le hτ_le
          (fun s hs => src.hderiv s ⟨hs.1, le_trans hs.2 hτ_le⟩ n) (src.hadotcont n)
        simp only [sub_zero] at hIBP
        have hres : a τ n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a τ n
            = Real.exp (-τ * unitIntervalCosineEigenvalue n) * a 0 n
              + ∫ s in (0:ℝ)..τ,
                Real.exp (-(τ - s) * unitIntervalCosineEigenvalue n) * src.adot s n := by
          simp only [duhamelSpectralCoeff] at *; linarith
        rw [hres]
        have h_exp_piece : |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a 0 n| ≤
            src.envelope n := by
          rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
          calc Real.exp (-τ * unitIntervalCosineEigenvalue n) * |a 0 n|
              ≤ 1 * |a 0 n| := by gcongr; exact Real.exp_le_one_iff.2 (by nlinarith)
            _ = |a 0 n| := one_mul _
            _ ≤ src.envelope n := src.henv_bound 0 ⟨le_refl _, by linarith⟩ n
        have h_int_piece : |∫ s in (0:ℝ)..τ,
              Real.exp (-(τ - s) * unitIntervalCosineEigenvalue n) * src.adot s n| ≤
            src.derivBound * reciprocalSquareTerm n := by
          rw [← Real.norm_eq_abs]
          calc ‖∫ s in (0:ℝ)..τ,
                  Real.exp (-(τ - s) * unitIntervalCosineEigenvalue n) * src.adot s n‖
              ≤ ∫ s in (0:ℝ)..τ,
                  ‖Real.exp (-(τ - s) * unitIntervalCosineEigenvalue n) * src.adot s n‖ :=
                intervalIntegral.norm_integral_le_integral_norm hτ_pos.le
            _ ≤ ∫ s in (0:ℝ)..τ,
                  src.derivBound * Real.exp (-(τ - s) * unitIntervalCosineEigenvalue n) := by
                apply intervalIntegral.integral_mono_on hτ_pos.le
                · have : ContinuousOn (fun s =>
                      Real.exp (-(τ - s) * unitIntervalCosineEigenvalue n) * src.adot s n)
                      (Set.Icc 0 τ) :=
                    (Real.continuous_exp.comp (by fun_prop : Continuous (fun s =>
                      -(τ - s) * unitIntervalCosineEigenvalue n))).continuousOn.mul
                    ((src.hadotcont n).mono (Icc_subset_Icc le_rfl hτ_le))
                  exact this.norm.intervalIntegrable_of_Icc hτ_pos.le
                · have : Continuous (fun s =>
                      src.derivBound * Real.exp (-(τ - s) * unitIntervalCosineEigenvalue n)) :=
                    by fun_prop
                  exact this.continuousOn.intervalIntegrable_of_Icc hτ_pos.le
                · intro s hs
                  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _), mul_comm]
                  exact mul_le_mul_of_nonneg_right
                    (src.hderivBound s ⟨hs.1, le_trans hs.2 hτ_le⟩ n) (Real.exp_nonneg _)
            _ = src.derivBound * ∫ s in (0:ℝ)..τ,
                  Real.exp (-(τ - s) * unitIntervalCosineEigenvalue n) := by
                rw [intervalIntegral.integral_const_mul]
            _ ≤ src.derivBound * (1 / unitIntervalCosineEigenvalue n) := by
                gcongr
                rw [le_div_iff₀ hlam_pos]
                linarith [ShenWork.IntervalDuhamelRegularity.parabolicGain_le_one hlam_nn hτ_pos.le]
            _ ≤ src.derivBound * reciprocalSquareTerm n := by
                gcongr
                rw [reciprocalSquareTerm, unitIntervalCosineEigenvalue]
                apply div_le_div_of_nonneg_left (by linarith) (by positivity)
                calc ((n : ℝ) * Real.pi) ^ 2 = (n : ℝ) ^ 2 * Real.pi ^ 2 := by ring
                  _ ≥ (n : ℝ) ^ 2 * 1 := by
                      apply mul_le_mul_of_nonneg_left _ (by positivity)
                      nlinarith [Real.pi_gt_three]
                  _ = (n : ℝ) ^ 2 := mul_one _
        linarith [abs_add_le
          (Real.exp (-τ * unitIntervalCosineEigenvalue n) * a 0 n)
          (∫ s in (0:ℝ)..τ,
            Real.exp (-(τ - s) * unitIntervalCosineEigenvalue n) * src.adot s n)]
    calc |a τ n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a τ n| *
              |cosineMode n x|
          ≤ (src.envelope n + src.derivBound * reciprocalSquareTerm n) * 1 :=
            mul_le_mul hcore (hcos_le n) (abs_nonneg _) hu_nn
        _ = src.envelope n + src.derivBound * reciprocalSquareTerm n := mul_one _
  -- Combine via eventuallyEq on (0, W)
  have hcombine := hd1.add hd2
  have hfun_ev : (fun τ => ∑' n, localRestartCoeff a₀ a τ n * cosineMode n x) =ᶠ[𝓝 τ₀]
      (fun τ => ∑' n, Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n * cosineMode n x +
        ∑' n, duhamelSpectralCoeff a τ n * cosineMode n x) := by
    apply Filter.eventuallyEq_of_mem (s := Ioo 0 W)
    · exact isOpen_Ioo.mem_nhds ⟨hτ₀, hτ₀W⟩
    · intro τ hτ; exact hfun_eq τ hτ
  have hstep1 := hcombine.congr_of_eventuallyEq hfun_ev
  -- Simplify derivative value using tsum_add
  have hsum1 : Summable (fun n =>
      -(unitIntervalCosineEigenvalue n * Real.exp (-τ₀ * unitIntervalCosineEigenvalue n)) *
        a₀ n * cosineMode n x) := by
    apply Summable.of_norm
    refine ((ShenWork.IntervalMildRegularityBootstrap.unitIntervalCosineEigenvalue_mul_exp_summable hτ₀).mul_right M).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun n => ?_)
    have hlam_nn : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue; positivity
    rw [Real.norm_eq_abs, show -(unitIntervalCosineEigenvalue n *
        Real.exp (-τ₀ * unitIntervalCosineEigenvalue n)) * a₀ n * cosineMode n x =
        -(unitIntervalCosineEigenvalue n *
          Real.exp (-τ₀ * unitIntervalCosineEigenvalue n) * a₀ n * cosineMode n x) from by ring,
      abs_neg, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg hlam_nn, abs_of_nonneg (Real.exp_nonneg _)]
    calc unitIntervalCosineEigenvalue n *
          Real.exp (-τ₀ * unitIntervalCosineEigenvalue n) *
            |a₀ n| * |cosineMode n x|
        ≤ unitIntervalCosineEigenvalue n *
            Real.exp (-τ₀ * unitIntervalCosineEigenvalue n) * M * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (ha₀ n) (by positivity))
            (hcos_le n) (abs_nonneg _) (by positivity)
      _ = unitIntervalCosineEigenvalue n *
            Real.exp (-τ₀ * unitIntervalCosineEigenvalue n) * M := mul_one _
  have hsum2 : Summable (fun n =>
      (a τ₀ n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a τ₀ n) *
        cosineMode n x) := by
    have hsumE := duhamelSpectralCoeff_eigenvalue_summable_on src hτ₀ hτ₀W.le
    refine Summable.of_norm_bounded
      (g := fun n => src.envelope n + unitIntervalCosineEigenvalue n *
        |duhamelSpectralCoeff a τ₀ n|) (src.henv_summable.add hsumE) (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have hlam_nn : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue; positivity
    have hlhs : |a τ₀ n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a τ₀ n| ≤
        |a τ₀ n| + unitIntervalCosineEigenvalue n * |duhamelSpectralCoeff a τ₀ n| := by
      calc |a τ₀ n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a τ₀ n|
          = |a τ₀ n + (-(unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a τ₀ n))| := by
            rw [sub_eq_add_neg]
        _ ≤ |a τ₀ n| + |-(unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a τ₀ n)| :=
            abs_add_le _ _
        _ = |a τ₀ n| + |unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a τ₀ n| := by
            rw [abs_neg]
        _ = |a τ₀ n| + unitIntervalCosineEigenvalue n * |duhamelSpectralCoeff a τ₀ n| := by
            rw [abs_mul, abs_of_nonneg hlam_nn]
    have henv : |a τ₀ n| ≤ src.envelope n := src.henv_bound τ₀ ⟨hτ₀.le, hτ₀W.le⟩ n
    calc |a τ₀ n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a τ₀ n|
          * |cosineMode n x|
        ≤ (|a τ₀ n| + unitIntervalCosineEigenvalue n * |duhamelSpectralCoeff a τ₀ n|) * 1 :=
          mul_le_mul hlhs (hcos_le n) (abs_nonneg _)
            (add_nonneg (abs_nonneg _) (mul_nonneg hlam_nn (abs_nonneg _)))
      _ = |a τ₀ n| + unitIntervalCosineEigenvalue n * |duhamelSpectralCoeff a τ₀ n| := mul_one _
      _ ≤ src.envelope n + unitIntervalCosineEigenvalue n * |duhamelSpectralCoeff a τ₀ n| := by
          gcongr
  rw [show (∑' n, (a τ₀ n - unitIntervalCosineEigenvalue n *
      localRestartCoeff a₀ a τ₀ n) * cosineMode n x) =
      ∑' n, -(unitIntervalCosineEigenvalue n *
        Real.exp (-τ₀ * unitIntervalCosineEigenvalue n)) * a₀ n * cosineMode n x +
      ∑' n, (a τ₀ n - unitIntervalCosineEigenvalue n *
        duhamelSpectralCoeff a τ₀ n) * cosineMode n x from by
    rw [← hsum1.tsum_add hsum2]
    congr 1; ext n; simp only [localRestartCoeff]; ring]
  exact hstep1

/-- Windowed time-derivative identity from a restart representation. -/
private theorem timeDeriv_eq_of_rep_on
    {u : ℝ → intervalDomainPoint → ℝ} {t₀ : ℝ}
    {a₀ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (ha₀ : ∀ n, |a₀ n| ≤ M)
    {a : ℝ → ℕ → ℝ} {W : ℝ}
    (src : DuhamelSourceTimeC1On a 0 W)
    {offset : ℝ} (hoff : 0 < t₀ - offset) (hoffW : t₀ - offset < W)
    (hrep : ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
      u s y = ∑' n, localRestartCoeff a₀ a (s - offset) n * cosineMode n y.1)
    (x : intervalDomainPoint) :
    intervalDomain.timeDeriv u t₀ x
      = ∑' n, (a (t₀ - offset) n - unitIntervalCosineEigenvalue n
          * localRestartCoeff a₀ a (t₀ - offset) n) * cosineMode n x.1 := by
  have hshift : HasDerivAt (fun s : ℝ => s - offset) 1 t₀ :=
    (hasDerivAt_id t₀).sub_const offset
  have hD := (restartCosineSeries_hasDerivAt_time_of_on hM ha₀ src hoff hoffW x.1).comp
    t₀ hshift
  have heq : (fun s => u s x) =ᶠ[𝓝 t₀]
      ((fun τ => ∑' n, localRestartCoeff a₀ a τ n * cosineMode n x.1)
        ∘ fun s => s - offset) := by
    filter_upwards [hrep] with s hs using hs x
  have hd := hD.congr_of_eventuallyEq heq
  show deriv (fun s => u s x) t₀ = _
  rw [hd.deriv, mul_one]

/-- Public version of the windowed restart time-derivative identity.  This
exposes the reusable On-source calculation without forcing downstream files to
duplicate the long `restartCosineSeries_hasDerivAt_time_of_on` proof. -/
theorem timeDeriv_eq_of_rep_on_public
    {u : ℝ → intervalDomainPoint → ℝ} {t₀ : ℝ}
    {a₀ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (ha₀ : ∀ n, |a₀ n| ≤ M)
    {a : ℝ → ℕ → ℝ} {W : ℝ}
    (src : DuhamelSourceTimeC1On a 0 W)
    {offset : ℝ} (hoff : 0 < t₀ - offset) (hoffW : t₀ - offset < W)
    (hrep : ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
      u s y = ∑' n, localRestartCoeff a₀ a (s - offset) n * cosineMode n y.1)
    (x : intervalDomainPoint) :
    intervalDomain.timeDeriv u t₀ x
      = ∑' n, (a (t₀ - offset) n - unitIntervalCosineEigenvalue n
          * localRestartCoeff a₀ a (t₀ - offset) n) * cosineMode n x.1 :=
  timeDeriv_eq_of_rep_on hM ha₀ src hoff hoffW hrep x

/-! ## Theorem 1 On — localized B-form PDE with explicit hpost -/

set_option maxHeartbeats 400000 in
/-- Localized B-form PDE with strict positivity supplied explicitly,
from windowed source data `DuhamelSourceTimeC1On aB 0 D.T`.

This is the windowed analogue of
`hasBFormSpectralPdeAgreement_conjugatePicardLimit_of_localized_data_with_hpost`.
The conclusion is the PDE identity (not `HasBFormSpectralPdeAgreement`),
since the latter packs a `DuhamelSourceTimeC1` witness that cannot be
derived from windowed data alone. -/
theorem pde_u_of_localized_data_with_hpost_on
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀)
    (hpost : ∀ σ, 0 < σ → σ < D.T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        0 < intervalDomainLift (conjugatePicardLimit p u₀ D.T σ) x)
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ < D.T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ < D.T →
      Set.EqOn (intervalDomainLift (conjugatePicardLimit p u₀ D.T σ))
        (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (aB : ℝ → ℕ → ℝ)
    (hsrcB_on : DuhamelSourceTimeC1On aB 0 D.T)
    (hsource_split : ∀ σ, 0 < σ → σ < D.T → ∀ n,
      aB σ n =
        coupledLogisticSourceCoeffs p (conjugatePicardLimit p u₀ D.T) σ n
          - p.χ₀ *
            coupledChemDivSourceCoeffs p (conjugatePicardLimit p u₀ D.T) σ n)
    (hB_restart : ∀ t₀, 0 < t₀ → t₀ < D.T →
      ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
        conjugatePicardLimit p u₀ D.T s y =
          ∑' n,
            localRestartCoeff
              (cosineCoeffs
                (intervalDomainLift
                  (conjugatePicardLimit p u₀ D.T (t₀ / 2))))
              (fun σ n => aB (t₀ / 2 + σ) n)
              (s - t₀ / 2) n * cosineMode n y.1)
    (hlogData : ∀ t, 0 < t → t < D.T →
      LogisticCosineFourierData p (conjugatePicardLimit p u₀ D.T) t)
    (hchemData : ∀ t, 0 < t → t < D.T →
      ChemDivCosineFourierDataIoo p
        ((conjugatePicardLimit p u₀ D.T) t)
        (coupledChemicalConcentration p
          (conjugatePicardLimit p u₀ D.T) t)) :
    ∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv (conjugatePicardLimit p u₀ D.T) t x =
        intervalDomain.laplacian ((conjugatePicardLimit p u₀ D.T) t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p
              ((conjugatePicardLimit p u₀ D.T) t)
              (ShenWork.IntervalMildToClassical.mildChemicalConcentration p
                (conjugatePicardLimit p u₀ D.T) t) x
          + (conjugatePicardLimit p u₀ D.T) t x
            * (p.a - p.b * ((conjugatePicardLimit p u₀ D.T) t x) ^ p.α) := by
  intro t₀ x ht₀ ht₀T hx
  set u : ℝ → intervalDomainPoint → ℝ := conjugatePicardLimit p u₀ D.T
  set τ : ℝ := t₀ / 2 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hτT : τ < D.T := by rw [hτdef]; linarith
  have htmτ : t₀ - τ = τ := by rw [hτdef]; ring
  have hMnn : 0 ≤ D.M := D.hM.le
  have hubt := conjugatePicardLimit_hubt_of_picard_data D
  set a₀ : ℕ → ℝ := cosineCoeffs (intervalDomainLift (u τ)) with ha₀def
  set a : ℝ → ℕ → ℝ := fun σ n => aB (τ + σ) n with hadef
  have ha₀_bd : ∀ k, |a₀ k| ≤ 2 * D.M := by
    intro k
    refine ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
      (((ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two
        (hbsum τ hτpos hτT)).continuous.continuousOn).congr
          (hagree τ hτpos hτT)) hMnn ?_ k
    intro y hy
    rw [abs_of_pos (hpost τ hτpos hτT y hy)]
    have hyb := hubt τ hτpos hτT y hy
    linarith
  -- Windowed shift: DuhamelSourceTimeC1On a 0 (D.T - τ)
  have srcShiftOn : DuhamelSourceTimeC1On a 0 (D.T - τ) := by
    -- Step 1: restrict [0, D.T] to [τ, D.T]
    have hIcc_sub : Icc τ D.T ⊆ Icc 0 D.T :=
      Icc_subset_Icc hτpos.le le_rfl
    have hsub : DuhamelSourceTimeC1On aB τ D.T :=
      { adot := hsrcB_on.adot
        hderiv := fun s hs n => (hsrcB_on.hderiv s (hIcc_sub hs) n).mono hIcc_sub
        hadotcont := fun n => (hsrcB_on.hadotcont n).mono hIcc_sub
        envelope := hsrcB_on.envelope
        henv_summable := hsrcB_on.henv_summable
        henv_bound := fun s hs n => hsrcB_on.henv_bound s (hIcc_sub hs) n
        derivBound := hsrcB_on.derivBound
        hderivBound := fun s hs n => hsrcB_on.hderivBound s (hIcc_sub hs) n }
    -- Step 2: shift [τ, τ+(D.T-τ)] → [0, D.T-τ]
    rw [show a = fun s n => aB (τ + s) n from rfl]
    have hsub' : DuhamelSourceTimeC1On aB τ (τ + (D.T - τ)) := by
      rwa [show τ + (D.T - τ) = D.T from by ring]
    exact hsub'.shift_zero
  have hoff : 0 < t₀ - τ := by rw [htmτ]; exact hτpos
  have hoffW : t₀ - τ < D.T - τ := by linarith
  have hrep : ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
      u s y = ∑' n, localRestartCoeff a₀ a (s - τ) n * cosineMode n y.1 := by
    have h := hB_restart t₀ ht₀ ht₀T
    simpa [u, a₀, a, τ, hτdef] using h
  have hsource_at : ∀ n, a (t₀ - τ) n =
      coupledLogisticSourceCoeffs p u t₀ n
        - p.χ₀ * coupledChemDivSourceCoeffs p u t₀ n := by
    intro n
    have harg : τ + (t₀ - τ) = t₀ := by ring
    change aB (τ + (t₀ - τ)) n =
      coupledLogisticSourceCoeffs p u t₀ n
        - p.χ₀ * coupledChemDivSourceCoeffs p u t₀ n
    rw [harg]
    simpa [u] using hsource_split t₀ ht₀ ht₀T n
  have hτ_le_Tmτ : τ ≤ D.T - τ := by linarith
  have hsum_b : Summable (fun n =>
      unitIntervalCosineEigenvalue n * |localRestartCoeff a₀ a (t₀ - τ) n|) := by
    rw [htmτ]
    exact localRestartCoeff_eigenvalue_summable_of_on
      hτpos hτ_le_Tmτ ha₀_bd srcShiftOn
  -- Time derivative via windowed path
  have htime :
      intervalDomain.timeDeriv u t₀ x
        = ∑' n,
            (coupledLogisticSourceCoeffs p u t₀ n
              - p.χ₀ * coupledChemDivSourceCoeffs p u t₀ n
              - unitIntervalCosineEigenvalue n
                * localRestartCoeff a₀ a (t₀ - τ) n)
              * cosineMode n x.1 := by
    have htimeRaw := timeDeriv_eq_of_rep_on
      (by nlinarith [D.hM.le]) ha₀_bd srcShiftOn hoff hoffW hrep x
    rw [htimeRaw]
    exact tsum_congr (fun n => by rw [hsource_at n])
  -- Laplacian
  have hrep_real : ∀ z ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t₀) z
        = ∑' n, localRestartCoeff a₀ a (t₀ - τ) n * cosineMode n z := by
    intro z hz
    rw [intervalDomainLift, dif_pos hz]
    exact hrep.self_of_nhds ⟨z, hz⟩
  have hlap :
      intervalDomain.laplacian (u t₀) x
        = ∑' n, localRestartCoeff a₀ a (t₀ - τ) n
            * (-(((n : ℝ) * Real.pi) ^ 2)
              * Real.cos ((n : ℝ) * Real.pi * x.1)) :=
    ShenWork.IntervalDomainPdeUChiZero.laplacian_eq_of_rep hsum_b hrep_real hx
  -- Fourier convergence
  have hreact :
      (∑' n, coupledLogisticSourceCoeffs p u t₀ n * cosineMode n x.1)
        = u t₀ x * (p.a - p.b * (u t₀ x) ^ p.α) :=
    ShenWork.IntervalBFormSpectral.coupledLogistic_cosineFourier_convergence
      (hlogData t₀ ht₀ ht₀T) hx
  have hchem :
      (∑' n, coupledChemDivSourceCoeffs p u t₀ n * cosineMode n x.1)
        = intervalDomain.chemotaxisDiv p (u t₀)
            (ShenWork.IntervalMildToClassical.mildChemicalConcentration p u t₀) x :=
    coupledChemDiv_cosineFourier_convergence_Ioo
      p u t₀ (hchemData t₀ ht₀ ht₀T) hx
  -- Summabilities
  have hsum_src := ShenWork.IntervalBFormSpectral.coupledLogistic_cosineSeries_summable
    (hlogData t₀ ht₀ ht₀T) hx
  have hsum_chem := coupledChemDiv_cosineSeries_summable_Ioo
    p u t₀ (hchemData t₀ ht₀ ht₀T) hx
  have hsum_lb : Summable (fun n => unitIntervalCosineEigenvalue n
      * localRestartCoeff a₀ a (t₀ - τ) n * cosineMode n x.1) := by
    refine Summable.of_norm_bounded
      (g := fun n => unitIntervalCosineEigenvalue n * |localRestartCoeff a₀ a (t₀ - τ) n|)
      hsum_b (fun n => ?_)
    have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue; positivity
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hlam]
    calc unitIntervalCosineEigenvalue n * |localRestartCoeff a₀ a (t₀ - τ) n|
          * |cosineMode n x.1|
        ≤ unitIntervalCosineEigenvalue n * |localRestartCoeff a₀ a (t₀ - τ) n|
          * 1 := by
          gcongr; simp only [cosineMode]; exact Real.abs_cos_le_one _
      _ = _ := mul_one _
  exact ShenWork.IntervalConjugateDuhamelMap.hpde_u_core_general_chi p
    hsum_src hsum_chem hsum_lb htime hlap hreact hchem

/-! ## Theorem 2 On — PID discharge with windowed source -/

/-- B-form PDE with `hpost` discharged from the PID inf-threshold and
`hB_restart` from a global cosine representation, using windowed source data.

Windowed analogue of
`hasBFormSpectralPdeAgreement_conjugatePicardLimit_of_PID_global_restart`. -/
theorem pde_u_PID_global_restart_on
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (Hinf : ConjugatePicardInfThresholdData p u₀ D.T)
    (hsmall :
      |p.χ₀| * (heatGradientLinftyLinftyConstant *
          (2 * Real.sqrt D.T) * Hinf.CQ)
        + D.T * Hinf.CL ≤ paperPositiveFloor hu₀ / 2)
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ < D.T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ < D.T →
      Set.EqOn (intervalDomainLift (conjugatePicardLimit p u₀ D.T σ))
        (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (aInit : ℕ → ℝ)
    (aB : ℝ → ℕ → ℝ)
    (hsrcB_on : DuhamelSourceTimeC1On aB 0 D.T)
    (hsource_split : ∀ σ, 0 < σ → σ < D.T → ∀ n,
      aB σ n =
        coupledLogisticSourceCoeffs p (conjugatePicardLimit p u₀ D.T) σ n
          - p.χ₀ *
            coupledChemDivSourceCoeffs p (conjugatePicardLimit p u₀ D.T) σ n)
    (hB_global : ∀ t, 0 < t → t ≤ D.T →
      Set.EqOn (intervalDomainLift (conjugatePicardLimit p u₀ D.T t))
        (fun x => ∑' n, localRestartCoeff aInit aB t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hB_global_summable : ∀ t, 0 < t → t ≤ D.T →
      Summable (fun n => |localRestartCoeff aInit aB t n|))
    (hlogData : ∀ t, 0 < t → t < D.T →
      LogisticCosineFourierData p (conjugatePicardLimit p u₀ D.T) t)
    (hchemData : ∀ t, 0 < t → t < D.T →
      ChemDivCosineFourierDataIoo p
        ((conjugatePicardLimit p u₀ D.T) t)
        (coupledChemicalConcentration p
          (conjugatePicardLimit p u₀ D.T) t)) :
    ∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv (conjugatePicardLimit p u₀ D.T) t x =
        intervalDomain.laplacian ((conjugatePicardLimit p u₀ D.T) t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p
              ((conjugatePicardLimit p u₀ D.T) t)
              (ShenWork.IntervalMildToClassical.mildChemicalConcentration p
                (conjugatePicardLimit p u₀ D.T) t) x
          + (conjugatePicardLimit p u₀ D.T) t x
            * (p.a - p.b * ((conjugatePicardLimit p u₀ D.T) t x) ^ p.α) := by
  have hpost := conjugatePicardLimit_hpost_of_PID
    (p := p) (u₀ := u₀) (T := D.T) hu₀ Hinf hsmall
  have ha_cont : ∀ k, ContinuousOn (fun s => aB s k) (Set.Icc 0 D.T) :=
    fun k s hs => (hsrcB_on.hderiv s hs k).continuousWithinAt
  have hB_restart :=
    conjugatePicardLimit_B_restart_of_global_cosine
      (p := p) (u₀ := u₀) (T := D.T) (a₀ := aInit) (aB := aB)
      ha_cont hB_global hB_global_summable
  exact pde_u_of_localized_data_with_hpost_on
    D hpost bc hbsum hagree aB hsrcB_on hsource_split hB_restart hlogData
      hchemData

/-! ## Theorem 3 On — Interior PDE from windowed source (self-contained) -/

/-- Interior B-form PDE with the two localized provider inputs discharged as in
`pde_u_PID_global_restart_on`, using windowed source data.

Windowed analogue of
`intervalConjugateMildSolution_pde_u_PID_global_restart`.
This is a trivial wrapper; all work is in theorem 2. -/
theorem intervalConjugateMildSolution_pde_u_PID_global_restart_on
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (Hinf : ConjugatePicardInfThresholdData p u₀ D.T)
    (hsmall :
      |p.χ₀| * (heatGradientLinftyLinftyConstant *
          (2 * Real.sqrt D.T) * Hinf.CQ)
        + D.T * Hinf.CL ≤ paperPositiveFloor hu₀ / 2)
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ < D.T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ < D.T →
      Set.EqOn (intervalDomainLift (conjugatePicardLimit p u₀ D.T σ))
        (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (aInit : ℕ → ℝ)
    (aB : ℝ → ℕ → ℝ)
    (hsrcB_on : DuhamelSourceTimeC1On aB 0 D.T)
    (hsource_split : ∀ σ, 0 < σ → σ < D.T → ∀ n,
      aB σ n =
        coupledLogisticSourceCoeffs p (conjugatePicardLimit p u₀ D.T) σ n
          - p.χ₀ *
            coupledChemDivSourceCoeffs p (conjugatePicardLimit p u₀ D.T) σ n)
    (hB_global : ∀ t, 0 < t → t ≤ D.T →
      Set.EqOn (intervalDomainLift (conjugatePicardLimit p u₀ D.T t))
        (fun x => ∑' n, localRestartCoeff aInit aB t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hB_global_summable : ∀ t, 0 < t → t ≤ D.T →
      Summable (fun n => |localRestartCoeff aInit aB t n|))
    (hlogData : ∀ t, 0 < t → t < D.T →
      LogisticCosineFourierData p (conjugatePicardLimit p u₀ D.T) t)
    (hchemData : ∀ t, 0 < t → t < D.T →
      ChemDivCosineFourierDataIoo p
        ((conjugatePicardLimit p u₀ D.T) t)
        (coupledChemicalConcentration p
          (conjugatePicardLimit p u₀ D.T) t)) :
    ∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv (conjugatePicardLimit p u₀ D.T) t x =
        intervalDomain.laplacian ((conjugatePicardLimit p u₀ D.T) t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p
              ((conjugatePicardLimit p u₀ D.T) t)
              (ShenWork.IntervalMildToClassical.mildChemicalConcentration p
                (conjugatePicardLimit p u₀ D.T) t) x
          + (conjugatePicardLimit p u₀ D.T) t x
            * (p.a - p.b * ((conjugatePicardLimit p u₀ D.T) t x) ^ p.α) :=
  pde_u_PID_global_restart_on
    D hu₀ Hinf hsmall bc hbsum hagree aInit aB hsrcB_on hsource_split
    hB_global hB_global_summable hlogData hchemData

#print axioms pde_u_of_localized_data_with_hpost_on
#print axioms pde_u_PID_global_restart_on
#print axioms intervalConjugateMildSolution_pde_u_PID_global_restart_on

end ShenWork.IntervalConjugatePicard
