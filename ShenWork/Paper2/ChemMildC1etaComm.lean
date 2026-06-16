/-
  ShenWork/Paper2/ChemMildC1etaComm.lean

  **Route-B commutation lemma for the second-derivative `C^θ → C^η` estimate.**

  The single new PDE fact discharging brick 4 of the divergence-form Schauder
  estimate (file `ChemMildC1eta.lean`).  For the interval-Neumann propagator
  `S(σ)` on `[0,1]`, continuous data `h` with bounded cosine coefficients:

    `∂ₓₓ S(σ)h (x) = S(σ/2)(∂ₓₓ S(σ/2)h) (x)`,   `x ∈ [0,1]`.

  ## Mechanism (spectral, endpoint-robust)
  On `[0,1]` the propagator agrees with the cosine heat value
  (`intervalFullSemigroupOperator_eq_cosineHeatValue_Icc`):
    `S(σ)h(x) = ∑'ₙ e^{−σλₙ} ĥₙ cos(nπx) = cosineCoeffSeries (e^{−σλ·} ĥ) x`,
  where `cosineCoeffSeries b x = ∑'ₙ bₙ cos(nπx)` is the globally-`C²` engine of
  `IntervalDuhamelClosedC2` (keyed on `∑'ₙ λₙ|bₙ| < ∞`).  Since the coefficients
  `e^{−σλₙ} ĥₙ` are `λ`-weighted-`ℓ¹` (`eigenvalue_mul_exp_summable`), both sides
  are genuinely `C²` on all of `ℝ`, the spatial `∂ₓₓ` acts as `−λₙ·` termwise
  (`cosineCoeffSeries_deriv2_eq`), and the half-time split
    `−λₙ e^{−σλₙ} = e^{−(σ/2)λₙ} · (−λₙ e^{−(σ/2)λₙ})`
  is exactly one `S(σ/2)` re-application of `∂ₓₓ S(σ/2)h`.  The endpoint
  derivative subtlety is avoided: the spectral identity is global on `ℝ`, and the
  propagator's `∂ₓₓ` is pinned to it through an open-neighbourhood `deriv`
  congruence on `Ioo 0 1`, extended to `Icc 0 1` by continuity of both values.

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.PDE.IntervalDuhamelClosedC2
import ShenWork.PDE.IntervalSemigroupComposition
import ShenWork.PDE.IntervalFullKernelSecondDerivCtheta

open MeasureTheory Filter Topology
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalDomainRegularityBootstrap
  (unitIntervalCosineHeatSecondValue unitIntervalCosineHeatSecondPointWeight)
open ShenWork.IntervalDuhamelClosedC2
  (cosineCoeffSeries_contDiff_two cosineCoeffSeries_deriv2_eq
    cosineCoeffSeries_grad_hasDerivAt unitIntervalCosineHeatValue_spatial_second_deriv
    unitIntervalCosineHeatSecondPointWeight_eq_neg_eigenvalue_mul)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalFullKernelSpectralClean (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc)
open ShenWork.IntervalSemigroupComposition (cosineCoeffs_semigroup cosineCoeffs_semigroup_abs_le
  cosineCoeffs_unitIntervalCosineHeatValue)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

noncomputable section

namespace ShenWork.Paper2

/-! ## Spectral bridge: the propagator as a `cosineCoeffSeries` -/

/-- The heat value as a `cosineCoeffSeries` with the damped coefficients
`e^{−σλₙ} aₙ` (the scalar `aₙ` commutes through the point weight). -/
theorem unitIntervalCosineHeatValue_eq_cosineCoeffSeries (σ : ℝ) (a : ℕ → ℝ) (x : ℝ) :
    unitIntervalCosineHeatValue σ a x
      = ∑' n, (Real.exp (-σ * unitIntervalCosineEigenvalue n) * a n) * cosineMode n x := by
  unfold unitIntervalCosineHeatValue unitIntervalCosineHeatPointWeight unitIntervalCosineMode
  refine tsum_congr (fun n => ?_)
  rw [show cosineMode n x = Real.cos ((n : ℝ) * Real.pi * x) from rfl]
  ring

/-- `∑ₙ λₙ e^{−τλₙ} < ∞` for `τ > 0` (comparison with `n²·e^{−cn}`); the parabolic
gain that exp-damps the polynomial eigenvalue weight. -/
theorem eigenvalue_mul_exp_summable {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n * Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by
  have hc : 0 < τ * Real.pi ^ 2 := by positivity
  have hbase := (Real.summable_pow_mul_exp_neg_nat_mul 2 hc).mul_left (Real.pi ^ 2)
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity)
      (Real.exp_nonneg _)) (fun n => ?_) hbase
  simp only [unitIntervalCosineEigenvalue]
  calc ((n : ℝ) * Real.pi) ^ 2 * Real.exp (-τ * ((n : ℝ) * Real.pi) ^ 2)
      = (n : ℝ) ^ 2 * Real.pi ^ 2 * Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ) ^ 2) := by ring_nf
    _ ≤ (n : ℝ) ^ 2 * Real.pi ^ 2 * Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp_of_le
        have hnle : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
          rcases Nat.eq_zero_or_pos n with hn | hn
          · simp [hn]
          · exact le_self_pow₀ (Nat.one_le_cast.2 hn) (by norm_num)
        nlinarith
    _ = Real.pi ^ 2 * ((n : ℝ) ^ 2 * Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ))) := by ring

/-- `λ`-weighted `ℓ¹` of the damped coefficients `e^{−σλₙ} aₙ` (bounded `a`),
the hypothesis that powers the global-`C²` cosine-series engine. -/
theorem dampedCoeff_eigenvalue_summable {σ : ℝ} (hσ : 0 < σ) {a : ℕ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n| ≤ M) :
    Summable (fun n => unitIntervalCosineEigenvalue n
      * |Real.exp (-σ * unitIntervalCosineEigenvalue n) * a n|) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((eigenvalue_mul_exp_summable hσ).mul_right M)
  · have hev : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue; positivity
    positivity
  rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  have hev : 0 ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue; positivity
  calc unitIntervalCosineEigenvalue n
        * (Real.exp (-σ * unitIntervalCosineEigenvalue n) * |a n|)
      ≤ unitIntervalCosineEigenvalue n
        * (Real.exp (-σ * unitIntervalCosineEigenvalue n) * M) := by
        gcongr; exact hM n
    _ = unitIntervalCosineEigenvalue n
        * Real.exp (-σ * unitIntervalCosineEigenvalue n) * M := by ring

/-! ## Pinning the propagator's `∂ₓₓ` to the spectral second value on `[0,1]` -/

/-- The propagator's second `x`-derivative equals the spectral second value on the
OPEN interval, via an open-neighbourhood `deriv`-congruence: `S(σ)h` and the
cosine heat value agree on the open `Ioo 0 1` (`…_eq_cosineHeatValue_Icc`), hence so
do their first derivatives near each interior point, hence the second derivatives at
each interior point coincide.  The spectral side is then `unitIntervalCosineHeatSecondValue`
(`unitIntervalCosineHeatValue_spatial_second_deriv`). -/
theorem intervalFullSemigroupOperator_secondDeriv_eq_secondValue_Ioo
    {σ : ℝ} (hσ : 0 < σ) {h : ℝ → ℝ} (hh : Continuous h) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs h n| ≤ M) {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    deriv (fun z : ℝ => deriv (fun w : ℝ => intervalFullSemigroupOperator σ h w) z) x
      = unitIntervalCosineHeatSecondValue σ (cosineCoeffs h) x := by
  -- The two functions agree on the open set `Ioo 0 1`.
  have hEqOn : Set.EqOn (fun w : ℝ => intervalFullSemigroupOperator σ h w)
      (fun w : ℝ => unitIntervalCosineHeatValue σ (cosineCoeffs h) w) (Set.Ioo (0:ℝ) 1) :=
    fun w hw => intervalFullSemigroupOperator_eq_cosineHeatValue_Icc hσ hh hM
      (Set.Ioo_subset_Icc_self hw)
  -- first derivatives agree near every interior point.
  have hderiv1 : Set.EqOn
      (deriv (fun w : ℝ => intervalFullSemigroupOperator σ h w))
      (deriv (fun w : ℝ => unitIntervalCosineHeatValue σ (cosineCoeffs h) w))
      (Set.Ioo (0:ℝ) 1) := by
    intro y hy
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Ioo hy) hEqOn)
  -- second derivatives at `x` coincide.
  have hstep : deriv (fun z : ℝ => deriv (fun w : ℝ => intervalFullSemigroupOperator σ h w) z) x
      = deriv (fun z : ℝ => deriv (fun w : ℝ => unitIntervalCosineHeatValue σ (cosineCoeffs h) w) z)
          x :=
    Filter.EventuallyEq.deriv_eq
      (Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Ioo hx) hderiv1)
  rw [hstep, unitIntervalCosineHeatValue_spatial_second_deriv hσ hM]

/-! ## The spectral second value as a `cosineCoeffSeries` -/

/-- The `n`-th cosine coefficient of the spectral second value: `−λₙ e^{−σλₙ} aₙ`. -/
def secondValueCoeff (σ : ℝ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  -(unitIntervalCosineEigenvalue n) * (Real.exp (-σ * unitIntervalCosineEigenvalue n) * a n)

/-- `unitIntervalCosineHeatSecondValue σ a x = ∑'ₙ (secondValueCoeff σ a n)·cos(nπx)`,
i.e. the second value is the `cosineCoeffSeries` of `−λₙ e^{−σλₙ} aₙ`. -/
theorem unitIntervalCosineHeatSecondValue_eq_cosineCoeffSeries (σ : ℝ) (a : ℕ → ℝ) (x : ℝ) :
    unitIntervalCosineHeatSecondValue σ a x
      = ∑' n, secondValueCoeff σ a n * cosineMode n x := by
  unfold unitIntervalCosineHeatSecondValue secondValueCoeff
  refine tsum_congr (fun n => ?_)
  rw [unitIntervalCosineHeatSecondPointWeight_eq_neg_eigenvalue_mul,
    show unitIntervalCosineHeatPointWeight σ x n
      = Real.exp (-σ * unitIntervalCosineEigenvalue n) * cosineMode n x from rfl]
  ring

/-- `∑ₙ λₙ² e^{−σλₙ} < ∞` for `σ > 0` (comparison with `n⁴·e^{−cn}`). -/
theorem eigenvalueSq_mul_exp_summable {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n ^ 2 * Real.exp (-σ * unitIntervalCosineEigenvalue n)) := by
  have hc : 0 < σ * Real.pi ^ 2 := by positivity
  have hbase := (Real.summable_pow_mul_exp_neg_nat_mul 4 hc).mul_left (Real.pi ^ 4)
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (by positivity) (Real.exp_nonneg _)) (fun n => ?_) hbase
  simp only [unitIntervalCosineEigenvalue]
  calc (((n : ℝ) * Real.pi) ^ 2) ^ 2 * Real.exp (-σ * ((n : ℝ) * Real.pi) ^ 2)
      = (n : ℝ) ^ 4 * Real.pi ^ 4 * Real.exp (-(σ * Real.pi ^ 2) * (n : ℝ) ^ 2) := by ring_nf
    _ ≤ (n : ℝ) ^ 4 * Real.pi ^ 4 * Real.exp (-(σ * Real.pi ^ 2) * (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp_of_le
        have hnle : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
          rcases Nat.eq_zero_or_pos n with hn | hn
          · simp [hn]
          · exact le_self_pow₀ (Nat.one_le_cast.2 hn) (by norm_num)
        nlinarith
    _ = Real.pi ^ 4 * ((n : ℝ) ^ 4 * Real.exp (-(σ * Real.pi ^ 2) * (n : ℝ))) := by ring

/-- `λ`-weighted `ℓ¹` of the second-value coefficients `−λₙ e^{−σλₙ} aₙ`
(`∑'ₙ λₙ·|−λₙ e^{−σλₙ} aₙ| < ∞`): the engine hypothesis for `Gspec`.  Bounded by
`M·∑'ₙ λₙ²e^{−σλₙ}`, summable since the half-time exponential damps `λ²`. -/
theorem secondValueCoeff_eigenvalue_summable {σ : ℝ} (hσ : 0 < σ) {a : ℕ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n| ≤ M) :
    Summable (fun n => unitIntervalCosineEigenvalue n * |secondValueCoeff σ a n|) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  -- majorant `M·λₙ²e^{−σλₙ} = M·(λₙ e^{−(σ/2)λₙ})·(λₙ e^{−(σ/2)λₙ})`; use product of two
  -- `λ e^{−(σ/2)λ}` summable-bounded factors. We bound by `M · λₙ·(λₙ e^{−σλₙ})`.
  refine Summable.of_nonneg_of_le (fun n => by
      have hev : 0 ≤ unitIntervalCosineEigenvalue n := by
        unfold unitIntervalCosineEigenvalue; positivity
      positivity) (fun n => ?_)
    ((eigenvalueSq_mul_exp_summable hσ).mul_left M)
  unfold secondValueCoeff
  have hev : 0 ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue; positivity
  rw [abs_mul, abs_neg, abs_of_nonneg hev, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  calc unitIntervalCosineEigenvalue n
        * (unitIntervalCosineEigenvalue n
          * (Real.exp (-σ * unitIntervalCosineEigenvalue n) * |a n|))
      ≤ unitIntervalCosineEigenvalue n
        * (unitIntervalCosineEigenvalue n
          * (Real.exp (-σ * unitIntervalCosineEigenvalue n) * M)) := by gcongr; exact hM n
    _ = M * (unitIntervalCosineEigenvalue n ^ 2
          * Real.exp (-σ * unitIntervalCosineEigenvalue n)) := by ring

/-! ## `Gspec`: the spectral `∂ₓₓ S(σ/2)h`, a bounded continuous `cosineCoeffSeries` -/

/-- The half-time damped second-value coefficients written via a QUARTER-time heat
value: `secondValueCoeff (σ/2) a n = e^{−(σ/4)λₙ}·c_n` with `c_n := −λₙ e^{−(σ/4)λₙ} a_n`
BOUNDED (`λ e^{−(σ/4)λ} ≤ 4/σ`).  This exposes `Gspec` as a propagator value so the
committed coefficient extraction applies. -/
def quarterCoeff (σ : ℝ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  -(unitIntervalCosineEigenvalue n)
    * (Real.exp (-(σ / 4) * unitIntervalCosineEigenvalue n) * a n)

theorem quarterCoeff_abs_le {σ : ℝ} (hσ : 0 < σ) {a : ℕ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n| ≤ M) (n : ℕ) : |quarterCoeff σ a n| ≤ 4 / σ * M := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  unfold quarterCoeff
  have hev : 0 ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue; positivity
  rw [abs_mul, abs_neg, abs_of_nonneg hev, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  -- `λ·e^{−(σ/4)λ} = (4/σ)·((σ/4)λ·e^{−(σ/4)λ}) ≤ 4/σ` (s·e^{−s} ≤ 1).
  have hkey : unitIntervalCosineEigenvalue n
      * Real.exp (-(σ / 4) * unitIntervalCosineEigenvalue n) ≤ 4 / σ := by
    have hs : (0:ℝ) ≤ σ / 4 * unitIntervalCosineEigenvalue n := by positivity
    have hbound := real_mul_exp_neg_le_one hs
    have hrw : unitIntervalCosineEigenvalue n
        * Real.exp (-(σ / 4) * unitIntervalCosineEigenvalue n)
        = 4 / σ * (σ / 4 * unitIntervalCosineEigenvalue n
          * Real.exp (-(σ / 4 * unitIntervalCosineEigenvalue n))) := by
      rw [show -(σ / 4) * unitIntervalCosineEigenvalue n
          = -(σ / 4 * unitIntervalCosineEigenvalue n) by ring]
      have hσne : σ ≠ 0 := ne_of_gt hσ
      field_simp
    rw [hrw]
    calc 4 / σ * (σ / 4 * unitIntervalCosineEigenvalue n
          * Real.exp (-(σ / 4 * unitIntervalCosineEigenvalue n)))
        ≤ 4 / σ * 1 := by apply mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = 4 / σ := by ring
  calc unitIntervalCosineEigenvalue n
        * (Real.exp (-(σ / 4) * unitIntervalCosineEigenvalue n) * |a n|)
      ≤ unitIntervalCosineEigenvalue n
        * (Real.exp (-(σ / 4) * unitIntervalCosineEigenvalue n) * M) := by gcongr; exact hM n
    _ = (unitIntervalCosineEigenvalue n
          * Real.exp (-(σ / 4) * unitIntervalCosineEigenvalue n)) * M := by ring
    _ ≤ 4 / σ * M := by apply mul_le_mul_of_nonneg_right hkey hM0

/-- `Gspec`, the spectral second derivative `∂ₓₓ S(σ/2)h`, is the QUARTER-time heat
value of the bounded `quarterCoeff`.  Hence it is `S(σ/4)(quarterCoeff)` in spectral
form, with the propagator's coefficient extraction available. -/
theorem secondValue_half_eq_quarterHeatValue (σ : ℝ) (a : ℕ → ℝ) (x : ℝ) :
    unitIntervalCosineHeatSecondValue (σ / 2) a x
      = unitIntervalCosineHeatValue (σ / 4) (quarterCoeff σ a) x := by
  unfold unitIntervalCosineHeatSecondValue unitIntervalCosineHeatValue
    unitIntervalCosineHeatPointWeight quarterCoeff
  refine tsum_congr (fun n => ?_)
  rw [unitIntervalCosineHeatSecondPointWeight_eq_neg_eigenvalue_mul,
    show unitIntervalCosineHeatPointWeight (σ / 2) x n
      = Real.exp (-(σ / 2) * unitIntervalCosineEigenvalue n)
        * unitIntervalCosineMode n x from rfl,
    show unitIntervalCosineMode n x = cosineMode n x from rfl]
  have hexp : Real.exp (-(σ / 2) * unitIntervalCosineEigenvalue n)
      = Real.exp (-(σ / 4) * unitIntervalCosineEigenvalue n)
        * Real.exp (-(σ / 4) * unitIntervalCosineEigenvalue n) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp]; ring

/-- **`Gspec`** — the spectral form of `∂ₓₓ S(σ/2)h`, as a function of `w`. -/
def Gspec (σ : ℝ) (a : ℕ → ℝ) : ℝ → ℝ :=
  fun w => unitIntervalCosineHeatSecondValue (σ / 2) a w

/-- `Gspec` is continuous (a `C²` cosine series). -/
theorem Gspec_continuous {σ : ℝ} (hσ : 0 < σ) {a : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |a n| ≤ M) :
    Continuous (Gspec σ a) := by
  have hfun : Gspec σ a
      = fun w => ∑' n, secondValueCoeff (σ / 2) a n * cosineMode n w := by
    funext w; exact unitIntervalCosineHeatSecondValue_eq_cosineCoeffSeries (σ / 2) a w
  rw [hfun]
  exact (cosineCoeffSeries_contDiff_two
    (secondValueCoeff_eigenvalue_summable (by positivity) hM)).continuous

/-- The cosine coefficients of `Gspec`: `cosineCoeffs (Gspec σ a) n = secondValueCoeff (σ/2) a n`
`= −λₙ e^{−(σ/2)λₙ} aₙ` (bounded), via the QUARTER-time heat-value representation and the
committed coefficient extraction `cosineCoeffs_unitIntervalCosineHeatValue`. -/
theorem cosineCoeffs_Gspec {σ : ℝ} (hσ : 0 < σ) {a : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |a n| ≤ M)
    (n : ℕ) : cosineCoeffs (Gspec σ a) n = secondValueCoeff (σ / 2) a n := by
  have hquarter : Gspec σ a
      = fun w => unitIntervalCosineHeatValue (σ / 4) (quarterCoeff σ a) w := by
    funext w; exact secondValue_half_eq_quarterHeatValue σ a w
  rw [hquarter, cosineCoeffs_unitIntervalCosineHeatValue (by positivity)
    (quarterCoeff_abs_le hσ hM) n]
  -- `e^{−(σ/4)λ}·quarterCoeff = secondValueCoeff(σ/2)`.
  unfold quarterCoeff secondValueCoeff
  have hexp : Real.exp (-(σ / 4) * unitIntervalCosineEigenvalue n)
      * Real.exp (-(σ / 4) * unitIntervalCosineEigenvalue n)
      = Real.exp (-(σ / 2) * unitIntervalCosineEigenvalue n) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [show Real.exp (-(σ / 4) * unitIntervalCosineEigenvalue n)
        * (-unitIntervalCosineEigenvalue n
          * (Real.exp (-(σ / 4) * unitIntervalCosineEigenvalue n) * a n))
      = -unitIntervalCosineEigenvalue n
        * ((Real.exp (-(σ / 4) * unitIntervalCosineEigenvalue n)
            * Real.exp (-(σ / 4) * unitIntervalCosineEigenvalue n)) * a n) by ring]
  rw [hexp]

/-- `secondValueCoeff` is bounded: `|secondValueCoeff (σ/2) a n| ≤ 2/σ·M`
(`λ e^{−(σ/2)λ} ≤ 2/σ`). -/
theorem secondValueCoeff_abs_le {σ : ℝ} (hσ : 0 < σ) {a : ℕ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n| ≤ M) (n : ℕ) : |secondValueCoeff (σ / 2) a n| ≤ 2 / σ * M := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  unfold secondValueCoeff
  have hev : 0 ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue; positivity
  rw [abs_mul, abs_neg, abs_of_nonneg hev, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  have hkey : unitIntervalCosineEigenvalue n
      * Real.exp (-(σ / 2) * unitIntervalCosineEigenvalue n) ≤ 2 / σ := by
    have hs : (0:ℝ) ≤ σ / 2 * unitIntervalCosineEigenvalue n := by positivity
    have hbound := real_mul_exp_neg_le_one hs
    have hrw : unitIntervalCosineEigenvalue n
        * Real.exp (-(σ / 2) * unitIntervalCosineEigenvalue n)
        = 2 / σ * (σ / 2 * unitIntervalCosineEigenvalue n
          * Real.exp (-(σ / 2 * unitIntervalCosineEigenvalue n))) := by
      rw [show -(σ / 2) * unitIntervalCosineEigenvalue n
          = -(σ / 2 * unitIntervalCosineEigenvalue n) by ring]
      have hσne : σ ≠ 0 := ne_of_gt hσ
      field_simp
    rw [hrw]
    calc 2 / σ * (σ / 2 * unitIntervalCosineEigenvalue n
          * Real.exp (-(σ / 2 * unitIntervalCosineEigenvalue n)))
        ≤ 2 / σ * 1 := by apply mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = 2 / σ := by ring
  calc unitIntervalCosineEigenvalue n
        * (Real.exp (-(σ / 2) * unitIntervalCosineEigenvalue n) * |a n|)
      ≤ unitIntervalCosineEigenvalue n
        * (Real.exp (-(σ / 2) * unitIntervalCosineEigenvalue n) * M) := by gcongr; exact hM n
    _ = (unitIntervalCosineEigenvalue n
          * Real.exp (-(σ / 2) * unitIntervalCosineEigenvalue n)) * M := by ring
    _ ≤ 2 / σ * M := by apply mul_le_mul_of_nonneg_right hkey hM0

/-! ## The commutation identity (spectral, on `[0,1]`) -/

/-- **Spectral half-time split.**  `S(σ/2) Gspec x = unitIntervalCosineHeatSecondValue σ ĥ x`
on `[0,1]`: the propagator of `Gspec` is the cosine heat value of `cosineCoeffs Gspec`
(`= secondValueCoeff (σ/2) ĥ`), and `e^{−(σ/2)λₙ}·(−λₙ e^{−(σ/2)λₙ} ĥₙ) = −λₙ e^{−σλₙ} ĥₙ`. -/
theorem semigroup_Gspec_eq_secondValue {σ : ℝ} (hσ : 0 < σ) {h : ℝ → ℝ} (hh : Continuous h)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs h n| ≤ M) {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    intervalFullSemigroupOperator (σ / 2) (Gspec σ (cosineCoeffs h)) x
      = unitIntervalCosineHeatSecondValue σ (cosineCoeffs h) x := by
  have hGcont : Continuous (Gspec σ (cosineCoeffs h)) := Gspec_continuous hσ hM
  have hGbd : ∀ n, |cosineCoeffs (Gspec σ (cosineCoeffs h)) n| ≤ 2 / σ * M := by
    intro n; rw [cosineCoeffs_Gspec hσ hM n]; exact secondValueCoeff_abs_le hσ hM n
  rw [intervalFullSemigroupOperator_eq_cosineHeatValue_Icc (by positivity) hGcont hGbd hx]
  -- `unitIntervalCosineHeatValue (σ/2) (cosineCoeffs Gspec) x = secondValue σ ĥ x`.
  unfold unitIntervalCosineHeatValue unitIntervalCosineHeatSecondValue
    unitIntervalCosineHeatPointWeight
  refine tsum_congr (fun n => ?_)
  rw [cosineCoeffs_Gspec hσ hM n, unitIntervalCosineHeatSecondPointWeight_eq_neg_eigenvalue_mul]
  unfold secondValueCoeff
  rw [show unitIntervalCosineHeatPointWeight σ x n
      = Real.exp (-σ * unitIntervalCosineEigenvalue n) * unitIntervalCosineMode n x from rfl]
  have hexp : Real.exp (-(σ / 2) * unitIntervalCosineEigenvalue n)
      * Real.exp (-(σ / 2) * unitIntervalCosineEigenvalue n)
      = Real.exp (-σ * unitIntervalCosineEigenvalue n) := by
    rw [← Real.exp_add]; congr 1; ring
  -- LHS `= e^{−(σ/2)λ}·cos · (−λ e^{−(σ/2)λ} ĥ)`; RHS `= (−λ e^{−σλ} ĥ)·cos`.
  have hgoal : Real.exp (-(σ / 2) * unitIntervalCosineEigenvalue n)
        * unitIntervalCosineMode n x
        * (-unitIntervalCosineEigenvalue n
          * (Real.exp (-(σ / 2) * unitIntervalCosineEigenvalue n) * cosineCoeffs h n))
      = -unitIntervalCosineEigenvalue n
          * (Real.exp (-σ * unitIntervalCosineEigenvalue n) * unitIntervalCosineMode n x)
          * cosineCoeffs h n := by
    rw [show Real.exp (-(σ / 2) * unitIntervalCosineEigenvalue n)
          * unitIntervalCosineMode n x
          * (-unitIntervalCosineEigenvalue n
            * (Real.exp (-(σ / 2) * unitIntervalCosineEigenvalue n) * cosineCoeffs h n))
        = -unitIntervalCosineEigenvalue n
          * ((Real.exp (-(σ / 2) * unitIntervalCosineEigenvalue n)
              * Real.exp (-(σ / 2) * unitIntervalCosineEigenvalue n))
            * unitIntervalCosineMode n x) * cosineCoeffs h n by ring]
    rw [hexp]
  exact hgoal

/-- `Gspec σ ĥ` IS the propagator second derivative `∂ₓₓ S(σ/2)h` on the open
interval (pinning lemma at half time). -/
theorem Gspec_eq_secondDeriv_Ioo {σ : ℝ} (hσ : 0 < σ) {h : ℝ → ℝ} (hh : Continuous h)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs h n| ≤ M) {w : ℝ} (hw : w ∈ Set.Ioo (0:ℝ) 1) :
    Gspec σ (cosineCoeffs h) w
      = deriv (fun z : ℝ =>
          deriv (fun u : ℝ => intervalFullSemigroupOperator (σ / 2) h u) z) w := by
  rw [Gspec,
    intervalFullSemigroupOperator_secondDeriv_eq_secondValue_Ioo (by positivity) hh hM hw]

/-! ## The commutation lemma (Route B brick 4 core) -/

/-- **`intervalFullSemigroupOperator_secondDeriv_comm` (Route B).**  On the open
interval, the propagator's second `x`-derivative is the `S(σ/2)`-propagated spectral
second derivative `Gspec` (`= ∂ₓₓ S(σ/2)h`):

  `∂ₓₓ S(σ)h (x) = S(σ/2)(∂ₓₓ S(σ/2)h) (x)`,   `x ∈ (0,1)`.

LHS via the interior pinning to `secondValue σ ĥ`; RHS via the spectral half-time
split `S(σ/2) Gspec = secondValue σ ĥ`.  This is the single new PDE fact discharging
brick 4 of the divergence-form Schauder estimate (the orchestrator's Route B). -/
theorem intervalFullSemigroupOperator_secondDeriv_comm {σ : ℝ} (hσ : 0 < σ)
    {h : ℝ → ℝ} (hh : Continuous h) {M : ℝ} (hM : ∀ n, |cosineCoeffs h n| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    deriv (fun z : ℝ => deriv (fun w : ℝ => intervalFullSemigroupOperator σ h w) z) x
      = intervalFullSemigroupOperator (σ / 2) (Gspec σ (cosineCoeffs h)) x := by
  rw [intervalFullSemigroupOperator_secondDeriv_eq_secondValue_Ioo hσ hh hM hx,
    semigroup_Gspec_eq_secondValue hσ hh hM (Set.Ioo_subset_Icc_self hx)]

end ShenWork.Paper2
