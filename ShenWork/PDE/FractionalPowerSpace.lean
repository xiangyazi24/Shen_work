import Mathlib

/-!
  Spectral fractional-power coefficient spaces for the one-dimensional
  Neumann Laplacian on `(0, L)`.

  The eigenvalues are `λₙ = (nπ/L)^2`.  This file records the coefficient
  characterization of the shifted fractional domain `(I - Δ)^σ` and the
  analytic core of the one-dimensional embedding: weighted `ℓ²` coefficients
  plus a summable reciprocal spectral trace give an absolutely convergent
  cosine series, hence a continuous representative.

  Scope note: this is the Hilbert/coefficient form of the H3.1 side input.
  It does not identify this concrete coefficient space with the abstract
  `Paper3.StabilityNorms.xpSigmaDistance` field; that bridge belongs to the
  Paper3 norm package rather than this standalone spectral block.
-/

noncomputable section

namespace ShenWork.PDE.FractionalPower

/-- Neumann eigenvalue `λₙ = (nπ/L)^2` for the interval of length `L`. -/
def neumannEigenvalue (L : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * Real.pi / L) ^ 2

/-- Shifted fractional-power weight `(1 + λₙ)^(2σ)`. -/
def fractionalPowerWeight (L sigma : ℝ) (n : ℕ) : ℝ :=
  (1 + neumannEigenvalue L n) ^ (2 * sigma)

/-- The weighted coefficient energy summand defining `X^σ`. -/
def fractionalPowerEnergyTerm (L sigma : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℝ :=
  fractionalPowerWeight L sigma n * ‖a n‖ ^ 2

/-- Reciprocal shifted spectral weight.  Summability of this trace is the
one-dimensional input behind the `X^σ ↪ C⁰` embedding. -/
def reciprocalFractionalPowerWeight (L sigma : ℝ) (n : ℕ) : ℝ :=
  (fractionalPowerWeight L sigma n)⁻¹

/-- Spectral fractional-power coefficient space for `(I - Δ)^σ` on `(0,L)`.

Membership is exactly square summability of the coefficients weighted by
`(1 + (nπ/L)^2)^(2σ)`. -/
abbrev FractionalPowerSpace (L sigma : ℝ) :=
  { a : ℕ → ℂ // Summable fun n : ℕ => fractionalPowerEnergyTerm L sigma a n }

/-- The subtype definition is exactly the usual weighted-`ℓ²` characterization
of the fractional-power space. -/
theorem fractionalPowerSpace_characterization
    (L sigma : ℝ) (a : ℕ → ℂ) :
    (∃ u : FractionalPowerSpace L sigma, (u : ℕ → ℂ) = a) ↔
      Summable fun n : ℕ => fractionalPowerEnergyTerm L sigma a n := by
  constructor
  · rintro ⟨u, rfl⟩
    exact u.property
  · intro h
    exact ⟨⟨a, h⟩, rfl⟩

theorem neumannEigenvalue_nonneg (L : ℝ) (n : ℕ) :
    0 ≤ neumannEigenvalue L n := by
  dsimp [neumannEigenvalue]
  positivity

theorem one_add_neumannEigenvalue_pos (L : ℝ) (n : ℕ) :
    0 < 1 + neumannEigenvalue L n := by
  have hlambda := neumannEigenvalue_nonneg L n
  linarith

theorem fractionalPowerWeight_pos (L sigma : ℝ) (n : ℕ) :
    0 < fractionalPowerWeight L sigma n := by
  dsimp [fractionalPowerWeight]
  exact Real.rpow_pos_of_pos (one_add_neumannEigenvalue_pos L n) _

theorem reciprocalFractionalPowerWeight_nonneg (L sigma : ℝ) (n : ℕ) :
    0 ≤ reciprocalFractionalPowerWeight L sigma n := by
  dsimp [reciprocalFractionalPowerWeight]
  exact inv_nonneg.mpr (fractionalPowerWeight_pos L sigma n).le

private theorem reciprocalFractionalPowerWeight_succ_le_pseries_majorant
    {L sigma : ℝ} (hL : 0 < L) (hsigma : 1 / 4 < sigma) (n : ℕ) :
    reciprocalFractionalPowerWeight L sigma (n + 1) ≤
      ((Real.pi / L) ^ 2) ^ (-(2 * sigma)) *
        (1 / |(n : ℝ) + 1| ^ (4 * sigma)) := by
  let c : ℝ := (Real.pi / L) ^ 2
  let m : ℕ := n + 1
  have hc_pos : 0 < c := by
    dsimp [c]
    exact sq_pos_of_pos (div_pos Real.pi_pos hL)
  have hm_pos_nat : 0 < m := Nat.succ_pos n
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm_pos_nat
  have hm_sq_pos : 0 < (m : ℝ) ^ 2 := sq_pos_of_pos hm_pos
  have hcm_sq_pos : 0 < c * (m : ℝ) ^ 2 := mul_pos hc_pos hm_sq_pos
  have hneumann :
      neumannEigenvalue L m = c * (m : ℝ) ^ 2 := by
    dsimp [neumannEigenvalue, c]
    ring
  have hbase_le :
      c * (m : ℝ) ^ 2 ≤ 1 + neumannEigenvalue L m := by
    rw [hneumann]
    linarith
  have hexp_nonpos : -(2 * sigma) ≤ 0 := by nlinarith [hsigma]
  have hone_nonneg : 0 ≤ 1 + neumannEigenvalue L m :=
    (one_add_neumannEigenvalue_pos L m).le
  have hrecip_eq :
      reciprocalFractionalPowerWeight L sigma m =
        (1 + neumannEigenvalue L m) ^ (-(2 * sigma)) := by
    dsimp [reciprocalFractionalPowerWeight, fractionalPowerWeight]
    rw [Real.rpow_neg hone_nonneg (2 * sigma)]
  have hpow_le :
      (1 + neumannEigenvalue L m) ^ (-(2 * sigma)) ≤
        (c * (m : ℝ) ^ 2) ^ (-(2 * sigma)) :=
    Real.rpow_le_rpow_of_nonpos hcm_sq_pos hbase_le hexp_nonpos
  have hsquare_rpow :
      ((m : ℝ) ^ 2) ^ (-(2 * sigma)) =
        (m : ℝ) ^ (-(4 * sigma)) := by
    have hpow :
        ((m : ℝ) ^ 2) ^ (-(2 * sigma)) =
          (m : ℝ) ^ ((2 : ℝ) * (-(2 * sigma))) := by
      rw [← Real.rpow_natCast (m : ℝ) 2]
      exact (Real.rpow_mul hm_pos.le (2 : ℝ) (-(2 * sigma))).symm
    calc
      ((m : ℝ) ^ 2) ^ (-(2 * sigma))
          = (m : ℝ) ^ ((2 : ℝ) * (-(2 * sigma))) := hpow
      _ = (m : ℝ) ^ (-(4 * sigma)) := by ring_nf
  have habs :
      |(n : ℝ) + 1| = (m : ℝ) := by
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    rw [abs_of_pos hpos]
    dsimp [m]
    norm_num
  have hm_rpow_neg :
      (m : ℝ) ^ (-(4 * sigma)) =
        1 / |(n : ℝ) + 1| ^ (4 * sigma) := by
    rw [habs, Real.rpow_neg hm_pos.le (4 * sigma)]
    ring
  calc
    reciprocalFractionalPowerWeight L sigma (n + 1)
        = reciprocalFractionalPowerWeight L sigma m := by rfl
    _ = (1 + neumannEigenvalue L m) ^ (-(2 * sigma)) := hrecip_eq
    _ ≤ (c * (m : ℝ) ^ 2) ^ (-(2 * sigma)) := hpow_le
    _ = c ^ (-(2 * sigma)) * ((m : ℝ) ^ 2) ^ (-(2 * sigma)) := by
          rw [Real.mul_rpow hc_pos.le (sq_nonneg (m : ℝ))]
    _ = c ^ (-(2 * sigma)) * (1 / |(n : ℝ) + 1| ^ (4 * sigma)) := by
          rw [hsquare_rpow, hm_rpow_neg]
    _ = ((Real.pi / L) ^ 2) ^ (-(2 * sigma)) *
          (1 / |(n : ℝ) + 1| ^ (4 * sigma)) := by
          rfl

/-- For `σ > 1/4`, the shifted reciprocal trace associated to
`λₙ = (nπ/L)^2` is summable. -/
theorem reciprocalFractionalPowerWeight_summable_of_sigma_gt_quarter
    {L sigma : ℝ} (hL : 0 < L) (hsigma : 1 / 4 < sigma) :
    Summable fun n : ℕ => reciprocalFractionalPowerWeight L sigma n := by
  have hp : 1 < 4 * sigma := by nlinarith [hsigma]
  have hpseries :
      Summable fun n : ℕ => 1 / |(n : ℝ) + 1| ^ (4 * sigma) :=
    (Real.summable_one_div_nat_add_rpow 1 (4 * sigma)).mpr hp
  have hmajorant :
      Summable fun n : ℕ =>
        ((Real.pi / L) ^ 2) ^ (-(2 * sigma)) *
          (1 / |(n : ℝ) + 1| ^ (4 * sigma)) :=
    hpseries.mul_left (((Real.pi / L) ^ 2) ^ (-(2 * sigma)))
  have htail :
      Summable fun n : ℕ => reciprocalFractionalPowerWeight L sigma (n + 1) := by
    refine Summable.of_nonneg_of_le
      (fun n => reciprocalFractionalPowerWeight_nonneg L sigma (n + 1))
      (fun n =>
        reciprocalFractionalPowerWeight_succ_le_pseries_majorant
          (L := L) (sigma := sigma) hL hsigma n)
      hmajorant
  exact (summable_nat_add_iff (f := fun n : ℕ =>
    reciprocalFractionalPowerWeight L sigma n) 1).mp htail

/-- Weighted `ℓ²` coefficients are `ℓ¹` once the reciprocal spectral trace is
summable.  This is the Cauchy-Schwarz/Young inequality core of the
one-dimensional fractional-domain embedding. -/
theorem coeff_norm_summable_of_reciprocal_trace
    {L sigma : ℝ} (a : ℕ → ℂ)
    (henergy : Summable fun n : ℕ => fractionalPowerEnergyTerm L sigma a n)
    (htrace : Summable fun n : ℕ => reciprocalFractionalPowerWeight L sigma n) :
    Summable fun n : ℕ => ‖a n‖ := by
  let majorant : ℕ → ℝ := fun n =>
    (1 / 2 : ℝ) *
      (fractionalPowerEnergyTerm L sigma a n +
        reciprocalFractionalPowerWeight L sigma n)
  have hmajorant :
      Summable majorant := by
    dsimp [majorant]
    exact (henergy.add htrace).mul_left (1 / 2 : ℝ)
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg (a n)) ?_ hmajorant
  intro n
  have hwpos := fractionalPowerWeight_pos L sigma n
  have hyoung :
      2 * ‖a n‖ * (1 : ℝ) ≤
        fractionalPowerWeight L sigma n * ‖a n‖ ^ 2 +
          (fractionalPowerWeight L sigma n)⁻¹ * (1 : ℝ) ^ 2 :=
    two_mul_le_add_mul_sq (a := ‖a n‖) (b := (1 : ℝ)) hwpos
  dsimp [majorant, fractionalPowerEnergyTerm, reciprocalFractionalPowerWeight]
  nlinarith

/-- Coefficients of an element of `X^σ` are absolutely summable under the
reciprocal-trace input. -/
theorem FractionalPowerSpace.coeff_norm_summable_of_reciprocal_trace
    {L sigma : ℝ} (u : FractionalPowerSpace L sigma)
    (htrace : Summable fun n : ℕ => reciprocalFractionalPowerWeight L sigma n) :
    Summable fun n : ℕ => ‖(u : ℕ → ℂ) n‖ :=
  _root_.ShenWork.PDE.FractionalPower.coeff_norm_summable_of_reciprocal_trace
    (L := L) (sigma := sigma) (u : ℕ → ℂ) u.property htrace

/-- Coefficients of an element of `X^σ` are absolutely summable for
`σ > 1/4`, using the Neumann spectrum `(nπ/L)^2`. -/
theorem FractionalPowerSpace.coeff_norm_summable_of_sigma_gt_quarter
    {L sigma : ℝ} (u : FractionalPowerSpace L sigma)
    (hL : 0 < L) (hsigma : 1 / 4 < sigma) :
    Summable fun n : ℕ => ‖(u : ℕ → ℂ) n‖ :=
  u.coeff_norm_summable_of_reciprocal_trace
    (reciprocalFractionalPowerWeight_summable_of_sigma_gt_quarter
      (L := L) (sigma := sigma) hL hsigma)

/-- The `n`-th cosine summand with coefficient `a n`. -/
def cosineSeriesTerm (L : ℝ) (a : ℕ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  a n * (Real.cos (((n : ℝ) * Real.pi / L) * x) : ℂ)

/-- Cosine-series representative of coefficient data. -/
def cosineSeries (L : ℝ) (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, cosineSeriesTerm L a n x

theorem norm_cosineSeriesTerm_le_coeff_norm
    (L : ℝ) (a : ℕ → ℂ) (n : ℕ) (x : ℝ) :
    ‖cosineSeriesTerm L a n x‖ ≤ ‖a n‖ := by
  let theta : ℝ := ((n : ℝ) * Real.pi / L) * x
  calc
    ‖cosineSeriesTerm L a n x‖
        = ‖a n‖ * |Real.cos theta| := by
          dsimp [cosineSeriesTerm, theta]
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖a n‖ * 1 := by
          exact mul_le_mul_of_nonneg_left
            (Real.abs_cos_le_one theta)
            (norm_nonneg (a n))
    _ = ‖a n‖ := by ring

theorem cosineSeriesTerm_summable_of_coeff_norm_summable
    {L : ℝ} {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖) (x : ℝ) :
    Summable fun n : ℕ => cosineSeriesTerm L a n x :=
  Summable.of_norm_bounded ha fun n => norm_cosineSeriesTerm_le_coeff_norm L a n x

theorem norm_cosineSeries_le_tsum_coeff_norm_of_coeff_norm_summable
    {L : ℝ} {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖) (x : ℝ) :
    ‖cosineSeries L a x‖ ≤ ∑' n : ℕ, ‖a n‖ := by
  have hsum := cosineSeriesTerm_summable_of_coeff_norm_summable
    (L := L) (a := a) ha x
  exact hsum.hasSum.norm_le_of_bounded ha.hasSum
    (fun n => norm_cosineSeriesTerm_le_coeff_norm L a n x)

theorem continuous_cosineSeriesTerm (L : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    Continuous fun x : ℝ => cosineSeriesTerm L a n x := by
  unfold cosineSeriesTerm
  fun_prop

theorem cosineSeries_continuous_of_coeff_norm_summable
    {L : ℝ} {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖) :
    Continuous fun x : ℝ => cosineSeries L a x := by
  unfold cosineSeries
  exact continuous_tsum
    (fun n => continuous_cosineSeriesTerm L a n)
    ha
    (fun n x => norm_cosineSeriesTerm_le_coeff_norm L a n x)

/-- Conditional `X^σ ↪ C⁰`: once the reciprocal shifted spectral trace is
summable, every fractional-power coefficient vector has a continuous cosine
representative. -/
theorem FractionalPowerSpace.continuous_cosineSeries_of_reciprocal_trace
    {L sigma : ℝ} (u : FractionalPowerSpace L sigma)
    (htrace : Summable fun n : ℕ => reciprocalFractionalPowerWeight L sigma n) :
    Continuous fun x : ℝ => cosineSeries L (u : ℕ → ℂ) x := by
  exact cosineSeries_continuous_of_coeff_norm_summable
    (FractionalPowerSpace.coeff_norm_summable_of_reciprocal_trace u htrace)

/-- Sup-norm form of the same conditional embedding. -/
theorem FractionalPowerSpace.norm_cosineSeries_le_tsum_coeff_norm
    {L sigma : ℝ} (u : FractionalPowerSpace L sigma)
    (htrace : Summable fun n : ℕ => reciprocalFractionalPowerWeight L sigma n)
    (x : ℝ) :
    ‖cosineSeries L (u : ℕ → ℂ) x‖ ≤
      ∑' n : ℕ, ‖(u : ℕ → ℂ) n‖ := by
  exact norm_cosineSeries_le_tsum_coeff_norm_of_coeff_norm_summable
    (FractionalPowerSpace.coeff_norm_summable_of_reciprocal_trace u htrace) x

/-- Fractional-power embedding `X^σ ↪ C⁰` on `(0,L)` for `σ > 1/4`.

The representative is the cosine series with spectral coefficients in
`X^σ`; continuity is obtained from absolute convergence of the coefficient
series. -/
theorem FractionalPowerSpace.continuous_cosineSeries_of_sigma_gt_quarter
    {L sigma : ℝ} (u : FractionalPowerSpace L sigma)
    (hL : 0 < L) (hsigma : 1 / 4 < sigma) :
    Continuous fun x : ℝ => cosineSeries L (u : ℕ → ℂ) x := by
  exact cosineSeries_continuous_of_coeff_norm_summable
    (u.coeff_norm_summable_of_sigma_gt_quarter hL hsigma)

/-- Sup-norm pointwise estimate accompanying `X^σ ↪ C⁰` for `σ > 1/4`. -/
theorem FractionalPowerSpace.norm_cosineSeries_le_tsum_coeff_norm_of_sigma_gt_quarter
    {L sigma : ℝ} (u : FractionalPowerSpace L sigma)
    (hL : 0 < L) (hsigma : 1 / 4 < sigma) (x : ℝ) :
    ‖cosineSeries L (u : ℕ → ℂ) x‖ ≤
      ∑' n : ℕ, ‖(u : ℕ → ℂ) n‖ := by
  exact norm_cosineSeries_le_tsum_coeff_norm_of_coeff_norm_summable
    (u.coeff_norm_summable_of_sigma_gt_quarter hL hsigma) x

end ShenWork.PDE.FractionalPower
