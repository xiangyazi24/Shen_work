import Mathlib
import ShenWork.Paper3.Statements

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
  Paper3 norm package rather than this standalone spectral block.  The Paper3
  bridge at the end of this file therefore keeps the remaining norm-comparison
  and small-data inputs explicit.
-/

noncomputable section

namespace ShenWork.PDE.FractionalPower

open _root_.ShenWork.Paper3

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

/-- Reciprocal trace weight for one spatial derivative:
`λₙ (1 + λₙ)^(-2σ)`. -/
def derivativeReciprocalFractionalPowerWeight (L sigma : ℝ) (n : ℕ) : ℝ :=
  neumannEigenvalue L n * reciprocalFractionalPowerWeight L sigma n

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

theorem fractionalPowerEnergyTerm_nonneg
    (L sigma : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    0 ≤ fractionalPowerEnergyTerm L sigma a n := by
  exact mul_nonneg (fractionalPowerWeight_pos L sigma n).le (sq_nonneg _)

theorem reciprocalFractionalPowerWeight_nonneg (L sigma : ℝ) (n : ℕ) :
    0 ≤ reciprocalFractionalPowerWeight L sigma n := by
  dsimp [reciprocalFractionalPowerWeight]
  exact inv_nonneg.mpr (fractionalPowerWeight_pos L sigma n).le

theorem derivativeReciprocalFractionalPowerWeight_nonneg
    (L sigma : ℝ) (n : ℕ) :
    0 ≤ derivativeReciprocalFractionalPowerWeight L sigma n := by
  exact mul_nonneg (neumannEigenvalue_nonneg L n)
    (reciprocalFractionalPowerWeight_nonneg L sigma n)

theorem reciprocalFractionalPowerWeight_succ_le_pseries_majorant
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

theorem derivativeReciprocalFractionalPowerWeight_succ_le_pseries_majorant
    {L sigma : ℝ} (hL : 0 < L) (hsigma : 3 / 4 < sigma) (n : ℕ) :
    derivativeReciprocalFractionalPowerWeight L sigma (n + 1) ≤
      ((Real.pi / L) ^ 2) ^ (1 - 2 * sigma) *
        (1 / |(n : ℝ) + 1| ^ (4 * sigma - 2)) := by
  let c : ℝ := (Real.pi / L) ^ 2
  let m : ℕ := n + 1
  have hsigma_quarter : 1 / 4 < sigma := by linarith
  have hc_pos : 0 < c := by
    dsimp [c]
    exact sq_pos_of_pos (div_pos Real.pi_pos hL)
  have hm_pos_nat : 0 < m := Nat.succ_pos n
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm_pos_nat
  have hneumann :
      neumannEigenvalue L m = c * (m : ℝ) ^ 2 := by
    dsimp [neumannEigenvalue, c]
    ring
  have hrecip_le :=
    reciprocalFractionalPowerWeight_succ_le_pseries_majorant
      (L := L) (sigma := sigma) hL hsigma_quarter n
  have habs : |(n : ℝ) + 1| = (m : ℝ) := by
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    rw [abs_of_pos hpos]
    dsimp [m]
    norm_num
  calc
    derivativeReciprocalFractionalPowerWeight L sigma (n + 1)
        = (c * (m : ℝ) ^ 2) *
            reciprocalFractionalPowerWeight L sigma (n + 1) := by
          dsimp [derivativeReciprocalFractionalPowerWeight]
          rw [show n + 1 = m from rfl, hneumann]
    _ ≤ (c * (m : ℝ) ^ 2) *
          (c ^ (-(2 * sigma)) *
            (1 / |(n : ℝ) + 1| ^ (4 * sigma))) := by
          exact mul_le_mul_of_nonneg_left hrecip_le
            (mul_nonneg hc_pos.le (sq_nonneg (m : ℝ)))
    _ = c ^ (1 - 2 * sigma) *
          (1 / |(n : ℝ) + 1| ^ (4 * sigma - 2)) := by
          rw [habs]
          have hc_id :
              c * c ^ (-(2 * sigma)) = c ^ (1 - 2 * sigma) := by
            calc
              c * c ^ (-(2 * sigma))
                  = c ^ (1 : ℝ) * c ^ (-(2 * sigma)) := by
                    rw [Real.rpow_one]
              _ = c ^ ((1 : ℝ) + (-(2 * sigma))) := by
                    rw [← Real.rpow_add hc_pos 1 (-(2 * sigma))]
              _ = c ^ (1 - 2 * sigma) := by ring_nf
          have hm_id :
              (m : ℝ) ^ 2 * (1 / (m : ℝ) ^ (4 * sigma)) =
                1 / (m : ℝ) ^ (4 * sigma - 2) := by
            calc
              (m : ℝ) ^ 2 * (1 / (m : ℝ) ^ (4 * sigma))
                  = (m : ℝ) ^ (2 : ℝ) /
                      (m : ℝ) ^ (4 * sigma) := by
                    rw [Real.rpow_two]
                    ring
              _ = (m : ℝ) ^ ((2 : ℝ) - 4 * sigma) := by
                    rw [← Real.rpow_sub' hm_pos.le
                      (by ring_nf; linarith [hsigma])]
              _ = 1 / (m : ℝ) ^ (4 * sigma - 2) := by
                    have hexp :
                        (2 : ℝ) - 4 * sigma = -(4 * sigma - 2) := by
                      ring
                    rw [hexp, Real.rpow_neg hm_pos.le (4 * sigma - 2)]
                    rw [one_div]
          calc
            (c * (m : ℝ) ^ 2) *
                (c ^ (-(2 * sigma)) *
                  (1 / (m : ℝ) ^ (4 * sigma)))
                = (c * c ^ (-(2 * sigma))) *
                    ((m : ℝ) ^ 2 *
                      (1 / (m : ℝ) ^ (4 * sigma))) := by
                  ring
            _ = c ^ (1 - 2 * sigma) *
                (1 / (m : ℝ) ^ (4 * sigma - 2)) := by
                  rw [hc_id, hm_id]

/-- For `σ > 3/4`, the one-derivative reciprocal shifted spectral trace is
summable.  This is the coefficient-side core of the one-dimensional
`X^σ ↪ C¹` embedding. -/
theorem derivativeReciprocalFractionalPowerWeight_summable_of_sigma_gt_three_quarters
    {L sigma : ℝ} (hL : 0 < L) (hsigma : 3 / 4 < sigma) :
    Summable fun n : ℕ =>
      derivativeReciprocalFractionalPowerWeight L sigma n := by
  have hp : 1 < 4 * sigma - 2 := by nlinarith [hsigma]
  have hpseries :
      Summable fun n : ℕ => 1 / |(n : ℝ) + 1| ^ (4 * sigma - 2) :=
    (Real.summable_one_div_nat_add_rpow 1 (4 * sigma - 2)).mpr hp
  have hmajorant :
      Summable fun n : ℕ =>
        ((Real.pi / L) ^ 2) ^ (1 - 2 * sigma) *
          (1 / |(n : ℝ) + 1| ^ (4 * sigma - 2)) :=
    hpseries.mul_left (((Real.pi / L) ^ 2) ^ (1 - 2 * sigma))
  have htail :
      Summable fun n : ℕ =>
        derivativeReciprocalFractionalPowerWeight L sigma (n + 1) := by
    refine Summable.of_nonneg_of_le
      (fun n => derivativeReciprocalFractionalPowerWeight_nonneg L sigma (n + 1))
      (fun n =>
        derivativeReciprocalFractionalPowerWeight_succ_le_pseries_majorant
          (L := L) (sigma := sigma) hL hsigma n)
      hmajorant
  exact (summable_nat_add_iff (f := fun n : ℕ =>
    derivativeReciprocalFractionalPowerWeight L sigma n) 1).mp htail

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

theorem sqrt_fractionalPowerEnergy_mul_sqrt_reciprocal_eq_norm
    (L sigma : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    Real.sqrt (fractionalPowerEnergyTerm L sigma a n) *
        Real.sqrt (reciprocalFractionalPowerWeight L sigma n) = ‖a n‖ := by
  have hwpos : 0 < fractionalPowerWeight L sigma n :=
    fractionalPowerWeight_pos L sigma n
  have henergy_nonneg :
      0 ≤ fractionalPowerEnergyTerm L sigma a n :=
    fractionalPowerEnergyTerm_nonneg L sigma a n
  rw [← Real.sqrt_mul henergy_nonneg]
  have hprod :
      fractionalPowerEnergyTerm L sigma a n *
          reciprocalFractionalPowerWeight L sigma n = ‖a n‖ ^ 2 := by
    dsimp [fractionalPowerEnergyTerm, reciprocalFractionalPowerWeight]
    field_simp [hwpos.ne']
  rw [hprod, Real.sqrt_sq (norm_nonneg (a n))]

/-- Quantitative Cauchy-Schwarz form of the one-dimensional spectral
embedding: weighted `ℓ²` coefficients and the reciprocal trace control the
plain `ℓ¹` coefficient norm. -/
theorem tsum_coeff_norm_le_fractionalPowerEnergy_mul_trace
    {L sigma : ℝ} (a : ℕ → ℂ)
    (henergy : Summable fun n : ℕ => fractionalPowerEnergyTerm L sigma a n)
    (htrace : Summable fun n : ℕ => reciprocalFractionalPowerWeight L sigma n) :
    (∑' n : ℕ, ‖a n‖) ≤
      (∑' n : ℕ, fractionalPowerEnergyTerm L sigma a n) ^ (1 / (2 : ℝ)) *
        (∑' n : ℕ, reciprocalFractionalPowerWeight L sigma n) ^ (1 / (2 : ℝ)) := by
  let f : ℕ → ℝ := fun n =>
    Real.sqrt (fractionalPowerEnergyTerm L sigma a n)
  let g : ℕ → ℝ := fun n =>
    Real.sqrt (reciprocalFractionalPowerWeight L sigma n)
  have hf_nonneg : ∀ n, 0 ≤ f n := fun n => Real.sqrt_nonneg _
  have hg_nonneg : ∀ n, 0 ≤ g n := fun n => Real.sqrt_nonneg _
  have hf_sum : Summable fun n : ℕ => f n ^ (2 : ℝ) := by
    dsimp [f]
    convert henergy using 1
    ext n
    rw [Real.rpow_two,
      Real.sq_sqrt (fractionalPowerEnergyTerm_nonneg L sigma a n)]
  have hg_sum : Summable fun n : ℕ => g n ^ (2 : ℝ) := by
    dsimp [g]
    convert htrace using 1
    ext n
    rw [Real.rpow_two,
      Real.sq_sqrt (reciprocalFractionalPowerWeight_nonneg L sigma n)]
  have hholder := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg
    (p := (2 : ℝ)) (q := (2 : ℝ))
    Real.HolderConjugate.two_two hf_nonneg hg_nonneg hf_sum hg_sum
  dsimp [f, g] at hholder
  simpa [sqrt_fractionalPowerEnergy_mul_sqrt_reciprocal_eq_norm,
    Real.rpow_two, Real.sq_sqrt, fractionalPowerEnergyTerm_nonneg,
    reciprocalFractionalPowerWeight_nonneg] using hholder

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

theorem FractionalPowerSpace.tsum_coeff_norm_le_fractionalPowerEnergy_mul_trace
    {L sigma : ℝ} (u : FractionalPowerSpace L sigma)
    (htrace : Summable fun n : ℕ => reciprocalFractionalPowerWeight L sigma n) :
    (∑' n : ℕ, ‖(u : ℕ → ℂ) n‖) ≤
      (∑' n : ℕ,
          fractionalPowerEnergyTerm L sigma (u : ℕ → ℂ) n) ^ (1 / (2 : ℝ)) *
        (∑' n : ℕ, reciprocalFractionalPowerWeight L sigma n) ^
          (1 / (2 : ℝ)) :=
  _root_.ShenWork.PDE.FractionalPower.tsum_coeff_norm_le_fractionalPowerEnergy_mul_trace
    (L := L) (sigma := sigma) (u : ℕ → ℂ) u.property htrace

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

/-- Quantitative pointwise form of `X^σ ↪ C⁰`: the cosine-series representative
is controlled by the weighted coefficient energy and the reciprocal spectral
trace. -/
theorem FractionalPowerSpace.norm_cosineSeries_le_fractionalPowerEnergy_mul_trace
    {L sigma : ℝ} (u : FractionalPowerSpace L sigma)
    (htrace : Summable fun n : ℕ => reciprocalFractionalPowerWeight L sigma n)
    (x : ℝ) :
    ‖cosineSeries L (u : ℕ → ℂ) x‖ ≤
      (∑' n : ℕ,
          fractionalPowerEnergyTerm L sigma (u : ℕ → ℂ) n) ^ (1 / (2 : ℝ)) *
        (∑' n : ℕ, reciprocalFractionalPowerWeight L sigma n) ^
          (1 / (2 : ℝ)) :=
  (FractionalPowerSpace.norm_cosineSeries_le_tsum_coeff_norm u htrace x).trans
    (FractionalPowerSpace.tsum_coeff_norm_le_fractionalPowerEnergy_mul_trace
      u htrace)

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

/-- Quantitative pointwise `X^σ ↪ C⁰` estimate for `σ > 1/4`. -/
theorem FractionalPowerSpace.norm_cosineSeries_le_energy_trace_of_sigma_gt_quarter
    {L sigma : ℝ} (u : FractionalPowerSpace L sigma)
    (hL : 0 < L) (hsigma : 1 / 4 < sigma) (x : ℝ) :
    ‖cosineSeries L (u : ℕ → ℂ) x‖ ≤
      (∑' n : ℕ,
          fractionalPowerEnergyTerm L sigma (u : ℕ → ℂ) n) ^ (1 / (2 : ℝ)) *
        (∑' n : ℕ, reciprocalFractionalPowerWeight L sigma n) ^
          (1 / (2 : ℝ)) :=
  FractionalPowerSpace.norm_cosineSeries_le_fractionalPowerEnergy_mul_trace
    u
    (reciprocalFractionalPowerWeight_summable_of_sigma_gt_quarter
      (L := L) (sigma := sigma) hL hsigma)
    x

/-! ### Paper3 target bridge -/

/-- In the Paper3 H3.1 range `1/2 < σ`, the unit-interval coefficient
fractional-power embedding `X^σ -> C⁰` is unconditional. -/
theorem unitInterval_continuous_cosineSeries_of_h31_sigma
    {sigma : ℝ} (hsigma_low : 1 / 2 < sigma)
    (u : FractionalPowerSpace 1 sigma) :
    Continuous fun x : ℝ => cosineSeries 1 (u : ℕ → ℂ) x := by
  exact FractionalPowerSpace.continuous_cosineSeries_of_sigma_gt_quarter
    u (by norm_num) (by nlinarith [hsigma_low])

/-- Paper3 Theorem 2.2 target bridge with the coefficient fractional-power
embedding discharged for the unit-interval Neumann spectrum.

This theorem is intentionally honest about the remaining H3.1 frontier:
the coefficient result proves the standard direction `X^σ -> C⁰`. The existing
Paper3 sup-norm theorem still needs the opposite neighborhood bridge
`SupControlsXpSigmaDistance` (`sup -> X^σ_p`) plus small-data existence, so
those inputs remain explicit here. -/
theorem paper3_unitInterval_T22_with_fractionalPowerEmbedding
    {D : BoundedDomainData} {p : _root_.CM2Params}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (hC :
      Paper3ConstantsUsesCriticalSpectrum unitIntervalNeumannSpectrum p C)
    (hraw :
      SectorialLocalExponentialRaw D p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hcontrol :
      ∀ uStar, SupControlsXpSigmaDistance D N sigma pNorm uStar)
    (hexist :
      ∀ uStar, ∀ delta > 0, SmallDataGlobalExistence D p uStar delta)
    (hmexist :
      ∀ uStar, ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence D p uStar delta) :
    (∀ u : FractionalPowerSpace 1 sigma,
      Continuous fun x : ℝ => cosineSeries 1 (u : ℕ → ℂ) x) ∧
      Theorem_2_2 D p unitIntervalNeumannSpectrum N C := by
  refine ⟨?_, ?_⟩
  · intro u
    exact unitInterval_continuous_cosineSeries_of_h31_sigma hsigma_low u
  · exact
      Theorem_2_2_full_by_chi_sign_of_raw
        unitIntervalNeumannSpectrum_hasNeumannSpectrum hC hraw
        hsigma_low hsigma_high hpNorm hcontrol hexist hmexist

/-- Same Paper3 Theorem 2.2 bridge with the remaining neighborhood frontier
spelled in the primitive pointwise form `X^σ_p ≤ supNorm`. The coefficient
embedding is still discharged unconditionally from `1/2 < σ`; the primitive
reverse comparison is not a consequence of `X^σ -> C⁰` and remains explicit. -/
theorem paper3_unitInterval_T22_with_fractionalPowerEmbedding_of_xp_le_sup
    {D : BoundedDomainData} {p : _root_.CM2Params}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (hC :
      Paper3ConstantsUsesCriticalSpectrum unitIntervalNeumannSpectrum p C)
    (hraw :
      SectorialLocalExponentialRaw D p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hxp :
      ∀ uStar, ∀ u₀ : D.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀ (fun _ => uStar) ≤
          D.supNorm (fun x => u₀ x - uStar))
    (hexist :
      ∀ uStar, ∀ delta > 0, SmallDataGlobalExistence D p uStar delta)
    (hmexist :
      ∀ uStar, ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence D p uStar delta) :
    (∀ u : FractionalPowerSpace 1 sigma,
      Continuous fun x : ℝ => cosineSeries 1 (u : ℕ → ℂ) x) ∧
      Theorem_2_2 D p unitIntervalNeumannSpectrum N C :=
  paper3_unitInterval_T22_with_fractionalPowerEmbedding
    hC hraw hsigma_low hsigma_high hpNorm
    (fun uStar =>
      SupControlsXpSigmaDistance.of_xpSigma_le_supNorm
        (D := D) (N := N) (sigma := sigma) (pNorm := pNorm)
        (uStar := uStar) (hxp uStar))
    hexist hmexist

end ShenWork.PDE.FractionalPower
