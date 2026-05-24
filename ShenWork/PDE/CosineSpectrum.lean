import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic
import ShenWork.PDE.IntervalDomain
import ShenWork.Paper3.Statements

open MeasureTheory

noncomputable section

namespace ShenWork.CosineSpectrum

open _root_.ShenWork.Paper3

/-- The cosine modes on the unit interval, indexed as Neumann eigenfunctions. -/
def cosineBasis : ℕ → (Subtype (Set.Icc (0 : ℝ) 1)) → ℝ :=
  fun n x => Real.cos ((n : ℝ) * Real.pi * x.1)

/-- The same cosine mode as a function on the ambient real line. -/
def cosineMode (n : ℕ) (x : ℝ) : ℝ :=
  Real.cos ((n : ℝ) * Real.pi * x)

/-- The eigenvalue attached to the `n`-th Neumann cosine mode. -/
def cosineEigenvalue (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2

theorem cosineEigenvalue_eq_frequency_sq (n : ℕ) :
    cosineEigenvalue n = ((n : ℝ) * Real.pi) ^ 2 := by
  simp [cosineEigenvalue]
  ring

theorem cosineBasis_eq_cosineMode (n : ℕ)
    (x : Subtype (Set.Icc (0 : ℝ) 1)) :
    cosineBasis n x = cosineMode n x.1 := by
  rfl

/-- The ambient lift of a cosine basis vector, using the interval-domain lift. -/
def cosineBasisLift (n : ℕ) : ℝ → ℝ :=
  _root_.ShenWork.IntervalDomain.intervalDomainLift (cosineBasis n)

theorem cosineBasisLift_eq_cosineMode_of_mem {n : ℕ} {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    cosineBasisLift n x = cosineMode n x := by
  simp [cosineBasisLift, _root_.ShenWork.IntervalDomain.intervalDomainLift,
    cosineBasis, cosineMode, hx]

private theorem hasDerivAt_const_mul_id (a x : ℝ) :
    HasDerivAt (fun y : ℝ => a * y) a x := by
  simpa using (hasDerivAt_id x).const_mul a

private theorem intervalIntegral_cos_mul_eq
    {a : ℝ} (ha : a ≠ 0) :
    ∫ x in (0 : ℝ)..1, Real.cos (a * x) = Real.sin a / a := by
  let F : ℝ → ℝ := fun x => Real.sin (a * x) / a
  have hderiv :
      ∀ x ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt F (Real.cos (a * x)) x := by
    intro x _hx
    have hsin :
        HasDerivAt (fun y : ℝ => Real.sin (a * y))
          (Real.cos (a * x) * a) x :=
      (Real.hasDerivAt_sin (a * x)).comp x (hasDerivAt_const_mul_id a x)
    convert hsin.div_const a using 1
    field_simp [ha]
  have hint :
      IntervalIntegrable (fun x : ℝ => Real.cos (a * x))
        volume (0 : ℝ) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := 1) hderiv hint
  simpa [F, ha] using hftc

private theorem intervalIntegral_cos_int_mul_pi_eq_zero
    {k : ℤ} (hk : k ≠ 0) :
    ∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) = 0 := by
  have hk_real : (k : ℝ) ≠ 0 := by
    exact_mod_cast hk
  have hfreq : (k : ℝ) * Real.pi ≠ 0 :=
    mul_ne_zero hk_real Real.pi_ne_zero
  have h :=
    intervalIntegral_cos_mul_eq (a := (k : ℝ) * Real.pi) hfreq
  have hsin : Real.sin ((k : ℝ) * Real.pi) = 0 := by
    simp
  simpa [hsin, mul_assoc] using h

private theorem cosine_product_eq_half_sum (m n : ℕ) (x : ℝ) :
    cosineMode m x * cosineMode n x =
      (1 / 2 : ℝ) *
        (Real.cos ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * Real.pi * x) +
          Real.cos ((((m : ℤ) + (n : ℤ) : ℤ) : ℝ) * Real.pi * x)) := by
  have h :=
    Real.two_mul_cos_mul_cos
      ((m : ℝ) * Real.pi * x) ((n : ℝ) * Real.pi * x)
  have hsub :
      (m : ℝ) * Real.pi * x - (n : ℝ) * Real.pi * x =
        (((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * Real.pi * x := by
    have hcast :
        (((m : ℤ) - (n : ℤ) : ℤ) : ℝ) = (m : ℝ) - (n : ℝ) := by
      norm_num
    rw [hcast]
    ring
  have hadd :
      (m : ℝ) * Real.pi * x + (n : ℝ) * Real.pi * x =
        (((m : ℤ) + (n : ℤ) : ℤ) : ℝ) * Real.pi * x := by
    have hcast :
        (((m : ℤ) + (n : ℤ) : ℤ) : ℝ) = (m : ℝ) + (n : ℝ) := by
      norm_num
    rw [hcast]
    ring
  rw [hsub, hadd] at h
  unfold cosineMode
  calc
    Real.cos ((m : ℝ) * Real.pi * x) *
        Real.cos ((n : ℝ) * Real.pi * x)
        = (1 / 2 : ℝ) *
          (2 * Real.cos ((m : ℝ) * Real.pi * x) *
            Real.cos ((n : ℝ) * Real.pi * x)) := by
          ring
    _ = (1 / 2 : ℝ) *
        (Real.cos ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * Real.pi * x) +
          Real.cos ((((m : ℤ) + (n : ℤ) : ℤ) : ℝ) * Real.pi * x)) := by
          rw [h]

theorem cosineMode_orthogonal {m n : ℕ} (hmn : m ≠ n) :
    ∫ x in (0 : ℝ)..1, cosineMode m x * cosineMode n x = 0 := by
  have hdiff_ne : ((m : ℤ) - (n : ℤ) : ℤ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hmn)
  have hsum_ne : ((m : ℤ) + (n : ℤ) : ℤ) ≠ 0 := by
    have hsum_nat : m + n ≠ 0 := by
      intro hzero
      have hm0 : m = 0 := Nat.eq_zero_of_add_eq_zero_right hzero
      have hn0 : n = 0 := Nat.eq_zero_of_add_eq_zero_left hzero
      exact hmn (hm0.trans hn0.symm)
    exact_mod_cast hsum_nat
  have hdiff_int :
      IntervalIntegrable
        (fun x : ℝ =>
          Real.cos ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * Real.pi * x))
        volume (0 : ℝ) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hsum_int :
      IntervalIntegrable
        (fun x : ℝ =>
          Real.cos ((((m : ℤ) + (n : ℤ) : ℤ) : ℝ) * Real.pi * x))
        volume (0 : ℝ) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  calc
    ∫ x in (0 : ℝ)..1, cosineMode m x * cosineMode n x
        = ∫ x in (0 : ℝ)..1,
            (1 / 2 : ℝ) *
              (Real.cos ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * Real.pi * x) +
                Real.cos ((((m : ℤ) + (n : ℤ) : ℤ) : ℝ) * Real.pi * x)) := by
          apply intervalIntegral.integral_congr
          intro x _hx
          exact cosine_product_eq_half_sum m n x
    _ = (1 / 2 : ℝ) *
          ((∫ x in (0 : ℝ)..1,
              Real.cos ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * Real.pi * x)) +
            (∫ x in (0 : ℝ)..1,
              Real.cos ((((m : ℤ) + (n : ℤ) : ℤ) : ℝ) * Real.pi * x))) := by
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_add hdiff_int hsum_int]
    _ = 0 := by
          rw [intervalIntegral_cos_int_mul_pi_eq_zero hdiff_ne,
            intervalIntegral_cos_int_mul_pi_eq_zero hsum_ne]
          ring

/-- Orthogonality of distinct cosine basis vectors on `[0,1]`, using interval integrals. -/
theorem ortho_basis {m n : ℕ} (hmn : m ≠ n) :
    ∫ x in (0 : ℝ)..1, cosineBasisLift m x * cosineBasisLift n x = 0 := by
  calc
    ∫ x in (0 : ℝ)..1, cosineBasisLift m x * cosineBasisLift n x
        = ∫ x in (0 : ℝ)..1, cosineMode m x * cosineMode n x := by
          apply intervalIntegral.integral_congr
          intro x hx
          have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
            simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hx
          have hm : cosineBasisLift m x = cosineMode m x :=
            cosineBasisLift_eq_cosineMode_of_mem (n := m) hxIcc
          have hn : cosineBasisLift n x = cosineMode n x :=
            cosineBasisLift_eq_cosineMode_of_mem (n := n) hxIcc
          simp [hm, hn]
    _ = 0 := cosineMode_orthogonal hmn

theorem cosineMode_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (cosineMode n)
      (-((n : ℝ) * Real.pi) *
        Real.sin ((n : ℝ) * Real.pi * x)) x := by
  have h :=
    (Real.hasDerivAt_cos ((n : ℝ) * Real.pi * x)).comp x
      (hasDerivAt_const_mul_id ((n : ℝ) * Real.pi) x)
  unfold cosineMode
  convert h using 1
  ring

theorem cosineMode_deriv (n : ℕ) (x : ℝ) :
    deriv (cosineMode n) x =
      -((n : ℝ) * Real.pi) *
        Real.sin ((n : ℝ) * Real.pi * x) :=
  (cosineMode_hasDerivAt n x).deriv

private theorem sine_frequency_hasDerivAt (a x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin (a * y))
      (a * Real.cos (a * x)) x := by
  have h :=
    (Real.hasDerivAt_sin (a * x)).comp x
      (hasDerivAt_const_mul_id a x)
  convert h using 1
  ring

theorem cosineMode_second_deriv (n : ℕ) (x : ℝ) :
    deriv (fun y : ℝ => deriv (cosineMode n) y) x =
      -(((n : ℝ) * Real.pi) ^ 2 * cosineMode n x) := by
  let a : ℝ := (n : ℝ) * Real.pi
  have hfirst :
      (fun y : ℝ => deriv (cosineMode n) y) =
        fun y : ℝ => -a * Real.sin (a * y) := by
    funext y
    simp [cosineMode_deriv, a]
  rw [hfirst]
  have h :=
    (sine_frequency_hasDerivAt a x).const_mul (-a)
  calc
    deriv (fun y : ℝ => -a * Real.sin (a * y)) x =
        -a * (a * Real.cos (a * x)) :=
      h.deriv
    _ = -(((n : ℝ) * Real.pi) ^ 2 * cosineMode n x) := by
      simp [cosineMode, a]
      ring

/-- The one-dimensional Neumann cosine eigenfunction equation. -/
theorem cosineEigenfunction (n : ℕ) (x : ℝ) :
    -deriv (fun y : ℝ => deriv (cosineMode n) y) x =
      ((n : ℝ) * Real.pi) ^ 2 * cosineMode n x := by
  rw [cosineMode_second_deriv]
  ring

theorem sine_nat_pi_left_endpoint (n : ℕ) :
    Real.sin ((n : ℝ) * Real.pi * (0 : ℝ)) = 0 := by
  simp

theorem sine_nat_pi_right_endpoint (n : ℕ) :
    Real.sin ((n : ℝ) * Real.pi * (1 : ℝ)) = 0 := by
  simp

theorem cosineMode_neumann_left (n : ℕ) :
    deriv (cosineMode n) 0 = 0 := by
  rw [cosineMode_deriv]
  simp

theorem cosineMode_neumann_right (n : ℕ) :
    deriv (cosineMode n) 1 = 0 := by
  rw [cosineMode_deriv]
  simp

/-- Paper3 spectral data generated by the unit-interval cosine modes. -/
def paper3CosineSpectralData : _root_.ShenWork.Paper3.SpectralData where
  eigenvalue := cosineEigenvalue
  firstNonzero := Real.pi ^ 2

theorem paper3CosineSpectralData_eq_unitInterval :
    paper3CosineSpectralData =
      _root_.ShenWork.Paper3.unitIntervalNeumannSpectrum := by
  rfl

/-- The cosine spectral data satisfies the Paper3 Neumann-spectrum API. -/
theorem paper3Cosine_hasNeumannSpectrum :
    _root_.ShenWork.Paper3.HasNeumannSpectrum paper3CosineSpectralData := by
  simpa [paper3CosineSpectralData_eq_unitInterval] using
    _root_.ShenWork.Paper3.unitIntervalNeumannSpectrum_hasNeumannSpectrum

theorem cosineEigenfunction_spectralData (n : ℕ) (x : ℝ) :
    -deriv (fun y : ℝ => deriv (cosineMode n) y) x =
      paper3CosineSpectralData.eigenvalue n * cosineMode n x := by
  rw [cosineEigenfunction]
  change ((n : ℝ) * Real.pi) ^ 2 * cosineMode n x =
    cosineEigenvalue n * cosineMode n x
  rw [cosineEigenvalue_eq_frequency_sq]

/-- Neumann spectrum package attached to `IntervalDomain.intervalDomain`. -/
abbrev intervalDomainNeumannSpectrum : _root_.ShenWork.Paper3.SpectralData :=
  paper3CosineSpectralData

/-- Domain-indexed carrier for a Paper3 Neumann spectrum.  The current Paper3
API keeps spectral positivity separate from the bounded-domain structure, so
this class records the attachment point without changing that API. -/
class DomainNeumannSpectrum (D : _root_.ShenWork.Paper2.BoundedDomainData) where
  spectralData : _root_.ShenWork.Paper3.SpectralData
  hasNeumannSpectrum : _root_.ShenWork.Paper3.HasNeumannSpectrum spectralData

/-- The concrete unit-interval bounded domain uses the cosine spectral data. -/
instance intervalDomain_domainNeumannSpectrum :
    DomainNeumannSpectrum _root_.ShenWork.IntervalDomain.intervalDomain where
  spectralData := intervalDomainNeumannSpectrum
  hasNeumannSpectrum := paper3Cosine_hasNeumannSpectrum

/-- The unit interval domain carries the cosine Neumann spectrum. -/
theorem intervalDomain_hasNeumannSpectrum :
    _root_.ShenWork.Paper3.HasNeumannSpectrum
      (DomainNeumannSpectrum.spectralData
        (D := _root_.ShenWork.IntervalDomain.intervalDomain)) :=
  DomainNeumannSpectrum.hasNeumannSpectrum
    (D := _root_.ShenWork.IntervalDomain.intervalDomain)

/-! ### Paper3 cosine spectral closures -/

lemma paper3Cosine_positiveEquilibrium_linearlyStable_of_chi_nonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyStable paper3CosineSpectralData p eq.1 eq.2 := by
  simpa [paper3CosineSpectralData_eq_unitInterval] using
    unitInterval_positiveEquilibrium_linearlyStable_of_chi_nonpos p hχ ha hb

lemma paper3Cosine_positiveEquilibrium_linearlyStable_of_chi_lt_critical
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity paper3CosineSpectralData p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyStable paper3CosineSpectralData p eq.1 eq.2 := by
  simpa [paper3CosineSpectralData_eq_unitInterval] using
    unitInterval_positiveEquilibrium_linearlyStable_of_chi_lt_critical
      p ha hb hχ

lemma paper3Cosine_positiveEquilibrium_linearlyUnstable_of_critical_lt_chi
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      paperCriticalSensitivity paper3CosineSpectralData p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2 <
        p.χ₀) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyUnstable paper3CosineSpectralData p eq.1 eq.2 := by
  simpa [paper3CosineSpectralData_eq_unitInterval] using
    unitInterval_positiveEquilibrium_linearlyUnstable_of_critical_lt_chi
      p ha hb hχ

lemma paper3Cosine_positiveEquilibrium_linearlyUnstable_of_first_mode_formula_lt_chi
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      sigmaCriticalChiPaperFormula p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2
          (Real.pi ^ 2) <
        p.χ₀) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyUnstable paper3CosineSpectralData p eq.1 eq.2 := by
  simpa [paper3CosineSpectralData_eq_unitInterval] using
    unitInterval_positiveEquilibrium_linearlyUnstable_of_first_mode_formula_lt_chi
      p ha hb hχ

lemma paper3Cosine_minimalEquilibrium_linearlyStable_of_chi_nonpos
    (p : CM2Params) {uStar : ℝ}
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (huStar : 0 < uStar) :
    let eq := minimalEquilibrium p uStar
    LinearlyStable paper3CosineSpectralData p eq.1 eq.2 := by
  simpa [paper3CosineSpectralData_eq_unitInterval] using
    unitInterval_minimalEquilibrium_linearlyStable_of_chi_nonpos
      p hχ ha huStar

lemma paper3Cosine_minimalEquilibrium_linearlyStable_of_chi_lt_critical
    (p : CM2Params) {uStar : ℝ} (huStar : 0 < uStar)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity paper3CosineSpectralData p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2) :
    let eq := minimalEquilibrium p uStar
    LinearlyStable paper3CosineSpectralData p eq.1 eq.2 := by
  simpa [paper3CosineSpectralData_eq_unitInterval] using
    unitInterval_minimalEquilibrium_linearlyStable_of_chi_lt_critical
      p huStar hχ

lemma paper3Cosine_minimalEquilibrium_linearlyUnstable_of_critical_lt_chi
    (p : CM2Params) {uStar : ℝ} (huStar : 0 < uStar)
    (hχ :
      paperCriticalSensitivity paper3CosineSpectralData p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 <
        p.χ₀) :
    let eq := minimalEquilibrium p uStar
    LinearlyUnstable paper3CosineSpectralData p eq.1 eq.2 := by
  simpa [paper3CosineSpectralData_eq_unitInterval] using
    unitInterval_minimalEquilibrium_linearlyUnstable_of_critical_lt_chi
      p huStar hχ

lemma paper3Cosine_minimalEquilibrium_linearlyUnstable_of_first_mode_formula_lt_chi
    (p : CM2Params) {uStar : ℝ} (huStar : 0 < uStar)
    (hχ :
      sigmaCriticalChiPaperFormula p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2
          (Real.pi ^ 2) <
        p.χ₀) :
    let eq := minimalEquilibrium p uStar
    LinearlyUnstable paper3CosineSpectralData p eq.1 eq.2 := by
  simpa [paper3CosineSpectralData_eq_unitInterval] using
    unitInterval_minimalEquilibrium_linearlyUnstable_of_first_mode_formula_lt_chi
      p huStar hχ

lemma paper3Cosine_Theorem_2_2_linear_stability_chi_nonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) :
    (∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      LinearlyStable paper3CosineSpectralData p eq.1 eq.2) ∧
    (p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        LinearlyStable paper3CosineSpectralData p eq.1 eq.2) := by
  simpa [paper3CosineSpectralData_eq_unitInterval] using
    Theorem_2_2_linear_stability_chi_nonpos_unitInterval p hχ

lemma paper3Cosine_Theorem_2_2_linear_threshold
    (p : CM2Params) :
    (∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      (p.χ₀ < paperCriticalSensitivity paper3CosineSpectralData p eq.1 eq.2 →
        LinearlyStable paper3CosineSpectralData p eq.1 eq.2) ∧
      (paperCriticalSensitivity paper3CosineSpectralData p eq.1 eq.2 < p.χ₀ →
        LinearlyUnstable paper3CosineSpectralData p eq.1 eq.2)) ∧
    (p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        (p.χ₀ <
            paperCriticalSensitivity paper3CosineSpectralData p eq.1 eq.2 →
          LinearlyStable paper3CosineSpectralData p eq.1 eq.2) ∧
        (paperCriticalSensitivity paper3CosineSpectralData p eq.1 eq.2 <
            p.χ₀ →
          LinearlyUnstable paper3CosineSpectralData p eq.1 eq.2)) := by
  simpa [paper3CosineSpectralData_eq_unitInterval] using
    Theorem_2_2_linear_threshold_unitInterval p

lemma paper3Cosine_Theorem_2_2_linear_mode_one_instability
    (p : CM2Params) :
    (∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      sigmaCriticalChiPaperFormula p eq.1 eq.2 (Real.pi ^ 2) < p.χ₀ →
        LinearlyUnstable paper3CosineSpectralData p eq.1 eq.2) ∧
    (p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        sigmaCriticalChiPaperFormula p eq.1 eq.2 (Real.pi ^ 2) < p.χ₀ →
          LinearlyUnstable paper3CosineSpectralData p eq.1 eq.2) := by
  simpa [paper3CosineSpectralData_eq_unitInterval] using
    Theorem_2_2_linear_mode_one_instability_unitInterval p

abbrev Paper3ConstantsUsesCosineCriticalSpectrum
    (p : CM2Params) {D : BoundedDomainData} (C : Paper3Constants D p) :
    Prop :=
  Paper3ConstantsUsesCriticalSpectrum paper3CosineSpectralData p C

lemma paper3Cosine_chiCritical_positiveEquilibrium
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    (ha : 0 < p.a) (hb : 0 < p.b) :
    C.chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1 =
      paperCriticalSensitivity paper3CosineSpectralData p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  hC.chiCritical_positiveEquilibrium ha hb

lemma paper3Cosine_chiCritical_minimalEquilibrium
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {uStar : ℝ}
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    (huStar : 0 < uStar) :
    C.chiCritical uStar =
      paperCriticalSensitivity paper3CosineSpectralData p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 :=
  hC.chiCritical_minimalEquilibrium huStar

lemma paper3Cosine_chiCritical_nonneg
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    {uStar : ℝ} (huStar : 0 < uStar) :
    0 ≤ C.chiCritical uStar :=
  hC.chiCritical_nonneg paper3Cosine_hasNeumannSpectrum huStar

lemma paper3Cosine_chiCritical_pos
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    {uStar : ℝ} (huStar : 0 < uStar) :
    0 < C.chiCritical uStar :=
  hC.chiCritical_pos paper3Cosine_hasNeumannSpectrum huStar

lemma paper3Cosine_chiCritical_positiveEquilibrium_nonneg
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    (ha : 0 < p.a) (hb : 0 < p.b) :
    0 ≤ C.chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1 :=
  hC.chiCritical_positiveEquilibrium_nonneg
    paper3Cosine_hasNeumannSpectrum ha hb

lemma paper3Cosine_chiCritical_positiveEquilibrium_pos
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    (ha : 0 < p.a) (hb : 0 < p.b) :
    0 < C.chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1 :=
  hC.chiCritical_positiveEquilibrium_pos
    paper3Cosine_hasNeumannSpectrum ha hb

lemma paper3Cosine_chiCritical_minimalEquilibrium_nonneg
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {uStar : ℝ}
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    (huStar : 0 < uStar) :
    0 ≤ C.chiCritical uStar :=
  hC.chiCritical_minimalEquilibrium_nonneg
    paper3Cosine_hasNeumannSpectrum huStar

lemma paper3Cosine_chiCritical_minimalEquilibrium_pos
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {uStar : ℝ}
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    (huStar : 0 < uStar) :
    0 < C.chiCritical uStar :=
  hC.chiCritical_minimalEquilibrium_pos
    paper3Cosine_hasNeumannSpectrum huStar

lemma paper3Cosine_positiveEquilibrium_linearlyStable_of_chiCritical
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ : p.χ₀ < C.chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1) :
    LinearlyStable paper3CosineSpectralData p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  hC.positiveEquilibrium_linearlyStable
    paper3Cosine_hasNeumannSpectrum ha hb hχ

lemma paper3Cosine_positiveEquilibrium_linearlyUnstable_of_chiCritical
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ : C.chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1 < p.χ₀) :
    LinearlyUnstable paper3CosineSpectralData p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  hC.positiveEquilibrium_linearlyUnstable
    paper3Cosine_hasNeumannSpectrum ha hb hχ

lemma paper3Cosine_minimalEquilibrium_linearlyStable_of_chiCritical
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {uStar : ℝ}
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    (huStar : 0 < uStar) (hχ : p.χ₀ < C.chiCritical uStar) :
    LinearlyStable paper3CosineSpectralData p
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  hC.minimalEquilibrium_linearlyStable
    paper3Cosine_hasNeumannSpectrum huStar hχ

lemma paper3Cosine_minimalEquilibrium_linearlyUnstable_of_chiCritical
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {uStar : ℝ}
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    (huStar : 0 < uStar) (hχ : C.chiCritical uStar < p.χ₀) :
    LinearlyUnstable paper3CosineSpectralData p
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  hC.minimalEquilibrium_linearlyUnstable
    paper3Cosine_hasNeumannSpectrum huStar hχ

lemma paper3Cosine_chi_pos_of_chiCritical_lt
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hχ : C.chiCritical uStar < p.χ₀) :
    0 < p.χ₀ :=
  hC.chi_pos_of_chiCritical_lt paper3Cosine_hasNeumannSpectrum huStar hχ

lemma paper3Cosine_chi_pos_of_positiveEquilibrium_chiCritical_lt
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ : C.chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1 < p.χ₀) :
    0 < p.χ₀ :=
  hC.chi_pos_of_positiveEquilibrium_chiCritical_lt
    paper3Cosine_hasNeumannSpectrum ha hb hχ

lemma paper3Cosine_Corollary_5_1_nonminimal_exponential_formula_of_raw
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    (hraw :
      ConvergenceToExponentialNonminimalRaw D p N.c1Distance
        (fun uStar =>
          paperCriticalSensitivity paper3CosineSpectralData p uStar
            (p.ν / p.μ * uStar ^ p.γ)))
    (hm : 1 ≤ p.m) (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity paper3CosineSpectralData p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hconv : UniformConvergesInSup D u (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ExponentialC1Convergence D N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  simpa [paper3CosineSpectralData_eq_unitInterval] using
    Corollary_5_1_nonminimal_exponential_formula_unitInterval_of_raw
      (D := D) (p := p) (N := N) hraw hm ha hb hχ huv hconv

lemma paper3Cosine_Corollary_5_1_minimal_exponential_formula_of_raw
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    (hraw :
      ConvergenceToExponentialMinimalRaw D p N.c1Distance
        (fun uStar =>
          paperCriticalSensitivity paper3CosineSpectralData p uStar
            (p.ν / p.μ * uStar ^ p.γ)))
    (hm : 1 ≤ p.m) (ha : p.a = 0) (hb : p.b = 0)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity paper3CosineSpectralData p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hmass : HasInitialMass D u uStar)
    (hconv : UniformConvergesInSup D u (minimalEquilibrium p uStar).1) :
    ExponentialC1Convergence D N u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 := by
  simpa [paper3CosineSpectralData_eq_unitInterval] using
    Corollary_5_1_minimal_exponential_formula_unitInterval_of_raw
      (D := D) (p := p) (N := N) hraw hm ha hb huStar hχ
      huv hmass hconv

end ShenWork.CosineSpectrum

end
