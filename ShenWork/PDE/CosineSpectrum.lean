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

abbrev paper3Cosine_Theorem_2_2_linear_critical_spectrum
    (D : BoundedDomainData) (p : CM2Params) (C : Paper3Constants D p)
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C) :=
  Theorem_2_2_linear_critical_spectrum_branch_direct
    D paper3CosineSpectralData p C paper3Cosine_hasNeumannSpectrum hC

abbrev paper3Cosine_Theorem_2_2_xpSigma_local_exponential_of_Lemma_A_1
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (C : Paper3Constants D p)
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    (hA1 : Lemma_A_1 D p paper3CosineSpectralData N) :=
  Theorem_2_2_xpSigma_local_exponential_branch_of_Lemma_A_1
    D paper3CosineSpectralData p N C paper3Cosine_hasNeumannSpectrum hC hA1

abbrev paper3Cosine_Theorem_2_2_xpSigma_local_exponential_of_raw
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (C : Paper3Constants D p)
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    (hraw :
      SectorialLocalExponentialRaw D p paper3CosineSpectralData
        N.c1Distance N.xpSigmaDistance) :=
  Theorem_2_2_xpSigma_local_exponential_branch_of_raw
    D paper3CosineSpectralData p N C paper3Cosine_hasNeumannSpectrum hC hraw

abbrev paper3Cosine_LinearStabilityInstabilityRaw_of_sectorial_paperCriticalSensitivity
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p paper3CosineSpectralData
        N.c1Distance N.xpSigmaDistance) :=
  fun {sigma pNorm : ℝ} =>
    LinearStabilityInstabilityRaw_of_sectorial_paperCriticalSensitivity
      (D := D) (S := paper3CosineSpectralData) (p := p) (N := N)
      (sigma := sigma) (pNorm := pNorm)
      paper3Cosine_hasNeumannSpectrum hraw

abbrev paper3Cosine_LinearStabilityInstabilityRaw_of_sectorial_critical_spectrum
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (C : Paper3Constants D p)
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    (hraw :
      SectorialLocalExponentialRaw D p paper3CosineSpectralData
        N.c1Distance N.xpSigmaDistance) :=
  fun {sigma pNorm : ℝ} =>
    LinearStabilityInstabilityRaw_of_sectorial_critical_spectrum
      (D := D) (S := paper3CosineSpectralData) (p := p) (N := N)
      (C := C) (sigma := sigma) (pNorm := pNorm)
      paper3Cosine_hasNeumannSpectrum hC hraw

abbrev paper3Cosine_LinearInstabilityNonminimalRaw_paperCriticalSensitivity
    (p : CM2Params) :=
  LinearInstabilityNonminimalRaw_paperCriticalSensitivity
    paper3CosineSpectralData p paper3Cosine_hasNeumannSpectrum

abbrev paper3Cosine_LinearInstabilityMinimalRaw_paperCriticalSensitivity
    (p : CM2Params) :=
  LinearInstabilityMinimalRaw_paperCriticalSensitivity
    paper3CosineSpectralData p paper3Cosine_hasNeumannSpectrum

lemma paper3Cosine_Lemma_A_7_of_firstNonzero_lower_and_formula_fields
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (M0 : ℝ)
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    (hstrong1 :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        C.chiStrong1 eq.1 = chiStrong1Formula p eq.1 eq.2)
    (hstrong2 :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        C.chiStrong2 eq.1 = chiStrong2Formula p eq.1)
    (hstrong3 :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        C.chiStrong3 eq.1 = chiStrong3Formula p M0 eq.1 eq.2)
    (hstrong4 :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        C.chiStrong4 eq.1 = chiStrong4Formula p M0 eq.1)
    (hfirst :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        max
            (max (chiStrong1Formula p eq.1 eq.2)
              (chiStrong2Formula p eq.1))
            (max (chiStrong3Formula p M0 eq.1 eq.2)
              (chiStrong4Formula p M0 eq.1)) ≤
          ((1 + eq.2) ^ p.β /
              (p.ν * p.γ * eq.1 ^ (p.m + p.γ - 1))) *
            (p.μ + Real.pi ^ 2)) :
    Lemma_A_7 D p C := by
  refine Lemma_A_7_of_firstNonzero_lower_and_formula_fields
    paper3CosineSpectralData M0 paper3Cosine_hasNeumannSpectrum hC
    hstrong1 hstrong2 hstrong3 hstrong4 ?_
  intro ha hb
  simpa [paper3CosineSpectralData] using hfirst ha hb

lemma paper3Cosine_Lemma_A_8_of_firstNonzero_lower_and_formula_fields
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (uBar vLower : ℝ)
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    (hminimal1 :
      ∀ uStar > 0,
        C.chiMinimal1 uStar =
          chiMinimal1Formula p 1 uStar uBar vLower)
    (hminimal2 :
      ∀ uStar > 0,
        C.chiMinimal2 uStar = chiMinimal2Formula p uBar vLower)
    (hfirst :
      ∀ uStar > 0,
        _root_.ShenWork.Paper2.chiBeta p ≤
          ((1 + (minimalEquilibrium p uStar).2) ^ p.β /
              (p.ν * p.γ *
                (minimalEquilibrium p uStar).1 ^ (p.m + p.γ - 1))) *
            (p.μ + Real.pi ^ 2)) :
    Lemma_A_8 D p C := by
  refine Lemma_A_8_of_firstNonzero_lower_and_formula_fields
    paper3CosineSpectralData uBar vLower paper3Cosine_hasNeumannSpectrum hC
    hminimal1 hminimal2 ?_
  intro uStar huStar
  simpa [paper3CosineSpectralData] using hfirst uStar huStar

abbrev paper3Cosine_Lemma_A_7_nonminimal_condition_linearlyStable_of_critical_spectrum
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Lemma_A_7 D p C)
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C) :=
  h.nonminimal_condition_linearlyStable_of_critical_spectrum
    paper3Cosine_hasNeumannSpectrum hC

abbrev paper3Cosine_Lemma_A_8_minimal_condition_linearlyStable_of_critical_spectrum
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Lemma_A_8 D p C)
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C) :=
  h.minimal_condition_linearlyStable_of_critical_spectrum
    paper3Cosine_hasNeumannSpectrum hC

abbrev paper3Cosine_Lemma_A_7_chiStrong1_linearlyStable_of_critical_spectrum
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Lemma_A_7 D p C)
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C) :=
  h.chiStrong1_linearlyStable_of_critical_spectrum
    paper3Cosine_hasNeumannSpectrum hC

abbrev paper3Cosine_Lemma_A_7_chiStrong2_linearlyStable_of_critical_spectrum
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Lemma_A_7 D p C)
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C) :=
  h.chiStrong2_linearlyStable_of_critical_spectrum
    paper3Cosine_hasNeumannSpectrum hC

abbrev paper3Cosine_Lemma_A_7_chiStrong3_linearlyStable_of_critical_spectrum
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Lemma_A_7 D p C)
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C) :=
  h.chiStrong3_linearlyStable_of_critical_spectrum
    paper3Cosine_hasNeumannSpectrum hC

abbrev paper3Cosine_Lemma_A_7_chiStrong4_linearlyStable_of_critical_spectrum
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Lemma_A_7 D p C)
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C) :=
  h.chiStrong4_linearlyStable_of_critical_spectrum
    paper3Cosine_hasNeumannSpectrum hC

abbrev paper3Cosine_Lemma_A_8_chiMinimal1_linearlyStable_of_critical_spectrum
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Lemma_A_8 D p C)
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C) :=
  h.chiMinimal1_linearlyStable_of_critical_spectrum
    paper3Cosine_hasNeumannSpectrum hC

abbrev paper3Cosine_Lemma_A_8_chiMinimal2_linearlyStable_of_critical_spectrum
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Lemma_A_8 D p C)
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C) :=
  h.chiMinimal2_linearlyStable_of_critical_spectrum
    paper3Cosine_hasNeumannSpectrum hC

abbrev paper3Cosine_Theorem_2_4_linear_stability_of_Lemma_A_7
    (D : BoundedDomainData) (p : CM2Params) (C : Paper3Constants D p)
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    (hA7 : Lemma_A_7 D p C) :=
  Theorem_2_4_linear_stability_branch_of_Lemma_A_7
    D paper3CosineSpectralData p C paper3Cosine_hasNeumannSpectrum hC hA7

abbrev paper3Cosine_Theorem_2_5_linear_stability_of_Lemma_A_8
    (D : BoundedDomainData) (p : CM2Params) (C : Paper3Constants D p)
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    (hA8 : Lemma_A_8 D p C) :=
  Theorem_2_5_linear_stability_branch_of_Lemma_A_8
    D paper3CosineSpectralData p C paper3Cosine_hasNeumannSpectrum hC hA8

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

lemma paper3Cosine_Corollary_5_1_nonminimal_exponential_formula_condition_critical_of_raw
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    (hraw :
      ConvergenceToExponentialNonminimalRaw D p N.c1Distance
        (fun uStar =>
          paperCriticalSensitivity paper3CosineSpectralData p uStar
            (p.ν / p.μ * uStar ^ p.γ)))
    (hm : 1 ≤ p.m) (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ)
    (hcritical :
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      max
          (max (chiStrong1Formula p eq.1 eq.2)
            (chiStrong2Formula p eq.1))
          (max (chiStrong3Formula p M0 eq.1 eq.2)
            (chiStrong4Formula p M0 eq.1)) ≤
        paperCriticalSensitivity paper3CosineSpectralData p eq.1 eq.2)
    (hcond :
      NonminimalGlobalStabilityFormulaCondition p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 M0)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hconv : UniformConvergesInSup D u (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ExponentialC1Convergence D N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  Corollary_5_1_nonminimal_exponential_formula_condition_critical_of_raw
    (S := paper3CosineSpectralData) hraw hm ha hb M0 hcritical hcond
    huv hconv

lemma paper3Cosine_Corollary_5_1_nonminimal_exponential_formula_condition_firstNonzero_of_raw
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    (hraw :
      ConvergenceToExponentialNonminimalRaw D p N.c1Distance
        (fun uStar =>
          paperCriticalSensitivity paper3CosineSpectralData p uStar
            (p.ν / p.μ * uStar ^ p.γ)))
    (hm : 1 ≤ p.m) (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ)
    (hfirst :
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      max
          (max (chiStrong1Formula p eq.1 eq.2)
            (chiStrong2Formula p eq.1))
          (max (chiStrong3Formula p M0 eq.1 eq.2)
            (chiStrong4Formula p M0 eq.1)) ≤
        ((1 + eq.2) ^ p.β /
            (p.ν * p.γ * eq.1 ^ (p.m + p.γ - 1))) *
          (p.μ + Real.pi ^ 2))
    (hcond :
      NonminimalGlobalStabilityFormulaCondition p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 M0)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hconv : UniformConvergesInSup D u (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ExponentialC1Convergence D N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  refine Corollary_5_1_nonminimal_exponential_formula_condition_firstNonzero_of_raw
    (S := paper3CosineSpectralData) hraw paper3Cosine_hasNeumannSpectrum
    hm ha hb M0 ?_ hcond huv hconv
  simpa [paper3CosineSpectralData] using hfirst

lemma paper3Cosine_Corollary_5_1_minimal_exponential_formula_condition_critical_of_raw
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    (hraw :
      ConvergenceToExponentialMinimalRaw D p N.c1Distance
        (fun uStar =>
          paperCriticalSensitivity paper3CosineSpectralData p uStar
            (p.ν / p.μ * uStar ^ p.γ)))
    (hm_le : 1 ≤ p.m) (ha : p.a = 0) (hb : p.b = 0) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ)
    (hcritical :
      _root_.ShenWork.Paper2.chiBeta p ≤
        paperCriticalSensitivity paper3CosineSpectralData p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2)
    (hcond : MinimalGlobalStabilityFormulaCondition p uStar uBar vLower)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hmass : HasInitialMass D u uStar)
    (hconv : UniformConvergesInSup D u (minimalEquilibrium p uStar).1) :
    ExponentialC1Convergence D N u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  Corollary_5_1_minimal_exponential_formula_condition_critical_of_raw
    (S := paper3CosineSpectralData) hraw hm_le ha hb hβ huStar
    uBar vLower hcritical hcond huv hmass hconv

lemma paper3Cosine_Corollary_5_1_minimal_exponential_formula_condition_firstNonzero_of_raw
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    (hraw :
      ConvergenceToExponentialMinimalRaw D p N.c1Distance
        (fun uStar =>
          paperCriticalSensitivity paper3CosineSpectralData p uStar
            (p.ν / p.μ * uStar ^ p.γ)))
    (hm_le : 1 ≤ p.m) (ha : p.a = 0) (hb : p.b = 0) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ)
    (hfirst :
      _root_.ShenWork.Paper2.chiBeta p ≤
        ((1 + (minimalEquilibrium p uStar).2) ^ p.β /
            (p.ν * p.γ *
              (minimalEquilibrium p uStar).1 ^ (p.m + p.γ - 1))) *
          (p.μ + Real.pi ^ 2))
    (hcond : MinimalGlobalStabilityFormulaCondition p uStar uBar vLower)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hmass : HasInitialMass D u uStar)
    (hconv : UniformConvergesInSup D u (minimalEquilibrium p uStar).1) :
    ExponentialC1Convergence D N u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 := by
  refine Corollary_5_1_minimal_exponential_formula_condition_firstNonzero_of_raw
    (S := paper3CosineSpectralData) hraw paper3Cosine_hasNeumannSpectrum
    hm_le ha hb hβ huStar uBar vLower ?_ hcond huv hmass hconv
  simpa [paper3CosineSpectralData] using hfirst

lemma paper3Cosine_Theorem_2_2_xpSigma_nonminimal_formula_of_Lemma_A_1
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hA1 : Lemma_A_1 D p paper3CosineSpectralData N)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    max
        (max (chiStrong1Formula p eq.1 eq.2)
          (chiStrong2Formula p eq.1))
        (max (chiStrong3Formula p M0 eq.1 eq.2)
          (chiStrong4Formula p M0 eq.1)) ≤
      paperCriticalSensitivity paper3CosineSpectralData p eq.1 eq.2 →
      NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, _root_.ShenWork.Paper2.PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                _root_.ShenWork.Paper2.IsPaper2GlobalClassicalSolution D p u v →
                _root_.ShenWork.Paper2.InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate :=
  Theorem_2_2_xpSigma_nonminimal_formula_branch_of_Lemma_A_1
    D paper3CosineSpectralData p N paper3Cosine_hasNeumannSpectrum hA1
    hsigma_low hsigma_high hpNorm ha hb M0

lemma paper3Cosine_Theorem_2_2_xpSigma_nonminimal_first_mode_of_Lemma_A_1
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hA1 : Lemma_A_1 D p paper3CosineSpectralData N)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    max
        (max (chiStrong1Formula p eq.1 eq.2)
          (chiStrong2Formula p eq.1))
        (max (chiStrong3Formula p M0 eq.1 eq.2)
          (chiStrong4Formula p M0 eq.1)) ≤
      ((1 + eq.2) ^ p.β /
          (p.ν * p.γ * eq.1 ^ (p.m + p.γ - 1))) *
        (p.μ + Real.pi ^ 2) →
      NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, _root_.ShenWork.Paper2.PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                _root_.ShenWork.Paper2.IsPaper2GlobalClassicalSolution D p u v →
                _root_.ShenWork.Paper2.InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate := by
  dsimp
  intro hfirst hcond
  exact
    Theorem_2_2_xpSigma_nonminimal_first_mode_branch_of_Lemma_A_1
      D paper3CosineSpectralData p N paper3Cosine_hasNeumannSpectrum hA1
      hsigma_low hsigma_high hpNorm ha hb M0
      (by simpa [paper3CosineSpectralData] using hfirst) hcond

lemma paper3Cosine_Theorem_2_2_xpSigma_minimal_formula_of_Lemma_A_1
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hA1 : Lemma_A_1 D p paper3CosineSpectralData N)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (_ha : p.a = 0) (_hb : p.b = 0) (_hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ) :
    _root_.ShenWork.Paper2.chiBeta p ≤
      paperCriticalSensitivity paper3CosineSpectralData p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 →
      MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, _root_.ShenWork.Paper2.PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀
                (fun _ => (minimalEquilibrium p uStar).1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                _root_.ShenWork.Paper2.IsPaper2GlobalClassicalSolution D p u v →
                _root_.ShenWork.Paper2.InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v
                    (minimalEquilibrium p uStar).1
                    (minimalEquilibrium p uStar).2 A rate :=
  Theorem_2_2_xpSigma_minimal_formula_branch_of_Lemma_A_1
    D paper3CosineSpectralData p N paper3Cosine_hasNeumannSpectrum hA1
    hsigma_low hsigma_high hpNorm _ha _hb _hm hβ huStar uBar vLower

lemma paper3Cosine_Theorem_2_2_xpSigma_minimal_first_mode_of_Lemma_A_1
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hA1 : Lemma_A_1 D p paper3CosineSpectralData N)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (_ha : p.a = 0) (_hb : p.b = 0) (_hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ) :
    _root_.ShenWork.Paper2.chiBeta p ≤
      ((1 + (minimalEquilibrium p uStar).2) ^ p.β /
          (p.ν * p.γ *
            (minimalEquilibrium p uStar).1 ^ (p.m + p.γ - 1))) *
        (p.μ + Real.pi ^ 2) →
      MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, _root_.ShenWork.Paper2.PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀
                (fun _ => (minimalEquilibrium p uStar).1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                _root_.ShenWork.Paper2.IsPaper2GlobalClassicalSolution D p u v →
                _root_.ShenWork.Paper2.InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v
                    (minimalEquilibrium p uStar).1
                    (minimalEquilibrium p uStar).2 A rate := by
  intro hfirst hcond
  exact
    Theorem_2_2_xpSigma_minimal_first_mode_branch_of_Lemma_A_1
      D paper3CosineSpectralData p N paper3Cosine_hasNeumannSpectrum hA1
      hsigma_low hsigma_high hpNorm _ha _hb _hm hβ huStar uBar vLower
      (by simpa [paper3CosineSpectralData] using hfirst) hcond

lemma paper3Cosine_Theorem_2_2_xpSigma_chi_nonpos_of_Lemma_A_1
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hA1 : Lemma_A_1 D p paper3CosineSpectralData N)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm) (hχ : p.χ₀ ≤ 0) :
    (∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
        ∀ u₀ : D.Point → ℝ, _root_.ShenWork.Paper2.PositiveInitialDatum D u₀ →
          N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
            ∀ u v : ℝ → D.Point → ℝ,
              _root_.ShenWork.Paper2.IsPaper2GlobalClassicalSolution D p u v →
              _root_.ShenWork.Paper2.InitialTrace D u₀ u →
                ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate) ∧
    (p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, _root_.ShenWork.Paper2.PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                _root_.ShenWork.Paper2.IsPaper2GlobalClassicalSolution D p u v →
                _root_.ShenWork.Paper2.InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate) :=
  Theorem_2_2_xpSigma_chi_nonpos_branch_of_Lemma_A_1
    D paper3CosineSpectralData p N paper3Cosine_hasNeumannSpectrum hA1
    hsigma_low hsigma_high hpNorm hχ

lemma paper3Cosine_Theorem_2_2_xpSigma_chi_nonpos_of_raw
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p paper3CosineSpectralData
        N.c1Distance N.xpSigmaDistance)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm) (hχ : p.χ₀ ≤ 0) :
    (∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
        ∀ u₀ : D.Point → ℝ, _root_.ShenWork.Paper2.PositiveInitialDatum D u₀ →
          N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
            ∀ u v : ℝ → D.Point → ℝ,
              _root_.ShenWork.Paper2.IsPaper2GlobalClassicalSolution D p u v →
              _root_.ShenWork.Paper2.InitialTrace D u₀ u →
                ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate) ∧
    (p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, _root_.ShenWork.Paper2.PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                _root_.ShenWork.Paper2.IsPaper2GlobalClassicalSolution D p u v →
                _root_.ShenWork.Paper2.InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate) :=
  Theorem_2_2_xpSigma_chi_nonpos_branch_of_raw
    D paper3CosineSpectralData p N paper3Cosine_hasNeumannSpectrum hraw
    hsigma_low hsigma_high hpNorm hχ

lemma paper3Cosine_Theorem_2_2_xpSigma_nonminimal_formula_of_raw
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p paper3CosineSpectralData
        N.c1Distance N.xpSigmaDistance)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    max
        (max (chiStrong1Formula p eq.1 eq.2)
          (chiStrong2Formula p eq.1))
        (max (chiStrong3Formula p M0 eq.1 eq.2)
          (chiStrong4Formula p M0 eq.1)) ≤
      paperCriticalSensitivity paper3CosineSpectralData p eq.1 eq.2 →
      NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, _root_.ShenWork.Paper2.PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                _root_.ShenWork.Paper2.IsPaper2GlobalClassicalSolution D p u v →
                _root_.ShenWork.Paper2.InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate :=
  Theorem_2_2_xpSigma_nonminimal_formula_branch_of_raw
    D paper3CosineSpectralData p N paper3Cosine_hasNeumannSpectrum hraw
    hsigma_low hsigma_high hpNorm ha hb M0

lemma paper3Cosine_Theorem_2_2_xpSigma_minimal_formula_of_raw
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p paper3CosineSpectralData
        N.c1Distance N.xpSigmaDistance)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (_ha : p.a = 0) (_hb : p.b = 0) (_hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ) :
    _root_.ShenWork.Paper2.chiBeta p ≤
      paperCriticalSensitivity paper3CosineSpectralData p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 →
      MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, _root_.ShenWork.Paper2.PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀
                (fun _ => (minimalEquilibrium p uStar).1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                _root_.ShenWork.Paper2.IsPaper2GlobalClassicalSolution D p u v →
                _root_.ShenWork.Paper2.InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v
                    (minimalEquilibrium p uStar).1
                    (minimalEquilibrium p uStar).2 A rate :=
  Theorem_2_2_xpSigma_minimal_formula_branch_of_raw
    D paper3CosineSpectralData p N paper3Cosine_hasNeumannSpectrum hraw
    hsigma_low hsigma_high hpNorm _ha _hb _hm hβ huStar uBar vLower

lemma paper3Cosine_Theorem_2_2_xpSigma_nonminimal_first_mode_of_raw
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p paper3CosineSpectralData
        N.c1Distance N.xpSigmaDistance)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    max
        (max (chiStrong1Formula p eq.1 eq.2)
          (chiStrong2Formula p eq.1))
        (max (chiStrong3Formula p M0 eq.1 eq.2)
          (chiStrong4Formula p M0 eq.1)) ≤
      ((1 + eq.2) ^ p.β /
          (p.ν * p.γ * eq.1 ^ (p.m + p.γ - 1))) *
        (p.μ + Real.pi ^ 2) →
      NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, _root_.ShenWork.Paper2.PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                _root_.ShenWork.Paper2.IsPaper2GlobalClassicalSolution D p u v →
                _root_.ShenWork.Paper2.InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate := by
  dsimp
  intro hfirst hcond
  exact
    Theorem_2_2_xpSigma_nonminimal_first_mode_branch_of_raw
      D paper3CosineSpectralData p N paper3Cosine_hasNeumannSpectrum hraw
      hsigma_low hsigma_high hpNorm ha hb M0
      (by simpa [paper3CosineSpectralData] using hfirst) hcond

lemma paper3Cosine_Theorem_2_2_xpSigma_minimal_first_mode_of_raw
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p paper3CosineSpectralData
        N.c1Distance N.xpSigmaDistance)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (_ha : p.a = 0) (_hb : p.b = 0) (_hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ) :
    _root_.ShenWork.Paper2.chiBeta p ≤
      ((1 + (minimalEquilibrium p uStar).2) ^ p.β /
          (p.ν * p.γ *
            (minimalEquilibrium p uStar).1 ^ (p.m + p.γ - 1))) *
        (p.μ + Real.pi ^ 2) →
      MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, _root_.ShenWork.Paper2.PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀
                (fun _ => (minimalEquilibrium p uStar).1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                _root_.ShenWork.Paper2.IsPaper2GlobalClassicalSolution D p u v →
                _root_.ShenWork.Paper2.InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v
                    (minimalEquilibrium p uStar).1
                    (minimalEquilibrium p uStar).2 A rate := by
  intro hfirst hcond
  exact
    Theorem_2_2_xpSigma_minimal_first_mode_branch_of_raw
      D paper3CosineSpectralData p N paper3Cosine_hasNeumannSpectrum hraw
      hsigma_low hsigma_high hpNorm _ha _hb _hm hβ huStar uBar vLower
      (by simpa [paper3CosineSpectralData] using hfirst) hcond

lemma paper3Cosine_Theorem_2_4_linear_stability_formula
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    max
        (max (chiStrong1Formula p eq.1 eq.2)
          (chiStrong2Formula p eq.1))
        (max (chiStrong3Formula p M0 eq.1 eq.2)
          (chiStrong4Formula p M0 eq.1)) ≤
      paperCriticalSensitivity paper3CosineSpectralData p eq.1 eq.2 →
      NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
        LinearlyStable paper3CosineSpectralData p eq.1 eq.2 :=
  Theorem_2_4_linear_stability_formula_branch_direct
    paper3CosineSpectralData p paper3Cosine_hasNeumannSpectrum ha hb M0

lemma paper3Cosine_Theorem_2_4_linear_stability_first_mode
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    max
        (max (chiStrong1Formula p eq.1 eq.2)
          (chiStrong2Formula p eq.1))
        (max (chiStrong3Formula p M0 eq.1 eq.2)
          (chiStrong4Formula p M0 eq.1)) ≤
      ((1 + eq.2) ^ p.β /
          (p.ν * p.γ * eq.1 ^ (p.m + p.γ - 1))) *
        (p.μ + Real.pi ^ 2) →
      NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
        LinearlyStable paper3CosineSpectralData p eq.1 eq.2 := by
  dsimp
  intro hfirst hcond
  exact
    Theorem_2_4_linear_stability_first_mode_branch_direct
      paper3CosineSpectralData p paper3Cosine_hasNeumannSpectrum
      ha hb M0 (by simpa [paper3CosineSpectralData] using hfirst) hcond

lemma paper3Cosine_Theorem_2_5_linear_stability_formula
    (p : CM2Params)
    (_ha : p.a = 0) (_hb : p.b = 0) (_hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ) :
    _root_.ShenWork.Paper2.chiBeta p ≤
      paperCriticalSensitivity paper3CosineSpectralData p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 →
      MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
        LinearlyStable paper3CosineSpectralData p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 :=
  Theorem_2_5_linear_stability_formula_branch_direct
    paper3CosineSpectralData p paper3Cosine_hasNeumannSpectrum
    _ha _hb _hm hβ huStar uBar vLower

lemma paper3Cosine_Theorem_2_5_linear_stability_first_mode
    (p : CM2Params)
    (_ha : p.a = 0) (_hb : p.b = 0) (_hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ) :
    _root_.ShenWork.Paper2.chiBeta p ≤
      ((1 + (minimalEquilibrium p uStar).2) ^ p.β /
          (p.ν * p.γ *
            (minimalEquilibrium p uStar).1 ^ (p.m + p.γ - 1))) *
        (p.μ + Real.pi ^ 2) →
      MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
        LinearlyStable paper3CosineSpectralData p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 := by
  intro hfirst hcond
  exact
    Theorem_2_5_linear_stability_first_mode_branch_direct
      paper3CosineSpectralData p paper3Cosine_hasNeumannSpectrum
      _ha _hb _hm hβ huStar uBar vLower
      (by simpa [paper3CosineSpectralData] using hfirst) hcond

lemma paper3Cosine_Theorem_2_3_negative_sensitivity_convergence_of_sectorial
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    (LinearlyStable paper3CosineSpectralData p eq.1 eq.2 →
      MassConstrainedLocallyExponentiallyStableFromSup D p N eq.1 eq.2) →
      LinearlyStable paper3CosineSpectralData p eq.1 eq.2 ∧
      MassConstrainedLocallyExponentiallyStableFromSup D p N eq.1 eq.2 :=
  Theorem_2_3_negative_sensitivity_convergence_formula_branch_of_sectorial
    D paper3CosineSpectralData p N paper3Cosine_hasNeumannSpectrum hχ ha hb

lemma paper3Cosine_Theorem_2_4_full_stability_formula_of_sectorial
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    max
        (max (chiStrong1Formula p eq.1 eq.2)
          (chiStrong2Formula p eq.1))
        (max (chiStrong3Formula p M0 eq.1 eq.2)
          (chiStrong4Formula p M0 eq.1)) ≤
      paperCriticalSensitivity paper3CosineSpectralData p eq.1 eq.2 →
      NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
        (LinearlyStable paper3CosineSpectralData p eq.1 eq.2 →
          MassConstrainedLocallyExponentiallyStableFromSup D p N eq.1 eq.2) →
          LinearlyStable paper3CosineSpectralData p eq.1 eq.2 ∧
          MassConstrainedLocallyExponentiallyStableFromSup D p N eq.1 eq.2 :=
  Theorem_2_4_full_stability_formula_branch_of_sectorial
    D paper3CosineSpectralData p N paper3Cosine_hasNeumannSpectrum ha hb M0

lemma paper3Cosine_Theorem_2_4_full_stability_first_mode_of_sectorial
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    max
        (max (chiStrong1Formula p eq.1 eq.2)
          (chiStrong2Formula p eq.1))
        (max (chiStrong3Formula p M0 eq.1 eq.2)
          (chiStrong4Formula p M0 eq.1)) ≤
      ((1 + eq.2) ^ p.β /
          (p.ν * p.γ * eq.1 ^ (p.m + p.γ - 1))) *
        (p.μ + Real.pi ^ 2) →
      NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
        (LinearlyStable paper3CosineSpectralData p eq.1 eq.2 →
          MassConstrainedLocallyExponentiallyStableFromSup D p N eq.1 eq.2) →
          LinearlyStable paper3CosineSpectralData p eq.1 eq.2 ∧
          MassConstrainedLocallyExponentiallyStableFromSup D p N eq.1 eq.2 := by
  dsimp
  intro hfirst hcond hsectorial
  exact
    Theorem_2_4_full_stability_first_mode_branch_of_sectorial
      D paper3CosineSpectralData p N paper3Cosine_hasNeumannSpectrum
      ha hb M0 (by simpa [paper3CosineSpectralData] using hfirst)
      hcond hsectorial

lemma paper3Cosine_Theorem_2_5_full_stability_formula_of_sectorial
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (_ha : p.a = 0) (_hb : p.b = 0) (_hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ) :
    _root_.ShenWork.Paper2.chiBeta p ≤
      paperCriticalSensitivity paper3CosineSpectralData p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 →
      MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
        (LinearlyStable paper3CosineSpectralData p
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 →
          MassConstrainedLocallyExponentiallyStableFromSup D p N
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2) →
          LinearlyStable paper3CosineSpectralData p
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 ∧
          MassConstrainedLocallyExponentiallyStableFromSup D p N
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 :=
  Theorem_2_5_full_stability_formula_branch_of_sectorial
    D paper3CosineSpectralData p N paper3Cosine_hasNeumannSpectrum
    _ha _hb _hm hβ huStar uBar vLower

lemma paper3Cosine_Theorem_2_5_full_stability_first_mode_of_sectorial
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (_ha : p.a = 0) (_hb : p.b = 0) (_hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ) :
    _root_.ShenWork.Paper2.chiBeta p ≤
      ((1 + (minimalEquilibrium p uStar).2) ^ p.β /
          (p.ν * p.γ *
            (minimalEquilibrium p uStar).1 ^ (p.m + p.γ - 1))) *
        (p.μ + Real.pi ^ 2) →
      MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
        (LinearlyStable paper3CosineSpectralData p
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 →
          MassConstrainedLocallyExponentiallyStableFromSup D p N
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2) →
          LinearlyStable paper3CosineSpectralData p
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 ∧
          MassConstrainedLocallyExponentiallyStableFromSup D p N
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 := by
  intro hfirst hcond hsectorial
  exact
    Theorem_2_5_full_stability_first_mode_branch_of_sectorial
      D paper3CosineSpectralData p N paper3Cosine_hasNeumannSpectrum
      _ha _hb _hm hβ huStar uBar vLower
      (by simpa [paper3CosineSpectralData] using hfirst) hcond hsectorial

abbrev paper3Cosine_Theorem_2_3_negative_sensitivity_mass_constrained_formula_of_raw
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p paper3CosineSpectralData
        N.c1Distance N.xpSigmaDistance) :=
  fun {sigma pNorm : ℝ} =>
    Theorem_2_3_negative_sensitivity_mass_constrained_formula_branch_of_raw
      (D := D) (S := paper3CosineSpectralData) (p := p) (N := N)
      (sigma := sigma) (pNorm := pNorm)
      paper3Cosine_hasNeumannSpectrum hraw

abbrev paper3Cosine_Theorem_2_3_negative_sensitivity_mass_constrained_formula_of_xpSigma_le_supNorm
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p paper3CosineSpectralData
        N.c1Distance N.xpSigmaDistance) :=
  fun {sigma pNorm : ℝ} =>
    Theorem_2_3_negative_sensitivity_mass_constrained_formula_branch_of_xpSigma_le_supNorm
      (D := D) (S := paper3CosineSpectralData) (p := p) (N := N)
      (sigma := sigma) (pNorm := pNorm)
      paper3Cosine_hasNeumannSpectrum hraw

abbrev paper3Cosine_Theorem_2_3_negative_sensitivity_local_formula_of_raw
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p paper3CosineSpectralData
        N.c1Distance N.xpSigmaDistance) :=
  fun {sigma pNorm : ℝ} =>
    Theorem_2_3_negative_sensitivity_local_formula_branch_of_raw
      (D := D) (S := paper3CosineSpectralData) (p := p) (N := N)
      (sigma := sigma) (pNorm := pNorm)
      paper3Cosine_hasNeumannSpectrum hraw

abbrev paper3Cosine_Theorem_2_3_negative_sensitivity_local_formula_of_xpSigma_le_supNorm
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p paper3CosineSpectralData
        N.c1Distance N.xpSigmaDistance) :=
  fun {sigma pNorm : ℝ} =>
    Theorem_2_3_negative_sensitivity_local_formula_branch_of_xpSigma_le_supNorm
      (D := D) (S := paper3CosineSpectralData) (p := p) (N := N)
      (sigma := sigma) (pNorm := pNorm)
      paper3Cosine_hasNeumannSpectrum hraw

abbrev paper3Cosine_Theorem_2_4_full_stability_formula_of_raw
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p paper3CosineSpectralData
        N.c1Distance N.xpSigmaDistance) :=
  fun {sigma pNorm : ℝ} =>
    Theorem_2_4_full_stability_formula_branch_of_raw
      (D := D) (S := paper3CosineSpectralData) (p := p) (N := N)
      (sigma := sigma) (pNorm := pNorm)
      paper3Cosine_hasNeumannSpectrum hraw

abbrev paper3Cosine_Theorem_2_4_full_stability_formula_of_xpSigma_le_supNorm
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p paper3CosineSpectralData
        N.c1Distance N.xpSigmaDistance) :=
  fun {sigma pNorm : ℝ} =>
    Theorem_2_4_full_stability_formula_branch_of_xpSigma_le_supNorm
      (D := D) (S := paper3CosineSpectralData) (p := p) (N := N)
      (sigma := sigma) (pNorm := pNorm)
      paper3Cosine_hasNeumannSpectrum hraw

abbrev paper3Cosine_Theorem_2_4_full_stability_first_mode_of_raw
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p paper3CosineSpectralData
        N.c1Distance N.xpSigmaDistance) :=
  fun {sigma pNorm : ℝ} =>
    Theorem_2_4_full_stability_first_mode_branch_of_raw
      (D := D) (S := paper3CosineSpectralData) (p := p) (N := N)
      (sigma := sigma) (pNorm := pNorm)
      paper3Cosine_hasNeumannSpectrum hraw

abbrev paper3Cosine_Theorem_2_4_full_stability_first_mode_of_xpSigma_le_supNorm
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p paper3CosineSpectralData
        N.c1Distance N.xpSigmaDistance) :=
  fun {sigma pNorm : ℝ} =>
    Theorem_2_4_full_stability_first_mode_branch_of_xpSigma_le_supNorm
      (D := D) (S := paper3CosineSpectralData) (p := p) (N := N)
      (sigma := sigma) (pNorm := pNorm)
      paper3Cosine_hasNeumannSpectrum hraw

abbrev paper3Cosine_Theorem_2_4_local_stability_formula_of_raw
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p paper3CosineSpectralData
        N.c1Distance N.xpSigmaDistance) :=
  fun {sigma pNorm : ℝ} =>
    Theorem_2_4_local_stability_formula_branch_of_raw
      (D := D) (S := paper3CosineSpectralData) (p := p) (N := N)
      (sigma := sigma) (pNorm := pNorm)
      paper3Cosine_hasNeumannSpectrum hraw

abbrev paper3Cosine_Theorem_2_4_local_stability_formula_of_xpSigma_le_supNorm
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p paper3CosineSpectralData
        N.c1Distance N.xpSigmaDistance) :=
  fun {sigma pNorm : ℝ} =>
    Theorem_2_4_local_stability_formula_branch_of_xpSigma_le_supNorm
      (D := D) (S := paper3CosineSpectralData) (p := p) (N := N)
      (sigma := sigma) (pNorm := pNorm)
      paper3Cosine_hasNeumannSpectrum hraw

abbrev paper3Cosine_Theorem_2_4_local_stability_first_mode_of_raw
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p paper3CosineSpectralData
        N.c1Distance N.xpSigmaDistance) :=
  fun {sigma pNorm : ℝ} =>
    Theorem_2_4_local_stability_first_mode_branch_of_raw
      (D := D) (S := paper3CosineSpectralData) (p := p) (N := N)
      (sigma := sigma) (pNorm := pNorm)
      paper3Cosine_hasNeumannSpectrum hraw

abbrev paper3Cosine_Theorem_2_4_local_stability_first_mode_of_xpSigma_le_supNorm
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p paper3CosineSpectralData
        N.c1Distance N.xpSigmaDistance) :=
  fun {sigma pNorm : ℝ} =>
    Theorem_2_4_local_stability_first_mode_branch_of_xpSigma_le_supNorm
      (D := D) (S := paper3CosineSpectralData) (p := p) (N := N)
      (sigma := sigma) (pNorm := pNorm)
      paper3Cosine_hasNeumannSpectrum hraw

abbrev paper3Cosine_Theorem_2_5_full_stability_formula_of_raw
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p paper3CosineSpectralData
        N.c1Distance N.xpSigmaDistance) :=
  fun {sigma pNorm : ℝ} =>
    Theorem_2_5_full_stability_formula_branch_of_raw
      (D := D) (S := paper3CosineSpectralData) (p := p) (N := N)
      (sigma := sigma) (pNorm := pNorm)
      paper3Cosine_hasNeumannSpectrum hraw

abbrev paper3Cosine_Theorem_2_5_full_stability_formula_of_xpSigma_le_supNorm
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p paper3CosineSpectralData
        N.c1Distance N.xpSigmaDistance) :=
  fun {sigma pNorm : ℝ} =>
    Theorem_2_5_full_stability_formula_branch_of_xpSigma_le_supNorm
      (D := D) (S := paper3CosineSpectralData) (p := p) (N := N)
      (sigma := sigma) (pNorm := pNorm)
      paper3Cosine_hasNeumannSpectrum hraw

abbrev paper3Cosine_Theorem_2_5_full_stability_first_mode_of_raw
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p paper3CosineSpectralData
        N.c1Distance N.xpSigmaDistance) :=
  fun {sigma pNorm : ℝ} =>
    Theorem_2_5_full_stability_first_mode_branch_of_raw
      (D := D) (S := paper3CosineSpectralData) (p := p) (N := N)
      (sigma := sigma) (pNorm := pNorm)
      paper3Cosine_hasNeumannSpectrum hraw

abbrev paper3Cosine_Theorem_2_5_full_stability_first_mode_of_xpSigma_le_supNorm
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p paper3CosineSpectralData
        N.c1Distance N.xpSigmaDistance) :=
  fun {sigma pNorm : ℝ} =>
    Theorem_2_5_full_stability_first_mode_branch_of_xpSigma_le_supNorm
      (D := D) (S := paper3CosineSpectralData) (p := p) (N := N)
      (sigma := sigma) (pNorm := pNorm)
      paper3Cosine_hasNeumannSpectrum hraw

lemma paper3Cosine_Corollary_5_1_nonminimal_exponential
    {D : BoundedDomainData} {p : CM2Params}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Corollary_5_1 D p N C)
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
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
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.nonminimal_exponential_of_chi_lt_paperCriticalSensitivity
    hC hm ha hb hχ huv hconv

lemma paper3Cosine_Corollary_5_1_minimal_exponential
    {D : BoundedDomainData} {p : CM2Params}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Corollary_5_1 D p N C)
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
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
      (minimalEquilibrium p uStar).2 :=
  h.minimal_exponential_of_chi_lt_paperCriticalSensitivity
    hC hm ha hb huStar hχ huv hmass hconv

lemma paper3Cosine_Corollary_5_1_nonminimal_exponential_of_firstNonzero_formula_fields
    {D : BoundedDomainData} {p : CM2Params}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Corollary_5_1 D p N C)
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    (M0 : ℝ)
    (hstrong1 :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        C.chiStrong1 eq.1 = chiStrong1Formula p eq.1 eq.2)
    (hstrong2 :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        C.chiStrong2 eq.1 = chiStrong2Formula p eq.1)
    (hstrong3 :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        C.chiStrong3 eq.1 = chiStrong3Formula p M0 eq.1 eq.2)
    (hstrong4 :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        C.chiStrong4 eq.1 = chiStrong4Formula p M0 eq.1)
    (hfirst :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        max
            (max (chiStrong1Formula p eq.1 eq.2)
              (chiStrong2Formula p eq.1))
            (max (chiStrong3Formula p M0 eq.1 eq.2)
              (chiStrong4Formula p M0 eq.1)) ≤
          ((1 + eq.2) ^ p.β /
              (p.ν * p.γ * eq.1 ^ (p.m + p.γ - 1))) *
            (p.μ + Real.pi ^ 2))
    (hm : 1 ≤ p.m) (ha : 0 < p.a) (hb : 0 < p.b)
    (hcond :
      NonminimalGlobalStabilityCondition D p C
        (positiveEquilibrium p ⟨ha, hb⟩).1)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hconv : UniformConvergesInSup D u (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ExponentialC1Convergence D N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  refine h.nonminimal_exponential_of_firstNonzero_formula_fields
    paper3Cosine_hasNeumannSpectrum hC M0 hstrong1 hstrong2 hstrong3
    hstrong4 ?_ hm ha hb hcond huv hconv
  intro ha' hb'
  simpa [paper3CosineSpectralData] using hfirst ha' hb'

lemma paper3Cosine_Corollary_5_1_minimal_exponential_of_firstNonzero_formula_fields
    {D : BoundedDomainData} {p : CM2Params}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Corollary_5_1 D p N C)
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    (uBar vLower : ℝ)
    (hminimal1 :
      ∀ uStar > 0,
        C.chiMinimal1 uStar =
          chiMinimal1Formula p 1 uStar uBar vLower)
    (hminimal2 :
      ∀ uStar > 0,
        C.chiMinimal2 uStar = chiMinimal2Formula p uBar vLower)
    (hfirst :
      ∀ uStar > 0,
        _root_.ShenWork.Paper2.chiBeta p ≤
          ((1 + (minimalEquilibrium p uStar).2) ^ p.β /
              (p.ν * p.γ *
                (minimalEquilibrium p uStar).1 ^ (p.m + p.γ - 1))) *
            (p.μ + Real.pi ^ 2))
    (hm_le : 1 ≤ p.m) (ha : p.a = 0) (hb : p.b = 0)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hcond : MinimalGlobalStabilityCondition D p C uStar)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hmass : HasInitialMass D u uStar)
    (hconv : UniformConvergesInSup D u (minimalEquilibrium p uStar).1) :
    ExponentialC1Convergence D N u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 := by
  refine h.minimal_exponential_of_firstNonzero_formula_fields
    paper3Cosine_hasNeumannSpectrum hC uBar vLower hminimal1 hminimal2
    ?_ hm_le ha hb hm hβ huStar hcond huv hmass hconv
  intro uStar' huStar'
  simpa [paper3CosineSpectralData] using hfirst uStar' huStar'

lemma paper3Cosine_Corollary_5_1_nonminimal_exponential_formula_condition_critical
    {D : BoundedDomainData} {p : CM2Params}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Corollary_5_1 D p N C)
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    (hm : 1 ≤ p.m) (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ)
    (hcritical :
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      max
          (max (chiStrong1Formula p eq.1 eq.2)
            (chiStrong2Formula p eq.1))
          (max (chiStrong3Formula p M0 eq.1 eq.2)
            (chiStrong4Formula p M0 eq.1)) ≤
        paperCriticalSensitivity paper3CosineSpectralData p eq.1 eq.2)
    (hcond :
      NonminimalGlobalStabilityFormulaCondition p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 M0)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hconv : UniformConvergesInSup D u (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ExponentialC1Convergence D N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.nonminimal_exponential_of_formula_condition_critical
    hC hm ha hb M0 hcritical hcond huv hconv

lemma paper3Cosine_Corollary_5_1_minimal_exponential_formula_condition_critical
    {D : BoundedDomainData} {p : CM2Params}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Corollary_5_1 D p N C)
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    (hm_le : 1 ≤ p.m) (ha : p.a = 0) (hb : p.b = 0) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ)
    (hcritical :
      _root_.ShenWork.Paper2.chiBeta p ≤
        paperCriticalSensitivity paper3CosineSpectralData p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2)
    (hcond : MinimalGlobalStabilityFormulaCondition p uStar uBar vLower)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hmass : HasInitialMass D u uStar)
    (hconv : UniformConvergesInSup D u (minimalEquilibrium p uStar).1) :
    ExponentialC1Convergence D N u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  h.minimal_exponential_of_formula_condition_critical
    hC hm_le ha hb hβ huStar uBar vLower hcritical hcond
    huv hmass hconv

lemma paper3Cosine_Corollary_5_1_nonminimal_exponential_formula_condition_firstNonzero
    {D : BoundedDomainData} {p : CM2Params}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Corollary_5_1 D p N C)
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    (hm : 1 ≤ p.m) (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ)
    (hfirst :
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      max
          (max (chiStrong1Formula p eq.1 eq.2)
            (chiStrong2Formula p eq.1))
          (max (chiStrong3Formula p M0 eq.1 eq.2)
            (chiStrong4Formula p M0 eq.1)) ≤
        ((1 + eq.2) ^ p.β /
            (p.ν * p.γ * eq.1 ^ (p.m + p.γ - 1))) *
          (p.μ + Real.pi ^ 2))
    (hcond :
      NonminimalGlobalStabilityFormulaCondition p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 M0)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hconv : UniformConvergesInSup D u (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ExponentialC1Convergence D N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  refine h.nonminimal_exponential_of_formula_condition_firstNonzero
    paper3Cosine_hasNeumannSpectrum hC hm ha hb M0 ?_ hcond huv hconv
  simpa [paper3CosineSpectralData] using hfirst

lemma paper3Cosine_Corollary_5_1_minimal_exponential_formula_condition_firstNonzero
    {D : BoundedDomainData} {p : CM2Params}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Corollary_5_1 D p N C)
    (hC : Paper3ConstantsUsesCosineCriticalSpectrum p C)
    (hm_le : 1 ≤ p.m) (ha : p.a = 0) (hb : p.b = 0) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ)
    (hfirst :
      _root_.ShenWork.Paper2.chiBeta p ≤
        ((1 + (minimalEquilibrium p uStar).2) ^ p.β /
            (p.ν * p.γ *
              (minimalEquilibrium p uStar).1 ^ (p.m + p.γ - 1))) *
          (p.μ + Real.pi ^ 2))
    (hcond : MinimalGlobalStabilityFormulaCondition p uStar uBar vLower)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hmass : HasInitialMass D u uStar)
    (hconv : UniformConvergesInSup D u (minimalEquilibrium p uStar).1) :
    ExponentialC1Convergence D N u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 := by
  refine h.minimal_exponential_of_formula_condition_firstNonzero
    paper3Cosine_hasNeumannSpectrum hC hm_le ha hb hβ huStar
    uBar vLower ?_ hcond huv hmass hconv
  simpa [paper3CosineSpectralData] using hfirst

end ShenWork.CosineSpectrum

end
