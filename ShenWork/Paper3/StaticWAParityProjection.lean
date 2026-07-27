import ShenWork.Paper3.StaticWASymmetry

/-!
# Continuous odd-imaginary projection in static `WA`

The nonlinear branch flux is most conveniently differentiated as an
ambient `WA`-valued expression.  This file supplies a bounded real-linear
projection from ambient coefficients onto the odd, purely imaginary
subspace.  On an already odd-imaginary element the projection is the
identity.
-/

noncomputable section

namespace ShenWork.M3Counterexample

open ShenWork.Wiener

/-! ## The two continuous real-linear involutions -/

def waReflRLM (r : ℕ) : WA r →ₗ[ℝ] WA r where
  toFun := waRefl
  map_add' := waRefl_add
  map_smul' c a := by
    apply WA.ext
    funext n
    rfl

theorem norm_waRefl (a : WA r) : ‖waRefl a‖ = ‖a‖ := by
  change wNorm r (fun n => a.toFun (-n)) = wNorm r a.toFun
  rw [wNorm]
  rw [← (Equiv.neg ℤ).tsum_eq
    (fun n => wWeight r n * ‖a.toFun (-n)‖)]
  apply tsum_congr
  intro n
  simp only [Equiv.neg_apply, neg_neg]
  rw [show wWeight r (-n) = wWeight r n by simp [wWeight, abs_neg]]

def waReflRCLM (r : ℕ) : WA r →L[ℝ] WA r :=
  (waReflRLM r).mkContinuous 1 (fun a => by
    rw [one_mul]
    change ‖waRefl a‖ ≤ ‖a‖
    rw [norm_waRefl])

@[simp]
theorem waReflRCLM_apply (r : ℕ) (a : WA r) :
    waReflRCLM r a = waRefl a :=
  rfl

def waConjRLM (r : ℕ) : WA r →ₗ[ℝ] WA r where
  toFun := waConj
  map_add' := waConj_add
  map_smul' c a := by
    apply WA.ext
    funext n
    change star ((c : ℂ) * a.toFun n) =
      (c : ℂ) * star (a.toFun n)
    simp

theorem norm_waConj (a : WA r) : ‖waConj a‖ = ‖a‖ := by
  change wNorm r (fun n => star (a.toFun n)) = wNorm r a.toFun
  apply tsum_congr
  intro n
  rw [norm_star]

def waConjRCLM (r : ℕ) : WA r →L[ℝ] WA r :=
  (waConjRLM r).mkContinuous 1 (fun a => by
    rw [one_mul]
    change ‖waConj a‖ ≤ ‖a‖
    rw [norm_waConj])

@[simp]
theorem waConjRCLM_apply (r : ℕ) (a : WA r) :
    waConjRCLM r a = waConj a :=
  rfl

/-! ## Projection onto the anti-fixed intersection -/

/-- Ambient projector onto coefficients anti-fixed by both reflection and
coefficient conjugation. -/
def oddImagAmbientProjectionCLM (r : ℕ) : WA r →L[ℝ] WA r :=
  (1 / 4 : ℝ) •
    (ContinuousLinearMap.id ℝ (WA r) - waReflRCLM r -
      waConjRCLM r + (waConjRCLM r).comp (waReflRCLM r))

@[simp]
theorem oddImagAmbientProjection_coeff (r : ℕ) (a : WA r) (n : ℤ) :
    (oddImagAmbientProjectionCLM r a).toFun n =
      (1 / 4 : ℝ) •
        (a.toFun n - a.toFun (-n) - star (a.toFun n) +
          star (a.toFun (-n))) := by
  rfl

theorem oddImagAmbientProjection_mem (r : ℕ) (a : WA r) :
    oddImagAmbientProjectionCLM r a ∈ oddImagSubmodule r := by
  rw [mem_oddImagSubmodule_iff]
  constructor
  · intro n
    rw [oddImagAmbientProjection_coeff]
    simp only [Complex.real_smul]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im,
      Complex.star_def, Complex.conj_re]
    ring
  · intro n
    rw [oddImagAmbientProjection_coeff, oddImagAmbientProjection_coeff]
    simp only [neg_neg]
    module

/-- Continuous projection from ambient Wiener coefficients onto the
odd-imaginary parity subspace. -/
def oddImagProjectionCLM (r : ℕ) : WA r →L[ℝ] OddImagWA r :=
  (oddImagAmbientProjectionCLM r).codRestrict
    (oddImagSubmodule r) (oddImagAmbientProjection_mem r)

@[simp]
theorem oddImagProjectionCLM_coe (r : ℕ) (a : WA r) :
    (oddImagProjectionCLM r a : WA r) =
      oddImagAmbientProjectionCLM r a :=
  rfl

@[simp]
theorem oddImagProjection_eq_self (a : OddImagWA r) :
    oddImagProjectionCLM r a.1 = a := by
  apply Subtype.ext
  rw [oddImagProjectionCLM_coe]
  have ha := (oddImag_iff_antifixed a.1).mp a.2
  have hboth : waConj (waRefl a.1) = a.1 := by
    rw [ha.1]
    change waConjRCLM r (-a.1) = a.1
    rw [map_neg, waConjRCLM_apply, ha.2, neg_neg]
  change
    (1 / 4 : ℝ) •
        (a.1 - waRefl a.1 - waConj a.1 + waConj (waRefl a.1)) =
      a.1
  rw [hboth, ha.1, ha.2]
  module

end ShenWork.M3Counterexample
