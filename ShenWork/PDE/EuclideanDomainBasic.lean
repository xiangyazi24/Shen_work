/-
  ShenWork/PDE/EuclideanDomainBasic.lean

  Basic measure and integral facts for the finite-dimensional Euclidean
  bounded-domain instance.
-/
import ShenWork.PDE.EuclideanDomainData

open MeasureTheory Set

noncomputable section

namespace ShenWork.EuclideanDomain
namespace EuclideanDomainData

variable {N : ℕ} (D : EuclideanDomainData N)

/-! ## The zero extension -/

@[simp] theorem lift_apply (f : D.Point → ℝ) (x : D.Point) :
    D.lift f x.1 = f x := by
  simp [lift, x.2]

theorem lift_apply_of_mem (f : D.Point → ℝ) {x : Ambient N}
    (hx : x ∈ D.Ω) : D.lift f x = f ⟨x, subset_closure hx⟩ := by
  simp [lift, subset_closure hx]

theorem lift_apply_of_not_mem_closure (f : D.Point → ℝ) {x : Ambient N}
    (hx : x ∉ closure D.Ω) : D.lift f x = 0 := by
  simp [lift, hx]

@[simp] theorem lift_zero : D.lift (fun _ : D.Point => 0) = 0 := by
  funext x
  by_cases hx : x ∈ closure D.Ω <;> simp [lift, hx]

theorem lift_add (f g : D.Point → ℝ) :
    D.lift (fun x => f x + g x) = fun x => D.lift f x + D.lift g x := by
  funext x
  by_cases hx : x ∈ closure D.Ω <;> simp [lift, hx]

theorem lift_neg (f : D.Point → ℝ) :
    D.lift (fun x => -f x) = fun x => -D.lift f x := by
  funext x
  by_cases hx : x ∈ closure D.Ω <;> simp [lift, hx]

theorem lift_sub (f g : D.Point → ℝ) :
    D.lift (fun x => f x - g x) = fun x => D.lift f x - D.lift g x := by
  funext x
  by_cases hx : x ∈ closure D.Ω <;> simp [lift, hx]

theorem lift_const_mul (c : ℝ) (f : D.Point → ℝ) :
    D.lift (fun x => c * f x) = fun x => c * D.lift f x := by
  funext x
  by_cases hx : x ∈ closure D.Ω <;> simp [lift, hx]

/-! ## Finiteness and constants -/

theorem domainMeasure_univ :
    D.domainMeasure Set.univ = volume D.Ω := by
  simp [domainMeasure]

@[simp] theorem domainMeasure_real_univ :
    D.domainMeasure.real Set.univ = D.euclideanDomain.volume := by
  simp [domainMeasure, measureReal_def, euclideanDomain, toBoundedDomainData]

theorem lift_const_ae_eq (c : ℝ) :
    D.lift (fun _ : D.Point => c) =ᵐ[D.domainMeasure] fun _ => c := by
  rw [domainMeasure]
  filter_upwards [ae_restrict_mem D.isOpen_Ω.measurableSet] with x hx
  simp [lift, subset_closure hx]

/-- Integrability of a closed-domain function means integrability of its zero
extension against restricted volume. -/
def DomainIntegrable (f : D.Point → ℝ) : Prop :=
  MeasureTheory.Integrable (D.lift f) D.domainMeasure

theorem domainIntegrable_const (c : ℝ) :
    D.DomainIntegrable (fun _ : D.Point => c) := by
  exact (integrable_const c).congr (D.lift_const_ae_eq c).symm

@[simp] theorem integral_zero : D.integral (fun _ : D.Point => 0) = 0 := by
  simp [integral, lift_zero]

/-- The abstract volume field is exactly the restricted Lebesgue volume. -/
theorem integral_const (c : ℝ) :
    D.integral (fun _ : D.Point => c) = D.euclideanDomain.volume * c := by
  unfold integral
  rw [integral_congr_ae (D.lift_const_ae_eq c)]
  rw [MeasureTheory.integral_const]
  simp [domainMeasure_real_univ, smul_eq_mul, euclideanDomain,
    toBoundedDomainData, mul_comm]

/-! ## Linearity and order -/

theorem domainIntegrable_add {f g : D.Point → ℝ}
    (hf : D.DomainIntegrable f) (hg : D.DomainIntegrable g) :
    D.DomainIntegrable (fun x => f x + g x) := by
  unfold DomainIntegrable at *
  rw [D.lift_add]
  exact hf.add hg

theorem domainIntegrable_sub {f g : D.Point → ℝ}
    (hf : D.DomainIntegrable f) (hg : D.DomainIntegrable g) :
    D.DomainIntegrable (fun x => f x - g x) := by
  unfold DomainIntegrable at *
  rw [D.lift_sub]
  exact hf.sub hg

theorem integral_add {f g : D.Point → ℝ}
    (hf : D.DomainIntegrable f) (hg : D.DomainIntegrable g) :
    D.integral (fun x => f x + g x) = D.integral f + D.integral g := by
  unfold integral DomainIntegrable at *
  rw [D.lift_add, MeasureTheory.integral_add hf hg]

theorem integral_neg (f : D.Point → ℝ) :
    D.integral (fun x => -f x) = -D.integral f := by
  unfold integral
  rw [D.lift_neg, MeasureTheory.integral_neg]

theorem integral_sub {f g : D.Point → ℝ}
    (hf : D.DomainIntegrable f) (hg : D.DomainIntegrable g) :
    D.integral (fun x => f x - g x) = D.integral f - D.integral g := by
  unfold integral DomainIntegrable at *
  rw [D.lift_sub, MeasureTheory.integral_sub hf hg]

theorem integral_const_mul (c : ℝ) (f : D.Point → ℝ) :
    D.integral (fun x => c * f x) = c * D.integral f := by
  unfold integral
  rw [D.lift_const_mul, MeasureTheory.integral_const_mul]

theorem integral_mono {f g : D.Point → ℝ}
    (hf : D.DomainIntegrable f) (hg : D.DomainIntegrable g)
    (hfg : ∀ x : D.Point, x ∈ D.euclideanDomain.inside → f x ≤ g x) :
    D.integral f ≤ D.integral g := by
  unfold integral DomainIntegrable at *
  apply MeasureTheory.integral_mono_ae hf hg
  rw [domainMeasure]
  filter_upwards [ae_restrict_mem D.isOpen_Ω.measurableSet] with x hx
  have hxc : x ∈ closure D.Ω := subset_closure hx
  simpa [lift, hxc] using hfg ⟨x, hxc⟩ hx

theorem integral_nonneg {f : D.Point → ℝ}
    (hf : ∀ x : D.Point, x ∈ D.euclideanDomain.inside → 0 ≤ f x) :
    0 ≤ D.integral f := by
  unfold integral
  apply MeasureTheory.integral_nonneg_of_ae
  rw [domainMeasure]
  filter_upwards [ae_restrict_mem D.isOpen_Ω.measurableSet] with x hx
  have hxc : x ∈ closure D.Ω := subset_closure hx
  simpa [lift, hxc] using hf ⟨x, hxc⟩ hx

theorem integral_nonneg_of_pointwise {f : D.Point → ℝ}
    (hf : ∀ x : D.Point, 0 ≤ f x) : 0 ≤ D.integral f :=
  D.integral_nonneg fun x _hx => hf x

/-- The all-points form in the exact abstract-record shape consumed by the
Paper3 Lyapunov utilities. -/
theorem euclideanDomain_integral_nonneg (f : D.Point → ℝ)
    (hf : ∀ x : D.Point, 0 ≤ f x) :
    0 ≤ D.euclideanDomain.integral f :=
  D.integral_nonneg_of_pointwise hf

@[simp] theorem euclideanDomain_integral_const (c : ℝ) :
    D.euclideanDomain.integral (fun _ : D.Point => c) =
      D.euclideanDomain.volume * c :=
  D.integral_const c

end EuclideanDomainData
end ShenWork.EuclideanDomain

end
