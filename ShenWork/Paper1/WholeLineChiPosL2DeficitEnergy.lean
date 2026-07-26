import ShenWork.Paper1.WholeLineChiPosL2SpectralCoercivity

/-!
# Localized L² deficit energy on the far left

Write `p = q - 1` for the raw deficit and localize it as `f = η p`, where
`η²` is the scalar cutoff weight.  This module supplies three pieces needed
for the far-left energy argument:

* the exact identity `E[f] = 1/2 ∫ η² |p|²`;
* differentiation of `E` from an actual `L²`-valued trajectory derivative;
* the coercive energy inequality with every non-linear, cutoff-derivative,
  and nonlocal commutator contribution isolated in an edge production.

The pointwise cutoff computation records the derivatives
`fₓ = η' p + η pₓ` and
`fₓₓ = η'' p + 2η' pₓ + η pₓₓ`.  Thus the explicit residual consists of
`η nonlinear`, the two cutoff-derivative errors, the co-moving cutoff error,
and the resolver commutator `χ(localizedPsi - η psi)`.
-/

open MeasureTheory Real
open scoped FourierTransform ComplexInnerProductSpace ENNReal

noncomputable section

namespace ShenWork.Paper1

/-- Half the squared physical `L²` norm of a Schwartz deficit. -/
def farLeftL2DeficitEnergy (p : SchwartzMap ℝ ℂ) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : ℝ, ‖p x‖ ^ 2

/-- The real `L²` pairing of a deficit with its time velocity. -/
def farLeftL2DeficitProduction
    (p pt : SchwartzMap ℝ ℂ) : ℝ :=
  (inner ℂ (p.toLp 2) (pt.toLp 2)).re

/-- The part of the energy production left after adding back the full
co-moving linear quadratic form.  For a localized PDE slice this contains
exactly the nonlinear, cutoff-edge, and resolver-commutator terms. -/
def farLeftL2EdgeProduction
    (chi c : ℝ) (p pt : SchwartzMap ℝ ℂ) : ℝ :=
    farLeftL2DeficitProduction p pt +
    farLeftL2QuadraticForm chi c p

/-- Plancherel-compatible identification of the squared `L²` norm of a
Schwartz function with its pointwise norm-square integral. -/
theorem schwartz_norm_toLp_two_sq
    (p : SchwartzMap ℝ ℂ) :
    ‖p.toLp 2‖ ^ 2 = ∫ x : ℝ, ‖p x‖ ^ 2 := by
  rw [SchwartzMap.norm_toLp' (p := (2 : ℝ≥0∞))
    (by norm_num) (by norm_num)]
  norm_num
  rw [← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)

/-- The deficit energy is one half of the squared `Lp 2` norm. -/
theorem farLeftL2DeficitEnergy_eq_half_norm_sq
    (p : SchwartzMap ℝ ℂ) :
    farLeftL2DeficitEnergy p =
      (1 / 2 : ℝ) * ‖p.toLp 2‖ ^ 2 := by
  rw [schwartz_norm_toLp_two_sq]
  rfl

/-- The localized deficit energy is nonnegative. -/
theorem farLeftL2DeficitEnergy_nonneg
    (p : SchwartzMap ℝ ℂ) :
    0 ≤ farLeftL2DeficitEnergy p := by
  unfold farLeftL2DeficitEnergy
  exact mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _)

/-- If `f = ηp`, then the localized energy has weight `η²`. -/
theorem farLeftL2DeficitEnergy_eq_weighted
    (f : SchwartzMap ℝ ℂ) (eta : ℝ → ℝ) (p : ℝ → ℂ)
    (hf : ∀ x, f x = (eta x : ℂ) * p x) :
    farLeftL2DeficitEnergy f =
      (1 / 2 : ℝ) *
        ∫ x : ℝ, eta x ^ 2 * ‖p x‖ ^ 2 := by
  unfold farLeftL2DeficitEnergy
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  rw [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

/-- A Schwartz-valued deficit trajectory together with its genuine derivative
in physical `L²`. -/
structure FarLeftL2DeficitEvolution where
  profile : ℝ → SchwartzMap ℝ ℂ
  velocity : ℝ → SchwartzMap ℝ ℂ
  l2_deriv : ∀ t, HasDerivAt
    (fun s => (profile s).toLp 2)
    ((velocity t).toLp 2) t

namespace FarLeftL2DeficitEvolution

variable (H : FarLeftL2DeficitEvolution)

/-- The derivative of the deficit energy is the real `L²` production pairing. -/
theorem energy_hasDerivAt (t : ℝ) :
    HasDerivAt
      (fun s => farLeftL2DeficitEnergy (H.profile s))
      (farLeftL2DeficitProduction (H.profile t) (H.velocity t)) t := by
  letI : InnerProductSpace ℝ (Lp (α := ℝ) ℂ 2) :=
    InnerProductSpace.rclikeToReal ℂ _
  have h := (H.l2_deriv t).norm_sq.const_mul (1 / 2 : ℝ)
  have hfun :
      (fun s => (1 / 2 : ℝ) * ‖(H.profile s).toLp 2‖ ^ 2) =
        fun s => farLeftL2DeficitEnergy (H.profile s) := by
    funext s
    rw [farLeftL2DeficitEnergy_eq_half_norm_sq]
  rw [hfun] at h
  convert h using 1
  rw [real_inner_eq_re_inner ℂ]
  ring_nf
  change
    (inner ℂ ((H.profile t).toLp 2) ((H.velocity t).toLp 2)).re =
      (inner ℂ ((H.profile t).toLp 2) ((H.velocity t).toLp 2)).re
  rfl

/-- Exact separation of the linear spectral dissipation from edge production. -/
theorem energy_production_split (chi c t : ℝ) :
    farLeftL2DeficitProduction (H.profile t) (H.velocity t) =
      -farLeftL2QuadraticForm chi c (H.profile t) +
        farLeftL2EdgeProduction chi c (H.profile t) (H.velocity t) := by
  unfold farLeftL2EdgeProduction
  ring

/-- The landed spectral gap converts the exact split into the localized
energy inequality
`E' ≤ -2 (2√χ - χ) E + edge`. -/
theorem energy_dissipation_le
    {chi : ℝ} (hchi : 0 < chi) (hchi4 : chi < 4)
    (c t : ℝ) :
    farLeftL2DeficitProduction (H.profile t) (H.velocity t) ≤
      -2 * farLeftL2Gap chi *
          farLeftL2DeficitEnergy (H.profile t) +
        farLeftL2EdgeProduction chi c (H.profile t) (H.velocity t) := by
  have hcoer :=
    (ShenWork.Paper1.farLeftL2_quadratic_coercivity
      hchi hchi4 c (H.profile t)).2
  rw [farLeftL2DeficitEnergy_eq_half_norm_sq]
  rw [schwartz_norm_toLp_two_sq]
  have hsplit := H.energy_production_split chi c t
  nlinarith

end FarLeftL2DeficitEvolution

/-- The explicit pointwise residual created by localizing the deficit PDE
with `f = ηp`. -/
def farLeftL2CutoffResidual
    (chi c : ℝ)
    (eta eta' eta'' p px nonlinear psi localizedPsi : ℝ → ℝ) :
    ℝ → ℝ :=
  fun x =>
    eta x * nonlinear x -
      2 * eta' x * px x - eta'' x * p x - c * eta' x * p x +
      chi * (localizedPsi x - eta x * psi x)

/-- Algebraic hypotheses for one localized PDE time slice.  The resolver
output for `p` is `psi`; the output used by the localized equation is
`localizedPsi`. -/
structure FarLeftL2CutoffSlice
    (chi c : ℝ)
    (eta eta' eta'' p px pxx pt psi localizedPsi nonlinear
      f fx fxx ft : ℝ → ℝ) : Prop where
  f_eq : ∀ x : ℝ, f x = eta x * p x
  fx_eq : ∀ x : ℝ, fx x = eta' x * p x + eta x * px x
  fxx_eq : ∀ x : ℝ,
    fxx x = eta'' x * p x + 2 * eta' x * px x + eta x * pxx x
  ft_eq : ∀ x : ℝ, ft x = eta x * pt x
  raw_pde : ∀ x : ℝ,
    pt x = pxx x + c * px x + (chi - 1) * p x -
      chi * psi x + nonlinear x

namespace FarLeftL2CutoffSlice

variable {chi c : ℝ}
  {eta eta' eta'' p px pxx pt psi localizedPsi nonlinear
    f fx fxx ft : ℝ → ℝ}
  (S : FarLeftL2CutoffSlice chi c eta eta' eta''
    p px pxx pt psi localizedPsi nonlinear f fx fxx ft)

include S

/-- Exact localized deficit equation, with all edge terms retained. -/
theorem localized_deficit_equation (x : ℝ) :
    ft x =
      fxx x + c * fx x + (chi - 1) * f x -
        chi * localizedPsi x +
        farLeftL2CutoffResidual chi c eta eta' eta''
          p px nonlinear psi localizedPsi x := by
  rw [S.ft_eq, S.raw_pde, S.fxx_eq, S.fx_eq, S.f_eq]
  unfold farLeftL2CutoffResidual
  ring

end FarLeftL2CutoffSlice

/-- Absolute pointwise control of the cutoff residual.  This exhibits the
`η'`, `η''`, nonlinear, and resolver-commutator errors separately. -/
theorem farLeftL2CutoffResidual_abs_le
    {chi c : ℝ} (hchi : 0 ≤ chi)
    (eta eta' eta'' p px nonlinear psi localizedPsi : ℝ → ℝ)
    (x : ℝ) :
    |farLeftL2CutoffResidual chi c eta eta' eta''
        p px nonlinear psi localizedPsi x| ≤
      |eta x| * |nonlinear x| +
        2 * |eta' x| * |px x| +
        |eta'' x| * |p x| +
        |c| * |eta' x| * |p x| +
        chi * |localizedPsi x - eta x * psi x| := by
  unfold farLeftL2CutoffResidual
  calc
    |eta x * nonlinear x -
        2 * eta' x * px x - eta'' x * p x - c * eta' x * p x +
        chi * (localizedPsi x - eta x * psi x)| ≤
      |eta x * nonlinear x| +
        |-(2 * eta' x * px x)| +
        |-(eta'' x * p x)| +
        |-(c * eta' x * p x)| +
        |chi * (localizedPsi x - eta x * psi x)| := by
      calc
        |eta x * nonlinear x -
            2 * eta' x * px x - eta'' x * p x - c * eta' x * p x +
            chi * (localizedPsi x - eta x * psi x)| ≤
          |eta x * nonlinear x -
            2 * eta' x * px x - eta'' x * p x - c * eta' x * p x| +
            |chi * (localizedPsi x - eta x * psi x)| := abs_add_le _ _
        _ ≤
          (|eta x * nonlinear x -
            2 * eta' x * px x - eta'' x * p x| +
            |-(c * eta' x * p x)|) +
            |chi * (localizedPsi x - eta x * psi x)| := by
          gcongr
          simpa only [sub_eq_add_neg] using abs_add_le
            (eta x * nonlinear x -
              2 * eta' x * px x - eta'' x * p x)
            (-(c * eta' x * p x))
        _ ≤
          ((|eta x * nonlinear x - 2 * eta' x * px x| +
            |-(eta'' x * p x)|) +
            |-(c * eta' x * p x)|) +
            |chi * (localizedPsi x - eta x * psi x)| := by
          gcongr
          simpa only [sub_eq_add_neg] using abs_add_le
            (eta x * nonlinear x - 2 * eta' x * px x)
            (-(eta'' x * p x))
        _ ≤
          (((|eta x * nonlinear x| + |-(2 * eta' x * px x)|) +
            |-(eta'' x * p x)|) +
            |-(c * eta' x * p x)|) +
            |chi * (localizedPsi x - eta x * psi x)| := by
          gcongr
          simpa only [sub_eq_add_neg] using abs_add_le
            (eta x * nonlinear x) (-(2 * eta' x * px x))
        _ = _ := by ring
    _ = _ := by
      simp only [abs_neg, abs_mul, abs_of_nonneg hchi]
      norm_num

section AxiomAudit

#print axioms schwartz_norm_toLp_two_sq
#print axioms farLeftL2DeficitEnergy_eq_weighted
#print axioms FarLeftL2DeficitEvolution.energy_hasDerivAt
#print axioms FarLeftL2DeficitEvolution.energy_production_split
#print axioms FarLeftL2DeficitEvolution.energy_dissipation_le
#print axioms FarLeftL2CutoffSlice.localized_deficit_equation
#print axioms farLeftL2CutoffResidual_abs_le

end AxiomAudit

end ShenWork.Paper1
