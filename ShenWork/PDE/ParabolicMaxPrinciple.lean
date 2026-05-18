import Mathlib

/-!
# ShenWork/PDE/ParabolicMaxPrinciple.lean

A Lean framework for the one-dimensional classical parabolic maximum principle
and the comparison theorem used for scalar reaction-diffusion equations.

The key analytic maximum-principle argument is isolated in
`weak_maximum_principle_linear` and marked with `sorry`.  The comparison theorem
itself is then proved from this weak maximum principle.
-/

noncomputable section

open Set
open scoped Topology

namespace ShenWork
namespace PDE
namespace ParabolicMaxPrinciple

/-- Time derivative of a function `u t x`. -/
def dt (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  deriv (fun τ : ℝ => u τ x) t

/-- First spatial derivative of a function `u t x`. -/
def dx (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  deriv (fun y : ℝ => u t y) x

/-- Second spatial derivative of a function `u t x`. -/
def dxx (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  deriv (fun y : ℝ => dx u t y) x

/-- The parabolic operator `∂ₜu - ∂ₓₓu`. -/
def parabolicOp (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  dt u t x - dxx u t x

/-- Boundedness on the finite parabolic strip `[0,T] × ℝ`. -/
def BoundedOnStrip (T : ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, |u t x| ≤ M

/--
A convenient real-line local Lipschitz hypothesis.

For every closed ball `[-R,R]`, there is a Lipschitz constant `L`.
-/
def LocallyLipschitzReal (g : ℝ → ℝ) : Prop :=
  ∀ R : ℝ,
    0 < R →
      ∃ L : ℝ,
        0 ≤ L ∧
          ∀ a b : ℝ,
            |a| ≤ R →
            |b| ≤ R →
            |g a - g b| ≤ L * |a - b|

/--
Classical subsolution of

`uₜ = uₓₓ + g(u)`,

i.e.

`uₜ - uₓₓ ≤ g(u)`.
-/
structure IsClassicalSubSolution
    (g : ℝ → ℝ) (T : ℝ) (u : ℝ → ℝ → ℝ) : Prop where
  time_hasDerivAt :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        HasDerivAt (fun τ : ℝ => u τ x) (dt u t x) t
  space_hasDerivAt :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        HasDerivAt (fun y : ℝ => u t y) (dx u t x) x
  space_second_hasDerivAt :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        HasDerivAt (fun y : ℝ => dx u t y) (dxx u t x) x
  pde_le :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        parabolicOp u t x ≤ g (u t x)
  bounded :
    BoundedOnStrip T u

/--
Classical supersolution of

`uₜ = uₓₓ + g(u)`,

i.e.

`vₜ - vₓₓ ≥ g(v)`.
-/
structure IsClassicalSuperSolution
    (g : ℝ → ℝ) (T : ℝ) (v : ℝ → ℝ → ℝ) : Prop where
  time_hasDerivAt :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        HasDerivAt (fun τ : ℝ => v τ x) (dt v t x) t
  space_hasDerivAt :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        HasDerivAt (fun y : ℝ => v t y) (dx v t x) x
  space_second_hasDerivAt :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        HasDerivAt (fun y : ℝ => dx v t y) (dxx v t x) x
  pde_ge :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        g (v t x) ≤ parabolicOp v t x
  bounded :
    BoundedOnStrip T v

/--
A positive-part linear subsolution.

This is the Lean-friendly form needed for comparison.  It only requires

`wₜ - wₓₓ ≤ c w`

at points where `w > 0`, which is exactly what follows from a two-sided
Lipschitz condition on `g` when `w = u - v`.
-/
structure IsClassicalLinearSubSolution
    (c : ℝ) (T : ℝ) (w : ℝ → ℝ → ℝ) : Prop where
  time_hasDerivAt :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        HasDerivAt (fun τ : ℝ => w τ x) (dt w t x) t
  space_hasDerivAt :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        HasDerivAt (fun y : ℝ => w t y) (dx w t x) x
  space_second_hasDerivAt :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        HasDerivAt (fun y : ℝ => dx w t y) (dxx w t x) x
  pde_le_of_pos :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        0 < w t x →
          parabolicOp w t x ≤ c * w t x
  bounded :
    BoundedOnStrip T w

/--
The exponential barrier

`w̃(t,x) = exp(-λt) w(t,x)`.

For `λ > c`, one obtains a strict inequality at positive maxima.
-/
def expBarrier (lam : ℝ) (w : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  Real.exp (-(lam * t)) * w t x

private def spatialCoercivePerturbation
    (ε : ℝ) (z : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t x => z t x - ε * (1 + x ^ 2)

private lemma dt_expBarrier_of_hasDerivAt
    {lam : ℝ} {w : ℝ → ℝ → ℝ} {t x : ℝ}
    (hw : HasDerivAt (fun τ : ℝ => w τ x) (dt w t x) t) :
    dt (expBarrier lam w) t x =
      Real.exp (-(lam * t)) * (dt w t x - lam * w t x) := by
  have hExp :
      HasDerivAt (fun τ : ℝ => Real.exp (-(lam * τ)))
        (Real.exp (-(lam * t)) * (-lam)) t := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id t).const_mul lam).neg.exp)
  have h := (hExp.mul hw).deriv
  unfold dt expBarrier
  convert h using 1
  · simp [dt]
    ring

private lemma dx_expBarrier_of_hasDerivAt
    {lam : ℝ} {w : ℝ → ℝ → ℝ} {t x : ℝ}
    (hw : HasDerivAt (fun y : ℝ => w t y) (dx w t x) x) :
    dx (expBarrier lam w) t x =
      Real.exp (-(lam * t)) * dx w t x := by
  simpa [dx, expBarrier, mul_comm, mul_left_comm, mul_assoc] using
    ((hasDerivAt_const x (Real.exp (-(lam * t)))).mul hw).deriv

private lemma dxx_expBarrier_of_hasDerivAt
    {lam : ℝ} {w : ℝ → ℝ → ℝ} {t x : ℝ}
    (hw₁ : ∀ y : ℝ,
      HasDerivAt (fun z : ℝ => w t z) (dx w t y) y)
    (hw₂ : HasDerivAt (fun y : ℝ => dx w t y) (dxx w t x) x) :
    dxx (expBarrier lam w) t x =
      Real.exp (-(lam * t)) * dxx w t x := by
  have hdx_fun :
      (fun y : ℝ => dx (expBarrier lam w) t y)
        =
      (fun y : ℝ => Real.exp (-(lam * t)) * dx w t y) := by
    funext y
    exact dx_expBarrier_of_hasDerivAt
      (lam := lam) (w := w) (t := t) (x := y) (hw₁ y)
  simpa [dxx, hdx_fun, mul_comm, mul_left_comm, mul_assoc] using
    ((hasDerivAt_const x (Real.exp (-(lam * t)))).mul hw₂).deriv

private lemma expBarrier_parabolicOp_le_of_pos
    {c T lam : ℝ} {w : ℝ → ℝ → ℝ}
    (hw : IsClassicalLinearSubSolution c T w) :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
      0 < expBarrier lam w t x →
        parabolicOp (expBarrier lam w) t x ≤
          (c - lam) * expBarrier lam w t x := by
  intro t x ht hpos
  have hEpos : 0 < Real.exp (-(lam * t)) := Real.exp_pos _
  have hwpos : 0 < w t x := by
    exact pos_of_mul_pos_right (by simpa [expBarrier] using hpos) hEpos.le
  have hdt :
      dt (expBarrier lam w) t x =
        Real.exp (-(lam * t)) * (dt w t x - lam * w t x) :=
    dt_expBarrier_of_hasDerivAt
      (lam := lam) (w := w) (t := t) (x := x)
      (hw.time_hasDerivAt ht)
  have hdxx :
      dxx (expBarrier lam w) t x =
        Real.exp (-(lam * t)) * dxx w t x :=
    dxx_expBarrier_of_hasDerivAt
      (lam := lam) (w := w) (t := t) (x := x)
      (fun y => hw.space_hasDerivAt (t := t) (x := y) ht)
      (hw.space_second_hasDerivAt ht)
  have hop :
      parabolicOp (expBarrier lam w) t x =
        Real.exp (-(lam * t)) *
          (parabolicOp w t x - lam * w t x) := by
    unfold parabolicOp
    rw [hdt, hdxx]
    ring
  have hpde : parabolicOp w t x ≤ c * w t x :=
    hw.pde_le_of_pos ht hwpos
  calc
    parabolicOp (expBarrier lam w) t x
        = Real.exp (-(lam * t)) *
            (parabolicOp w t x - lam * w t x) := hop
    _ ≤ Real.exp (-(lam * t)) *
            (c * w t x - lam * w t x) := by
          gcongr
    _ = (c - lam) * expBarrier lam w t x := by
          simp [expBarrier]
          ring

private lemma expBarrier_c_add_three_parabolicOp_le
    {c T : ℝ} {w : ℝ → ℝ → ℝ}
    (hw : IsClassicalLinearSubSolution c T w) :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
      0 < expBarrier (c + 3) w t x →
        parabolicOp (expBarrier (c + 3) w) t x ≤
          -3 * expBarrier (c + 3) w t x := by
  intro t x ht hpos
  have h :=
    expBarrier_parabolicOp_le_of_pos
      (c := c) (T := T) (lam := c + 3) (w := w) hw ht hpos
  convert h using 1
  ring

private lemma exists_max_on_Icc_prod
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R)
    {F : ℝ × ℝ → ℝ}
    (hF :
      ContinuousOn F
        (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (-R) R)) :
    ∃ p : ℝ × ℝ,
      p ∈ Set.Icc (0 : ℝ) T ×ˢ Set.Icc (-R) R ∧
      ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ Set.Icc (-R) R,
        F q ≤ F p := by
  have hK :
      IsCompact
        (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (-R) R) :=
    isCompact_Icc.prod isCompact_Icc
  have hne :
      (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (-R) R).Nonempty := by
    refine ⟨(0, 0), ?_⟩
    constructor
    · exact ⟨le_rfl, hT⟩
    · exact ⟨by linarith, hR⟩
  obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn hne hF
  exact ⟨p, hp, fun q hq => hmax hq⟩

private lemma parabolicOp_spatialCoercivePerturbation_eq
    {z : ℝ → ℝ → ℝ} {ε t x : ℝ}
    (hdt : HasDerivAt (fun τ : ℝ => z τ x) (dt z t x) t)
    (hdx : ∀ y : ℝ,
      HasDerivAt (fun r : ℝ => z t r) (dx z t y) y)
    (hdxx : HasDerivAt (fun y : ℝ => dx z t y) (dxx z t x) x) :
    parabolicOp (spatialCoercivePerturbation ε z) t x =
      parabolicOp z t x + 2 * ε := by
  have hdtψ :
      dt (spatialCoercivePerturbation ε z) t x = dt z t x := by
    unfold dt spatialCoercivePerturbation
    simpa using
      (hdt.sub
        (hasDerivAt_const t (ε * (1 + x ^ 2)))).deriv
  have hdxψ_fun :
      (fun y : ℝ => dx (spatialCoercivePerturbation ε z) t y) =
        fun y : ℝ => dx z t y - 2 * ε * y := by
    funext y
    unfold dx spatialCoercivePerturbation
    have hquad :
        HasDerivAt (fun r : ℝ => ε * (1 + r ^ 2)) (2 * ε * y) y := by
      have hinner :
          HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * y) y := by
        have hpow : HasDerivAt (fun r : ℝ => r ^ 2) (2 * y) y := by
          convert ((hasDerivAt_id y).mul (hasDerivAt_id y)) using 1
          · funext r
            simp [Pi.mul_apply, pow_two]
          · simp only [id_eq]
            ring
        convert (hasDerivAt_const (x := y) (c := (1 : ℝ))).add hpow using 1
        ring
      convert hinner.const_mul ε using 1 <;> ring
    simpa [mul_assoc] using ((hdx y).sub hquad).deriv
  have hdxxψ :
      dxx (spatialCoercivePerturbation ε z) t x = dxx z t x - 2 * ε := by
    unfold dxx
    rw [hdxψ_fun]
    have hlin :
        HasDerivAt (fun y : ℝ => 2 * ε * y) (2 * ε) x := by
      simpa [mul_assoc] using (hasDerivAt_id x).const_mul (2 * ε)
    simpa using (hdxx.sub hlin).deriv
  unfold parabolicOp
  rw [hdtψ, hdxxψ]
  ring

private lemma spatialCoercivePerturbation_parabolicOp_lt_of_pos
    {c T ε : ℝ} {w : ℝ → ℝ → ℝ}
    (hε : 0 < ε)
    (hw : IsClassicalLinearSubSolution c T w)
    {t x : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hpos :
      0 < spatialCoercivePerturbation ε
        (expBarrier (c + 3) w) t x) :
    parabolicOp
      (spatialCoercivePerturbation ε (expBarrier (c + 3) w)) t x < 0 := by
  let z : ℝ → ℝ → ℝ := expBarrier (c + 3) w
  have hpos_z : 0 < z t x := by
    dsimp [z, spatialCoercivePerturbation] at hpos
    nlinarith [sq_nonneg x, hε]
  have hε_le_z : ε < z t x := by
    dsimp [z, spatialCoercivePerturbation] at hpos
    nlinarith [sq_nonneg x, hε]
  have hop_z :
      parabolicOp z t x ≤ -3 * z t x := by
    exact expBarrier_c_add_three_parabolicOp_le
      (c := c) (T := T) (w := w) hw ht (by simpa [z] using hpos_z)
  have hop :
      parabolicOp
        (spatialCoercivePerturbation ε (expBarrier (c + 3) w)) t x =
        parabolicOp z t x + 2 * ε := by
    have hdt_z :
        HasDerivAt (fun τ : ℝ => z τ x) (dt z t x) t := by
      have hExp :
          HasDerivAt (fun τ : ℝ => Real.exp (-((c + 3) * τ)))
            (Real.exp (-((c + 3) * t)) * (-(c + 3))) t := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (((hasDerivAt_id t).const_mul (c + 3)).neg.exp)
      have hprod :
          HasDerivAt (fun τ : ℝ => Real.exp (-((c + 3) * τ)) * w τ x)
            (Real.exp (-((c + 3) * t)) * (-(c + 3)) * w t x +
              Real.exp (-((c + 3) * t)) * dt w t x) t := by
        simpa [Pi.mul_apply] using hExp.mul (hw.time_hasDerivAt (t := t) (x := x) ht)
      unfold z dt expBarrier
      convert hprod using 1
      exact hprod.deriv
    have hdx_z :
        ∀ y : ℝ, HasDerivAt (fun r : ℝ => z t r) (dx z t y) y := by
      intro y
      have hprod :
          HasDerivAt
            (fun r : ℝ => Real.exp (-((c + 3) * t)) * w t r)
            (Real.exp (-((c + 3) * t)) * dx w t y) y := by
        simpa [Pi.mul_apply] using
          (hasDerivAt_const y (Real.exp (-((c + 3) * t)))).mul
            (hw.space_hasDerivAt (t := t) (x := y) ht)
      unfold z dx expBarrier
      convert hprod using 1
      exact hprod.deriv
    have hdxx_z :
        HasDerivAt (fun y : ℝ => dx z t y) (dxx z t x) x := by
      have hdx_fun :
          (fun y : ℝ => dx z t y) =
            fun y : ℝ => Real.exp (-((c + 3) * t)) * dx w t y := by
        funext y
        exact dx_expBarrier_of_hasDerivAt
          (lam := c + 3) (w := w) (t := t) (x := y)
          (hw.space_hasDerivAt (t := t) (x := y) ht)
      have hder :
          HasDerivAt
            (fun y : ℝ => Real.exp (-((c + 3) * t)) * dx w t y)
            (Real.exp (-((c + 3) * t)) * dxx w t x) x := by
        simpa [Pi.mul_apply] using
          (hasDerivAt_const x (Real.exp (-((c + 3) * t)))).mul
            (hw.space_second_hasDerivAt (t := t) (x := x) ht)
      have hder_z :
          HasDerivAt (fun y : ℝ => dx z t y)
            (Real.exp (-((c + 3) * t)) * dxx w t x) x := by
        simpa [hdx_fun] using hder
      convert hder_z using 1
      simpa [z] using dxx_expBarrier_of_hasDerivAt
        (lam := c + 3) (w := w) (t := t) (x := x)
        (fun y => hw.space_hasDerivAt (t := t) (x := y) ht)
        (hw.space_second_hasDerivAt (t := t) (x := x) ht)
    exact parabolicOp_spatialCoercivePerturbation_eq
      (z := z) (ε := ε) (t := t) (x := x)
      hdt_z hdx_z hdxx_z
  rw [hop]
  nlinarith

private lemma dt_eq_zero_at_space_time_global_max
    {ψ : ℝ → ℝ → ℝ} {t₀ x₀ : ℝ}
    (hdt : HasDerivAt (fun τ : ℝ => ψ τ x₀) (dt ψ t₀ x₀) t₀)
    (hmax : ∀ t x : ℝ, ψ t x ≤ ψ t₀ x₀) :
    dt ψ t₀ x₀ = 0 := by
  have hloc : IsLocalMax (fun τ : ℝ => ψ τ x₀) t₀ :=
    Filter.Eventually.of_forall fun τ => hmax τ x₀
  exact hloc.hasDerivAt_eq_zero hdt

private lemma dx_eq_zero_at_space_time_global_max
    {ψ : ℝ → ℝ → ℝ} {t₀ x₀ : ℝ}
    (hdx : HasDerivAt (fun y : ℝ => ψ t₀ y) (dx ψ t₀ x₀) x₀)
    (hmax : ∀ t x : ℝ, ψ t x ≤ ψ t₀ x₀) :
    dx ψ t₀ x₀ = 0 := by
  have hloc : IsLocalMax (fun y : ℝ => ψ t₀ y) x₀ :=
    Filter.Eventually.of_forall fun y => hmax t₀ y
  exact hloc.hasDerivAt_eq_zero hdx

private lemma parabolicOp_nonneg_at_max_derivative_signs
    {ψ : ℝ → ℝ → ℝ} {t x : ℝ}
    (hdt : 0 ≤ dt ψ t x)
    (hdxx : dxx ψ t x ≤ 0) :
    0 ≤ parabolicOp ψ t x := by
  unfold parabolicOp
  linarith

private lemma spatialCoercivePerturbation_no_positive_max_with_derivative_signs
    {c T ε : ℝ} {w : ℝ → ℝ → ℝ}
    (hε : 0 < ε)
    (hw : IsClassicalLinearSubSolution c T w)
    {t x : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hpos :
      0 < spatialCoercivePerturbation ε
        (expBarrier (c + 3) w) t x)
    (hdt :
      0 ≤ dt
        (spatialCoercivePerturbation ε (expBarrier (c + 3) w)) t x)
    (hdxx :
      dxx
        (spatialCoercivePerturbation ε (expBarrier (c + 3) w)) t x ≤ 0) :
    False := by
  have hneg :=
    spatialCoercivePerturbation_parabolicOp_lt_of_pos
      (c := c) (T := T) (ε := ε) (w := w) hε hw ht hpos
  have hnonneg :=
    parabolicOp_nonneg_at_max_derivative_signs
      (ψ := spatialCoercivePerturbation ε (expBarrier (c + 3) w))
      (t := t) (x := x) hdt hdxx
  linarith

private lemma spatialCoercivePerturbation_initial_neg
    {c ε : ℝ} {w : ℝ → ℝ → ℝ}
    (hε : 0 < ε)
    (hinit : ∀ x : ℝ, w 0 x ≤ 0)
    (x : ℝ) :
    spatialCoercivePerturbation ε (expBarrier (c + 3) w) 0 x < 0 := by
  unfold spatialCoercivePerturbation expBarrier
  simp only [mul_zero, neg_zero, Real.exp_zero, one_mul]
  have hquad : 0 ≤ x ^ 2 := sq_nonneg x
  have hw0 : w 0 x ≤ 0 := hinit x
  nlinarith

private lemma expBarrier_le_on_strip_of_bounded
    {c T M : ℝ} {w : ℝ → ℝ → ℝ}
    (hT : 0 ≤ T)
    (hM : 0 ≤ M)
    (hw : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, |w t x| ≤ M) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ,
      expBarrier (c + 3) w t x ≤ Real.exp (|c + 3| * T) * M := by
  intro t ht x
  have ht0 : 0 ≤ t := ht.1
  have htT : t ≤ T := ht.2
  have hexp_le :
      Real.exp (-((c + 3) * t)) ≤ Real.exp (|c + 3| * T) := by
    apply Real.exp_le_exp.mpr
    have hneg_le_abs : -(c + 3) ≤ |c + 3| := neg_le_abs (c + 3)
    have habs_nonneg : 0 ≤ |c + 3| := abs_nonneg (c + 3)
    calc
      -((c + 3) * t) = (-(c + 3)) * t := by ring
      _ ≤ |c + 3| * t := mul_le_mul_of_nonneg_right hneg_le_abs ht0
      _ ≤ |c + 3| * T := mul_le_mul_of_nonneg_left htT habs_nonneg
  have hw_le : w t x ≤ M := by
    exact (le_abs_self (w t x)).trans (hw t ht x)
  have hMexp_nonneg : 0 ≤ Real.exp (-((c + 3) * t)) :=
    (Real.exp_pos _).le
  calc
    expBarrier (c + 3) w t x
        = Real.exp (-((c + 3) * t)) * w t x := rfl
    _ ≤ Real.exp (-((c + 3) * t)) * M :=
        mul_le_mul_of_nonneg_left hw_le hMexp_nonneg
    _ ≤ Real.exp (|c + 3| * T) * M :=
        mul_le_mul_of_nonneg_right hexp_le hM

private lemma spatialCoercivePerturbation_neg_of_barrier_lt
    {c ε B t x : ℝ} {w : ℝ → ℝ → ℝ}
    (hz_le : expBarrier (c + 3) w t x ≤ B)
    (hB : B < ε * (1 + x ^ 2)) :
    spatialCoercivePerturbation ε (expBarrier (c + 3) w) t x < 0 := by
  unfold spatialCoercivePerturbation
  linarith

private lemma spatialCoercivePerturbation_neg_on_large_spatial_boundary
    {c T M ε R : ℝ} {w : ℝ → ℝ → ℝ}
    (hT : 0 ≤ T)
    (hM : 0 ≤ M)
    (hε : 0 < ε)
    (hw : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, |w t x| ≤ M)
    (hR : Real.exp (|c + 3| * T) * M < ε * (1 + R ^ 2)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      spatialCoercivePerturbation ε (expBarrier (c + 3) w) t R < 0 ∧
      spatialCoercivePerturbation ε (expBarrier (c + 3) w) t (-R) < 0 := by
  intro t ht
  have hbound :=
    expBarrier_le_on_strip_of_bounded
      (c := c) (T := T) (M := M) (w := w) hT hM hw t ht
  constructor
  · exact spatialCoercivePerturbation_neg_of_barrier_lt
      (c := c) (ε := ε) (B := Real.exp (|c + 3| * T) * M)
      (w := w) (t := t) (x := R) (hbound R) hR
  · have hRneg :
        Real.exp (|c + 3| * T) * M < ε * (1 + (-R) ^ 2) := by
      simpa using hR
    exact spatialCoercivePerturbation_neg_of_barrier_lt
      (c := c) (ε := ε) (B := Real.exp (|c + 3| * T) * M)
      (w := w) (t := t) (x := -R) (hbound (-R)) hRneg

private lemma spatialCoercivePerturbation_pos_not_on_parabolic_boundary
    {c T ε R : ℝ} {w : ℝ → ℝ → ℝ}
    (hε : 0 < ε)
    (hinit : ∀ x : ℝ, w 0 x ≤ 0)
    (hside :
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        spatialCoercivePerturbation ε (expBarrier (c + 3) w) t R < 0 ∧
        spatialCoercivePerturbation ε (expBarrier (c + 3) w) t (-R) < 0)
    {p : ℝ × ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) T ×ˢ Set.Icc (-R) R)
    (hpos :
      0 < spatialCoercivePerturbation ε
        (expBarrier (c + 3) w) p.1 p.2) :
    p.1 ≠ 0 ∧ p.2 ≠ R ∧ p.2 ≠ -R := by
  constructor
  · intro ht0
    have hneg :=
      spatialCoercivePerturbation_initial_neg
        (c := c) (ε := ε) (w := w) hε hinit p.2
    have hpos0 :
        0 < spatialCoercivePerturbation ε
          (expBarrier (c + 3) w) 0 p.2 := by
      simpa [ht0] using hpos
    exact (not_lt_of_ge (le_of_lt hneg)) hpos0
  constructor
  · intro hxR
    have hneg := (hside p.1 hp.1).1
    have hposR :
        0 < spatialCoercivePerturbation ε
          (expBarrier (c + 3) w) p.1 R := by
      simpa [hxR] using hpos
    exact (not_lt_of_ge (le_of_lt hneg)) hposR
  · intro hxR
    have hneg := (hside p.1 hp.1).2
    have hposR :
        0 < spatialCoercivePerturbation ε
          (expBarrier (c + 3) w) p.1 (-R) := by
      simpa [hxR] using hpos
    exact (not_lt_of_ge (le_of_lt hneg)) hposR

private lemma spatialCoercivePerturbation_pos_has_positive_time_and_interior_space
    {c T ε R : ℝ} {w : ℝ → ℝ → ℝ}
    (hε : 0 < ε)
    (hinit : ∀ x : ℝ, w 0 x ≤ 0)
    (hside :
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        spatialCoercivePerturbation ε (expBarrier (c + 3) w) t R < 0 ∧
        spatialCoercivePerturbation ε (expBarrier (c + 3) w) t (-R) < 0)
    {p : ℝ × ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) T ×ˢ Set.Icc (-R) R)
    (hpos :
      0 < spatialCoercivePerturbation ε
        (expBarrier (c + 3) w) p.1 p.2) :
    0 < p.1 ∧ p.2 ∈ Set.Ioo (-R) R := by
  have hnot :=
    spatialCoercivePerturbation_pos_not_on_parabolic_boundary
      (c := c) (T := T) (ε := ε) (R := R) (w := w)
      hε hinit hside hp hpos
  constructor
  · exact lt_of_le_of_ne hp.1.1 (Ne.symm hnot.1)
  · exact
      ⟨lt_of_le_of_ne hp.2.1 (Ne.symm hnot.2.2),
        lt_of_le_of_ne hp.2.2 hnot.2.1⟩

/--
Weak parabolic maximum principle on the whole line.

If `w` is bounded on `[0,T] × ℝ`, satisfies

`wₜ - wₓₓ ≤ c w`

at positive points, and `w(0,x) ≤ 0`, then `w ≤ 0` on the strip.

Proof idea:

1. Choose `λ > c`.
2. Let `z(t,x) = exp(-λt) w(t,x)`.
3. Then, at positive points,

   `zₜ - zₓₓ ≤ (c - λ) z < 0`.

4. Add a spatial coercive barrier, for example

   `zε(t,x) = z(t,x) - ε * (1 + t + x^2)`,

   so that `zε → -∞` as `|x| → ∞`.
5. If `zε` had a positive maximum in `(0,T] × ℝ`, then at the maximum
   one has `zεₜ ≥ 0` and `zεₓₓ ≤ 0`, contradicting the strict inequality.
6. Let `ε → 0`.

This is the only genuinely hard analytic maximum-principle step.
-/
private lemma le_zero_of_forall_pos_le_mul {z A : ℝ} (hA : 0 ≤ A)
    (h : ∀ ε : ℝ, 0 < ε → z ≤ ε * A) : z ≤ 0 := by
  by_contra hz
  push_neg at hz
  by_cases hA0 : A = 0
  · linarith [h 1 one_pos, hA0]
  · have hA_pos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
    have := h (z / (2 * A)) (div_pos hz (by positivity))
    have : z / (2 * A) * A = z / 2 := by field_simp
    linarith

/-- Core barrier estimate: for all ε > 0, exp(-(c+3)t)*w(t,x) ≤ ε*(1+x²).

Proof sketch (exponential barrier + spatial coercion):
1. Let z(t,x) = exp(-(c+3)t)*w(t,x). At positive points: z_t - z_xx ≤ -3z.
2. For ε > 0, let ψ(t,x) = z(t,x) - ε*(1+t+x²). Then ψ → -∞ as |x| → ∞.
3. At t=0: ψ(0,x) = w(0,x) - ε*(1+x²) ≤ -ε < 0.
4. If ψ > 0 somewhere, max at interior (t₀,x₀) with t₀ > 0:
   ψ_t ≥ 0, ψ_xx ≤ 0, so 0 ≤ ψ_t - ψ_xx = (z_t - z_xx) - ε + 2ε ≤ -3z + ε.
   Since z > ε*(1+t₀+x₀²) ≥ ε: -3z + ε < -3ε + ε = -2ε < 0. Contradiction.
5. So ψ ≤ 0, i.e., z ≤ ε*(1+t+x²) ≤ ε*(1+T+x²). In particular z ≤ ε*(1+x²)
   after adjusting the barrier constant.

This is the irreducible analytic step — needs compactness on truncated domain
and interior max characterization (∂_t ≥ 0, ∂_xx ≤ 0 at spatial max). -/
private theorem coercive_exponential_barrier_estimate
    {c T : ℝ} {w : ℝ → ℝ → ℝ}
    (_hT : 0 < T) (_hc : 0 ≤ c)
    (_hw : IsClassicalLinearSubSolution c T w)
    (_hinit : ∀ x : ℝ, w 0 x ≤ 0) :
    ∀ ε : ℝ, 0 < ε →
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ,
        expBarrier (c + 3) w t x ≤ ε * (1 + x ^ 2) := by
  intro ε hε t ht x
  suffices h : spatialCoercivePerturbation ε (expBarrier (c + 3) w) t x ≤ 0 by
    simp only [spatialCoercivePerturbation] at h; linarith
  obtain ⟨M, hM_nn, hM⟩ := _hw.bounded
  -- Choose R large enough for boundary conditions
  set B := Real.exp (|c + 3| * T) * M
  have hB_nn : 0 ≤ B := mul_nonneg (Real.exp_nonneg _) hM_nn
  -- Need R s.t. B < ε * (1 + R²) and |x| ≤ R
  set R := max (|x| + 1) (Real.sqrt ((B / ε) + 1) + 1)
  have hR_pos : 0 < R := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hxR : |x| < R := by linarith [le_max_left (|x| + 1) (Real.sqrt ((B / ε) + 1) + 1)]
  have hR_large : B < ε * (1 + R ^ 2) := by sorry
  -- On the rectangle [0,T]×[-R,R], ψ is continuous and achieves max
  -- ψ < 0 on boundary (t=0, x=±R)
  -- If ψ(t,x) > 0, max on rectangle is positive and at interior point
  -- At interior max: dt ≥ 0, dxx ≤ 0 → contradiction
  sorry

theorem weak_maximum_principle_linear
    {c T : ℝ} {w : ℝ → ℝ → ℝ}
    (hT : 0 < T)
    (hc : 0 ≤ c)
    (hw : IsClassicalLinearSubSolution c T w)
    (hinit : ∀ x : ℝ, w 0 x ≤ 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, w t x ≤ 0 := by
  have hbar := coercive_exponential_barrier_estimate hT hc hw hinit
  intro t ht x
  have hA : 0 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hz : expBarrier (c + 3) w t x ≤ 0 :=
    le_zero_of_forall_pos_le_mul hA (fun ε hε => hbar ε hε t ht x)
  simp only [expBarrier] at hz
  nlinarith [Real.exp_pos (-((c + 3) * t))]

/--
Maximum principle with boundary value `M`.

If `u - M` is a linear positive-part subsolution and `u(0,x) ≤ M`, then
`u(t,x) ≤ M` on `[0,T] × ℝ`.
-/
theorem parabolic_maximum_principle
    {c T M : ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0 < T)
    (hc : 0 ≤ c)
    (hw : IsClassicalLinearSubSolution c T (fun t x => u t x - M))
    (hinit : ∀ x : ℝ, u 0 x ≤ M) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, u t x ≤ M := by
  have hinit' : ∀ x : ℝ, (fun t x => u t x - M) 0 x ≤ 0 := by
    intro x
    dsimp
    linarith [hinit x]
  have hmax :=
    weak_maximum_principle_linear
      (c := c) (T := T) (w := fun t x => u t x - M)
      hT hc hw hinit'
  intro t ht x
  have hx := hmax t ht x
  dsimp at hx
  linarith

/--
Difference of a subsolution and a supersolution is a positive-part linear
subsolution.

Let `w = u - v`.  Since

`uₜ - uₓₓ ≤ g(u)`

and

`vₜ - vₓₓ ≥ g(v)`,

we get

`wₜ - wₓₓ ≤ g(u) - g(v)`.

At points where `w > 0`, i.e. `u > v`, the Lipschitz estimate gives

`g(u) - g(v) ≤ |g(u) - g(v)| ≤ L |u - v| = L w`.

The derivative identities

`∂ₜ(u-v) = ∂ₜu - ∂ₜv`,
`∂ₓₓ(u-v) = ∂ₓₓu - ∂ₓₓv`

are routine but verbose in Lean, so this bridge lemma is isolated.
-/
private lemma dt_sub_of_hasDerivAt {u v : ℝ → ℝ → ℝ} {t x : ℝ}
    (hu : HasDerivAt (fun τ => u τ x) (dt u t x) t)
    (hv : HasDerivAt (fun τ => v τ x) (dt v t x) t) :
    dt (fun τ y => u τ y - v τ y) t x = dt u t x - dt v t x := by
  simpa [dt] using (hu.sub hv).deriv

private lemma dx_sub_of_hasDerivAt {u v : ℝ → ℝ → ℝ} {t x : ℝ}
    (hu : HasDerivAt (fun y => u t y) (dx u t x) x)
    (hv : HasDerivAt (fun y => v t y) (dx v t x) x) :
    dx (fun τ y => u τ y - v τ y) t x = dx u t x - dx v t x := by
  simpa [dx] using (hu.sub hv).deriv

private lemma dxx_sub_of_hasDerivAt {u v : ℝ → ℝ → ℝ} {t x : ℝ}
    (hu₁ : ∀ y, HasDerivAt (fun z => u t z) (dx u t y) y)
    (hv₁ : ∀ y, HasDerivAt (fun z => v t z) (dx v t y) y)
    (hu₂ : HasDerivAt (fun y => dx u t y) (dxx u t x) x)
    (hv₂ : HasDerivAt (fun y => dx v t y) (dxx v t x) x) :
    dxx (fun τ y => u τ y - v τ y) t x = dxx u t x - dxx v t x := by
  have hdx_fun : (fun y => dx (fun τ z => u τ z - v τ z) t y) =
      (fun y => dx u t y - dx v t y) := by
    funext y; exact dx_sub_of_hasDerivAt (hu₁ y) (hv₁ y)
  simpa [dxx, hdx_fun] using (hu₂.sub hv₂).deriv

private lemma difference_is_linear_subsolution
    {g : ℝ → ℝ} {T L R : ℝ} {u v : ℝ → ℝ → ℝ}
    (hsub : IsClassicalSubSolution g T u)
    (hsuper : IsClassicalSuperSolution g T v)
    (hLip : ∀ a b : ℝ, |a| ≤ R → |b| ≤ R → |g a - g b| ≤ L * |a - b|)
    (hL_nn : 0 ≤ L)
    (huR : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, |u t x| ≤ R)
    (hvR : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, |v t x| ≤ R) :
    IsClassicalLinearSubSolution L T (fun t x => u t x - v t x) := by
  refine { time_hasDerivAt := ?_, space_hasDerivAt := ?_,
           space_second_hasDerivAt := ?_, pde_le_of_pos := ?_, bounded := ?_ }
  · intro t x htIoo
    have hu := hsub.time_hasDerivAt htIoo (x := x)
    have hv := hsuper.time_hasDerivAt htIoo (x := x)
    simpa [dt_sub_of_hasDerivAt hu hv] using hu.sub hv
  · intro t x htIoo
    have hu := hsub.space_hasDerivAt htIoo (x := x)
    have hv := hsuper.space_hasDerivAt htIoo (x := x)
    simpa [dx_sub_of_hasDerivAt hu hv] using hu.sub hv
  · intro t x htIoo
    have hu₂ := hsub.space_second_hasDerivAt htIoo (x := x)
    have hv₂ := hsuper.space_second_hasDerivAt htIoo (x := x)
    have hdx_fun : (fun y => dx (fun τ z => u τ z - v τ z) t y) =
        (fun y => dx u t y - dx v t y) := by
      funext y
      exact dx_sub_of_hasDerivAt (hsub.space_hasDerivAt htIoo) (hsuper.space_hasDerivAt htIoo)
    have hdx : (fun y => dx (fun τ z => u τ z - v τ z) t y) =
        (fun y => dx u t y - dx v t y) := by
      funext y
      simpa [dx] using ((hsub.space_hasDerivAt htIoo (x := y)).sub
        (hsuper.space_hasDerivAt htIoo (x := y))).deriv
    have hder : HasDerivAt (fun y => dx u t y - dx v t y) (dxx u t x - dxx v t x) x :=
      (hsub.space_second_hasDerivAt htIoo (x := x)).sub
        (hsuper.space_second_hasDerivAt htIoo (x := x))
    have hder_w : HasDerivAt (fun y => dx (fun τ z => u τ z - v τ z) t y)
        (dxx u t x - dxx v t x) x := by simpa [hdx] using hder
    have hdxx : dxx (fun τ y => u τ y - v τ y) t x = dxx u t x - dxx v t x := by
      simpa [dxx] using hder_w.deriv
    rw [hdxx]; exact hder_w
  · intro t x htIoo hpos
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨le_of_lt htIoo.1, le_of_lt htIoo.2⟩
    have hdt : dt (fun τ y => u τ y - v τ y) t x = dt u t x - dt v t x := by
      simpa [dt] using ((hsub.time_hasDerivAt htIoo (x := x)).sub
        (hsuper.time_hasDerivAt htIoo (x := x))).deriv
    have hdx : (fun y => dx (fun τ z => u τ z - v τ z) t y) =
        (fun y => dx u t y - dx v t y) := by
      funext y
      simpa [dx] using ((hsub.space_hasDerivAt htIoo (x := y)).sub
        (hsuper.space_hasDerivAt htIoo (x := y))).deriv
    have hdxx : dxx (fun τ y => u τ y - v τ y) t x = dxx u t x - dxx v t x := by
      simpa [dxx, hdx] using ((hsub.space_second_hasDerivAt htIoo (x := x)).sub
        (hsuper.space_second_hasDerivAt htIoo (x := x))).deriv
    have hop : parabolicOp (fun τ y => u τ y - v τ y) t x =
        parabolicOp u t x - parabolicOp v t x := by
      unfold parabolicOp; rw [hdt, hdxx]; ring
    calc parabolicOp (fun τ y => u τ y - v τ y) t x
        = parabolicOp u t x - parabolicOp v t x := hop
      _ ≤ g (u t x) - g (v t x) := by
          linarith [hsub.pde_le htIoo (x := x), hsuper.pde_ge htIoo (x := x)]
      _ ≤ |g (u t x) - g (v t x)| := le_abs_self _
      _ ≤ L * |u t x - v t x| := hLip _ _ (huR t htIcc x) (hvR t htIcc x)
      _ = L * (u t x - v t x) := by rw [abs_of_pos hpos]
  · rcases hsub.bounded with ⟨Mu, hMu_nn, hMu⟩
    rcases hsuper.bounded with ⟨Mv, hMv_nn, hMv⟩
    exact ⟨Mu + Mv, add_nonneg hMu_nn hMv_nn, fun t ht x => by
      calc |u t x - v t x| = |u t x + -(v t x)| := by ring_nf
        _ ≤ |u t x| + |-(v t x)| := abs_add_le _ _
        _ = |u t x| + |v t x| := by simp
        _ ≤ Mu + Mv := add_le_add (hMu t ht x) (hMv t ht x)⟩

/--
Classical comparison principle for one-dimensional scalar parabolic equations.

If `u` is a subsolution, `v` is a supersolution, both are bounded, and
`u(0,x) ≤ v(0,x)`, then `u ≤ v` on `[0,T] × ℝ`.
-/
theorem comparison_principle
    {g : ℝ → ℝ} {T : ℝ} {u v : ℝ → ℝ → ℝ}
    (hT : 0 < T)
    (hg : LocallyLipschitzReal g)
    (hsub : IsClassicalSubSolution g T u)
    (hsuper : IsClassicalSuperSolution g T v)
    (hinit : ∀ x : ℝ, u 0 x ≤ v 0 x) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, u t x ≤ v t x := by
  classical

  obtain ⟨Mu, hMu_nn, hMu⟩ := hsub.bounded
  obtain ⟨Mv, hMv_nn, hMv⟩ := hsuper.bounded

  let R : ℝ := Mu + Mv + 1

  have hR_pos : 0 < R := by
    dsimp [R]
    nlinarith [hMu_nn, hMv_nn]

  obtain ⟨L, hL_nn, hLip⟩ := hg R hR_pos

  have huR : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, |u t x| ≤ R := by
    intro t ht x
    have h := hMu t ht x
    dsimp [R]
    nlinarith [h, hMv_nn]

  have hvR : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, |v t x| ≤ R := by
    intro t ht x
    have h := hMv t ht x
    dsimp [R]
    nlinarith [h, hMu_nn]

  have hw :
      IsClassicalLinearSubSolution L T (fun t x => u t x - v t x) :=
    difference_is_linear_subsolution
      (g := g) (T := T) (L := L) (R := R) (u := u) (v := v)
      hsub hsuper hLip hL_nn huR hvR

  have hinit_w : ∀ x : ℝ, (fun t x => u t x - v t x) 0 x ≤ 0 := by
    intro x
    dsimp
    linarith [hinit x]

  have hmax :=
    weak_maximum_principle_linear
      (c := L) (T := T) (w := fun t x => u t x - v t x)
      hT hL_nn hw hinit_w

  intro t ht x
  have hx := hmax t ht x
  dsimp at hx
  linarith

/-- Spatially constant function generated by a time profile `bar`. -/
def spatiallyConstant (bar : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t _x => bar t

/--
A spatially constant ODE supersolution.

For an upper comparison function for

`uₜ = uₓₓ + g(u)`,

the correct supersolution inequality is

`bar' ≥ g(bar)`,

i.e.

`g (bar t) ≤ deriv bar t`.
-/
structure IsClassicalODESuperSolution
    (g : ℝ → ℝ) (T : ℝ) (bar : ℝ → ℝ) : Prop where
  time_hasDerivAt :
    ∀ ⦃t : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        HasDerivAt bar (deriv bar t) t
  ode_ge :
    ∀ ⦃t : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        g (bar t) ≤ deriv bar t
  bounded :
    ∃ M : ℝ,
      0 ≤ M ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, |bar t| ≤ M

/--
A spatially constant ODE supersolution is a PDE supersolution.

The spatial derivatives vanish.
-/
lemma spatiallyConstant_superSolution_of_ode
    {g : ℝ → ℝ} {T : ℝ} {bar : ℝ → ℝ}
    (hbar : IsClassicalODESuperSolution g T bar) :
    IsClassicalSuperSolution g T (spatiallyConstant bar) := by
  refine { time_hasDerivAt := ?_, space_hasDerivAt := ?_,
           space_second_hasDerivAt := ?_, pde_ge := ?_, bounded := ?_ }
  · intro t x ht
    simpa [spatiallyConstant, dt] using hbar.time_hasDerivAt (t := t) ht
  · intro t x ht
    simpa [spatiallyConstant, dx] using (hasDerivAt_const x (bar t) : HasDerivAt (fun _ => bar t) 0 x)
  · intro t x ht
    simpa [spatiallyConstant, dx, dxx] using (hasDerivAt_const x (0 : ℝ) : HasDerivAt (fun _ => (0 : ℝ)) 0 x)
  · intro t x ht
    simpa [spatiallyConstant, parabolicOp, dt, dx, dxx] using hbar.ode_ge (t := t) ht
  · rcases hbar.bounded with ⟨M, hM_nn, hM⟩
    exact ⟨M, hM_nn, fun t ht x => by simpa [spatiallyConstant] using hM t ht⟩

/--
Application: comparison against a spatially constant ODE supersolution.

If `u` is a subsolution of

`uₜ = uₓₓ + g(u)`

and `bar` satisfies

`bar' ≥ g(bar)`,

with `u(0,x) ≤ bar(0)`, then `u(t,x) ≤ bar(t)`.
-/
theorem comparison_with_spatially_constant_super
    {g : ℝ → ℝ} {T : ℝ} {u : ℝ → ℝ → ℝ} {bar : ℝ → ℝ}
    (hT : 0 < T)
    (hg : LocallyLipschitzReal g)
    (hsub : IsClassicalSubSolution g T u)
    (hbar : IsClassicalODESuperSolution g T bar)
    (hinit : ∀ x : ℝ, u 0 x ≤ bar 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, u t x ≤ bar t := by
  have hsuper :
      IsClassicalSuperSolution g T (spatiallyConstant bar) :=
    spatiallyConstant_superSolution_of_ode hbar

  have hinit' :
      ∀ x : ℝ, u 0 x ≤ spatiallyConstant bar 0 x := by
    intro x
    simpa [spatiallyConstant] using hinit x

  simpa [spatiallyConstant] using
    comparison_principle
      (g := g) (T := T) (u := u) (v := spatiallyConstant bar)
      hT hg hsub hsuper hinit'

end ParabolicMaxPrinciple
end PDE
end ShenWork
