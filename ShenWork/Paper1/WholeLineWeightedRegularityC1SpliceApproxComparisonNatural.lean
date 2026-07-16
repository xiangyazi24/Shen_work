import ShenWork.Paper1.WholeLineWeightedRegularityC1SpliceParabolicComparisonNatural

open Filter Topology Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Approximate-contact parabolic comparison at a C¹ splice

The operator estimate needed for the paper equation is naturally available
only at penalized almost-maxima.  This version of the finite-slab comparison
therefore asks for the parabolic inequality only under the corresponding
first- and second-derivative contact bounds.  The exponential time weight is
internal.  Its positive scale is divided out before invoking the raw contact
estimate, so an error `E * eta` remains exactly `E * rho` after rescaling.
-/

set_option maxHeartbeats 800000 in
-- The space-time almost-maximizer and its two splice branches need an
-- extended arithmetic normalization budget.
/-- Finite-slab comparison for a stationary barrier with one constant-to-
smooth `C¹` splice, using only error-tolerant PDE estimates at approximate
positive contacts.  Away from the splice the raw contact data concern
`A - u(t)`.  At the splice the constant branch gives the one-sided replacement
`u_x = 0` and `-u_xx < eta`.

The hypotheses are the direct parabolic form obtained from a stationary
subsolution, the exact evolution equation, and an estimate such as
`paperWaveOperator_diff_le_of_approx_contact`. -/
theorem stationary_C1splice_le_of_approx_contact_parabolic_comparison
    {T B C E X : ℝ} {A : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0 < T) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hAleft : ∀ x, x ≤ X → A x = A X)
    (hAX : HasDerivAt A 0 X)
    (hAaway : ∀ x, x ≠ X → ContDiffAt ℝ 2 A x)
    (hcont : Continuous (fun q : ℝ × ℝ => A q.2 - u q.1 q.2))
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, |A x - u t x| ≤ B)
    (hinit : ∀ x, A x ≤ u 0 x)
    (huspace : ∀ ⦃t⦄, t ∈ Set.Ioc (0 : ℝ) T → ContDiff ℝ 2 (u t))
    (htime : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => A x - u s x)
        (deriv (fun s : ℝ => A x - u s x) t) t)
    (hpdeAway : ∀ ⦃eta : ℝ⦄, 0 < eta → ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioc (0 : ℝ) T → x ≠ X →
      0 < A x - u t x →
      |deriv (fun y : ℝ => A y - u t y) x| < eta →
      deriv (deriv (fun y : ℝ => A y - u t y)) x < eta →
      deriv (fun s : ℝ => A x - u s x) t ≤
        C * (A x - u t x) + E * eta)
    (hpdeSplice : ∀ ⦃eta : ℝ⦄, 0 < eta → ∀ ⦃t : ℝ⦄,
      t ∈ Set.Ioc (0 : ℝ) T →
      0 < A X - u t X →
      deriv (u t) X = 0 →
      -deriv (deriv (u t)) X < eta →
      deriv (fun s : ℝ => A X - u s X) t ≤
        C * (A X - u t X) + E * eta) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, A x ≤ u t x := by
  let lam : ℝ := C + 1
  let scale : ℝ → ℝ := fun t => Real.exp (-(lam * t))
  let w : ℝ → ℝ → ℝ := fun t x => scale t * (A x - u t x)
  have hlam : 0 < lam := by
    dsimp [lam]
    linarith
  have hscale_pos : ∀ t, 0 < scale t := by
    intro t
    exact Real.exp_pos _
  have hscale_le_one : ∀ t, 0 ≤ t → scale t ≤ 1 := by
    intro t ht
    dsimp [scale]
    rw [Real.exp_le_one_iff]
    nlinarith
  have hB : 0 ≤ B := by
    have h := hbound 0 ⟨le_rfl, hT.le⟩ 0
    exact (abs_nonneg (A 0 - u 0 0)).trans h
  have hwcont : Continuous (fun q : ℝ × ℝ => w q.1 q.2) := by
    dsimp [w, scale, lam]
    have hscont : Continuous (fun q : ℝ × ℝ =>
        Real.exp (-((C + 1) * q.1))) := by
      fun_prop
    exact hscont.mul hcont
  have hwupper : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, w t x ≤ B := by
    intro t ht x
    have heB : A x - u t x ≤ B :=
      (le_abs_self (A x - u t x)).trans (hbound t ht x)
    have hmul : scale t * (A x - u t x) ≤ scale t * B :=
      mul_le_mul_of_nonneg_left heB (hscale_pos t).le
    have hmulB : scale t * B ≤ 1 * B :=
      mul_le_mul_of_nonneg_right (hscale_le_one t ht.1) hB
    exact hmul.trans (by simpa [w] using hmulB)
  have hwinit : ∀ x, w 0 x ≤ 0 := by
    intro x
    dsimp [w, scale]
    simpa using sub_nonpos.mpr (hinit x)
  have htimeW : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => w s x)
        (deriv (fun s : ℝ => w s x) t) t := by
    intro t x ht
    have hlin : HasDerivAt (fun s : ℝ => -(lam * s)) (-lam) t := by
      convert ((hasDerivAt_id t).const_mul lam).neg using 1 <;> ring
    have hexp : HasDerivAt scale (-lam * scale t) t := by
      simpa [scale, mul_comm] using hlin.exp
    have hprod := hexp.mul (htime (t := t) (x := x) ht)
    exact hprod.differentiableAt.hasDerivAt
  intro t ht x
  by_contra hnot
  have hlt : u t x < A x := lt_of_not_ge hnot
  have hepos : 0 < A x - u t x := by linarith
  have hwpos : 0 < w t x := mul_pos (hscale_pos t) hepos
  let L : ℝ := wholeLineSlabSup T w
  have hwL : w t x ≤ L :=
    le_wholeLineSlabSup hT.le hwupper ht x
  have hL : 0 < L := lt_of_lt_of_le hwpos hwL
  let delta : ℝ := L / 8
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hgap : 0 + 2 * delta < L := by
    dsimp [delta]
    linarith
  let rho : ℝ := L / (8 * (E + 1))
  have hEone : 0 < E + 1 := by linarith
  have hrho : 0 < rho := by
    dsimp [rho]
    positivity
  obtain ⟨t₀, ht₀, x₀, hwclose, hwtNonneg, hbranch⟩ :=
    exists_wholeLineSlab_approx_max_deriv_data_C1splice
      (A := A) (u := u) (scale := scale) hT hdelta hrho
      (fun s _ => hscale_pos s) hwcont hwupper hwinit hgap
      hAleft hAX hAaway huspace htimeW
  have hclose : L - 2 * delta < w t₀ x₀ := by
    simpa [w, L] using hwclose
  have hwcontact : 0 < w t₀ x₀ := by
    dsimp [delta] at hclose
    linarith
  have hecontact : 0 < A x₀ - u t₀ x₀ := by
    have hwcontact' : 0 < scale t₀ * (A x₀ - u t₀ x₀) := by
      simpa [w] using hwcontact
    exact (mul_pos_iff_of_pos_left (hscale_pos t₀)).mp hwcontact'
  let eta : ℝ := rho / scale t₀
  have heta : 0 < eta := div_pos hrho (hscale_pos t₀)
  have hscale_eta : scale t₀ * eta = rho := by
    dsimp [eta]
    field_simp [ne_of_gt (hscale_pos t₀)]
  have hlin : HasDerivAt (fun s : ℝ => -(lam * s)) (-lam) t₀ := by
    convert ((hasDerivAt_id t₀).const_mul lam).neg using 1 <;> ring
  have hexp : HasDerivAt scale (-lam * scale t₀) t₀ := by
    simpa [scale, mul_comm] using hlin.exp
  have hprod := hexp.mul (htime (t := t₀) (x := x₀) ht₀)
  have hwt : deriv (fun s : ℝ => w s x₀) t₀ =
      (-lam * scale t₀) * (A x₀ - u t₀ x₀) +
        scale t₀ * deriv (fun s : ℝ => A x₀ - u s x₀) t₀ := by
    simpa [w] using hprod.deriv
  have hEscale : scale t₀ * (E * eta) = E * rho := by
    calc
      scale t₀ * (E * eta) = E * (scale t₀ * eta) := by ring
      _ = E * rho := by rw [hscale_eta]
  have hpdeRaw : deriv (fun s : ℝ => A x₀ - u s x₀) t₀ ≤
      C * (A x₀ - u t₀ x₀) + E * eta := by
    rcases hbranch with haway | hsplice
    · have hx : x₀ ≠ X := haway.1
      let e : ℝ → ℝ := fun y => A y - u t₀ y
      have hwx : deriv (fun y : ℝ => w t₀ y) x₀ =
          scale t₀ * deriv e x₀ := by
        simpa [w, e] using
          (deriv_const_mul_field (x := x₀) (scale t₀) e)
      have hwxx : deriv (deriv (fun y : ℝ => w t₀ y)) x₀ =
          scale t₀ * deriv (deriv e) x₀ := by
        have hiter := iteratedDeriv_const_mul_field
          (x := x₀) (n := 2) (scale t₀) e
        simpa [w, e, show (2 : ℕ) = 1 + 1 by norm_num,
          iteratedDeriv_succ] using hiter
      have hslopeScaled : scale t₀ * |deriv e x₀| < rho := by
        rw [← abs_of_pos (hscale_pos t₀), ← abs_mul, ← hwx]
        exact haway.2.1
      have hslopeRaw : |deriv e x₀| < eta := by
        rw [lt_div_iff₀ (hscale_pos t₀)]
        simpa [mul_comm] using hslopeScaled
      have hsecondRaw : deriv (deriv e) x₀ < eta := by
        have hsecondScaled : scale t₀ * deriv (deriv e) x₀ < rho := by
          rw [← hwxx]
          exact haway.2.2
        rw [lt_div_iff₀ (hscale_pos t₀)]
        simpa [mul_comm] using hsecondScaled
      exact hpdeAway heta ht₀ hx hecontact hslopeRaw hsecondRaw
    · have hx : x₀ = X := hsplice.1
      subst x₀
      have hsecondRaw : -deriv (deriv (u t₀)) X < eta := by
        rw [lt_div_iff₀ (hscale_pos t₀)]
        nlinarith [hsplice.2.2]
      exact hpdeSplice heta ht₀ hecontact hsplice.2.1 hsecondRaw
  have hpdeScaled : deriv (fun s : ℝ => w s x₀) t₀ ≤
      -w t₀ x₀ + E * rho := by
    have hmul := mul_le_mul_of_nonneg_left hpdeRaw (hscale_pos t₀).le
    rw [mul_add, hEscale] at hmul
    rw [hwt]
    dsimp [w, lam]
    linarith
  have hErho : E * rho ≤ L / 8 := by
    have hEle : E ≤ E + 1 := by linarith
    have hmul : E * L ≤ (E + 1) * L :=
      mul_le_mul_of_nonneg_right hEle hL.le
    dsimp [rho]
    calc
      E * (L / (8 * (E + 1))) = (E * L) / (8 * (E + 1)) := by ring
      _ ≤ ((E + 1) * L) / (8 * (E + 1)) :=
        (div_le_div_iff_of_pos_right (by positivity : 0 < 8 * (E + 1))).2 hmul
      _ = L / 8 := by field_simp [ne_of_gt hEone]
  have hneg : -w t₀ x₀ + E * rho < 0 := by
    dsimp [delta] at hclose
    linarith
  linarith

section AxiomAudit

#print axioms stationary_C1splice_le_of_approx_contact_parabolic_comparison

end AxiomAudit

end ShenWork.Paper1
