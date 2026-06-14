import ShenWork.Wiener.EWA.ChemDivTopLevel

/-!
# Route R2 — chemDiv eigenvalue-ℓ¹ summability via a split-integral estimate

This file proves the SAME windowed conclusion as
`ShenWork.EWA.chemDiv_eigenvalueSummableOn_of_solution`
(`ChemDivFinal.lean`) / `chemDiv_eigenvalueSummableOn_of_EWA`
(`ChemDivTopLevel.lean`), namely, for a fixed interior time `t ∈ (0, T]`,

```
Summable (fun n => unitIntervalCosineEigenvalue n *
  |∫ s in 0..t, Real.exp (-(t - s) * unitIntervalCosineEigenvalue n)
      * coupledChemDivSourceCoeffs p u s n|)
```

but **DIRECTLY**, by a split-integral estimate, **bypassing** the committed
`DuhamelSourceTimeC1On` consumer.  The whole point: this route needs
**NEITHER** the time-derivative data (`Mdot`/`adot`) **NOR** the all-`s` `A¹`
regularity that the `DuhamelSourceTimeC1On` route carries.  The only data it
consumes are:

* (I) a **window `A⁰` source envelope** `E` with `|G_n s| ≤ E n` for
  `s ∈ [τ₀, t]` and `Summable E`;
* (II) a **polynomial early bound** `|G_n s| ≤ C·(1+n)` for `s ∈ [0, τ₀]`
  (from `u, v ∈ L∞` — NOT `A¹`);
* the per-mode continuity of `s ↦ G_n s` (a `C⁰` input, far weaker than the
  `C¹`/`Mdot` data of the bypassed route).

The CORE CONTRIBUTION genuinely proven here:

* the split `∫₀ᵗ = ∫₀^{τ₀} + ∫_{τ₀}^t` with honest interval-integrability;
* the LATE estimate `λ_n·∫_{τ₀}^t e^{-(t-s)λ_n} ds = 1 - e^{-(t-τ₀)λ_n} ≤ 1`
  (FTC-2 with the explicit antiderivative);
* the EARLY estimate `∫₀^{τ₀} e^{-(t-s)λ_n} ds ≤ τ₀·e^{-(t-τ₀)λ_n}`;
* the heat-tail summability `Summable ((1+n)·λ_n·e^{-c·λ_n})` for `c > 0`
  (super-polynomial decay beats the polynomial factor);
* `Summable.add` of the two pieces.

NO `sorry`, `axiom`, `native_decide`, or `admit`.
-/

open scoped BigOperators
open MeasureTheory
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemDivSourceCoeffs)

noncomputable section

namespace ShenWork.EWA.R2

/-- Nonnegativity of the eigenvalue. -/
lemma eigenvalue_nonneg (n : ℕ) : 0 ≤ unitIntervalCosineEigenvalue n := by
  unfold unitIntervalCosineEigenvalue; positivity

/-- The eigenvalue written as `(nπ)²`. -/
lemma eigenvalue_eq (n : ℕ) :
    unitIntervalCosineEigenvalue n = (n : ℝ) ^ 2 * Real.pi ^ 2 := by
  unfold unitIntervalCosineEigenvalue; ring

/-- **Heat-tail summability with a polynomial weight.**
For every `c > 0`, the sequence `(1 + n) · λ_n · e^{-c·λ_n}` is summable:
the super-polynomial heat decay `e^{-c(nπ)²}` beats the cubic polynomial
`(1+n)·(nπ)²`. -/
lemma poly_mul_eigenvalue_mul_exp_summable {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ =>
      (1 + (n : ℝ)) *
        (unitIntervalCosineEigenvalue n *
          Real.exp (-c * unitIntervalCosineEigenvalue n))) := by
  -- Compare to `π² · ((n³ + n²) · e^{-r n})` with `r = c·π²`.
  set r : ℝ := c * Real.pi ^ 2 with hr_def
  have hr : 0 < r := by rw [hr_def]; positivity
  have h3 : Summable (fun n : ℕ => (n : ℝ) ^ 3 * Real.exp (-r * (n : ℝ))) :=
    Real.summable_pow_mul_exp_neg_nat_mul 3 hr
  have h2 : Summable (fun n : ℕ => (n : ℝ) ^ 2 * Real.exp (-r * (n : ℝ))) :=
    Real.summable_pow_mul_exp_neg_nat_mul 2 hr
  have hbase : Summable (fun n : ℕ =>
      Real.pi ^ 2 *
        (((n : ℝ) ^ 3 + (n : ℝ) ^ 2) * Real.exp (-r * (n : ℝ)))) := by
    have hsum : Summable (fun n : ℕ =>
        (n : ℝ) ^ 3 * Real.exp (-r * (n : ℝ))
          + (n : ℝ) ^ 2 * Real.exp (-r * (n : ℝ))) := h3.add h2
    refine (hsum.mul_left (Real.pi ^ 2)).congr (fun n => ?_)
    ring
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hbase
  · have : 0 ≤ unitIntervalCosineEigenvalue n := eigenvalue_nonneg n
    positivity
  · -- Pointwise: `(1+n)·λ_n·e^{-cλ_n} ≤ π²·(n³+n²)·e^{-r n}`.
    have hexp_le :
        Real.exp (-c * unitIntervalCosineEigenvalue n)
          ≤ Real.exp (-r * (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hn1 : (1 : ℝ) ≤ (n : ℝ) ∨ (n : ℝ) = 0 := by
        rcases Nat.eq_zero_or_pos n with h | h
        · right; simp [h]
        · left; exact_mod_cast h
      have hn_le : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
        rcases hn1 with h | h
        · nlinarith [h]
        · rw [h]; norm_num
      have hkey : r * (n : ℝ) ≤ c * unitIntervalCosineEigenvalue n := by
        rw [eigenvalue_eq, hr_def]
        nlinarith [mul_nonneg hc.le (sq_nonneg Real.pi), hn_le]
      linarith
    have hlamnn : 0 ≤ unitIntervalCosineEigenvalue n := eigenvalue_nonneg n
    have hlampoly : unitIntervalCosineEigenvalue n ≤ Real.pi ^ 2 * (n : ℝ) ^ 2 := by
      rw [eigenvalue_eq]; exact le_of_eq (by ring)
    have he : 0 ≤ Real.exp (-r * (n : ℝ)) := Real.exp_nonneg _
    calc (1 + (n : ℝ)) *
            (unitIntervalCosineEigenvalue n *
              Real.exp (-c * unitIntervalCosineEigenvalue n))
        ≤ (1 + (n : ℝ)) *
            (unitIntervalCosineEigenvalue n * Real.exp (-r * (n : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hexp_le hlamnn
      _ ≤ (1 + (n : ℝ)) *
            (Real.pi ^ 2 * (n : ℝ) ^ 2 * Real.exp (-r * (n : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right hlampoly he
      _ ≤ Real.pi ^ 2 *
            (((n : ℝ) ^ 3 + (n : ℝ) ^ 2) * Real.exp (-r * (n : ℝ))) := by
          nlinarith [Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n : ℝ), he,
            mul_nonneg (sq_nonneg Real.pi) he]

/-- **Exact LATE-window integral identity (via FTC-2).**
For `lam > 0` and `τ₀ ≤ t`,
`lam · ∫_{τ₀}^t e^{-(t-s)·lam} ds = 1 - e^{-(t-τ₀)·lam}`. -/
lemma eigenvalue_mul_late_integral {t τ₀ lam : ℝ} (hlam : 0 < lam) (_hτt : τ₀ ≤ t) :
    lam * ∫ s in τ₀..t, Real.exp (-(t - s) * lam)
      = 1 - Real.exp (-(t - τ₀) * lam) := by
  -- Antiderivative `F s = (1/lam) e^{-(t-s)·lam}`, `F' s = e^{-(t-s)·lam}`.
  have hderiv : ∀ s ∈ Set.uIcc τ₀ t,
      HasDerivAt (fun s => (1 / lam) * Real.exp (-(t - s) * lam))
        (Real.exp (-(t - s) * lam)) s := by
    intro s _
    have hinner : HasDerivAt (fun s : ℝ => -(t - s) * lam) (1 * lam) s := by
      have hsub : HasDerivAt (fun s : ℝ => -(t - s)) (1 : ℝ) s := by
        have : HasDerivAt (fun s : ℝ => -(t - s)) (-(0 - 1)) s :=
          ((hasDerivAt_const s t).sub (hasDerivAt_id s)).neg
        simpa using this
      simpa using hsub.mul_const lam
    have h1 : HasDerivAt (fun s : ℝ => -(t - s) * lam) lam s := by
      simpa using hinner
    have h2 : HasDerivAt (fun s => Real.exp (-(t - s) * lam))
        (Real.exp (-(t - s) * lam) * lam) s := by
      simpa [mul_comm] using (Real.hasDerivAt_exp _).comp s h1
    have h3 := h2.const_mul (1 / lam)
    convert h3 using 1
    field_simp
  have hint : IntervalIntegrable (fun s => Real.exp (-(t - s) * lam)) volume τ₀ t := by
    apply Continuous.intervalIntegrable; continuity
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hFTC]
  have ht0 : (t : ℝ) - t = 0 := by ring
  have hlamne : lam ≠ 0 := ne_of_gt hlam
  rw [ht0]
  simp only [neg_zero, zero_mul, Real.exp_zero]
  field_simp

/-- **Per-mode summand decomposition into LATE + EARLY pieces.**
`|∫₀ᵗ| ≤ |∫₀^{τ₀}| + |∫_{τ₀}^t|`. -/
lemma abs_full_le_split {f : ℝ → ℝ} {t τ₀ : ℝ}
    (hint0 : IntervalIntegrable f volume 0 τ₀)
    (hint1 : IntervalIntegrable f volume τ₀ t) :
    |∫ s in (0 : ℝ)..t, f s|
      ≤ |∫ s in (0 : ℝ)..τ₀, f s| + |∫ s in τ₀..t, f s| := by
  have hsplit :
      (∫ s in (0 : ℝ)..t, f s)
        = (∫ s in (0 : ℝ)..τ₀, f s) + (∫ s in τ₀..t, f s) :=
    (intervalIntegral.integral_add_adjacent_intervals hint0 hint1).symm
  rw [hsplit]
  exact abs_add_le _ _

end ShenWork.EWA.R2

namespace ShenWork.EWA

variable {T : ℝ}

open ShenWork.IntervalDomain (intervalDomainPoint)

/-- **Route R2: chemDiv eigenvalue-ℓ¹ summability via the split estimate.**

For a fixed interior time `t ∈ (0, T]`, the eigenvalue-weighted Duhamel spectral
coefficients of the chemotaxis-divergence source are summable, proven DIRECTLY
by splitting the time integral at an interior gap `τ₀ ∈ (0, t)`.

The hypotheses are exactly the R2 data — **NO** `Mdot`, **NO** `adot`, **NO**
all-`s` `A¹`:

* `hGcont` — per-mode continuity of `s ↦ G_n s` (a `C⁰` input);
* (I) `E`, `hE_nonneg`, `hE_bound` (on `[τ₀, t]`), `hE_summable` — the window
  `A⁰` source envelope;
* (II) `C`, `hC`, `hpoly` (on `[0, τ₀]`) — the polynomial early bound.

The split + the two elementary estimates + the heat-tail summability are
genuinely proven (see the `R2` namespace lemmas). -/
theorem chemDiv_eigenvalueSummableOn_viaR2
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    {t τ₀ : ℝ} (_htlo : 0 < t) (_hthi : t ≤ T)
    (hτ0 : 0 < τ₀) (hτt : τ₀ < t)
    (hGcont : ∀ n, Continuous (fun s => coupledChemDivSourceCoeffs p u s n))
    (E : ℕ → ℝ) (hE_nonneg : ∀ n, 0 ≤ E n)
    (hE_bound : ∀ s ∈ Set.Icc τ₀ t, ∀ n,
      |coupledChemDivSourceCoeffs p u s n| ≤ E n)
    (hE_summable : Summable E)
    (C : ℝ) (_hC : 0 ≤ C)
    (hpoly : ∀ s ∈ Set.Icc (0 : ℝ) τ₀, ∀ n,
      |coupledChemDivSourceCoeffs p u s n| ≤ C * (1 + (n : ℝ))) :
    Summable (fun n => unitIntervalCosineEigenvalue n *
      |∫ s in (0 : ℝ)..t,
        Real.exp (-(t - s) * unitIntervalCosineEigenvalue n)
          * coupledChemDivSourceCoeffs p u s n|) := by
  set G : ℝ → ℕ → ℝ := coupledChemDivSourceCoeffs p u with hG_def
  set f : ℕ → ℝ → ℝ :=
    fun n s => Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * G s n with hf_def
  have hf_cont : ∀ n, Continuous (f n) := by
    intro n
    rw [hf_def]
    apply Continuous.mul _ (hGcont n)
    apply Real.continuous_exp.comp
    exact (((continuous_const.sub continuous_id).neg).mul continuous_const)
  have hf_int : ∀ n (a b : ℝ), IntervalIntegrable (f n) volume a b :=
    fun n a b => (hf_cont n).intervalIntegrable a b
  set late : ℕ → ℝ :=
    fun n => unitIntervalCosineEigenvalue n * |∫ s in τ₀..t, f n s| with hlate_def
  set early : ℕ → ℝ :=
    fun n => unitIntervalCosineEigenvalue n * |∫ s in (0 : ℝ)..τ₀, f n s| with hearly_def
  -- (A) LATE piece is summable: `late n ≤ E n`.
  have hlate_summable : Summable late := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hE_summable
    · exact mul_nonneg (ShenWork.EWA.R2.eigenvalue_nonneg n) (abs_nonneg _)
    · rcases eq_or_lt_of_le (ShenWork.EWA.R2.eigenvalue_nonneg n) with hlam0 | hlampos
      · -- `λ_n = 0` ⟹ `late n = 0 ≤ E n`.
        change unitIntervalCosineEigenvalue n * |∫ s in τ₀..t, f n s| ≤ E n
        rw [← hlam0, zero_mul]; exact hE_nonneg n
      · set lam := unitIntervalCosineEigenvalue n with hlam_def
        have hbound_int :
            |∫ s in τ₀..t, f n s|
              ≤ ∫ s in τ₀..t, Real.exp (-(t - s) * lam) * E n := by
          refine le_trans (intervalIntegral.abs_integral_le_integral_abs hτt.le) ?_
          apply intervalIntegral.integral_mono_on hτt.le
          · exact ((hf_cont n).abs).intervalIntegrable _ _
          · apply Continuous.intervalIntegrable; continuity
          · intro s hs
            change |f n s| ≤ Real.exp (-(t - s) * lam) * E n
            rw [hf_def]
            simp only [abs_mul]
            have hexp_nonneg : (0 : ℝ) ≤ Real.exp (-(t - s) * lam) := Real.exp_nonneg _
            rw [abs_of_nonneg hexp_nonneg]
            exact mul_le_mul_of_nonneg_left (hE_bound s hs n) hexp_nonneg
        have hEint :
            (∫ s in τ₀..t, Real.exp (-(t - s) * lam) * E n)
              = (∫ s in τ₀..t, Real.exp (-(t - s) * lam)) * E n :=
          intervalIntegral.integral_mul_const _ _
        have hlate_le :
            late n ≤ lam * (∫ s in τ₀..t, Real.exp (-(t - s) * lam)) * E n := by
          change lam * |∫ s in τ₀..t, f n s|
            ≤ lam * (∫ s in τ₀..t, Real.exp (-(t - s) * lam)) * E n
          calc lam * |∫ s in τ₀..t, f n s|
              ≤ lam * (∫ s in τ₀..t, Real.exp (-(t - s) * lam) * E n) :=
                mul_le_mul_of_nonneg_left hbound_int hlampos.le
            _ = lam * (∫ s in τ₀..t, Real.exp (-(t - s) * lam)) * E n := by
                rw [hEint]; ring
        have hid := ShenWork.EWA.R2.eigenvalue_mul_late_integral hlampos hτt.le
        rw [show lam * (∫ s in τ₀..t, Real.exp (-(t - s) * lam)) * E n
              = (lam * ∫ s in τ₀..t, Real.exp (-(t - s) * lam)) * E n by ring,
          hid] at hlate_le
        have hfac_le : (1 - Real.exp (-(t - τ₀) * lam)) * E n ≤ E n := by
          have h1 : 1 - Real.exp (-(t - τ₀) * lam) ≤ 1 := by
            have := Real.exp_nonneg (-(t - τ₀) * lam); linarith
          calc (1 - Real.exp (-(t - τ₀) * lam)) * E n
              ≤ 1 * E n := mul_le_mul_of_nonneg_right h1 (hE_nonneg n)
            _ = E n := one_mul _
        linarith [hlate_le, hfac_le]
  -- (B) EARLY piece is summable.
  set c : ℝ := t - τ₀ with hc_def
  have hc_pos : 0 < c := by rw [hc_def]; linarith
  set maj : ℕ → ℝ :=
    fun n => C * τ₀ *
      ((1 + (n : ℝ)) *
        (unitIntervalCosineEigenvalue n *
          Real.exp (-c * unitIntervalCosineEigenvalue n)))
    with hmaj_def
  have hmaj_summable : Summable maj :=
    (ShenWork.EWA.R2.poly_mul_eigenvalue_mul_exp_summable hc_pos).mul_left (C * τ₀)
  have hearly_summable : Summable early := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj_summable
    · exact mul_nonneg (ShenWork.EWA.R2.eigenvalue_nonneg n) (abs_nonneg _)
    · set lam := unitIntervalCosineEigenvalue n with hlam_def
      have hlamnn : 0 ≤ lam := ShenWork.EWA.R2.eigenvalue_nonneg n
      have hbound_int :
          |∫ s in (0 : ℝ)..τ₀, f n s|
            ≤ ∫ s in (0 : ℝ)..τ₀, Real.exp (-c * lam) * (C * (1 + (n : ℝ))) := by
        refine le_trans (intervalIntegral.abs_integral_le_integral_abs hτ0.le) ?_
        apply intervalIntegral.integral_mono_on hτ0.le
        · exact ((hf_cont n).abs).intervalIntegrable _ _
        · apply Continuous.intervalIntegrable; continuity
        · intro s hs
          change |f n s| ≤ Real.exp (-c * lam) * (C * (1 + (n : ℝ)))
          rw [hf_def]
          simp only [abs_mul]
          have hexp_nonneg : (0 : ℝ) ≤ Real.exp (-(t - s) * lam) := Real.exp_nonneg _
          rw [abs_of_nonneg hexp_nonneg]
          have hexp_le : Real.exp (-(t - s) * lam) ≤ Real.exp (-c * lam) := by
            apply Real.exp_le_exp.mpr
            rw [hc_def]
            nlinarith [hlamnn, hs.2]
          have hG_le : |G s n| ≤ C * (1 + (n : ℝ)) := hpoly s hs n
          calc Real.exp (-(t - s) * lam) * |G s n|
              ≤ Real.exp (-c * lam) * |G s n| :=
                mul_le_mul_of_nonneg_right hexp_le (abs_nonneg _)
            _ ≤ Real.exp (-c * lam) * (C * (1 + (n : ℝ))) :=
                mul_le_mul_of_nonneg_left hG_le (Real.exp_nonneg _)
      have hconst_int :
          (∫ s in (0 : ℝ)..τ₀, Real.exp (-c * lam) * (C * (1 + (n : ℝ))))
            = τ₀ * (Real.exp (-c * lam) * (C * (1 + (n : ℝ)))) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      have hearly_le :
          early n ≤ lam * (τ₀ * (Real.exp (-c * lam) * (C * (1 + (n : ℝ))))) := by
        change lam * |∫ s in (0 : ℝ)..τ₀, f n s|
          ≤ lam * (τ₀ * (Real.exp (-c * lam) * (C * (1 + (n : ℝ)))))
        calc lam * |∫ s in (0 : ℝ)..τ₀, f n s|
            ≤ lam * (∫ s in (0 : ℝ)..τ₀, Real.exp (-c * lam) * (C * (1 + (n : ℝ)))) :=
              mul_le_mul_of_nonneg_left hbound_int hlamnn
          _ = lam * (τ₀ * (Real.exp (-c * lam) * (C * (1 + (n : ℝ))))) := by
              rw [hconst_int]
      change lam * |∫ s in (0 : ℝ)..τ₀, f n s| ≤ maj n
      rw [hmaj_def]
      calc lam * |∫ s in (0 : ℝ)..τ₀, f n s|
          ≤ lam * (τ₀ * (Real.exp (-c * lam) * (C * (1 + (n : ℝ))))) := hearly_le
        _ = C * τ₀ * ((1 + (n : ℝ)) * (lam * Real.exp (-c * lam))) := by ring
  -- (C) Combine.
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (hearly_summable.add hlate_summable)
  · exact mul_nonneg (ShenWork.EWA.R2.eigenvalue_nonneg n) (abs_nonneg _)
  · have hsplit := ShenWork.EWA.R2.abs_full_le_split
      (f := f n) (t := t) (τ₀ := τ₀)
      (hf_int n 0 τ₀) (hf_int n τ₀ t)
    have hlamnn : 0 ≤ unitIntervalCosineEigenvalue n :=
      ShenWork.EWA.R2.eigenvalue_nonneg n
    change unitIntervalCosineEigenvalue n * |∫ s in (0 : ℝ)..t, f n s| ≤ early n + late n
    calc unitIntervalCosineEigenvalue n * |∫ s in (0 : ℝ)..t, f n s|
        ≤ unitIntervalCosineEigenvalue n *
            (|∫ s in (0 : ℝ)..τ₀, f n s| + |∫ s in τ₀..t, f n s|) :=
          mul_le_mul_of_nonneg_left hsplit hlamnn
      _ = early n + late n := by rw [hearly_def, hlate_def]; ring

end ShenWork.EWA

#print axioms ShenWork.EWA.chemDiv_eigenvalueSummableOn_viaR2
