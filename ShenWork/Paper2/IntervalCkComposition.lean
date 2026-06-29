import ShenWork.Paper2.IntervalWienerAlgebraResidual
import ShenWork.Paper2.IntervalCosineSobolevEmbedding

/-!
  ShenWork/Paper2/IntervalCkComposition.lean

  WALL-A composition residual, `Cᵏ`-coefficient-decay route.

  Chen-Ruau-Shen (arXiv:2512.14858) chemotaxis flux on `[0,1]`:
      `φ(y) = u(y) · v'(y) / (1+v(y))^β`
  (`intervalDomainChemotaxisDiv`, `ShenWork/PDE/IntervalDomain.lean:2923`).  The
  real-exponent factor needing `H^σ` membership is `(1+v)^{−β}` (the `u`-power is
  `m = 1` in the concrete interval model; the general real `m` of `CM2Params` only
  enters the *abstract* boundedness criterion of `Statements.lean §4`).

  This file supplies the exponent-agnostic engine:
    * `cosineCoeffs_decay_one`  — `f ∈ C¹`            ⟹ `|cosineCoeffs f n| ≤ C/n`
    * `cosineCoeffs_decay_two`  — `f ∈ C²` + Neumann  ⟹ `|cosineCoeffs f n| ≤ C/n²`
  via integration by parts of `∫₀¹ cos(nπx) f(x) dx`, then
    * `memHSigma_of_cosineCoeffs_decay_two` — feeds `memHSigma_of_coeff_decay`
    * `memHSigma_one_add_rpow_neg_of_contDiff_two` (Task 3) — the `(1+v)^{−β}` factor.

  Builds on `memHSigma_of_coeff_decay` (`IntervalWienerAlgebraResidual.lean`) and
  `cosineCoeffs_eq_cw` (`cosineCoeffs f n = cw n · ∫₀¹ cos(nπx) f`).
-/

noncomputable section

open MeasureTheory intervalIntegral
open ShenWork.Paper2.HSigmaScale
open ShenWork.IntervalNeumannFullKernel

namespace ShenWork.Paper2.IntervalCkComposition

open ShenWork.Paper2.IntervalWienerAlgebra

/-! ## 1. The two integration-by-parts primitives. -/

/-- **Cosine step (boundary-free).**  For `f` with derivative `f'` on `[0,1]`
(`f'` interval-integrable), `∫₀¹ cos(nπx) f = −(1/nπ) ∫₀¹ sin(nπx) f'`.  The
boundary term `[sin(nπx)/(nπ)·f]₀¹` vanishes for every `n` because
`sin 0 = sin(nπ) = 0`. -/
theorem cos_ibp_step (n : ℕ) (hn : 1 ≤ n) (f f' : ℝ → ℝ)
    (hf : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt f (f' x) x)
    (hf'i : IntervalIntegrable f' volume 0 1) :
    (∫ x in (0:ℝ)..1, Real.cos ((n:ℝ) * Real.pi * x) * f x)
      = - (1 / ((n:ℝ)*Real.pi)) * ∫ x in (0:ℝ)..1, Real.sin ((n:ℝ)*Real.pi*x) * f' x := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hpi : (n:ℝ) * Real.pi ≠ 0 := mul_ne_zero hnR Real.pi_ne_zero
  set S : ℝ → ℝ := fun x => Real.sin ((n:ℝ) * Real.pi * x) / ((n:ℝ) * Real.pi) with hS
  have hSderiv : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt S (Real.cos ((n:ℝ) * Real.pi * x)) x := by
    intro x _
    have hc : HasDerivAt (fun x : ℝ => (n:ℝ) * Real.pi * x) ((n:ℝ)*Real.pi) x := by
      simpa using (hasDerivAt_id x).const_mul ((n:ℝ)*Real.pi)
    have hd : HasDerivAt (fun x => Real.sin ((n:ℝ) * Real.pi * x))
        (Real.cos ((n:ℝ)*Real.pi*x) * ((n:ℝ)*Real.pi)) x := (Real.hasDerivAt_sin _).comp x hc
    have h2 := hd.div_const ((n:ℝ) * Real.pi)
    rw [mul_div_assoc, div_self hpi, mul_one] at h2
    exact h2
  have hSi : IntervalIntegrable (fun x => Real.cos ((n:ℝ)*Real.pi*x)) volume 0 1 :=
    (Real.continuous_cos.comp (by continuity)).intervalIntegrable _ _
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hSderiv hf hSi hf'i
  have hb0 : S 0 = 0 := by simp [hS]
  have hb1 : S 1 = 0 := by
    simp only [hS, mul_one]; rw [Real.sin_nat_mul_pi]; simp
  rw [hb0, hb1] at key
  simp only [zero_mul, sub_zero, zero_sub] at key
  have hSf : (fun x => S x * f' x)
      = (fun x => (1/((n:ℝ)*Real.pi)) * (Real.sin ((n:ℝ)*Real.pi*x) * f' x)) := by
    funext x; rw [hS]; ring
  rw [hSf, intervalIntegral.integral_const_mul] at key
  linarith [key]

/-- **Sine step (carries the Neumann boundary term).**  For `g` with derivative
`g'` on `[0,1]`, `∫₀¹ sin(nπx) g = (1/nπ)(g 0 − (−1)ⁿ g 1) + (1/nπ) ∫₀¹ cos(nπx) g'`.
For the Neumann-compatible derivative `g = f'` with `f'(0)=f'(1)=0` the boundary
term vanishes. -/
theorem sin_ibp_step (n : ℕ) (hn : 1 ≤ n) (g g' : ℝ → ℝ)
    (hg : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt g (g' x) x)
    (hg'i : IntervalIntegrable g' volume 0 1) :
    (∫ x in (0:ℝ)..1, Real.sin ((n:ℝ) * Real.pi * x) * g x)
      = (1/((n:ℝ)*Real.pi)) * (g 0 - (-1)^n * g 1)
        + (1 / ((n:ℝ)*Real.pi)) * ∫ x in (0:ℝ)..1, Real.cos ((n:ℝ)*Real.pi*x) * g' x := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hpi : (n:ℝ) * Real.pi ≠ 0 := mul_ne_zero hnR Real.pi_ne_zero
  set C : ℝ → ℝ := fun x => -Real.cos ((n:ℝ) * Real.pi * x) / ((n:ℝ) * Real.pi) with hC
  have hCderiv : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt C (Real.sin ((n:ℝ) * Real.pi * x)) x := by
    intro x _
    have hc : HasDerivAt (fun x : ℝ => (n:ℝ) * Real.pi * x) ((n:ℝ)*Real.pi) x := by
      simpa using (hasDerivAt_id x).const_mul ((n:ℝ)*Real.pi)
    have hd : HasDerivAt (fun x => -Real.cos ((n:ℝ) * Real.pi * x))
        (Real.sin ((n:ℝ)*Real.pi*x) * ((n:ℝ)*Real.pi)) x := by
      have := ((Real.hasDerivAt_cos ((n:ℝ)*Real.pi*x)).comp x hc).neg
      convert this using 1; ring
    have h2 := hd.div_const ((n:ℝ) * Real.pi)
    rw [mul_div_assoc, div_self hpi, mul_one] at h2
    exact h2
  have hCi : IntervalIntegrable (fun x => Real.sin ((n:ℝ)*Real.pi*x)) volume 0 1 :=
    (Real.continuous_sin.comp (by continuity)).intervalIntegrable _ _
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hCderiv hg hCi hg'i
  have hC0 : C 0 = -1/((n:ℝ)*Real.pi) := by simp [hC]
  have hC1 : C 1 = -((-1)^n)/((n:ℝ)*Real.pi) := by
    simp only [hC]; rw [mul_one, Real.cos_nat_mul_pi]
  rw [hC0, hC1] at key
  have hCg : (fun x => C x * g' x)
      = (fun x => (1/((n:ℝ)*Real.pi)) * (-(Real.cos ((n:ℝ)*Real.pi*x)) * g' x)) := by
    funext x; rw [hC]; ring
  rw [hCg, intervalIntegral.integral_const_mul] at key
  have hsplit : (∫ x in (0:ℝ)..1, -(Real.cos ((n:ℝ)*Real.pi*x)) * g' x)
      = - ∫ x in (0:ℝ)..1, Real.cos ((n:ℝ)*Real.pi*x) * g' x := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext x; ring
  rw [hsplit] at key
  rw [eq_comm, ← sub_eq_zero] at key ⊢
  field_simp at key ⊢
  linarith [key]

/-! ## 2. Uniform `|∫ trig·g| ≤ ∫|g|` envelopes. -/

/-- `|∫₀¹ sin(nπx) g| ≤ ∫₀¹ |g|` for continuous `g`. -/
theorem abs_sin_integral_le (n : ℕ) (g : ℝ → ℝ) (hg : Continuous g) :
    |∫ x in (0:ℝ)..1, Real.sin ((n:ℝ)*Real.pi*x) * g x| ≤ ∫ x in (0:ℝ)..1, |g x| := by
  have h1 : |∫ x in (0:ℝ)..1, Real.sin ((n:ℝ)*Real.pi*x) * g x|
      ≤ ∫ x in (0:ℝ)..1, |Real.sin ((n:ℝ)*Real.pi*x) * g x| :=
    intervalIntegral.abs_integral_le_integral_abs (by norm_num)
  refine h1.trans ?_
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact (((Real.continuous_sin.comp (by continuity)).mul hg).intervalIntegrable 0 1).abs
  · exact (hg.intervalIntegrable 0 1).abs
  · intro x _
    rw [abs_mul]
    have : |Real.sin ((n:ℝ)*Real.pi*x)| ≤ 1 := Real.abs_sin_le_one _
    nlinarith [abs_nonneg (g x), abs_nonneg (Real.sin ((n:ℝ)*Real.pi*x))]

/-- `|∫₀¹ cos(nπx) g| ≤ ∫₀¹ |g|` for continuous `g`. -/
theorem abs_cos_integral_le (n : ℕ) (g : ℝ → ℝ) (hg : Continuous g) :
    |∫ x in (0:ℝ)..1, Real.cos ((n:ℝ)*Real.pi*x) * g x| ≤ ∫ x in (0:ℝ)..1, |g x| := by
  have h1 : |∫ x in (0:ℝ)..1, Real.cos ((n:ℝ)*Real.pi*x) * g x|
      ≤ ∫ x in (0:ℝ)..1, |Real.cos ((n:ℝ)*Real.pi*x) * g x| :=
    intervalIntegral.abs_integral_le_integral_abs (by norm_num)
  refine h1.trans ?_
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact (((Real.continuous_cos.comp (by continuity)).mul hg).intervalIntegrable 0 1).abs
  · exact (hg.intervalIntegrable 0 1).abs
  · intro x _
    rw [abs_mul]
    have : |Real.cos ((n:ℝ)*Real.pi*x)| ≤ 1 := Real.abs_cos_le_one _
    nlinarith [abs_nonneg (g x), abs_nonneg (Real.cos ((n:ℝ)*Real.pi*x))]

/-! ## 3. `Cᵏ ⟹ cosine-coefficient decay`. -/

/-- **`C¹ ⟹ n^{−1}` decay (boundary-free).**  If `f` has a continuous derivative
`f'` on `[0,1]`, then `|cosineCoeffs f n| ≤ (2/π)·(∫₀¹|f'|) / n` for `n ≥ 1`. -/
theorem cosineCoeffs_decay_one (f f' : ℝ → ℝ) (hf : Continuous f)
    (hderiv : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt f (f' x) x) (hf' : Continuous f') :
    ∀ n : ℕ, 1 ≤ n →
      |cosineCoeffs f n| ≤ (2 / Real.pi * ∫ x in (0:ℝ)..1, |f' x|) / (n : ℝ) := by
  intro n hn
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hcw : cw n = 2 := cw_succ (by omega)
  have heq := cosineCoeffs_eq_cw f hf n
  have hstep := cos_ibp_step n hn f f' hderiv (hf'.intervalIntegrable 0 1)
  rw [heq, hcw, hstep]
  have hbound := abs_sin_integral_le n f' hf'
  set J : ℝ := ∫ x in (0:ℝ)..1, |f' x| with hJ
  have hJ0 : 0 ≤ J := by
    rw [hJ]; exact intervalIntegral.integral_nonneg (by norm_num) (fun x _ => abs_nonneg _)
  rw [abs_mul, abs_mul]
  have habs2 : |(2:ℝ)| = 2 := by norm_num
  have hsign : |(-(1 / ((n:ℝ)*Real.pi)))| = 1/((n:ℝ)*Real.pi) := by
    rw [abs_neg, abs_of_pos (by positivity)]
  rw [habs2, hsign]
  have hI := abs_sin_integral_le n f' hf'
  calc 2 * (1/((n:ℝ)*Real.pi)
        * |∫ x in (0:ℝ)..1, Real.sin ((n:ℝ)*Real.pi*x) * f' x|)
      ≤ 2 * (1/((n:ℝ)*Real.pi) * J) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul_of_nonneg_left hI (by positivity)
    _ = (2 / Real.pi * J) / (n:ℝ) := by
        have hnR' : (n:ℝ) ≠ 0 := ne_of_gt hnR
        have hpi' : Real.pi ≠ 0 := Real.pi_ne_zero
        field_simp

/-- **`C² + Neumann ⟹ n^{−2}` decay.**  If `f` has derivatives `f', f''` on
`[0,1]` (with `f''` continuous) and satisfies the Neumann compatibility
`f'(0) = f'(1) = 0`, then `|cosineCoeffs f n| ≤ (2/π²)·(∫₀¹|f''|) / n²` for `n ≥ 1`.
Two integrations by parts: the first (cosine) boundary term always vanishes, the
second (sine) boundary term `(1/nπ)(f'(0) − (−1)ⁿ f'(1))` vanishes by Neumann. -/
theorem cosineCoeffs_decay_two (f f' f'' : ℝ → ℝ) (hf : Continuous f)
    (hf' : Continuous f')
    (hd1 : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt f (f' x) x)
    (hd2 : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'') (hN0 : f' 0 = 0) (hN1 : f' 1 = 0) :
    ∀ n : ℕ, 1 ≤ n →
      |cosineCoeffs f n| ≤ (2 / Real.pi ^ 2 * ∫ x in (0:ℝ)..1, |f'' x|) / (n : ℝ) ^ 2 := by
  intro n hn
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hcw : cw n = 2 := cw_succ (by omega)
  have heq := cosineCoeffs_eq_cw f hf n
  have hstep1 := cos_ibp_step n hn f f' hd1 (hf'.intervalIntegrable 0 1)
  have hstep2 := sin_ibp_step n hn f' f'' hd2 (hf''.intervalIntegrable 0 1)
  rw [hN0, hN1] at hstep2
  simp only [mul_zero, sub_zero] at hstep2
  -- hstep2 now reads:  ∫sin·f' = (1/nπ)·0 + (1/nπ)·∫cos·f''  (boundary killed)
  set K : ℝ := ∫ x in (0:ℝ)..1, |f'' x| with hK
  have hKnn : 0 ≤ K := by
    rw [hK]; exact intervalIntegral.integral_nonneg (by norm_num) (fun x _ => abs_nonneg _)
  set Ic : ℝ := ∫ x in (0:ℝ)..1, Real.cos ((n:ℝ)*Real.pi*x) * f'' x with hIc
  have hbnd : |Ic| ≤ K := by rw [hIc, hK]; exact abs_cos_integral_le n f'' hf''
  rw [heq, hcw, hstep1, hstep2]
  -- target: |2 * (−(1/nπ) * (0 + (1/nπ) * Ic))| ≤ (2/π² K)/n²
  rw [zero_add, abs_mul, abs_mul, abs_neg, abs_mul]
  have h2 : |(2:ℝ)| = 2 := by norm_num
  have hs : |(1/((n:ℝ)*Real.pi))| = 1/((n:ℝ)*Real.pi) := abs_of_pos (by positivity)
  rw [h2, hs]
  calc 2 * (1/((n:ℝ)*Real.pi) * (1/((n:ℝ)*Real.pi) * |Ic|))
      ≤ 2 * (1/((n:ℝ)*Real.pi) * (1/((n:ℝ)*Real.pi) * K)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left hbnd (by positivity)
    _ = (2 / Real.pi^2 * K) / (n:ℝ)^2 := by
        have hnR' : (n:ℝ) ≠ 0 := ne_of_gt hnR
        have hpi' : Real.pi ≠ 0 := Real.pi_ne_zero
        field_simp

/-- `C² + Neumann ⟹ MemHSigma σ` (coefficient route), for `σ < 3/2`.  The `n^{−2}`
decay from `cosineCoeffs_decay_two` feeds `memHSigma_of_coeff_decay` with `q = 2`. -/
theorem memHSigma_of_cosineCoeffs_decay_two {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < 3 / 2)
    (f f' f'' : ℝ → ℝ) (hf : Continuous f) (hf' : Continuous f')
    (hd1 : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt f (f' x) x)
    (hd2 : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'') (hN0 : f' 0 = 0) (hN1 : f' 1 = 0) :
    MemHSigma σ (cosineCoeffs f) := by
  have hdecay := cosineCoeffs_decay_two f f' f'' hf hf' hd1 hd2 hf'' hN0 hN1
  refine memHSigma_of_coeff_decay (q := 2) (C := 2 / Real.pi ^ 2 * ∫ x in (0:ℝ)..1, |f'' x|)
    hσ0 (by linarith) ?_
  intro n hn
  have := hdecay n hn
  rwa [← Real.rpow_natCast (n:ℝ) 2, show ((2:ℕ):ℝ) = (2:ℝ) by norm_num] at this

/-! ## 4. `Cᵏ` extraction helper (the `ContDiff ℝ 2` derivative tower). -/

/-- From `ContDiff ℝ 2 g` extract continuity of `g, g', g''` and the pointwise
two-step derivative tower (`g' = deriv g`, `g'' = deriv (deriv g)`). -/
theorem contDiff_two_tower {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) :
    Continuous g ∧ Continuous (deriv g) ∧ Continuous (deriv (deriv g)) ∧
      (∀ x, HasDerivAt g (deriv g x) x) ∧
      (∀ x, HasDerivAt (deriv g) (deriv (deriv g) x) x) := by
  have hg1 : ContDiff ℝ 1 (deriv g) := ContDiff.deriv' hg
  have hg0 : ContDiff ℝ 0 (deriv (deriv g)) := ContDiff.deriv' hg1
  have h1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have h2 : Differentiable ℝ (deriv g) := hg1.differentiable (by norm_num)
  exact ⟨hg.continuous, hg1.continuous, hg0.continuous,
    fun x => h1.differentiableAt.hasDerivAt, fun x => h2.differentiableAt.hasDerivAt⟩

/-- `ContDiff ℝ 2 f` + Neumann `(deriv f) 0 = (deriv f) 1 = 0 ⟹ MemHSigma σ`
(`0 ≤ σ < 3/2`).  The clean `Cᵏ`-route entry: discharges all the pointwise
derivative/continuity inputs from the single hypothesis `ContDiff ℝ 2 f`. -/
theorem memHSigma_of_contDiff_two {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < 3 / 2)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hN0 : deriv f 0 = 0) (hN1 : deriv f 1 = 0) :
    MemHSigma σ (cosineCoeffs f) := by
  obtain ⟨hc0, hc1, hc2, hda, hdb⟩ := contDiff_two_tower hf
  exact memHSigma_of_cosineCoeffs_decay_two hσ0 hσ f (deriv f) (deriv (deriv f))
    hc0 hc1 (fun x _ => hda x) (fun x _ => hdb x) hc2 hN0 hN1

/-! ## 5. Task 2 — the `(1+v)^{−β}` chain rule. -/

/-- **`(1+v)^{−β} ∈ C²`.**  If `v ∈ C²` and `v ≥ 0` (so the base `1+v ≥ 1 > 0`),
then `x ↦ (1 + v x)^(−β)` is `C²` for every real `β`.  The outer map `w ↦ w^{−β}`
is `C^∞` away from `0` (`Real.contDiffAt_rpow_const_of_ne`), composed with the
inner `C²` map `1 + v` via the chain rule. -/
theorem contDiff_two_one_add_rpow_neg {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (hvnn : ∀ x, 0 ≤ v x) (β : ℝ) :
    ContDiff ℝ 2 (fun x => (1 + v x) ^ (-β)) := by
  have hbase : ContDiff ℝ 2 (fun x => 1 + v x) := contDiff_const.add hv
  rw [contDiff_iff_contDiffAt]
  intro x
  have hbasept : (1 + v x) ≠ 0 := by have := hvnn x; positivity
  exact (Real.contDiffAt_rpow_const_of_ne (p := -β) hbasept).comp x hbase.contDiffAt

/-- Companion for a strictly-positive base `u ≥ c > 0`: `u^m ∈ C²` for every real
exponent `m` (the general-real-`m` factor `u^m`; in the concrete interval flux
`m = 1`, but this covers the abstract criterion's general `m`). -/
theorem contDiff_two_rpow_of_pos {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) {c : ℝ}
    (hc : 0 < c) (hupos : ∀ x, c ≤ u x) (m : ℝ) :
    ContDiff ℝ 2 (fun x => (u x) ^ m) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hupt : u x ≠ 0 := by have := hupos x; linarith
  exact (Real.contDiffAt_rpow_const_of_ne (p := m) hupt).comp x hu.contDiffAt

/-- Companion for a strictly-positive base `u ≥ c > 0`: `u^m ∈ C⁴` for every
real exponent `m`.  This is the C⁴ version of `contDiff_two_rpow_of_pos`. -/
theorem contDiff_four_rpow_of_pos {u : ℝ → ℝ} (hu : ContDiff ℝ 4 u) {c : ℝ}
    (hc : 0 < c) (hupos : ∀ x, c ≤ u x) (m : ℝ) :
    ContDiff ℝ 4 (fun x => (u x) ^ m) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hupt : u x ≠ 0 := by have := hupos x; linarith
  exact (Real.contDiffAt_rpow_const_of_ne (p := m) hupt).comp x hu.contDiffAt

/-! ## 6. Task 3 — factor membership + the flux assembly. -/

/-- **The `(1+v)^{−β}` factor lands in `H^σ`.**  `v ∈ C²`, `v ≥ 0`, and the Neumann
compatibility of the composed factor (`deriv ((1+v)^{−β}) = 0` at `{0,1}`, which
holds whenever `v' = 0` there) give `(1+v)^{−β} ∈ MemHSigma σ` for `0 ≤ σ < 3/2`.
This is the WALL-A real-exponent residual for the chemotaxis flux denominator. -/
theorem memHSigma_one_add_rpow_neg_of_contDiff_two {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < 3 / 2)
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvnn : ∀ x, 0 ≤ v x) (β : ℝ)
    (hN0 : deriv (fun x => (1 + v x) ^ (-β)) 0 = 0)
    (hN1 : deriv (fun x => (1 + v x) ^ (-β)) 1 = 0) :
    MemHSigma σ (cosineCoeffs (fun x => (1 + v x) ^ (-β))) :=
  memHSigma_of_contDiff_two hσ0 hσ (contDiff_two_one_add_rpow_neg hv hvnn β) hN0 hN1

/-- **The `u^m` factor lands in `H^σ`** for strictly-positive `u` and general real
`m` (covers the abstract boundedness criterion's `m`; in the concrete interval
flux `m = 1` and this specializes to `u` itself). -/
theorem memHSigma_rpow_of_contDiff_two {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < 3 / 2)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) {c : ℝ} (hc : 0 < c) (hupos : ∀ x, c ≤ u x) (m : ℝ)
    (hN0 : deriv (fun x => (u x) ^ m) 0 = 0) (hN1 : deriv (fun x => (u x) ^ m) 1 = 0) :
    MemHSigma σ (cosineCoeffs (fun x => (u x) ^ m)) :=
  memHSigma_of_contDiff_two hσ0 hσ (contDiff_two_rpow_of_pos hu hc hupos m) hN0 hN1

/-- **Unconditional chemotaxis-flux factor memberships (m = 1 concrete case).**
For the concrete interval flux `φ = u · v' · (1+v)^{−β}` the only real-exponent
factor is `(1+v)^{−β}` (since `m = 1`).  Given the bootstrap data — `v ∈ C²`
(two derivatives ahead of `u`, from the elliptic gain), `v ≥ 0`, and the Neumann
compatibility of the composed denominator — its cosine coefficients lie in `H^σ`
for `0 ≤ σ < 3/2`.  This is the WALL-A real-exponent residual, discharged. -/
theorem chemotaxisFlux_denom_memHSigma_uncond {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < 3 / 2)
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvnn : ∀ x, 0 ≤ v x) (β : ℝ)
    (hN0 : deriv (fun x => (1 + v x) ^ (-β)) 0 = 0)
    (hN1 : deriv (fun x => (1 + v x) ^ (-β)) 1 = 0) :
    MemHSigma σ (cosineCoeffs (fun x => (1 + v x) ^ (-β))) :=
  memHSigma_one_add_rpow_neg_of_contDiff_two hσ0 hσ hv hvnn β hN0 hN1

#print axioms cos_ibp_step
#print axioms sin_ibp_step
#print axioms cosineCoeffs_decay_one
#print axioms cosineCoeffs_decay_two
#print axioms memHSigma_of_contDiff_two
#print axioms contDiff_two_one_add_rpow_neg
#print axioms memHSigma_one_add_rpow_neg_of_contDiff_two
#print axioms chemotaxisFlux_denom_memHSigma_uncond

end ShenWork.Paper2.IntervalCkComposition
