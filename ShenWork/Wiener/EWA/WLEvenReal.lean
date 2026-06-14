import ShenWork.Wiener.EWA.WienerLevy
import ShenWork.Wiener.EWA.EvenRealClosure

/-!
# EWA brick — the Wiener–Lévy **even-real parity** (`FnegEWA_evenReal`)

This file discharges the single isolated hypothesis
`FnegEWA_evenReal_Hyp` of `EvenRealClosure.lean`: for an **even-real**
`f : EWA T 1`, the Gamma/Laplace Wiener–Lévy element
`FnegEWA f s = (1/Γ s) • ∫_{Ioi 0} t^{s−1} • e^{−t f} dt` is again even-real.

## Strategy — two unconditional involutions

`EvenRealEWA a` is equivalent to `a` being fixed by **two** involutions of
`EWA T 1`:

* the **reflection** `R a` with `(R a).toFun n = a.toFun (−n)` — a `ℂ`-linear
  isometric **ring** automorphism (convolution is reindex-invariant); `a` even
  ⇔ `R a = a`;
* the **conjugation** `C a` with `(C a).toFun n = star (a.toFun n)` (pointwise
  complex-conjugation in the coefficient ring `CT T = C(Icc 0 T, ℂ)`) — an
  `ℝ`-linear isometric **ring** endomorphism; `a` real ⇔ `C a = a`.

Both involutions are *linear isometries over `ℝ`*, hence commute with the
**Bochner integral unconditionally** (`LinearIsometry.integral_comp_comm`, no
integrability hypothesis — exactly what is needed since `FnegEWA` carries no
spectral-floor / `s > 0` hypothesis here), and *continuous ring homs*, hence
commute with `NormedSpace.exp` (`NormedSpace.map_exp`).  Since the integrand
`t^{s−1} • e^{−t f}` is built from real scalars and `e^{−t f}`, and `R`/`C` fix
`f` (by even/real of `f`) and the real scalars, each involution fixes the
integrand pointwise, hence fixes the integral, hence fixes `FnegEWA f s`.

NO `sorry`, `axiom`, `native_decide`, or `admit`.
-/

open scoped BigOperators
open MeasureTheory Set
open ShenWork.GWA ShenWork.Wiener

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### Part 1 — the reflection involution `R : EWA T 1 → EWA T 1`. -/

/-- The reflected sequence `n ↦ a (−n)` stays weighted-ℓ¹ (the weight is
reflection-invariant, and `n ↦ −n` is an equiv). -/
theorem gMemW_refl (a : EWA T 1) : GMemW 1 (fun n => a.toFun (-n)) := by
  have heq := ((Equiv.neg ℤ).summable_iff
    (f := fun n => gWeight 1 n * ‖a.toFun n‖)).2 a.mem
  refine heq.congr (fun n => ?_)
  simp only [Function.comp_apply, Equiv.neg_apply]
  rw [show gWeight 1 (-n) = gWeight 1 n from by simp [gWeight, abs_neg]]

/-- The raw reflection map on `EWA T 1`. -/
def reflRaw (a : EWA T 1) : EWA T 1 := ⟨fun n => a.toFun (-n), gMemW_refl a⟩

@[simp] theorem reflRaw_toFun (a : EWA T 1) (n : ℤ) :
    (reflRaw a).toFun n = a.toFun (-n) := rfl

theorem reflRaw_add (a b : EWA T 1) : reflRaw (a + b) = reflRaw a + reflRaw b := by
  apply GWA.ext; funext n; simp [Pi.add_apply]

theorem reflRaw_smul (c : ℂ) (a : EWA T 1) : reflRaw (c • a) = c • reflRaw a := by
  apply GWA.ext; funext n; simp [Pi.smul_apply]

theorem reflRaw_norm (a : EWA T 1) : ‖reflRaw a‖ = ‖a‖ := by
  show gNorm 1 (fun n => a.toFun (-n)) = gNorm 1 a.toFun
  rw [gNorm, gNorm, ← (Equiv.neg ℤ).tsum_eq (fun n => gWeight 1 n * ‖a.toFun n‖)]
  refine tsum_congr (fun n => ?_)
  simp only [Equiv.neg_apply]
  rw [show gWeight 1 (-n) = gWeight 1 n from by simp [gWeight, abs_neg]]

/-- The reflection commutes with convolution: `R (a*b) = R a * R b`.
The single fiddly point is the `m ↦ −m` reindex of the bilateral `tsum`. -/
theorem reflRaw_mul (a b : EWA T 1) : reflRaw (a * b) = reflRaw a * reflRaw b := by
  apply GWA.ext; funext n
  show gConv a.toFun b.toFun (-n)
      = gConv (fun m => a.toFun (-m)) (fun m => b.toFun (-m)) n
  change (∑' m, a.toFun m * b.toFun (-n - m))
      = ∑' m, a.toFun (-m) * b.toFun (-(n - m))
  rw [← (Equiv.neg ℤ).tsum_eq (fun m => a.toFun m * b.toFun (-n - m))]
  refine tsum_congr (fun m => ?_)
  simp only [Equiv.neg_apply]
  congr 2
  ring

theorem reflRaw_one : reflRaw (1 : EWA T 1) = 1 := by
  apply GWA.ext; funext n
  show (GWA.gOne (-n) : CT T) = GWA.gOne n
  by_cases h : n = 0
  · subst h; simp
  · have hn : (-n) ≠ 0 := by omega
    rw [GWA.gOne, GWA.gOne]; simp [h, hn]

/-- The reflection as a continuous **ring hom** `EWA T 1 →+* EWA T 1`. -/
def reflRH : EWA T 1 →+* EWA T 1 where
  toFun := reflRaw
  map_one' := reflRaw_one
  map_mul' := reflRaw_mul
  map_zero' := by apply GWA.ext; funext n; simp
  map_add' := reflRaw_add

@[simp] theorem reflRH_apply (a : EWA T 1) : reflRH a = reflRaw a := rfl

theorem reflRH_continuous : Continuous (reflRH (T := T)) := by
  refine AddMonoidHomClass.continuous_of_bound reflRH 1 (fun a => ?_)
  rw [reflRH_apply, one_mul]; exact le_of_eq (reflRaw_norm a)

/-- The reflection as an `ℝ`-linear isometry `EWA T 1 →ₗᵢ[ℝ] EWA T 1`
(for the unconditional Bochner-integral commutation). -/
def reflLI : EWA T 1 →ₗᵢ[ℝ] EWA T 1 where
  toFun := reflRaw
  map_add' := reflRaw_add
  map_smul' c a := by
    show reflRaw ((c : ℂ) • a) = (c : ℂ) • reflRaw a
    exact reflRaw_smul (c : ℂ) a
  norm_map' := reflRaw_norm

@[simp] theorem reflLI_apply (a : EWA T 1) : reflLI a = reflRaw a := rfl

/-! ### Part 2 — the conjugation involution `C : EWA T 1 → EWA T 1`. -/

/-- The conjugated sequence `n ↦ star (a n)` stays weighted-ℓ¹
(`star` is isometric on `CT T`, so each summand is unchanged). -/
theorem gMemW_conj (a : EWA T 1) : GMemW 1 (fun n => star (a.toFun n)) := by
  refine a.mem.congr (fun n => ?_)
  rw [norm_star]

/-- The raw conjugation map on `EWA T 1`. -/
def conjRaw (a : EWA T 1) : EWA T 1 := ⟨fun n => star (a.toFun n), gMemW_conj a⟩

@[simp] theorem conjRaw_toFun (a : EWA T 1) (n : ℤ) :
    (conjRaw a).toFun n = star (a.toFun n) := rfl

theorem conjRaw_add (a b : EWA T 1) : conjRaw (a + b) = conjRaw a + conjRaw b := by
  apply GWA.ext; funext n; simp [Pi.add_apply, star_add]

/-- `ℝ`-linearity: for a **real** scalar `(c : ℝ)`, conjugation is homogeneous
(`star (c:ℂ) = (c:ℂ)`). -/
theorem conjRaw_smul_real (c : ℝ) (a : EWA T 1) :
    conjRaw ((c : ℂ) • a) = (c : ℂ) • conjRaw a := by
  apply GWA.ext; funext n
  show star (((c : ℂ) • a.toFun) n) = ((c : ℂ) • fun m => star (a.toFun m)) n
  rw [Pi.smul_apply, Pi.smul_apply, star_smul, Complex.star_def, Complex.conj_ofReal]

theorem conjRaw_norm (a : EWA T 1) : ‖conjRaw a‖ = ‖a‖ := by
  show gNorm 1 (fun n => star (a.toFun n)) = gNorm 1 a.toFun
  rw [gNorm, gNorm]
  refine tsum_congr (fun n => ?_)
  rw [norm_star]

/-- Conjugation commutes with convolution: `C (a*b) = C a * C b`
(`star` is a continuous ring hom on the commutative coefficient ring `CT T`,
hence distributes over the convolution `tsum` via `tsum_star` + `star_mul'`). -/
theorem conjRaw_mul (a b : EWA T 1) : conjRaw (a * b) = conjRaw a * conjRaw b := by
  apply GWA.ext; funext n
  show star (gConv a.toFun b.toFun n)
      = gConv (fun m => star (a.toFun m)) (fun m => star (b.toFun m)) n
  change star (∑' m, a.toFun m * b.toFun (n - m))
      = ∑' m, star (a.toFun m) * star (b.toFun (n - m))
  rw [tsum_star]
  refine tsum_congr (fun m => ?_)
  rw [star_mul']

theorem conjRaw_one : conjRaw (1 : EWA T 1) = 1 := by
  apply GWA.ext; funext n
  show star (GWA.gOne n : CT T) = GWA.gOne n
  by_cases h : n = 0
  · subst h; rw [GWA.gOne]; simp
  · rw [GWA.gOne]; simp [h]

/-- The conjugation as a continuous **ring hom** `EWA T 1 →+* EWA T 1`. -/
def conjRH : EWA T 1 →+* EWA T 1 where
  toFun := conjRaw
  map_one' := conjRaw_one
  map_mul' := conjRaw_mul
  map_zero' := by apply GWA.ext; funext n; simp
  map_add' := conjRaw_add

@[simp] theorem conjRH_apply (a : EWA T 1) : conjRH a = conjRaw a := rfl

theorem conjRH_continuous : Continuous (conjRH (T := T)) := by
  refine AddMonoidHomClass.continuous_of_bound conjRH 1 (fun a => ?_)
  rw [conjRH_apply, one_mul]; exact le_of_eq (conjRaw_norm a)

/-- The conjugation as an `ℝ`-linear isometry `EWA T 1 →ₗᵢ[ℝ] EWA T 1`
(for the unconditional Bochner-integral commutation). -/
def conjLI : EWA T 1 →ₗᵢ[ℝ] EWA T 1 where
  toFun := conjRaw
  map_add' := conjRaw_add
  map_smul' c a := by
    show conjRaw ((c : ℂ) • a) = (c : ℂ) • conjRaw a
    exact conjRaw_smul_real (c : ℝ) a
  norm_map' := conjRaw_norm

@[simp] theorem conjLI_apply (a : EWA T 1) : conjLI a = conjRaw a := rfl

/-! ### Part 3 — the even-real ⇔ fixed-point bridge. -/

/-- **Evenness ⇔ reflection-fixed.**  `a` is even (at every slice) iff `R a = a`. -/
theorem even_iff_reflRaw_eq (a : EWA T 1) :
    (∀ (τ : TimeDom T) (n : ℤ), (sliceWA τ a).toFun (-n) = (sliceWA τ a).toFun n)
      ↔ reflRaw a = a := by
  constructor
  · intro h
    apply GWA.ext; funext n
    apply ContinuousMap.ext; intro τ
    exact h τ n
  · intro h τ n
    have := congrFun (congrArg GWA.toFun h) n
    rw [reflRaw_toFun] at this
    show (a.toFun (-n)) τ = (a.toFun n) τ
    rw [this]

/-- **Reality ⇔ conjugation-fixed.**  `a` is real (at every slice) iff `C a = a`. -/
theorem real_iff_conjRaw_eq (a : EWA T 1) :
    (∀ (τ : TimeDom T) (n : ℤ), ((sliceWA τ a).toFun n).im = 0)
      ↔ conjRaw a = a := by
  constructor
  · intro h
    apply GWA.ext; funext n
    apply ContinuousMap.ext; intro τ
    show star ((a.toFun n) τ) = (a.toFun n) τ
    rw [Complex.star_def]; exact Complex.conj_eq_iff_im.2 (h τ n)
  · intro h τ n
    have := congrFun (congrArg GWA.toFun h) n
    rw [conjRaw_toFun] at this
    have hτ := DFunLike.congr_fun this τ
    rw [ContinuousMap.star_apply] at hτ
    show ((a.toFun n) τ).im = 0
    refine Complex.conj_eq_iff_im.1 ?_
    rw [← Complex.star_def]; exact hτ

/-- Packaged: `EvenRealEWA a` iff `a` is fixed by **both** involutions. -/
theorem evenReal_iff_fixed (a : EWA T 1) :
    EvenRealEWA a ↔ (reflRaw a = a ∧ conjRaw a = a) := by
  constructor
  · intro h
    exact ⟨(even_iff_reflRaw_eq a).1 h.even, (real_iff_conjRaw_eq a).1 h.real⟩
  · intro ⟨hR, hC⟩
    exact ⟨(even_iff_reflRaw_eq a).2 hR, (real_iff_conjRaw_eq a).2 hC⟩

/-! ### Part 4 — the involutions fix `FnegEWA f s`. -/

/-- `R` commutes with `NormedSpace.exp` (continuous ring hom). -/
theorem reflRaw_exp (x : EWA T 1) :
    reflRaw (NormedSpace.exp x) = NormedSpace.exp (reflRaw x) := by
  have := NormedSpace.map_exp reflRH reflRH_continuous x
  simpa using this

/-- `C` commutes with `NormedSpace.exp` (continuous ring hom). -/
theorem conjRaw_exp (x : EWA T 1) :
    conjRaw (NormedSpace.exp x) = NormedSpace.exp (conjRaw x) := by
  have := NormedSpace.map_exp conjRH conjRH_continuous x
  simpa using this

/-- `R` fixes the integrand `t ↦ t^{s−1} • e^{−t f}` when `R f = f`. -/
theorem reflRaw_gammaIntegrand (f : EWA T 1) (s : ℝ) (hf : reflRaw f = f) (t : ℝ) :
    reflRaw (gammaIntegrandEWA f s t) = gammaIntegrandEWA f s t := by
  rw [gammaIntegrandEWA, reflRaw_smul, reflRaw_exp, reflRaw_smul, hf]

/-- `C` fixes the integrand when `C f = f`. -/
theorem conjRaw_gammaIntegrand (f : EWA T 1) (s : ℝ) (hf : conjRaw f = f) (t : ℝ) :
    conjRaw (gammaIntegrandEWA f s t) = gammaIntegrandEWA f s t := by
  rw [gammaIntegrandEWA, conjRaw_smul_real, conjRaw_exp, conjRaw_smul_real, hf]

/-- `R` fixes the Bochner integral `∫ t^{s−1} • e^{−t f}` when `R f = f`
(unconditionally, via the `ℝ`-linear isometry `reflLI`). -/
theorem reflRaw_integral (f : EWA T 1) (s : ℝ) (hf : reflRaw f = f) :
    reflRaw (∫ t in Ioi 0, gammaIntegrandEWA f s t)
      = ∫ t in Ioi 0, gammaIntegrandEWA f s t := by
  have hcomm := LinearIsometry.integral_comp_comm reflLI (μ := volume.restrict (Ioi 0))
    (gammaIntegrandEWA f s)
  rw [reflLI_apply] at hcomm
  rw [← hcomm]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  rw [reflLI_apply, reflRaw_gammaIntegrand f s hf t]

/-- `C` fixes the Bochner integral when `C f = f`. -/
theorem conjRaw_integral (f : EWA T 1) (s : ℝ) (hf : conjRaw f = f) :
    conjRaw (∫ t in Ioi 0, gammaIntegrandEWA f s t)
      = ∫ t in Ioi 0, gammaIntegrandEWA f s t := by
  have hcomm := LinearIsometry.integral_comp_comm conjLI (μ := volume.restrict (Ioi 0))
    (gammaIntegrandEWA f s)
  rw [conjLI_apply] at hcomm
  rw [← hcomm]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  rw [conjLI_apply, conjRaw_gammaIntegrand f s hf t]

/-- **The Wiener–Lévy even-real parity.**  For an even-real `f : EWA T 1`,
`FnegEWA f s` is even-real. -/
theorem FnegEWA_evenReal (f : EWA T 1) (s : ℝ) (hf : EvenRealEWA f) :
    EvenRealEWA (FnegEWA f s) := by
  rw [evenReal_iff_fixed] at hf ⊢
  obtain ⟨hR, hC⟩ := hf
  refine ⟨?_, ?_⟩
  · rw [FnegEWA, reflRaw_smul, reflRaw_integral f s hR]
  · rw [FnegEWA, conjRaw_smul_real, conjRaw_integral f s hC]

/-- The isolated hypothesis `FnegEWA_evenReal_Hyp` of `EvenRealClosure` is now a
theorem. -/
theorem FnegEWA_evenReal_Hyp_proved : FnegEWA_evenReal_Hyp :=
  fun f s hf => FnegEWA_evenReal f s hf

end ShenWork.EWA

#print axioms ShenWork.EWA.FnegEWA_evenReal
#print axioms ShenWork.EWA.FnegEWA_evenReal_Hyp_proved
