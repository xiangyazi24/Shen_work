import ShenWork.Wiener.EWA.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# EWA Duhamel operators (value `𝒱` ≤T + divergence `𝒟` √T) — sup-inside (brick B1)

This brick (Phase B, cron2 Brick 4) delivers the **per-mode Volterra time-integral
operators** of the Duhamel formula on the time-coefficient ring `CT T :=
C(Icc 0 T, ℂ)`, and lifts them to the time-envelope algebra `EWA T r` via the
committed master coeffwise lemma `GWA.coeffwiseCLM`.

For a time-coefficient `f ∈ CT T` and Fourier mode `n`, with `y² := (nπ)²`:

* **Value** `(𝒱f)(t) = ∫₀ᵗ e^{−(t−s)(nπ)²}·f(s) ds`, with the per-mode bound
  `sup_{t∈[0,T]} |(𝒱f)(t)| ≤ T · sup_s|f(s)|`.
* **Divergence** `(𝒟f)(t) = ∫₀ᵗ e^{−(t−s)(nπ)²}·(inπ)·f(s) ds`, with the
  genuinely-new **sup-inside** per-mode bound
  `sup_{t∈[0,T]} |(𝒟f)(t)| ≤ C₀·√T · sup_s|f(s)|`, the sup taken *inside* the
  coefficient.  Here `C₀ = 1` is a clean finite upper bound for the true sup
  `sup_{u≥0}(1−e^{−u})/√u ≈ 0.638` (the math constant of the estimate); the
  bound `(1−e^{−u})/√u ≤ 1` is proved as `c0_key`.

The two operators are genuine CT→CT continuous linear maps:

* **linear in `f`** — the interval integral is linear in its (continuous)
  integrand, which is linear in `f` through `Set.IccExtend`;
* **continuous in `t`** — factoring `e^{−(t−s)y²} = e^{−ty²}·e^{sy²}` makes the
  inner integral `∫₀ᵗ e^{sy²}f(s)ds` a primitive whose upper-limit dependence is
  continuous (`intervalIntegral.continuous_primitive`), times the continuous
  prefactor `e^{−ty²}`.

The EWA lifts `valDuhamelEWA`/`divDuhamelEWA` are `r → r` CLMs via
`GWA.coeffwiseCLM`, with the `EWA`-level bounds `valDuhamelEWA_bound`
(`≤ T·‖·‖`) and `divDuhamelEWA_bound` (`≤ C₀√T·‖·‖`, **the √T contraction**).
-/

open scoped BigOperators
open Set Real MeasureTheory intervalIntegral
open ShenWork.GWA ShenWork.Wiener

namespace ShenWork.EWA

/-! ### The constant `C₀` and its key sup bound. -/

/-- The √T-Duhamel constant.  The true value is `sup_{u≥0}(1−e^{−u})/√u ≈ 0.638`;
we use the clean finite upper bound `C₀ = 1`, which dominates it (`c0_key`). -/
noncomputable def C₀ : ℝ := 1

theorem C₀_nonneg : (0 : ℝ) ≤ C₀ := by unfold C₀; norm_num

/-- **The `C₀` sup bound.** `(1−e^{−u})/√u ≤ 1 = C₀` for all `u > 0` (the genuine
finite-constant fact behind the √T estimate).  As `u→0` it `~√u→0`; as `u→∞` it
`~1/√u→0`; the bound `1−e^{−u} ≤ min(u,1) ≤ √u` gives the clean dominating `1`. -/
theorem c0_key {u : ℝ} (hu : 0 < u) : (1 - Real.exp (-u)) / Real.sqrt u ≤ C₀ := by
  unfold C₀
  rw [div_le_one (Real.sqrt_pos.mpr hu)]
  rcases le_or_gt u 1 with h | h
  · have h1 : 1 - Real.exp (-u) ≤ u := by have := Real.add_one_le_exp (-u); linarith
    have h2 : u ≤ Real.sqrt u := by
      calc u = Real.sqrt (u ^ 2) := by rw [Real.sqrt_sq hu.le]
        _ ≤ Real.sqrt u := by apply Real.sqrt_le_sqrt; nlinarith [hu, h]
    linarith
  · have h1 : 1 - Real.exp (-u) ≤ 1 := by have := Real.exp_nonneg (-u); linarith
    have h2 : (1 : ℝ) ≤ Real.sqrt u := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; apply Real.sqrt_le_sqrt; linarith
    linarith

/-! ### The scalar kernel integral `∫₀ᵗ e^{−(t−s)y²} ds = (1−e^{−ty²})/y²`. -/

/-- The scalar time-integral of the heat kernel: `∫₀ᵗ e^{−(t−s)y2} ds =
(1−e^{−ty2})/y2` for `y2 > 0` (substitution `u = t−s` + the exp integral). -/
theorem scalar_kernel_integral (y2 t : ℝ) (hy2 : 0 < y2) :
    (∫ s in (0:ℝ)..t, Real.exp (-((t - s) * y2)))
      = (1 - Real.exp (-(t * y2))) / y2 := by
  have hcongr : (∫ s in (0:ℝ)..t, Real.exp (-((t - s) * y2)))
      = ∫ s in (0:ℝ)..t, Real.exp (-(t * y2)) * Real.exp (s * y2) := by
    apply intervalIntegral.integral_congr; intro s hs
    show Real.exp (-((t - s) * y2)) = Real.exp (-(t * y2)) * Real.exp (s * y2)
    rw [← Real.exp_add]; congr 1; ring
  rw [hcongr, intervalIntegral.integral_const_mul]
  have hexp : (∫ s in (0:ℝ)..t, Real.exp (s * y2)) = (Real.exp (t * y2) - 1) / y2 := by
    rw [integral_comp_mul_right (fun x => Real.exp x) (ne_of_gt hy2), integral_exp]
    simp [div_eq_inv_mul, mul_comm]
  rw [hexp, mul_div_assoc', mul_sub, mul_one, ← Real.exp_add,
    show -(t * y2) + t * y2 = 0 by ring, Real.exp_zero]

/-! ### The per-mode Duhamel kernel function on `ℝ` and its continuity. -/

section PerMode

variable {T : ℝ}

/-- The per-mode Duhamel time-integral `t ↦ ∫₀ᵗ e^{−(t−s)y²}·coef·g(s) ds`, for a
spatial coefficient `coef : ℂ`, an extended time-coefficient `g : ℝ → ℂ` and
spectral square `y2 = (nπ)²`.  `coef = 1` gives the value operator; `coef = inπ`
the divergence operator. -/
noncomputable def duhFun (y2 : ℝ) (coef : ℂ) (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ s in (0:ℝ)..t, Complex.exp (-((↑(t - s)) * (↑y2))) * (coef * g s)

/-- **Continuity in the upper limit `t`.**  Factoring `e^{−(t−s)y²} =
e^{−ty²}·e^{sy²}` makes `duhFun` the product of the continuous prefactor
`e^{−ty²}` with the continuous primitive `t ↦ ∫₀ᵗ e^{sy²}·coef·g(s) ds`. -/
theorem duhFun_continuous (y2 : ℝ) (coef : ℂ) {g : ℝ → ℂ} (hg : Continuous g) :
    Continuous (duhFun y2 coef g) := by
  have hfact : duhFun y2 coef g
      = fun t : ℝ => Complex.exp (-((↑t) * (↑y2)))
          * ∫ s in (0:ℝ)..t, Complex.exp ((↑s) * (↑y2)) * (coef * g s) := by
    funext t
    show (∫ s in (0:ℝ)..t, Complex.exp (-((↑(t - s)) * (↑y2))) * (coef * g s))
        = Complex.exp (-((↑t) * (↑y2)))
          * ∫ s in (0:ℝ)..t, Complex.exp ((↑s) * (↑y2)) * (coef * g s)
    have h1 : (∫ s in (0:ℝ)..t, Complex.exp (-((↑(t - s)) * (↑y2))) * (coef * g s))
        = ∫ s in (0:ℝ)..t,
            Complex.exp (-((↑t) * (↑y2))) * (Complex.exp ((↑s) * (↑y2)) * (coef * g s)) := by
      apply intervalIntegral.integral_congr; intro s hs
      have hexp : Complex.exp (-((↑(t - s)) * (↑y2)))
          = Complex.exp (-((↑t) * (↑y2))) * Complex.exp ((↑s) * (↑y2)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      simp only []; rw [hexp]; ring
    rw [h1]; exact intervalIntegral.integral_const_mul _ _
  rw [hfact]
  refine Continuous.mul (by fun_prop) ?_
  apply intervalIntegral.continuous_primitive
  intro a b; apply Continuous.intervalIntegrable; fun_prop

end PerMode

/-! ### The extended time-coefficient `g = IccExtend f` and pointwise facts. -/

section Extend

variable {T : ℝ}

/-- The constant-extension of a time-coefficient `f ∈ CT T` to all of `ℝ`
(`Set.IccExtend`), continuous on `ℝ`, agreeing with `f` on `[0,T]`. -/
noncomputable def ext (hT : 0 ≤ T) (f : CT T) : ℝ → ℂ :=
  Set.IccExtend hT (f : Set.Icc (0:ℝ) T → ℂ)

theorem ext_continuous (hT : 0 ≤ T) (f : CT T) : Continuous (ext hT f) :=
  f.continuous.Icc_extend'

theorem ext_of_mem (hT : 0 ≤ T) (f : CT T) {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) T) :
    ext hT f s = f ⟨s, hs⟩ := Set.IccExtend_of_mem hT _ hs

theorem norm_ext_le (hT : 0 ≤ T) (f : CT T) {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) T) :
    ‖ext hT f s‖ ≤ ‖f‖ := by
  rw [ext_of_mem hT f hs]; exact f.norm_coe_le_norm _

theorem ext_add (hT : 0 ≤ T) (f g : CT T) :
    ext hT (f + g) = ext hT f + ext hT g := by
  funext s; simp only [ext, Set.IccExtend, Function.comp, ContinuousMap.add_apply,
    Pi.add_apply]

theorem ext_smul (hT : 0 ≤ T) (c : ℂ) (f : CT T) :
    ext hT (c • f) = c • ext hT f := by
  funext s; simp only [ext, Set.IccExtend, Function.comp, ContinuousMap.smul_apply,
    Pi.smul_apply]

end Extend

/-! ### The per-mode CT→CT operators as bundled `ContinuousMap`s. -/

section Operators

variable {T : ℝ}

/-- The bundled CT-valued image of `f` under the Duhamel operator with spatial
coefficient `coef` and spectral square `y2`: the continuous map
`t ↦ ∫₀ᵗ e^{−(t−s)y²}·coef·f(s) ds` on `[0,T]`. -/
noncomputable def duhCM (hT : 0 ≤ T) (y2 : ℝ) (coef : ℂ) (f : CT T) : CT T :=
  ⟨fun x => duhFun y2 coef (ext hT f) x,
    (duhFun_continuous y2 coef (ext_continuous hT f)).comp continuous_subtype_val⟩

@[simp] theorem duhCM_apply (hT : 0 ≤ T) (y2 : ℝ) (coef : ℂ) (f : CT T)
    (x : Set.Icc (0:ℝ) T) :
    (duhCM hT y2 coef f) x = duhFun y2 coef (ext hT f) x := rfl

/-- `duhCM` is additive in `f` (interval integral of a sum, integrands
continuous). -/
theorem duhCM_add (hT : 0 ≤ T) (y2 : ℝ) (coef : ℂ) (f g : CT T) :
    duhCM hT y2 coef (f + g) = duhCM hT y2 coef f + duhCM hT y2 coef g := by
  apply ContinuousMap.ext; intro x
  show duhFun y2 coef (ext hT (f + g)) x
      = duhFun y2 coef (ext hT f) x + duhFun y2 coef (ext hT g) x
  rw [ext_add]
  unfold duhFun
  rw [← intervalIntegral.integral_add]
  · apply intervalIntegral.integral_congr; intro s hs
    show Complex.exp _ * (coef * (ext hT f + ext hT g) s)
        = Complex.exp _ * (coef * ext hT f s) + Complex.exp _ * (coef * ext hT g s)
    rw [Pi.add_apply]; ring
  · apply Continuous.intervalIntegrable
    have := ext_continuous hT f; fun_prop
  · apply Continuous.intervalIntegrable
    have := ext_continuous hT g; fun_prop

/-- `duhCM` is `ℂ`-homogeneous in `f` (scalar pulls out of the integral). -/
theorem duhCM_smul (hT : 0 ≤ T) (y2 : ℝ) (coef : ℂ) (c : ℂ) (f : CT T) :
    duhCM hT y2 coef (c • f) = c • duhCM hT y2 coef f := by
  apply ContinuousMap.ext; intro x
  show duhFun y2 coef (ext hT (c • f)) x = c • duhFun y2 coef (ext hT f) x
  rw [ext_smul, smul_eq_mul]
  unfold duhFun
  have h1 : (∫ s in (0:ℝ)..(x:ℝ),
        Complex.exp (-((↑((x:ℝ) - s)) * (↑y2))) * (coef * (c • ext hT f) s))
      = ∫ s in (0:ℝ)..(x:ℝ),
          c * (Complex.exp (-((↑((x:ℝ) - s)) * (↑y2))) * (coef * ext hT f s)) := by
    apply intervalIntegral.integral_congr; intro s hs
    show Complex.exp _ * (coef * (c • ext hT f) s)
        = c * (Complex.exp _ * (coef * ext hT f s))
    rw [Pi.smul_apply, smul_eq_mul]; ring
  rw [h1]; exact intervalIntegral.integral_const_mul _ _

/-! #### The value operator (`coef = 1`, bound `≤ T`). -/

/-- The per-mode **value** Duhamel kernel applied to `f`, `coef = 1`. -/
noncomputable def duhValMode (n : ℤ) (f : CT T) (hT : 0 ≤ T) : CT T :=
  duhCM hT (((n : ℝ) * Real.pi) ^ 2) 1 f

/-- **Per-mode value bound** `sup_t |(𝒱f)(t)| ≤ T · sup_s|f(s)|`.  Pointwise:
`|∫₀ᵗ e^{−(t−s)y²}f(s)ds| ≤ ∫₀ᵗ 1·‖f‖ ds = t·‖f‖ ≤ T·‖f‖`. -/
theorem duhValMode_norm_le (n : ℤ) (f : CT T) (hT : 0 ≤ T) :
    ‖duhValMode n f hT‖ ≤ T * ‖f‖ := by
  set y2 : ℝ := ((n : ℝ) * Real.pi) ^ 2 with hy2def
  have hy2 : 0 ≤ y2 := by rw [hy2def]; positivity
  have hTnn : 0 ≤ T := hT
  rw [show duhValMode n f hT = duhCM hT y2 1 f from rfl,
    ContinuousMap.norm_le _ (by positivity)]
  intro x
  show ‖duhFun y2 1 (ext hT f) x‖ ≤ T * ‖f‖
  set t : ℝ := (x : ℝ) with htdef
  have ht0 : 0 ≤ t := x.2.1
  have htT : t ≤ T := x.2.2
  have hconst : ∀ s ∈ Set.uIoc (0:ℝ) t,
      ‖Complex.exp (-((↑(t - s)) * (↑y2))) * (1 * ext hT f s)‖ ≤ ‖f‖ := by
    intro s hs
    rw [Set.uIoc_of_le ht0] at hs
    have hsmem : s ∈ Set.Icc (0:ℝ) T := ⟨hs.1.le, le_trans hs.2 htT⟩
    rw [norm_mul, one_mul]
    have hknorm : ‖Complex.exp (-((↑(t - s)) * (↑y2)))‖ ≤ 1 := by
      rw [Complex.norm_exp]
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        sub_zero, mul_zero]
      rw [Real.exp_le_one_iff]
      nlinarith [hs.1, hs.2, hy2]
    calc ‖Complex.exp (-((↑(t - s)) * (↑y2)))‖ * ‖ext hT f s‖
        ≤ 1 * ‖f‖ :=
          mul_le_mul hknorm (norm_ext_le hT f hsmem) (norm_nonneg _) (by norm_num)
      _ = ‖f‖ := one_mul _
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const hconst
  have hbn : ‖duhFun y2 1 (ext hT f) t‖ ≤ ‖f‖ * |t - 0| := by
    unfold duhFun; exact hb
  calc ‖duhFun y2 1 (ext hT f) t‖ ≤ ‖f‖ * |t - 0| := hbn
    _ = ‖f‖ * t := by rw [sub_zero, abs_of_nonneg ht0]
    _ ≤ T * ‖f‖ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right htT (norm_nonneg _)

/-! #### The divergence operator (`coef = inπ`, the sup-inside √T bound). -/

/-- The per-mode **divergence** Duhamel kernel applied to `f`, `coef = inπ`. -/
noncomputable def duhDivMode (n : ℤ) (f : CT T) (hT : 0 ≤ T) : CT T :=
  duhCM hT (((n : ℝ) * Real.pi) ^ 2) (Complex.I * ((n : ℝ) * Real.pi)) f

/-- **The genuinely-new sup-inside per-mode √T bound**
`sup_t |(𝒟f)(t)| ≤ C₀·√T · sup_s|f(s)|`.  For `n = 0` the coefficient `inπ·0 =
0` makes `(𝒟f) = 0`; for `n ≠ 0`, with `y = |nπ| > 0`, the pointwise estimate
`|(𝒟f)(t)| ≤ ‖f‖·(1−e^{−ty²})/y ≤ ‖f‖·√T·C₀` (monotone in `t≤T`, then `c0_key`). -/
theorem duhDivMode_norm_le (n : ℤ) (f : CT T) (hT : 0 ≤ T) :
    ‖duhDivMode n f hT‖ ≤ (C₀ * Real.sqrt T) * ‖f‖ := by
  have hCnn : 0 ≤ C₀ * Real.sqrt T := by have := C₀_nonneg; positivity
  have hCfnn : 0 ≤ (C₀ * Real.sqrt T) * ‖f‖ := mul_nonneg hCnn (norm_nonneg _)
  set y : ℝ := (n : ℝ) * Real.pi with hydef
  set y2 : ℝ := ((n : ℝ) * Real.pi) ^ 2 with hy2def
  have hunfold : duhDivMode n f hT = duhCM hT y2 (Complex.I * (↑y)) f := by
    show duhCM hT (((n : ℝ) * Real.pi) ^ 2) (Complex.I * ((n : ℝ) * Real.pi)) f
        = duhCM hT y2 (Complex.I * (↑y)) f
    rw [hydef, hy2def]; norm_cast
  rw [hunfold, ContinuousMap.norm_le _ hCfnn]
  intro x
  show ‖duhFun y2 (Complex.I * (↑y)) (ext hT f) x‖ ≤ (C₀ * Real.sqrt T) * ‖f‖
  set t : ℝ := (x : ℝ) with htdef
  have ht0 : 0 ≤ t := x.2.1
  have htT : t ≤ T := x.2.2
  rcases eq_or_ne n 0 with hn | hn
  · -- n = 0 ⇒ coefficient is 0 ⇒ integrand 0 ⇒ integral 0.
    have hy0 : y = 0 := by rw [hydef, hn]; push_cast; ring
    have : duhFun y2 (Complex.I * (↑y)) (ext hT f) t = 0 := by
      unfold duhFun
      rw [show (Complex.I * (↑y)) = 0 by rw [hy0]; push_cast; ring]
      simp
    rw [this, norm_zero]; positivity
  · -- n ≠ 0 ⇒ y ≠ 0 ⇒ the sharp √T estimate.
    have hypos : 0 < |y| := by
      rw [abs_pos]; rw [hydef]
      exact mul_ne_zero (by exact_mod_cast hn) (ne_of_gt Real.pi_pos)
    have hyy : |y| ^ 2 = y2 := by rw [hy2def, hydef, sq_abs]
    have hy2pos : 0 < y2 := by rw [← hyy]; positivity
    -- norm ≤ ∫‖·‖ ≤ ∫ majorant = ‖f‖·(1−e^{−ty²})/|y|
    have hs1 : ‖duhFun y2 (Complex.I * (↑y)) (ext hT f) t‖
        ≤ ∫ s in (0:ℝ)..t,
            ‖Complex.exp (-((↑(t - s)) * (↑y2))) * (Complex.I * (↑y) * ext hT f s)‖ := by
      unfold duhFun; exact intervalIntegral.norm_integral_le_integral_norm ht0
    have hmajint : IntervalIntegrable
        (fun s => ‖f‖ * |y| * Real.exp (-((t - s) * y2))) volume 0 t :=
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    have hintnorm : IntervalIntegrable
        (fun s => ‖Complex.exp (-((↑(t - s)) * (↑y2))) * (Complex.I * (↑y) * ext hT f s)‖)
        volume 0 t := by
      apply Continuous.intervalIntegrable; apply Continuous.norm
      exact (by fun_prop : Continuous fun s => Complex.exp (-((↑(t - s)) * (↑y2)))).mul
        (continuous_const.mul (ext_continuous hT f))
    have hpt : ∀ s ∈ Set.Ioo (0:ℝ) t,
        ‖Complex.exp (-((↑(t - s)) * (↑y2))) * (Complex.I * (↑y) * ext hT f s)‖
          ≤ ‖f‖ * |y| * Real.exp (-((t - s) * y2)) := by
      intro s hs
      have hsmem : s ∈ Set.Icc (0:ℝ) T := ⟨hs.1.le, le_trans hs.2.le htT⟩
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
      have hknorm : ‖Complex.exp (-((↑(t - s)) * (↑y2)))‖ = Real.exp (-((t - s) * y2)) := by
        rw [Complex.norm_exp]
        simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          sub_zero, mul_zero]
      rw [hknorm]
      have hes : 0 ≤ Real.exp (-((t - s) * y2)) := Real.exp_nonneg _
      calc Real.exp (-((t - s) * y2)) * (|y| * ‖ext hT f s‖)
          ≤ Real.exp (-((t - s) * y2)) * (|y| * ‖f‖) := by
            apply mul_le_mul_of_nonneg_left _ hes
            exact mul_le_mul_of_nonneg_left (norm_ext_le hT f hsmem) (abs_nonneg _)
        _ = ‖f‖ * |y| * Real.exp (-((t - s) * y2)) := by ring
    have hs2 : (∫ s in (0:ℝ)..t,
          ‖Complex.exp (-((↑(t - s)) * (↑y2))) * (Complex.I * (↑y) * ext hT f s)‖)
        ≤ ∫ s in (0:ℝ)..t, ‖f‖ * |y| * Real.exp (-((t - s) * y2)) :=
      intervalIntegral.integral_mono_on_of_le_Ioo ht0 hintnorm hmajint hpt
    have hs3 : (∫ s in (0:ℝ)..t, ‖f‖ * |y| * Real.exp (-((t - s) * y2)))
        = ‖f‖ * |y| * ((1 - Real.exp (-(t * y2))) / y2) := by
      rw [intervalIntegral.integral_const_mul, scalar_kernel_integral _ _ hy2pos]
    -- final: ‖f‖·|y|·(1−e^{−ty²})/y² = ‖f‖·(1−e^{−ty²})/|y| ≤ C₀·√T·‖f‖.
    have hfin : ‖f‖ * |y| * ((1 - Real.exp (-(t * y2))) / y2)
        ≤ (C₀ * Real.sqrt T) * ‖f‖ := by
      have hyabs : |y| ^ 2 = y2 := hyy
      have heq : ‖f‖ * |y| * ((1 - Real.exp (-(t * y2))) / y2)
          = ‖f‖ * ((1 - Real.exp (-(t * y2))) / |y|) := by
        rw [← hyabs]; field_simp
      rw [heq]
      have hnumnn : 0 ≤ 1 - Real.exp (-(t * y2)) := by
        have : Real.exp (-(t * y2)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [hy2pos.le, ht0])
        linarith
      have hmono : 1 - Real.exp (-(t * y2)) ≤ 1 - Real.exp (-(T * y2)) := by
        have : Real.exp (-(T * y2)) ≤ Real.exp (-(t * y2)) :=
          Real.exp_le_exp.mpr (by nlinarith [hy2pos.le, htT])
        linarith
      rcases eq_or_lt_of_le hT with hT0 | hTpos
      · -- T = 0 ⇒ t = 0 ⇒ numerator vanishes.
        have ht00 : t = 0 := le_antisymm (by rw [← hT0] at htT; exact htT) ht0
        rw [ht00, zero_mul, neg_zero, Real.exp_zero, sub_self, zero_div, mul_zero]
        have := norm_nonneg f; positivity
      · -- T > 0 ⇒ u = T·y2 > 0 ⇒ c0_key.
        set u : ℝ := T * y2 with hudef
        have hupos : 0 < u := by rw [hudef]; exact mul_pos hTpos hy2pos
        have hck := c0_key hupos
        have hsu : 1 - Real.exp (-u) ≤ C₀ * Real.sqrt u := by
          rwa [div_le_iff₀ (Real.sqrt_pos.mpr hupos)] at hck
        have hsqrtu : Real.sqrt u = Real.sqrt T * |y| := by
          rw [hudef, ← hyy, Real.sqrt_mul hT, Real.sqrt_sq (abs_nonneg _)]
        have hfnn : 0 ≤ ‖f‖ := norm_nonneg f
        -- ‖f‖·(1−e^{−ty²})/|y| ≤ ‖f‖·(C₀√T·|y|)/|y| = C₀√T·‖f‖.
        have hstep : ‖f‖ * ((1 - Real.exp (-(t * y2))) / |y|)
            ≤ ‖f‖ * ((C₀ * Real.sqrt T * |y|) / |y|) := by
          apply mul_le_mul_of_nonneg_left _ hfnn
          gcongr ?_ / |y|
          calc 1 - Real.exp (-(t * y2)) ≤ 1 - Real.exp (-(T * y2)) := hmono
            _ = 1 - Real.exp (-u) := by rw [hudef]
            _ ≤ C₀ * Real.sqrt u := hsu
            _ = C₀ * Real.sqrt T * |y| := by rw [hsqrtu]; ring
        calc ‖f‖ * ((1 - Real.exp (-(t * y2))) / |y|)
            ≤ ‖f‖ * ((C₀ * Real.sqrt T * |y|) / |y|) := hstep
          _ = (C₀ * Real.sqrt T) * ‖f‖ := by field_simp
    calc ‖duhFun y2 (Complex.I * (↑y)) (ext hT f) t‖
        ≤ _ := hs1
      _ ≤ _ := hs2
      _ = ‖f‖ * |y| * ((1 - Real.exp (-(t * y2))) / y2) := hs3
      _ ≤ (C₀ * Real.sqrt T) * ‖f‖ := hfin

/-! ### The per-mode operators as bundled CT→CT CLMs. -/

/-- The per-mode Duhamel operator `duhCM hT y2 coef` bundled as a `ℂ`-linear map
on `CT T`, from the additivity `duhCM_add` and homogeneity `duhCM_smul`. -/
noncomputable def duhCMLM (hT : 0 ≤ T) (y2 : ℝ) (coef : ℂ) : CT T →ₗ[ℂ] CT T where
  toFun f := duhCM hT y2 coef f
  map_add' f g := duhCM_add hT y2 coef f g
  map_smul' c f := duhCM_smul hT y2 coef c f

@[simp] theorem duhCMLM_apply (hT : 0 ≤ T) (y2 : ℝ) (coef : ℂ) (f : CT T) :
    duhCMLM hT y2 coef f = duhCM hT y2 coef f := rfl

/-- The per-mode **value** Duhamel operator as a CLM `CT T →L[ℂ] CT T`, the
linear map `duhCMLM` made continuous with the per-mode `≤ T` bound. -/
noncomputable def duhValModeCLM (n : ℤ) (hT : 0 ≤ T) : CT T →L[ℂ] CT T :=
  (duhCMLM hT (((n : ℝ) * Real.pi) ^ 2) 1).mkContinuous (T * 1)
    (fun f => by
      rw [duhCMLM_apply, mul_one]
      have := duhValMode_norm_le n f hT
      rwa [show duhValMode n f hT = duhCM hT (((n : ℝ) * Real.pi) ^ 2) 1 f from rfl] at this)

@[simp] theorem duhValModeCLM_apply (n : ℤ) (hT : 0 ≤ T) (f : CT T) :
    duhValModeCLM n hT f = duhCM hT (((n : ℝ) * Real.pi) ^ 2) 1 f := rfl

/-- The per-mode value CLM bound `‖duhValModeCLM n f‖ ≤ T·‖f‖`. -/
theorem duhValModeCLM_norm_le (n : ℤ) (hT : 0 ≤ T) (f : CT T) :
    ‖duhValModeCLM n hT f‖ ≤ T * ‖f‖ := by
  rw [duhValModeCLM_apply]
  have := duhValMode_norm_le n f hT
  rwa [show duhValMode n f hT = duhCM hT (((n : ℝ) * Real.pi) ^ 2) 1 f from rfl] at this

/-- The per-mode **divergence** Duhamel operator as a CLM `CT T →L[ℂ] CT T`, the
linear map `duhCMLM` made continuous with the per-mode `C₀√T` bound. -/
noncomputable def duhDivModeCLM (n : ℤ) (hT : 0 ≤ T) : CT T →L[ℂ] CT T :=
  (duhCMLM hT (((n : ℝ) * Real.pi) ^ 2) (Complex.I * ((n : ℝ) * Real.pi))).mkContinuous
    (C₀ * Real.sqrt T)
    (fun f => by
      rw [duhCMLM_apply]
      have := duhDivMode_norm_le n f hT
      rwa [show duhDivMode n f hT
        = duhCM hT (((n : ℝ) * Real.pi) ^ 2) (Complex.I * ((n : ℝ) * Real.pi)) f
        from rfl] at this)

@[simp] theorem duhDivModeCLM_apply (n : ℤ) (hT : 0 ≤ T) (f : CT T) :
    duhDivModeCLM n hT f
      = duhCM hT (((n : ℝ) * Real.pi) ^ 2) (Complex.I * ((n : ℝ) * Real.pi)) f := rfl

/-- The per-mode divergence CLM bound `‖duhDivModeCLM n f‖ ≤ C₀√T·‖f‖`. -/
theorem duhDivModeCLM_norm_le (n : ℤ) (hT : 0 ≤ T) (f : CT T) :
    ‖duhDivModeCLM n hT f‖ ≤ (C₀ * Real.sqrt T) * ‖f‖ := by
  rw [duhDivModeCLM_apply]
  have := duhDivMode_norm_le n f hT
  rwa [show duhDivMode n f hT
    = duhCM hT (((n : ℝ) * Real.pi) ^ 2) (Complex.I * ((n : ℝ) * Real.pi)) f
    from rfl] at this

end Operators

/-! ### The EWA-level Duhamel operators via `GWA.coeffwiseCLM`. -/

section EWAAssembly

variable {T : ℝ} {r : ℕ}

/-- The per-mode weight bound for the value operator (the `coeffwiseCLM` premise
`hOp`), from `duhValModeCLM_norm_le`. -/
theorem valDuhamel_hOp (hT : 0 ≤ T) (n : ℤ) (f : CT T) :
    GWA.gWeight r n * ‖duhValModeCLM n hT f‖ ≤ T * (GWA.gWeight r n * ‖f‖) := by
  have hw : (0 : ℝ) ≤ GWA.gWeight r n := GWA.gWeight_nonneg r n
  calc GWA.gWeight r n * ‖duhValModeCLM n hT f‖
      ≤ GWA.gWeight r n * (T * ‖f‖) :=
        mul_le_mul_of_nonneg_left (duhValModeCLM_norm_le n hT f) hw
    _ = T * (GWA.gWeight r n * ‖f‖) := by ring

/-- The per-mode weight bound for the divergence operator, from
`duhDivModeCLM_norm_le`. -/
theorem divDuhamel_hOp (hT : 0 ≤ T) (n : ℤ) (f : CT T) :
    GWA.gWeight r n * ‖duhDivModeCLM n hT f‖
      ≤ (C₀ * Real.sqrt T) * (GWA.gWeight r n * ‖f‖) := by
  have hw : (0 : ℝ) ≤ GWA.gWeight r n := GWA.gWeight_nonneg r n
  calc GWA.gWeight r n * ‖duhDivModeCLM n hT f‖
      ≤ GWA.gWeight r n * ((C₀ * Real.sqrt T) * ‖f‖) :=
        mul_le_mul_of_nonneg_left (duhDivModeCLM_norm_le n hT f) hw
    _ = (C₀ * Real.sqrt T) * (GWA.gWeight r n * ‖f‖) := by ring

/-- **The value Duhamel operator on `EWA T r`**, the `r → r` CLM assembled from
the per-mode `duhValModeCLM` via the master `GWA.coeffwiseCLM`, with overall
constant `T`. -/
noncomputable def valDuhamelEWA (hT : 0 ≤ T) : EWA T r →L[ℂ] EWA T r :=
  GWA.coeffwiseCLM (fun n => duhValModeCLM n hT) T hT (valDuhamel_hOp hT)

/-- **The divergence Duhamel operator on `EWA T r`** (the √T contraction), the
`r → r` CLM assembled from `duhDivModeCLM` via `GWA.coeffwiseCLM`, with overall
constant `C₀√T`. -/
noncomputable def divDuhamelEWA (hT : 0 ≤ T) : EWA T r →L[ℂ] EWA T r :=
  GWA.coeffwiseCLM (fun n => duhDivModeCLM n hT) (C₀ * Real.sqrt T)
    (by have := C₀_nonneg; positivity) (divDuhamel_hOp hT)

/-- **The value EWA bound** `‖valDuhamelEWA F‖ ≤ T·‖F‖` (the operator-norm bound
inherited from `coeffwiseCLM`'s `norm_coeffwiseLM_le`). -/
theorem valDuhamelEWA_bound (hT : 0 ≤ T) (F : EWA T r) :
    ‖valDuhamelEWA hT F‖ ≤ T * ‖F‖ :=
  GWA.norm_coeffwiseLM_le (fun n => duhValModeCLM n hT) T hT (valDuhamel_hOp hT) F

/-- **The divergence EWA bound** `‖divDuhamelEWA B‖ ≤ C₀√T·‖B‖` — the √T
contraction at the EWA level (the operator-norm bound from `coeffwiseCLM`). -/
theorem divDuhamelEWA_bound (hT : 0 ≤ T) (B : EWA T r) :
    ‖divDuhamelEWA hT B‖ ≤ (C₀ * Real.sqrt T) * ‖B‖ :=
  GWA.norm_coeffwiseLM_le (fun n => duhDivModeCLM n hT) (C₀ * Real.sqrt T)
    (by have := C₀_nonneg; positivity) (divDuhamel_hOp hT) B

end EWAAssembly

end ShenWork.EWA
