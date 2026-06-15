/-
  ShenWork/Paper1/WaveFluxIBP.lean

  The flux integration-by-parts brick discharging the `hIBP` hypothesis of
  `auxMap_eq_negGreenConv`.

  GOAL (`flux_ibp`):
      `−χ · ∫ y, Kλ'(x−y)·flux(y) dy = greenConv c λ (−χ·flux') x`.

  ROUTE.  Write `g(y) = Kλ(x−y)`.  The chain rule gives, for `y ≠ x`,
      `g'(y) = −Kλ'(x−y) = −greenKernelDeriv c λ (x−y)`.
  Integrate by parts on `Iic x` and `Ioi x` SEPARATELY (avoiding the kernel
  kink at `y = x`), using the improper half-line parts lemmas
  `MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul` and its `Iic`
  counterpart.  The interior boundary terms are both `Kλ(0)·flux(x)` and
  cancel (the kernel is `C⁰` at the kink); the `±∞` boundary terms vanish by
  decay (`hdecay`).  Combining the two half-lines gives the core identity
      `∫ y, Kλ'(x−y)·flux(y) = ∫ y, Kλ(x−y)·flux'(y)`,
  and `kernelConv_eq_greenConv` then turns `∫ Kλ(x−y)·(−χ·flux')` into
  `greenConv c λ (−χ·flux')`.
-/
import ShenWork.Paper1.WaveConvRepr
import ShenWork.Paper1.WaveAuxMap

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## Continuity of the Green kernel (the `C⁰` kink) -/

/-- The Green kernel is continuous on all of `ℝ` (the two exponential branches
agree at the kink `z = 0`, common value `1/δ`). -/
theorem greenKernel_continuous : Continuous (greenKernel c lam) := by
  unfold greenKernel
  refine Continuous.if_le (g := fun _ : ℝ => (0 : ℝ)) ?_ ?_ continuous_id continuous_const ?_
  · exact continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))
  · exact continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))
  · intro a ha
    simp only [ha, mul_zero, Real.exp_zero, mul_one]

/-- `y ↦ Kλ(x−y)` is continuous. -/
theorem greenKernel_comp_const_sub_continuous (x : ℝ) :
    Continuous (fun y => greenKernel c lam (x - y)) :=
  greenKernel_continuous.comp (continuous_const.sub continuous_id)

/-! ## The chain-rule derivative of `y ↦ Kλ(x−y)` -/

/-- For `y ≠ x`, `d/dy [Kλ(x−y)] = −Kλ'(x−y)`. -/
theorem greenKernel_comp_hasDerivAt (hlam : 0 < lam) (x : ℝ) {y : ℝ} (hy : y ≠ x) :
    HasDerivAt (fun y => greenKernel c lam (x - y))
      (-greenKernelDeriv c lam (x - y)) y := by
  have hxy : x - y ≠ 0 := sub_ne_zero.mpr (fun h => hy h.symm)
  have hd : HasDerivAt (greenKernel c lam) (greenKernelDeriv c lam (x - y)) (x - y) :=
    greenKernel_hasDerivAt hlam hxy
  exact hd.comp_const_sub x y

/-! ## The flux integration by parts -/

/-- **Flux integration by parts.**  The `χ·Kλ'∗flux` term equals
`greenConv c λ (−χ·flux')`, matching the `hIBP` hypothesis of
`auxMap_eq_negGreenConv` verbatim.

`hflux_C1` is the `C¹` hypothesis (flux differentiable with derivative
`deriv (auxFlux p u)`).  The remaining hypotheses are the MINIMAL decay /
integrability data: the two per-tail integrabilities of `Kλ(x−·)·flux'` and
`Kλ'(x−·)·flux`, the per-tail integrability of `Kλ(x−·)·(−χ·flux')` feeding
`kernelConv_eq_greenConv`, and the four boundary-decay limits at `±∞`. -/
theorem flux_ibp (c lam : ℝ) (hlam : 0 < lam) (p : CMParams) (u : ℝ → ℝ) (x : ℝ)
    (hflux_C1 : ∀ y, HasDerivAt (auxFlux p u) (deriv (auxFlux p u) y) y)
    -- per-tail integrability of  Kλ(x−·)·flux'
    (hKv'_Ioi : IntegrableOn
      ((fun y => greenKernel c lam (x - y)) * deriv (auxFlux p u)) (Ioi x))
    (hKv'_Iic : IntegrableOn
      ((fun y => greenKernel c lam (x - y)) * deriv (auxFlux p u)) (Iic x))
    -- per-tail integrability of  (−Kλ'(x−·))·flux
    (hK'v_Ioi : IntegrableOn
      ((fun y => -greenKernelDeriv c lam (x - y)) * auxFlux p u) (Ioi x))
    (hK'v_Iic : IntegrableOn
      ((fun y => -greenKernelDeriv c lam (x - y)) * auxFlux p u) (Iic x))
    -- per-tail integrability of the assembled smooth source  Kλ(x−·)·(−χ·flux')
    (hKG_Iic : IntegrableOn
      (fun y => greenKernel c lam (x - y) * (-p.χ * deriv (auxFlux p u) y)) (Iic x))
    (hKG_Ioi : IntegrableOn
      (fun y => greenKernel c lam (x - y) * (-p.χ * deriv (auxFlux p u) y)) (Ioi x))
    -- boundary decay at  ±∞  (the product Kλ(x−·)·flux → 0)
    (hdecay_top : Tendsto ((fun y => greenKernel c lam (x - y)) * auxFlux p u)
      atTop (𝓝 0))
    (hdecay_bot : Tendsto ((fun y => greenKernel c lam (x - y)) * auxFlux p u)
      atBot (𝓝 0)) :
    -p.χ * ∫ y, greenKernelDeriv c lam (x - y) * auxFlux p u y
      = greenConv c lam (fun y => -p.χ * deriv (auxFlux p u) y) x := by
  set g : ℝ → ℝ := fun y => greenKernel c lam (x - y) with hg
  set f : ℝ → ℝ := auxFlux p u with hf
  set f' : ℝ → ℝ := deriv (auxFlux p u) with hf'
  -- continuity of g and f
  have hg_cont : Continuous g := greenKernel_comp_const_sub_continuous x
  have hf_cont : Continuous f := by
    refine continuous_iff_continuousAt.mpr (fun y => (hflux_C1 y).continuousAt)
  -- the common kink boundary value  K(0)·f(x)
  set bdy : ℝ := greenKernel c lam 0 * f x with hbdy
  -- tendsto of g·f at the kink from each side
  have hkink_at : Tendsto (g * f) (𝓝 x) (𝓝 bdy) := by
    have : Continuous (g * f) := hg_cont.mul hf_cont
    have h0 : (g * f) x = bdy := by
      simp only [Pi.mul_apply, hg, hbdy, sub_self]
    simpa [h0] using this.tendsto x
  have hkink_gt : Tendsto (g * f) (𝓝[>] x) (𝓝 bdy) :=
    hkink_at.mono_left nhdsWithin_le_nhds
  have hkink_lt : Tendsto (g * f) (𝓝[<] x) (𝓝 bdy) :=
    hkink_at.mono_left nhdsWithin_le_nhds
  -- derivatives of g on each open half-line
  have hg_Ioi : ∀ y ∈ Ioi x, HasDerivAt g (-greenKernelDeriv c lam (x - y)) y := by
    intro y hy; exact greenKernel_comp_hasDerivAt hlam x (ne_of_gt hy)
  have hg_Iio : ∀ y ∈ Iio x, HasDerivAt g (-greenKernelDeriv c lam (x - y)) y := by
    intro y hy; exact greenKernel_comp_hasDerivAt hlam x (ne_of_lt hy)
  have hf_all : ∀ y ∈ (Ioi x ∪ Iio x), HasDerivAt f (f' y) y :=
    fun y _ => hflux_C1 y
  -- ===== IBP on  Ioi x  =====
  -- ∫_Ioi g·f' = b' − a' − ∫_Ioi g'·f , with a' = bdy, b' = 0
  have hIoi := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := g) (v := f) (u' := fun y => -greenKernelDeriv c lam (x - y)) (v' := f')
    (a := x) (a' := bdy) (b' := 0)
    hg_Ioi (fun y hy => hflux_C1 y) hKv'_Ioi hK'v_Ioi hkink_gt hdecay_top
  -- ===== IBP on  Iic x  =====
  have hIic := integral_Iic_mul_deriv_eq_deriv_mul
    (u := g) (v := f) (u' := fun y => -greenKernelDeriv c lam (x - y)) (v' := f')
    (a := x) (a' := bdy) (b' := 0)
    hg_Iio (fun y hy => hflux_C1 y) hKv'_Iic hK'v_Iic hkink_lt hdecay_bot
  -- rewrite both into  ∫ greenKernelDeriv·f = ±bdy + ∫ g·f'
  -- Ioi : ∫_Ioi g·f' = 0 − bdy − ∫_Ioi (−K')·f
  --   ⇒ ∫_Ioi K'·f = bdy + ∫_Ioi g·f'
  have eq_Ioi : (∫ y in Ioi x, greenKernelDeriv c lam (x - y) * f y)
      = bdy + ∫ y in Ioi x, g y * f' y := by
    have hneg : (∫ y in Ioi x, -greenKernelDeriv c lam (x - y) * f y)
        = -∫ y in Ioi x, greenKernelDeriv c lam (x - y) * f y := by
      rw [← integral_neg]; congr 1; funext y; ring
    rw [hneg] at hIoi
    linarith [hIoi]
  have eq_Iic : (∫ y in Iic x, greenKernelDeriv c lam (x - y) * f y)
      = -bdy + ∫ y in Iic x, g y * f' y := by
    have hneg : (∫ y in Iic x, -greenKernelDeriv c lam (x - y) * f y)
        = -∫ y in Iic x, greenKernelDeriv c lam (x - y) * f y := by
      rw [← integral_neg]; congr 1; funext y; ring
    rw [hneg] at hIic
    linarith [hIic]
  -- whole-line integrabilities of greenKernelDeriv·f  (from the (−K')·f tails)
  have hK'f_Ioi : IntegrableOn (fun y => greenKernelDeriv c lam (x - y) * f y) (Ioi x) := by
    have h := hK'v_Ioi.neg
    refine h.congr_fun ?_ measurableSet_Ioi
    intro y _; simp only [Pi.neg_apply, Pi.mul_apply, neg_mul, neg_neg]
  have hK'f_Iic : IntegrableOn (fun y => greenKernelDeriv c lam (x - y) * f y) (Iic x) := by
    have h := hK'v_Iic.neg
    refine h.congr_fun ?_ measurableSet_Iic
    intro y _; simp only [Pi.neg_apply, Pi.mul_apply, neg_mul, neg_neg]
  -- whole-line integrabilities of g·f'
  have hgf'_Ioi : IntegrableOn (fun y => g y * f' y) (Ioi x) := by
    have := hKv'_Ioi; simpa [Pi.mul_apply] using this
  have hgf'_Iic : IntegrableOn (fun y => g y * f' y) (Iic x) := by
    have := hKv'_Iic; simpa [Pi.mul_apply] using this
  -- assemble the whole-line integral of greenKernelDeriv·f
  have hsplit_K'f : (∫ y, greenKernelDeriv c lam (x - y) * f y)
      = (∫ y in Iic x, greenKernelDeriv c lam (x - y) * f y)
        + ∫ y in Ioi x, greenKernelDeriv c lam (x - y) * f y := by
    have hfull : Integrable (fun y => greenKernelDeriv c lam (x - y) * f y) := by
      rw [← integrableOn_univ,
        show (univ : Set ℝ) = Iic x ∪ Ioi x by
          ext y; simp only [mem_univ, mem_union, mem_Iic, mem_Ioi, true_iff]
          exact le_or_gt y x]
      exact hK'f_Iic.union hK'f_Ioi
    have := MeasureTheory.integral_add_compl (s := Iic x) measurableSet_Iic hfull
    simpa [Set.compl_Iic] using this.symm
  -- assemble the whole-line integral of g·f'
  have hsplit_gf' : (∫ y, g y * f' y)
      = (∫ y in Iic x, g y * f' y) + ∫ y in Ioi x, g y * f' y := by
    have hfull : Integrable (fun y => g y * f' y) := by
      rw [← integrableOn_univ,
        show (univ : Set ℝ) = Iic x ∪ Ioi x by
          ext y; simp only [mem_univ, mem_union, mem_Iic, mem_Ioi, true_iff]
          exact le_or_gt y x]
      exact hgf'_Iic.union hgf'_Ioi
    have := MeasureTheory.integral_add_compl (s := Iic x) measurableSet_Iic hfull
    simpa [Set.compl_Iic] using this.symm
  -- the CORE identity:  ∫ K'(x−·)·f = ∫ K(x−·)·f'
  have hcore : (∫ y, greenKernelDeriv c lam (x - y) * f y)
      = ∫ y, g y * f' y := by
    rw [hsplit_K'f, hsplit_gf', eq_Iic, eq_Ioi]; ring
  -- finish:  −χ · ∫ K'·f = −χ · ∫ K·f' = ∫ K·(−χ·f') = greenConv(−χ·f')
  rw [hcore]
  have hconv := kernelConv_eq_greenConv (c := c) (lam := lam)
    (fun y => -p.χ * f' y) x hKG_Iic hKG_Ioi
  rw [← hconv]
  rw [show (-p.χ * ∫ y, g y * f' y) = ∫ y, greenKernel c lam (x - y) * (-p.χ * f' y) by
    rw [← MeasureTheory.integral_const_mul]
    congr 1; funext y; simp only [hg]; ring]

end ShenWork.Paper1
