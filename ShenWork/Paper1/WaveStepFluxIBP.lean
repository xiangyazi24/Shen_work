/-
  ShenWork/Paper1/WaveStepFluxIBP.lean

  The CROSS-FROZEN flux-difference integration-by-parts brick discharging the
  last carried obligation of the B1 Rothe trapping.

  GOAL (`stepFlux_diff_ibp`):
      `−χ · ∫ y, Kλ'(x−y)·(stepFlux p u B y − stepFlux p u W y) dy
         = greenConv c λ (fun y ↦ −χ·deriv (fun z ↦ stepFlux p u B z − stepFlux p u W z) y) x`.

  This is the flux-difference analogue of the committed `flux_ibp`
  (WaveFluxIBP.lean:74), needed because the implicit Rothe step uses the
  CROSS-frozen flux `stepFlux p u W = W^m · (frozenElliptic p u)'` (W in the
  power base, u in the elliptic) rather than the single-profile
  `auxFlux p u = u^m · (frozenElliptic p u)'`.

  ROUTE.  The proof of `flux_ibp` never uses any property of `auxFlux` beyond
  it being `C¹` (with the named decay / per-tail integrability data); the kernel
  kink cancels by `greenKernel_continuous` regardless of the flux.  So we first
  abstract `flux_ibp` to an ARBITRARY `C¹` flux `G : ℝ → ℝ` and an arbitrary
  scalar coefficient `κ` (`= −χ`) — `flux_ibp_generic` — by the IDENTICAL
  argument (two half-line improper IBPs, kink cancellation, ±∞ decay). Then
  `flux_ibp` is the `G = auxFlux p u`, `κ = −χ` instance, and `stepFlux_diff_ibp`
  is the `G = stepFlux p u B − stepFlux p u W`, `κ = −χ` instance.
-/
import ShenWork.Paper1.WaveFluxIBP
import ShenWork.Paper1.WaveRotheOrder

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## The generic flux integration by parts

`flux_ibp` proved verbatim for an abstract `C¹` flux `G : ℝ → ℝ` and an abstract
scalar coefficient `κ : ℝ`.  Nothing in the route used `auxFlux`'s definition —
only that it is `C¹` with convergent tails and that the kernel is `C⁰` at its
kink.  We therefore record the generic statement once and instantiate it twice
(the single-profile `flux_ibp` and the cross-frozen difference). -/

/-- **Generic flux integration by parts.**  For any `C¹` flux `G` (with the
minimal per-tail integrability and `±∞` decay data) and any scalar `κ`,

    `κ · ∫ y, Kλ'(x−y)·G y  =  greenConv c λ (κ·G') x`.

The proof is the verbatim transcription of `flux_ibp` (WaveFluxIBP.lean:74) with
`auxFlux p u ↦ G`, `deriv (auxFlux p u) ↦ deriv G`, `−p.χ ↦ κ`. -/
theorem flux_ibp_generic (c lam : ℝ) (hlam : 0 < lam) (κ : ℝ) (G : ℝ → ℝ) (x : ℝ)
    (hG_C1 : ∀ y, HasDerivAt G (deriv G y) y)
    (hKv'_Ioi : IntegrableOn
      ((fun y => greenKernel c lam (x - y)) * deriv G) (Ioi x))
    (hKv'_Iic : IntegrableOn
      ((fun y => greenKernel c lam (x - y)) * deriv G) (Iic x))
    (hK'v_Ioi : IntegrableOn
      ((fun y => -greenKernelDeriv c lam (x - y)) * G) (Ioi x))
    (hK'v_Iic : IntegrableOn
      ((fun y => -greenKernelDeriv c lam (x - y)) * G) (Iic x))
    (hKG_Iic : IntegrableOn
      (fun y => greenKernel c lam (x - y) * (κ * deriv G y)) (Iic x))
    (hKG_Ioi : IntegrableOn
      (fun y => greenKernel c lam (x - y) * (κ * deriv G y)) (Ioi x))
    (hdecay_top : Tendsto ((fun y => greenKernel c lam (x - y)) * G)
      atTop (𝓝 0))
    (hdecay_bot : Tendsto ((fun y => greenKernel c lam (x - y)) * G)
      atBot (𝓝 0)) :
    κ * ∫ y, greenKernelDeriv c lam (x - y) * G y
      = greenConv c lam (fun y => κ * deriv G y) x := by
  set g : ℝ → ℝ := fun y => greenKernel c lam (x - y) with hg
  set f : ℝ → ℝ := G with hf
  set f' : ℝ → ℝ := deriv G with hf'
  -- continuity of g and f
  have hg_cont : Continuous g := greenKernel_comp_const_sub_continuous x
  have hf_cont : Continuous f := by
    refine continuous_iff_continuousAt.mpr (fun y => (hG_C1 y).continuousAt)
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
  -- ===== IBP on  Ioi x  =====
  have hIoi := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := g) (v := f) (u' := fun y => -greenKernelDeriv c lam (x - y)) (v' := f')
    (a := x) (a' := bdy) (b' := 0)
    hg_Ioi (fun y _ => hG_C1 y) hKv'_Ioi hK'v_Ioi hkink_gt hdecay_top
  -- ===== IBP on  Iic x  =====
  have hIic := integral_Iic_mul_deriv_eq_deriv_mul
    (u := g) (v := f) (u' := fun y => -greenKernelDeriv c lam (x - y)) (v' := f')
    (a := x) (a' := bdy) (b' := 0)
    hg_Iio (fun y _ => hG_C1 y) hKv'_Iic hK'v_Iic hkink_lt hdecay_bot
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
  -- finish:  κ · ∫ K'·f = κ · ∫ K·f' = ∫ K·(κ·f') = greenConv(κ·f')
  rw [hcore]
  have hconv := kernelConv_eq_greenConv (c := c) (lam := lam)
    (fun y => κ * f' y) x hKG_Iic hKG_Ioi
  rw [← hconv]
  rw [show (κ * ∫ y, g y * f' y) = ∫ y, greenKernel c lam (x - y) * (κ * f' y) by
    rw [← MeasureTheory.integral_const_mul]
    congr 1; funext y; simp only [hg]; ring]

/-! ## `flux_ibp` recovered as the single-profile instance -/

/-- The committed `flux_ibp` is the `G = auxFlux p u`, `κ = −χ` instance of
`flux_ibp_generic`.  (Sanity check that the generalization is faithful.) -/
theorem flux_ibp_of_generic (c lam : ℝ) (hlam : 0 < lam) (p : CMParams)
    (u : ℝ → ℝ) (x : ℝ)
    (hflux_C1 : ∀ y, HasDerivAt (auxFlux p u) (deriv (auxFlux p u) y) y)
    (hKv'_Ioi : IntegrableOn
      ((fun y => greenKernel c lam (x - y)) * deriv (auxFlux p u)) (Ioi x))
    (hKv'_Iic : IntegrableOn
      ((fun y => greenKernel c lam (x - y)) * deriv (auxFlux p u)) (Iic x))
    (hK'v_Ioi : IntegrableOn
      ((fun y => -greenKernelDeriv c lam (x - y)) * auxFlux p u) (Ioi x))
    (hK'v_Iic : IntegrableOn
      ((fun y => -greenKernelDeriv c lam (x - y)) * auxFlux p u) (Iic x))
    (hKG_Iic : IntegrableOn
      (fun y => greenKernel c lam (x - y) * (-p.χ * deriv (auxFlux p u) y)) (Iic x))
    (hKG_Ioi : IntegrableOn
      (fun y => greenKernel c lam (x - y) * (-p.χ * deriv (auxFlux p u) y)) (Ioi x))
    (hdecay_top : Tendsto ((fun y => greenKernel c lam (x - y)) * auxFlux p u)
      atTop (𝓝 0))
    (hdecay_bot : Tendsto ((fun y => greenKernel c lam (x - y)) * auxFlux p u)
      atBot (𝓝 0)) :
    -p.χ * ∫ y, greenKernelDeriv c lam (x - y) * auxFlux p u y
      = greenConv c lam (fun y => -p.χ * deriv (auxFlux p u) y) x :=
  flux_ibp_generic c lam hlam (-p.χ) (auxFlux p u) x hflux_C1
    hKv'_Ioi hKv'_Iic hK'v_Ioi hK'v_Iic hKG_Iic hKG_Ioi hdecay_top hdecay_bot

/-! ## The cross-frozen flux-difference IBP

`stepFlux_diff_ibp` is the `flux_ibp_generic` instance with
`G = fun y ↦ stepFlux p u B y − stepFlux p u W y`, `κ = −χ`.

`G` is `C¹` because `B`, `W` are `C¹` step solutions and the frozen elliptic
profile `frozenElliptic p u` is smooth, so each `stepFlux p u · = ·^m · V'` is
`C¹`; we carry that `C¹`-ness as the named hypothesis `hG_C1` (a `HasDerivAt`
for the difference, which is exactly the `C¹` of the two step fluxes —
satisfiable, not the conclusion).  The decay / per-tail integrability data are
the same `flux_ibp` requires, now for the difference flux. -/

/-- The cross-frozen flux DIFFERENCE `y ↦ stepFlux p u B y − stepFlux p u W y`. -/
def stepFluxDiff (p : CMParams) (u W B : ℝ → ℝ) (y : ℝ) : ℝ :=
  stepFlux p u B y - stepFlux p u W y

/-- **Cross-frozen flux-difference integration by parts.**  The
flux-difference analogue of `flux_ibp` for the implicit Rothe step:

    `−χ · ∫ y, Kλ'(x−y)·(stepFlux p u B y − stepFlux p u W y) dy
       = greenConv c λ (fun y ↦ −χ · deriv (stepFluxDiff p u W B) y) x`.

This is the `flux_ibp_generic` instance with `G = stepFluxDiff p u W B`,
`κ = −p.χ`.  It moves the derivative off the flux DIFFERENCE at the level of the
whole Green map (NO pointwise `W'` survives), which is exactly what is needed to
discharge `RotheChemoMonotoneResidual` in integrated form against
`greenConv_mono`. -/
theorem stepFlux_diff_ibp (c lam : ℝ) (hlam : 0 < lam) (p : CMParams)
    (u W B : ℝ → ℝ) (x : ℝ)
    (hG_C1 : ∀ y, HasDerivAt (stepFluxDiff p u W B) (deriv (stepFluxDiff p u W B) y) y)
    (hKv'_Ioi : IntegrableOn
      ((fun y => greenKernel c lam (x - y)) * deriv (stepFluxDiff p u W B)) (Ioi x))
    (hKv'_Iic : IntegrableOn
      ((fun y => greenKernel c lam (x - y)) * deriv (stepFluxDiff p u W B)) (Iic x))
    (hK'v_Ioi : IntegrableOn
      ((fun y => -greenKernelDeriv c lam (x - y)) * stepFluxDiff p u W B) (Ioi x))
    (hK'v_Iic : IntegrableOn
      ((fun y => -greenKernelDeriv c lam (x - y)) * stepFluxDiff p u W B) (Iic x))
    (hKG_Iic : IntegrableOn
      (fun y => greenKernel c lam (x - y) * (-p.χ * deriv (stepFluxDiff p u W B) y)) (Iic x))
    (hKG_Ioi : IntegrableOn
      (fun y => greenKernel c lam (x - y) * (-p.χ * deriv (stepFluxDiff p u W B) y)) (Ioi x))
    (hdecay_top : Tendsto ((fun y => greenKernel c lam (x - y)) * stepFluxDiff p u W B)
      atTop (𝓝 0))
    (hdecay_bot : Tendsto ((fun y => greenKernel c lam (x - y)) * stepFluxDiff p u W B)
      atBot (𝓝 0)) :
    -p.χ * ∫ y, greenKernelDeriv c lam (x - y) * (stepFlux p u B y - stepFlux p u W y)
      = greenConv c lam (fun y => -p.χ * deriv (stepFluxDiff p u W B) y) x := by
  have h := flux_ibp_generic c lam hlam (-p.χ) (stepFluxDiff p u W B) x hG_C1
    hKv'_Ioi hKv'_Iic hK'v_Ioi hK'v_Iic hKG_Iic hKG_Ioi hdecay_top hdecay_bot
  -- rewrite the integrand `stepFluxDiff` to its expanded difference form
  simpa only [stepFluxDiff] using h

/-! ## Axiom audit -/

section AxiomAudit

#print axioms flux_ibp_generic
#print axioms flux_ibp_of_generic
#print axioms stepFlux_diff_ibp

end AxiomAudit

end ShenWork.Paper1
