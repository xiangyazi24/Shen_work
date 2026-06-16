/-
  ShenWork/Paper1/WaveRotheStationary.lean

  Rothe-limit stationary-equation brick for the B1 traveling-wave assembly
  (Shen, arXiv:2605.04401, §6 / B1 doctrine).

  This file is the analytic heart of passing the implicit-Euler (Rothe) orbit to
  its limit and recovering the STATIONARY profile equation.  The route is the
  ChatGPT-Pro design: we pass the *integral* fixed-point equation
  `z_{k+1} = Φ_{λ,u,z_k}(z_{k+1})` (`crossImplicitMap`) to the `k → ∞` limit,
  NOT the differential operator.  Concretely:

    * `z_{k+1}(x) → U(x)` pointwise (loc-unif convergence `hLU`).
    * Each Green integral
        `∫ Kλ(x−y)·(reaction(z·)+λ z·)` ,  `∫ Kλ'(x−y)·(z·)^m·V_u'`
      converges to its `U`-version by DOMINATED CONVERGENCE: the integrand
      converges pointwise (loc-unif + continuity of `s↦s(1−s^a)`, `s↦s^m` on the
      trapped range `[0,M]`) and is dominated by `|Kλ(x−y)|·C` / `|Kλ'(x−y)|·C`,
      both `L¹` (committed `greenKernel_l1_eq` / `greenKernelDeriv_l1_eq`,
      translation-invariant via `Measure.measurePreserving_sub_left`).

  Hence `crossImplicitMap p c lam u U U = U`.  At the OUTER Schauder fixed point
  (`u = U`), `crossImplicitMap_self_eq_auxMap` collapses this to `auxMap p c lam U
  = U`, and the committed `fixedPoint_stationary` (modulo the per-`U` Green
  identity) yields `∀ x, frozenWaveOperator p c U U x = 0` — the B1 headline
  stationarity.

  HYPOTHESES are carried explicitly and are all SATISFIABLE (the equicontinuity /
  standard-regularity pieces proved elsewhere):
    * `hLU : LocallyUniformConverges z U`           (equicontinuity output),
    * trap bounds `0 ≤ z k y ≤ M`, `0 ≤ U y ≤ M`,
    * continuity of each `z k`, of `U`, of `V_u' = deriv (frozenElliptic p u)`,
    * a sup bound `|V_u'| ≤ Bv`.
-/
import ShenWork.Paper1.WaveRotheStep
import ShenWork.Paper1.WaveRotheLimit
import ShenWork.Paper1.WaveFluxIBP
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## Measurability of the kernel pieces -/

/-- The kernel derivative `Kλ'` is measurable (a step function with two
continuous exponential branches; it jumps at the kink `z = 0`). -/
theorem greenKernelDeriv_measurable : Measurable (greenKernelDeriv c lam) := by
  unfold greenKernelDeriv
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) ?_ ?_
  · exact (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).measurable
  · exact (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).measurable

/-- `y ↦ Kλ'(x−y)` is measurable. -/
theorem greenKernelDeriv_comp_const_sub_measurable (x : ℝ) :
    Measurable (fun y => greenKernelDeriv c lam (x - y)) :=
  greenKernelDeriv_measurable.comp (measurable_const.sub measurable_id)

/-! ## Translation-invariant `L¹` domination

`fun y => |Kλ(x−y)|·C` and `fun y => |Kλ'(x−y)|·C` are integrable, by the
committed `L¹` facts on the kernels composed with the measure-preserving
reflection `y ↦ x − y`. -/

/-- `y ↦ x − y` is measure preserving on `(ℝ, volume)`. -/
theorem measurePreserving_const_sub (x : ℝ) :
    MeasurePreserving (fun y : ℝ => x - y) (volume : Measure ℝ) volume :=
  Measure.measurePreserving_sub_left volume x

theorem integrable_abs_greenKernel_comp_const_sub_mul
    (hlam : 0 < lam) (x C : ℝ) :
    Integrable (fun y => |greenKernel c lam (x - y)| * C) := by
  have hbase : Integrable (fun z => |greenKernel c lam z| * C) := by
    have hKi : Integrable (fun z => |greenKernel c lam z|) := by
      have := (greenKernel_integrable (c := c) hlam).abs
      simpa using this
    exact hKi.mul_const C
  have := (measurePreserving_const_sub x).integrable_comp_of_integrable hbase
  simpa [Function.comp] using this

theorem integrable_abs_greenKernelDeriv_comp_const_sub_mul
    (hlam : 0 < lam) (x C : ℝ) :
    Integrable (fun y => |greenKernelDeriv c lam (x - y)| * C) := by
  have hKi : Integrable (fun z => |greenKernelDeriv c lam z|) :=
    greenKernelDeriv_integrable (c := c) hlam
  have hbase : Integrable (fun z => |greenKernelDeriv c lam z| * C) := hKi.mul_const C
  have := (measurePreserving_const_sub x).integrable_comp_of_integrable hbase
  simpa [Function.comp] using this

/-! ## Continuity of the scalar nonlinearities

`reactionFun a s = s·(1 − s^a)` and `s ↦ s^m` are continuous on `ℝ` for the
admissible exponents (`a ≥ 1`, `m ≥ 1`, so `0 ≤ a`, `0 ≤ m`), hence they push
pointwise convergence of the iterates through. -/

theorem continuous_reactionFun {a : ℝ} (ha : 0 ≤ a) :
    Continuous (reactionFun a) := by
  unfold reactionFun
  exact continuous_id.mul (continuous_const.sub
    (Real.continuous_rpow_const ha))

theorem continuous_rpow_const_exp {m : ℝ} (hm : 0 ≤ m) :
    Continuous (fun s : ℝ => s ^ m) :=
  Real.continuous_rpow_const hm

/-! ## Dominated-convergence limit of the two Green integrals

We carry the Rothe data as explicit hypotheses (see header).  `seqR`/`seqF` are
the two integrand families; their `x`-fibre limits are the `U`-integrands.  The
shifted index `z (k+1)` enters the nonlinear reaction/flux and `z k` enters the
linear `λZ` shift — both converge to `U`. -/

section DomConv

variable {p : CMParams} {u : ℝ → ℝ} {z : ℕ → ℝ → ℝ} {U : ℝ → ℝ} {M Bv : ℝ}

/-- **Reaction integral converges (dominated convergence).**
For the Rothe data, the linear-shift Green integral converges:
`∫ Kλ(x−y)·(reaction(z(k+1) y)+λ z k y) → ∫ Kλ(x−y)·(reaction(U y)+λ U y)`. -/
theorem rothe_reactionIntegral_tendsto
    (hlam : 0 < lam) (hM : 0 ≤ M)
    (hLU : LocallyUniformConverges z U)
    (hz_cont : ∀ k, Continuous (z k))
    (hU_cont : Continuous U)
    (hz_lb : ∀ k y, 0 ≤ z k y) (hz_ub : ∀ k y, z k y ≤ M)
    (hU_lb : ∀ y, 0 ≤ U y) (hU_ub : ∀ y, U y ≤ M)
    (x : ℝ) :
    Tendsto (fun k => ∫ y, greenKernel c lam (x - y)
        * (reactionFun p.α (z (k+1) y) + lam * z k y)) atTop
      (𝓝 (∫ y, greenKernel c lam (x - y)
        * (reactionFun p.α (U y) + lam * U y))) := by
  -- Dominating constant: |reaction| ≤ M(1+M^α) on [0,M], |λ·z| ≤ λM.
  set Crxn : ℝ := M * (1 + M ^ p.α) + lam * M with hCrxn
  have hαnn : (0:ℝ) ≤ p.α := le_trans zero_le_one p.hα
  have hcontR : Continuous (reactionFun p.α) := continuous_reactionFun hαnn
  -- bound on |reactionFun α s| for s ∈ [0,M]
  have hreact_bound : ∀ s : ℝ, 0 ≤ s → s ≤ M → |reactionFun p.α s| ≤ M * (1 + M ^ p.α) := by
    intro s hs0 hsM
    have hsa_nonneg : 0 ≤ s ^ p.α := Real.rpow_nonneg hs0 _
    have hsa_le : s ^ p.α ≤ M ^ p.α := Real.rpow_le_rpow hs0 hsM hαnn
    have hMa_nonneg : 0 ≤ M ^ p.α := Real.rpow_nonneg hM _
    unfold reactionFun
    rw [abs_mul]
    have h1 : |s| ≤ M := by rw [abs_of_nonneg hs0]; exact hsM
    have h2 : |1 - s ^ p.α| ≤ 1 + M ^ p.α := by
      rw [abs_le]
      constructor
      · nlinarith [hsa_nonneg, hsa_le, hMa_nonneg]
      · nlinarith [hsa_nonneg, hsa_le, hMa_nonneg]
    exact mul_le_mul h1 h2 (abs_nonneg _) hM
  -- apply DCT
  refine tendsto_integral_of_dominated_convergence
    (bound := fun y => |greenKernel c lam (x - y)| * Crxn) ?_ ?_ ?_ ?_
  · -- measurability of each integrand
    intro k
    exact ((greenKernel_comp_const_sub_continuous (c := c) (lam := lam) x).mul
      (((hcontR.comp (hz_cont (k+1))).add
        (continuous_const.mul (hz_cont k))))).aestronglyMeasurable
  · -- bound integrable
    exact integrable_abs_greenKernel_comp_const_sub_mul hlam x Crxn
  · -- domination
    intro k
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hkern : |greenKernel c lam (x - y)| = |greenKernel c lam (x - y)| := rfl
    have hR : |reactionFun p.α (z (k+1) y)| ≤ M * (1 + M ^ p.α) :=
      hreact_bound _ (hz_lb (k+1) y) (hz_ub (k+1) y)
    have hZ : |lam * z k y| ≤ lam * M := by
      rw [abs_mul, abs_of_pos hlam, abs_of_nonneg (hz_lb k y)]
      exact mul_le_mul_of_nonneg_left (hz_ub k y) hlam.le
    have hsum : |reactionFun p.α (z (k+1) y) + lam * z k y| ≤ Crxn :=
      le_trans (abs_add_le _ _) (by rw [hCrxn]; linarith [hR, hZ])
    exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
  · -- pointwise integrand convergence
    refine Filter.Eventually.of_forall (fun y => ?_)
    have hzy : Tendsto (fun k => z k y) atTop (𝓝 (U y)) := hLU.tendsto_at y
    have hzy1 : Tendsto (fun k => z (k+1) y) atTop (𝓝 (U y)) :=
      hzy.comp (tendsto_add_atTop_nat 1)
    have hreactconv : Tendsto (fun k => reactionFun p.α (z (k+1) y)) atTop
        (𝓝 (reactionFun p.α (U y))) :=
      (hcontR.tendsto (U y)).comp hzy1
    have hshiftconv : Tendsto (fun k => lam * z k y) atTop (𝓝 (lam * U y)) :=
      hzy.const_mul lam
    have hsumconv : Tendsto (fun k => reactionFun p.α (z (k+1) y) + lam * z k y) atTop
        (𝓝 (reactionFun p.α (U y) + lam * U y)) := hreactconv.add hshiftconv
    exact (hsumconv.const_mul (greenKernel c lam (x - y)))

/-- **Flux integral converges (dominated convergence).**
`∫ Kλ'(x−y)·(z(k+1) y)^m·V_u' y → ∫ Kλ'(x−y)·(U y)^m·V_u' y`. -/
theorem rothe_fluxIntegral_tendsto
    (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (hLU : LocallyUniformConverges z U)
    (hz_cont : ∀ k, Continuous (z k))
    (hU_cont : Continuous U)
    (hV_cont : Continuous (deriv (frozenElliptic p u)))
    (hV_bound : ∀ y, |deriv (frozenElliptic p u) y| ≤ Bv)
    (hz_lb : ∀ k y, 0 ≤ z k y) (hz_ub : ∀ k y, z k y ≤ M)
    (hU_lb : ∀ y, 0 ≤ U y) (hU_ub : ∀ y, U y ≤ M)
    (x : ℝ) :
    Tendsto (fun k => ∫ y, greenKernelDeriv c lam (x - y)
        * ((z (k+1) y) ^ p.m * deriv (frozenElliptic p u) y)) atTop
      (𝓝 (∫ y, greenKernelDeriv c lam (x - y)
        * ((U y) ^ p.m * deriv (frozenElliptic p u) y))) := by
  set Cflux : ℝ := M ^ p.m * Bv with hCflux
  have hmnn : (0:ℝ) ≤ p.m := le_trans zero_le_one p.hm
  have hcontM : Continuous (fun s : ℝ => s ^ p.m) := continuous_rpow_const_exp hmnn
  have hMm_nonneg : 0 ≤ M ^ p.m := Real.rpow_nonneg hM _
  refine tendsto_integral_of_dominated_convergence
    (bound := fun y => |greenKernelDeriv c lam (x - y)| * Cflux) ?_ ?_ ?_ ?_
  · -- measurability
    intro k
    refine (greenKernelDeriv_comp_const_sub_measurable (c := c) (lam := lam) x).aestronglyMeasurable.mul ?_
    exact ((hcontM.comp (hz_cont (k+1))).mul hV_cont).aestronglyMeasurable
  · exact integrable_abs_greenKernelDeriv_comp_const_sub_mul hlam x Cflux
  · -- domination
    intro k
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hpm : |(z (k+1) y) ^ p.m| ≤ M ^ p.m := by
      have hznn : 0 ≤ (z (k+1) y) ^ p.m := Real.rpow_nonneg (hz_lb (k+1) y) _
      rw [abs_of_nonneg hznn]
      exact Real.rpow_le_rpow (hz_lb (k+1) y) (hz_ub (k+1) y) hmnn
    have hbody : |(z (k+1) y) ^ p.m * deriv (frozenElliptic p u) y| ≤ Cflux := by
      rw [abs_mul, hCflux]
      exact mul_le_mul hpm (hV_bound y) (abs_nonneg _) hMm_nonneg
    exact mul_le_mul_of_nonneg_left hbody (abs_nonneg _)
  · -- pointwise convergence
    refine Filter.Eventually.of_forall (fun y => ?_)
    have hzy : Tendsto (fun k => z k y) atTop (𝓝 (U y)) := hLU.tendsto_at y
    have hzy1 : Tendsto (fun k => z (k+1) y) atTop (𝓝 (U y)) :=
      hzy.comp (tendsto_add_atTop_nat 1)
    have hpmconv : Tendsto (fun k => (z (k+1) y) ^ p.m) atTop (𝓝 ((U y) ^ p.m)) :=
      (hcontM.tendsto (U y)).comp hzy1
    have hbodyconv : Tendsto
        (fun k => (z (k+1) y) ^ p.m * deriv (frozenElliptic p u) y) atTop
        (𝓝 ((U y) ^ p.m * deriv (frozenElliptic p u) y)) :=
      hpmconv.mul_const _
    exact hbodyconv.const_mul (greenKernelDeriv c lam (x - y))

/-! ## The limit is a fixed point of the cross map -/

/-- **Goal 1 — the Rothe limit is a `crossImplicitMap` fixed point.**
For the Rothe sequence `z` (with the implicit-step relation
`z (k+1) = crossImplicitMap p c lam u (z k) (z (k+1))`) converging loc-uniformly
to `U := rotheLimit z`, the limit satisfies
`crossImplicitMap p c lam u U U = U`.

Route: at each `x`, `z (k+1) x → U x` (loc-unif), while the RHS
`crossImplicitMap p c lam u (z k) (z (k+1)) x` converges to
`crossImplicitMap p c lam u U U x` by dominated convergence on the two Green
integrals; uniqueness of limits closes it. -/
theorem rotheLimit_crossImplicitMap_fixed
    (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (hU_def : U = rotheLimit z)
    (hrec : ∀ k, z (k+1) = crossImplicitMap p c lam u (z k) (z (k+1)))
    (hLU : LocallyUniformConverges z U)
    (hz_cont : ∀ k, Continuous (z k))
    (hU_cont : Continuous U)
    (hV_cont : Continuous (deriv (frozenElliptic p u)))
    (hV_bound : ∀ y, |deriv (frozenElliptic p u) y| ≤ Bv)
    (hz_lb : ∀ k y, 0 ≤ z k y) (hz_ub : ∀ k y, z k y ≤ M)
    (hU_lb : ∀ y, 0 ≤ U y) (hU_ub : ∀ y, U y ≤ M) :
    crossImplicitMap p c lam u U U = U := by
  funext x
  -- LHS sequence: z (k+1) x → U x
  have hzy : Tendsto (fun k => z k x) atTop (𝓝 (U x)) := hLU.tendsto_at x
  have hLHS : Tendsto (fun k => z (k+1) x) atTop (𝓝 (U x)) :=
    hzy.comp (tendsto_add_atTop_nat 1)
  -- RHS sequence via the recursion = crossImplicitMap at (z k, z(k+1))
  have hRHSeq : ∀ k, z (k+1) x = crossImplicitMap p c lam u (z k) (z (k+1)) x := by
    intro k; exact congrFun (hrec k) x
  -- the two Green integrals converge
  have hI1 := rothe_reactionIntegral_tendsto (p := p) (c := c) (lam := lam)
    (z := z) (U := U) (M := M) hlam hM hLU hz_cont hU_cont hz_lb hz_ub hU_lb hU_ub x
  have hI2 := rothe_fluxIntegral_tendsto (p := p) (u := u) (c := c) (lam := lam)
    (z := z) (U := U) (M := M) (Bv := Bv) hlam hM hBv hLU hz_cont hU_cont hV_cont
    hV_bound hz_lb hz_ub hU_lb hU_ub x
  -- assemble the RHS convergence to crossImplicitMap p c lam u U U x
  have hRHS : Tendsto (fun k => crossImplicitMap p c lam u (z k) (z (k+1)) x) atTop
      (𝓝 (crossImplicitMap p c lam u U U x)) := by
    have := hI1.sub (hI2.const_mul p.χ)
    -- rewrite both sides to the crossImplicitMap form
    simpa only [crossImplicitMap] using this
  -- now the recursion makes LHS = RHS sequence; equate limits
  have hRHS' : Tendsto (fun k => z (k+1) x) atTop
      (𝓝 (crossImplicitMap p c lam u U U x)) := by
    refine hRHS.congr ?_
    intro k; exact (hRHSeq k).symm
  exact tendsto_nhds_unique hRHS' hLHS

end DomConv

/-! ## Diagonal collapse and the assembled stationarity -/

/-- **Goal 2 — diagonal collapse to `auxMap` at the outer fixed point.**
At the OUTER Schauder fixed point the frozen profile equals the limit (`u = U`).
Then the cross-map fixed point `crossImplicitMap p c lam U U U = U` collapses,
via the committed `crossImplicitMap_self_eq_auxMap`, to `auxMap p c lam U = U`. -/
theorem rotheLimit_auxMap_fixed_at_diagonal
    (p : CMParams) (c lam : ℝ) (U : ℝ → ℝ)
    (hcross : crossImplicitMap p c lam U U U = U) :
    auxMap p c lam U = U := by
  rw [← crossImplicitMap_self_eq_auxMap p c lam U]
  exact hcross

/-- **Goal 3 — assembled Rothe-limit stationarity (B1 headline).**
At the outer fixed point (`u = U`), the diagonal `crossImplicitMap p c lam U U U
= U` (from the Rothe limit, Goal 1 + Goal 2) together with the per-`U` Green
identity yields the stationary profile equation
`∀ x, frozenWaveOperator p c U U x = 0` via the committed `fixedPoint_stationary`.

`hcross` is supplied by `rotheLimit_crossImplicitMap_fixed` specialised to the
diagonal `u = U`; `hgreen` is the per-`U` Green identity (discharged elsewhere
by `greenIdentity_of_convRepr` + `flux_ibp` under the per-`U` C¹/decay data). -/
theorem rotheLimit_stationary
    (p : CMParams) (c lam : ℝ) (U : ℝ → ℝ)
    (hcross : crossImplicitMap p c lam U U U = U)
    (hgreen : GreenIdentity p c lam U) :
    ∀ x, frozenWaveOperator p c U U x = 0 := by
  have hfix : auxMap p c lam U = U :=
    rotheLimit_auxMap_fixed_at_diagonal p c lam U hcross
  exact fixedPoint_stationary p c lam U hgreen hfix

end ShenWork.Paper1
