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
import ShenWork.Paper1.WaveStepFluxId
import ShenWork.Paper1.WaveRotheC1
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

/-! ## Stationary Green representation bridge -/

/-- Bounded homogeneous solutions of
`W'' + c W' - lam W = 0` on the line vanish.  The proof uses the two
characteristic-root invariants and kills their constants by boundedness at the
two spatial infinities. -/
theorem bounded_solution_unique_of_linear_homogeneous
    (hlam : 0 < lam) {W : ℝ → ℝ}
    (hW_diff : Differentiable ℝ W)
    (hW'_diff : Differentiable ℝ (deriv W))
    (hW_eq : ∀ x, deriv (deriv W) x + c * deriv W x - lam * W x = 0)
    (hW_bdd : ∃ M : ℝ, ∀ x, |W x| ≤ M)
    (hW'_bdd : ∃ M : ℝ, ∀ x, |deriv W x| ≤ M) :
    ∀ x, W x = 0 := by
  let rp : ℝ := greenRootPlus c lam
  let rm : ℝ := greenRootMinus c lam
  have hrp_pos : 0 < rp := by
    simpa [rp] using greenRootPlus_pos (c := c) (lam := lam) hlam
  have hrm_neg : rm < 0 := by
    simpa [rm] using greenRootMinus_neg (c := c) (lam := lam) hlam
  have hsum : rp + rm = -c := by
    simpa [rp, rm] using greenRoots_add (c := c) (lam := lam)
  have hmul : rp * rm = -lam := by
    simpa [rp, rm] using greenRoots_mul (c := c) (lam := lam) hlam
  let A : ℝ → ℝ := fun x => deriv W x - rm * W x
  let u : ℝ → ℝ := fun x => A x * Real.exp (-(rp * x))
  have hexp_rp : ∀ x, HasDerivAt (fun y : ℝ => Real.exp (-(rp * y)))
      (-(rp) * Real.exp (-(rp * x))) x := by
    intro x
    have hlin : HasDerivAt (fun y : ℝ => -(rp) * y) (-(rp)) x := by
      simpa [neg_mul] using (hasDerivAt_id x).const_mul (-(rp))
    convert hlin.exp using 1
    · ext y; ring
    · ring
  have hA_deriv : ∀ x, HasDerivAt A (rp * A x) x := by
    intro x
    have hA0 : HasDerivAt A (deriv (deriv W) x - rm * deriv W x) x := by
      simpa [A] using
        (hW'_diff x).hasDerivAt.sub ((hW_diff x).hasDerivAt.const_mul rm)
    convert hA0 using 1
    dsimp [A]
    have hc_eq : c = -(rp + rm) := by linarith
    have hlam_eq : lam = -(rp * rm) := by linarith
    have hval :
        deriv (deriv W) x - rm * deriv W x
          = rp * (deriv W x - rm * W x) := by
      calc
        deriv (deriv W) x - rm * deriv W x
          = (-c * deriv W x + lam * W x) - rm * deriv W x := by
              linarith [hW_eq x]
        _ = rp * (deriv W x - rm * W x) := by
              rw [hc_eq, hlam_eq]
              ring
    exact hval.symm
  have hu_diff : Differentiable ℝ u := by
    intro x
    exact ((hA_deriv x).mul (hexp_rp x)).differentiableAt
  have hu_deriv : ∀ x, deriv u x = 0 := by
    intro x
    have hu_at : HasDerivAt u
        (rp * A x * Real.exp (-(rp * x))
          + A x * (-rp * Real.exp (-(rp * x)))) x := by
      simpa [u] using (hA_deriv x).mul (hexp_rp x)
    rw [hu_at.deriv]
    ring
  have hu_const : ∀ x, u x = u 0 :=
    fun x => is_const_of_deriv_eq_zero hu_diff hu_deriv x 0
  have hA_exp : ∀ x, A x = u 0 * Real.exp (rp * x) := by
    intro x
    have h_eq : A x * Real.exp (-(rp * x)) = u 0 := hu_const x
    have hexp_inv : Real.exp (-(rp * x)) * Real.exp (rp * x) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      simp
    calc
      A x = A x * 1 := by ring
      _ = A x * (Real.exp (-(rp * x)) * Real.exp (rp * x)) := by rw [hexp_inv]
      _ = (A x * Real.exp (-(rp * x))) * Real.exp (rp * x) := by ring
      _ = u 0 * Real.exp (rp * x) := by rw [h_eq]
  have hA0 : u 0 = 0 := by
    by_contra hne
    obtain ⟨MW, hMW⟩ := hW_bdd
    obtain ⟨MW', hMW'⟩ := hW'_bdd
    have hMW_nonneg : 0 ≤ MW := le_trans (abs_nonneg (W 0)) (hMW 0)
    have hMW'_nonneg : 0 ≤ MW' := le_trans (abs_nonneg (deriv W 0)) (hMW' 0)
    have hA_bdd : ∀ x, |A x| ≤ MW' + |rm| * MW := by
      intro x
      calc
        |A x| = |deriv W x - rm * W x| := rfl
        _ ≤ |deriv W x| + |rm * W x| := abs_sub _ _
        _ = |deriv W x| + |rm| * |W x| := by rw [abs_mul]
        _ ≤ MW' + |rm| * MW := by
          exact add_le_add (hMW' x)
            (mul_le_mul_of_nonneg_left (hMW x) (abs_nonneg rm))
    have hbound_nonneg : 0 ≤ MW' + |rm| * MW := by positivity
    have hu0_pos : 0 < |u 0| := abs_pos.mpr hne
    have h_exp_atTop :
        Tendsto (fun x : ℝ => Real.exp (rp * x)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hrp_pos)
    obtain ⟨x, hx⟩ :=
      (h_exp_atTop.eventually_gt_atTop ((MW' + |rm| * MW) / |u 0|)).exists
    have hbig : MW' + |rm| * MW < |u 0| * Real.exp (rp * x) := by
      rw [div_lt_iff₀ hu0_pos] at hx
      linarith
    have hA_abs : |A x| = |u 0| * Real.exp (rp * x) := by
      rw [hA_exp x, abs_mul, abs_of_pos (Real.exp_pos _)]
    linarith [hA_bdd x, hA_abs, hbig]
  have hA_zero : ∀ x, A x = 0 := by
    intro x
    rw [hA_exp x, hA0]
    simp
  let B : ℝ → ℝ := fun x => deriv W x - rp * W x
  let v : ℝ → ℝ := fun x => B x * Real.exp (-(rm * x))
  have hexp_rm : ∀ x, HasDerivAt (fun y : ℝ => Real.exp (-(rm * y)))
      (-(rm) * Real.exp (-(rm * x))) x := by
    intro x
    have hlin : HasDerivAt (fun y : ℝ => -(rm) * y) (-(rm)) x := by
      simpa [neg_mul] using (hasDerivAt_id x).const_mul (-(rm))
    convert hlin.exp using 1
    · ext y; ring
    · ring
  have hB_deriv : ∀ x, HasDerivAt B (rm * B x) x := by
    intro x
    have hB0 : HasDerivAt B (deriv (deriv W) x - rp * deriv W x) x := by
      simpa [B] using
        (hW'_diff x).hasDerivAt.sub ((hW_diff x).hasDerivAt.const_mul rp)
    convert hB0 using 1
    dsimp [B]
    have hc_eq : c = -(rp + rm) := by linarith
    have hlam_eq : lam = -(rp * rm) := by linarith
    have hval :
        deriv (deriv W) x - rp * deriv W x
          = rm * (deriv W x - rp * W x) := by
      calc
        deriv (deriv W) x - rp * deriv W x
          = (-c * deriv W x + lam * W x) - rp * deriv W x := by
              linarith [hW_eq x]
        _ = rm * (deriv W x - rp * W x) := by
              rw [hc_eq, hlam_eq]
              ring
    exact hval.symm
  have hv_diff : Differentiable ℝ v := by
    intro x
    exact ((hB_deriv x).mul (hexp_rm x)).differentiableAt
  have hv_deriv : ∀ x, deriv v x = 0 := by
    intro x
    have hv_at : HasDerivAt v
        (rm * B x * Real.exp (-(rm * x))
          + B x * (-rm * Real.exp (-(rm * x)))) x := by
      simpa [v] using (hB_deriv x).mul (hexp_rm x)
    rw [hv_at.deriv]
    ring
  have hv_const : ∀ x, v x = v 0 :=
    fun x => is_const_of_deriv_eq_zero hv_diff hv_deriv x 0
  have hB_exp : ∀ x, B x = v 0 * Real.exp (rm * x) := by
    intro x
    have h_eq : B x * Real.exp (-(rm * x)) = v 0 := hv_const x
    have hexp_inv : Real.exp (-(rm * x)) * Real.exp (rm * x) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      simp
    calc
      B x = B x * 1 := by ring
      _ = B x * (Real.exp (-(rm * x)) * Real.exp (rm * x)) := by rw [hexp_inv]
      _ = (B x * Real.exp (-(rm * x))) * Real.exp (rm * x) := by ring
      _ = v 0 * Real.exp (rm * x) := by rw [h_eq]
  have hB0 : v 0 = 0 := by
    by_contra hne
    obtain ⟨MW, hMW⟩ := hW_bdd
    obtain ⟨MW', hMW'⟩ := hW'_bdd
    have hMW_nonneg : 0 ≤ MW := le_trans (abs_nonneg (W 0)) (hMW 0)
    have hMW'_nonneg : 0 ≤ MW' := le_trans (abs_nonneg (deriv W 0)) (hMW' 0)
    have hB_bdd : ∀ x, |B x| ≤ MW' + |rp| * MW := by
      intro x
      calc
        |B x| = |deriv W x - rp * W x| := rfl
        _ ≤ |deriv W x| + |rp * W x| := abs_sub _ _
        _ = |deriv W x| + |rp| * |W x| := by rw [abs_mul]
        _ ≤ MW' + |rp| * MW := by
          exact add_le_add (hMW' x)
            (mul_le_mul_of_nonneg_left (hMW x) (abs_nonneg rp))
    have hbound_nonneg : 0 ≤ MW' + |rp| * MW := by positivity
    have hv0_pos : 0 < |v 0| := abs_pos.mpr hne
    have h_exp_atBot :
        Tendsto (fun x : ℝ => Real.exp (rm * x)) atBot atTop :=
      Real.tendsto_exp_atTop.comp
        ((tendsto_const_mul_atTop_of_neg (f := fun x : ℝ => x) hrm_neg).2 tendsto_id)
    obtain ⟨x, hx⟩ :=
      (h_exp_atBot.eventually_gt_atTop ((MW' + |rp| * MW) / |v 0|)).exists
    have hbig : MW' + |rp| * MW < |v 0| * Real.exp (rm * x) := by
      rw [div_lt_iff₀ hv0_pos] at hx
      linarith
    have hB_abs : |B x| = |v 0| * Real.exp (rm * x) := by
      rw [hB_exp x, abs_mul, abs_of_pos (Real.exp_pos _)]
    linarith [hB_bdd x, hB_abs, hbig]
  have hB_zero : ∀ x, B x = 0 := by
    intro x
    rw [hB_exp x, hB0]
    simp
  intro x
  have hroot_ne : rp - rm ≠ 0 := by
    have : rm < rp := lt_trans hrm_neg hrp_pos
    linarith
  have hlin : (rp - rm) * W x = 0 := by
    have hA := hA_zero x
    have hB := hB_zero x
    dsimp [A, B] at hA hB
    linarith
  exact (mul_eq_zero.mp hlin).resolve_left hroot_ne

/-- `greenConv` solves the negative-source resolvent equation, expressed with
the actual `deriv` and `iteratedDeriv` operators. -/
theorem greenConv_variation_negative_stationary
    (hlam : 0 < lam) {R : ℝ → ℝ} (hR : Continuous R)
    (hRhi : ∀ x,
      IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi x))
    (hRlo : ∀ x,
      IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic x))
    (x : ℝ) :
    iteratedDeriv 2 (greenConv c lam R) x
        + c * deriv (greenConv c lam R) x
        - lam * greenConv c lam R x
      = -R x := by
  have hw' : ∀ y, HasDerivAt (greenConv c lam R)
      (greenConvDeriv c lam R y) y := fun y =>
    greenConv_hasDerivAt (c := c) (lam := lam) hR hRhi hRlo y
  have hderiv_eq :
      deriv (greenConv c lam R) = fun y => greenConvDeriv c lam R y :=
    funext fun y => (hw' y).deriv
  have hw'' : HasDerivAt (deriv (greenConv c lam R))
      (greenConvDeriv2 c lam R x) x := by
    rw [hderiv_eq]
    exact greenConvDeriv_hasDerivAt (c := c) (lam := lam) hR hRhi hRlo x
  have hiter : iteratedDeriv 2 (greenConv c lam R) x =
      greenConvDeriv2 c lam R x := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact hw''.deriv
  rw [hiter, hderiv_eq]
  exact greenConv_solves (c := c) (lam := lam) hlam (H := R) x

/-- A bounded source gives a bounded Green convolution.  The bound is written
in the two-tail constants used by the explicit `greenConv` formula. -/
theorem greenConv_abs_le_of_source_bound
    (hlam : 0 < lam) {H : ℝ → ℝ} {B : ℝ}
    (hB : ∀ y, |H y| ≤ B)
    (hHi : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) H) (Ioi x))
    (hLo : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) H) (Iic x))
    (x : ℝ) :
    |greenConv c lam H x| ≤
      (greenDelta c lam)⁻¹ *
        (B / greenRootPlus c lam + B / (-greenRootMinus c lam)) := by
  have hrp : 0 < greenRootPlus c lam := greenRootPlus_pos (c := c) (lam := lam) hlam
  have hrm : greenRootMinus c lam < 0 := greenRootMinus_neg (c := c) (lam := lam) hlam
  have hδ : 0 < (greenDelta c lam)⁻¹ :=
    inv_pos.mpr (greenDelta_pos (c := c) hlam)
  have hHi_bd :=
    tailHi_weighted_abs_le
      (r := greenRootPlus c lam) hrp hHi hB x
  have hLo_bd :=
    tailLo_weighted_abs_le
      (r := greenRootMinus c lam) hrm hLo hB x
  have hHi' :
      Real.exp (greenRootPlus c lam * x) *
          |tailHi (greenRootPlus c lam) H x|
        ≤ B / greenRootPlus c lam := by
    rw [le_div_iff₀ hrp]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hHi_bd
  have hLo' :
      Real.exp (greenRootMinus c lam * x) *
          |tailLo (greenRootMinus c lam) H x|
        ≤ B / (-greenRootMinus c lam) := by
    rw [le_div_iff₀ (neg_pos.mpr hrm)]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hLo_bd
  rw [greenConv, abs_mul, abs_of_pos hδ]
  have hsum :
      |Real.exp (greenRootPlus c lam * x) *
            tailHi (greenRootPlus c lam) H x
        + Real.exp (greenRootMinus c lam * x) *
            tailLo (greenRootMinus c lam) H x|
        ≤ B / greenRootPlus c lam + B / (-greenRootMinus c lam) := by
    have hA :
        |Real.exp (greenRootPlus c lam * x) *
            tailHi (greenRootPlus c lam) H x|
          =
        Real.exp (greenRootPlus c lam * x) *
            |tailHi (greenRootPlus c lam) H x| := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hBtail :
        |Real.exp (greenRootMinus c lam * x) *
            tailLo (greenRootMinus c lam) H x|
          =
        Real.exp (greenRootMinus c lam * x) *
            |tailLo (greenRootMinus c lam) H x| := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      |Real.exp (greenRootPlus c lam * x) *
            tailHi (greenRootPlus c lam) H x
        + Real.exp (greenRootMinus c lam * x) *
            tailLo (greenRootMinus c lam) H x|
          ≤ |Real.exp (greenRootPlus c lam * x) *
              tailHi (greenRootPlus c lam) H x|
            + |Real.exp (greenRootMinus c lam * x) *
              tailLo (greenRootMinus c lam) H x| := abs_add_le _ _
      _ = Real.exp (greenRootPlus c lam * x) *
              |tailHi (greenRootPlus c lam) H x|
            + Real.exp (greenRootMinus c lam * x) *
              |tailLo (greenRootMinus c lam) H x| := by rw [hA, hBtail]
      _ ≤ B / greenRootPlus c lam + B / (-greenRootMinus c lam) :=
            add_le_add hHi' hLo'
  exact mul_le_mul_of_nonneg_left hsum hδ.le

/-- The source in the diagonal cross map, rewritten by stationary operator
zero as the linear resolvent source. -/
theorem crossSource_eq_linear_of_frozenWaveOperator_zero
    (p : CMParams) (c lam : ℝ) (U : ℝ → ℝ)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0) :
    ∀ x, crossSource p lam U U U x =
      lam * U x - (iteratedDeriv 2 U x + c * deriv U x) := by
  intro x
  have hx := hstat x
  unfold frozenWaveOperator at hx
  unfold crossSource reactionFun
  linarith

/-- The flux/IBP hypotheses needed to identify the raw diagonal cross map with
the Green convolution of its differential source.  These are exactly the
non-algebraic inputs consumed by `crossImplicitMap_eq_greenConv_crossSource`,
specialized to `u = Z = W = U`. -/
structure StationaryCrossGreenData
    (p : CMParams) (c lam : ℝ) (U : ℝ → ℝ) : Prop where
  hSmIic : ∀ x, IntegrableOn (fun y => greenKernel c lam (x - y)
      * (reactionFun p.α (U y) + lam * U y)) (Set.Iic x)
  hSmIoi : ∀ x, IntegrableOn (fun y => greenKernel c lam (x - y)
      * (reactionFun p.α (U y) + lam * U y)) (Set.Ioi x)
  hFlIic : ∀ x, IntegrableOn (fun y => greenKernel c lam (x - y)
      * (-p.χ * deriv (stepFlux p U U) y)) (Set.Iic x)
  hFlIoi : ∀ x, IntegrableOn (fun y => greenKernel c lam (x - y)
      * (-p.χ * deriv (stepFlux p U U) y)) (Set.Ioi x)
  hG_C1 : ∀ y, HasDerivAt (stepFlux p U U) (deriv (stepFlux p U U) y) y
  hKv'_Ioi : ∀ x, IntegrableOn
      ((fun y => greenKernel c lam (x - y)) * deriv (stepFlux p U U)) (Ioi x)
  hKv'_Iic : ∀ x, IntegrableOn
      ((fun y => greenKernel c lam (x - y)) * deriv (stepFlux p U U)) (Iic x)
  hK'v_Ioi : ∀ x, IntegrableOn
      ((fun y => -greenKernelDeriv c lam (x - y)) * stepFlux p U U) (Ioi x)
  hK'v_Iic : ∀ x, IntegrableOn
      ((fun y => -greenKernelDeriv c lam (x - y)) * stepFlux p U U) (Iic x)
  hKG_Iic : ∀ x, IntegrableOn
      (fun y => greenKernel c lam (x - y)
        * (-p.χ * deriv (stepFlux p U U) y)) (Iic x)
  hKG_Ioi : ∀ x, IntegrableOn
      (fun y => greenKernel c lam (x - y)
        * (-p.χ * deriv (stepFlux p U U) y)) (Ioi x)
  hdecay_top : ∀ x, Tendsto
      ((fun y => greenKernel c lam (x - y)) * stepFlux p U U) atTop (𝓝 0)
  hdecay_bot : ∀ x, Tendsto
      ((fun y => greenKernel c lam (x - y)) * stepFlux p U U) atBot (𝓝 0)

theorem StationaryCrossGreenData.crossImplicitMap_eq_greenConv_crossSource
    {p : CMParams} {c lam : ℝ} {U : ℝ → ℝ}
    (hlam : 0 < lam) (hdata : StationaryCrossGreenData p c lam U) :
    crossImplicitMap p c lam U U U =
      fun x => greenConv c lam (crossSource p lam U U U) x := by
  funext x
  exact ShenWork.Paper1.crossImplicitMap_eq_greenConv_crossSource p hlam U U U x
    (hdata.hSmIic x) (hdata.hSmIoi x) (hdata.hFlIic x) (hdata.hFlIoi x)
    hdata.hG_C1 (hdata.hKv'_Ioi x) (hdata.hKv'_Iic x)
    (hdata.hK'v_Ioi x) (hdata.hK'v_Iic x)
    (hdata.hKG_Iic x) (hdata.hKG_Ioi x)
    (hdata.hdecay_top x) (hdata.hdecay_bot x)

/-- Resolvent inversion for a stationary diagonal profile: operator-zero and
the source/IBP hypotheses force the diagonal cross implicit map to fix `U`. -/
theorem frozenWaveOperator_zero_crossImplicitMap_fixed
    {p : CMParams} {c lam : ℝ} {U : ℝ → ℝ}
    (hlam : 0 < lam)
    (hdata : StationaryCrossGreenData p c lam U)
    (hR_cont : Continuous (crossSource p lam U U U))
    (hR_bound : ∃ B : ℝ, ∀ y, |crossSource p lam U U U y| ≤ B)
    (hRhi : ∀ x,
      IntegrableOn (gWeight (greenRootPlus c lam) (crossSource p lam U U U)) (Ioi x))
    (hRlo : ∀ x,
      IntegrableOn (gWeight (greenRootMinus c lam) (crossSource p lam U U U)) (Iic x))
    (hU_diff : Differentiable ℝ U)
    (hU'_diff : Differentiable ℝ (deriv U))
    (hU_bdd : ∃ M : ℝ, ∀ x, |U x| ≤ M)
    (hU'_bdd : ∃ M : ℝ, ∀ x, |deriv U x| ≤ M)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0) :
    crossImplicitMap p c lam U U U = U := by
  let R : ℝ → ℝ := crossSource p lam U U U
  obtain ⟨BR, hBR⟩ := hR_bound
  have hcross_green :
      crossImplicitMap p c lam U U U = fun x => greenConv c lam R x := by
    simpa [R] using
      StationaryCrossGreenData.crossImplicitMap_eq_greenConv_crossSource
        (p := p) (c := c) (lam := lam) (U := U) hlam hdata
  have hU_linear : ∀ x,
      iteratedDeriv 2 U x + c * deriv U x - lam * U x = -R x := by
    intro x
    have hsrc := crossSource_eq_linear_of_frozenWaveOperator_zero
      p c lam U hstat x
    dsimp [R] at hsrc ⊢
    linarith
  have hG_linear : ∀ x,
      iteratedDeriv 2 (greenConv c lam R) x
        + c * deriv (greenConv c lam R) x
        - lam * greenConv c lam R x = -R x := by
    intro x
    exact greenConv_variation_negative_stationary
      (c := c) (lam := lam) hlam (R := R) (by simpa [R] using hR_cont)
      (by simpa [R] using hRhi) (by simpa [R] using hRlo) x
  have hG_diff : Differentiable ℝ (greenConv c lam R) := by
    intro x
    exact (greenConv_hasDerivAt
      (c := c) (lam := lam) (H := R) (by simpa [R] using hR_cont)
      (by simpa [R] using hRhi) (by simpa [R] using hRlo) x).differentiableAt
  have hG_deriv_eq :
      deriv (greenConv c lam R) = fun y => greenConvDeriv c lam R y :=
    funext fun y =>
      (greenConv_hasDerivAt
        (c := c) (lam := lam) (H := R) (by simpa [R] using hR_cont)
        (by simpa [R] using hRhi) (by simpa [R] using hRlo) y).deriv
  have hG'_diff : Differentiable ℝ (deriv (greenConv c lam R)) := by
    rw [hG_deriv_eq]
    intro x
    exact (greenConvDeriv_hasDerivAt
      (c := c) (lam := lam) (H := R) (by simpa [R] using hR_cont)
      (by simpa [R] using hRhi) (by simpa [R] using hRlo) x).differentiableAt
  have hG_bdd : ∃ M : ℝ, ∀ x, |greenConv c lam R x| ≤ M := by
    refine ⟨(greenDelta c lam)⁻¹ *
        (BR / greenRootPlus c lam + BR / (-greenRootMinus c lam)), ?_⟩
    intro x
    exact greenConv_abs_le_of_source_bound
      (c := c) (lam := lam) hlam (H := R) (B := BR)
      (by simpa [R] using hBR)
      (by simpa [R] using hRhi) (by simpa [R] using hRlo) x
  have hG'_bdd : ∃ M : ℝ, ∀ x, |deriv (greenConv c lam R) x| ≤ M := by
    refine ⟨2 * (greenDelta c lam)⁻¹ * BR, ?_⟩
    intro x
    rw [hG_deriv_eq]
    exact greenConvDeriv_abs_le
      (c := c) (lam := lam) hlam (H := R) (B := BR)
      (by simpa [R] using hBR)
      (by simpa [R] using hRhi) (by simpa [R] using hRlo) x
  let W : ℝ → ℝ := fun x => U x - greenConv c lam R x
  have hW_diff : Differentiable ℝ W := by
    intro x
    exact ((hU_diff x).sub (hG_diff x))
  have hW_deriv_eq :
      deriv W = fun x => deriv U x - deriv (greenConv c lam R) x := by
    funext x
    exact ((hU_diff x).hasDerivAt.sub (hG_diff x).hasDerivAt).deriv
  have hW'_diff : Differentiable ℝ (deriv W) := by
    rw [hW_deriv_eq]
    intro x
    exact (hU'_diff x).sub (hG'_diff x)
  have hW_eq : ∀ x, deriv (deriv W) x + c * deriv W x - lam * W x = 0 := by
    intro x
    have hsecond : deriv (deriv W) x =
        deriv (deriv U) x - deriv (deriv (greenConv c lam R)) x := by
      rw [hW_deriv_eq]
      exact ((hU'_diff x).hasDerivAt.sub (hG'_diff x).hasDerivAt).deriv
    have hiterU : iteratedDeriv 2 U x = deriv (deriv U) x := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have hiterG : iteratedDeriv 2 (greenConv c lam R) x =
        deriv (deriv (greenConv c lam R)) x := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [hsecond]
    rw [hW_deriv_eq]
    dsimp [W]
    have hUeq := hU_linear x
    have hGeq := hG_linear x
    rw [hiterU] at hUeq
    rw [hiterG] at hGeq
    linarith
  have hW_bdd : ∃ M : ℝ, ∀ x, |W x| ≤ M := by
    obtain ⟨MU, hMU⟩ := hU_bdd
    obtain ⟨MG, hMG⟩ := hG_bdd
    refine ⟨MU + MG, ?_⟩
    intro x
    have htri : |W x| ≤ |U x| + |greenConv c lam R x| := by
      dsimp [W]
      exact abs_sub _ _
    linarith [htri, hMU x, hMG x]
  have hW'_bdd : ∃ M : ℝ, ∀ x, |deriv W x| ≤ M := by
    obtain ⟨MU', hMU'⟩ := hU'_bdd
    obtain ⟨MG', hMG'⟩ := hG'_bdd
    refine ⟨MU' + MG', ?_⟩
    intro x
    rw [hW_deriv_eq]
    have htri : |deriv U x - deriv (greenConv c lam R) x| ≤
        |deriv U x| + |deriv (greenConv c lam R) x| := abs_sub _ _
    linarith [htri, hMU' x, hMG' x]
  have hW_zero : ∀ x, W x = 0 :=
    bounded_solution_unique_of_linear_homogeneous
      (c := c) (lam := lam) hlam hW_diff hW'_diff hW_eq hW_bdd hW'_bdd
  have hU_green : U = fun x => greenConv c lam R x := by
    funext x
    have hx := hW_zero x
    dsimp [W] at hx
    linarith
  rw [hcross_green, ← hU_green]

end ShenWork.Paper1
