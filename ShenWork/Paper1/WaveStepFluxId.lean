/-
  ShenWork/Paper1/WaveStepFluxId.lean

  **The cross-frozen step-flux IBP identity** discharging the genuinely-uncommitted
  `step_eq` field of `RotheStepAnalytic` (the carried `crossStepSelfMap`↔
  `crossImplicitMap` bridge of `RotheStepInput`/`rotheStepProducer`,
  WaveRotheProducer.lean).

  GOAL (`crossStepSelfMap_apply_eq_crossImplicitMap`):
  for a TRAPPED `W` (`∀ y, W y ∈ [0,M]`), the concrete bcf step self-map built on
  the `[0,M]`-truncated source equals the raw double-integral implicit map:

      `(crossStepSelfMap (greenKernel_continuous) (greenKernel_integrable hlam)
          (crossStepSourceConcrete p.α p.m M lam … Z Vu') W : ℝ → ℝ)
        = crossImplicitMap p c lam u Z W`.

  ROUTE (the step-level analogue of the committed `auxMap_eq_negGreenConv`,
  WaveConvRepr.lean):

    * **Truncation removal.** On the trapped range the global truncations are
      invisible: `reactionTrunc p.α M (W y) = reactionFun p.α (W y)` and
      `rpowTrunc p.m M (W y) = (W y)^p.m` (`reactionTrunc_eq_on_Icc`/
      `rpowTrunc_eq_on_Icc`, WaveRotheTrunc.lean), so the source collapses to the
      raw source `reactionFun(W) + λ·Z + (W^m·Vu')`.

    * **bcf → raw split.** `greenConvBCF` unfolds to `kernelConvVal greenKernel`,
      whose value at `x` is the raw `∫ y, greenKernel(x−y)·(source y)` (by
      definition of `kernelConvVal`, WaveRotheTrap.lean).  Splitting the source
      into the reaction/λ-shift part and the flux part (carried integrability),
      the reaction part is exactly the first raw integral of `crossImplicitMap`.

    * **The single-flux step IBP.**  The concrete source carries its flux
      contribution as the *folded divergence* `−χ·∂ₓ(stepFlux p u W)`, recorded as
      the satisfiable bridge `hfold` (the way the producer constructs `Vu'`/the
      source).  Its `greenKernel`-convolution is `greenConv c λ (−χ·stepFlux')`
      (`kernelConv_eq_greenConv`), which the committed `flux_ibp_generic`
      (WaveStepFluxIBP.lean) — instantiated at `G = stepFlux p u W`, `κ = −p.χ`,
      carrying ONLY the standard flux `C¹`/decay/per-tail integrability it
      requires — turns into `−χ·∫ greenKernelDeriv(x−y)·stepFlux`, exactly the
      second term of `crossImplicitMap`.

  No `sorry`/`axiom`/`native_decide`/`admit`.  We carry ONLY the standard flux
  `C¹`/decay/integrability hypotheses that `flux_ibp_generic` consumes (NOT its
  conclusion), the smooth-source per-tail integrabilities, and the folded-flux
  bridge `hfold` — each satisfiable, none the conclusion.  Touches only Paper1.
-/
import ShenWork.Paper1.WaveRotheTrunc
import ShenWork.Paper1.WaveStepFluxIBP
import ShenWork.Paper1.WaveConvRepr

open Filter Topology MeasureTheory Real Set
open scoped BoundedContinuousFunction

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## The cross-frozen step-flux IBP identity -/

/-- **`crossStepSelfMap_apply_eq_crossImplicitMap` — the step-flux bcf↔raw +
truncation-on-trap identity.**

For a trapped `W` (`∀ y, W y ∈ [0,M]`), the concrete `[0,M]`-truncated bcf step
self-map equals the raw double-integral implicit step map `crossImplicitMap`.

The carried hypotheses are exactly:

* `hWtrap` — the trap `W y ∈ [0,M]` (kills the truncation);
* `hfold` — the folded divergence form of the concrete source flux
  (`(W y)^m·Vu' y = −χ·deriv (stepFlux p u W) y`), the way the producer builds the
  source; satisfiable, not the conclusion;
* the smooth-source per-tail integrabilities `hSmIic`/`hSmIoi` (reaction + λ·Z
  against the kernel), and the folded-flux convolution per-tail integrabilities
  `hFlIic`/`hFlIoi`, needed to split the single combined source integral;
* the standard flux `C¹`/decay/per-tail integrability data
  (`hG_C1`, `hKv'_*`, `hK'v_*`, `hKG_*`, `hdecay_*`) that `flux_ibp_generic`
  consumes at `G = stepFlux p u W`, `κ = −p.χ`. -/
theorem crossStepSelfMap_apply_eq_crossImplicitMap
    (p : CMParams) (hlam : 0 < lam) (M : ℝ) (hM : 0 ≤ M)
    (u Z : ℝ → ℝ) (Zb Vu' : ℝ →ᵇ ℝ) (W : ℝ →ᵇ ℝ)
    (hZ : ∀ y, (Zb y : ℝ) = Z y)
    (hWtrap : ∀ y, (W y : ℝ) ∈ Set.Icc (0 : ℝ) M)
    (hfold : ∀ y, ((W y : ℝ)) ^ p.m * Vu' y
      = -p.χ * deriv (stepFlux p u (fun y => (W y : ℝ))) y)
    (hSmIic : ∀ x, IntegrableOn (fun y => greenKernel c lam (x - y)
      * (reactionFun p.α (W y) + lam * Z y)) (Set.Iic x))
    (hSmIoi : ∀ x, IntegrableOn (fun y => greenKernel c lam (x - y)
      * (reactionFun p.α (W y) + lam * Z y)) (Set.Ioi x))
    (hFlIic : ∀ x, IntegrableOn (fun y => greenKernel c lam (x - y)
      * (-p.χ * deriv (stepFlux p u (fun y => (W y : ℝ))) y)) (Set.Iic x))
    (hFlIoi : ∀ x, IntegrableOn (fun y => greenKernel c lam (x - y)
      * (-p.χ * deriv (stepFlux p u (fun y => (W y : ℝ))) y)) (Set.Ioi x))
    (hG_C1 : ∀ y, HasDerivAt (stepFlux p u (fun y => (W y : ℝ)))
      (deriv (stepFlux p u (fun y => (W y : ℝ))) y) y)
    (hKv'_Ioi : ∀ x, IntegrableOn
      ((fun y => greenKernel c lam (x - y)) * deriv (stepFlux p u (fun y => (W y : ℝ)))) (Ioi x))
    (hKv'_Iic : ∀ x, IntegrableOn
      ((fun y => greenKernel c lam (x - y)) * deriv (stepFlux p u (fun y => (W y : ℝ)))) (Iic x))
    (hK'v_Ioi : ∀ x, IntegrableOn
      ((fun y => -greenKernelDeriv c lam (x - y)) * stepFlux p u (fun y => (W y : ℝ))) (Ioi x))
    (hK'v_Iic : ∀ x, IntegrableOn
      ((fun y => -greenKernelDeriv c lam (x - y)) * stepFlux p u (fun y => (W y : ℝ))) (Iic x))
    (hKG_Iic : ∀ x, IntegrableOn
      (fun y => greenKernel c lam (x - y)
        * (-p.χ * deriv (stepFlux p u (fun y => (W y : ℝ))) y)) (Iic x))
    (hKG_Ioi : ∀ x, IntegrableOn
      (fun y => greenKernel c lam (x - y)
        * (-p.χ * deriv (stepFlux p u (fun y => (W y : ℝ))) y)) (Ioi x))
    (hdecay_top : ∀ x, Tendsto
      ((fun y => greenKernel c lam (x - y)) * stepFlux p u (fun y => (W y : ℝ)))
      atTop (𝓝 0))
    (hdecay_bot : ∀ x, Tendsto
      ((fun y => greenKernel c lam (x - y)) * stepFlux p u (fun y => (W y : ℝ)))
      atBot (𝓝 0)) :
    (fun x => (crossStepSelfMap (greenKernel_continuous (c := c) (lam := lam))
        (greenKernel_integrable hlam)
        (crossStepSourceConcrete p.α p.m M lam p.hα p.hm hM Zb Vu') W : ℝ → ℝ) x)
      = crossImplicitMap p c lam u Z (fun y => (W y : ℝ)) := by
  funext x
  -- abbreviations for the cross-frozen step flux and its folded source
  set Wr : ℝ → ℝ := fun y => (W y : ℝ) with hWr
  -- ===== Step 0: unfold the LHS bcf self-map to the raw kernel convolution =====
  -- `crossStepSelfMap … S W x = greenConvBCF … (S W) x = kernelConvVal K (S W) x
  --                            = ∫ y, greenKernel(x−y)·(S W y)`
  have hLHS :
      (crossStepSelfMap (greenKernel_continuous (c := c) (lam := lam))
          (greenKernel_integrable hlam)
          (crossStepSourceConcrete p.α p.m M lam p.hα p.hm hM Zb Vu') W : ℝ → ℝ) x
        = ∫ y, greenKernel c lam (x - y)
            * (reactionFun p.α (Wr y) + lam * Z y
                + (-p.χ * deriv (stepFlux p u Wr) y)) := by
    -- unfold self-map → greenConvBCF → kernelConvVal (definitional)
    show greenConvBCF (greenKernel_continuous (c := c) (lam := lam))
        (greenKernel_integrable hlam)
        (crossStepSourceConcrete p.α p.m M lam p.hα p.hm hM Zb Vu' W) x = _
    rw [greenConvBCF_apply]
    show (∫ y, greenKernel c lam (x - y)
        * (crossStepSourceConcrete p.α p.m M lam p.hα p.hm hM Zb Vu' W) y) = _
    -- pointwise rewrite of the source integrand (truncation removal + fold)
    apply MeasureTheory.integral_congr_ae
    refine Filter.Eventually.of_forall (fun y => ?_)
    simp only [crossStepSourceConcrete_apply]
    have hWy : (W y : ℝ) ∈ Set.Icc (0 : ℝ) M := hWtrap y
    rw [reactionTrunc_eq_on_Icc hM hWy, rpowTrunc_eq_on_Icc hM hWy, hZ y, hfold y]
  -- ===== Step 1: split the combined source integral (reaction/λ + folded flux) =====
  have hsplit :
      (∫ y, greenKernel c lam (x - y)
          * (reactionFun p.α (Wr y) + lam * Z y
              + (-p.χ * deriv (stepFlux p u Wr) y)))
        = (∫ y, greenKernel c lam (x - y) * (reactionFun p.α (Wr y) + lam * Z y))
          + ∫ y, greenKernel c lam (x - y)
              * (-p.χ * deriv (stepFlux p u Wr) y) := by
    have hint_sm : Integrable (fun y => greenKernel c lam (x - y)
        * (reactionFun p.α (Wr y) + lam * Z y)) := by
      rw [← integrableOn_univ,
        show (Set.univ : Set ℝ) = Set.Iic x ∪ Set.Ioi x by
          ext y; simp only [Set.mem_univ, Set.mem_union, Set.mem_Iic, Set.mem_Ioi,
            true_iff]; exact le_or_gt y x]
      exact (hSmIic x).union (hSmIoi x)
    have hint_fl : Integrable (fun y => greenKernel c lam (x - y)
        * (-p.χ * deriv (stepFlux p u Wr) y)) := by
      rw [← integrableOn_univ,
        show (Set.univ : Set ℝ) = Set.Iic x ∪ Set.Ioi x by
          ext y; simp only [Set.mem_univ, Set.mem_union, Set.mem_Iic, Set.mem_Ioi,
            true_iff]; exact le_or_gt y x]
      exact (hFlIic x).union (hFlIoi x)
    rw [← MeasureTheory.integral_add hint_sm hint_fl]
    apply MeasureTheory.integral_congr_ae
    refine Filter.Eventually.of_forall (fun y => ?_)
    ring
  -- ===== Step 2: the folded-flux convolution = greenConv(−χ·stepFlux') =====
  have hfluxConv :
      (∫ y, greenKernel c lam (x - y) * (-p.χ * deriv (stepFlux p u Wr) y))
        = greenConv c lam (fun y => -p.χ * deriv (stepFlux p u Wr) y) x :=
    kernelConv_eq_greenConv (c := c) (lam := lam)
      (fun y => -p.χ * deriv (stepFlux p u Wr) y) x (hFlIic x) (hFlIoi x)
  -- ===== Step 3: flux IBP — greenConv(−χ·stepFlux') = −χ·∫ K'·stepFlux =====
  have hIBP :
      (-p.χ) * ∫ y, greenKernelDeriv c lam (x - y) * stepFlux p u Wr y
        = greenConv c lam (fun y => -p.χ * deriv (stepFlux p u Wr) y) x :=
    flux_ibp_generic c lam hlam (-p.χ) (stepFlux p u Wr) x
      (hG_C1) (hKv'_Ioi x) (hKv'_Iic x) (hK'v_Ioi x) (hK'v_Iic x)
      (hKG_Iic x) (hKG_Ioi x) (hdecay_top x) (hdecay_bot x)
  -- ===== Assemble =====
  rw [hLHS, hsplit, hfluxConv, ← hIBP]
  -- RHS = crossImplicitMap = (smooth) − χ·∫ K'·stepFlux
  show _ = (∫ y, greenKernel c lam (x - y) * (reactionFun p.α (Wr y) + lam * Z y))
      - p.χ * ∫ y, greenKernelDeriv c lam (x - y)
          * ((Wr y) ^ p.m * deriv (frozenElliptic p u) y)
  -- `stepFlux p u Wr y = (Wr y)^m · (frozenElliptic p u)'`, and `−χ·∫ = −(χ·∫)`
  simp only [stepFlux]
  ring

/-- **Green source representation of the raw cross-frozen step.**
The divergence-form implicit map is the Green convolution of the differential
source

`crossSource p lam u Z W = reaction(W) + lam*Z - χ * deriv(stepFlux p u W)`.

This is the source-side half of the Banach construction: once a fixed point has
been identified with `crossImplicitMap`, this lemma gives the committed
`W = greenConv c lam (crossSource p lam u Z W)` representation, modulo exactly
the same flux `C¹`/tail/decay hypotheses consumed by `flux_ibp_generic`. -/
theorem crossImplicitMap_eq_greenConv_crossSource
    (p : CMParams) (hlam : 0 < lam) (u Z W : ℝ → ℝ) (x : ℝ)
    (hSmIic : IntegrableOn (fun y => greenKernel c lam (x - y)
      * (reactionFun p.α (W y) + lam * Z y)) (Set.Iic x))
    (hSmIoi : IntegrableOn (fun y => greenKernel c lam (x - y)
      * (reactionFun p.α (W y) + lam * Z y)) (Set.Ioi x))
    (hFlIic : IntegrableOn (fun y => greenKernel c lam (x - y)
      * (-p.χ * deriv (stepFlux p u W) y)) (Set.Iic x))
    (hFlIoi : IntegrableOn (fun y => greenKernel c lam (x - y)
      * (-p.χ * deriv (stepFlux p u W) y)) (Set.Ioi x))
    (hG_C1 : ∀ y, HasDerivAt (stepFlux p u W) (deriv (stepFlux p u W) y) y)
    (hKv'_Ioi : IntegrableOn
      ((fun y => greenKernel c lam (x - y)) * deriv (stepFlux p u W)) (Ioi x))
    (hKv'_Iic : IntegrableOn
      ((fun y => greenKernel c lam (x - y)) * deriv (stepFlux p u W)) (Iic x))
    (hK'v_Ioi : IntegrableOn
      ((fun y => -greenKernelDeriv c lam (x - y)) * stepFlux p u W) (Ioi x))
    (hK'v_Iic : IntegrableOn
      ((fun y => -greenKernelDeriv c lam (x - y)) * stepFlux p u W) (Iic x))
    (hKG_Iic : IntegrableOn
      (fun y => greenKernel c lam (x - y) * (-p.χ * deriv (stepFlux p u W) y)) (Iic x))
    (hKG_Ioi : IntegrableOn
      (fun y => greenKernel c lam (x - y) * (-p.χ * deriv (stepFlux p u W) y)) (Ioi x))
    (hdecay_top : Tendsto ((fun y => greenKernel c lam (x - y)) * stepFlux p u W)
      atTop (𝓝 0))
    (hdecay_bot : Tendsto ((fun y => greenKernel c lam (x - y)) * stepFlux p u W)
      atBot (𝓝 0)) :
    crossImplicitMap p c lam u Z W x =
      greenConv c lam (crossSource p lam u Z W) x := by
  have hCrossIic : IntegrableOn (fun y => greenKernel c lam (x - y)
      * crossSource p lam u Z W y) (Set.Iic x) := by
    have hsum := hSmIic.add hFlIic
    refine hsum.congr_fun ?_ measurableSet_Iic
    intro y _hy
    simp only [Pi.add_apply]
    unfold crossSource stepFlux
    ring_nf
  have hCrossIoi : IntegrableOn (fun y => greenKernel c lam (x - y)
      * crossSource p lam u Z W y) (Set.Ioi x) := by
    have hsum := hSmIoi.add hFlIoi
    refine hsum.congr_fun ?_ measurableSet_Ioi
    intro y _hy
    simp only [Pi.add_apply]
    unfold crossSource stepFlux
    ring_nf
  have hsplit :
      (∫ y, greenKernel c lam (x - y) * crossSource p lam u Z W y)
        = (∫ y, greenKernel c lam (x - y) *
              (reactionFun p.α (W y) + lam * Z y))
          + ∫ y, greenKernel c lam (x - y) *
              (-p.χ * deriv (stepFlux p u W) y) := by
    have hint_sm : Integrable (fun y => greenKernel c lam (x - y)
        * (reactionFun p.α (W y) + lam * Z y)) := by
      rw [← integrableOn_univ,
        show (Set.univ : Set ℝ) = Set.Iic x ∪ Set.Ioi x by
          ext y; simp only [Set.mem_univ, Set.mem_union, Set.mem_Iic, Set.mem_Ioi,
            true_iff]; exact le_or_gt y x]
      exact hSmIic.union hSmIoi
    have hint_fl : Integrable (fun y => greenKernel c lam (x - y)
        * (-p.χ * deriv (stepFlux p u W) y)) := by
      rw [← integrableOn_univ,
        show (Set.univ : Set ℝ) = Set.Iic x ∪ Set.Ioi x by
          ext y; simp only [Set.mem_univ, Set.mem_union, Set.mem_Iic, Set.mem_Ioi,
            true_iff]; exact le_or_gt y x]
      exact hFlIic.union hFlIoi
    rw [← MeasureTheory.integral_add hint_sm hint_fl]
    apply MeasureTheory.integral_congr_ae
    refine Filter.Eventually.of_forall (fun y => ?_)
    unfold crossSource stepFlux
    ring
  have hfluxConv :
      (∫ y, greenKernel c lam (x - y) * (-p.χ * deriv (stepFlux p u W) y))
        = greenConv c lam (fun y => -p.χ * deriv (stepFlux p u W) y) x :=
    kernelConv_eq_greenConv (c := c) (lam := lam)
      (fun y => -p.χ * deriv (stepFlux p u W) y) x hFlIic hFlIoi
  have hIBP :
      (-p.χ) * ∫ y, greenKernelDeriv c lam (x - y) * stepFlux p u W y
        = greenConv c lam (fun y => -p.χ * deriv (stepFlux p u W) y) x :=
    flux_ibp_generic c lam hlam (-p.χ) (stepFlux p u W) x hG_C1
      hKv'_Ioi hKv'_Iic hK'v_Ioi hK'v_Iic hKG_Iic hKG_Ioi
      hdecay_top hdecay_bot
  calc
    crossImplicitMap p c lam u Z W x
        = (∫ y, greenKernel c lam (x - y) *
              (reactionFun p.α (W y) + lam * Z y))
          + (-p.χ) * ∫ y, greenKernelDeriv c lam (x - y) * stepFlux p u W y := by
            unfold crossImplicitMap stepFlux
            ring
    _ = (∫ y, greenKernel c lam (x - y) *
              (reactionFun p.α (W y) + lam * Z y))
          + greenConv c lam (fun y => -p.χ * deriv (stepFlux p u W) y) x := by
            rw [hIBP]
    _ = (∫ y, greenKernel c lam (x - y) *
              (reactionFun p.α (W y) + lam * Z y))
          + ∫ y, greenKernel c lam (x - y) *
              (-p.χ * deriv (stepFlux p u W) y) := by
            rw [← hfluxConv]
    _ = ∫ y, greenKernel c lam (x - y) * crossSource p lam u Z W y := hsplit.symm
    _ = greenConv c lam (crossSource p lam u Z W) x :=
            kernelConv_eq_greenConv (c := c) (lam := lam)
              (crossSource p lam u Z W) x hCrossIic hCrossIoi

/-! ## Axiom audit -/

section AxiomAudit
#print axioms crossStepSelfMap_apply_eq_crossImplicitMap
#print axioms crossImplicitMap_eq_greenConv_crossSource
end AxiomAudit

end ShenWork.Paper1
