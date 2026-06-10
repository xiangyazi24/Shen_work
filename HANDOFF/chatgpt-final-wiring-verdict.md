I’ll audit the current fa2adee wiring directly, focusing on hDu consumption, cone horizon choice versus restriction, GateCondition/A₂ selection, and Wdata representation shapes.

I found Hvsrc is already clamped-local, but hDu remains function-level and is used by rewrite, so restriction would require retyping. Strengthening the cone horizon looks preferable.

Verdict

Use the “strengthen the cone horizon up front” path, not restrictHorizon, for the final MildLocalChi0/Hres wiring.

restrictHorizon is mathematically valid, but it deliberately preserves D.u while changing D.T; therefore the canonical Picard-limit identity survives only on the smaller time window, not as function equality. The file says this explicitly: function-level equality after restriction is false because the restricted Picard limit is zero past T', while the old trajectory may be nonzero on (T', D.T].

IntervalDomainHresProducer

Current downstream APIs still require the strong function equality:

lean
D.u = picardLimit p u₀ D.T

in both MildLocalChi0.hMildLocal_chi0_zero_of_inputs and the Hres capstone/provider.

IntervalDomainMildLocalChi0



IntervalDomainThm11ChiZeroCoreP…

So horizon restriction would force a safe but broad retype to an EqOn/pointwise-on-window form. That retype is doable, but it is not the shortest route. The cone proof already chooses the horizon internally; strengthen that choice to satisfy the gate, and keep exact hDu : D.u = picardLimit p u₀ D.T.

1. Audit of hDu consumption

The current uses of hDu are slice-local, so an EqOn retype would be semantically safe.

In hconv_of_residual, hDu is only used to rewrite the evaluated slice D.u s for 0 < s ≤ D.T:

lean
have hslice : D.u s = picardLimit p u₀ D.T s := by rw [hDu]
rw [hslice]

IntervalDomainThm11ChiZeroResid…

In picardIterateResidualData_of_cone, hDu is likewise only used for one evaluated slice when proving limit-source continuity:

lean
have : picardLimit p u₀ D.T σ = D.u σ := by rw [hDu]

IntervalDomainHresProducer

The provider itself passes hDu only into hconv_of_residual; the rest of the construction uses D.hmild, D.hbound, D.hpos, D.hcont, and derived source packages.

IntervalDomainThm11ChiZeroCoreP…

So the following retype would be safe if you choose the restriction path:

lean
def PicardLimitEqOn
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∀ s, 0 < s → s ≤ D.T →
    D.u s = picardLimit p u₀ D.T s

Then replace every hDu : D.u = ... consumer with hDuOn s hs hsT.

But that is still more invasive than strengthening the cone: it touches MildLocalChi0, IntervalDomainThm11ChiZeroResidual, IntervalDomainHresProducer, IntervalDomainThm11ChiZeroCoreProvider, and any PLF/Hres lambdas. It also forces consistency work for PicardConvFacts.T = D.T, Wdata : ... D.T, and hsliceTC after restriction.

2. Cone horizon: current status and recommended strengthening

The cone theorem’s current horizon is not proven to satisfy the gate. Its header says the horizon is chosen from four constraints: contraction, ball preservation, δ ≤ 1, and cone-smallness.

IntervalMildPicardConeData

The actual proof sets

lean
Dn := C_L + C_L_val + Ke * Real.exp p.a + 1
T₀ := 1 / (2 * Dn)

and proves T₀ ≤ 1, C_L*T₀ < 1, the ball bound, and cone-smallness.

IntervalMildPicardConeData

There is no GateCondition in that proof. So the correct statement is:

The cone horizon does not already satisfy the gate in the code, but the proof is free to choose a smaller horizon. Strengthen the cone proof to choose T₀ ≤ Tgate as well.

This is the better path because the constructed record still has

lean
u := picardLimit p u₀ T₀

and the theorem returns exact function equality by rfl.

IntervalMildPicardConeData

GateCondition is downward-monotone in the horizon: its definition quantifies over t with t ≤ T, and Benv p M A₂ t depends on t, not on T.

IntervalPicardIterateUniform



IntervalPicardIterateUniform

Add:

lean
theorem GateCondition.mono
    {p : CM2Params} {M A₂ T₁ T₂ : ℝ}
    (hgate : GateCondition p M A₂ T₂)
    (hT : T₁ ≤ T₂) :
    GateCondition p M A₂ T₁ := by
  intro t ht htT₁
  exact hgate t ht (le_trans htT₁ hT)

Then the cone can choose a smaller T₀ and inherit the gate.

3. Where to choose A₂

Do not thread A₂ through public theorem statements unless you want it as a visible quantitative parameter. It is an internal bootstrap constant. Choose it inside the strengthened cone/Hres instantiation.

Add a small numeric gate-solver lemma near IntervalPicardIterateUniform.lean, or in a new file such as:

ShenWork/Paper2/IntervalPicardGateSolve.lean

Recommended theorem shape:

lean
theorem exists_gate_solution
    (p : CM2Params) {M : ℝ} (hM : 0 ≤ M) :
    ∃ A₂ Tgate : ℝ,
      0 ≤ A₂ ∧
      0 < Tgate ∧
      Tgate ≤ 1 ∧
      GateCondition p M A₂ Tgate

Concrete proof shape:

lean
let A₂ := max 1 (64 * M / (Real.exp 1 * Real.pi ^ 2))

Then choose Tgate > 0 small enough so the Duhamel self-coupling term

lean
duhamelGainConst * (t/2)^(1/4) *
  Benv p M A₂ t

is absorbed into the spare half of A₂ / t^2, after the homogeneous piece is bounded by homWeightBound. The existing g2_step_closes theorem shows the exact shape expected by the gate: the M2 step is absorbed once the gate is available.

IntervalPicardIterateUniform

If the explicit calculus is tedious, isolate it behind exists_gate_solution and use Classical.choose only inside the cone-strengthening theorem. Do not spread Classical.choose into MildLocalChi0.

Suggested strengthened cone theorem:

lean
theorem coneGradientMildSolutionData_exists_with_gate_data
    (p : CM2Params) (hχ : p.χ₀ = 0)
    {M_in : ℝ} (hM_in : 0 < M_in) (hα_ge : 1 ≤ p.α) :
    ∃ δ A₂ : ℝ, 0 < δ ∧ 0 ≤ A₂ ∧
      -- optionally expose the actual cone M if needed:
      -- ∃ Mcone, ...
      ∀ u₀ : intervalDomainPoint → ℝ,
        Continuous u₀ →
        (∀ x, |u₀ x| ≤ M_in) →
        (∀ x, 0 ≤ u₀ x) →
        (∃ x₀, 0 < u₀ x₀) →
        ∃ D : GradientMildSolutionData p u₀,
          D.T = δ ∧
          D.u = picardLimit p u₀ δ ∧
          GateCondition p D.M A₂ D.T ∧
          (∀ n, HasContinuousSlices D.T (picardIter p u₀ n)) ∧
          (∃ F : PicardConvFacts p u₀, F.T = δ)

If proving GateCondition p D.M A₂ D.T is awkward because D.M is hidden after packaging, also return D.M = Mcone, or build D in a let where rfl simplifies D.M.

Keep the old theorem as a projection, exactly as the current file already does for _with_data.

IntervalMildPicardConeData

4. MildLocalChi0 final instantiation

Replace the current call:

lean
obtain ⟨δ, _hδ, hD⟩ :=
  coneGradientMildSolutionData_exists p hχ0 hM hα_ge

IntervalDomainMildLocalChi0

with the strengthened cone theorem:

lean
obtain ⟨δ, A₂, hδ, hA₂, hD⟩ :=
  coneGradientMildSolutionData_exists_with_gate_data p hχ0 hM hα_ge

obtain ⟨D, hDT, hDu, hgateD, hcont_iter, hFacts_ex⟩ :=
  hD u₀ hu₀.admissible.2 hbound
    (positiveInitialDatum_nonneg hu₀)
    (positiveInitialDatum_pos_somewhere hu₀)

Then exact hDu remains available:

lean
have hDu' : D.u = picardLimit p u₀ D.T := by
  rw [hDT]
  exact hDu

No EqOn retype is needed.

Build the residual bundle with the returned cone data plus the Wdata assembly:

lean
let W : UniformWiring p u₀ D.M A₂ D.T :=
  uniformWiring_closure
    p hχ0 u₀ D.hM.le D.hT hT1 hgateD
    ... -- datum bounds, source meas/sup, source packages

Then:

lean
let Wdata :=
  wdata_all_of_wiring p u₀ W hA₂ bcfun hbsumW hagreeW hposW hubW

Finally:

lean
have R : PicardIterateResidualData p u₀ D :=
  Hres u₀ hu₀ D hDu'
-- or, if Hres is being constructed locally:
  HresProducer.picardIterateResidualData_of_cone hDu'
    hcont_iter F hFacts_T Wdata hsliceTC

The current capstone already routes Hres into the provider and then into MildLocalChi0; it expects exact hDu.

IntervalDomainThm11ChiZeroCoreP…

5. hDu EqOn fallback plan

If you still prefer restrictHorizon, use this retype:

lean
def PicardLimitEqOn
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∀ s, 0 < s → s ≤ D.T →
    D.u s = picardLimit p u₀ D.T s

Then edit:

IntervalDomainMildLocalChi0.lean
IntervalDomainThm11ChiZeroResidual.lean
IntervalDomainHresProducer.lean
IntervalDomainThm11ChiZeroCoreProvider.lean
IntervalDomainLedgerSweep.lean, if its exported theorem still quantifies hDu

Specific changes:

lean
-- hconv_of_residual
(hDuOn : PicardLimitEqOn p u₀ D)
...
have hslice : D.u s = picardLimit p u₀ D.T s :=
  hDuOn s hs hsT
rw [hslice]
lean
-- picardIterateResidualData_of_cone / hLcont_lim
have : picardLimit p u₀ D.T σ = D.u σ := by
  exact (hDuOn σ hσ hσT).symm

But you must also provide restricted versions of the residual side data:

lean
PicardConvFacts.restrict :
  F.T = D.T → 0 < T' → T' ≤ D.T →
  PicardConvFacts p u₀   -- with T := T'

HasContinuousSlices restrict:
  HasContinuousSlices D.T u →
  HasContinuousSlices T' u

Wdata restrict/rebuild:
  Wdata : ∀ a', 0 < a' → IterateWindowC2Data p u₀ a' D.T
  cannot be used directly as Wdata for T' unless you wrap/rebuild the fields.

This is why I recommend strengthening the cone instead.

6. Per-window representation triple threading

wdata_all_of_wiring wants this shape:

lean
bcfun : ℝ → ℕ → ℝ → ℕ → ℝ
hbsum : ∀ a', 0 < a' → a' ≤ T → ∀ n σ,
  a' ≤ σ → σ ≤ T → Summable ...
hagree : ∀ a', 0 < a' → a' ≤ T → ∀ n σ,
  a' ≤ σ → σ ≤ T → EqOn ...

IntervalPicardWdataAssembly

Use:

lean
bcfun := fun _a' n σ k =>
  IntervalPicardIterateRepresentation.iterateReprCoeff p u₀ n σ k

The a' argument is dummy. The window hypotheses give 0 < σ by 0 < a' and a' ≤ σ, which is exactly what the representation lemmas need.

IntervalPicardIterateRepresentation provides:

lean
iterateReprCoeff
hbsum_zero
hagree_zero
hbsum_succ
hagree_succ

with the expected homogeneous/restart split.

IntervalPicardIterateRepresenta…



IntervalPicardIterateRepresenta…



IntervalPicardIterateRepresenta…



IntervalPicardIterateRepresenta…

Shape mismatch to fix

hagree_succ currently requires:

lean
hu₀_cont : Continuous (intervalDomainLift u₀)

IntervalPicardIterateRepresenta…

That is the old false zero-extension continuity shape for positive boundary data. The zero case already uses the subtype spectral adapter and takes Continuous u₀.

IntervalPicardIterateRepresenta…

Add a subtype-continuity variant:

lean
theorem hagree_succ_of_subtypeCont
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (n : ℕ) {σ : ℝ}
    (hσ : 0 < σ)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k))
    (hL_cont : ∀ s, 0 < s → s ≤ σ →
      Continuous (logisticLifted p (picardIter p u₀ n s))) :
    Set.EqOn ...

It should route through the same subtype restart adapter pattern used elsewhere, not through Continuous (intervalDomainLift u₀).

Also ensure the source packages exported by IntervalPicardIterateSourcePackage match the exact uniformWiring_closure inputs:

lean
hsrc0 : ∀ n, DuhamelSourceTimeC1 ...
srcσ : ∀ n t, DuhamelSourceTimeC1 ...
hdecay : ∀ n t, 0 < t → t ≤ T → ∀ σ, 0 ≤ σ → ...
hσcont : ∀ n t k, Continuous ...

These are the exact arguments of uniformWiring_closure.

IntervalPicardUniformWiringClos…

For windows a' > T, wdata_all_of_wiring already handles the degenerate case vacuously, so no special representation data is needed there.

IntervalPicardWdataAssembly

7. Concrete edit list
IntervalPicardIterateUniform.lean or new IntervalPicardGateSolve.lean

Add:

lean
theorem GateCondition.mono ...
theorem exists_gate_solution ...

Use exists_gate_solution as the only numeric gate API needed by the cone theorem.

IntervalMildPicardConeData.lean

Add a strengthened theorem, preserving the old theorem as a projection:

lean
coneGradientMildSolutionData_exists_with_gate_data

Return:

lean
δ, A₂, hδ, hA₂, hgate

and the already-returned data:

lean
D.T = δ
D.u = picardLimit p u₀ δ
hcont_iterates
PicardConvFacts

Optionally return D.M = Mcone if simplifying hgate : GateCondition p D.M A₂ D.T needs it.

IntervalDomainMildLocalChi0.lean

At the cone instantiation, call the strengthened theorem instead of the old projection. Keep function-level hDu; do not use restrictHorizon.

IntervalPicardIterateRepresentation.lean

Add the subtype-continuity version of hagree_succ, or replace the old hagree_succ argument if all consumers can be moved safely.

IntervalPicardWdataAssembly.lean

No structural change needed. Feed:

lean
bcfun := fun _a' n σ k => iterateReprCoeff p u₀ n σ k

and supply hbsum/hagree by case-splitting on n, using the representation lemmas.

IntervalDomainHresProducer.lean

Keep restrictHorizon as a fallback utility, but do not route the final MildLocal instantiation through it. No necessary changes if cone strengthening is used.

IntervalDomainThm11ChiZeroCoreProvider.lean

No hDu retype needed. Ensure the Hres construction receives the exact hDu from the strengthened cone theorem, and ensure Wdata is built using the returned A₂ and hgate.

Trap list

Do not restrict the horizon unless you also retype hDu. Function equality is false after restriction; the file explicitly warns this.

IntervalDomainHresProducer

Do not assume the current cone δ satisfies the gate. It is chosen from contraction, ball, δ ≤ 1, and cone-smallness only.

IntervalMildPicardConeData

Do not thread A₂ as a public theorem parameter. It is an internal bootstrap constant; choose it via exists_gate_solution.

Do not miss the hagree_succ continuity wall. It currently asks for Continuous (intervalDomainLift u₀), which is the false zero-extension shape. Add a subtype-continuity variant.

IntervalPicardIterateRepresenta…

Do not rebuild Wdata with a shrinking horizon unless all matching horizons are changed. PicardConvFacts.T, Wdata, hsliceTC, and D.T must agree.

Use GateCondition.mono; do not reprove the gate after every min. Since T only appears as an upper bound in the quantifier, downward monotonicity is immediate.