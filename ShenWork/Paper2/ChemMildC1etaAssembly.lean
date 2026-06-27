/-
  ShenWork/Paper2/ChemMildC1etaAssembly.lean

  **P2-T11 step (ii) FINAL ASSEMBLY: `u(t₀,·) ∈ C^{1+η}` ⟹ Wiener ℓ¹.**

  The last mile of the χ₀<0 local-existence Hölder bootstrap.  All analytic bricks
  are committed (`ChemMildC1eta`, `ChemMildC1etaComm`, `ChemMildHolderBootstrap`,
  `HolderCosineDecay`); this file assembles them into the `C^{1+η}` slice and the
  Wiener-ℓ¹ feed.

  ## What is delivered
  * `chemFlux_Ctheta` — the chemotaxis flux `Q = u·g` (`g = V_x/(1+R)^β` the resolver
    multiplier) is `C^θ` on `[0,1]` with the explicit modulus `Cu·Hg + Hu·Cg`, via the
    committed product-Hölder algebra `holder_mul`.  The `u`-factor Hölder `Hu` comes
    from step (i) `mild_orderBox_positiveTime_holder`; the multiplier `g`-factor data
    `(Cg, Hg)` is the resolver-regularity interface (`V_x ∈ C^{1+θ} ⊂ C^θ`).
  * `DifferentiatedMildSlice` — the faithful Duhamel-differentiation BRIDGE package:
    the (genuinely missing) deriv-under-the-integral interchange for the three legs of
    `u_x(t₀)`, recorded as `HasDerivAt` of each leg plus their `C^η` Hölder data.  This
    is a concrete analytic interchange hypothesis, NOT the regularity conclusion — the
    `C^η` modulus of `u_x` and the Neumann boundary fact are PROVED/supplied separately.
  * `chemLeg_holder_of_brick4` (in `ChemMildC1eta`) +
    `differentiatedMildSlice_of_brick4_chem` — the chemotaxis-leg `C^η` Hölder is
    DISCHARGED, not assumed: brick 4 (Route B, `neumannHeatSecondDerivCthetaToCeta_routeB_Icc`)
    is applied per slice to the flux `Q(s)`, then integrated over `[0,t₀]` via the
    integral-Minkowski core `holder_of_duhamel_integral` (time integrand integrable by
    `brick4_time_integrand_integrable`).  The constructor builds the slice with
    `chem_holder` PROVED, leaving only the interchange representation carried.
  * `chemMild_positiveTime_C1eta_slice` — from a `DifferentiatedMildSlice` and the
    Neumann boundary package, the derivative `u_x(t₀,·)` is `η`-Hölder on `[0,1]` (and
    `u(t₀)` is differentiable, Neumann), via the triangle inequality on the three legs.
  * `chemMild_positiveTime_wiener_l1` — chains the `C^{1+η}` slice through the committed
    `holderCosineCoeff_summable`, delivering `Summable (|ĉₙ|)`, the P2-T11 `hQuant` feed.

  ## Why the differentiation is a hypothesis, not a theorem (audit honesty)
  Differentiating the mild equation `u(t) = S(t)u₀ − χ₀∫∂ₓS(t−s)Q + ∫S(t−s)L` once in
  `x` requires interchanging `deriv` with the singular Duhamel integrals
  (`∂ₓ ∫ = ∫ ∂ₓ`, dominated by the integrable `(t₀−s)^{−1+(θ−η)/2}` / `(t₀−s)^{−(1+η)/2}`
  kernels).  That Leibniz-under-the-integral interchange is a separate analytic theorem,
  not among the committed bricks.  Recording it as the `DifferentiatedMildSlice`
  hypothesis (the derivative EXISTS and EQUALS the differentiated representation) is the
  honest bridge: everything downstream of the representation — the `C^η` Hölder estimate
  and the Wiener feed — is then PROVED here from the committed leg bounds.  The boundary
  Neumann fact `u_x(t₀,0)=u_x(t₀,1)=0` is the PDE no-flux invariant (a property of the
  solution, not a termwise consequence of `∂ₓₓS(σ)Q`), supplied as `NeumannBoundarySlice`.

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.Paper2.ChemMildC1eta
import ShenWork.Paper2.ChemMildInterchange
import ShenWork.Paper2.IntervalMildRegularityBootstrap
import ShenWork.Paper2.IntervalDuhamelSpatialLeibniz
import ShenWork.PDE.IntervalSemigroupNeumann
import ShenWork.Wiener.EWA.HolderCosineDecayDiffOn

open MeasureTheory
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalDomainRegularityBootstrap (unitIntervalCosineHeatSecondValue)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalMildRegularityBootstrap
  (HasRestartCosineRepresentations
    gradientMild_closedC2_endpointDerivs_of_restartCosineRepresentations)
open ShenWork.Paper2 (neumannHeatGradient_Linf_to_Ctheta secondDerivSmoothingConst
  gradSmoothingConst)

namespace ShenWork.Paper2

noncomputable section

/-! ## `chemFlux_Ctheta` — the chemotaxis flux `Q = u·g ∈ C^θ` (product algebra) -/

/-- **`chemFlux_Ctheta` — the chemotaxis flux is `C^θ`.**  Writing the lifted flux as a
binary product `Q = f·g` of the lifted solution factor `f` (Hölder modulus `Hf` from
step (i), sup bound `Cf = M`) and the resolver multiplier `g = V_x/(1+R)^β` (Hölder
modulus `Hg`, sup bound `Cg` from the resolver `C¹` regularity), the committed product
algebra `holder_mul` gives the `θ`-Hölder modulus

  `|Q(a) − Q(b)| ≤ (Cf·Hg + Hf·Cg)·|a−b|^θ`,   `a,b ∈ [0,1]`.

This is the brick-5 product algebra specialised to `Q`; the two factor moduli are the
clean resolver-regularity / step-(i) interface (the prompt's `[u]_θ + V_x∈C^{1+θ}`). -/
theorem chemFlux_Ctheta {θ Cf Cg Hf Hg : ℝ} {f g : ℝ → ℝ}
    (hCf : 0 ≤ Cf) (hHf : 0 ≤ Hf)
    (hf_bdd : ∀ y ∈ Set.Icc (0:ℝ) 1, |f y| ≤ Cf)
    (hg_bdd : ∀ y ∈ Set.Icc (0:ℝ) 1, |g y| ≤ Cg)
    (hf : ∀ a b, a ∈ Set.Icc (0:ℝ) 1 → b ∈ Set.Icc (0:ℝ) 1 → |f a - f b| ≤ Hf * |a - b| ^ θ)
    (hg : ∀ a b, a ∈ Set.Icc (0:ℝ) 1 → b ∈ Set.Icc (0:ℝ) 1 → |g a - g b| ≤ Hg * |a - b| ^ θ)
    (a b : ℝ) (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1) :
    |(f a * g a) - (f b * g b)| ≤ (Cf * Hg + Hf * Cg) * |a - b| ^ θ :=
  holder_mul hCf hHf hf_bdd hg_bdd hf hg a b ha hb

/-! ## The faithful Duhamel-differentiation bridge package -/

/-- **`DifferentiatedMildSlice` — the deriv-under-the-integral BRIDGE.**

The (genuinely missing) Leibniz interchange for the spatial derivative of the mild
slice `w = u(t₀,·)`, recorded faithfully as data, NOT as the regularity conclusion:

* `hasDeriv` — `w` is differentiable on `ℝ` with derivative `Dw` (the differentiated
  mild representation; this is exactly the `∂ₓ ∫ = ∫ ∂ₓ` interchange, a separate
  analytic theorem).
* `init_holder` / `chem_holder` / `react_holder` — the three legs of `Dw` are each
  `η`-Hölder on `ℝ` with the explicit constants `Ainit, Achem, Areact`
  (`Ainit` = gradient Hölder of `∂ₓS(δ)u(τ)`, GLOBAL via `gradLeg_holder_global`;
  `Achem` = brick-4 second-derivative Schauder integral over `[τ,t₀]`;
  `Areact` = gradient Hölder of `∫∂ₓS(t₀−s)L`).  Global `x,y` is what the downstream
  `holderCosineCoeff_summable` consumes (its cosine integral probes `[0,1]`).
* `deriv_split` — the pointwise leg decomposition of `Dw` on `ℝ`:
  `Dw x = init x − χ₀·chem x + react x`.

The `Aᵢ ≥ 0` side conditions keep the package non-vacuous (real Hölder constants).
None of the fields is the `C^η`-of-`Dw` conclusion or a Neumann-zero claim — those are
proved / supplied separately. -/
structure DifferentiatedMildSlice (χ₀ η : ℝ) (w Dw : ℝ → ℝ)
    (initLeg chemLeg reactLeg : ℝ → ℝ) (Ainit Achem Areact : ℝ) : Prop where
  /-- `w` is differentiable with derivative `Dw` (the Duhamel-Leibniz interchange). -/
  hasDeriv : ∀ x : ℝ, HasDerivAt w (Dw x) x
  /-- The three-leg decomposition of `Dw` on `ℝ` (the differentiated mild
  representation; each leg is defined on all of `ℝ`). -/
  deriv_split : ∀ x : ℝ, Dw x = initLeg x - χ₀ * chemLeg x + reactLeg x
  /-- Nonneg leg constants (non-vacuity). -/
  Ainit_nn : 0 ≤ Ainit
  Achem_nn : 0 ≤ Achem
  Areact_nn : 0 ≤ Areact
  /-- Initial-leg `η`-Hölder on `ℝ`: `[∂ₓS(δ)u(τ)]_η ≤ Ainit` (the gradient smoothing
  lemma `neumannHeatGradient_Linf_to_Ctheta` is genuinely global in `x,y`). -/
  init_holder : ∀ x y : ℝ, |initLeg x - initLeg y| ≤ Ainit * |x - y| ^ η
  /-- Chemotaxis-leg `η`-Hölder on `ℝ`: `[∫∂ₓₓS(t₀−s)Q]_η ≤ Achem` (brick-4 Schauder
  integral over `[0,t₀]` of the second-derivative estimate).  NOT carried in practice:
  the constructor `differentiatedMildSlice_of_brick4_chem` DISCHARGES this field from
  `chemLeg_holder_of_brick4` (bricks 1–4 applied to the integrated clamped Duhamel leg). -/
  chem_holder : ∀ x y : ℝ, |chemLeg x - chemLeg y| ≤ Achem * |x - y| ^ η
  /-- Reaction-leg `η`-Hölder on `ℝ`: `[∫∂ₓS(t₀−s)L]_η ≤ Areact` (global gradient
  smoothing). -/
  react_holder : ∀ x y : ℝ, |reactLeg x - reactLeg y| ≤ Areact * |x - y| ^ η

/-- **`NeumannBoundarySlice` — the no-flux boundary invariant.**  The mild solution's
spatial derivative vanishes at the endpoints, `Dw 0 = Dw 1 = 0` (homogeneous Neumann
BC of the chemotaxis–logistic PDE).  This is a genuine property of the solution, NOT a
termwise consequence of the chemotaxis leg, so it is supplied as a separate package. -/
structure NeumannBoundarySlice (Dw : ℝ → ℝ) : Prop where
  deriv_zero : Dw 0 = 0
  deriv_one : Dw 1 = 0

/-! ## Phase 1 — initial/reaction Leibniz and Neumann discharges -/

/-- The value-form initial heat leg `S(t)u₀`. -/
noncomputable def initialValueLeg (t : ℝ) (u₀ : ℝ → ℝ) : ℝ → ℝ :=
  fun x => intervalFullSemigroupOperator t u₀ x

/-- The differentiated initial heat leg `∂ₓS(t)u₀`. -/
noncomputable def initialDerivLeg (t : ℝ) (u₀ : ℝ → ℝ) : ℝ → ℝ :=
  fun x => deriv (fun z : ℝ => intervalFullSemigroupOperator t u₀ z) x

/-- The value-form reaction Duhamel leg `∫₀ᵗ S(t-s)L(s) ds`. -/
noncomputable def reactionValueLeg (t : ℝ) (L : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun x => ∫ s in (0 : ℝ)..t, intervalFullSemigroupOperator (t - s) (L s) x

/-- The differentiated reaction leg `∫₀ᵗ ∂ₓS(t-s)L(s) ds`. -/
noncomputable def reactionDerivLeg (t : ℝ) (L : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun x => ∫ s in (0 : ℝ)..t,
    deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (L s) z) x

/-- The Phase-2 residual: the chemotaxis value leg still has to be differentiated.
This package deliberately contains no endpoint Neumann claim for the second-derivative
chemotaxis leg: `∂ₓₓS(σ)Q` does not vanish at the endpoints in general. -/
structure ChemotaxisLegPhase2Residual
    (chemValue chemDeriv : ℝ → ℝ) : Prop where
  hasDeriv : ∀ x : ℝ, HasDerivAt chemValue (chemDeriv x) x

/-- The precise remaining Phase-2 residual after applying the committed interior
chemotaxis Leibniz theorem: only the off-interior `HasDerivAt` extension is external
data.  Endpoint no-flux is a solution-level invariant of `w`, not a per-leg fact for
`chemDeriv = ∂ₓ chemValue`. -/
structure ChemotaxisLegOffInteriorResidual
    (chemValue chemDeriv : ℝ → ℝ) : Prop where
  hasDeriv_offInterior : ∀ x : ℝ, x ∉ Set.Ioo (0 : ℝ) 1 →
    HasDerivAt chemValue (chemDeriv x) x

/-- Phase 2, chemotaxis leg: the committed dominated-Leibniz theorem discharges the
interior `HasDerivAt` field from Q-data. -/
theorem chemotaxisLeg_interior_hasDerivAt
    {t₀ θ CQ HQ : ℝ} {Q : ℝ → ℝ → ℝ}
    (ht₀ : 0 < t₀) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hHQ_nn : 0 ≤ HQ)
    (hQmeas : Measurable (Function.uncurry Q))
    (hQint : ∀ s, Integrable (Q s) (ShenWork.IntervalDomain.intervalMeasure 1))
    (hCQ_nn : 0 ≤ CQ) (hQbdd : ∀ s y, |Q s y| ≤ CQ)
    (hQholder : ∀ s ∈ Set.Ioo (0 : ℝ) t₀, ∀ a b,
      a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |Q s a - Q s b| ≤ HQ * |a - b| ^ θ)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (chemLitLeg t₀ Q) (chemLitLeg₂ t₀ Q x₀) x₀ :=
  chemLeg_interior_hasDerivAt ht₀ hθ0 hθ1 hHQ_nn hQmeas hQint
    hCQ_nn hQbdd hQholder hx₀

/-- Phase 2, chemotaxis leg: `deriv` form of the committed interior interchange. -/
theorem chemotaxisLeg_interior_deriv_eq
    {t₀ θ CQ HQ : ℝ} {Q : ℝ → ℝ → ℝ}
    (ht₀ : 0 < t₀) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hHQ_nn : 0 ≤ HQ)
    (hQmeas : Measurable (Function.uncurry Q))
    (hQint : ∀ s, Integrable (Q s) (ShenWork.IntervalDomain.intervalMeasure 1))
    (hCQ_nn : 0 ≤ CQ) (hQbdd : ∀ s y, |Q s y| ≤ CQ)
    (hQholder : ∀ s ∈ Set.Ioo (0 : ℝ) t₀, ∀ a b,
      a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |Q s a - Q s b| ≤ HQ * |a - b| ^ θ)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (chemLitLeg t₀ Q) x₀ = chemLitLeg₂ t₀ Q x₀ :=
  chemLeg_interior_deriv_eq ht₀ hθ0 hθ1 hHQ_nn hQmeas hQint
    hCQ_nn hQbdd hQholder hx₀

/-- Phase 2 partial discharge of `ChemotaxisLegPhase2Residual`: Q-data proves the
interior field; only off-interior differentiability remains. -/
theorem chemotaxisLegPhase2Residual_of_Qdata_offInterior
    {t₀ θ CQ HQ : ℝ} {Q : ℝ → ℝ → ℝ}
    (ht₀ : 0 < t₀) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hHQ_nn : 0 ≤ HQ)
    (hQmeas : Measurable (Function.uncurry Q))
    (hQint : ∀ s, Integrable (Q s) (ShenWork.IntervalDomain.intervalMeasure 1))
    (hCQ_nn : 0 ≤ CQ) (hQbdd : ∀ s y, |Q s y| ≤ CQ)
    (hQholder : ∀ s ∈ Set.Ioo (0 : ℝ) t₀, ∀ a b,
      a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |Q s a - Q s b| ≤ HQ * |a - b| ^ θ)
    (hOff : ChemotaxisLegOffInteriorResidual (chemLitLeg t₀ Q) (chemLitLeg₂ t₀ Q)) :
    ChemotaxisLegPhase2Residual (chemLitLeg t₀ Q) (chemLitLeg₂ t₀ Q) := by
  refine ⟨?_⟩
  intro x
  by_cases hx : x ∈ Set.Ioo (0 : ℝ) 1
  · exact chemotaxisLeg_interior_hasDerivAt ht₀ hθ0 hθ1 hHQ_nn hQmeas
      hQint hCQ_nn hQbdd hQholder hx
  · exact hOff.hasDeriv_offInterior x hx

/-- Phase 1, initial leg: `S(t)u₀` has derivative `∂ₓS(t)u₀`. -/
theorem initialValueLeg_hasDerivAt
    {t : ℝ} (ht : 0 < t) {u₀ : ℝ → ℝ}
    (hu₀_meas : AEStronglyMeasurable u₀
      (ShenWork.IntervalDomain.intervalMeasure 1))
    {Cu₀ : ℝ} (hu₀_bdd : ∀ y, |u₀ y| ≤ Cu₀) (x : ℝ) :
    HasDerivAt (initialValueLeg t u₀) (initialDerivLeg t u₀ x) x := by
  unfold initialValueLeg initialDerivLeg
  exact ShenWork.IntervalPicardG1Split.homogeneous_hasDerivAt
    ht hu₀_meas hu₀_bdd x

/-- Phase 1, initial leg: the `deriv` API form of
`initialValueLeg_hasDerivAt`. -/
theorem initialValueLeg_deriv_eq
    {t : ℝ} (ht : 0 < t) {u₀ : ℝ → ℝ}
    (hu₀_meas : AEStronglyMeasurable u₀
      (ShenWork.IntervalDomain.intervalMeasure 1))
    {Cu₀ : ℝ} (hu₀_bdd : ∀ y, |u₀ y| ≤ Cu₀) (x : ℝ) :
    deriv (initialValueLeg t u₀) x = initialDerivLeg t u₀ x :=
  (initialValueLeg_hasDerivAt ht hu₀_meas hu₀_bdd x).deriv

/-- Phase 1, reaction leg: the value Duhamel leg has derivative
`∫₀ᵗ ∂ₓS(t-s)L(s) ds`. -/
theorem reactionValueLeg_hasDerivAt
    {t : ℝ} (ht : 0 < t) {L : ℝ → ℝ → ℝ}
    (hL_meas : Measurable (Function.uncurry L))
    {CL : ℝ} (hCL_nn : 0 ≤ CL) (hL_bdd : ∀ s y, |L s y| ≤ CL)
    (x : ℝ) :
    HasDerivAt (reactionValueLeg t L) (reactionDerivLeg t L x) x := by
  unfold reactionValueLeg reactionDerivLeg
  have hL_int : ∀ s, Integrable (L s) (ShenWork.IntervalDomain.intervalMeasure 1) :=
    ShenWork.IntervalDuhamelSpatialLeibniz.duhamel_source_integrable
      hL_meas hL_bdd
  exact ShenWork.IntervalDuhamelSpatialLeibniz.intervalFullDuhamel_hasDerivAt_fst
    ht hL_meas hL_int hCL_nn hL_bdd x

/-- Phase 1, reaction leg: the `deriv` API form of the Duhamel spatial Leibniz rule. -/
theorem reactionValueLeg_deriv_eq
    {t : ℝ} (ht : 0 < t) {L : ℝ → ℝ → ℝ}
    (hL_meas : Measurable (Function.uncurry L))
    {CL : ℝ} (hCL_nn : 0 ≤ CL) (hL_bdd : ∀ s y, |L s y| ≤ CL)
    (x : ℝ) :
    deriv (reactionValueLeg t L) x = reactionDerivLeg t L x := by
  unfold reactionValueLeg reactionDerivLeg
  have hL_int : ∀ s, Integrable (L s) (ShenWork.IntervalDomain.intervalMeasure 1) :=
    ShenWork.IntervalDuhamelSpatialLeibniz.duhamel_source_integrable
      hL_meas hL_bdd
  exact ShenWork.IntervalDuhamelSpatialLeibniz.intervalFullDuhamel_deriv_eq_integral_deriv
    ht hL_meas hL_int hCL_nn hL_bdd x

/-- Phase 1, initial leg: homogeneous Neumann boundary values. -/
theorem initialDerivLeg_neumann
    {t : ℝ} (ht : 0 < t) {u₀ : ℝ → ℝ} (hu₀_cont : Continuous u₀)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs u₀ n| ≤ M) :
    NeumannBoundarySlice (initialDerivLeg t u₀) := by
  constructor
  · unfold initialDerivLeg
    exact ShenWork.IntervalSemigroupNeumann.intervalFullSemigroupOperator_neumann_at_zero
      ht hu₀_cont hM
  · unfold initialDerivLeg
    exact ShenWork.IntervalSemigroupNeumann.intervalFullSemigroupOperator_neumann_at_one
      ht hu₀_cont hM

/-- Phase 1, reaction leg: value-Duhamel homogeneous Neumann boundary values. -/
theorem reactionDerivLeg_neumann
    {t : ℝ} (ht : 0 < t) {L : ℝ → ℝ → ℝ}
    (hL_meas : Measurable (Function.uncurry L))
    (hL_cont : ∀ s, Continuous (L s))
    {CL : ℝ} (hCL_nn : 0 ≤ CL) (hL_bdd : ∀ s y, |L s y| ≤ CL)
    {M : ℝ} (hM : ∀ s n, |cosineCoeffs (L s) n| ≤ M) :
    NeumannBoundarySlice (reactionDerivLeg t L) := by
  constructor
  · unfold reactionDerivLeg
    have hL_int : ∀ s, Integrable (L s) (ShenWork.IntervalDomain.intervalMeasure 1) :=
      ShenWork.IntervalDuhamelSpatialLeibniz.duhamel_source_integrable
        hL_meas hL_bdd
    have hLeibniz :=
      ShenWork.IntervalDuhamelSpatialLeibniz.intervalFullDuhamel_hasDerivAt_fst
        ht hL_meas hL_int hCL_nn hL_bdd (0 : ℝ)
    have hNeu :=
      ShenWork.IntervalSemigroupNeumann.valueDuhamel_neumann_at_zero_of_hasDerivAt
        ht hL_cont hM hLeibniz
    rw [hLeibniz.deriv] at hNeu
    exact hNeu
  · unfold reactionDerivLeg
    have hL_int : ∀ s, Integrable (L s) (ShenWork.IntervalDomain.intervalMeasure 1) :=
      ShenWork.IntervalDuhamelSpatialLeibniz.duhamel_source_integrable
        hL_meas hL_bdd
    have hLeibniz :=
      ShenWork.IntervalDuhamelSpatialLeibniz.intervalFullDuhamel_hasDerivAt_fst
        ht hL_meas hL_int hCL_nn hL_bdd (1 : ℝ)
    have hNeu :=
      ShenWork.IntervalSemigroupNeumann.valueDuhamel_neumann_at_one_of_hasDerivAt
        ht hL_cont hM hLeibniz
    rw [hLeibniz.deriv] at hNeu
    exact hNeu

/-- Phase 1, total representation: initial and reaction differentiation are
discharged; the only remaining derivative input is the chemotaxis-leg residual. -/
theorem differentiatedMildSlice_of_phase1_chemResidual
    {χ₀ t η Ainit Achem Areact : ℝ}
    {u₀ : ℝ → ℝ} {L : ℝ → ℝ → ℝ} {w chemValue chemDeriv : ℝ → ℝ}
    (ht : 0 < t)
    (hu₀_meas : AEStronglyMeasurable u₀
      (ShenWork.IntervalDomain.intervalMeasure 1))
    {Cu₀ CL : ℝ} (hu₀_bdd : ∀ y, |u₀ y| ≤ Cu₀)
    (hL_meas : Measurable (Function.uncurry L))
    (hCL_nn : 0 ≤ CL) (hL_bdd : ∀ s y, |L s y| ≤ CL)
    (hChem : ChemotaxisLegPhase2Residual chemValue chemDeriv)
    (hw_eq : ∀ x : ℝ,
      w x = initialValueLeg t u₀ x - χ₀ * chemValue x + reactionValueLeg t L x)
    (hAinit_nn : 0 ≤ Ainit) (hAchem_nn : 0 ≤ Achem)
    (hAreact_nn : 0 ≤ Areact)
    (init_holder : ∀ x y : ℝ,
      |initialDerivLeg t u₀ x - initialDerivLeg t u₀ y| ≤ Ainit * |x - y| ^ η)
    (chem_holder : ∀ x y : ℝ,
      |chemDeriv x - chemDeriv y| ≤ Achem * |x - y| ^ η)
    (react_holder : ∀ x y : ℝ,
      |reactionDerivLeg t L x - reactionDerivLeg t L y| ≤ Areact * |x - y| ^ η) :
    DifferentiatedMildSlice χ₀ η w
      (fun x => initialDerivLeg t u₀ x - χ₀ * chemDeriv x + reactionDerivLeg t L x)
      (initialDerivLeg t u₀) chemDeriv (reactionDerivLeg t L)
      Ainit Achem Areact := by
  refine
    { hasDeriv := ?_
      deriv_split := ?_
      Ainit_nn := hAinit_nn
      Achem_nn := hAchem_nn
      Areact_nn := hAreact_nn
      init_holder := init_holder
      chem_holder := chem_holder
      react_holder := react_holder }
  · intro x
    have hInit := initialValueLeg_hasDerivAt ht hu₀_meas hu₀_bdd x
    have hReact := reactionValueLeg_hasDerivAt ht hL_meas hCL_nn hL_bdd x
    have hChemX := hChem.hasDeriv x
    have hsum : HasDerivAt
        (fun z : ℝ =>
          initialValueLeg t u₀ z - χ₀ * chemValue z + reactionValueLeg t L z)
        (initialDerivLeg t u₀ x - χ₀ * chemDeriv x + reactionDerivLeg t L x)
        x := by
      simpa using (hInit.sub (hChemX.const_mul χ₀)).add hReact
    exact hsum.congr_of_eventuallyEq
      (Filter.Eventually.of_forall hw_eq)
  · intro x
    rfl

/-- Aggregate Neumann from the intrinsic endpoint derivative values of the slice.
This is the only correct assembly route for `Dw`: it uses `deriv w 0 = deriv w 1 = 0`,
then transports through the already-built derivative representation `deriv w = Dw`. -/
theorem neumannBoundarySlice_of_intrinsic_endpointDerivs
    {w Dw : ℝ → ℝ}
    (hDeriv : ∀ x : ℝ, HasDerivAt w (Dw x) x)
    (h0 : deriv w 0 = 0) (h1 : deriv w 1 = 0) :
    NeumannBoundarySlice Dw := by
  constructor
  · rw [← (hDeriv 0).deriv]
    exact h0
  · rw [← (hDeriv 1).deriv]
    exact h1

/-- Solution-level intrinsic no-flux, discharged from the committed restart-cosine
regularity package.  The proof never uses endpoint values of the chemotaxis
second-derivative leg. -/
theorem neumannBoundarySlice_of_restartCosineRepresentations
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (Dsol : GradientMildSolutionData p u₀)
    (H : HasRestartCosineRepresentations Dsol.T Dsol.u)
    {t : ℝ} (ht : 0 < t) (htT : t < Dsol.T)
    {w Dw : ℝ → ℝ}
    (hDeriv : ∀ x : ℝ, HasDerivAt w (Dw x) x)
    (hw_eq : ∀ x : ℝ, w x = intervalDomainLift (Dsol.u t) x) :
    NeumannBoundarySlice Dw := by
  have hEnd :=
    gradientMild_closedC2_endpointDerivs_of_restartCosineRepresentations Dsol H t ht htT
  have hw_fun : w = intervalDomainLift (Dsol.u t) := funext hw_eq
  exact neumannBoundarySlice_of_intrinsic_endpointDerivs hDeriv
    (by rw [hw_fun]; exact hEnd.2.1)
    (by rw [hw_fun]; exact hEnd.2.2)

/-- Phase 2 wiring for the differentiated slice.  The old full
`ChemotaxisLegPhase2Residual` is built internally: Q-data discharges the interior
Leibniz field, while `hOff` records the precise off-interior remainder. -/
theorem differentiatedMildSlice_of_phase2_Qdata_offInterior
    {χ₀ t θ η CQ HQ Ainit Achem Areact : ℝ}
    {u₀ : ℝ → ℝ} {L Q : ℝ → ℝ → ℝ} {w : ℝ → ℝ}
    (ht : 0 < t) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hHQ_nn : 0 ≤ HQ)
    (hu₀_meas : AEStronglyMeasurable u₀
      (ShenWork.IntervalDomain.intervalMeasure 1))
    {Cu₀ CL : ℝ} (hu₀_bdd : ∀ y, |u₀ y| ≤ Cu₀)
    (hL_meas : Measurable (Function.uncurry L))
    (hCL_nn : 0 ≤ CL) (hL_bdd : ∀ s y, |L s y| ≤ CL)
    (hQmeas : Measurable (Function.uncurry Q))
    (hQint : ∀ s, Integrable (Q s) (ShenWork.IntervalDomain.intervalMeasure 1))
    (hCQ_nn : 0 ≤ CQ) (hQbdd : ∀ s y, |Q s y| ≤ CQ)
    (hQholder : ∀ s ∈ Set.Ioo (0 : ℝ) t, ∀ a b,
      a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |Q s a - Q s b| ≤ HQ * |a - b| ^ θ)
    (hOff : ChemotaxisLegOffInteriorResidual (chemLitLeg t Q) (chemLitLeg₂ t Q))
    (hw_eq : ∀ x : ℝ,
      w x = initialValueLeg t u₀ x - χ₀ * chemLitLeg t Q x + reactionValueLeg t L x)
    (hAinit_nn : 0 ≤ Ainit) (hAchem_nn : 0 ≤ Achem)
    (hAreact_nn : 0 ≤ Areact)
    (init_holder : ∀ x y : ℝ,
      |initialDerivLeg t u₀ x - initialDerivLeg t u₀ y| ≤ Ainit * |x - y| ^ η)
    (chem_holder : ∀ x y : ℝ,
      |chemLitLeg₂ t Q x - chemLitLeg₂ t Q y| ≤ Achem * |x - y| ^ η)
    (react_holder : ∀ x y : ℝ,
      |reactionDerivLeg t L x - reactionDerivLeg t L y| ≤ Areact * |x - y| ^ η) :
    DifferentiatedMildSlice χ₀ η w
      (fun x => initialDerivLeg t u₀ x - χ₀ * chemLitLeg₂ t Q x + reactionDerivLeg t L x)
      (initialDerivLeg t u₀) (chemLitLeg₂ t Q) (reactionDerivLeg t L)
      Ainit Achem Areact := by
  have hChem :=
    chemotaxisLegPhase2Residual_of_Qdata_offInterior ht hθ0 hθ1 hHQ_nn
      hQmeas hQint hCQ_nn hQbdd hQholder hOff
  exact differentiatedMildSlice_of_phase1_chemResidual ht hu₀_meas hu₀_bdd
    hL_meas hCL_nn hL_bdd hChem hw_eq hAinit_nn hAchem_nn hAreact_nn
    init_holder chem_holder react_holder

/-! ## Grounding the bridge: the gradient legs ARE globally `η`-Hölder (satisfiability) -/

/-- **Gradient-leg Hölder is committed (init/reaction legs).**  A first `x`-derivative
of a heat-semigroup value `∂ₓS(δ)f` is globally `η`-Hölder with the committed constant —
exactly the shape the bridge's `init_holder` / `react_holder` fields require.  This is
the committed global gradient smoothing `neumannHeatGradient_Linf_to_Ctheta`
(`intervalNeumannHeatSemigroup = intervalFullSemigroupOperator`), so the bridge's
gradient-leg Hölder fields are NON-VACUOUSLY realizable from a committed brick. -/
theorem gradLeg_holder_global {δ η : ℝ} (hδ : 0 < δ) (hη0 : 0 < η) (hη1 : η < 1)
    {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (ShenWork.IntervalDomain.intervalMeasure 1))
    {Cf : ℝ} (hf : ∀ y, |f y| ≤ Cf) (x y : ℝ) :
    |deriv (fun z : ℝ =>
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator δ f z) x
      - deriv (fun z : ℝ =>
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator δ f z) y|
      ≤ ((2 : ℝ) ^ (1 - η) * (secondDerivSmoothingConst ^ η * gradSmoothingConst ^ (1 - η))
          * δ ^ (-((1 + η) / 2) : ℝ) * Cf) * |x - y| ^ η := by
  have h := neumannHeatGradient_Linf_to_Ctheta hδ hη0 hη1 hf_meas hf x y
  -- `intervalNeumannHeatSemigroup = intervalFullSemigroupOperator` definitionally.
  simpa using h

/-! ## Discharging the chemotaxis leg: bricks 1–4 applied to the integrated Duhamel -/

/-- The concrete clamped chemotaxis Duhamel leg integrand built from the per-slice flux
family `Q`: the spectral second value `∂ₓₓS(t₀−s)Q(s)` evaluated at the clamped point. -/
noncomputable def chemDuhamelLeg (t₀ : ℝ) (Q : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun x => ∫ s in (0:ℝ)..t₀,
    unitIntervalCosineHeatSecondValue (t₀ - s) (cosineCoeffs (Q s)) (clamp01 x)

/-- The brick-4 chemotaxis Hölder CONSTANT: `Achem = ∫₀^{t₀} brick4Const·(t₀−s)^{−1+(θ−η)/2}·HQ`. -/
noncomputable def chemDuhamelConst (t₀ θ η HQ : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..t₀, brick4Const θ η * (t₀ - s) ^ (-1 + (θ - η) / 2 : ℝ) * HQ

/-- **`differentiatedMildSlice_of_brick4_chem` — the slice constructor that PROVES the
chemotaxis Hölder.**  Where the bare `DifferentiatedMildSlice` would CARRY `chem_holder`
as a free field, this constructor DISCHARGES it: the chemotaxis leg is the concrete
clamped Duhamel integral `chemDuhamelLeg t₀ Q`, and its `η`-Hölder bound with constant
`chemDuhamelConst t₀ θ η HQ` is PROVED by `chemLeg_holder_of_brick4` (bricks 1–4 actually
applied to the integrated Duhamel, then integral-Minkowski over `[0,t₀]`).

The remaining inputs are exactly the honest bridge data: the deriv-under-the-integral
INTERCHANGE (`hasDeriv` + `deriv_split` — the REPRESENTATION, not a regularity conclusion)
and the GROUNDED gradient legs (`init_holder`/`react_holder`, realizable from the committed
`gradLeg_holder_global`).  `chem_holder` is NO LONGER assumed. -/
theorem differentiatedMildSlice_of_brick4_chem
    {χ₀ t₀ θ η M CQ HQ Ainit Areact : ℝ} {Q : ℝ → ℝ → ℝ} {w Dw initLeg reactLeg : ℝ → ℝ}
    (ht₀ : 0 < t₀) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hη0 : 0 < η) (hη1 : η < 1) (hθη : η < θ)
    (hHQ_nn : 0 ≤ HQ) (hAinit_nn : 0 ≤ Ainit) (hAreact_nn : 0 ≤ Areact)
    (hQcont : ∀ s ∈ Set.Ioo (0:ℝ) t₀, Continuous (Q s))
    (hQcoeff : ∀ s ∈ Set.Ioo (0:ℝ) t₀, ∀ n, |cosineCoeffs (Q s) n| ≤ M)
    (hQbdd : ∀ s ∈ Set.Ioo (0:ℝ) t₀, ∀ y, |Q s y| ≤ CQ)
    (hQholder : ∀ s ∈ Set.Ioo (0:ℝ) t₀, ∀ a b, a ∈ Set.Icc (0:ℝ) 1 →
      b ∈ Set.Icc (0:ℝ) 1 → |Q s a - Q s b| ≤ HQ * |a - b| ^ θ)
    (hleg_int : ∀ x : ℝ, IntervalIntegrable
      (fun s => unitIntervalCosineHeatSecondValue (t₀ - s) (cosineCoeffs (Q s)) (clamp01 x))
      volume 0 t₀)
    (hasDeriv : ∀ x : ℝ, HasDerivAt w (Dw x) x)
    (deriv_split : ∀ x : ℝ, Dw x = initLeg x - χ₀ * chemDuhamelLeg t₀ Q x + reactLeg x)
    (init_holder : ∀ x y : ℝ, |initLeg x - initLeg y| ≤ Ainit * |x - y| ^ η)
    (react_holder : ∀ x y : ℝ, |reactLeg x - reactLeg y| ≤ Areact * |x - y| ^ η) :
    DifferentiatedMildSlice χ₀ η w Dw initLeg (chemDuhamelLeg t₀ Q) reactLeg
      Ainit (chemDuhamelConst t₀ θ η HQ) Areact := by
  -- the chemotaxis Hölder constant is nonneg (integral of a nonneg integrand on [0,t₀])
  have hAchem_nn : 0 ≤ chemDuhamelConst t₀ θ η HQ := by
    unfold chemDuhamelConst
    refine intervalIntegral.integral_nonneg ht₀.le (fun s hs => ?_)
    have hts : (0:ℝ) ≤ t₀ - s := by have := hs.2; linarith
    have hb := brick4Const_nonneg θ η
    have hr : (0:ℝ) ≤ (t₀ - s) ^ (-1 + (θ - η) / 2 : ℝ) := Real.rpow_nonneg hts _
    positivity
  -- the chemotaxis Hölder field, DISCHARGED via brick 4 + integral-Minkowski
  have hChem : ∀ x y : ℝ,
      |chemDuhamelLeg t₀ Q x - chemDuhamelLeg t₀ Q y|
        ≤ chemDuhamelConst t₀ θ η HQ * |x - y| ^ η := by
    intro x y
    exact chemLeg_holder_of_brick4 ht₀ hθ0 hθ1 hη0 hη1 hθη hHQ_nn hQcont hQcoeff hQbdd
      hQholder x y (hleg_int x) (hleg_int y)
  exact
    { hasDeriv := hasDeriv
      deriv_split := deriv_split
      Ainit_nn := hAinit_nn
      Achem_nn := hAchem_nn
      Areact_nn := hAreact_nn
      init_holder := init_holder
      chem_holder := hChem
      react_holder := react_holder }

/-! ## The `C^{1+η}` slice: `u_x(t₀,·) ∈ C^η`, differentiable, Neumann -/

/-- **`chemMild_positiveTime_C1eta_slice` — the `C^{1+η}` slice.**

From the Duhamel-differentiation bridge `DifferentiatedMildSlice` and the no-flux
boundary package `NeumannBoundarySlice`, the mild slice `w = u(t₀,·)` is `C^{1+η}` on
`[0,1]` in the Wiener-ready shape:

* `w` is differentiable on `ℝ`;
* `deriv w 0 = 0 ∧ deriv w 1 = 0` (Neumann);
* `[deriv w]_η ≤ Ainit + |χ₀|·Achem + Areact` on all of `ℝ`.

PROOF: differentiability and `deriv w = Dw` from `hasDeriv`; Neumann from the boundary
package transported through `deriv w = Dw`; the `η`-Hölder of `Dw` from the three-leg
decomposition + triangle inequality on the per-leg Hölder estimates
(`init_holder + |χ₀|·chem_holder + react_holder`).  Nothing here is assumed about the
regularity conclusion — only the differentiated representation (the interchange) and the
PDE boundary invariant are inputs. -/
theorem chemMild_positiveTime_C1eta_slice {χ₀ η : ℝ} (_hη0 : 0 < η)
    {w Dw initLeg chemLeg reactLeg : ℝ → ℝ} {Ainit Achem Areact : ℝ}
    (D : DifferentiatedMildSlice χ₀ η w Dw initLeg chemLeg reactLeg Ainit Achem Areact)
    (N : NeumannBoundarySlice Dw) :
    Differentiable ℝ w ∧ (deriv w 0 = 0 ∧ deriv w 1 = 0) ∧
      0 ≤ Ainit + |χ₀| * Achem + Areact ∧
      (∀ x y : ℝ,
        |deriv w x - deriv w y| ≤ (Ainit + |χ₀| * Achem + Areact) * |x - y| ^ η) := by
  -- `deriv w = Dw` everywhere (from the recorded `HasDerivAt`).
  have hderiv_eq : ∀ x : ℝ, deriv w x = Dw x := fun x => (D.hasDeriv x).deriv
  have hdiff : Differentiable ℝ w := fun x => (D.hasDeriv x).differentiableAt
  -- Neumann boundary: `deriv w 0 = Dw 0 = 0`, `deriv w 1 = Dw 1 = 0`.
  have hNeu : deriv w 0 = 0 ∧ deriv w 1 = 0 :=
    ⟨by rw [hderiv_eq]; exact N.deriv_zero, by rw [hderiv_eq]; exact N.deriv_one⟩
  -- the assembled Hölder constant is nonneg.
  have hK_nn : 0 ≤ Ainit + |χ₀| * Achem + Areact := by
    have h2 : 0 ≤ |χ₀| * Achem := mul_nonneg (abs_nonneg _) D.Achem_nn
    have := D.Ainit_nn; have := D.Areact_nn; linarith
  refine ⟨hdiff, hNeu, hK_nn, fun x y => ?_⟩
  -- rewrite `deriv w` as `Dw` and split into the three legs.
  rw [hderiv_eq x, hderiv_eq y, D.deriv_split x, D.deriv_split y]
  set dxy : ℝ := |x - y| ^ η with hdxy
  have hdxy_nn : 0 ≤ dxy := by rw [hdxy]; exact Real.rpow_nonneg (abs_nonneg _) _
  -- per-leg Hölder bounds.
  have hI := D.init_holder x y
  have hC := D.chem_holder x y
  have hR := D.react_holder x y
  -- rearrange the difference of the three-leg sums into leg differences.
  have hsplit :
      (initLeg x - χ₀ * chemLeg x + reactLeg x)
        - (initLeg y - χ₀ * chemLeg y + reactLeg y)
      = (initLeg x - initLeg y) + (-χ₀) * (chemLeg x - chemLeg y)
        + (reactLeg x - reactLeg y) := by ring
  rw [hsplit]
  -- triangle inequality on the three legs.
  have htri :
      |(initLeg x - initLeg y) + (-χ₀) * (chemLeg x - chemLeg y)
          + (reactLeg x - reactLeg y)|
        ≤ |initLeg x - initLeg y| + |(-χ₀) * (chemLeg x - chemLeg y)|
          + |reactLeg x - reactLeg y| := by
    refine (abs_add_le _ _).trans ?_
    gcongr
    exact abs_add_le _ _
  refine htri.trans ?_
  -- bound `|(-χ₀)·Δchem| = |χ₀|·|Δchem| ≤ |χ₀|·(Achem·dxy)`.
  have hχC : |(-χ₀) * (chemLeg x - chemLeg y)| ≤ |χ₀| * (Achem * dxy) := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left hC (abs_nonneg _)
  -- sum the three bounds and collect the common `dxy` factor.
  calc |initLeg x - initLeg y| + |(-χ₀) * (chemLeg x - chemLeg y)|
          + |reactLeg x - reactLeg y|
      ≤ Ainit * dxy + |χ₀| * (Achem * dxy) + Areact * dxy :=
        add_le_add (add_le_add hI hχC) hR
    _ = (Ainit + |χ₀| * Achem + Areact) * dxy := by ring

/-! ## Final wrapper: the `C^{1+η}` slice ⟹ Wiener ℓ¹ (`hQuant` feed) -/

/-- **`chemMild_positiveTime_wiener_l1` — the P2-T11 `hQuant` feed.**

Chains the `C^{1+η}` slice (`chemMild_positiveTime_C1eta_slice`) through the committed
`holderCosineCoeff_summable`: from the Duhamel-differentiation bridge and the no-flux
boundary package (`0 < η ≤ 1`), the mild slice `w = u(t₀,·)` has SUMMABLE cosine
coefficients `∑ₙ |ŵₙ| < ∞`, i.e. lies in the Wiener algebra.  This is the endpoint of
the entire χ₀<0 local-existence Hölder bootstrap (P2-T11 step (ii)). -/
theorem chemMild_positiveTime_wiener_l1 {χ₀ η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    {w Dw initLeg chemLeg reactLeg : ℝ → ℝ} {Ainit Achem Areact : ℝ}
    (D : DifferentiatedMildSlice χ₀ η w Dw initLeg chemLeg reactLeg Ainit Achem Areact)
    (N : NeumannBoundarySlice Dw) :
    Summable (fun n : ℕ => |cosineCoeffs w n|) := by
  obtain ⟨hdiff, hNeu, hK_nn, hHolder⟩ :=
    chemMild_positiveTime_C1eta_slice hη0 D N
  -- the slice supplies the GLOBAL `η`-Hölder of `deriv w`, exactly the hypothesis of the
  -- committed `holderCosineCoeff_summable`.
  exact chemMild_C1eta_slice_wiener_l1 hdiff hNeu hη0 hη1 hK_nn hHolder

/-- Closed-interval replacement for the Wiener feed.

This is the correct endpoint shape for zero-extended interval slices: it uses
`DifferentiableOn` and `derivWithin` on `[0,1]`, so it does not ask the lift to be
two-sided differentiable at the jump endpoints. -/
theorem chemMild_positiveTime_wiener_l1_diffOn {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    {w : ℝ → ℝ} (hw_cont : Continuous w)
    (hw_diff : DifferentiableOn ℝ w (Set.Icc (0:ℝ) 1))
    (hD_cont : Continuous (fun x => derivWithin w (Set.Icc (0:ℝ) 1) (clamp01 x)))
    (hNeumann : derivWithin w (Set.Icc (0:ℝ) 1) 0 = 0 ∧
      derivWithin w (Set.Icc (0:ℝ) 1) 1 = 0)
    {K : ℝ} (hK : 0 ≤ K)
    (hHolder : ∀ x y, x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 →
      |derivWithin w (Set.Icc (0:ℝ) 1) x -
        derivWithin w (Set.Icc (0:ℝ) 1) y| ≤ K * |x - y| ^ η) :
    Summable (fun n : ℕ => |cosineCoeffs w n|) :=
  ShenWork.Wiener.EWA.holderCosineCoeff_summable_diffOn w hw_cont hw_diff hD_cont
    hNeumann hη0 hη1 hK hHolder

/-- Transfer the closed-interval Wiener conclusion from the continuous clamped
representative `liftRepr u` back to the zero extension `intervalDomainLift u`; their
cosine coefficients agree because the coefficient integral only sees `[0,1]`. -/
theorem intervalDomainLift_wiener_l1_of_liftRepr
    {u : intervalDomainPoint → ℝ}
    (h : Summable (fun n : ℕ => |cosineCoeffs (liftRepr u) n|)) :
    Summable (fun n : ℕ => |cosineCoeffs (intervalDomainLift u) n|) := by
  simpa [cosineCoeffs_liftRepr] using h

/-- Wiener feed after Phase 2 interior discharge.  It no longer takes the old full
chemotaxis residual; the remaining chemotaxis input is only the named off-interior
`HasDerivAt` residual.  Endpoint no-flux is supplied intrinsically as `deriv w 0 = 0`
and `deriv w 1 = 0`, not via endpoint values of `chemLitLeg₂`. -/
theorem chemMild_positiveTime_wiener_l1_of_phase2_Qdata_offInterior
    {χ₀ t θ η CQ HQ Ainit Achem Areact : ℝ}
    {u₀ : ℝ → ℝ} {L Q : ℝ → ℝ → ℝ} {w : ℝ → ℝ}
    (hη0 : 0 < η) (hη1_le : η ≤ 1)
    (ht : 0 < t) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hHQ_nn : 0 ≤ HQ)
    (hu₀_meas : AEStronglyMeasurable u₀
      (ShenWork.IntervalDomain.intervalMeasure 1))
    {Cu₀ CL : ℝ} (hu₀_bdd : ∀ y, |u₀ y| ≤ Cu₀)
    (hL_meas : Measurable (Function.uncurry L))
    (hCL_nn : 0 ≤ CL) (hL_bdd : ∀ s y, |L s y| ≤ CL)
    (hQmeas : Measurable (Function.uncurry Q))
    (hQint : ∀ s, Integrable (Q s) (ShenWork.IntervalDomain.intervalMeasure 1))
    (hCQ_nn : 0 ≤ CQ) (hQbdd : ∀ s y, |Q s y| ≤ CQ)
    (hQholder : ∀ s ∈ Set.Ioo (0 : ℝ) t, ∀ a b,
      a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |Q s a - Q s b| ≤ HQ * |a - b| ^ θ)
    (hOff : ChemotaxisLegOffInteriorResidual (chemLitLeg t Q) (chemLitLeg₂ t Q))
    (hw_eq : ∀ x : ℝ,
      w x = initialValueLeg t u₀ x - χ₀ * chemLitLeg t Q x + reactionValueLeg t L x)
    (hw_neumann_zero : deriv w 0 = 0) (hw_neumann_one : deriv w 1 = 0)
    (hAinit_nn : 0 ≤ Ainit) (hAchem_nn : 0 ≤ Achem)
    (hAreact_nn : 0 ≤ Areact)
    (init_holder : ∀ x y : ℝ,
      |initialDerivLeg t u₀ x - initialDerivLeg t u₀ y| ≤ Ainit * |x - y| ^ η)
    (chem_holder : ∀ x y : ℝ,
      |chemLitLeg₂ t Q x - chemLitLeg₂ t Q y| ≤ Achem * |x - y| ^ η)
    (react_holder : ∀ x y : ℝ,
      |reactionDerivLeg t L x - reactionDerivLeg t L y| ≤ Areact * |x - y| ^ η) :
    Summable (fun n : ℕ => |cosineCoeffs w n|) := by
  have hD := differentiatedMildSlice_of_phase2_Qdata_offInterior
    ht hθ0 hθ1 hHQ_nn hu₀_meas hu₀_bdd hL_meas hCL_nn hL_bdd hQmeas hQint
    hCQ_nn hQbdd hQholder hOff hw_eq hAinit_nn hAchem_nn hAreact_nn
    init_holder chem_holder react_holder
  have hN := neumannBoundarySlice_of_intrinsic_endpointDerivs
    hD.hasDeriv hw_neumann_zero hw_neumann_one
  exact chemMild_positiveTime_wiener_l1 hη0 hη1_le hD hN

/-- Wiener feed with the endpoint no-flux discharged from the committed intrinsic
solution-level restart-cosine package.  The chemotaxis leg contributes only the
off-interior `HasDerivAt` residual; no endpoint condition on `chemLitLeg₂` is used. -/
theorem chemMild_positiveTime_wiener_l1_of_phase2_Qdata_restartCosine
    {p : CM2Params} {uDom₀ : intervalDomainPoint → ℝ}
    (Dsol : GradientMildSolutionData p uDom₀)
    (H : HasRestartCosineRepresentations Dsol.T Dsol.u)
    {χ₀ t θ η CQ HQ Ainit Achem Areact : ℝ}
    {u₀ : ℝ → ℝ} {L Q : ℝ → ℝ → ℝ} {w : ℝ → ℝ}
    (hη0 : 0 < η) (hη1_le : η ≤ 1)
    (ht : 0 < t) (htT : t < Dsol.T)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hHQ_nn : 0 ≤ HQ)
    (hu₀_meas : AEStronglyMeasurable u₀
      (ShenWork.IntervalDomain.intervalMeasure 1))
    {Cu₀ CL : ℝ} (hu₀_bdd : ∀ y, |u₀ y| ≤ Cu₀)
    (hL_meas : Measurable (Function.uncurry L))
    (hCL_nn : 0 ≤ CL) (hL_bdd : ∀ s y, |L s y| ≤ CL)
    (hQmeas : Measurable (Function.uncurry Q))
    (hQint : ∀ s, Integrable (Q s) (ShenWork.IntervalDomain.intervalMeasure 1))
    (hCQ_nn : 0 ≤ CQ) (hQbdd : ∀ s y, |Q s y| ≤ CQ)
    (hQholder : ∀ s ∈ Set.Ioo (0 : ℝ) t, ∀ a b,
      a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |Q s a - Q s b| ≤ HQ * |a - b| ^ θ)
    (hOff : ChemotaxisLegOffInteriorResidual (chemLitLeg t Q) (chemLitLeg₂ t Q))
    (hw_eq : ∀ x : ℝ,
      w x = initialValueLeg t u₀ x - χ₀ * chemLitLeg t Q x + reactionValueLeg t L x)
    (hw_solution : ∀ x : ℝ, w x = intervalDomainLift (Dsol.u t) x)
    (hAinit_nn : 0 ≤ Ainit) (hAchem_nn : 0 ≤ Achem)
    (hAreact_nn : 0 ≤ Areact)
    (init_holder : ∀ x y : ℝ,
      |initialDerivLeg t u₀ x - initialDerivLeg t u₀ y| ≤ Ainit * |x - y| ^ η)
    (chem_holder : ∀ x y : ℝ,
      |chemLitLeg₂ t Q x - chemLitLeg₂ t Q y| ≤ Achem * |x - y| ^ η)
    (react_holder : ∀ x y : ℝ,
      |reactionDerivLeg t L x - reactionDerivLeg t L y| ≤ Areact * |x - y| ^ η) :
    Summable (fun n : ℕ => |cosineCoeffs w n|) := by
  have hEnd :=
    gradientMild_closedC2_endpointDerivs_of_restartCosineRepresentations Dsol H t ht htT
  have hw_fun : w = intervalDomainLift (Dsol.u t) := funext hw_solution
  exact chemMild_positiveTime_wiener_l1_of_phase2_Qdata_offInterior
    hη0 hη1_le ht hθ0 hθ1 hHQ_nn hu₀_meas hu₀_bdd hL_meas
    hCL_nn hL_bdd hQmeas hQint hCQ_nn hQbdd hQholder hOff hw_eq
    (by rw [hw_fun]; exact hEnd.2.1)
    (by rw [hw_fun]; exact hEnd.2.2)
    hAinit_nn hAchem_nn hAreact_nn init_holder chem_holder react_holder

end

end ShenWork.Paper2
