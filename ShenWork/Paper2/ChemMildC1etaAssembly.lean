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

open MeasureTheory
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDomainRegularityBootstrap (unitIntervalCosineHeatSecondValue)
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

end

end ShenWork.Paper2
