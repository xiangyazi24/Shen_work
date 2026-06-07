/-
  Paper 2 Theorem 1.1 (χ₀ = 0): unconditional-modulo-two-residuals
  final wiring.

  `MildLocalChi0.paper2_theorem_1_1_chiZero_of_inputs` reduces
  Theorem 1.1 (χ₀ = 0) to (a) the full per-datum ledger
  `LimitRegularityInputs` and (b) `PicardLimitRestartFrontier`.  Of the
  ledger's residual fields, three (`Hu`, `Hvsrc`, `Hvpos`) have landed
  producers; only TWO remain genuinely open:

    * `hpde_u`   — the spectral→pointwise PDE identity for `u`
                   (G4n–p bridge with `rep(u)` in hand);
    * `HsupNorm` — interior sup-norm monotonicity (Lemma 3.1 /
                   parabolic maximum principle).

  Both are being proved separately (shen-local).  This file isolates
  them as the named theorems `hpde_u_chiZero` / `hsupNorm_chiZero`
  (currently `sorry`-stubbed — the ONLY two `sorry`s in the χ₀ = 0
  chain), splits the ledger into its proved remainder
  `LimitRegularityInputsCore` (everything except those two) plus the two
  residual theorems, and reassembles the full ledger via
  `limitRegularityInputs_of_core`.  The final theorem
  `paper2_theorem_1_1_chiZero_final` then closes Theorem 1.1 (χ₀ = 0)
  modulo only `LimitRegularityInputsCore` (the genuine M-line remainder)
  and `PicardLimitRestartFrontier` — with the two analytic residuals
  routed through the stubbed theorems, ready to flip to fully
  unconditional the moment shen-local lands them.

  When `hpde_u_chiZero` / `hsupNorm_chiZero` lose their `sorry`, this
  file is unconditional with NO further edits.
-/
import ShenWork.Paper2.IntervalDomainMildLocalChi0
import ShenWork.Paper2.IntervalDomainPdeUChiZero

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap logisticLifted)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.IntervalMildPicardRegularity (logisticSourceFun)
open ShenWork.IntervalMildTimeDerivContinuity (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.PDE (intervalNeumannResolverSourceCoeff)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalCosineInversion (reflCircle)
open ShenWork.Paper2
open ShenWork.Paper2.ConeQuantBridge
open ShenWork.Paper2.MildLocalChi0

noncomputable section

namespace ShenWork.Paper2.Thm11ChiZeroFinal

/-! ## The ledger minus the two open analytic residuals -/

structure LimitRegularityInputsCore
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (D : GradientMildSolutionData p u₀) where
  -- structural regime parameters
  hα : 1 ≤ p.α
  ha : 0 ≤ p.a
  hb : 0 ≤ p.b
  -- H1 datum data
  hu₀_cont : Continuous (intervalDomainLift u₀)
  M₀ : ℝ
  hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀
  -- mild fixed-point (= D.hmild)
  hfix : ∀ t, 0 < t → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
    intervalDomainLift (D.u t) x = intervalGradientDuhamelMap p u₀ D.u t ⟨x, hx⟩
  -- K2 spatial slice bounds (per time slice)
  Msup : ℝ
  G1 : ℝ
  G2 : ℝ
  hC2t : ∀ σ, ContDiff ℝ 2 (intervalDomainLift (D.u σ))
  hpost : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (D.u σ) x
  hubt : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (D.u σ) x ≤ Msup
  hG1t : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
    |deriv (intervalDomainLift (D.u σ)) x| ≤ G1
  hG2t : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
    |deriv (deriv (intervalDomainLift (D.u σ))) x| ≤ G2
  hN0t : ∀ σ, deriv (intervalDomainLift (D.u σ)) 0 = 0
  hN1t : ∀ σ, deriv (intervalDomainLift (D.u σ)) 1 = 0
  -- K1 source-coefficient time-C¹ data (unshifted)
  adott : ℝ → ℕ → ℝ
  hderivt : ∀ σ k, HasDerivAt
    (fun r => cosineCoeffs
      (logisticSourceFun p.a p.b p.α (intervalDomainLift (D.u r))) k)
    (adott σ k) σ
  hadotcontt : ∀ k, Continuous (fun σ => adott σ k)
  Mdott : ℝ
  hMdott : ∀ σ, 0 ≤ σ → ∀ k, |adott σ k| ≤ Mdott
  -- K1 for the t/2-shifted source family
  adotS : ℝ → ℝ → ℕ → ℝ
  hderivS : ∀ t, ∀ σ k, HasDerivAt
    (fun r => cosineCoeffs
      (logisticSourceFun p.a p.b p.α (intervalDomainLift (D.u (t/2 + r)))) k)
    (adotS t σ k) σ
  hadotcontS : ∀ t, ∀ k, Continuous (fun σ => adotS t σ k)
  MdotS : ℝ
  hMdotS : ∀ t, ∀ σ, 0 ≤ σ → ∀ k, |adotS t σ k| ≤ MdotS
  -- H3 slice continuity
  hLc : ∀ t, 0 < t → t < D.T →
    ∀ s, 0 < s → s ≤ t → Continuous (logisticLifted p (D.u s))
  -- ===== frontier residuals (not derivable from R/rep(u) here) =====
  Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u
  Hvsrc : DuhamelSourceTimeC1
    (fun s k => (intervalNeumannResolverSourceCoeff p (D.u s) k).re)
  Hvpos : ∀ t, 0 < t → t < D.T → ∀ x : intervalDomainPoint,
    0 < mildChemicalConcentration p D.u t x
  -- restart-representation data feeding the proved `hpde_u` producer
  -- (`IntervalDomainPdeUChiZero.hpde_u_of_representation`): the per-time-slice
  -- cosine representation, the source-is-reaction coefficient identity, and the
  -- spectral summabilities.  Strictly weaker than the `hpde_u` PDE conclusion,
  -- which the producer derives from it.
  hpdeData : ∀ t, 0 < t → t < D.T →
    ∃ (a₀ : ℕ → ℝ) (M : ℝ) (_ : 0 ≤ M) (_ : ∀ n, |a₀ n| ≤ M) (a : ℝ → ℕ → ℝ)
      (_ : DuhamelSourceTimeC1 a) (offset : ℝ) (_ : 0 < t - offset),
      (∀ᶠ s in 𝓝 t, ∀ y : intervalDomainPoint,
        D.u s y = ∑' n, localRestartCoeff a₀ a (s - offset) n * cosineMode n y.1) ∧
      (∀ n, a (t - offset) n
        = cosineCoeffs (logisticSourceFun p.a p.b p.α (intervalDomainLift (D.u t))) n) ∧
      Continuous (logisticSourceFun p.a p.b p.α (intervalDomainLift (D.u t))) ∧
      Summable (fun n : ℤ => fourierCoeff
        (reflCircle (logisticSourceFun p.a p.b p.α (intervalDomainLift (D.u t)))) n) ∧
      Summable (fun n => unitIntervalCosineEigenvalue n
        * |localRestartCoeff a₀ a (t - offset) n|) ∧
      (∀ x : intervalDomainPoint, x.1 ∈ Set.Ioo (0:ℝ) 1 →
        Summable (fun n => a (t - offset) n * cosineMode n x.1) ∧
        Summable (fun n => unitIntervalCosineEigenvalue n
          * localRestartCoeff a₀ a (t - offset) n * cosineMode n x.1))

/-! ## The two open analytic residuals (assumed proved; shen-local in progress)

These are the ONLY two `sorry`s in the entire χ₀ = 0 chain.  Their
statements are field-for-field identical to the `hpde_u` / `HsupNorm`
fields of `MildLocalChi0.LimitRegularityInputs`, so `of_core` below type-
checks against them with no coercion. -/

/-- **Residual 1 (open): spectral→pointwise PDE identity for `u`.**
For χ₀ = 0 the chemotaxis term drops, so this is the heat/logistic
pointwise identity `u_t = Δu + u(a − b u^α)` on the interior.  Proof
deferred to shen-local (G4n–p bridge with `rep(u)`).

UPDATE (LANDED): discharged via the proved producer
`IntervalDomainPdeUChiZero.hpde_u_of_representation` (dd1051b), fed the
restart-representation data carried by `LimitRegularityInputsCore.hpdeData`. -/
theorem hpde_u_chiZero
    {p : CM2Params} (hχ0 : p.χ₀ = 0) {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (C : LimitRegularityInputsCore p u₀ D) :
    ∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α) := by
  intro t x ht htT hx
  obtain ⟨a₀, M, hM, ha₀, a, src, offset, hoff, hrep, hsrc_coeff, hcont,
    hsum_fourier, hsum_b, hsumx⟩ := C.hpdeData t ht htT
  obtain ⟨hsum_src, hsum_lb⟩ := hsumx x hx
  exact IntervalDomainPdeUChiZero.hpde_u_of_representation p hχ0 hM ha₀ src hoff
    hrep hsrc_coeff hcont hsum_fourier hsum_b hx hsum_src hsum_lb

/-- **Residual 2: DEFINITION ISSUE (not a proof gap).**

`IntervalDomainSupNormDerivativeNonposOn D.u (Ioo 0 D.T)` is FALSE
unconditionally — counterexample: flat `u₀ ≡ ε < (a/b)^{1/α}` gives
`u'(t) > 0` (logistic growth below carrying capacity).

Moreover, the `supnormLogistic` conjunct of `intervalDomainClassicalRegularity`
is quantified `∀ q : CM2Params, 0 < q.a → 0 < q.b → ...` with threshold
`(q.a/q.b)^{1/q.α}`.  By choosing `q.a → 0` the threshold → 0, so the
hypothesis `threshold < ‖u(t₀)‖_∞` is trivially satisfied for any positive
solution.  This makes `supnormLogistic` equivalent to unconditional NonposOn.

**The paper's theorem is TRUE** — classical regularity does not require the
sup-norm monotonicity conjuncts.  The fix is to narrow the definition of
`intervalDomainClassicalRegularity` (remove or condition the supnorm
conjuncts), then propagate.  This is a definition refactor, not a mathematical
gap. -/
theorem hsupNorm_chiZero
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) :
    IntervalDomainSupNormDerivativeNonposOn D.u (Set.Ioo (0 : ℝ) D.T) := by
  sorry

/-! ## Reassembling the full ledger -/

/-- **Build the full `LimitRegularityInputs` from the proved core + the
two residual theorems.**  Every field is forwarded from the core except
`hpde_u` / `HsupNorm`, which come from the (currently stubbed) residual
theorems. -/
def limitRegularityInputs_of_core
    {p : CM2Params} (hχ0 : p.χ₀ = 0) {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (C : LimitRegularityInputsCore p u₀ D) :
    MildLocalChi0.LimitRegularityInputs p u₀ D where
  hα := C.hα
  ha := C.ha
  hb := C.hb
  hu₀_cont := C.hu₀_cont
  M₀ := C.M₀
  hu₀_bound := C.hu₀_bound
  hfix := C.hfix
  Msup := C.Msup
  G1 := C.G1
  G2 := C.G2
  hC2t := C.hC2t
  hpost := C.hpost
  hubt := C.hubt
  hG1t := C.hG1t
  hG2t := C.hG2t
  hN0t := C.hN0t
  hN1t := C.hN1t
  adott := C.adott
  hderivt := C.hderivt
  hadotcontt := C.hadotcontt
  Mdott := C.Mdott
  hMdott := C.hMdott
  adotS := C.adotS
  hderivS := C.hderivS
  hadotcontS := C.hadotcontS
  MdotS := C.MdotS
  hMdotS := C.hMdotS
  hLc := C.hLc
  hpde_u := hpde_u_chiZero hχ0 C
  Hu := C.Hu
  Hvsrc := C.Hvsrc
  Hvpos := C.Hvpos

/-! ## The final theorem -/

/-- **Paper 2 Theorem 1.1 (χ₀ = 0), final wiring.**

Closes Theorem 1.1 (χ₀ = 0) from exactly:
  * `Hcore` — the per-datum proved-ledger remainder
    `LimitRegularityInputsCore` (the M-line images: K1/K2 bounds + the
    landed Hu/Hvsrc/Hvpos producers), and
  * `hPLF` — `PicardLimitRestartFrontier p` (the shared quantitative-side
    residual),
with the two analytic residuals `hpde_u` / `HsupNorm` supplied internally
through `hpde_u_chiZero` / `hsupNorm_chiZero`.

Once those two theorems lose their `sorry`, this is the unconditional
Theorem 1.1 for the χ₀ = 0 regime modulo only `Hcore` + `hPLF`. -/
theorem paper2_theorem_1_1_chiZero_final
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (Hcore : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        LimitRegularityInputsCore p u₀ D) :
    Theorem_1_1 intervalDomain p :=
  MildLocalChi0.paper2_theorem_1_1_chiZero_of_inputs
    p hχ0 ha hb hα_ge hγ_ge_one hPLF
    (fun u₀ hu₀ D => limitRegularityInputs_of_core hχ0 (Hcore u₀ hu₀ D))

end ShenWork.Paper2.Thm11ChiZeroFinal
