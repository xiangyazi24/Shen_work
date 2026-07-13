import ShenWork.Paper1.IntervalP1PerStepFixedSource
import ShenWork.Paper1.WaveLemma42G1Discharge
import ShenWork.Paper1.WavePaperAdaptiveSourceCompactness
import ShenWork.Paper1.WavePaperRouteARotheAnalytic
import ShenWork.Paper1.WaveLocalUniformClosedGraph
import ShenWork.Paper1.WaveUniformModulusTrap
import ShenWork.Paper1.WaveLocalStepConstruction
import ShenWork.Paper1.WaveControlledSchauder
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- Build the Route-A Green core from the explicit source-box parameter layer.

This is the concrete source-box route from `IntervalP1PerStepFixedSource`, kept
as a reusable adapter so the B1 lower-raw floor can expose these smaller
residuals instead of a monolithic all-supertrap Green core. -/
def paperRouteAParamGreenCore
    {p : CMParams} {c lam M κ Λ B sigma aL C_u L_u C_R m_sigma : ℝ}
    {u : ℝ → ℝ}
    (params : PerStepBoxParams p c lam M κ Λ B sigma aL C_u L_u C_R m_sigma u)
    (wit : ∀ Z : ℝ → ℝ, PaperIterateBase p c κ M u Z →
        PerStepBoxZWitness p c lam M κ B sigma aL C_R m_sigma u Z
          params.hlam params.hrpκ params.hrmκ params.hκ params.hM
          params.hBnn params.hu.trap)
    (hrest : PaperGreenStepInputRouteARegularRestProvider
      p c lam M κ Λ u) :
    PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u :=
  paperGreenStepInputRouteAOrbitCore_of_regularFixedSource
    (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ) (u := u)
    params.hu params.hlam params.basePaperSuper
    (paperStepFixedSourceExistsForRegularSuperTrap_of_params params wit)
    hrest

/-- Scalar and Route-A data for the genuine no-tail local-source construction.
The fixed source itself is built internally for each regular orbit iterate. -/
structure PaperLocalRouteAStepParameters
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) where
  B : ℝ
  hlam : 0 < lam
  hrpκ : κ < greenRootPlus c lam
  hrmκ : κ < -greenRootMinus c lam
  hκ : 0 < κ
  hM : 0 < M
  hB : 0 ≤ B
  chi_nonpos : p.χ ≤ 0
  hu : InMonotoneWaveTrapSet κ M u
  sourceScalar :
    |(-p.χ * p.m)| * M ^ (p.m - 1) * M ^ p.γ *
          greenWeightedMass1 c lam κ * B
      + (1 + |p.χ| * M ^ (p.m - 1) * M ^ p.γ
          + M ^ p.α + |p.χ| * M ^ (p.m + p.γ - 1))
      + lam ≤ B
  barrier : PaperUpperBarrierSuperScalarConditions p c κ M
  derivBound : Λ = 2 * (greenDelta c lam)⁻¹ * (B * M)
  rest : PaperLocalFixedStepRestProvider p c lam M κ Λ u

namespace PaperLocalRouteAStepParameters

/-- The no-tail source Schauder theorem turns the scalar package into the
analytic-preserving Route-A orbit core. -/
noncomputable def toOrbitCore
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (h : PaperLocalRouteAStepParameters p c lam M κ Λ u) :
    PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u :=
  paperGreenStepInputRouteAOrbitCore_of_localFixedStep
    p h.hlam h.hrpκ h.hrmκ h.hκ h.hM h.hB h.hu
    h.sourceScalar h.barrier h.derivBound h.rest

end PaperLocalRouteAStepParameters

/-- Route-A lower-raw producer core using the genuine no-tail local source
Schauder construction.  No exponential rate of the frozen parameter profile
or of an arbitrary old iterate is present. -/
structure PaperLowerRawStepProducerRouteAParamCore
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (u : ℝ → ℝ) : Type where
  stepParams : PaperLocalRouteAStepParameters p c lam M κ Λ u
  lowerRawAux :
    InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
      ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤
        rotheSeqOfPaperRouteA p c lam M κ Λ u
          stepParams.toOrbitCore hκ hM k x) →
        ∃ C_chem La Lb,
          PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
            (rotheSeqOfPaperRouteA p c lam M κ Λ u
              stepParams.toOrbitCore
              hκ hM (k + 1))

/-- The Route-A Green core produced by the parameterized lower-raw core. -/
def paperLowerRawRouteAParamGreenCore
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M} {u : ℝ → ℝ}
    (h : PaperLowerRawStepProducerRouteAParamCore
      p c lam M κ κtilde D Λ hκ hM u) :
    PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u :=
  h.stepParams.toOrbitCore

/-- The orbit-faithful Green producer induced by the parameterized lower-raw
core. -/
def paperLowerRawRouteAParamProducer
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M} {u : ℝ → ℝ}
    (h : PaperLowerRawStepProducerRouteAParamCore
      p c lam M κ κtilde D Λ hκ hM u) :
    PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u :=
  paperLowerRawRouteAParamGreenCore h

/-- Route A is intrinsically the nonpositive-sensitivity derivative maximum
principle.  In particular, the parameterized producer is not a satisfiable
input for a strictly positive-sensitivity branch: its first regular Green step
already contains `p.χ ≤ 0` in the structural Route-A payload. -/
theorem PaperLowerRawStepProducerRouteAParamCore.chi_nonpos
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M} {u : ℝ → ℝ}
    (h : PaperLowerRawStepProducerRouteAParamCore
      p c lam M κ κtilde D Λ hκ hM u) :
    p.χ ≤ 0 :=
  h.stepParams.chi_nonpos

/-! ## Counterexample to the retired shared-left-rate parameterization -/

/-- A continuous antitone profile with a polynomially slow left tail and a
zero right half-line.  It belongs to every wave trap with `κ ≥ 0` and `M ≥ 1`,
but it has no positive exponential left-rate witness. -/
def slowLeftTrapProfile (x : ℝ) : ℝ :=
  let t := max (-x) 0
  t / (1 + t)

theorem slowLeftTrapProfile_continuous : Continuous slowLeftTrapProfile := by
  let t : ℝ → ℝ := fun x => max (-x) 0
  have ht : Continuous t := continuous_id.neg.max continuous_const
  have hden : ∀ x, 1 + t x ≠ 0 := by
    intro x
    have htx : 0 ≤ t x := le_max_right _ _
    linarith
  simpa [slowLeftTrapProfile, t] using ht.div (continuous_const.add ht) hden

theorem slowLeftTrapProfile_nonneg (x : ℝ) :
    0 ≤ slowLeftTrapProfile x := by
  let t : ℝ := max (-x) 0
  have ht : 0 ≤ t := le_max_right _ _
  have hden : 0 < 1 + t := by linarith
  exact div_nonneg ht hden.le

theorem slowLeftTrapProfile_le_one (x : ℝ) :
    slowLeftTrapProfile x ≤ 1 := by
  let t : ℝ := max (-x) 0
  have ht : 0 ≤ t := le_max_right _ _
  have hden : 0 < 1 + t := by linarith
  rw [slowLeftTrapProfile, div_le_iff₀ hden]
  linarith

theorem slowLeftTrapProfile_eq_zero_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    slowLeftTrapProfile x = 0 := by
  simp [slowLeftTrapProfile, max_eq_right (neg_nonpos.mpr hx)]

theorem slowLeftTrapProfile_eq_neg_div_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    slowLeftTrapProfile x = (-x) / (1 - x) := by
  have hneg : 0 ≤ -x := neg_nonneg.mpr hx
  simp [slowLeftTrapProfile, max_eq_left hneg]
  ring

theorem slowLeftTrapProfile_antitone : Antitone slowLeftTrapProfile := by
  intro x y hxy
  let tx : ℝ := max (-x) 0
  let ty : ℝ := max (-y) 0
  have htyx : ty ≤ tx := by
    dsimp [tx, ty]
    exact max_le_max_right 0 (neg_le_neg hxy)
  have htx0 : 0 ≤ tx := le_max_right _ _
  have hty0 : 0 ≤ ty := le_max_right _ _
  have hdx : 0 < 1 + tx := by linarith
  have hdy : 0 < 1 + ty := by linarith
  rw [slowLeftTrapProfile, slowLeftTrapProfile]
  rw [div_le_div_iff₀ hdy hdx]
  nlinarith

theorem slowLeftTrapProfile_mem_monotoneTrap
    {κ M : ℝ} (hκ : 0 ≤ κ) (hM : 1 ≤ M) :
    InMonotoneWaveTrapSet κ M slowLeftTrapProfile := by
  refine ⟨⟨⟨slowLeftTrapProfile_continuous, ⟨1, ?_⟩⟩, ?_⟩,
    slowLeftTrapProfile_antitone⟩
  · intro x
    rw [abs_of_nonneg (slowLeftTrapProfile_nonneg x)]
    exact slowLeftTrapProfile_le_one x
  · intro x
    refine ⟨slowLeftTrapProfile_nonneg x, ?_⟩
    rw [upperBarrier]
    apply le_min
    · exact le_trans (slowLeftTrapProfile_le_one x) hM
    · by_cases hx : x ≤ 0
      · have hexp : 1 ≤ Real.exp (-κ * x) := by
          apply Real.one_le_exp
          have hmul : κ * x ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hκ hx
          nlinarith
        exact le_trans (slowLeftTrapProfile_le_one x) hexp
      · rw [slowLeftTrapProfile_eq_zero_of_nonneg (le_of_not_ge hx)]
        exact (Real.exp_pos _).le

theorem slowLeftTrapProfile_tendsto_atBot_one :
    Tendsto slowLeftTrapProfile atBot (𝓝 1) := by
  have hden : Tendsto (fun x : ℝ => 1 - x) atBot atTop := by
    have hneg : Tendsto (fun x : ℝ => -x) atBot atTop :=
      tendsto_neg_atBot_atTop
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atBot (𝓝 1) :=
      tendsto_const_nhds
    simpa [sub_eq_add_neg, add_comm] using hneg.atTop_add hone
  have hinv : Tendsto (fun x : ℝ => (1 - x)⁻¹) atBot (𝓝 0) :=
    hden.inv_tendsto_atTop
  have hformula :
      (fun x : ℝ => slowLeftTrapProfile x) =ᶠ[atBot]
        (fun x => 1 - (1 - x)⁻¹) := by
    filter_upwards [eventually_le_atBot 0] with x hx
    rw [slowLeftTrapProfile_eq_neg_div_of_nonpos hx]
    have hden_ne : 1 - x ≠ 0 := by linarith
    field_simp
    ring
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atBot (𝓝 1) :=
    tendsto_const_nhds
  have htend : Tendsto (fun x : ℝ => 1 - (1 - x)⁻¹) atBot (𝓝 1) := by
    simpa using hone.sub hinv
  exact htend.congr' hformula.symm

/-- Polynomial decay at the left cannot obey any positive exponential rate. -/
theorem slowLeftTrapProfile_not_expLeftRateData :
    ¬ ExpLeftRateData slowLeftTrapProfile := by
  rintro ⟨sigma, aL, C, ell, hsigma, hrate⟩
  have hell : ell = 1 :=
    tendsto_nhds_unique (ExpLeftRate.tendsto_atBot hsigma hrate)
      slowLeftTrapProfile_tendsto_atBot_one
  subst ell
  let A : ℝ := C * Real.exp (-sigma * aL)
  have hexp0 :
      Tendsto (fun t : ℝ => Real.exp (-sigma * t)) atTop (𝓝 0) := by
    exact Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hsigma))
  have htexp0 :
      Tendsto (fun t : ℝ => t * Real.exp (-sigma * t)) atTop (𝓝 0) := by
    simpa [Real.rpow_one] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 sigma hsigma)
  have hdecay :
      Tendsto
        (fun t : ℝ => A * ((1 + t) * Real.exp (-sigma * t)))
        atTop (𝓝 0) := by
    have hsum : Tendsto
        (fun t : ℝ => Real.exp (-sigma * t) +
          t * Real.exp (-sigma * t)) atTop (𝓝 0) := by
      simpa using hexp0.add htexp0
    simpa [mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm] using
      hsum.const_mul A
  have hevent :
      ∀ᶠ t : ℝ in atTop,
        A * ((1 + t) * Real.exp (-sigma * t)) < 1 / 2 := by
    have hball := Metric.tendsto_atTop.mp hdecay (1 / 2) (by norm_num)
    rcases hball with ⟨T, hT⟩
    exact eventually_atTop.2 ⟨T, fun t ht => by
      have hd := hT t ht
      rw [Real.dist_eq, sub_zero] at hd
      exact lt_of_le_of_lt (le_abs_self _) hd⟩
  rcases eventually_atTop.1 hevent with ⟨T, hT⟩
  let t : ℝ := max T 0
  have htT : T ≤ t := le_max_left _ _
  have ht : 0 ≤ t := le_max_right _ _
  have htiny : A * ((1 + t) * Real.exp (-sigma * t)) < 1 / 2 :=
    hT t htT
  have hrate_t := hrate (-t)
  have hslow : slowLeftTrapProfile (-t) = t / (1 + t) := by
    rw [slowLeftTrapProfile_eq_neg_div_of_nonpos (by linarith)]
    congr 1 <;> ring
  have hleft : |slowLeftTrapProfile (-t) - 1| = 1 / (1 + t) := by
    rw [hslow]
    have hden : 0 < 1 + t := by linarith
    have hsub : t / (1 + t) - 1 = -(1 / (1 + t)) := by
      field_simp
      ring
    rw [hsub, abs_neg, abs_of_nonneg]
    exact one_div_nonneg.mpr hden.le
  rw [hleft] at hrate_t
  have hden : 0 < 1 + t := by linarith
  have hmul := mul_le_mul_of_nonneg_left hrate_t hden.le
  have hone : (1 + t) * (1 / (1 + t)) = 1 := by
    field_simp
  have hexp_split :
      Real.exp (sigma * (-t - aL)) =
        Real.exp (-sigma * t) * Real.exp (-sigma * aL) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hge : 1 ≤ A * ((1 + t) * Real.exp (-sigma * t)) := by
    rw [hone, hexp_split] at hmul
    dsimp [A]
    nlinarith [hmul]
  linarith

/-- The total analytic-preserving Rothe sequence induced by a trap-indexed
parameterized Route-A Green core. -/
def paperLowerRawParamRotheSeq
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (producer : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperLowerRawStepProducerRouteAParamCore
        p c lam M κ κtilde D Λ hκ hM u) :
    (ℝ → ℝ) → ℕ → ℝ → ℝ :=
  rotheSeqOfPaperRouteAFromTrap p c lam M κ Λ
    (fun u hu => paperLowerRawRouteAParamGreenCore (producer u hu)) hκ hM

/-- The exact L10 residual after compactness: every local-uniform cluster of
Rothe limits along converging frozen profiles is the Rothe limit at the target
profile.  Compact range turns this closed-graph statement into full sequential
continuity below. -/
def PaperLowerRawParamRotheLimitClosedGraph
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (producer : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperLowerRawStepProducerRouteAParamCore
        p c lam M κ κtilde D Λ hκ hM u) : Prop :=
  LocalUniformSequentialClosedGraphOn
    (InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D))
    (fun u => rotheLimit (paperLowerRawParamRotheSeq producer u))

/-- The irreducible L10 identification statement after the off-diagonal Green
closed graph: a lower-pinned stationary cluster for the frozen profile `u` is
the particular upper-start Rothe limit selected at `u`.  The lower pin is
essential: on the bare trap the zero profile is always a self step. -/
def PaperLowerRawParamRotheStationaryIdentification
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (producer : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperLowerRawStepProducerRouteAParamCore
        p c lam M κ κtilde D Λ hκ hM u) : Prop :=
  ∀ u W,
    InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
    InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) W →
    (∀ x, paperImplicitStepOp p c (1 / lam) u W x = W x) →
      W = rotheLimit (paperLowerRawParamRotheSeq producer u)

/-- Route-A paper Rothe parabolic floor after source compactness, adaptive
step closed graph, and finite-cube fields have been removed.  The remaining
map-level analytic datum is exactly L10: local-uniform continuity of the
long-time Rothe limit on the lower-pinned trap. -/
structure PaperLowerRawParabolicFloorRouteAParamCoreNoBar
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : Type where
  producer :
    ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperLowerRawStepProducerRouteAParamCore
        p c lam M κ κtilde D Λ hκ hM u
  limitContinuous :
    LocalUniformContinuousOn
      (InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D))
      (fun u => rotheLimit (paperLowerRawParamRotheSeq producer u))

/-- The full Route-A parabolic floor inherits the sign restriction of every
one of its step producers. -/
theorem PaperLowerRawParabolicFloorRouteAParamCoreNoBar.chi_nonpos
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (h : PaperLowerRawParabolicFloorRouteAParamCoreNoBar
      p c lam M κ κtilde D Λ hκ hM) :
    p.χ ≤ 0 := by
  have htrap :
      InMonotoneWaveTrapSet κ M (upperBarrier κ M) :=
    upperBarrier_mem_InMonotoneWaveTrapSet hκ hM
  exact (h.producer (upperBarrier κ M) htrap).chi_nonpos

/-- The total map used by Schauder, with the producer invoked only on its trap
domain and the upper barrier used outside it. -/
def paperLowerRawParamRotheSeqFromTrap
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (h : PaperLowerRawParabolicFloorRouteAParamCoreNoBar
      p c lam M κ κtilde D Λ hκ hM) :
    (ℝ → ℝ) → ℕ → ℝ → ℝ :=
  paperLowerRawParamRotheSeq h.producer

/-- The parameterized Route-A orbit supplies its moving Green-source cluster
from the analytic payload retained at every successor.  No source compactness
or family-uniform Rothe tail remains as a carried hypothesis. -/
theorem paperLowerRawParamGreenSourceCompactness
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (h : PaperLowerRawParabolicFloorRouteAParamCoreNoBar
      p c lam M κ κtilde D Λ hκ hM)
    (hMpos : 0 < M) (hΛ0 : 0 ≤ Λ) :
    PaperGreenRotheAdaptiveSourceCompactnessOnTrap p c lam M κ Λ
      (paperLowerRawParamRotheSeq h.producer) := by
  let hinput : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u :=
    fun u hu => paperLowerRawRouteAParamGreenCore (h.producer u hu)
  have hlam : 0 < lam :=
    (hinput (upperBarrier κ M)
      (upperBarrier_mem_InMonotoneWaveTrapSet hκ hM)).hlam
  apply paperGreenRotheAdaptiveSourceCompactness_of_stepAnalytic
    p c lam M κ Λ hMpos hΛ0 hlam (paperLowerRawParamRotheSeq h.producer)
  · intro u hu k
    change PaperStepAnalytic p c lam M κ Λ u
      (rotheSeqOfPaperRouteAFromTrap p c lam M κ Λ hinput hκ hM u k)
      (rotheSeqOfPaperRouteAFromTrap p c lam M κ Λ hinput hκ hM u (k + 1))
    rw [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu]
    exact rotheSeqOfPaperRouteA_stepAnalytic (hinput u hu) hκ hM k
  · intro u hu k x
    change 0 ≤ rotheSeqOfPaperRouteAFromTrap p c lam M κ Λ hinput hκ hM
      u (k + 1) x
    rw [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu]
    exact rotheSeqOfPaperRouteA_nonneg (hinput u hu) hκ hM (k + 1) x
  · intro u hu k x
    change rotheSeqOfPaperRouteAFromTrap p c lam M κ Λ hinput hκ hM
      u (k + 1) x ≤ M
    rw [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu]
    exact rotheSeqOfPaperRouteA_le_M (hinput u hu) hκ hM (k + 1) x

/-- The parameterized Route-A orbit supplies the stronger off-diagonal Green
closed graph needed for continuity of its long-time limit map. -/
theorem paperLowerRawParamOffDiagonalStepClosedGraph
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (h : PaperLowerRawParabolicFloorRouteAParamCoreNoBar
      p c lam M κ κtilde D Λ hκ hM)
    (hMpos : 0 < M) (hΛ0 : 0 ≤ Λ) :
    PaperGreenRotheAdaptiveOffDiagonalStepClosedGraphOnTrap p c lam M κ
      (paperLowerRawParamRotheSeq h.producer) := by
  let hinput : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u :=
    fun u hu => paperLowerRawRouteAParamGreenCore (h.producer u hu)
  have hlam : 0 < lam :=
    (hinput (upperBarrier κ M)
      (upperBarrier_mem_InMonotoneWaveTrapSet hκ hM)).hlam
  apply paperGreenRotheAdaptiveOffDiagonalStepClosedGraph_of_stepAnalytic
    p c lam M κ Λ hMpos hΛ0 hlam (paperLowerRawParamRotheSeq h.producer)
  · intro u hu k
    change PaperStepAnalytic p c lam M κ Λ u
      (rotheSeqOfPaperRouteAFromTrap p c lam M κ Λ hinput hκ hM u k)
      (rotheSeqOfPaperRouteAFromTrap p c lam M κ Λ hinput hκ hM u (k + 1))
    rw [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu]
    exact rotheSeqOfPaperRouteA_stepAnalytic (hinput u hu) hκ hM k
  · intro u hu k x
    change 0 ≤ rotheSeqOfPaperRouteAFromTrap p c lam M κ Λ hinput hκ hM
      u (k + 1) x
    rw [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu]
    exact rotheSeqOfPaperRouteA_nonneg (hinput u hu) hκ hM (k + 1) x
  · intro u hu k x
    change rotheSeqOfPaperRouteAFromTrap p c lam M κ Λ hinput hκ hM
      u (k + 1) x ≤ M
    rw [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu]
    exact rotheSeqOfPaperRouteA_le_M (hinput u hu) hκ hM (k + 1) x

/-- L10 continuity immediately gives the sequential closed graph of the
long-time map.  The adaptive Green closed graph is used later, at the Schauder
fixed point, to pass the implicit step equation and obtain stationarity. -/
theorem paperLowerRawParamRotheLimitClosedGraph
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (h : PaperLowerRawParabolicFloorRouteAParamCoreNoBar
      p c lam M κ κtilde D Λ hκ hM)
    (_hMpos : 0 < M) (_hΛ0 : 0 ≤ Λ)
    (_hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|) :
    PaperLowerRawParamRotheLimitClosedGraph h.producer := by
  intro seq u W hseq hu _hW houter hlimits
  exact hlimits.unique (h.limitContinuous seq u hseq hu houter)

/-- The L10 field is exactly the `RotheContinuousDependence` interface used by
the Schauder construction. -/
theorem paperLowerRawParamRotheContinuousDependence
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (h : PaperLowerRawParabolicFloorRouteAParamCoreNoBar
      p c lam M κ κtilde D Λ hκ hM)
    (_hlower : RotheOrbitLowerBound κ M (lowerBarrierRaw κ κtilde D)
      (paperLowerRawParamRotheSeq h.producer))
    (_hMpos : 0 < M) (_hΛ0 : 0 ≤ Λ)
    (_hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|) :
    RotheContinuousDependence p c lam
      (InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D))
      (paperLowerRawParamRotheSeq h.producer) :=
  h.limitContinuous

/-- Only the left-flatness half of the legacy stationary/flat floor.  The
adaptive Green closed graph now supplies stationarity itself. -/
def PaperLowerPinnedFlatFloor
    (p : CMParams) (c κ M : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
    (∀ x, frozenWaveOperator p c U U x = 0) →
      FrozenStationaryFlatAtLeft p U

/-- Direct Schauder--Tychonoff fixed point followed by the adaptive whole-line
Green closed graph, with amplitude and spatial modulus independent.  This is
the finite-cube-free construction used by the live lower-raw branch. -/
theorem paperLowerPinned_stationary_of_modulusSchauder
    (p : CMParams) (c lam M κ L : ℝ) (φ : ℝ → ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hlam : 0 < lam)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheOrbitDataWithModulus p c lam M κ L (rotheSeq u))
    (hlower : RotheOrbitLowerBound κ M φ rotheSeq)
    (hcont : LocalUniformContinuousOn
      (InLowerPinnedMonotoneTrap κ M φ)
      (fun u => rotheLimit (rotheSeq u)))
    (hgraph : PaperGreenRotheAdaptiveStepClosedGraphOnTrap
      p c lam M κ rotheSeq)
    (hne : ∃ u, InLowerPinnedMonotoneTrap κ M φ u) :
    ∃ U, InLowerPinnedMonotoneTrap κ M φ U ∧
      (∀ x, frozenWaveOperator p c U U x = 0) ∧
      Differentiable ℝ U ∧ Differentiable ℝ (deriv U) ∧
      PaperGreenSourceTailData c lam U := by
  let Tmap : (ℝ → ℝ) → ℝ → ℝ :=
    fun u => rotheLimit (rotheSeq u)
  have hbareMap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u) := by
    intro u hu
    let h := hdata u hu
    exact rotheLimit_mem_trap (h.limit_continuous hL) h.bddBelow
      h.anti_x h.nonneg h.le_upperBarrier (upperBarrier_isBddFun hM)
  have hlowerMap : ∀ u, InLowerPinnedMonotoneTrap κ M φ u →
      ∀ x, φ x ≤ Tmap u x :=
    Tmap_lowerInvariant_of_rotheOrbitLowerBound hlower
  have hmap : ∀ u, InLowerPinnedMonotoneTrap κ M φ u →
      InLowerPinnedMonotoneTrap κ M φ (Tmap u) :=
    fun u hu => ⟨hbareMap u hu.bare, hlowerMap u hu⟩
  have hcompactBare : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap := by
    simpa [Tmap] using paperTmap_compactRange_of_orbitModulus
      p c lam M κ L hM hL rotheSeq hdata
  have hcompact : LocalUniformSequentiallyCompactRange
      (InLowerPinnedMonotoneTrap κ M φ) Tmap := by
    intro seq hseq
    obtain ⟨sub, hsub, U, hUbare, hconv⟩ :=
      hcompactBare seq (fun n => (hseq n).bare)
    have hUlower : ∀ x, φ x ≤ U x := by
      intro x
      exact le_of_tendsto_of_tendsto tendsto_const_nhds (hconv.tendsto_at x)
        (Eventually.of_forall fun n =>
          hlowerMap (seq (sub n)) (hseq (sub n)) x)
    exact ⟨sub, hsub, U, ⟨hUbare, hUlower⟩, hconv⟩
  obtain ⟨U, hU, hfix⟩ :=
    (InLowerPinnedMonotoneTrap.boundedConvexProfileTrapData hne).exists_fixed
      hmap hcont hcompact
  have hLU : LocallyUniformConverges (rotheSeq U) U := by
    simpa only [Tmap, hfix] using (hdata U hU.bare).locallyUniform hL
  have hLU_succ : LocallyUniformConverges
      (fun n => rotheSeq U (n + 1)) U :=
    hLU.comp_strictMono (strictMono_id.add_const 1)
  obtain ⟨hstep, hUdiff, hUderivDiff, hsourceTail⟩ :=
    hgraph (fun _ : ℕ => U) U id (fun _ => hU.bare) hU.bare
      (LocallyUniformConverges.const U) tendsto_id
      (by simpa using hLU) (by simpa using hLU_succ)
  have hstat : ∀ x, frozenWaveOperator p c U U x = 0 :=
    frozenWaveOperator_eq_zero_of_paperImplicitStepOp_self
      p c lam U hlam hU.bare.trap.cunif_bdd hU.bare.nonneg hUdiff
      (fun x => frozenElliptic_deriv_differentiableAt p
        hU.bare.trap.cunif_bdd hU.bare.nonneg x)
      (fun x => (hUdiff x).rpow_const (Or.inr p.hm)) hstep
  exact ⟨U, hU, hstat, hUdiff, hUderivDiff, hsourceTail⟩

/-- B1 χ≤0 Route-A wrapper after replacing the monolithic Route-A per-step
producer residual by the explicit source-box parameter layer. -/
theorem b1_chiNeg_existence_paper_routeA_paramCore_noBar_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ)
    (hpar :
      PaperLowerRawParabolicFloorRouteAParamCoreNoBar
        p c lam M κ κtilde D Λ hcond.hκ0.le
        (le_trans zero_le_one hcond.hM)) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U ∧
      Differentiable ℝ U ∧ Differentiable ℝ (deriv U) := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hcond.hM
  let hinputTrap : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u :=
    fun u hu => paperLowerRawRouteAParamGreenCore (hpar.producer u hu)
  let zseq := paperLowerRawParamRotheSeqFromTrap hpar
  have hstep : RotheStepLowerInvariant κ M
      (lowerBarrierRaw κ κtilde D) zseq := by
    refine rotheStepLowerInvariant_lowerBarrierRaw_of_paperStepData
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
      (κtilde := κtilde) (D := D) (Λ := Λ)
      hcond hD hD_ge_one ?_
    intro u hu k hprev
    let hp := hpar.producer u hu.bare
    have hzu : zseq u = rotheSeqOfPaperRouteA p c lam M κ Λ u
        (paperLowerRawRouteAParamGreenCore hp) hcond.hκ0.le hM0 := by
      simpa [zseq, paperLowerRawParamRotheSeqFromTrap, hinputTrap, hp] using
        rotheSeqOfPaperRouteAFromTrap_eq hinputTrap hcond.hκ0.le hM0 hu.bare
    rw [hzu] at hprev ⊢
    obtain ⟨C_chem, La, Lb, haux⟩ := hp.lowerRawAux hu k hprev
    have hfacts := rotheSeqOfPaperRouteA_stepFacts
      (paperLowerRawRouteAParamGreenCore hp) hcond.hκ0.le hM0 k
    exact ⟨C_chem, La, Lb,
      (paperLowerRawRouteAParamGreenCore hp).hlam, hfacts.step_op, haux⟩
  have hlower : RotheOrbitLowerBound κ M
      (lowerBarrierRaw κ κtilde D) zseq :=
    rotheOrbitLowerBound_of_stepLowerInvariant
      (fun u hu => by
        have hzu : zseq u = rotheSeqOfPaperRouteA p c lam M κ Λ u
            (hinputTrap u hu.bare) hcond.hκ0.le hM0 := by
          simpa [zseq, paperLowerRawParamRotheSeqFromTrap, hinputTrap] using
            rotheSeqOfPaperRouteAFromTrap_eq hinputTrap
              hcond.hκ0.le hM0 hu.bare
        rw [hzu]
        exact rotheSeqOfPaperRouteA_lowerPinned_base (hinputTrap u hu.bare)
          hcond.hκ0.le hM0 hu)
      hstep
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hcond.hM
  let Q : ℝ := max M Λ
  have hQ0 : 0 ≤ Q := le_trans hM0 (le_max_left M Λ)
  have hΛQ : Λ ≤ Q := le_max_right M Λ
  have hMQ : M ≤ Q := le_max_left M Λ
  have hbarLipQ : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ Q * |x - y| := by
    intro x y
    exact (hcond.upperBarrier_barLip x y).trans
      (mul_le_mul_of_nonneg_right hMQ (abs_nonneg _))
  have hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheOrbitDataWithModulus p c lam M κ Q (zseq u) := by
    intro u hu
    simpa [zseq, paperLowerRawParamRotheSeqFromTrap, hinputTrap] using
      paperRouteARotheOrbitDataWithModulus_fromTrap
        (p := p) (c := c) (lam := lam)
        (M := M) (κ := κ) (Λ := Λ) (u := u) hinputTrap
        hcond.hκ0.le hM0 hΛ0 hΛQ hbarLipQ hu
  have hlam : 0 < lam :=
    (hpar.producer (upperBarrier κ M)
      (upperBarrier_mem_InMonotoneWaveTrapSet hcond.hκ0.le hM0)).stepParams.hlam
  have hgap_pos : 0 < κtilde - κ := sub_pos.mpr hcond.hgap
  have hDpos : 0 < D := D_pos_of_paperDMin_lt hcond hD
  have hExpM :
      Real.exp (-κ * lowerBarrierXPlus κ κtilde D) ≤ M :=
    lowerBarrierExpXPlus_le_one_of_one_le_D hcond.hκ0 hgap_pos
      hD_ge_one hcond.hM
  have hplat : InMonotoneWaveTrapSet κ M
      (lowerBarrierPlateau κ κtilde D) :=
    lowerBarrierPlateau_mem_InMonotoneWaveTrapSet_of_exp_xplus_le
      hcond.hκ0 hgap_pos hDpos hExpM
  have hcont : LocalUniformContinuousOn
      (InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D))
      (fun u => rotheLimit (zseq u)) := by
    simpa [zseq, paperLowerRawParamRotheSeqFromTrap] using
      paperLowerRawParamRotheContinuousDependence hpar hlower
        hMpos hΛ0 hcond.upperBarrier_barLip
  have hgraph : PaperGreenRotheAdaptiveStepClosedGraphOnTrap
      p c lam M κ zseq := by
    simpa [zseq, paperLowerRawParamRotheSeqFromTrap] using
      paperGreenRotheAdaptiveStepClosedGraph_of_sourceCompactness
        p c lam M κ Λ hMpos hΛ0 hlam
        (paperLowerRawParamRotheSeq hpar.producer)
        (paperLowerRawParamGreenSourceCompactness hpar hMpos hΛ0)
  obtain ⟨U, hU, hstat, hUdiff, hUderivDiff, hsourceTail⟩ :=
    paperLowerPinned_stationary_of_modulusSchauder
      p c lam M κ Q (lowerBarrierRaw κ κtilde D)
      hM0 hQ0 hlam zseq hdata hlower hcont hgraph
      ⟨lowerBarrierPlateau κ κtilde D, hplat,
        lowerBarrierRaw_le_plateau hcond.hκ0 hgap_pos hDpos⟩
  have hnontriv : ProfileNontrivial U :=
    profileNontrivial_of_lowerBarrierRaw_tail_bound hcond hD
      (fun x _hx => hU.lower x)
  have hpos : ∀ x, 0 < U x :=
    stationaryProfile_strictlyPositive_of_trap_regularity
      hMpos hU.bare hstat hUdiff hUderivDiff hnontriv
  have hsource : FrozenStationaryGreenSourceTail c lam U := by
    simpa [PaperGreenSourceTailData, FrozenStationaryGreenSourceTail] using
      hsourceTail
  have hflatU : FrozenStationaryFlatAtLeft p U :=
    frozenStationaryFlatAtLeft_of_green_source_tail
      hlam hMpos hU hUdiff hsource
  have hlim_neg : Tendsto U atBot (nhds 1) :=
    InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_lowerBarrierRaw_pin
      hcond.hκ0 hgap_pos hDpos hU.bare hU.lower hflatU hstat
  have hlim_pos : Tendsto U atTop (nhds 0) :=
    hU.bare.tendsto_atTop_zero hcond.hκ0
  have hcpos : 0 < c := by
    rw [hcond.hc]
    have hinv : 0 < κ⁻¹ := inv_pos.mpr hcond.hκ0
    nlinarith [hcond.hκ0, hinv]
  exact ⟨U, hU,
    FrozenStationaryWaveProfile.mk_auto_limits hcpos hpos
      hU.bare.trap.cunif_bdd hstat hlim_neg hlim_pos,
    hUdiff, hUderivDiff⟩

/-- B1 χ≥0 Route-A wrapper after replacing the monolithic Route-A per-step
producer residual by the explicit source-box parameter layer. -/
theorem b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ)
    (hpar :
      PaperLowerRawParabolicFloorRouteAParamCoreNoBar
        p c lam M κ κtilde D Λ hcond.hκ0.le
        (le_trans zero_le_one hcond.hM)) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U ∧
      Differentiable ℝ U ∧ Differentiable ℝ (deriv U) := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hcond.hM
  let hinputTrap : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u :=
    fun u hu => paperLowerRawRouteAParamGreenCore (hpar.producer u hu)
  let zseq := paperLowerRawParamRotheSeqFromTrap hpar
  have hstep : RotheStepLowerInvariant κ M
      (lowerBarrierRaw κ κtilde D) zseq := by
    refine rotheStepLowerInvariant_lowerBarrierRaw_of_positivePaperStepData
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
      (κtilde := κtilde) (D := D) (Λ := Λ)
      hcond hD hD_ge_one ?_
    intro u hu k hprev
    let hp := hpar.producer u hu.bare
    have hzu : zseq u = rotheSeqOfPaperRouteA p c lam M κ Λ u
        (paperLowerRawRouteAParamGreenCore hp) hcond.hκ0.le hM0 := by
      simpa [zseq, paperLowerRawParamRotheSeqFromTrap, hinputTrap, hp] using
        rotheSeqOfPaperRouteAFromTrap_eq hinputTrap hcond.hκ0.le hM0 hu.bare
    rw [hzu] at hprev ⊢
    obtain ⟨C_chem, La, Lb, haux⟩ := hp.lowerRawAux hu k hprev
    have hfacts := rotheSeqOfPaperRouteA_stepFacts
      (paperLowerRawRouteAParamGreenCore hp) hcond.hκ0.le hM0 k
    exact ⟨C_chem, La, Lb,
      (paperLowerRawRouteAParamGreenCore hp).hlam, hfacts.step_op, haux⟩
  have hlower : RotheOrbitLowerBound κ M
      (lowerBarrierRaw κ κtilde D) zseq :=
    rotheOrbitLowerBound_of_stepLowerInvariant
      (fun u hu => by
        have hzu : zseq u = rotheSeqOfPaperRouteA p c lam M κ Λ u
            (hinputTrap u hu.bare) hcond.hκ0.le hM0 := by
          simpa [zseq, paperLowerRawParamRotheSeqFromTrap, hinputTrap] using
            rotheSeqOfPaperRouteAFromTrap_eq hinputTrap
              hcond.hκ0.le hM0 hu.bare
        rw [hzu]
        exact rotheSeqOfPaperRouteA_lowerPinned_base (hinputTrap u hu.bare)
          hcond.hκ0.le hM0 hu)
      hstep
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hcond.hM
  let Q : ℝ := max M Λ
  have hQ0 : 0 ≤ Q := le_trans hM0 (le_max_left M Λ)
  have hΛQ : Λ ≤ Q := le_max_right M Λ
  have hMQ : M ≤ Q := le_max_left M Λ
  have hbarLipQ : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ Q * |x - y| := by
    intro x y
    exact (hcond.upperBarrier_barLip x y).trans
      (mul_le_mul_of_nonneg_right hMQ (abs_nonneg _))
  have hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheOrbitDataWithModulus p c lam M κ Q (zseq u) := by
    intro u hu
    simpa [zseq, paperLowerRawParamRotheSeqFromTrap, hinputTrap] using
      paperRouteARotheOrbitDataWithModulus_fromTrap
        (p := p) (c := c) (lam := lam)
        (M := M) (κ := κ) (Λ := Λ) (u := u) hinputTrap
        hcond.hκ0.le hM0 hΛ0 hΛQ hbarLipQ hu
  have hlam : 0 < lam :=
    (hpar.producer (upperBarrier κ M)
      (upperBarrier_mem_InMonotoneWaveTrapSet hcond.hκ0.le hM0)).stepParams.hlam
  have hgap_pos : 0 < κtilde - κ := sub_pos.mpr hcond.hgap
  have hDpos : 0 < D := D_pos_of_positive_paperDMin_lt hcond hD
  have hExpM :
      Real.exp (-κ * lowerBarrierXPlus κ κtilde D) ≤ M :=
    lowerBarrierExpXPlus_le_one_of_one_le_D hcond.hκ0 hgap_pos
      hD_ge_one hcond.hM
  have hplat : InMonotoneWaveTrapSet κ M
      (lowerBarrierPlateau κ κtilde D) :=
    lowerBarrierPlateau_mem_InMonotoneWaveTrapSet_of_exp_xplus_le
      hcond.hκ0 hgap_pos hDpos hExpM
  have hcont : LocalUniformContinuousOn
      (InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D))
      (fun u => rotheLimit (zseq u)) := by
    simpa [zseq, paperLowerRawParamRotheSeqFromTrap] using
      paperLowerRawParamRotheContinuousDependence hpar hlower
        hMpos hΛ0 hcond.upperBarrier_barLip
  have hgraph : PaperGreenRotheAdaptiveStepClosedGraphOnTrap
      p c lam M κ zseq := by
    simpa [zseq, paperLowerRawParamRotheSeqFromTrap] using
      paperGreenRotheAdaptiveStepClosedGraph_of_sourceCompactness
        p c lam M κ Λ hMpos hΛ0 hlam
        (paperLowerRawParamRotheSeq hpar.producer)
        (paperLowerRawParamGreenSourceCompactness hpar hMpos hΛ0)
  obtain ⟨U, hU, hstat, hUdiff, hUderivDiff, hsourceTail⟩ :=
    paperLowerPinned_stationary_of_modulusSchauder
      p c lam M κ Q (lowerBarrierRaw κ κtilde D)
      hM0 hQ0 hlam zseq hdata hlower hcont hgraph
      ⟨lowerBarrierPlateau κ κtilde D, hplat,
        lowerBarrierRaw_le_plateau hcond.hκ0 hgap_pos hDpos⟩
  have hnontriv : ProfileNontrivial U :=
    profileNontrivial_of_lowerBarrierRaw_positive_tail_bound hcond hD
      (fun x _hx => hU.lower x)
  have hpos : ∀ x, 0 < U x :=
    stationaryProfile_strictlyPositive_of_trap_regularity
      hMpos hU.bare hstat hUdiff hUderivDiff hnontriv
  have hsource : FrozenStationaryGreenSourceTail c lam U := by
    simpa [PaperGreenSourceTailData, FrozenStationaryGreenSourceTail] using
      hsourceTail
  have hflatU : FrozenStationaryFlatAtLeft p U :=
    frozenStationaryFlatAtLeft_of_green_source_tail
      hlam hMpos hU hUdiff hsource
  have hlim_neg : Tendsto U atBot (nhds 1) :=
    InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_lowerBarrierRaw_pin
      hcond.hκ0 hgap_pos hDpos hU.bare hU.lower hflatU hstat
  have hlim_pos : Tendsto U atTop (nhds 0) :=
    hU.bare.tendsto_atTop_zero hcond.hκ0
  have hcpos : 0 < c := by
    rw [hcond.hc]
    have hinv : 0 < κ⁻¹ := inv_pos.mpr hcond.hκ0
    nlinarith [hcond.hκ0, hinv]
  exact ⟨U, hU,
    FrozenStationaryWaveProfile.mk_auto_limits hcpos hpos
      hU.bare.trap.cunif_bdd hstat hlim_neg hlim_pos,
    hUdiff, hUderivDiff⟩

/-- Clean negative-branch name after the finite-cube approximation and adaptive
Green source compactness have both become internal theorems. -/
theorem b1_chiNeg_existence_paper_routeA_paramCore_noBar
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ)
    (hpar : PaperLowerRawParabolicFloorRouteAParamCoreNoBar
      p c lam M κ κtilde D Λ hcond.hκ0.le
        (le_trans zero_le_one hcond.hM)) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U ∧
      Differentiable ℝ U ∧ Differentiable ℝ (deriv U) :=
  b1_chiNeg_existence_paper_routeA_paramCore_noBar_of_cubeApproxData
    p c lam M κ κtilde D Λ hcond hD hD_ge_one hΛ0 hpar

/-- Clean positive-branch name after the finite-cube approximation and adaptive
Green source compactness have both become internal theorems. -/
theorem b1_chiPos_existence_paper_routeA_paramCore_noBar
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ)
    (hpar : PaperLowerRawParabolicFloorRouteAParamCoreNoBar
      p c lam M κ κtilde D Λ hcond.hκ0.le
        (le_trans zero_le_one hcond.hM)) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U ∧
      Differentiable ℝ U ∧ Differentiable ℝ (deriv U) :=
  b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData
    p c lam M κ κtilde D Λ hcond hD hD_ge_one hΛ0 hpar

section AxiomAudit

#print axioms paperRouteAParamGreenCore
#print axioms PaperLocalRouteAStepParameters.toOrbitCore
#print axioms PaperLowerRawStepProducerRouteAParamCore.chi_nonpos
#print axioms PaperLowerRawParabolicFloorRouteAParamCoreNoBar.chi_nonpos
#print axioms slowLeftTrapProfile_mem_monotoneTrap
#print axioms slowLeftTrapProfile_not_expLeftRateData
#print axioms paperLowerRawParamRotheSeq
#print axioms paperLowerRawParamRotheSeqFromTrap
#print axioms paperLowerRawParamGreenSourceCompactness
#print axioms paperLowerRawParamOffDiagonalStepClosedGraph
#print axioms paperLowerRawParamRotheLimitClosedGraph
#print axioms paperLowerRawParamRotheContinuousDependence
#print axioms PaperLowerPinnedFlatFloor
#print axioms paperLowerPinned_stationary_of_modulusSchauder
#print axioms b1_chiNeg_existence_paper_routeA_paramCore_noBar_of_cubeApproxData
#print axioms b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData
#print axioms b1_chiNeg_existence_paper_routeA_paramCore_noBar
#print axioms b1_chiPos_existence_paper_routeA_paramCore_noBar

end AxiomAudit

end ShenWork.Paper1
