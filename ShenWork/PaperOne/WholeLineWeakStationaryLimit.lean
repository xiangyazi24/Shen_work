import ShenWork.PaperOne.WholeLineLongTimeLimit
import ShenWork.PaperOne.WholeLineMildMapConcreteContinuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.Filter.AtTopBot.Archimedean

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/-!
Weak stationary limit for the whole-line auxiliary flow.

This file records the weak-form route from the auxiliary parabolic orbit to the
long-time stationary profile.  The parabolic weak identity and the final
time-integrated dominated-convergence passage are named inputs; the order,
local-uniform, and whole-line resolvent/flux continuity pieces are consumed
from the existing bank.
-/

/-- Lightweight compactly supported one-dimensional weak test datum.  The
fields `phi'` and `phi''` are the first two test derivatives used in the weak
identity; compact support is recorded by a single radius. -/
structure WholeLineWeakTestFunction where
  phi : ℝ → ℝ
  phi' : ℝ → ℝ
  phi'' : ℝ → ℝ
  supportRadius : ℝ
  supportRadius_nonneg : 0 ≤ supportRadius
  phi_zero_of_radius :
    ∀ x, supportRadius < |x| → phi x = 0
  phi'_zero_of_radius :
    ∀ x, supportRadius < |x| → phi' x = 0
  phi''_zero_of_radius :
    ∀ x, supportRadius < |x| → phi'' x = 0

/-- Divergence-form weak stationary integrand for
`U_t = U_xx + c U_x - χ ∂x(U^m V_x) + U(1-U^α)`. -/
def wholeLineDivergenceWeakIntegrand
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ)
    (Φ : WholeLineWeakTestFunction) (x : ℝ) : ℝ :=
  U x * Φ.phi'' x - c * U x * Φ.phi' x
    + p.χ * wholeLineFlux p U x * Φ.phi' x
    + wholeLineReaction p U x * Φ.phi x

/-- The stationary weak functional against a compactly supported test datum. -/
def wholeLineStationaryWeakFunctional
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ)
    (Φ : WholeLineWeakTestFunction) : ℝ :=
  ∫ x : ℝ, wholeLineDivergenceWeakIntegrand p c U Φ x

/-- Explicit weak stationary solution statement used by this file. -/
def WholeLineWeakStationary
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ Φ : WholeLineWeakTestFunction,
    wholeLineStationaryWeakFunctional p c U Φ = 0

/-- Pairing of a time increment with the test function. -/
def wholeLineWeakIncrement
    (w : ℝ → ℝ → ℝ) (τ : ℝ)
    (Φ : WholeLineWeakTestFunction) (n : ℕ) : ℝ :=
  ∫ x : ℝ, (w ((n : ℝ) + τ) x - w (n : ℝ) x) * Φ.phi x

/-- Shifted time-integrated right-hand side in the parabolic weak identity. -/
def wholeLineTimeIntegratedWeakRHS
    (p : CMParams) (c : ℝ) (w : ℝ → ℝ → ℝ) (τ : ℝ)
    (Φ : WholeLineWeakTestFunction) (n : ℕ) : ℝ :=
  ∫ s in Icc (0 : ℝ) τ,
    ∫ x : ℝ,
      wholeLineDivergenceWeakIntegrand p c (fun y => w ((n : ℝ) + s) y) Φ x

/-- Time average of the weak right-hand side. -/
def wholeLineTimeAveragedWeakRHS
    (p : CMParams) (c : ℝ) (w : ℝ → ℝ → ℝ) (τ : ℝ)
    (Φ : WholeLineWeakTestFunction) (n : ℕ) : ℝ :=
  (1 / τ) * wholeLineTimeIntegratedWeakRHS p c w τ Φ n

/-- Named input: the genuine parabolic weak form of the auxiliary flow, already
integrated over the shifted window `[n,n+τ]`. -/
def WholeLineFlowWeakForm
    (p : CMParams) (c : ℝ) (w : ℝ → ℝ → ℝ) (τ : ℝ) : Prop :=
  ∀ n Φ,
    wholeLineWeakIncrement w τ Φ n =
      wholeLineTimeIntegratedWeakRHS p c w τ Φ n

/-- Named input: the endpoint increment vanishes along the long-time sequence. -/
def WholeLineWeakIncrementVanishes
    (w : ℝ → ℝ → ℝ) (τ : ℝ) : Prop :=
  ∀ Φ,
    Tendsto (fun n : ℕ => wholeLineWeakIncrement w τ Φ n)
      atTop (𝓝 0)

/--
Named dominated-convergence output for the shifted time-integrated weak
identity.  Its arguments are precisely the limit data produced by the preceding
bricks: local-uniform convergence of the orbit, the time-shift squeeze, and the
source convergence supplied by the Yukawa/flux and reaction continuity bank.
-/
def WholeLineTimeIntegratedWeakDCT
    (p : CMParams) (c : ℝ) (w : ℝ → ℝ → ℝ) (U : ℝ → ℝ) (τ : ℝ) : Prop :=
  ∀
    (_orbit_locunif :
      ShenWork.Paper1.LocallyUniformConverges
        (fun n x => w (n : ℝ) x) U)
    (_shift_locunif :
      ∀ R > 0, ∀ ε > 0,
        ∀ᶠ n : ℕ in atTop,
          ∀ s : ℝ, s ∈ Icc (0 : ℝ) τ →
            ∀ x : ℝ, x ∈ Icc (-R) R →
              |w ((n : ℝ) + s) x - U x| < ε)
    (_flux_locunif :
      ShenWork.Paper1.LocallyUniformConverges
        (fun n x => wholeLineFlux p (fun y => w (n : ℝ) y) x)
        (wholeLineFlux p U))
    (_reaction_locunif :
      ShenWork.Paper1.LocallyUniformConverges
        (fun n x => wholeLineReaction p (fun y => w (n : ℝ) y) x)
        (wholeLineReaction p U)),
      ∀ Φ,
        Tendsto
          (fun n : ℕ =>
            wholeLineTimeAveragedWeakRHS p c w τ Φ n)
          atTop
          (𝓝 (wholeLineStationaryWeakFunctional p c U Φ))

/-- Brick 9 plus the carried equi-Lipschitz input give local-uniform
convergence of integer-time slices to the long-time infimum profile. -/
theorem longtime_limit_locallyUniform
    {κ κt D Λ : ℝ} {w : ℝ → ℝ → ℝ}
    (htime : ∀ x, Antitone fun t : ℝ => w t x)
    (hlower : ∀ t x, lowerBarrier κ κt D x ≤ w t x)
    (hΛ : 0 ≤ Λ)
    (hw_lip : ∀ t x y, |w t x - w t y| ≤ Λ * |x - y|)
    (hU_lip :
      ∀ x y,
        |wholeLineLongTimeLimit w x - wholeLineLongTimeLimit w y|
          ≤ Λ * |x - y|) :
    ShenWork.Paper1.LocallyUniformConverges
      (fun n x => w (n : ℝ) x) (wholeLineLongTimeLimit w) := by
  have hpt :
      ∀ x,
        Tendsto (fun n : ℕ => w (n : ℝ) x) atTop
          (𝓝 (wholeLineLongTimeLimit w x)) := by
    intro x
    exact (wholeLine_longTime_limit_tendsto
      (κ := κ) (κt := κt) (D := D) (w := w)
      htime hlower x).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  exact ShenWork.Paper1.locallyUniform_of_pointwise_of_equiLipschitz
    hΛ hpt (fun n x y => hw_lip (n : ℝ) x y) hU_lip

/-- Order squeeze for shifted orbit slices. -/
theorem time_shift_squeeze
    {κ κt D : ℝ} {w : ℝ → ℝ → ℝ}
    (htime : ∀ x, Antitone fun t : ℝ => w t x)
    (hlower : ∀ t x, lowerBarrier κ κt D x ≤ w t x)
    {t s x : ℝ} (hs : 0 ≤ s) :
    wholeLineLongTimeLimit w x ≤ w (t + s) x ∧
      w (t + s) x ≤ w t x := by
  constructor
  · simpa [wholeLineLongTimeLimit] using
      (ciInf_le_of_le
        (wholeLine_longTime_bddBelow
          (κ := κ) (κt := κt) (D := D) (w := w) hlower x)
        (t + s) le_rfl)
  · exact htime x (by linarith : t ≤ t + s)

/-- The squeeze upgrades integer-time local-uniform convergence to local-uniform
convergence of all shifted slices `n+s`, uniformly for `s ∈ [0,τ]`. -/
theorem time_shift_locallyUniform
    {κ κt D τ : ℝ} {w : ℝ → ℝ → ℝ}
    (htime : ∀ x, Antitone fun t : ℝ => w t x)
    (hlower : ∀ t x, lowerBarrier κ κt D x ≤ w t x)
    (horbit :
      ShenWork.Paper1.LocallyUniformConverges
        (fun n x => w (n : ℝ) x) (wholeLineLongTimeLimit w)) :
    ∀ R > 0, ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ s : ℝ, s ∈ Icc (0 : ℝ) τ →
          ∀ x : ℝ, x ∈ Icc (-R) R →
            |w ((n : ℝ) + s) x - wholeLineLongTimeLimit w x| < ε := by
  intro R hR ε hε
  filter_upwards [horbit R hR ε hε] with n hn
  intro s hs x hx
  have hs0 : 0 ≤ s := hs.1
  have hsqueeze :=
    time_shift_squeeze
      (κ := κ) (κt := κt) (D := D) (w := w)
      htime hlower (t := (n : ℝ)) (s := s) (x := x) hs0
  have hbase :=
    time_shift_squeeze
      (κ := κ) (κt := κt) (D := D) (w := w)
      htime hlower (t := (n : ℝ)) (s := 0) (x := x) le_rfl
  rw [add_zero] at hbase
  rw [abs_of_nonneg (sub_nonneg.mpr hsqueeze.1)]
  calc
    w ((n : ℝ) + s) x - wholeLineLongTimeLimit w x
        ≤ w (n : ℝ) x - wholeLineLongTimeLimit w x := by
          linarith [hsqueeze.2]
    _ = |w (n : ℝ) x - wholeLineLongTimeLimit w x| := by
          rw [abs_of_nonneg (sub_nonneg.mpr hbase.1)]
    _ < ε := hn x hx

/-- Yukawa derivative continuity, in the concrete whole-line notation. -/
theorem yukawa_derivative_limit
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M)
    {seq : ℕ → ℝ → ℝ} {U : ℝ → ℝ}
    (hseq : ∀ n, ShenWork.Paper1.InConstantBarrierTrap M (seq n))
    (hU : ShenWork.Paper1.InConstantBarrierTrap M U)
    (hconv : ShenWork.Paper1.LocallyUniformConverges seq U) :
    ShenWork.Paper1.LocallyUniformConverges
      (fun n x =>
        deriv (wholeLineResolvent
          (fun y => (seq n y) ^ p.γ)) x)
      (fun x =>
        deriv (wholeLineResolvent
          (fun y => (U y) ^ p.γ)) x) :=
  ShenWork.Paper1.wholeLineResolventDeriv_source_locallyUniform_constantBarrier
    p hM hseq hU hconv

/-- Flux convergence, consuming the banked Yukawa derivative continuity. -/
theorem flux_limit
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M)
    {seq : ℕ → ℝ → ℝ} {U : ℝ → ℝ}
    (hseq : ∀ n, ShenWork.Paper1.InConstantBarrierTrap M (seq n))
    (hU : ShenWork.Paper1.InConstantBarrierTrap M U)
    (hconv : ShenWork.Paper1.LocallyUniformConverges seq U) :
    ShenWork.Paper1.LocallyUniformConverges
      (fun n x => wholeLineFlux p (seq n) x)
      (fun x => wholeLineFlux p U x) :=
  ShenWork.Paper1.wholeLineFlux_source_locallyUniform_constantBarrier
    p hM hseq hU hconv

/-- Reaction-source convergence on the trap. -/
theorem nonlinearity_limit
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M)
    {seq : ℕ → ℝ → ℝ} {U : ℝ → ℝ}
    (hseq : ∀ n, ShenWork.Paper1.InConstantBarrierTrap M (seq n))
    (hU : ShenWork.Paper1.InConstantBarrierTrap M U)
    (hconv : ShenWork.Paper1.LocallyUniformConverges seq U) :
    ShenWork.Paper1.LocallyUniformConverges
      (fun n x => wholeLineReaction p (seq n) x)
      (fun x => wholeLineReaction p U x) :=
  ShenWork.Paper1.wholeLineReaction_source_locallyUniform_constantBarrier
    p hM hseq hU hconv

/-- Limit passage through the time-integrated weak identity. -/
theorem weak_stationary_limit
    {p : CMParams} {c τ : ℝ} {w : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (_hτ : τ ≠ 0)
    (hweak : WholeLineFlowWeakForm p c w τ)
    (hinc : WholeLineWeakIncrementVanishes w τ)
    (hDCT :
      ∀ Φ,
        Tendsto
          (fun n : ℕ => wholeLineTimeAveragedWeakRHS p c w τ Φ n)
          atTop
          (𝓝 (wholeLineStationaryWeakFunctional p c U Φ))) :
    WholeLineWeakStationary p c U := by
  intro Φ
  have havg_zero :
      Tendsto
        (fun n : ℕ => wholeLineTimeAveragedWeakRHS p c w τ Φ n)
        atTop (𝓝 0) := by
    have hmul :
        Tendsto
          (fun n : ℕ => (1 / τ) * wholeLineWeakIncrement w τ Φ n)
          atTop (𝓝 0) := by
      simpa using ((hinc Φ).const_mul (1 / τ))
    refine Tendsto.congr' ?_ hmul
    refine Eventually.of_forall ?_
    intro n
    unfold wholeLineTimeAveragedWeakRHS
    change
      (1 / τ) * wholeLineWeakIncrement w τ Φ n =
        (1 / τ) * wholeLineTimeIntegratedWeakRHS p c w τ Φ n
    rw [← hweak n Φ]
  exact (tendsto_nhds_unique havg_zero (hDCT Φ)).symm

/--
Main weak stationary limit assembly.

The theorem consumes Brick 9 for the orbit limit, the squeeze for shifted
windows, the banked Yukawa/flux continuity, and reaction continuity.  The
actual parabolic weak form and the dominated-convergence theorem for the
time-integrated weak identity remain explicit named inputs.
-/
theorem wholeLine_longTime_weak_stationary
    {p : CMParams} {c τ κ κt D Λ M : ℝ} {w : ℝ → ℝ → ℝ}
    (hτ : τ ≠ 0)
    (htime : ∀ x, Antitone fun t : ℝ => w t x)
    (hlower : ∀ t x, lowerBarrier κ κt D x ≤ w t x)
    (hΛ : 0 ≤ Λ)
    (hw_lip : ∀ t x y, |w t x - w t y| ≤ Λ * |x - y|)
    (hU_lip :
      ∀ x y,
        |wholeLineLongTimeLimit w x - wholeLineLongTimeLimit w y|
          ≤ Λ * |x - y|)
    (hM : 0 ≤ M)
    (hseq_trap :
      ∀ n : ℕ,
        ShenWork.Paper1.InConstantBarrierTrap M
          (fun x => w (n : ℝ) x))
    (hU_trap :
      ShenWork.Paper1.InConstantBarrierTrap M
        (wholeLineLongTimeLimit w))
    (hweak : WholeLineFlowWeakForm p c w τ)
    (hinc : WholeLineWeakIncrementVanishes w τ)
    (hDCT :
      WholeLineTimeIntegratedWeakDCT p c w (wholeLineLongTimeLimit w) τ) :
    WholeLineWeakStationary p c (wholeLineLongTimeLimit w) := by
  have horbit :
      ShenWork.Paper1.LocallyUniformConverges
        (fun n x => w (n : ℝ) x) (wholeLineLongTimeLimit w) :=
    longtime_limit_locallyUniform
      (κ := κ) (κt := κt) (D := D) (Λ := Λ) (w := w)
      htime hlower hΛ hw_lip hU_lip
  have hshift :
      ∀ R > 0, ∀ ε > 0,
        ∀ᶠ n : ℕ in atTop,
          ∀ s : ℝ, s ∈ Icc (0 : ℝ) τ →
            ∀ x : ℝ, x ∈ Icc (-R) R →
              |w ((n : ℝ) + s) x - wholeLineLongTimeLimit w x| < ε :=
    time_shift_locallyUniform
      (κ := κ) (κt := κt) (D := D) (τ := τ) (w := w)
      htime hlower horbit
  have hflux :
      ShenWork.Paper1.LocallyUniformConverges
        (fun n x => wholeLineFlux p (fun y => w (n : ℝ) y) x)
        (wholeLineFlux p (wholeLineLongTimeLimit w)) :=
    flux_limit p hM hseq_trap hU_trap horbit
  have hreaction :
      ShenWork.Paper1.LocallyUniformConverges
        (fun n x => wholeLineReaction p (fun y => w (n : ℝ) y) x)
        (wholeLineReaction p (wholeLineLongTimeLimit w)) :=
    nonlinearity_limit p hM hseq_trap hU_trap horbit
  exact weak_stationary_limit
    (p := p) (c := c) (τ := τ) (w := w)
    (U := wholeLineLongTimeLimit w)
    hτ hweak hinc (hDCT horbit hshift hflux hreaction)

#print axioms longtime_limit_locallyUniform
#print axioms time_shift_squeeze
#print axioms time_shift_locallyUniform
#print axioms yukawa_derivative_limit
#print axioms flux_limit
#print axioms nonlinearity_limit
#print axioms weak_stationary_limit
#print axioms wholeLine_longTime_weak_stationary

end ShenWork.PaperOne
