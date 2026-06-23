/-
  ShenWork/Paper2/IntervalChiNegTrajBridges.lean

  χ₀<0 — the Traj-BCF model bridges that close the local-existence interface of
  `chiNeg_base_envelope_unconditional` (IntervalChiNegUnconditional).

  Three bridges, each CONSUMING a landed lemma whose hypotheses are supplied:

   * G1  `trajPhi_hcontFam_of_legs` — the FULL `hcontFam` joint (τ,x)-continuity of
     `intervalConjugateDuhamelMap p u₀ (trajFun U)` on the box `[0,t] × Ω̄`,
     assembled from its three legs.  The chemotaxis leg is DERIVED here by wiring
     the landed `conjugateLeg_continuous_full` (IntervalChiNegTrajBanachFinal) with
     `F s = chemFluxLifted p (trajFun U s)`.  The homogeneous and logistic legs'
     joint continuity are CARRIED as the precise named hypotheses `hHom`/`hLog`
     (no landed full-box joint-continuity producer exists for them — see audit).

   * G2  `trajPhi_supLipschitz_of_pointwise` — the genuine sup-LIFT of a per-point
     Duhamel contraction to the BCF sup-metric
       `dist (trajPhi U₁) (trajPhi U₂) ≤ q · dist U₁ U₂`,
     via `ContinuousMap.dist_le` + the correspondence `trajPhi_apply`.  CONSUMES the
     pointwise bound `hpt` (the landed `intervalConjugateDuhamelMap_diff_bound_of_banked`
     shape, with `d = dist U₁ U₂`).

   * G3  `conjugatePicardLimit_trajLift_isFixedPt` — the trajPhi fixed point `Uu`
     (Banach, via the landed `chemMildLocal_contractionCore`) and its uniqueness
     identification slot.  The s>0 lift-identity is reduced to a single trajPhi
     fixed-point coincidence via the landed `fixedPoint_unique_traj`; the s=0
     endpoint (`conjugatePicardLimit … 0 = 0 ≠ trajFun Uu 0`) is the τ=0 convention,
     carried downstream (G4) — so the clean identity is stated on `Ioc 0 t`.

  DERIVED vs CARRIED is stated per bridge at each lemma.  No
  `sorry`/`admit`/`native_decide`/custom `axiom`.  Lines ≤ 100.  Mathlib v4.29.1.
-/
import ShenWork.Paper2.IntervalChiNegUnconditional
import ShenWork.Paper2.IntervalChiNegTrajBanachFinal
import ShenWork.Paper2.IntervalConjugatePicardBounds
import ShenWork.Paper2.ChemMildLocal
import ShenWork.Paper2.IntervalConjugatePicard

namespace ShenWork.Paper2.IntervalChiNegTrajBridges

open MeasureTheory Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator intervalConjugateDuhamelMap)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.Paper2.IntervalChiNegTrajBanach
open scoped NNReal

/-! ## G1 — the full `hcontFam` (chemotaxis leg DERIVED, other legs CARRIED). -/

/-- **G1 chemotaxis leg — DERIVED.**  The conjugate-kernel chemotaxis integral leg
of the Duhamel map, as a function of `(τ,x)` on the box, is continuous — by wiring
the landed `conjugateLeg_continuous_full` with `F s = chemFluxLifted p (trajFun U s)`
(jointly continuous, measurable, integrable, `CF`-bounded). -/
theorem trajChemLeg_continuous (p : CM2Params)
    {t : ℝ} (U : Traj t) {CF : ℝ} (hCF : 0 ≤ CF)
    (hF_meas : Measurable (Function.uncurry (fun s => chemFluxLifted p (trajFun U s))))
    (hF_cont : Continuous (Function.uncurry (fun s => chemFluxLifted p (trajFun U s))))
    (hF_int : ∀ s, Integrable (chemFluxLifted p (trajFun U s)) (intervalMeasure 1))
    (hF_bound : ∀ s y, |chemFluxLifted p (trajFun U s) y| ≤ CF) :
    Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      ∫ s in (0 : ℝ)..(z.1.1),
        intervalConjugateKernelOperator (z.1.1 - s)
          (chemFluxLifted p (trajFun U s)) z.2.1) :=
  ShenWork.Paper2.IntervalChiNegTrajBanachFinal.conjugateLeg_continuous_full
    hCF hF_meas hF_cont hF_int hF_bound

/-- **G1 assembly — full `hcontFam` (PARTIAL: hom/log legs CARRIED).**  The full
joint `(τ,x)`-continuity of `intervalConjugateDuhamelMap p u₀ (trajFun U)` on the
box, assembled from the three legs: the homogeneous leg `hHom`, the DERIVED
chemotaxis leg (scaled by the constant `-p.χ₀`), and the logistic leg `hLog`. -/
theorem trajPhi_hcontFam_of_legs (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {t : ℝ} (U : Traj t)
    (hHom : Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      intervalFullSemigroupOperator z.1.1 (intervalDomainLift u₀) z.2.1))
    (hChem : Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      ∫ s in (0 : ℝ)..(z.1.1),
        intervalConjugateKernelOperator (z.1.1 - s)
          (chemFluxLifted p (trajFun U s)) z.2.1))
    (hLog : Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      ∫ s in (0 : ℝ)..(z.1.1),
        intervalFullSemigroupOperator (z.1.1 - s)
          (logisticLifted p (trajFun U s)) z.2.1)) :
    Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      intervalConjugateDuhamelMap p u₀ (trajFun U) z.1.1 z.2) := by
  have heq : (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      intervalConjugateDuhamelMap p u₀ (trajFun U) z.1.1 z.2)
      = fun z => intervalFullSemigroupOperator z.1.1 (intervalDomainLift u₀) z.2.1
          + (-p.χ₀) * (∫ s in (0 : ℝ)..(z.1.1),
              intervalConjugateKernelOperator (z.1.1 - s)
                (chemFluxLifted p (trajFun U s)) z.2.1)
          + ∫ s in (0 : ℝ)..(z.1.1),
              intervalFullSemigroupOperator (z.1.1 - s)
                (logisticLifted p (trajFun U s)) z.2.1 := by
    funext z; rfl
  rw [heq]
  exact (hHom.add (continuous_const.mul hChem)).add hLog

/-! ## G2 — the sup-LIFT of a per-point Duhamel contraction to the BCF metric. -/

/-- **G2 — DERIVED sup-lift.**  Given the per-point Duhamel contraction `hpt`
(`|Duhamel U₁ − Duhamel U₂|(s,x) ≤ q · dist U₁ U₂` at every box point — the landed
`intervalConjugateDuhamelMap_diff_bound_of_banked` shape with `d = dist U₁ U₂`),
the BCF sup-metric distance is bounded:
`dist (trajPhi U₁) (trajPhi U₂) ≤ q · dist U₁ U₂`.  Pure sup-lift via
`ContinuousMap.dist_le` + the correspondence `trajPhi_apply`. -/
theorem trajPhi_supLipschitz_of_pointwise (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ} {t : ℝ} {q : ℝ} (hq : 0 ≤ q)
    {U₁ U₂ : Traj t}
    (hc₁ : Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      intervalConjugateDuhamelMap p u₀ (trajFun U₁) z.1.1 z.2))
    (hc₂ : Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      intervalConjugateDuhamelMap p u₀ (trajFun U₂) z.1.1 z.2))
    (hpt : ∀ z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint,
      |intervalConjugateDuhamelMap p u₀ (trajFun U₁) z.1.1 z.2
        - intervalConjugateDuhamelMap p u₀ (trajFun U₂) z.1.1 z.2|
        ≤ q * dist U₁ U₂) :
    dist (trajPhi p u₀ U₁ hc₁) (trajPhi p u₀ U₂ hc₂) ≤ q * dist U₁ U₂ := by
  rw [ContinuousMap.dist_le (by positivity)]
  intro z
  rw [trajPhi_apply, trajPhi_apply, Real.dist_eq]
  exact hpt z

/-! ## G3 — the trajPhi fixed point + the τ>0 lift-identity slot. -/

/-- **G3 — DERIVED fixed point.**  From `ContractingWith q trajPhi` (produced by G2
via `chiNeg_hPhi_of_lip`) the landed `chemMildLocal_contractionCore` delivers a
trajPhi fixed point `Uu`.  `Traj t` is a nonempty complete metric space. -/
theorem trajPhi_fixedPoint_exists {t : ℝ} {q : ℝ≥0}
    {Phi : Traj t → Traj t} (hPhi : ContractingWith q Phi) :
    ∃ Uu : Traj t, Function.IsFixedPt Phi Uu :=
  let ⟨Uu, hfix, _⟩ := ShenWork.Paper2.chemMildLocal_contractionCore hPhi (0 : Traj t)
  ⟨Uu, hfix⟩

/-- **G3 — DERIVED uniqueness identity (τ>0 form).**  If both the trajPhi fixed
point `Uu` AND a candidate `Vstar` are trajPhi fixed points, they coincide by the
landed `fixedPoint_unique_traj`.  Consumers identify `trajFun Uu` with
`conjugatePicardLimit p u₀ T` by supplying `Vstar = ` the BCF lift of
`conjugatePicardLimit` (a trajPhi fixed point on `(0,t]` by
`conjugatePicardLimit_is_mildSolution`); the resulting box equality, evaluated at
any `s ∈ Ioc 0 t`, gives the τ>0 lift-identity.  The `s = 0` endpoint is the τ=0
convention (`conjugatePicardLimit … 0 = 0`), carried downstream (G4). -/
theorem conjugatePicardLimit_trajLift_isFixedPt {t : ℝ} {q : ℝ≥0}
    {Phi : Traj t → Traj t} (hPhi : ContractingWith q Phi)
    {Uu Vstar : Traj t}
    (hUfix : Function.IsFixedPt Phi Uu) (hVfix : Function.IsFixedPt Phi Vstar)
    {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) t) (x : intervalDomainPoint) :
    Uu (⟨s, ⟨le_of_lt hs.1, hs.2⟩⟩, x) = Vstar (⟨s, ⟨le_of_lt hs.1, hs.2⟩⟩, x) := by
  rw [fixedPoint_unique_traj hPhi hUfix hVfix]

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms trajChemLeg_continuous
#print axioms trajPhi_hcontFam_of_legs
#print axioms trajPhi_supLipschitz_of_pointwise
#print axioms trajPhi_fixedPoint_exists
#print axioms conjugatePicardLimit_trajLift_isFixedPt
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegTrajBridges
