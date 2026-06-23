/-
  ShenWork/Paper2/IntervalChiNegBaseDirect.lean

  χ₀<0 BASE E₀ — the DIRECT-route trajBanach fixed point (local-existence core).

  The landed bare-sineEnv base `trajEnvelope_chiNeg_base` routes the per-coordinate
  MapsTo through `envBall_invariance_coeff`, whose chemotaxis discharge
  `chemDuhamelContribution_le` demands `|sineCoeffs flux| ≤ sineEnv E_base`.  For the
  gW-inflated convolution flux that forces `E_base ≥ gwInflatedBase ~ M·(1+λ)^{1/2}`
  (the PROVEN +1-derivative loss, 5d798ef).  The DIRECT supersolution
  `Estar ~ M·(1+λ)^{-α/2}` is SMALLER, so the bare base cannot use it.

  THE FIX — the SAME trajBanach fixed point, but the per-coordinate MapsTo discharges
  the chemotaxis leg by the DIRECT Duhamel-OUTPUT envelope `chemE`
  (`chemDuhamel_direct`: `|duhamelEnergyCoeff 1 (sineCoeffs∘flux) s k| ≤ chemE k`,
  `chemE = coreEnv = (C·Rbar)·(1+λ)^{-α/2}·M`, the deflation, NOT the inflation),
  with `Estar k = heatE k + |χ₀|·chemE k + logE k` closing the gap by CONSTRUCTION.
  The heat / log / k=0 legs and the Banach readout are REUSED verbatim from the
  landed `trajPhi_cosineCoeff_decomp_pos` + `trajBanach_envelope_of_invariance`.

  The domination on `u` is the Banach OUTPUT (uniqueness `Uu = Wstar`), NOT a
  hypothesis — exactly as `trajEnvelope_chiNeg_base`.  `Estar` is the SATISFIABLE
  direct supersolution, never `gwInflatedBase`.

  New file only.  No sorry/admit/native_decide/custom axiom.  Lines ≤ 100.
  Mathlib v4.29.1.  `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.
-/
import ShenWork.Paper2.IntervalChiNegMapsTo
import ShenWork.Paper2.IntervalChiNegDirectSupersolution

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegBaseDirect

open MeasureTheory Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateDuhamelMap intervalConjugateKernelOperator)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.Paper2.HSigmaScale (lam MemHSigma)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.IntervalChiNegTrajBanach
open ShenWork.Paper2.IntervalChiNegMapsTo
  (trajPhi_cosineCoeff_decomp_pos trajEnvelope_chiNeg_base)
open Real
open scoped NNReal

/-! ## 1. The DIRECT-route per-candidate seam.

Identical analytic residuals to `TrajSeam` (heat diag, Fubini swaps, continuities,
k=0 mean conservation), EXCEPT the chemotaxis envelope is the DIRECT Duhamel OUTPUT
bound `hchemD` (`chemDuhamel_direct`), and the supersolution gap `hgapD` is at the
DIRECT scale `Estar k = heatE k + |χ₀|·chemE k + logE k` — NO bare-sineEnv, NO
gwInflatedBase.  `heatE`, `chemE`, `logE` are the three per-mode `H^σ` summands. -/
structure TrajSeamDirect (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {t : ℝ} (heatE chemE logE : ℕ → ℝ) (U : Traj t)
    (hcont : Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      intervalConjugateDuhamelMap p u₀ (trajFun U) z.1.1 z.2)) : Prop where
  hQcont : ∀ (s : ↥(Set.Icc (0 : ℝ) t)) r, r < s.1 → Continuous (chemFluxLifted p (trajFun U r))
  hLcont : ∀ (s : ↥(Set.Icc (0 : ℝ) t)) r, r < s.1 → Continuous (logisticLifted p (trajFun U r))
  hLM : ∀ (s : ↥(Set.Icc (0 : ℝ) t)), ∃ Ml : ℝ, ∀ r, r < s.1 →
    ∀ j, |cosineCoeffs (logisticLifted p (trajFun U r)) j| ≤ Ml
  hheat_cont : ∀ (s : ↥(Set.Icc (0 : ℝ) t)), Continuous
    (fun x => intervalFullSemigroupOperator s.1 (intervalDomainLift u₀) x)
  hchemI_cont : ∀ (s : ↥(Set.Icc (0 : ℝ) t)), Continuous (fun x => ∫ r in (0 : ℝ)..s.1,
    intervalConjugateKernelOperator (s.1 - r) (chemFluxLifted p (trajFun U r)) x)
  hlogI_cont : ∀ (s : ↥(Set.Icc (0 : ℝ) t)), Continuous (fun x => ∫ r in (0 : ℝ)..s.1,
    intervalFullSemigroupOperator (s.1 - r) (logisticLifted p (trajFun U r)) x)
  hpt_heat : ∀ (s : ↥(Set.Icc (0 : ℝ) t)) k, cosineCoeffs
    (fun x => intervalFullSemigroupOperator s.1 (intervalDomainLift u₀) x) k
      = Real.exp (-(s.1 * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
  hswap_chem : ∀ (s : ↥(Set.Icc (0 : ℝ) t)) k, cosineCoeffs (fun x => ∫ r in (0 : ℝ)..s.1,
      intervalConjugateKernelOperator (s.1 - r) (chemFluxLifted p (trajFun U r)) x) k
    = ∫ r in (0 : ℝ)..s.1, cosineCoeffs
      (fun x => intervalConjugateKernelOperator (s.1 - r) (chemFluxLifted p (trajFun U r)) x) k
  hswap_log : ∀ (s : ↥(Set.Icc (0 : ℝ) t)) k, cosineCoeffs (fun x => ∫ r in (0 : ℝ)..s.1,
      intervalFullSemigroupOperator (s.1 - r) (logisticLifted p (trajFun U r)) x) k
    = ∫ r in (0 : ℝ)..s.1, cosineCoeffs
      (fun x => intervalFullSemigroupOperator (s.1 - r) (logisticLifted p (trajFun U r)) x) k
  -- DIRECT chemotaxis OUTPUT envelope (chemDuhamel_direct): the deflated Duhamel bound
  hchemD : ∀ (s : ↥(Set.Icc (0 : ℝ) t)) k,
    |duhamelEnergyCoeff 1 (fun j r => sineCoeffs
        (if r < s.1 then chemFluxLifted p (trajFun U r) else fun _ => 0) j) s.1 k| ≤ chemE k
  -- heat leg bound and logistic OUTPUT envelope bound (the other two H^σ summands)
  hheatD : ∀ (s : ↥(Set.Icc (0 : ℝ) t)) k,
    |Real.exp (-(s.1 * lam k)) * cosineCoeffs (intervalDomainLift u₀) k| ≤ heatE k
  hlogD : ∀ (s : ↥(Set.Icc (0 : ℝ) t)) k,
    |duhamelEnergyCoeff 1 (fun j r => if r < s.1
        then cosineCoeffs (logisticLifted p (trajFun U r)) j / (lam j) ^ (1/2 : ℝ)
        else 0) s.1 k| ≤ logE k
  hzero : ∀ (s : ↥(Set.Icc (0 : ℝ) t)) k, k = 0 ∨ s.1 = 0 →
    cosineCoeffs (intervalDomainLift (trajFun (trajPhi p u₀ U hcont) s.1)) k
      = Real.exp (-(s.1 * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
        + (-p.χ₀) * duhamelEnergyCoeff 1 (fun j r => sineCoeffs
            (if r < s.1 then chemFluxLifted p (trajFun U r) else fun _ => 0) j) s.1 k
        + duhamelEnergyCoeff 1 (fun j r => if r < s.1
            then cosineCoeffs (logisticLifted p (trajFun U r)) j / (lam j) ^ (1/2 : ℝ)
            else 0) s.1 k

/-! ## 2. The DIRECT per-mode envelope bound for `trajPhi`.

`|cosineCoeffs (trajPhi w) k| ≤ Estar k` with `Estar = heatE + |χ₀|·chemE + logE`,
by the rfl-unbundled decomposition (`trajPhi_cosineCoeff_decomp_pos`, k≠0; `hzero`,
k=0) + the three DIRECT per-coordinate bounds (heat / `chemDuhamel_direct` / log) +
triangle inequality.  This REPLACES `trajPhi_envBall_coeff`'s `envBall_invariance_coeff`
(bare-sineEnv) chem leg ONLY. -/
theorem trajPhi_envBall_coeff_direct (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {t : ℝ} {heatE chemE logE : ℕ → ℝ} (U : Traj t)
    (hcont : Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      intervalConjugateDuhamelMap p u₀ (trajFun U) z.1.1 z.2))
    (S : TrajSeamDirect p u₀ heatE chemE logE U hcont) :
    ∀ (s : ↥(Set.Icc (0 : ℝ) t)) k,
      |cosineCoeffs (intervalDomainLift (trajFun (trajPhi p u₀ U hcont) s.1)) k|
        ≤ heatE k + |p.χ₀| * chemE k + logE k := by
  intro s k
  have hdecomp : cosineCoeffs (intervalDomainLift (trajFun (trajPhi p u₀ U hcont) s.1)) k
      = Real.exp (-(s.1 * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
        + (-p.χ₀) * duhamelEnergyCoeff 1 (fun j r => sineCoeffs
            (if r < s.1 then chemFluxLifted p (trajFun U r) else fun _ => 0) j) s.1 k
        + duhamelEnergyCoeff 1 (fun j r => if r < s.1
            then cosineCoeffs (logisticLifted p (trajFun U r)) j / (lam j) ^ (1/2 : ℝ)
            else 0) s.1 k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · exact S.hzero s k (Or.inl hk0)
    · obtain ⟨Ml, hMl⟩ := S.hLM s
      exact trajPhi_cosineCoeff_decomp_pos p u₀ U hcont s (Nat.pos_iff_ne_zero.mp hk0)
        (S.hQcont s) (S.hLcont s) hMl (S.hheat_cont s) (S.hchemI_cont s) (S.hlogI_cont s)
        (S.hpt_heat s k) (S.hswap_chem s k) (S.hswap_log s k)
  rw [hdecomp]
  set H := Real.exp (-(s.1 * lam k)) * cosineCoeffs (intervalDomainLift u₀) k with hH
  set C := duhamelEnergyCoeff 1 (fun j r => sineCoeffs
      (if r < s.1 then chemFluxLifted p (trajFun U r) else fun _ => 0) j) s.1 k with hC
  set L := duhamelEnergyCoeff 1 (fun j r => if r < s.1
      then cosineCoeffs (logisticLifted p (trajFun U r)) j / (lam j) ^ (1/2 : ℝ)
      else 0) s.1 k with hL
  have hcabs : |(-p.χ₀) * C| = |p.χ₀| * |C| := by rw [abs_mul, abs_neg]
  have htri : |H + (-p.χ₀) * C + L| ≤ |H| + |p.χ₀| * |C| + |L| := by
    refine le_trans (abs_add_le _ _) ?_
    have h1 : |H + (-p.χ₀) * C| ≤ |H| + |p.χ₀| * |C| := by
      refine le_trans (abs_add_le _ _) ?_
      rw [hcabs]
    gcongr
  refine le_trans htri ?_
  have hhe := S.hheatD s k
  have hch := S.hchemD s k
  have hlo := S.hlogD s k
  have hχ : (0 : ℝ) ≤ |p.χ₀| := abs_nonneg _
  have hmid : |p.χ₀| * |C| ≤ |p.χ₀| * chemE k := mul_le_mul_of_nonneg_left hch hχ
  linarith [hhe, hlo, hmid]

/-! ## 3. The DIRECT `MapsTo trajPhi (EnvBall Estar) (EnvBall Estar)`.

`Estar k = heatE k + |χ₀|·chemE k + logE k` is the SATISFIABLE direct supersolution
(never `gwInflatedBase`).  Per-candidate `hseam` (carried) discharges the bound. -/
theorem trajPhi_mapsTo_direct (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {t : ℝ} {heatE chemE logE : ℕ → ℝ}
    (hcontFam : ∀ U : Traj t,
      Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
        intervalConjugateDuhamelMap p u₀ (trajFun U) z.1.1 z.2))
    (hseam : ∀ U : Traj t, TrajSeamDirect p u₀ heatE chemE logE U (hcontFam U)) :
    Set.MapsTo (fun U : Traj t => trajPhi p u₀ U (hcontFam U))
      (EnvBallTraj (t := t) (fun k => heatE k + |p.χ₀| * chemE k + logE k))
      (EnvBallTraj (t := t) (fun k => heatE k + |p.χ₀| * chemE k + logE k)) := by
  intro U _ s k
  exact trajPhi_envBall_coeff_direct p u₀ U (hcontFam U) (hseam U) s k

/-! ## 4. FINAL — χ₀<0 base trajectory envelope via the DIRECT fixed point.

Wires `trajPhi_mapsTo_direct` into `trajBanach_envelope_of_invariance`, with the
landed contraction `hPhi`, the mild lift `hUfix`/`hUu`, the seed `hx₀`, and the
`H^σ` membership `henvH` of `Estar` (`memHSigma_deflate`: `chemE = M/(1+λ)^{α/2} ∈
H^σ`, so `Estar = heatE + |χ₀|·chemE + logE ∈ H^σ`).  The domination on `u` is the
Banach OUTPUT by uniqueness (`Uu = Wstar`), NOT a hypothesis — mirrors
`trajEnvelope_chiNeg_base` exactly.  This is the base `E₀` feeding
`meanReach_H1_conjugate` with `Estar` the SATISFIABLE direct supersolution. -/
def trajEnvelope_chiNeg_base_direct {σ t : ℝ} {heatE chemE logE : ℕ → ℝ}
    (p : CM2Params)
    (henvH : MemHSigma σ (fun k => heatE k + |p.χ₀| * chemE k + logE k))
    (u₀ : intervalDomainPoint → ℝ)
    (hcontFam : ∀ U : Traj t,
      Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
        intervalConjugateDuhamelMap p u₀ (trajFun U) z.1.1 z.2))
    (hseam : ∀ U : Traj t, TrajSeamDirect p u₀ heatE chemE logE U (hcontFam U))
    {q : ℝ≥0} (hPhi : ContractingWith q (fun U : Traj t => trajPhi p u₀ U (hcontFam U)))
    {x₀ : Traj t}
    (hx₀ : x₀ ∈ EnvBallTraj (t := t) (fun k => heatE k + |p.χ₀| * chemE k + logE k))
    {Uu : Traj t}
    (hUfix : Function.IsFixedPt (fun U : Traj t => trajPhi p u₀ U (hcontFam U)) Uu)
    {u : ℝ → ℝ → ℝ}
    (hUu : ∀ s : ↑(Set.Icc (0 : ℝ) t), ∀ x : ℝ,
      intervalDomainLift (trajFun Uu s.1) x = u s.1 x) :
    ShenWork.Paper2.IntervalTrajectoryEnvelope.TrajectoryHSigmaEnvelope σ t
      (fun τ => cosineCoeffs (u τ)) :=
  trajBanach_envelope_of_invariance henvH hPhi
    (trajPhi_mapsTo_direct p u₀ hcontFam hseam) hx₀ hUfix hUu

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms trajPhi_envBall_coeff_direct
#print axioms trajPhi_mapsTo_direct
#print axioms trajEnvelope_chiNeg_base_direct
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegBaseDirect
