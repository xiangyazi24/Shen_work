/-
  ShenWork/Paper2/IntervalChiNegGwInvariance.lean

  chi0<0 PDE-crux REFRAME -- the gW-INFLATED candidate-generic envelope-ball
  invariance.  The full flux `chemFluxLifted = weight*gradient/denom` needs the
  gW-INFLATED flux envelope `trueCosProd (gW E Gden) (sineEnv E)` (the genv output),
  NOT the bare `sineEnv E`.  This file reframes the landed `envBall_invariance_coeff`
  to that envelope, by ABSORBING the gW factor into a single INFLATED base sequence
  `gwInflatedBase E Gden` whose `sineEnv` IS EXACTLY the gW-inflated envelope (at
  every divergence mode k>=1) -- so the LANDED chemDuhamel strictness
  (`chemDuhamel_uniform_strict`, the sqrt(lam_k) cancellation) and the LANDED
  `envBall_invariance_coeff` apply VERBATIM at the inflated base.

  ## DERIVED-NEW here (axiom-clean)
  * `gwInflatedBase` -- the inflated base, `Ehat_k = trueCosProd (gW E Gden)
    (sineEnv E) k * (1+lam k)/sqrt(lam k)` (k>=1), `Ehat_0 = 0`.
  * `sineEnv_gwInflatedBase_pos` -- `sineEnv (gwInflatedBase E Gden) k
    = trueCosProd (gW E Gden) (sineEnv E) k` for k>=1.  THE bridge: the divergence
    `sqrt(lam_k)` of `sineEnv` cancels the kernel `1/sqrt(lam_k)` at the SAME mode,
    after the gW weight has been pushed into the inflated coefficient.
  * `henv_gwInflated` -- the gW-inflated flux envelope (from genv) RE-FRAMED as a
    bare-sineEnv envelope at the inflated base (k=0 by `sineCoeffs_zero`; k>=1 by the
    bridge).
  * `envBall_invariance_coeff_gw` -- the gW-INFLATED candidate-generic invariance:
    `|sineCoeffs (Q s) k| <= trueCosProd (gW E Gden)(sineEnv E) k` (genv) + the
    inflated-base supersolution gap => the three-term Duhamel image stays in
    `EnvBall (gwInflatedBase E Gden)`, via LANDED `envBall_invariance_coeff` at Ehat.
  * `trajEnvelope_chiNeg_gw` -- the gW-route chi0<0 `TrajectoryHSigmaEnvelope`,
    DERIVED through the base-generic `trajBanach_envelope_of_invariance` at `Ehat`.

  ## CARRIED -- the genuine PDE-crux residual (PRECISE, never faked)
  The gW factor is a CONVOLUTION (`trueCosProd` = Cauchy product of `gW` against
  `sineEnv`), NOT a pointwise scalar multiple.  Hence the C_gw uniform-in-k bound
  `gwInflatedBase E Gden k <= C_gw * E_base k` is the H^sigma Banach-algebra DECAY
  condition on the convolution, NOT a scalar inflation; it is `MemHSigma`-typed
  through `hEhatH`.  The supersolution / contraction / mild-lift inputs of
  `trajBanach_envelope_of_invariance` are threaded as EXPLICIT inputs at `Ehat`.
  No sorry/admit/native_decide/custom axiom.
-/
import ShenWork.Paper2.IntervalChiNegMapsTo
import ShenWork.Paper2.IntervalGWProductEnvelope
import ShenWork.Paper2.IntervalChiNegTrajBanach

open scoped Topology NNReal

noncomputable section

open Real Set
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HSigmaScale (lam lam_nonneg one_add_lam_pos MemHSigma resolverCoeff)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalFluxFactorEnvelope (sineEnv)
open ShenWork.Paper2.IntervalGWProductEnvelope (gW)
open ShenWork.Paper2.IntervalWienerAlgebra (trueCosProd)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs sineCoeffs_zero)
open ShenWork.Paper2.IntervalChiNegLocalExist (EnvBall envBall_invariance_coeff)

namespace ShenWork.Paper2.IntervalChiNegGwInvariance

/-! ## 1. The gW-inflated base whose `sineEnv` IS the gW-inflated flux envelope. -/

/-- **The gW-inflated base sequence.**  `Ehat_k` is defined so that
`sineEnv Ehat k = trueCosProd (gW E Gden) (sineEnv E) k` (k>=1): it divides the
gW-inflated envelope by the `sineEnv` multiplier `sqrt(lam_k)/(1+lam_k)`; at `k=0`
(where `lam_0 = 0`, the divergence/chemotaxis mode vanishes) it is `0`. -/
def gwInflatedBase (E Gden : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0
  else trueCosProd (gW E Gden) (sineEnv E) k * ((1 + lam k) / Real.sqrt (lam k))

/-- **THE BRIDGE (DERIVED), positive modes.**  `sineEnv (gwInflatedBase E Gden) k`
equals the gW-inflated flux envelope for `k>=1`: the inflation `(1+lam_k)/sqrt(lam_k)`
is exactly the inverse of the `sineEnv` multiplier `sqrt(lam_k)/(1+lam_k)`. -/
theorem sineEnv_gwInflatedBase_pos (E Gden : ℕ → ℝ) {k : ℕ} (hk : 0 < k) :
    sineEnv (gwInflatedBase E Gden) k = trueCosProd (gW E Gden) (sineEnv E) k := by
  have hlam : 0 < lam k := by
    have : 0 < (k : ℝ) := by exact_mod_cast hk
    simp only [lam, unitIntervalCosineEigenvalue]; positivity
  have hsl : 0 < Real.sqrt (lam k) := Real.sqrt_pos.mpr hlam
  have hkne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
  have hden : (0:ℝ) < 1 + lam k := one_add_lam_pos k
  have hsq : Real.sqrt (lam k) * Real.sqrt (lam k) = lam k := Real.mul_self_sqrt hlam.le
  rw [sineEnv, resolverCoeff, gwInflatedBase, if_neg hkne]
  field_simp

/-- `gwInflatedBase E Gden 0 = 0`. -/
@[simp] theorem gwInflatedBase_zero (E Gden : ℕ → ℝ) : gwInflatedBase E Gden 0 = 0 := by
  simp [gwInflatedBase]

/-- `sineEnv (gwInflatedBase E Gden) 0 = 0` (the divergence mode vanishes). -/
@[simp] theorem sineEnv_gwInflatedBase_zero (E Gden : ℕ → ℝ) :
    sineEnv (gwInflatedBase E Gden) 0 = 0 := by
  have hlam0 : lam 0 = 0 := by
    simp [lam, unitIntervalCosineEigenvalue]
  simp [sineEnv, resolverCoeff, hlam0]

/-- The inflated base is nonnegative provided the gW-inflated envelope is. -/
theorem gwInflatedBase_nonneg {E Gden : ℕ → ℝ}
    (hpos : ∀ k, 0 ≤ trueCosProd (gW E Gden) (sineEnv E) k) (k : ℕ) :
    0 ≤ gwInflatedBase E Gden k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hlam : 0 < lam k := by
      have : 0 < (k : ℝ) := by exact_mod_cast hk
      simp only [lam, unitIntervalCosineEigenvalue]; positivity
    have hsl : 0 < Real.sqrt (lam k) := Real.sqrt_pos.mpr hlam
    have hden : (0:ℝ) < 1 + lam k := one_add_lam_pos k
    have hkne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
    simp only [gwInflatedBase, if_neg hkne]
    have := hpos k; positivity

/-! ## 2. The gW-inflated flux envelope re-framed at the inflated base. -/

/-- **The gW-inflated flux envelope, re-framed.**  A divergence flux source
`Qsrc k s = sineCoeffs (Q s) k` bounded by the gW-inflated envelope (genv) at every
mode is bounded by `sineEnv (gwInflatedBase E Gden) k`: k=0 by `sineCoeffs_zero`
(the divergence mode vanishes), k>=1 by the bridge. -/
theorem henv_gwInflated {E Gden : ℕ → ℝ} {Q : ℝ → ℝ → ℝ}
    (hgenv : ∀ k s, |sineCoeffs (Q s) k| ≤ trueCosProd (gW E Gden) (sineEnv E) k)
    (k : ℕ) (s : ℝ) :
    |sineCoeffs (Q s) k| ≤ sineEnv (gwInflatedBase E Gden) k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [sineEnv_gwInflatedBase_zero, sineCoeffs_zero, abs_zero]
  · rw [sineEnv_gwInflatedBase_pos E Gden hk]; exact hgenv k s

/-! ## 3. The gW-INFLATED candidate-generic envelope-ball invariance. -/

/-- **gW-inflated candidate-generic envelope-ball invariance.**  Identical to the
landed `envBall_invariance_coeff` but with the gW-INFLATED flux envelope: the
divergence flux source `Q s` is bounded by the genv envelope
`trueCosProd (gW E Gden) (sineEnv E) k` at every mode (`hgenv`); the three-term
Duhamel image stays in the INFLATED ball `EnvBall (gwInflatedBase E Gden)`, with the
supersolution gap stated at the inflated base.  This consumes the landed
`envBall_invariance_coeff` at `Ehat := gwInflatedBase E Gden`: the genv envelope is
re-framed to `sineEnv Ehat` by `henv_gwInflated` (the bridge), so the LANDED
sqrt(lam_k)-cancellation strictness carries the gW-inflated flux VERBATIM. -/
theorem envBall_invariance_coeff_gw {E Gden : ℕ → ℝ}
    (hpos : ∀ k, 0 ≤ trueCosProd (gW E Gden) (sineEnv E) k)
    {δ χ₀ : ℝ} (hδ : 0 ≤ δ) {u0hat : ℕ → ℝ} {Q : ℝ → ℝ → ℝ} {flLeg : ℕ → ℝ}
    (hcont : ∀ k, Continuous (fun s => sineCoeffs (Q s) k))
    (hgenv : ∀ k s, |sineCoeffs (Q s) k| ≤ trueCosProd (gW E Gden) (sineEnv E) k)
    (hgap : ∀ k, |Real.exp (-(δ * lam k)) * u0hat k| + |flLeg k|
      ≤ (1 - |χ₀| * δ) * gwInflatedBase E Gden k) :
    EnvBall (gwInflatedBase E Gden)
      (fun k => Real.exp (-(δ * lam k)) * u0hat k
        + (-χ₀) * duhamelEnergyCoeff 1 (fun k s => sineCoeffs (Q s) k) δ k + flLeg k) :=
  envBall_invariance_coeff (gwInflatedBase_nonneg hpos) hδ hcont
    (fun k s => henv_gwInflated hgenv k s) hgap

/-! ## 4. The gW-route chi0<0 TrajectoryHSigmaEnvelope (base-generic Banach). -/

open ShenWork.Paper2.IntervalChiNegMapsTo (TrajSeam trajPhi_mapsTo)
open ShenWork.Paper2.IntervalChiNegTrajBanach
  (Traj trajPhi trajFun EnvBallTraj trajBanach_envelope_of_invariance)
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateDuhamelMap)

/-- **gW-route `MapsTo trajPhi (EnvBall Ehat)`.**  Instantiates the base-generic
`trajPhi_mapsTo` at the INFLATED base `Ehat := gwInflatedBase E Gden`.  The per-
candidate seam's flux-envelope field `henv : |sineCoeffs (flux) k| <= sineEnv Ehat k`
IS the gW-inflated genv envelope `trueCosProd (gW E Gden)(sineEnv E) k` (k>=1, via the
bridge `sineEnv_gwInflatedBase_pos`; k=0 vanishing) -- so the seam carried here is
exactly the gW-inflated flux seam.  No bare-sineEnv mis-framing. -/
theorem trajPhi_mapsTo_gw {E Gden : ℕ → ℝ}
    (hpos : ∀ k, 0 ≤ trueCosProd (gW E Gden) (sineEnv E) k)
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {t : ℝ}
    (hcontFam : ∀ U : Traj t,
      Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
        intervalConjugateDuhamelMap p u₀ (trajFun U) z.1.1 z.2))
    (hseam : ∀ U : Traj t, TrajSeam p u₀ (gwInflatedBase E Gden) U (hcontFam U)) :
    Set.MapsTo (fun U : Traj t => trajPhi p u₀ U (hcontFam U))
      (EnvBallTraj (t := t) (gwInflatedBase E Gden))
      (EnvBallTraj (t := t) (gwInflatedBase E Gden)) :=
  trajPhi_mapsTo p u₀ (gwInflatedBase_nonneg hpos) hcontFam hseam

/-- **The gW-route chi0<0 `TrajectoryHSigmaEnvelope`.**  DERIVED through the
base-generic `trajBanach_envelope_of_invariance` at the INFLATED base
`Ehat := gwInflatedBase E Gden`.  The genuine PDE-crux residual is `hEhatH :
MemHSigma σ Ehat` -- the H^sigma Banach-algebra DECAY of the convolution
`trueCosProd (gW E Gden)(sineEnv E) * (1+lam)/sqrt(lam)` (the precise C_gw
uniform-in-k condition, CARRIED, not faked).  The MapsTo (gW-inflated flux seam),
contraction `hPhi`, seed `hx0`, mild lift `hUfix`/`hUu` are EXPLICIT inputs; the
Banach fixed point in the inflated ball is produced internally and uniqueness
transfers domination to `u` (the conclusion stays an OUTPUT). -/
def trajEnvelope_chiNeg_gw {σ t : ℝ} {E Gden : ℕ → ℝ}
    (hpos : ∀ k, 0 ≤ trueCosProd (gW E Gden) (sineEnv E) k)
    (hEhatH : MemHSigma σ (gwInflatedBase E Gden))
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (hcontFam : ∀ U : Traj t,
      Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
        intervalConjugateDuhamelMap p u₀ (trajFun U) z.1.1 z.2))
    (hseam : ∀ U : Traj t, TrajSeam p u₀ (gwInflatedBase E Gden) U (hcontFam U))
    {q : ℝ≥0} (hPhi : ContractingWith q (fun U : Traj t => trajPhi p u₀ U (hcontFam U)))
    {x₀ : Traj t} (hx₀ : x₀ ∈ EnvBallTraj (t := t) (gwInflatedBase E Gden))
    {Uu : Traj t}
    (hUfix : Function.IsFixedPt (fun U : Traj t => trajPhi p u₀ U (hcontFam U)) Uu)
    {u : ℝ → ℝ → ℝ}
    (hUu : ∀ s : ↑(Set.Icc (0 : ℝ) t), ∀ x : ℝ,
      intervalDomainLift (trajFun Uu s.1) x = u s.1 x) :
    ShenWork.Paper2.IntervalTrajectoryEnvelope.TrajectoryHSigmaEnvelope σ t
      (fun τ => cosineCoeffs (u τ)) :=
  trajBanach_envelope_of_invariance hEhatH hPhi
    (trajPhi_mapsTo_gw hpos p u₀ hcontFam hseam) hx₀ hUfix hUu

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms gwInflatedBase
#print axioms sineEnv_gwInflatedBase_pos
#print axioms henv_gwInflated
#print axioms envBall_invariance_coeff_gw
#print axioms trajPhi_mapsTo_gw
#print axioms trajEnvelope_chiNeg_gw
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegGwInvariance
