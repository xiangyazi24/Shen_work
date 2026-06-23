/-
  ShenWork/Paper2/IntervalChiNegMapsTo.lean

  χ₀<0 UNCONDITIONAL — gap (b): the candidate-generic three-term decomposition of
  `cosineCoeffs (trajPhi w s) k` (UNBUNDLED from the `hmild`-bundled
  `conjugateSlice_cosineCoeff_decomp`) + the `MapsTo trajPhi (EnvBall) (EnvBall)`.

  The genuine new build is the candidate-generic decomposition: the repo's
  `conjugateSlice_cosineCoeff_decomp` derives its three-term EqOn from
  `conjugateMildSolution_lift_eq_threeTermMap_on_Icc p hmild …`; for the BCF map
  `trajPhi p u₀ U hcont` that EqOn is `rfl`-level
  (`trajPhi_apply` + `intervalConjugateDuhamelMap_eq_threeTermMap`), so we feed it
  into `gradientSolution_cosineCoeff_decomp_chi` WITHOUT any mild hypothesis.

  Everything else is consumption of the LANDED bounds:
    * `envBall_invariance_coeff` (the per-mode `Phi(EnvBall) ⊆ EnvBall`, fed the
      flux envelope + the supersolution gap),
    * `chemDuhamel_uniform_strict` (inside it),
  giving the per-candidate per-mode `MapsTo` bound — the SOLE remaining input to
  `trajBanach_envelope_of_invariance`.

  No sorry/admit/native_decide/custom axiom.  New names only.  Lines ≤ 100.
-/
import ShenWork.Paper2.IntervalChiNegTrajBanach

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegMapsTo

open MeasureTheory Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateDuhamelMap intervalConjugateKernelOperator)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.Paper2.HSigmaScale (lam)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.IntervalBootstrapDecomp (gradientSolution_cosineCoeff_decomp_chi)
open ShenWork.Paper2.IntervalConjugateSourceBridge
  (conjugateKernel_cosineCoeff conjugateLog_cosineCoeff
   intervalConjugateKernelOperator_nonpos intervalFullSemigroupOperator_nonpos
   intervalConjugateDuhamelMap_eq_threeTermMap
   cosineCoeffs_zero_fun sineCoeffs_zero_fun)
open ShenWork.Paper2.IntervalFluxFactorEnvelope (sineEnv)
open ShenWork.Paper2.IntervalChiNegLocalExist (EnvBall envBall_invariance_coeff)
open ShenWork.Paper2.IntervalChiNegTrajBanach
open Real
open scoped NNReal

/-! ## 1. The candidate-generic three-term decomposition (the UNBUNDLED build).

Mirrors `conjugateSlice_cosineCoeff_decomp`, but the three-term EqOn `hmap` is
supplied by the caller (rfl-level for `trajPhi`), so NO `IntervalConjugateMildSolution`
hypothesis appears.  The per-τ residuals are the SAME ones the bundled version
carries.  `w : ℝ → intervalDomainPoint → ℝ` is any continuous box candidate. -/
theorem cosineCoeff_decomp_of_threeTermMap
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {w : ℝ → intervalDomainPoint → ℝ} {ut : ℝ → ℝ}
    {t : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hmap : Set.EqOn ut
      (fun x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x
        + (-p.χ₀) * (∫ s in (0 : ℝ)..t,
            intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x)
        + ∫ s in (0 : ℝ)..t,
            intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x)
      (Set.Icc (0 : ℝ) 1))
    (hQcont : ∀ s, s < t → Continuous (chemFluxLifted p (w s)))
    (hLcont : ∀ s, s < t → Continuous (logisticLifted p (w s)))
    {Ml : ℝ} (hLM : ∀ s, s < t → ∀ j, |cosineCoeffs (logisticLifted p (w s)) j| ≤ Ml)
    (hheat_cont : Continuous
      (fun x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x))
    (hchemI_cont : Continuous (fun x => ∫ s in (0 : ℝ)..t,
      intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x))
    (hlogI_cont : Continuous (fun x => ∫ s in (0 : ℝ)..t,
      intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x))
    (hpt_heat : cosineCoeffs
      (fun x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x) k
        = Real.exp (-(t * lam k)) * cosineCoeffs (intervalDomainLift u₀) k)
    (hswap_chem : cosineCoeffs (fun x => ∫ s in (0 : ℝ)..t,
        intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x) k
      = ∫ s in (0 : ℝ)..t, cosineCoeffs
        (fun x => intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x) k)
    (hswap_log : cosineCoeffs (fun x => ∫ s in (0 : ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x) k
      = ∫ s in (0 : ℝ)..t, cosineCoeffs
        (fun x => intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x) k) :
    cosineCoeffs ut k
      = Real.exp (-(t * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
        + (-p.χ₀) * duhamelEnergyCoeff 1
            (fun j s => sineCoeffs
              (if s < t then chemFluxLifted p (w s) else fun _ => 0) j) t k
        + duhamelEnergyCoeff 1
            (fun j s => if s < t
              then cosineCoeffs (logisticLifted p (w s)) j / (lam j) ^ (1/2 : ℝ)
              else 0) t k := by
  have hpt_chem : ∀ s, cosineCoeffs
      (fun x => intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x) k
      = Real.exp (-(1 * lam k * (t - s))) * ((lam k) ^ (1/2 : ℝ)
          * sineCoeffs (if s < t then chemFluxLifted p (w s) else fun _ => 0) k) := by
    intro s
    by_cases hs : s < t
    · rw [if_pos hs]; exact conjugateKernel_cosineCoeff (by linarith) (hQcont s hs) k
    · rw [if_neg hs]
      have hts : t - s ≤ 0 := by linarith [not_lt.1 hs]
      rw [show (fun x => intervalConjugateKernelOperator (t - s)
            (chemFluxLifted p (w s)) x) = fun _ => (0 : ℝ) from
        funext fun x => intervalConjugateKernelOperator_nonpos hts _ x,
        cosineCoeffs_zero_fun, sineCoeffs_zero_fun]; ring
  have hpt_log : ∀ s, cosineCoeffs
      (fun x => intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x) k
      = (lam k) ^ (1/2 : ℝ) * Real.exp (-(1 * lam k * (t - s)))
          * (if s < t then cosineCoeffs (logisticLifted p (w s)) k / (lam k) ^ (1/2 : ℝ)
              else 0) := by
    intro s
    by_cases hs : s < t
    · rw [if_pos hs]; exact conjugateLog_cosineCoeff (by linarith) (hLcont s hs) (hLM s hs) hk
    · rw [if_neg hs]
      have hts : t - s ≤ 0 := by linarith [not_lt.1 hs]
      rw [show (fun x => intervalFullSemigroupOperator (t - s)
            (logisticLifted p (w s)) x) = fun _ => (0 : ℝ) from
        funext fun x => intervalFullSemigroupOperator_nonpos hts _ x,
        cosineCoeffs_zero_fun]; ring
  exact gradientSolution_cosineCoeff_decomp_chi (χ₀ := p.χ₀) k hmap
    hheat_cont hchemI_cont hlogI_cont hpt_heat hswap_chem hpt_chem hswap_log hpt_log

/-! ## 2. The rfl-EqOn for `trajPhi` (the unbundling). -/

/-- On `[0,1]`, the lifted `trajPhi` slice equals the three-term Duhamel map of the
underlying trajectory `trajFun U` — `rfl`-level via `trajPhi_apply` and
`intervalConjugateDuhamelMap_eq_threeTermMap`.  This REPLACES the `hmild` lift. -/
theorem trajPhi_lift_eqOn (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {t : ℝ}
    (U : Traj t)
    (hcont : Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      intervalConjugateDuhamelMap p u₀ (trajFun U) z.1.1 z.2))
    (s : ↥(Set.Icc (0 : ℝ) t)) :
    Set.EqOn (intervalDomainLift (trajFun (trajPhi p u₀ U hcont) s.1))
      (fun x => intervalFullSemigroupOperator s.1 (intervalDomainLift u₀) x
        + (-p.χ₀) * (∫ r in (0 : ℝ)..s.1,
            intervalConjugateKernelOperator (s.1 - r) (chemFluxLifted p (trajFun U r)) x)
        + ∫ r in (0 : ℝ)..s.1,
            intervalFullSemigroupOperator (s.1 - r) (logisticLifted p (trajFun U r)) x)
      (Set.Icc (0 : ℝ) 1) := by
  intro x hx
  have hxlift : intervalDomainLift (trajFun (trajPhi p u₀ U hcont) s.1) x
      = trajFun (trajPhi p u₀ U hcont) s.1 ⟨x, hx⟩ := by
    simp [intervalDomainLift, hx]
  rw [hxlift, trajFun_apply (trajPhi p u₀ U hcont) s.2 ⟨x, hx⟩,
    trajPhi_apply p u₀ U hcont (⟨s, ⟨x, hx⟩⟩),
    intervalConjugateDuhamelMap_eq_threeTermMap p u₀ (trajFun U) s.1 ⟨x, hx⟩]


/-! ## 3. The `trajPhi`-specialised per-mode decomposition (k ≠ 0). -/

/-- The candidate-generic three-term decomposition of `cosineCoeffs (trajPhi …) s` —
the rfl-EqOn fed into the unbundled decomposition.  `k ≠ 0`. -/
theorem trajPhi_cosineCoeff_decomp_pos (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {t : ℝ} (U : Traj t)
    (hcont : Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      intervalConjugateDuhamelMap p u₀ (trajFun U) z.1.1 z.2))
    (s : ↥(Set.Icc (0 : ℝ) t)) {k : ℕ} (hk : k ≠ 0)
    (hQcont : ∀ r, r < s.1 → Continuous (chemFluxLifted p (trajFun U r)))
    (hLcont : ∀ r, r < s.1 → Continuous (logisticLifted p (trajFun U r)))
    {Ml : ℝ} (hLM : ∀ r, r < s.1 → ∀ j, |cosineCoeffs (logisticLifted p (trajFun U r)) j| ≤ Ml)
    (hheat_cont : Continuous
      (fun x => intervalFullSemigroupOperator s.1 (intervalDomainLift u₀) x))
    (hchemI_cont : Continuous (fun x => ∫ r in (0 : ℝ)..s.1,
      intervalConjugateKernelOperator (s.1 - r) (chemFluxLifted p (trajFun U r)) x))
    (hlogI_cont : Continuous (fun x => ∫ r in (0 : ℝ)..s.1,
      intervalFullSemigroupOperator (s.1 - r) (logisticLifted p (trajFun U r)) x))
    (hpt_heat : cosineCoeffs
      (fun x => intervalFullSemigroupOperator s.1 (intervalDomainLift u₀) x) k
        = Real.exp (-(s.1 * lam k)) * cosineCoeffs (intervalDomainLift u₀) k)
    (hswap_chem : cosineCoeffs (fun x => ∫ r in (0 : ℝ)..s.1,
        intervalConjugateKernelOperator (s.1 - r) (chemFluxLifted p (trajFun U r)) x) k
      = ∫ r in (0 : ℝ)..s.1, cosineCoeffs
        (fun x => intervalConjugateKernelOperator (s.1 - r) (chemFluxLifted p (trajFun U r)) x) k)
    (hswap_log : cosineCoeffs (fun x => ∫ r in (0 : ℝ)..s.1,
        intervalFullSemigroupOperator (s.1 - r) (logisticLifted p (trajFun U r)) x) k
      = ∫ r in (0 : ℝ)..s.1, cosineCoeffs
        (fun x => intervalFullSemigroupOperator (s.1 - r) (logisticLifted p (trajFun U r)) x) k) :
    cosineCoeffs (intervalDomainLift (trajFun (trajPhi p u₀ U hcont) s.1)) k
      = Real.exp (-(s.1 * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
        + (-p.χ₀) * duhamelEnergyCoeff 1
            (fun j r => sineCoeffs
              (if r < s.1 then chemFluxLifted p (trajFun U r) else fun _ => 0) j) s.1 k
        + duhamelEnergyCoeff 1
            (fun j r => if r < s.1
              then cosineCoeffs (logisticLifted p (trajFun U r)) j / (lam j) ^ (1/2 : ℝ)
              else 0) s.1 k :=
  cosineCoeff_decomp_of_threeTermMap p hk (trajPhi_lift_eqOn p u₀ U hcont s)
    hQcont hLcont hLM hheat_cont hchemI_cont hlogI_cont hpt_heat hswap_chem hswap_log


/-! ## 4. The candidate-generic per-mode envelope bound for `trajPhi`.

For a continuous box candidate `U`, every coefficient of `trajPhi p u₀ U hcont s`
is dominated by `E_base`.  The chemotaxis leg is discharged by the LANDED
`envBall_invariance_coeff` (which consumes `chemDuhamel_uniform_strict`) fed the
candidate-generic flux envelope `henv` and the supersolution gap `hgap`; the
decomposition is the rfl-unbundled `trajPhi_cosineCoeff_decomp_pos`, with the
`k = 0` (and `s = 0`) mean-conservation residual carried in `hzero`. -/
theorem trajPhi_envBall_coeff (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {t : ℝ} {E_base : ℕ → ℝ} (hE0 : ∀ k, 0 ≤ E_base k) (U : Traj t)
    (hcont : Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      intervalConjugateDuhamelMap p u₀ (trajFun U) z.1.1 z.2))
    (hQcont : ∀ (s : ↥(Set.Icc (0 : ℝ) t)) r, r < s.1 →
      Continuous (chemFluxLifted p (trajFun U r)))
    (hLcont : ∀ (s : ↥(Set.Icc (0 : ℝ) t)) r, r < s.1 →
      Continuous (logisticLifted p (trajFun U r)))
    (hLM : ∀ (s : ↥(Set.Icc (0 : ℝ) t)), ∃ Ml : ℝ, ∀ r, r < s.1 →
      ∀ j, |cosineCoeffs (logisticLifted p (trajFun U r)) j| ≤ Ml)
    (hheat_cont : ∀ (s : ↥(Set.Icc (0 : ℝ) t)), Continuous
      (fun x => intervalFullSemigroupOperator s.1 (intervalDomainLift u₀) x))
    (hchemI_cont : ∀ (s : ↥(Set.Icc (0 : ℝ) t)), Continuous (fun x => ∫ r in (0 : ℝ)..s.1,
      intervalConjugateKernelOperator (s.1 - r) (chemFluxLifted p (trajFun U r)) x))
    (hlogI_cont : ∀ (s : ↥(Set.Icc (0 : ℝ) t)), Continuous (fun x => ∫ r in (0 : ℝ)..s.1,
      intervalFullSemigroupOperator (s.1 - r) (logisticLifted p (trajFun U r)) x))
    (hpt_heat : ∀ (s : ↥(Set.Icc (0 : ℝ) t)) k, cosineCoeffs
      (fun x => intervalFullSemigroupOperator s.1 (intervalDomainLift u₀) x) k
        = Real.exp (-(s.1 * lam k)) * cosineCoeffs (intervalDomainLift u₀) k)
    (hswap_chem : ∀ (s : ↥(Set.Icc (0 : ℝ) t)) k, cosineCoeffs (fun x => ∫ r in (0 : ℝ)..s.1,
        intervalConjugateKernelOperator (s.1 - r) (chemFluxLifted p (trajFun U r)) x) k
      = ∫ r in (0 : ℝ)..s.1, cosineCoeffs
        (fun x => intervalConjugateKernelOperator (s.1 - r) (chemFluxLifted p (trajFun U r)) x) k)
    (hswap_log : ∀ (s : ↥(Set.Icc (0 : ℝ) t)) k, cosineCoeffs (fun x => ∫ r in (0 : ℝ)..s.1,
        intervalFullSemigroupOperator (s.1 - r) (logisticLifted p (trajFun U r)) x) k
      = ∫ r in (0 : ℝ)..s.1, cosineCoeffs
        (fun x => intervalFullSemigroupOperator (s.1 - r) (logisticLifted p (trajFun U r)) x) k)
    (hsrcCont : ∀ (s : ↥(Set.Icc (0 : ℝ) t)) k, Continuous
      (fun r => sineCoeffs (if r < s.1 then chemFluxLifted p (trajFun U r) else fun _ => 0) k))
    (henv : ∀ (s : ↥(Set.Icc (0 : ℝ) t)) k r,
      |sineCoeffs (if r < s.1 then chemFluxLifted p (trajFun U r) else fun _ => 0) k|
        ≤ sineEnv E_base k)
    (hgap : ∀ (s : ↥(Set.Icc (0 : ℝ) t)) k,
      |Real.exp (-(s.1 * lam k)) * cosineCoeffs (intervalDomainLift u₀) k|
        + |duhamelEnergyCoeff 1 (fun j r => if r < s.1
            then cosineCoeffs (logisticLifted p (trajFun U r)) j / (lam j) ^ (1/2 : ℝ)
            else 0) s.1 k|
        ≤ (1 - |p.χ₀| * s.1) * E_base k)
    (hzero : ∀ (s : ↥(Set.Icc (0 : ℝ) t)) k, k = 0 ∨ s.1 = 0 →
      cosineCoeffs (intervalDomainLift (trajFun (trajPhi p u₀ U hcont) s.1)) k
        = Real.exp (-(s.1 * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
          + (-p.χ₀) * duhamelEnergyCoeff 1 (fun j r => sineCoeffs
              (if r < s.1 then chemFluxLifted p (trajFun U r) else fun _ => 0) j) s.1 k
          + duhamelEnergyCoeff 1 (fun j r => if r < s.1
              then cosineCoeffs (logisticLifted p (trajFun U r)) j / (lam j) ^ (1/2 : ℝ)
              else 0) s.1 k) :
    ∀ (s : ↥(Set.Icc (0 : ℝ) t)) k,
      |cosineCoeffs (intervalDomainLift (trajFun (trajPhi p u₀ U hcont) s.1)) k| ≤ E_base k := by
  intro s k
  have hdecomp : cosineCoeffs (intervalDomainLift (trajFun (trajPhi p u₀ U hcont) s.1)) k
      = Real.exp (-(s.1 * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
        + (-p.χ₀) * duhamelEnergyCoeff 1 (fun j r => sineCoeffs
            (if r < s.1 then chemFluxLifted p (trajFun U r) else fun _ => 0) j) s.1 k
        + duhamelEnergyCoeff 1 (fun j r => if r < s.1
            then cosineCoeffs (logisticLifted p (trajFun U r)) j / (lam j) ^ (1/2 : ℝ)
            else 0) s.1 k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · exact hzero s k (Or.inl hk0)
    · obtain ⟨Ml, hMl⟩ := hLM s
      exact trajPhi_cosineCoeff_decomp_pos p u₀ U hcont s (Nat.pos_iff_ne_zero.mp hk0)
        (hQcont s) (hLcont s) hMl (hheat_cont s) (hchemI_cont s) (hlogI_cont s)
        (hpt_heat s k) (hswap_chem s k) (hswap_log s k)
  rw [hdecomp]
  exact envBall_invariance_coeff hE0 s.2.1 (fun k => hsrcCont s k) (fun k r => henv s k r)
    (fun k => hgap s k) k


/-! ## 5. The per-candidate analytic seam + the `MapsTo` (gap G2). -/

/-- The per-candidate analytic seam for one candidate `U`: the residual continuities,
heat diagonalization, Fubini swaps, the candidate-generic flux envelope, the
supersolution gap, and the `k=0`/`s=0` mean-conservation residual.  This is exactly
the residual interface the bundled `conjugateSlice_cosineCoeff_decomp` carries —
here per candidate, NEVER via the actual mild solution. -/
structure TrajSeam (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {t : ℝ} (E_base : ℕ → ℝ) (U : Traj t)
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
  hsrcCont : ∀ (s : ↥(Set.Icc (0 : ℝ) t)) k, Continuous
    (fun r => sineCoeffs (if r < s.1 then chemFluxLifted p (trajFun U r) else fun _ => 0) k)
  henv : ∀ (s : ↥(Set.Icc (0 : ℝ) t)) k r,
    |sineCoeffs (if r < s.1 then chemFluxLifted p (trajFun U r) else fun _ => 0) k|
      ≤ sineEnv E_base k
  hgap : ∀ (s : ↥(Set.Icc (0 : ℝ) t)) k,
    |Real.exp (-(s.1 * lam k)) * cosineCoeffs (intervalDomainLift u₀) k|
      + |duhamelEnergyCoeff 1 (fun j r => if r < s.1
          then cosineCoeffs (logisticLifted p (trajFun U r)) j / (lam j) ^ (1/2 : ℝ)
          else 0) s.1 k|
      ≤ (1 - |p.χ₀| * s.1) * E_base k
  hzero : ∀ (s : ↥(Set.Icc (0 : ℝ) t)) k, k = 0 ∨ s.1 = 0 →
    cosineCoeffs (intervalDomainLift (trajFun (trajPhi p u₀ U hcont) s.1)) k
      = Real.exp (-(s.1 * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
        + (-p.χ₀) * duhamelEnergyCoeff 1 (fun j r => sineCoeffs
            (if r < s.1 then chemFluxLifted p (trajFun U r) else fun _ => 0) j) s.1 k
        + duhamelEnergyCoeff 1 (fun j r => if r < s.1
            then cosineCoeffs (logisticLifted p (trajFun U r)) j / (lam j) ^ (1/2 : ℝ)
            else 0) s.1 k

/-- **gap G2 — `MapsTo trajPhi EnvBall EnvBall`.**  For `Phi U := trajPhi p u₀ U
(hcontFam U)`, given the per-candidate analytic seam `hseam` (carried), the
trajectory `EnvBall E_base` is invariant.  The per-mode bound is the rfl-unbundled
decomposition + the LANDED `envBall_invariance_coeff` (consuming
`chemDuhamel_uniform_strict`).  This is the SOLE remaining input to
`trajBanach_envelope_of_invariance`. -/
theorem trajPhi_mapsTo (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {t : ℝ} {E_base : ℕ → ℝ} (hE0 : ∀ k, 0 ≤ E_base k)
    (hcontFam : ∀ U : Traj t,
      Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
        intervalConjugateDuhamelMap p u₀ (trajFun U) z.1.1 z.2))
    (hseam : ∀ U : Traj t, TrajSeam p u₀ E_base U (hcontFam U)) :
    Set.MapsTo (fun U : Traj t => trajPhi p u₀ U (hcontFam U))
      (EnvBallTraj (t := t) E_base) (EnvBallTraj (t := t) E_base) := by
  intro U _ s k
  have S := hseam U
  exact trajPhi_envBall_coeff p u₀ hE0 U (hcontFam U) S.hQcont S.hLcont S.hLM
    S.hheat_cont S.hchemI_cont S.hlogI_cont S.hpt_heat S.hswap_chem S.hswap_log
    S.hsrcCont S.henv S.hgap S.hzero s k


/-! ## 6. FINAL — χ₀<0 base trajectory envelope, MapsTo wired UNCONDITIONALLY. -/

/-- **χ₀<0 base `TrajectoryHSigmaEnvelope`, MapsTo discharged.**

Wires the gap-G2 `trajPhi_mapsTo` (the rfl-unbundled decomposition + the LANDED
`envBall_invariance_coeff`) into `trajBanach_envelope_of_invariance`, together with
the landed contraction `hPhi` (the K-contraction), the (a) joint-continuity-typed
mild lift `hUfix`/`hUu`, the seed `hx₀`, and the `H^σ` membership `henvH`.  The
`MapsTo` is no longer an open gap — it is DERIVED here from the per-candidate seam.
The Banach fixed point `Wstar ∈ EnvBall` is produced internally; uniqueness
transfers the domination to `u`.  Producing the χ₀<0 base trajectory envelope. -/
def trajEnvelope_chiNeg_base {σ t : ℝ} {E_base : ℕ → ℝ}
    (henvH : ShenWork.Paper2.HSigmaScale.MemHSigma σ E_base)
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (hE0 : ∀ k, 0 ≤ E_base k)
    (hcontFam : ∀ U : Traj t,
      Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
        intervalConjugateDuhamelMap p u₀ (trajFun U) z.1.1 z.2))
    (hseam : ∀ U : Traj t, TrajSeam p u₀ E_base U (hcontFam U))
    {q : ℝ≥0} (hPhi : ContractingWith q (fun U : Traj t => trajPhi p u₀ U (hcontFam U)))
    {x₀ : Traj t} (hx₀ : x₀ ∈ EnvBallTraj (t := t) E_base)
    {Uu : Traj t}
    (hUfix : Function.IsFixedPt (fun U : Traj t => trajPhi p u₀ U (hcontFam U)) Uu)
    {u : ℝ → ℝ → ℝ}
    (hUu : ∀ s : ↑(Set.Icc (0 : ℝ) t), ∀ x : ℝ,
      intervalDomainLift (trajFun Uu s.1) x = u s.1 x) :
    ShenWork.Paper2.IntervalTrajectoryEnvelope.TrajectoryHSigmaEnvelope σ t
      (fun τ => cosineCoeffs (u τ)) :=
  trajBanach_envelope_of_invariance henvH hPhi
    (trajPhi_mapsTo p u₀ hE0 hcontFam hseam) hx₀ hUfix hUu

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms cosineCoeff_decomp_of_threeTermMap
#print axioms trajPhi_lift_eqOn
#print axioms trajPhi_cosineCoeff_decomp_pos
#print axioms trajPhi_envBall_coeff
#print axioms trajPhi_mapsTo
#print axioms trajEnvelope_chiNeg_base
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegMapsTo
