/-
  ShenWork/Paper2/IntervalDecompTauLift.lean

  R1b — the τ-LIFT of the landed per-endpoint cosine-coefficient decomposition.

  The landed `conjugateSlice_cosineCoeff_decomp` (IntervalConjugateSourceBridge)
  is already a statement about ONE endpoint `t`, of the exact 3-term
  `duhamelEnergyCoeff` shape, but with the source legs CUT OFF at the endpoint
  (`if s < t then … else 0`) — the cutoff is forced because the per-τ kernel
  identities only hold for positive elapsed time `t − s > 0`, i.e. `s < t`.

  This file PROMOTES that single-endpoint result to a τ-UNIFORM statement
  `∀ τ ∈ Icc 0 t, ∀ k, …` of the EXACT shape `TrajLadderData.hdecomp` consumes,
  for the conjugate mild solution, with the τ-INDEPENDENT raw source families
      `Q τ  = chemFluxLifted p (u τ)`,
      `Fl k τ = cosineCoeffs (logisticLifted p (u τ)) k / √λ_k`.
  The lift instantiates the landed endpoint decomposition at each `τ` (endpoint
  `:= τ`) and CONVERTS the endpoint-cut source legs to the raw families inside the
  `[0,τ]` Duhamel integral — the cut and the raw integrands differ only at the
  single point `s = τ` (Lebesgue-null), so the `duhamelEnergyCoeff` integrals
  agree (`intervalIntegral.integral_congr_ae` + `Real.volume_singleton`).

  ## What is closed vs carried (honest accounting)

  * UNCONDITIONALLY closed (given the conjugate mild solution and the per-`τ`
    analytic residuals that the LANDED endpoint decomposition already carries):
    the τ-uniform decomposition for every mode `k ≠ 0`.
  * CARRIED as explicit ∀-`τ`-indexed hypotheses (NOT faked): the per-`τ` Fubini
    swaps, source continuities, logistic coefficient bound, spatial continuities
    and heat diagonalization — these are exactly the residuals already carried in
    the landed per-endpoint interface, here required uniformly in the endpoint.
  * The `k = 0` mode is a GENUINE residual: `√λ₀ = 0` collapses BOTH engine
    coefficients to `0` (the `lam k ^ (1/2)` prefactor in `duhamelModeCoeff`
    vanishes), so the shape at `k = 0` is the mean-conservation identity
    `cosineCoeffs (u τ) 0 = û₀ 0`, which the logistic reaction does NOT satisfy in
    general.  It is therefore carried as the explicit hypothesis `hzero` and
    reported precisely, NOT hidden.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.
-/
import ShenWork.Paper2.IntervalConjugateSourceBridge

noncomputable section

namespace ShenWork.Paper2.IntervalDecompTauLift

open MeasureTheory
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator IntervalConjugateMildSolution)
open ShenWork.IntervalConjugatePicard
open ShenWork.Paper2.HSigmaScale (lam)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.BFormHSigmaDuhamelMode (duhamelModeCoeff)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.IntervalConjugateSourceBridge (conjugateSlice_cosineCoeff_decomp)
open Real

/-! ## Cutoff → raw single-point reconciliation for `duhamelEnergyCoeff`. -/

/-- For positive endpoint `τ`, the `k`-th Duhamel energy coefficient of an
endpoint-cut source family `G` (i.e. `G k s = H k s` whenever `s < τ`) equals
that of the raw family `H`.  The two integrands of `duhamelModeCoeff` over
`[0,τ]` agree for `s < τ`, hence a.e. on `uIoc 0 τ = Ioc 0 τ` (they may differ
only at the single point `s = τ`, which is Lebesgue-null). -/
theorem duhamelEnergyCoeff_endpointCut_eq {τ : ℝ} (hτ : 0 < τ)
    {G H : ℕ → ℝ → ℝ} (k : ℕ) (hagree : ∀ s, s < τ → G k s = H k s) :
    duhamelEnergyCoeff 1 G τ k = duhamelEnergyCoeff 1 H τ k := by
  unfold duhamelEnergyCoeff duhamelModeCoeff
  refine intervalIntegral.integral_congr_ae ?_
  have huIoc_eq : Set.uIoc (0:ℝ) τ = Set.Ioc (0:ℝ) τ := Set.uIoc_of_le hτ.le
  have hae_ne : ∀ᵐ s ∂volume, s ≠ τ := by
    have heq : {s : ℝ | ¬ s ≠ τ} = {τ} := by ext s; simp [eq_comm]
    rw [MeasureTheory.ae_iff, heq]; exact Real.volume_singleton
  filter_upwards [hae_ne] with s hsne hs_mem
  rw [huIoc_eq] at hs_mem
  have hslt : s < τ := lt_of_le_of_ne hs_mem.2 hsne
  rw [hagree s hslt]

/-! ## R1b — the τ-uniform decomposition for the conjugate mild solution. -/

/-- The raw (τ-independent) chemotaxis flux source family of the conjugate mild
solution: `Q s = chemFluxLifted p (u s)`.  Its sine coefficients are the
`hdecomp`/envelope chemotaxis source. -/
def conjQ (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ) : ℝ → ℝ :=
  chemFluxLifted p (u s)

/-- The raw (τ-independent) logistic source family of the conjugate mild
solution: `Fl k s = cosineCoeffs (logisticLifted p (u s)) k / √λ_k` (the
`√λ`-stripped logistic coefficient; at `k = 0` the value is irrelevant since the
`duhamelModeCoeff` prefactor `√λ₀ = 0`). -/
def conjFl (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  cosineCoeffs (logisticLifted p (u s)) k / (lam k) ^ (1/2 : ℝ)

/-- **R1b — τ-uniform 3-term Duhamel decomposition for the conjugate mild
solution, mode `k ≠ 0`.**

For each `τ ∈ (0,t]`, the `k`-th cosine coefficient (`k ≠ 0`) of the lifted slice
`intervalDomainLift (u τ)` decomposes in the EXACT `TrajLadderData.hdecomp` shape
with `û₀ = cosineCoeffs (intervalDomainLift u₀)`, raw sources `conjQ`/`conjFl`,
`χ₀ = p.χ₀`.  This is the landed `conjugateSlice_cosineCoeff_decomp` at endpoint
`τ`, with the endpoint-cut source legs converted to the raw families inside the
`[0,τ]` Duhamel integral (single-point reconciliation).

The per-`τ` analytic residuals (continuities, Fubini swaps, heat diagonalization,
logistic coefficient bound) are the SAME residuals the landed endpoint
decomposition carries, here supplied uniformly in the endpoint `τ`. -/
theorem conjugateSlice_decomp_tauLift_pos
    (p : CM2Params) {T : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hmild : IntervalConjugateMildSolution p T u₀ u)
    {t : ℝ} (htT : t ≤ T)
    -- per-endpoint analytic residuals, uniform in the endpoint τ ∈ (0,t]
    (hQcont : ∀ τ, 0 < τ → ∀ s, s < τ → Continuous (chemFluxLifted p (u s)))
    (hLcont : ∀ τ, 0 < τ → ∀ s, s < τ → Continuous (logisticLifted p (u s)))
    (hLM : ∀ τ, 0 < τ → ∃ Ml : ℝ, ∀ s, s < τ → ∀ j,
      |cosineCoeffs (logisticLifted p (u s)) j| ≤ Ml)
    (hheat_cont : ∀ τ, 0 < τ → Continuous
      (fun x => intervalFullSemigroupOperator τ (intervalDomainLift u₀) x))
    (hchemI_cont : ∀ τ, 0 < τ → Continuous (fun x => ∫ s in (0:ℝ)..τ,
      intervalConjugateKernelOperator (τ - s) (chemFluxLifted p (u s)) x))
    (hlogI_cont : ∀ τ, 0 < τ → Continuous (fun x => ∫ s in (0:ℝ)..τ,
      intervalFullSemigroupOperator (τ - s) (logisticLifted p (u s)) x))
    (hpt_heat : ∀ τ, 0 < τ → ∀ k, cosineCoeffs
      (fun x => intervalFullSemigroupOperator τ (intervalDomainLift u₀) x) k
        = Real.exp (-(τ * lam k)) * cosineCoeffs (intervalDomainLift u₀) k)
    (hswap_chem : ∀ τ, 0 < τ → ∀ k, cosineCoeffs (fun x => ∫ s in (0:ℝ)..τ,
        intervalConjugateKernelOperator (τ - s) (chemFluxLifted p (u s)) x) k
      = ∫ s in (0:ℝ)..τ, cosineCoeffs
        (fun x => intervalConjugateKernelOperator (τ - s) (chemFluxLifted p (u s)) x) k)
    (hswap_log : ∀ τ, 0 < τ → ∀ k, cosineCoeffs (fun x => ∫ s in (0:ℝ)..τ,
        intervalFullSemigroupOperator (τ - s) (logisticLifted p (u s)) x) k
      = ∫ s in (0:ℝ)..τ, cosineCoeffs
        (fun x => intervalFullSemigroupOperator (τ - s) (logisticLifted p (u s)) x) k)
    {τ : ℝ} (hτ0 : 0 < τ) (hτt : τ ≤ t) {k : ℕ} (hk : k ≠ 0) :
    cosineCoeffs (intervalDomainLift (u τ)) k
      = Real.exp (-(τ * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
        + (-p.χ₀) * duhamelEnergyCoeff 1
            (fun k τ => sineCoeffs (conjQ p u τ) k) τ k
        + duhamelEnergyCoeff 1 (conjFl p u) τ k := by
  obtain ⟨Ml, hMl⟩ := hLM τ hτ0
  -- the landed endpoint decomposition at endpoint τ (endpoint-cut sources)
  have hdec := conjugateSlice_cosineCoeff_decomp p hmild hτ0 (le_trans hτt htT) hk
    (hQcont τ hτ0) (hLcont τ hτ0) hMl (hheat_cont τ hτ0) (hchemI_cont τ hτ0)
    (hlogI_cont τ hτ0) (hpt_heat τ hτ0 k) (hswap_chem τ hτ0 k) (hswap_log τ hτ0 k)
  rw [hdec]
  -- convert the two endpoint-cut Duhamel coefficients to the raw families
  have hchemEq : duhamelEnergyCoeff 1
      (fun j s => sineCoeffs (if s < τ then chemFluxLifted p (u s) else fun _ => 0) j) τ k
        = duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (conjQ p u τ) k) τ k :=
    duhamelEnergyCoeff_endpointCut_eq hτ0 k (fun s hs => by rw [if_pos hs]; rfl)
  have hlogEq : duhamelEnergyCoeff 1
      (fun j s => if s < τ
        then cosineCoeffs (logisticLifted p (u s)) j / (lam j) ^ (1/2 : ℝ) else 0) τ k
        = duhamelEnergyCoeff 1 (conjFl p u) τ k :=
    duhamelEnergyCoeff_endpointCut_eq hτ0 k (fun s hs => by rw [if_pos hs]; rfl)
  rw [hchemEq, hlogEq]

/-- **R1b — the full τ-uniform `hdecomp`, including `k = 0`.**

Combines `conjugateSlice_decomp_tauLift_pos` (every `k ≠ 0`) with the carried
`k = 0` mean-conservation residual `hzero` to produce the EXACT
`TrajLadderData.hdecomp` field `∀ τ ∈ Icc 0 t, ∀ k, …` for the conjugate mild
solution (`u := fun τ => intervalDomainLift (u τ)`,
`û₀ := cosineCoeffs (intervalDomainLift u₀)`, `Q := conjQ`, `Fl := conjFl`,
`χ₀ := p.χ₀`).

`hzero` is the GENUINE `k = 0` residual: both engine coefficients vanish there
(`√λ₀ = 0`), so the shape forces `cosineCoeffs (u τ) 0 = û₀ 0` — the spatial-mean
conservation the logistic reaction does not satisfy in general; it is carried, not
faked.  The `τ = 0` endpoint of `Icc 0 t` is also routed through `hzero` for all
`k` (at `τ = 0` the kernel identities degenerate; see note below). -/
theorem conjugateSlice_decomp_tauLift
    (p : CM2Params) {T : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hmild : IntervalConjugateMildSolution p T u₀ u)
    {t : ℝ} (htT : t ≤ T)
    (hQcont : ∀ τ, 0 < τ → ∀ s, s < τ → Continuous (chemFluxLifted p (u s)))
    (hLcont : ∀ τ, 0 < τ → ∀ s, s < τ → Continuous (logisticLifted p (u s)))
    (hLM : ∀ τ, 0 < τ → ∃ Ml : ℝ, ∀ s, s < τ → ∀ j,
      |cosineCoeffs (logisticLifted p (u s)) j| ≤ Ml)
    (hheat_cont : ∀ τ, 0 < τ → Continuous
      (fun x => intervalFullSemigroupOperator τ (intervalDomainLift u₀) x))
    (hchemI_cont : ∀ τ, 0 < τ → Continuous (fun x => ∫ s in (0:ℝ)..τ,
      intervalConjugateKernelOperator (τ - s) (chemFluxLifted p (u s)) x))
    (hlogI_cont : ∀ τ, 0 < τ → Continuous (fun x => ∫ s in (0:ℝ)..τ,
      intervalFullSemigroupOperator (τ - s) (logisticLifted p (u s)) x))
    (hpt_heat : ∀ τ, 0 < τ → ∀ k, cosineCoeffs
      (fun x => intervalFullSemigroupOperator τ (intervalDomainLift u₀) x) k
        = Real.exp (-(τ * lam k)) * cosineCoeffs (intervalDomainLift u₀) k)
    (hswap_chem : ∀ τ, 0 < τ → ∀ k, cosineCoeffs (fun x => ∫ s in (0:ℝ)..τ,
        intervalConjugateKernelOperator (τ - s) (chemFluxLifted p (u s)) x) k
      = ∫ s in (0:ℝ)..τ, cosineCoeffs
        (fun x => intervalConjugateKernelOperator (τ - s) (chemFluxLifted p (u s)) x) k)
    (hswap_log : ∀ τ, 0 < τ → ∀ k, cosineCoeffs (fun x => ∫ s in (0:ℝ)..τ,
        intervalFullSemigroupOperator (τ - s) (logisticLifted p (u s)) x) k
      = ∫ s in (0:ℝ)..τ, cosineCoeffs
        (fun x => intervalFullSemigroupOperator (τ - s) (logisticLifted p (u s)) x) k)
    -- the carried k = 0 (and τ = 0) mean-conservation residual
    (hzero : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
      (k = 0 ∨ τ = 0) → cosineCoeffs (intervalDomainLift (u τ)) k
        = Real.exp (-(τ * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
          + (-p.χ₀) * duhamelEnergyCoeff 1
              (fun k τ => sineCoeffs (conjQ p u τ) k) τ k
          + duhamelEnergyCoeff 1 (conjFl p u) τ k) :
    ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
      cosineCoeffs (intervalDomainLift (u τ)) k
        = Real.exp (-(τ * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
          + (-p.χ₀) * duhamelEnergyCoeff 1
              (fun k τ => sineCoeffs (conjQ p u τ) k) τ k
          + duhamelEnergyCoeff 1 (conjFl p u) τ k := by
  intro τ hτ k
  rcases eq_or_lt_of_le hτ.1 with hτ0 | hτ0
  · exact hzero τ hτ k (Or.inr hτ0.symm)
  · rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · exact hzero τ hτ k (Or.inl hk0)
    · exact conjugateSlice_decomp_tauLift_pos p hmild htT hQcont hLcont hLM
        hheat_cont hchemI_cont hlogI_cont hpt_heat hswap_chem hswap_log
        hτ0 hτ.2 (Nat.pos_iff_ne_zero.mp hk0)

#print axioms duhamelEnergyCoeff_endpointCut_eq
#print axioms conjugateSlice_decomp_tauLift_pos
#print axioms conjugateSlice_decomp_tauLift

end ShenWork.Paper2.IntervalDecompTauLift
