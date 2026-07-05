/-
  ShenWork/Wiener/EWA/SourceChiNegUniformBridge.lean

  **MASTER BRIDGE: Uniform Wiener data → `ChiNegDatumUniformCore` → `Theorem_1_1`.**

  This file wires the complete chain:

  1. `exists_uniform_EWA_lifespan` gives uniform T* from bar-constants
  2. `chiNeg_EWA_core_of_datum_prescribedT` gives Core at T* for each datum
  3. Result: `∃ T* > 0, ∀ PPID bounded by M, ∃ u, Core p T* u₀ u`
  4. → `ChiNegDatumUniformCore p` → `Theorem_1_1 intervalDomain p`

  The hypothesis `DatumWienerData` encapsulates the Wiener gap:
  - For each M > 0, a uniform floor fm > 0
  - For each PPID datum bounded by M: a Wiener lifting with ‖u₀E‖ ≤ WM

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceChiNegPerDatumPrescribed
import ShenWork.Wiener.EWA.ChiNegUniformLifespan
import ShenWork.Wiener.EWA.WienerLiftingC3
import ShenWork.Paper2.IntervalDomainTheorem11CorePath

open Set Filter Topology
open ShenWork.Wiener (WA ofCosineCoeffs)
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomain)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.Paper2 (PaperPositiveInitialDatum Theorem_1_1)

noncomputable section

namespace ShenWork.EWA

/-- **Uniform Wiener data for PPID datums bounded by M.**

For each M > 0, provides:
- A uniform floor fm > 0 (all datums have floor ≥ fm)
- A uniform Wiener norm bound WM (all datums have ‖u₀E‖ ≤ WM)
- A Wiener lifting for each individual datum -/
structure DatumWienerData (p : CM2Params) where
  liftM : ∀ M : ℝ, 0 < M →
    ∃ (fm : ℝ) (_ : 0 < fm) (WM : ℝ) (_ : 0 ≤ WM),
      ∀ {u₀p : intervalDomainPoint → ℝ},
        PaperPositiveInitialDatum intervalDomain u₀p →
        (∀ x, |u₀p x| ≤ M) →
        ∃ (W : DatumWienerLifting u₀p),
          fm ≤ W.floor ∧
          ‖(⟨ofCosineCoeffs (cosineCoeffs W.u₀), W.hmem⟩ : WA 1)‖ ≤ WM

/-- **THE MASTER BRIDGE: `DatumWienerData → ChiNegDatumUniformCore`.**

Given uniform Wiener lifting data, produces the EWA-free uniform Core
construction. The proof:
1. Extract (fm, WM) for the given M
2. Compute bar-constants = CleanFPConst at (WM, fm)
3. `exists_uniform_EWA_lifespan` → uniform T*
4. For each datum: prescribed-T FP at T* → Core at T* -/
theorem uniformCore_of_datumWienerData (p : CM2Params)
    (hβpos : 0 < p.β) (hαnn : 0 ≤ p.α) (hμle1 : p.μ ≤ 1)
    (hD : DatumWienerData p) :
    ChiNegDatumUniformCore p := by
  intro M hM
  -- Step 1: get uniform floor and Wiener norm bound for this M.
  obtain ⟨fm, hfm_pos, WM, hWM_nn, hlift⟩ := hD.liftM M hM
  -- Step 2: compute bar-constants at (WM, fm).
  set LQbar := CleanFPConst.L_Q p WM fm
  set LGbar := CleanFPConst.L_G p WM fm
  set MQbar := CleanFPConst.M_Q p WM fm
  set MGbar := CleanFPConst.M_G p WM fm
  set ρbar := fm / 2
  -- Step 3: uniform lifespan from bar-constants.
  -- exists_uniform_EWA_lifespan gives T* where the conditions hold.
  have hLQnn : 0 ≤ LQbar := CleanFPConst.L_Q_nonneg hWM_nn hfm_pos hβpos
  have hLGnn : 0 ≤ LGbar := CleanFPConst.L_G_nonneg hWM_nn hfm_pos
  have hMQnn : 0 ≤ MQbar := CleanFPConst.M_Q_nonneg hWM_nn hfm_pos hβpos
  have hMGnn : 0 ≤ MGbar := CleanFPConst.M_G_nonneg hWM_nn hfm_pos
  have hρpos : 0 < ρbar := by
    change 0 < fm / 2
    linarith
  obtain ⟨Tstar, hTstar_pos, hTstar_body⟩ :=
    exists_uniform_EWA_lifespan (χ₀ := p.χ₀)
      hLQnn hLGnn hMQnn hMGnn hρpos
  -- Instantiate conditions at bar-constants (L_Q = LQbar, etc.).
  have hbar_conds : (|p.χ₀| * C₀ * LQbar) * Real.sqrt Tstar + LGbar * Tstar < 1 ∧
      (|p.χ₀| * C₀ * MQbar) * Real.sqrt Tstar + MGbar * Tstar ≤ ρbar :=
    hTstar_body hLQnn hLGnn hMQnn hMGnn
      (le_refl _) (le_refl _) (le_refl _) (le_refl _)
  -- Rewrite to match prescribed-T FP's format (ring identity).
  have hKlt : |p.χ₀| * C₀ * LQbar * Real.sqrt Tstar + LGbar * Tstar < 1 := by
    have := hbar_conds.1; ring_nf at this ⊢; exact this
  have hsmall : |p.χ₀| * C₀ * MQbar * Real.sqrt Tstar + MGbar * Tstar ≤ fm / 2 := by
    change |p.χ₀| * C₀ * MQbar * Real.sqrt Tstar + MGbar * Tstar ≤ ρbar
    have := hbar_conds.2; ring_nf at this ⊢; exact this
  -- Step 4: for each datum, run the prescribed-T FP at Tstar.
  refine ⟨Tstar, hTstar_pos, fun {u₀p} hu₀p hbd => ?_⟩
  obtain ⟨W, hfm_le, hWM_le⟩ := hlift hu₀p hbd
  -- Run per-datum Core at Tstar.
  -- The floor hypothesis: u₀(y) ≥ W.floor ≥ fm, so ∀ y, fm ≤ u₀(y).
  have hfloor_fm : ∀ y, fm ≤ W.u₀ y := fun y => le_trans hfm_le (W.hfloor y)
  -- Call prescribed-T FP + v6 at Tstar with normBound = WM, floor = fm.
  obtain ⟨u_star, hCore⟩ :=
    chiNeg_EWA_core_of_datum_prescribedT p W.u₀ W.hu₀ hfm_pos hfloor_fm
      W.hsumc W.hmem W.hcoeff_bound u₀p W.hrecon hβpos hαnn hμle1
      hWM_nn hWM_le Tstar hTstar_pos hKlt hsmall
  exact ⟨realSlice u_star, hCore⟩

/-- **THE HEADLINE: `DatumWienerData → Theorem_1_1`.**

Complete chain from uniform Wiener lifting data to the headline theorem. -/
theorem theorem_1_1_of_datumWienerData (p : CM2Params) (hchi : p.χ₀ < 0)
    (ha : 0 < p.a) (hb : 0 < p.b) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hβpos : 0 < p.β) (hαnn : 0 ≤ p.α) (hμle1 : p.μ ≤ 1)
    (hD : DatumWienerData p) :
    Theorem_1_1 intervalDomain p :=
  chiNeg_theorem_1_1_of_uniformCore p hchi ha hb hα hγ
    (uniformCore_of_datumWienerData p hβpos hαnn hμle1 hD)

end ShenWork.EWA

#print axioms ShenWork.EWA.theorem_1_1_of_datumWienerData
