/-
  ShenWork/Wiener/EWA/ResolverSliceWindowBounds.lean

  **χ₀<0 — window-uniform C⁰ bounds `m`/`M` for the EWA fixed-point slice
  `realSlice u_star`, from the committed VALUE-field joint continuity.**

  `realSlice_powerSource_window_uniform_decay` (`ResolverSourceWindowUniformDecay.lean`)
  consumes four window-uniform scalar bundles over the clamp window
  `Icc (t₀/4) ((t₀+3T)/4)`:

  * `m t₀ > 0` — a window-uniform strictly-positive LOWER bound (`hm`/`hlb`),
  * `M t₀`     — a window-uniform UPPER bound (`hub`),
  * `G1 t₀`    — a window-uniform first-spatial-derivative bound (`hG1`),
  * `G2 t₀`    — a window-uniform second-spatial-derivative bound (`hG2`).

  This file DISCHARGES the C⁰ pair `m`/`M` directly from the standing atoms of
  `realSlice_Hv_closed`:

  * the VALUE-field JOINT (t,x)-continuity on the closed slab `Ioo 0 T ×ˢ Icc 0 1`
    is ALREADY committed — `fullSourceCoeff_jointSolutionClosed`
    (`SourceJointRegularity.lean`), from `hu0bd`/`hchem`/`hlog`;
  * on each clamp window `Icc (t₀/4) ((t₀+3T)/4) ⊂ Ioo 0 T` the lift equals that
    jointly-continuous field (`hrealizes`), so over the COMPACT window-by-`[0,1]`
    box `IsCompact.exists_isMinOn` / `IsCompact.exists_isMaxOn` extract a finite
    window-uniform min/max;
  * the min is strictly positive by the heat-floor positivity `realSlice_pos`.

  So `m`/`M` are NOT carried residuals — they are produced here from the value-field
  joint continuity + positivity, the χ₀<0 window-uniform C⁰ envelope.

  The C¹/C² pair `G1`/`G2` is NOT produced here: it needs the joint (t,x)-continuity
  of the SPATIAL derivatives `∂ₓ`/`∂ₓₓ` of the value field over the window — the
  spatial analogue of `SourceJointRegularity`'s value/time-derivative joint
  continuity, which is not in the tree.  That is the precise remaining residual; this
  file leaves `G1`/`G2` to the caller (see `ResolverSliceHvWiring.lean`).

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceJointRegularity
import ShenWork.Wiener.EWA.SourcePositivity

noncomputable section

namespace ShenWork.EWA

open Set Topology
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.CosineSpectrum (cosineMode)

variable {T : ℝ}

/-- The clamp window `Icc (t₀/4) ((t₀+3T)/4)` sits inside `Ioo 0 T` for interior `t₀`. -/
private theorem clampWindow_subset_Ioo {t₀ : ℝ} (ht₀ : 0 < t₀) (ht₀T : t₀ < T) :
    Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4) ⊆ Set.Ioo (0 : ℝ) T := by
  intro y hy
  exact ⟨lt_of_lt_of_le (by linarith) hy.1, lt_of_le_of_lt hy.2 (by linarith)⟩

/-- **Window-uniform C⁰ bounds `m`/`M` for `realSlice u_star` — DISCHARGED.**

For each interior `t₀ ∈ (0,T)`, the value-field joint continuity
`fullSourceCoeff_jointSolutionClosed` on the closed slab, combined with the slice
representation `hrealizes` and the heat-floor positivity `realSlice_pos`, gives — over
the COMPACT window box `Icc (t₀/4) ((t₀+3T)/4) ×ˢ Icc 0 1` — a strictly-positive
window-uniform lower bound `m t₀` and an upper bound `M t₀` on the lift
`intervalDomainLift (realSlice u_star σ) x`, uniformly in `(σ,x)` over the window.

This is the χ₀<0 σ-uniformization of the per-slice C⁰ min/max of
`SourceResolverSpectralDischarge` (which extracts the min/max over `[0,1]` at a single
`t`); here the min/max is over the whole `(σ,x)`-box, via the joint continuity. -/
theorem realSlice_window_uniform_C0
    (p : CM2Params) (u_star : EWA T 1) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : ShenWork.IntervalDuhamelClosedC2.DuhamelSourceTimeC1
      (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivSourceCoeffs p
        (realSlice u_star)))
    (hlog : ShenWork.IntervalDuhamelClosedC2.DuhamelSourceTimeC1
      (ShenWork.IntervalCoupledRegularityBootstrap.coupledLogisticSourceCoeffs p
        (realSlice u_star)))
    {u₀E : WA 1} {δ ρ : ℝ} (hδρ : 0 < δ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ)
    (hu_ball : u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    (hrealizes : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x) :
    ∃ m M : ℝ → ℝ, (∀ t₀, 0 < m t₀) ∧
      (∀ t₀, 0 < t₀ → t₀ < T → ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
        ∀ x ∈ Set.Icc (0 : ℝ) 1, m t₀ ≤ intervalDomainLift (realSlice u_star σ) x) ∧
      (∀ t₀, 0 < t₀ → t₀ < T → ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
        ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (realSlice u_star σ) x ≤ M t₀) := by
  classical
  -- value-field joint continuity on the closed slab (committed).
  have hjc : ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    fullSourceCoeff_jointSolutionClosed p (realSlice u_star) u₀cos hu0bd hchem hlog
  -- per-`t₀` window min/max of the lift over the compact box.
  have hwin : ∀ t₀, 0 < t₀ → t₀ < T →
      ∃ mt Mt : ℝ, 0 < mt ∧
        (∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4), ∀ x ∈ Set.Icc (0 : ℝ) 1,
          mt ≤ intervalDomainLift (realSlice u_star σ) x) ∧
        (∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4), ∀ x ∈ Set.Icc (0 : ℝ) 1,
          intervalDomainLift (realSlice u_star σ) x ≤ Mt) := by
    intro t₀ ht₀ ht₀T
    set W : Set ℝ := Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4) with hWdef
    have hsub : W ⊆ Set.Ioo (0 : ℝ) T := clampWindow_subset_Ioo ht₀ ht₀T
    have hcd : t₀ / 4 ≤ (t₀ + 3 * T) / 4 := by linarith
    -- the value field, on the box, agrees with the lift (`hrealizes`).
    set F : ℝ × ℝ → ℝ :=
      fun q => ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos q.1 n * cosineMode n q.2
      with hFdef
    have hbox_sub : W ×ˢ Set.Icc (0 : ℝ) 1 ⊆ Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 :=
      Set.prod_mono hsub (subset_refl _)
    have hFcont : ContinuousOn F (W ×ˢ Set.Icc (0 : ℝ) 1) := by
      have : ContinuousOn (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
          ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x))
          (W ×ˢ Set.Icc (0 : ℝ) 1) := hjc.mono hbox_sub
      simpa [hFdef, Function.uncurry] using this
    have hKcompact : IsCompact (W ×ˢ Set.Icc (0 : ℝ) 1) :=
      (isCompact_Icc).prod isCompact_Icc
    have hKne : (W ×ˢ Set.Icc (0 : ℝ) 1).Nonempty :=
      ⟨(t₀ / 4, 0), Set.mem_prod.mpr ⟨Set.left_mem_Icc.mpr hcd, by norm_num⟩⟩
    -- min and max of F over the compact box.
    obtain ⟨q₀, hq₀mem, hq₀min⟩ := hKcompact.exists_isMinOn hKne hFcont
    obtain ⟨q₁, _, hq₁max⟩ := hKcompact.exists_isMaxOn hKne hFcont
    -- lift = F on the box.
    have hliftF : ∀ σ ∈ W, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        intervalDomainLift (realSlice u_star σ) x = F (σ, x) := by
      intro σ hσ x hx
      have hσIoo : σ ∈ Set.Ioo (0 : ℝ) T := hsub hσ
      simpa [hFdef] using hrealizes σ hσIoo x hx
    refine ⟨F q₀, F q₁, ?_, ?_, ?_⟩
    · -- F q₀ > 0: q₀ = (σ₀, x₀) in the box, where the lift is the positive slice.
      obtain ⟨hσ₀, hx₀⟩ := Set.mem_prod.1 hq₀mem
      have hσ₀Ioo : q₀.1 ∈ Set.Ioo (0 : ℝ) T := hsub hσ₀
      have : intervalDomainLift (realSlice u_star q₀.1) q₀.2 = F (q₀.1, q₀.2) :=
        hliftF q₀.1 hσ₀ q₀.2 hx₀
      rw [show F q₀ = F (q₀.1, q₀.2) from rfl, ← this, intervalDomainLift, dif_pos hx₀]
      have htIcc : q₀.1 ∈ Set.Icc (0 : ℝ) T := ⟨hσ₀Ioo.1.le, hσ₀Ioo.2.le⟩
      exact realSlice_pos hδρ hheat hu_ball htIcc ⟨q₀.2, hx₀⟩
    · intro σ hσ x hx
      rw [hliftF σ hσ x hx]
      exact hq₀min (Set.mem_prod.mpr ⟨hσ, hx⟩)
    · intro σ hσ x hx
      rw [hliftF σ hσ x hx]
      exact hq₁max (Set.mem_prod.mpr ⟨hσ, hx⟩)
  -- assemble the per-window constants into `m`/`M : ℝ → ℝ`.
  refine ⟨fun t₀ => if h : 0 < t₀ ∧ t₀ < T then (hwin t₀ h.1 h.2).choose else 1,
    fun t₀ => if h : 0 < t₀ ∧ t₀ < T then (hwin t₀ h.1 h.2).choose_spec.choose else 0,
    ?_, ?_, ?_⟩
  · intro t₀
    dsimp only
    split_ifs with h
    · exact (hwin t₀ h.1 h.2).choose_spec.choose_spec.1
    · exact one_pos
  · intro t₀ ht₀ ht₀T σ hσ x hx
    have h : 0 < t₀ ∧ t₀ < T := ⟨ht₀, ht₀T⟩
    simp only [dif_pos h]
    exact (hwin t₀ ht₀ ht₀T).choose_spec.choose_spec.2.1 σ hσ x hx
  · intro t₀ ht₀ ht₀T σ hσ x hx
    have h : 0 < t₀ ∧ t₀ < T := ⟨ht₀, ht₀T⟩
    simp only [dif_pos h]
    exact (hwin t₀ ht₀ ht₀T).choose_spec.choose_spec.2.2 σ hσ x hx

end ShenWork.EWA

#print axioms ShenWork.EWA.realSlice_window_uniform_C0
