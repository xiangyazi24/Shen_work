/-
  ShenWork/Paper1/IntervalP1RotheLimit.lean

  The final P1 pieces toward `RightVanishingWaveExistence`:

  (1) `hsign` — the integrated chemotaxis sign estimate of
      `crossSource_greenConv_le_barrierSource_of_integrated_residual`
      (`IntervalP1ChemoMonotone.lean`), discharged HONESTLY from the single
      pointwise quasi-monotonicity sign
        `∀ y, 0 ≤ barrierSource p lam u Z y − crossSource p lam u Z W y`
      (the genuine, satisfiable-on-the-trap content: the reaction increment
      against the chemotaxis flux defect, with the `λ·Z` terms cancelled since
      the comparison barrier is `B = Z`).  The W'-obstruction is already gone:
      the integrated residual is `greenConv(reactionIncr) + (−χ)∫Kλ'·fluxdiff`,
      whose Green pre-image is exactly `barrierSource − crossSource` by
      `greenConv_residual_eq` + the carried IBP identity `hChemo`.  Then
      `greenConv` positivity (`greenConv_mono` against the zero source) closes
      the sign.  No reaction-monotonicity is assumed (reaction is logistic, not
      monotone) and the kernel-derivative integral is NOT split (Kλ' changes
      sign at the kink) — the sign lives at the level of the whole Green map.

  (2) The Rothe-limit stationarity `hstationary` — REDUCED to the two LANDED
      Rothe-limit theorems `rotheLimit_crossImplicitMap_fixed` (the dominated-
      convergence pass-to-the-limit in the Green integral fixed-point relation)
      and `rotheLimit_stationary` (diagonal collapse `crossImplicitMap U U U = U`
      ⟹ `auxMap U = U` ⟹ `frozenWaveOperator U U = 0`, via the per-`U`
      `GreenIdentity`).  We package the genuinely-analytic carried inputs (the
      recursion in Green-representation form, the local-uniform convergence /
      equicontinuity output, the trap/continuity/V-bound data, and the per-`U`
      `GreenIdentity`) into `RotheLimitStationaryData` and discharge the
      `∀ x, frozenWaveOperator p c U U x = 0` shape OUTRIGHT from it.  This shows
      `hstationary` does NOT need a fresh compactness argument: it composes the
      landed pass-to-the-limit + diagonal-collapse engines.  The only genuine
      remaining wall is the local-uniform (equicontinuity) hypothesis `hLU`,
      isolated as a single named field — not re-proved here.

  No `sorry`/`axiom`/`native_decide`/`admit`.  New file only; touches nothing
  existing.  Axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
import ShenWork.Paper1.IntervalP1ChemoMonotone
import ShenWork.Paper1.WaveRotheStationary

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## 1 — `hsign` from the pointwise quasi-monotonicity sign

The integrated residual
  `greenConv(reactionIncr) + (−χ)∫Kλ'·(stepFlux_Z − stepFlux_W)`
is the Green image of the pointwise residual `barrierSource Z − crossSource W`
(`greenConv_residual_eq` rewritten through the carried IBP identity `hChemo`).
Its nonnegativity therefore reduces, by Green-map positivity (`greenConv_mono`
against the zero source), to the POINTWISE sign of that residual — the honest
quasi-monotonicity content, satisfiable on the wave trap. -/

/-- **`hsign` discharged from the pointwise residual sign.**

Given the two-profile `C¹` data, the per-tail integrabilities of the reaction
increment and the folded chemotaxis defect, and the carried IBP identity
`hChemo` (from `greenConv_chemoDefect_eq_kernelDeriv`), the single POINTWISE
sign `0 ≤ barrierSource Z − crossSource W` implies the integrated sign
obligation `hsign` of
`crossSource_greenConv_le_barrierSource_of_integrated_residual`.

No reaction monotonicity, no kernel-derivative-sign split: the nonnegativity is
transported through the whole Green map. -/
theorem hsign_of_pointwise_residual
    (hlam : 0 < lam) (p : CMParams) (u Z W : ℝ → ℝ) (x : ℝ)
    (hZC1 : ∀ y, HasDerivAt (stepFlux p u Z) (deriv (stepFlux p u Z) y) y)
    (hWC1 : ∀ y, HasDerivAt (stepFlux p u W) (deriv (stepFlux p u W) y) y)
    (hRI_Hi : IntegrableOn (gWeight (greenRootPlus c lam) (reactionIncr p Z W)) (Ioi x))
    (hRI_Lo : IntegrableOn (gWeight (greenRootMinus c lam) (reactionIncr p Z W)) (Iic x))
    (hCD_Hi : IntegrableOn
      (gWeight (greenRootPlus c lam) (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y)) (Ioi x))
    (hCD_Lo : IntegrableOn
      (gWeight (greenRootMinus c lam) (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y)) (Iic x))
    (hChemo : greenConv c lam (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y) x
      = (-p.χ) * ∫ y, greenKernelDeriv c lam (x - y) * (stepFlux p u Z y - stepFlux p u W y))
    (hres : ∀ y, 0 ≤ barrierSource p lam u Z y - crossSource p lam u Z W y) :
    0 ≤ greenConv c lam (reactionIncr p Z W) x
        + (-p.χ) * ∫ y, greenKernelDeriv c lam (x - y) * (stepFlux p u Z y - stepFlux p u W y) := by
  -- The integrated residual equals `greenConv (barrierSource − crossSource)`.
  have hsplit := greenConv_residual_eq (c := c) (lam := lam) p u Z W x hZC1 hWC1
    hRI_Hi hRI_Lo hCD_Hi hCD_Lo
  rw [hChemo] at hsplit
  rw [← hsplit]
  -- The pointwise source is nonnegative; compare against the zero source.
  have hHi : IntegrableOn
      (gWeight (greenRootPlus c lam)
        (fun y => barrierSource p lam u Z y - crossSource p lam u Z W y)) (Ioi x) := by
    have : (fun y => barrierSource p lam u Z y - crossSource p lam u Z W y)
        = fun y => reactionIncr p Z W y + (-p.χ) * deriv (stepFluxDiff p u W Z) y := by
      funext y; exact barrierSource_sub_crossSource p lam u Z W (hZC1 y) (hWC1 y)
    rw [this]
    exact (hRI_Hi.add hCD_Hi).congr_fun (by intro y _; simp [gWeight]; ring) measurableSet_Ioi
  have hLo : IntegrableOn
      (gWeight (greenRootMinus c lam)
        (fun y => barrierSource p lam u Z y - crossSource p lam u Z W y)) (Iic x) := by
    have : (fun y => barrierSource p lam u Z y - crossSource p lam u Z W y)
        = fun y => reactionIncr p Z W y + (-p.χ) * deriv (stepFluxDiff p u W Z) y := by
      funext y; exact barrierSource_sub_crossSource p lam u Z W (hZC1 y) (hWC1 y)
    rw [this]
    exact (hRI_Lo.add hCD_Lo).congr_fun (by intro y _; simp [gWeight]; ring) measurableSet_Iic
  have hmono := greenConv_mono (c := c) hlam hres
    (gWeight_zero_integrableOn_Ioi (greenRootPlus c lam) x) hHi
    (gWeight_zero_integrableOn_Iic (greenRootMinus c lam) x) hLo
  rwa [greenConv_zero] at hmono

/-- **`W ≤ Z` from the pointwise quasi-monotonicity sign** (the `upperOld` order
field), composing `hsign_of_pointwise_residual` into
`crossSource_greenConv_le_barrierSource_of_integrated_residual`.  This is the
honest, W'-free statement of the chemotaxis quasi-monotonicity: the per-step
iterate `W` (Green image of `crossSource`) stays below the old profile `Z`
(Green image of `barrierSource`), discharged from the single pointwise residual
sign. -/
theorem crossSource_greenConv_le_barrierSource_of_pointwise_residual
    (hlam : 0 < lam) (p : CMParams) (u Z W : ℝ → ℝ) (x : ℝ)
    (hZC1 : ∀ y, HasDerivAt (stepFlux p u Z) (deriv (stepFlux p u Z) y) y)
    (hWC1 : ∀ y, HasDerivAt (stepFlux p u W) (deriv (stepFlux p u W) y) y)
    (hBS_Hi : IntegrableOn (gWeight (greenRootPlus c lam) (barrierSource p lam u Z)) (Ioi x))
    (hBS_Lo : IntegrableOn (gWeight (greenRootMinus c lam) (barrierSource p lam u Z)) (Iic x))
    (hCS_Hi : IntegrableOn (gWeight (greenRootPlus c lam) (crossSource p lam u Z W)) (Ioi x))
    (hCS_Lo : IntegrableOn (gWeight (greenRootMinus c lam) (crossSource p lam u Z W)) (Iic x))
    (hRI_Hi : IntegrableOn (gWeight (greenRootPlus c lam) (reactionIncr p Z W)) (Ioi x))
    (hRI_Lo : IntegrableOn (gWeight (greenRootMinus c lam) (reactionIncr p Z W)) (Iic x))
    (hCD_Hi : IntegrableOn
      (gWeight (greenRootPlus c lam) (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y)) (Ioi x))
    (hCD_Lo : IntegrableOn
      (gWeight (greenRootMinus c lam) (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y)) (Iic x))
    (hChemo : greenConv c lam (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y) x
      = (-p.χ) * ∫ y, greenKernelDeriv c lam (x - y) * (stepFlux p u Z y - stepFlux p u W y))
    (hres : ∀ y, 0 ≤ barrierSource p lam u Z y - crossSource p lam u Z W y) :
    greenConv c lam (crossSource p lam u Z W) x ≤ greenConv c lam (barrierSource p lam u Z) x :=
  crossSource_greenConv_le_barrierSource_of_integrated_residual p u Z W x hZC1 hWC1
    hBS_Hi hBS_Lo hCS_Hi hCS_Lo hRI_Hi hRI_Lo hCD_Hi hCD_Lo hChemo
    (hsign_of_pointwise_residual hlam p u Z W x hZC1 hWC1 hRI_Hi hRI_Lo hCD_Hi hCD_Lo hChemo hres)

/-! ## 2 — the Rothe-limit stationarity, reduced to the landed engines

The carried inputs of the landed `rotheLimit_crossImplicitMap_fixed` +
`rotheLimit_stationary` are packaged here.  `hstationary` then discharges
OUTRIGHT — no fresh compactness.  The only genuinely-analytic carried field is
the local-uniform convergence `hLU` (the equicontinuity output), isolated as a
single named hypothesis. -/

/-- **Packaged Rothe-limit data at the diagonal `u = U`.**  Everything the two
landed Rothe-limit theorems need to turn the Schauder fixed point `U` into a
stationary profile: the Green-representation recursion, the local-uniform
convergence, the trap/continuity/V-bound regularity, and the per-`U`
`GreenIdentity`.  Each field is exactly an argument of
`rotheLimit_crossImplicitMap_fixed` / `rotheLimit_stationary`. -/
structure RotheLimitStationaryData (p : CMParams) (c lam : ℝ) (U : ℝ → ℝ)
    (z : ℕ → ℝ → ℝ) (M Bv : ℝ) : Prop where
  hM : 0 ≤ M
  hBv : 0 ≤ Bv
  hU_def : U = rotheLimit z
  hrec : ∀ k, z (k + 1) = crossImplicitMap p c lam U (z k) (z (k + 1))
  hLU : LocallyUniformConverges z U
  hz_cont : ∀ k, Continuous (z k)
  hU_cont : Continuous U
  hV_cont : Continuous (deriv (frozenElliptic p U))
  hV_bound : ∀ y, |deriv (frozenElliptic p U) y| ≤ Bv
  hz_lb : ∀ k y, 0 ≤ z k y
  hz_ub : ∀ k y, z k y ≤ M
  hU_lb : ∀ y, 0 ≤ U y
  hU_ub : ∀ y, U y ≤ M
  hgreen : GreenIdentity p c lam U

/-- **The diagonal Green-fixed point from the packaged data.**
`crossImplicitMap p c lam U U U = U`, via the landed dominated-convergence pass
to the limit `rotheLimit_crossImplicitMap_fixed` specialised to `u = U`. -/
theorem RotheLimitStationaryData.crossImplicitMap_diagonal_fixed
    {p : CMParams} {c lam : ℝ} {U : ℝ → ℝ} {z : ℕ → ℝ → ℝ} {M Bv : ℝ}
    (hlam : 0 < lam) (hd : RotheLimitStationaryData p c lam U z M Bv) :
    crossImplicitMap p c lam U U U = U :=
  rotheLimit_crossImplicitMap_fixed (c := c) (lam := lam) (u := U) (z := z)
    (U := U) (M := M) (Bv := Bv) hlam hd.hM hd.hBv hd.hU_def hd.hrec hd.hLU
    hd.hz_cont hd.hU_cont hd.hV_cont hd.hV_bound hd.hz_lb hd.hz_ub hd.hU_lb hd.hU_ub

/-- **Rothe-limit stationarity from the packaged data.**
`∀ x, frozenWaveOperator p c U U x = 0`, composing the diagonal Green-fixed
point with the landed diagonal collapse + `GreenIdentity` engine
`rotheLimit_stationary`.  This is the `hstationary` obligation discharged
OUTRIGHT — no fresh compactness argument; the pass-to-the-limit and the
diagonal collapse are both landed. -/
theorem RotheLimitStationaryData.frozenWaveOperator_zero
    {p : CMParams} {c lam : ℝ} {U : ℝ → ℝ} {z : ℕ → ℝ → ℝ} {M Bv : ℝ}
    (hlam : 0 < lam) (hd : RotheLimitStationaryData p c lam U z M Bv) :
    ∀ x, frozenWaveOperator p c U U x = 0 :=
  rotheLimit_stationary p c lam U (hd.crossImplicitMap_diagonal_fixed hlam) hd.hgreen

/-! ## 3 — `hstationary` shape

The `b1_chiPos_existence_paper_of_cubeApproxData` `hstationary` hypothesis is
`∀ U, trap U → rotheLimit (rotheSeq U) = U → ∀ x, frozenWaveOperator p c U U x
= 0`.  We supply it from a per-`U` `RotheLimitStationaryData` producer.  The
fixed-point premise `rotheLimit (rotheSeq U) = U` is exactly `hd.hU_def`
(populated by the Schauder fixed point at the call site); the producer carries
the remaining genuinely-analytic data. -/

/-- **`hstationary` from a per-`U` packaged Rothe-limit producer.**
For any predicate `P` on profiles (the lower-pinned monotone trap), if every
`P`-profile `U` that is its own Rothe limit carries `RotheLimitStationaryData`,
then the `hstationary` obligation holds.  This is the clean reduction of the
Rothe-limit headline to the landed engines, with the equicontinuity output
`hLU` the sole remaining analytic field. -/
theorem hstationary_of_rotheLimitData
    {p : CMParams} {c lam : ℝ} {P : (ℝ → ℝ) → Prop}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ} {M Bv : ℝ} (hlam : 0 < lam)
    (hprod : ∀ U, P U → rotheLimit (rotheSeq U) = U →
      RotheLimitStationaryData p c lam U (rotheSeq U) M Bv) :
    ∀ U, P U → rotheLimit (rotheSeq U) = U →
      ∀ x, frozenWaveOperator p c U U x = 0 :=
  fun U hU hfix => (hprod U hU hfix).frozenWaveOperator_zero hlam

/-! ## Axiom audit -/

section AxiomAudit
#print axioms hsign_of_pointwise_residual
#print axioms crossSource_greenConv_le_barrierSource_of_pointwise_residual
#print axioms RotheLimitStationaryData.crossImplicitMap_diagonal_fixed
#print axioms RotheLimitStationaryData.frozenWaveOperator_zero
#print axioms hstationary_of_rotheLimitData
end AxiomAudit

end ShenWork.Paper1
