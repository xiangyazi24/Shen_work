/-
  P1 #4 — NON-DIAGONAL `crossSource` analysis (antitone / tendsto for distinct
  triples `crossSource p lam u Z W`).

  The landed `crossSource` analysis (WavePaperStationaryFloor.lean:1023/1118/1168)
  is DIAGONAL-only: it handles `crossSource p lam U U U`, where the SAME profile
  `U` occupies all three slots (the stationary fixed point).  The per-step Rothe
  data feeds the genuinely non-diagonal object
  `crossSource p lam u Z (greenConv c lam R)`: the frozen-elliptic slot `u` (the
  previous iterate), the source slot `Z`, and the produced iterate `W` are
  DISTINCT.  This file proves the non-diagonal flux/tendsto analysis from the
  three slot limits, building toward `RotheFloorOrbitDataResidual`'s `hRbot`,
  `hRtop` fields.

  HARD RULES: new file only; no sorry/admit/native_decide/axiom; Mathlib v4.29.1;
  lines ≤100.  §3.3 non-circular (consume slot data, not the conclusion).
-/
import ShenWork.Paper1.RotheFloorOrbitDataImpl

namespace ShenWork.Paper1

noncomputable section

open Filter Topology MeasureTheory Real Set

/-! ## Non-diagonal chemotaxis-flux derivative → 0

`crossSource p lam u Z W` contains the chemotaxis flux
`deriv (fun t => (W t)^m * deriv (frozenElliptic p u) t)`, with the POWER on `W`
and the FROZEN ELLIPTIC on `u` (distinct slots).  Its derivative expands by the
product + Leibniz rule into
  `deriv W · m · W^(m-1) · V'_u  +  W^m · (V_u − u^γ)`
using `frozenElliptic_deriv_deriv_eq` for the `u`-slot.  This file proves it
tends to `0` at `−∞` from: `deriv W → 0`, `W → L_W`, `u → L_u`, the trapped-`u`
bound `|V'_u| ≤ M^γ`, and `V_u → L_u^γ`.  This is the genuine non-diagonal
analysis the diagonal lemma cannot supply (there all slots coincide). -/

/-- The non-diagonal chemotaxis-flux derivative `deriv (fun t => (W t)^m · V'_u)`
expands pointwise into `(deriv W · m · W^(m-1)) · V'_u + W^m · (V_u − u^γ)`,
for the frozen-elliptic `V_u = frozenElliptic p u` on the `u`-slot and the
power on the `W`-slot.  Requires `W` differentiable; `u` trapped (cunif/nonneg)
gives `V_u` twice differentiable with the elliptic ODE `V''_u = V_u − u^γ`. -/
theorem crossFlux_deriv_eq_nondiagonal
    {p : CMParams} {u W : ℝ → ℝ}
    (hu_bdd : IsCUnifBdd u) (hu_nn : ∀ x, 0 ≤ u x)
    (hW : Differentiable ℝ W) :
    (fun x => deriv (fun t => (W t) ^ p.m * deriv (frozenElliptic p u) t) x)
      = fun x =>
        deriv W x * p.m * (W x) ^ (p.m - 1) * deriv (frozenElliptic p u) x
          + (W x) ^ p.m * (frozenElliptic p u x - (u x) ^ p.γ) := by
  funext x
  have hWpow : HasDerivAt (fun t => (W t) ^ p.m)
      (deriv W x * p.m * (W x) ^ (p.m - 1)) x :=
    (hW x).hasDerivAt.rpow_const (Or.inr p.hm)
  have hV'' := frozenElliptic_deriv_deriv_eq p hu_bdd hu_nn x
  have hVderiv : HasDerivAt (deriv (frozenElliptic p u))
      (frozenElliptic p u x - (u x) ^ p.γ) x := by
    convert (frozenElliptic_deriv_differentiableAt p hu_bdd hu_nn x).hasDerivAt
      using 1
    exact hV''.symm
  have hprod := hWpow.mul hVderiv
  have hfun_eq :
      (fun t => (W t) ^ p.m * deriv (frozenElliptic p u) t)
        = (fun t => (W t) ^ p.m) * deriv (frozenElliptic p u) := by
    ext t; simp [Pi.mul_apply]
  rw [hfun_eq, hprod.deriv]

/-- The non-diagonal chemotaxis-flux derivative tends to `0` at `−∞`, from the
slot tails: `deriv W → 0` (the iterate's profile-derivative tail), `W → L_W`,
`V_u → L_u^γ`, and the trapped-`u` bound `|V'_u| ≤ M^γ` plus `u → L_u`.  This is
the per-step non-diagonal analogue of
`frozenChemFlux_deriv_tendsto_atBot_zero_of_profile_tails` (diagonal `U U U`). -/
theorem crossFlux_deriv_tendsto_atBot_nondiagonal
    {p : CMParams} {u W : ℝ → ℝ} {LW Lu Bγ : ℝ}
    (hu_bdd : IsCUnifBdd u) (hu_nn : ∀ x, 0 ≤ u x)
    (hW : Differentiable ℝ W)
    (hVbd : ∀ x, |deriv (frozenElliptic p u) x| ≤ Bγ) (hBγ : 0 ≤ Bγ)
    (hWlim : Tendsto W atBot (𝓝 LW)) (hUlim : Tendsto u atBot (𝓝 Lu))
    (hVlim : Tendsto (frozenElliptic p u) atBot (𝓝 (Lu ^ p.γ)))
    (hD1 : Tendsto (fun x => deriv W x) atBot (𝓝 0)) :
    Tendsto
      (fun x => deriv (fun t => (W t) ^ p.m * deriv (frozenElliptic p u) t) x)
      atBot (𝓝 0) := by
  have hD1V :
      Tendsto (fun x => deriv W x * deriv (frozenElliptic p u) x) atBot (𝓝 0) :=
    tendsto_zero_mul_of_bounded_right_atBot hBγ hVbd hD1
  have hm1_nn : 0 ≤ p.m - 1 := by linarith [p.hm]
  have hpow_m1 : Tendsto (fun x => (W x) ^ (p.m - 1)) atBot (𝓝 (LW ^ (p.m - 1))) :=
    hWlim.rpow_const (Or.inr hm1_nn)
  have hterm1 :
      Tendsto (fun x => deriv W x * p.m * (W x) ^ (p.m - 1)
        * deriv (frozenElliptic p u) x) atBot (𝓝 0) := by
    have hbase : Tendsto (fun x => (deriv W x * deriv (frozenElliptic p u) x)
        * (W x) ^ (p.m - 1)) atBot (𝓝 0) := by simpa using hD1V.mul hpow_m1
    have hscaled := hbase.const_mul p.m
    convert hscaled using 1
    · ext x; ring_nf
    · ring_nf
  have hpow_m : Tendsto (fun x => (W x) ^ p.m) atBot (𝓝 (LW ^ p.m)) :=
    hWlim.rpow_const (Or.inr (le_trans zero_le_one p.hm))
  have hpow_γ : Tendsto (fun x => (u x) ^ p.γ) atBot (𝓝 (Lu ^ p.γ)) :=
    hUlim.rpow_const (Or.inr (le_trans zero_le_one p.hγ))
  have hdiffV : Tendsto (fun x => frozenElliptic p u x - (u x) ^ p.γ) atBot (𝓝 0) := by
    simpa using hVlim.sub hpow_γ
  have hterm2 :
      Tendsto (fun x => (W x) ^ p.m * (frozenElliptic p u x - (u x) ^ p.γ))
        atBot (𝓝 0) := by simpa using hpow_m.mul hdiffV
  rw [crossFlux_deriv_eq_nondiagonal hu_bdd hu_nn hW]
  simpa using hterm1.add hterm2

/-- atTop twin of `crossFlux_deriv_tendsto_atBot_nondiagonal`.  Same product/Leibniz
expansion; the `V_u → LV` limit (and matching `u^γ → LV`) is taken abstractly so it
covers both the right-pinned endpoint and any trapped right limit. -/
theorem crossFlux_deriv_tendsto_atTop_nondiagonal
    {p : CMParams} {u W : ℝ → ℝ} {LW Lu Bγ : ℝ}
    (hu_bdd : IsCUnifBdd u) (hu_nn : ∀ x, 0 ≤ u x)
    (hW : Differentiable ℝ W)
    (hVbd : ∀ x, |deriv (frozenElliptic p u) x| ≤ Bγ) (hBγ : 0 ≤ Bγ)
    (hWlim : Tendsto W atTop (𝓝 LW)) (hUlim : Tendsto u atTop (𝓝 Lu))
    (hVlim : Tendsto (frozenElliptic p u) atTop (𝓝 (Lu ^ p.γ)))
    (hD1 : Tendsto (fun x => deriv W x) atTop (𝓝 0)) :
    Tendsto
      (fun x => deriv (fun t => (W t) ^ p.m * deriv (frozenElliptic p u) t) x)
      atTop (𝓝 0) := by
  have hD1V :
      Tendsto (fun x => deriv W x * deriv (frozenElliptic p u) x) atTop (𝓝 0) :=
    tendsto_zero_mul_of_bounded_right_atTop hBγ hVbd hD1
  have hm1_nn : 0 ≤ p.m - 1 := by linarith [p.hm]
  have hpow_m1 : Tendsto (fun x => (W x) ^ (p.m - 1)) atTop (𝓝 (LW ^ (p.m - 1))) :=
    hWlim.rpow_const (Or.inr hm1_nn)
  have hterm1 :
      Tendsto (fun x => deriv W x * p.m * (W x) ^ (p.m - 1)
        * deriv (frozenElliptic p u) x) atTop (𝓝 0) := by
    have hbase : Tendsto (fun x => (deriv W x * deriv (frozenElliptic p u) x)
        * (W x) ^ (p.m - 1)) atTop (𝓝 0) := by simpa using hD1V.mul hpow_m1
    have hscaled := hbase.const_mul p.m
    convert hscaled using 1
    · ext x; ring_nf
    · ring_nf
  have hpow_m : Tendsto (fun x => (W x) ^ p.m) atTop (𝓝 (LW ^ p.m)) :=
    hWlim.rpow_const (Or.inr (le_trans zero_le_one p.hm))
  have hpow_γ : Tendsto (fun x => (u x) ^ p.γ) atTop (𝓝 (Lu ^ p.γ)) :=
    hUlim.rpow_const (Or.inr (le_trans zero_le_one p.hγ))
  have hdiffV : Tendsto (fun x => frozenElliptic p u x - (u x) ^ p.γ) atTop (𝓝 0) := by
    simpa using hVlim.sub hpow_γ
  have hterm2 :
      Tendsto (fun x => (W x) ^ p.m * (frozenElliptic p u x - (u x) ^ p.γ))
        atTop (𝓝 0) := by simpa using hpow_m.mul hdiffV
  rw [crossFlux_deriv_eq_nondiagonal hu_bdd hu_nn hW]
  simpa using hterm1.add hterm2

/-! ## Non-diagonal `crossSource` whole-line limits (#4-C)

`crossSource p lam u Z W = reactionFun α (W) + lam·Z − χ·(flux)`.  The reaction
slot is `W`, the source slot is `Z`, the flux slot pair is `(W,u)`.  From the
three slot limits the source limit is `reactionFun α L_W + lam·L_Z`. -/

/-- **#4-C atBot.** Non-diagonal `crossSource p lam u Z W` tendsto at `−∞`, from
the three slot limits `W → L_W`, `Z → L_Z`, `u → L_u`, the iterate derivative
tail `deriv W → 0`, `V_u → L_u^γ` and the trapped-`u` bound `|V'_u| ≤ Bγ`. -/
theorem crossSource_tendsto_atBot_nondiagonal
    {p : CMParams} {lam : ℝ} {u Z W : ℝ → ℝ} {LW LZ Lu Bγ : ℝ}
    (hu_bdd : IsCUnifBdd u) (hu_nn : ∀ x, 0 ≤ u x)
    (hW : Differentiable ℝ W)
    (hVbd : ∀ x, |deriv (frozenElliptic p u) x| ≤ Bγ) (hBγ : 0 ≤ Bγ)
    (hWlim : Tendsto W atBot (𝓝 LW)) (hZlim : Tendsto Z atBot (𝓝 LZ))
    (hUlim : Tendsto u atBot (𝓝 Lu))
    (hVlim : Tendsto (frozenElliptic p u) atBot (𝓝 (Lu ^ p.γ)))
    (hD1 : Tendsto (fun x => deriv W x) atBot (𝓝 0)) :
    Tendsto (crossSource p lam u Z W) atBot (𝓝 (reactionFun p.α LW + lam * LZ)) := by
  have hα_nn : 0 ≤ p.α := le_trans zero_le_one p.hα
  have hpowα : Tendsto (fun x => (W x) ^ p.α) atBot (𝓝 (LW ^ p.α)) :=
    hWlim.rpow_const (Or.inr hα_nn)
  have hreact : Tendsto (fun x => reactionFun p.α (W x)) atBot
      (𝓝 (reactionFun p.α LW)) := by
    unfold reactionFun; exact hWlim.mul (tendsto_const_nhds.sub hpowα)
  have hflux := crossFlux_deriv_tendsto_atBot_nondiagonal hu_bdd hu_nn hW hVbd hBγ
    hWlim hUlim hVlim hD1
  have hflux_scaled : Tendsto (fun x => p.χ *
      deriv (fun t => (W t) ^ p.m * deriv (frozenElliptic p u) t) x) atBot (𝓝 0) := by
    simpa using hflux.const_mul p.χ
  have hmain := (hreact.add (hZlim.const_mul lam)).sub hflux_scaled
  simpa [crossSource] using hmain

/-- **#4-C atTop.** atTop twin. -/
theorem crossSource_tendsto_atTop_nondiagonal
    {p : CMParams} {lam : ℝ} {u Z W : ℝ → ℝ} {LW LZ Lu Bγ : ℝ}
    (hu_bdd : IsCUnifBdd u) (hu_nn : ∀ x, 0 ≤ u x)
    (hW : Differentiable ℝ W)
    (hVbd : ∀ x, |deriv (frozenElliptic p u) x| ≤ Bγ) (hBγ : 0 ≤ Bγ)
    (hWlim : Tendsto W atTop (𝓝 LW)) (hZlim : Tendsto Z atTop (𝓝 LZ))
    (hUlim : Tendsto u atTop (𝓝 Lu))
    (hVlim : Tendsto (frozenElliptic p u) atTop (𝓝 (Lu ^ p.γ)))
    (hD1 : Tendsto (fun x => deriv W x) atTop (𝓝 0)) :
    Tendsto (crossSource p lam u Z W) atTop (𝓝 (reactionFun p.α LW + lam * LZ)) := by
  have hα_nn : 0 ≤ p.α := le_trans zero_le_one p.hα
  have hpowα : Tendsto (fun x => (W x) ^ p.α) atTop (𝓝 (LW ^ p.α)) :=
    hWlim.rpow_const (Or.inr hα_nn)
  have hreact : Tendsto (fun x => reactionFun p.α (W x)) atTop
      (𝓝 (reactionFun p.α LW)) := by
    unfold reactionFun; exact hWlim.mul (tendsto_const_nhds.sub hpowα)
  have hflux := crossFlux_deriv_tendsto_atTop_nondiagonal hu_bdd hu_nn hW hVbd hBγ
    hWlim hUlim hVlim hD1
  have hflux_scaled : Tendsto (fun x => p.χ *
      deriv (fun t => (W t) ^ p.m * deriv (frozenElliptic p u) t) x) atTop (𝓝 0) := by
    simpa using hflux.const_mul p.χ
  have hmain := (hreact.add (hZlim.const_mul lam)).sub hflux_scaled
  simpa [crossSource] using hmain

/-! ## Orbit connector — `hRbot`/`hRtop` from R's source data (#4-C wired)

The residual struct carries `R = crossSource p lam u Z (greenConv c lam R)`
(`hR`) and R's two-sided bounded limits.  Here the produced iterate is
`W = greenConv c lam R`; the landed Green bridges give
`W → Rbot·lam⁻¹` / `W → Rtop·lam⁻¹` (`greenConv_tendsto_at*_of_source_tendsto`)
and `deriv W → 0` at BOTH ends (`greenConvDeriv_tendsto_zero_of_source_tail_limits`).
Feeding these into the non-diagonal crossSource tendsto produces the source
limits.  This wires #4-C to the residual's R-data, leaving only the u-slot
frozen-elliptic limits as named inputs. -/

/-- **#4-C wired (atBot).**  From R's data (continuous, bounded, two-sided limits)
and the u-slot trap data (`V_u → Lu^γ`, `|V'_u| ≤ Bγ`, `u → Lu`) plus Z's limit,
the per-step source `crossSource p lam u Z (greenConv c lam R)` tends to a limit
at `−∞`.  The produced-iterate tails come from the landed Green bridges. -/
theorem crossSource_greenConv_tendsto_atBot
    {p : CMParams} {c lam : ℝ} {u Z R : ℝ → ℝ} {Rbot LZ Lu Bγ B : ℝ}
    (hlam : 0 < lam)
    (hu_bdd : IsCUnifBdd u) (hu_nn : ∀ x, 0 ≤ u x)
    (hVbd : ∀ x, |deriv (frozenElliptic p u) x| ≤ Bγ) (hBγ : 0 ≤ Bγ)
    (hUlim : Tendsto u atBot (𝓝 Lu))
    (hVlim : Tendsto (frozenElliptic p u) atBot (𝓝 (Lu ^ p.γ)))
    (hRcont : Continuous R) (hRbd : ∀ y, |R y| ≤ B)
    (hRbot : Tendsto R atBot (𝓝 Rbot)) (hRtop : ∃ Rt, Tendsto R atTop (𝓝 Rt))
    (hZlim : Tendsto Z atBot (𝓝 LZ)) :
    Tendsto (crossSource p lam u Z (fun x => greenConv c lam R x)) atBot
      (𝓝 (reactionFun p.α (Rbot * lam⁻¹) + lam * LZ)) := by
  have hWdiff : Differentiable ℝ (fun x => greenConv c lam R x) := by
    intro x
    have hHi : ∀ t, IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi t) :=
      fun t => gWeight_integrableOn_Ioi_of_bounded
        (greenRootPlus_pos (c := c) hlam) hRcont hRbd t
    have hLo : ∀ t, IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic t) :=
      fun t => gWeight_integrableOn_Iic_of_bounded
        (greenRootMinus_neg (c := c) hlam) hRcont hRbd t
    exact (greenConv_hasDerivAt (c := c) (lam := lam) hRcont hHi hLo x).differentiableAt
  have hWlim : Tendsto (fun x => greenConv c lam R x) atBot (𝓝 (Rbot * lam⁻¹)) :=
    greenConv_tendsto_atBot_of_source_tendsto (c := c) (lam := lam) hlam
      hRcont hRbd hRbot
  have hD1 : Tendsto (fun x => deriv (fun y => greenConv c lam R y) x) atBot (𝓝 0) :=
    (greenConvDeriv_tendsto_zero_of_source_tail_limits (c := c) (lam := lam)
      hlam hRcont ⟨B, hRbd⟩ ⟨Rbot, hRbot⟩ hRtop).1
  exact crossSource_tendsto_atBot_nondiagonal hu_bdd hu_nn hWdiff hVbd hBγ
    hWlim hZlim hUlim hVlim hD1

/-- **#4-C wired (atTop).** atTop twin (the u-slot `V_u → Lu^γ` at `+∞` is the
named input; for the right-pinned endpoint `Lu = 0` it is the landed
`frozenElliptic_tendsto_atTop_of_U_tendsto`). -/
theorem crossSource_greenConv_tendsto_atTop
    {p : CMParams} {c lam : ℝ} {u Z R : ℝ → ℝ} {Rtop LZ Lu Bγ B : ℝ}
    (hlam : 0 < lam)
    (hu_bdd : IsCUnifBdd u) (hu_nn : ∀ x, 0 ≤ u x)
    (hVbd : ∀ x, |deriv (frozenElliptic p u) x| ≤ Bγ) (hBγ : 0 ≤ Bγ)
    (hUlim : Tendsto u atTop (𝓝 Lu))
    (hVlim : Tendsto (frozenElliptic p u) atTop (𝓝 (Lu ^ p.γ)))
    (hRcont : Continuous R) (hRbd : ∀ y, |R y| ≤ B)
    (hRbot : ∃ Rb, Tendsto R atBot (𝓝 Rb)) (hRtop : Tendsto R atTop (𝓝 Rtop))
    (hZlim : Tendsto Z atTop (𝓝 LZ)) :
    Tendsto (crossSource p lam u Z (fun x => greenConv c lam R x)) atTop
      (𝓝 (reactionFun p.α (Rtop * lam⁻¹) + lam * LZ)) := by
  have hWdiff : Differentiable ℝ (fun x => greenConv c lam R x) := by
    intro x
    have hHi : ∀ t, IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi t) :=
      fun t => gWeight_integrableOn_Ioi_of_bounded
        (greenRootPlus_pos (c := c) hlam) hRcont hRbd t
    have hLo : ∀ t, IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic t) :=
      fun t => gWeight_integrableOn_Iic_of_bounded
        (greenRootMinus_neg (c := c) hlam) hRcont hRbd t
    exact (greenConv_hasDerivAt (c := c) (lam := lam) hRcont hHi hLo x).differentiableAt
  have hWlim : Tendsto (fun x => greenConv c lam R x) atTop (𝓝 (Rtop * lam⁻¹)) :=
    greenConv_tendsto_atTop_of_source_tendsto (c := c) (lam := lam) hlam
      hRcont hRbd hRtop
  have hD1 : Tendsto (fun x => deriv (fun y => greenConv c lam R y) x) atTop (𝓝 0) :=
    (greenConvDeriv_tendsto_zero_of_source_tail_limits (c := c) (lam := lam)
      hlam hRcont ⟨B, hRbd⟩ hRbot ⟨Rtop, hRtop⟩).2
  exact crossSource_tendsto_atTop_nondiagonal hu_bdd hu_nn hWdiff hVbd hBγ
    hWlim hZlim hUlim hVlim hD1

/-! ## #4-B — non-diagonal `crossSource` antitonicity (additive decomposition)

`crossSource p lam u Z W = (reactionFun α (W·) + lam·Z·) + (−χ·deriv(stepFlux u W)·)`.
Antitonicity of a sum follows from antitonicity of each summand.  Two of the three
slot contributions are CLEAN:
  • the source slot `lam·Z` is antitone whenever `0 ≤ lam` and `Z` is antitone;
  • combined with the `reactionFun∘W` slot via the quasimonotone `λ`-shift.
The genuinely IRREDUCIBLE piece is the chemotaxis-flux defect
`−χ·deriv (stepFlux p u W)` (the maximum-principle sign content, the carried
`RotheChemoMonotoneResidual` obligation).  We assemble `Antitone (crossSource …)`
from the named antitone summands — the flux-defect antitonicity is the precise
missing sub-lemma, NOT proved here (would require the chemotaxis-flux divergence
sign on the trapped range; see WaveRotheOrder STALL). -/

/-- The non-diagonal `crossSource` re-expressed as a sum of the reaction-plus-step
part `g(y) = reactionFun α (W y) + lam·Z y` and the chemotaxis-flux defect
`h(y) = −χ·deriv (stepFlux p u W) y`.  Pure rewrite via `crossSource_eq_stepFlux`. -/
theorem crossSource_eq_reactStep_add_fluxDefect
    (p : CMParams) (lam : ℝ) (u Z W : ℝ → ℝ) :
    crossSource p lam u Z W
      = (fun y => reactionFun p.α (W y) + lam * Z y)
        + fun y => -(p.χ * deriv (stepFlux p u W) y) := by
  funext y
  rw [crossSource_eq_stepFlux]
  simp [Pi.add_apply]
  ring

/-- **#4-B (additive assembly).**  `Antitone (crossSource p lam u Z W)` from the
two named antitone summands: the reaction-plus-step part `g` (carrying the
`λ`-shift quasimonotonicity, including `Z` antitone via `0 ≤ lam`) and the
chemotaxis-flux defect part `h = −χ·deriv(stepFlux)` (the irreducible
maximum-principle sign — `RotheChemoMonotoneResidual`).  This isolates EXACTLY the
missing sub-lemma; it does not assume the conclusion (the two summand antitone
facts are strictly weaker per-slot statements, supplied separately). -/
theorem crossSource_antitone_of_summands
    {p : CMParams} {lam : ℝ} {u Z W : ℝ → ℝ}
    (hg : Antitone (fun y => reactionFun p.α (W y) + lam * Z y))
    (hh : Antitone (fun y => -(p.χ * deriv (stepFlux p u W) y))) :
    Antitone (crossSource p lam u Z W) := by
  rw [crossSource_eq_reactStep_add_fluxDefect]
  exact hg.add hh

/-! ## STALL — what closed unconditionally vs. what is precisely carried

CLOSED UNCONDITIONALLY (relative to slot data, no obligation re-carried):
  • `crossFlux_deriv_eq_nondiagonal` — the non-diagonal product/Leibniz expansion
    of the chemotaxis-flux derivative (distinct `u`/`W` slots), via
    `frozenElliptic_deriv_deriv_eq` for the `u`-slot ODE.
  • `crossFlux_deriv_tendsto_at{Bot,Top}_nondiagonal` — flux derivative → 0 from
    `deriv W → 0`, `W → L_W`, `u → L_u`, `V_u → L_u^γ`, `|V'_u| ≤ Bγ`.
  • `crossSource_tendsto_at{Bot,Top}_nondiagonal` — **#4-C**: the full per-step
    non-diagonal source limit `reactionFun α L_W + lam·L_Z` from the three slot
    limits.  This is the genuine non-diagonal analogue the diagonal `U U U` lemma
    (WavePaperStationaryFloor.lean:1118) cannot supply.
  • `crossSource_greenConv_tendsto_at{Bot,Top}` — **#4-C wired to R-data**: from
    `R` continuous/bounded/two-sided limits the produced iterate `W=greenConv c lam R`
    tails (`W → Rbot·lam⁻¹`, `deriv W → 0`) come from the landed Green bridges
    (`greenConv_tendsto_at*_of_source_tendsto`,
    `greenConvDeriv_tendsto_zero_of_source_tail_limits`), discharging the
    SOURCE→ITERATE bridge flagged in RotheFloorOrbitDataImpl:280.

CARRIED — precise missing sub-lemmas (file:line + verdict):
  • **#4-B antitone** (`crossSource_antitone_of_summands`): the ADDITIVE assembly
    is proved; the irreducible piece is the chemotaxis-flux-defect antitonicity
    `Antitone (fun y => −(χ · deriv (stepFlux p u W) y))`.  VERDICT: this is the
    maximum-principle SIGN content — the same obligation carried diagonally as
    `RotheChemoMonotoneResidual` (WaveRotheOrder.lean:126, its STALL NOTE).  It
    needs the chemotaxis-flux divergence sign on the trapped range (`χ ≤ 0`, `Z`
    antitone, `u` trapped); not provable by slot limits alone.  The reaction-step
    summand `Antitone (reactionFun α (W·) + lam·Z·)` is the `λ`-shift quasimono-
    tonicity (needs the per-step `W ≤ Z` coupling) — also carried as `hg`.
  • **#4-C u-slot limit** (input `hVlim : V_u → Lu^γ`): for the right-pinned
    endpoint `Lu = 0` it is the landed `frozenElliptic_tendsto_atTop_of_U_tendsto`
    (Statements.lean:2811); for a general trapped `u` tail it is the named input.
  • **#4-B `hR` source identity** `R = crossSource p lam u Z (greenConv c lam R)`:
    VERDICT — GENUINELY CARRIED, NOT `rfl`.  `crossImplicitMap` (WaveRotheStep:381)
    is `greenConv c lam (crossSource …)`, and `hstep_eq` gives
    `W = greenConv c lam (crossSource … W)`; but the abstract fixed-point source `R`
    is the bcf fixed point, which is only PROVABLY (not definitionally) equal to
    `crossSource … (greenConv c lam R)`.  So `hR` is a real identity carried by the
    producer, not closeable by `rfl`.

EXACT STALL: the per-step non-diagonal tendsto/flux analysis (#4-C) and the
additive antitone reduction (#4-B) are closed; the residual is the single
chemotaxis-flux-defect SIGN (`RotheChemoMonotoneResidual`, WaveRotheOrder:126) for
antitone, plus the per-step `W ≤ Z` coupling for the reaction-step summand. -/

#print axioms crossFlux_deriv_eq_nondiagonal
#print axioms crossFlux_deriv_tendsto_atBot_nondiagonal
#print axioms crossFlux_deriv_tendsto_atTop_nondiagonal
#print axioms crossSource_tendsto_atBot_nondiagonal
#print axioms crossSource_tendsto_atTop_nondiagonal
#print axioms crossSource_greenConv_tendsto_atBot
#print axioms crossSource_greenConv_tendsto_atTop
#print axioms crossSource_eq_reactStep_add_fluxDefect
#print axioms crossSource_antitone_of_summands

end

end ShenWork.Paper1
