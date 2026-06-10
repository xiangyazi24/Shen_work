/-
  ShenWork/Paper2/IntervalPicardWdataAssembly.lean

  **Deliverables B & C — the `IterateWindowC2Data` assembler (the Wdata bundle).**

  The grand-assembly target is the `PicardIterateResidualData.Wdata` field
  (`IntervalDomainThm11ChiZeroResidual.lean`):

      Wdata : ∀ a', 0 < a' → IterateWindowC2Data p u₀ a' T

  consumed by `hCwin_ex_of_residual` through `source_coeff_window_uniform`.

  This file builds one window bundle `IterateWindowC2Data p u₀ a' T` from:

    * **(repr)** the shared per-iterate cosine representation triple
      `(bc, hbsum, hagree)` of deliverable A
      (`IntervalPicardIterateRepresentation`), supplied per `(n, σ)`;
    * **(ball)** the window-uniform positivity / sup bounds `hpos`/`hub`
      (cone-exposable — taken as hypotheses in the exact `IterateWindowC2Data`
      field shape, since the cone supplies them but `PicardConvFacts` carries only
      `0 ≤` not strict `0 <`);
    * **(G1/G2)** the window-uniform spatial derivative sup bounds, obtained from
      `picardIterateUniformData_all` (every level `n`) and a `UniformWiring`, by
      bounding the `t`-profiles `G1profile`/`G2profile` on the window `[a',T]`.

  `wdata_of_wiring` (deliverable C) assembles the bundle; `wdata_all_of_wiring`
  produces the `∀ a', 0 < a' →` family (the exact `Wdata` field).  The G1/G2 window
  constants are the genuinely-new content; the representation and ball legs are
  threaded as the honest cone-exposable boundary.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardIterateUniform
import ShenWork.Paper2.IntervalPicardWeightedC2Bootstrap
import ShenWork.Paper2.IntervalPicardIterateRepresentation

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalPicardIterateUniform
  (CL G1profile G2profile PicardIterateUniformData UniformWiring
   picardIterateUniformData_all CL_nonneg G1profile_nonneg)
open ShenWork.IntervalPicardWeightedC2Bootstrap (IterateWindowC2Data)
open ShenWork.HeatKernelGradientEstimates (heatGradientLinftyLinftyConstant
  heatGradientLinftyLinftyConstant_nonneg)

noncomputable section

namespace ShenWork.IntervalPicardWdataAssembly

/-! ## §1 — Window constants from the `t`-profiles.

The `IterateWindowC2Data` carries *scalar* window constants `G1`/`G2`, but the
`UniformWiring`/`picardIterateUniformData_all` route delivers the `t`-dependent
profiles `G1profile p M t` and `G2profile A₂ t = A₂/t²`.  On a window `[a',T]` both
profiles are dominated by an explicit window constant. -/

/-- The window first-derivative constant: dominates `G1profile p M t` for all
`t ∈ [a',T]`.  `G1profile p M t = Cg/√t·M + Cg·2√t·CL` has a decreasing first piece
(`Cg/√t`) and an increasing second piece (`2√t`); the window sup is taken termwise:
`Cg/√a'·M` (first piece at the left endpoint) `+ Cg·2√T·CL` (second piece at the
right endpoint). -/
def G1win (p : CM2Params) (M a' T : ℝ) : ℝ :=
  heatGradientLinftyLinftyConstant / Real.sqrt a' * M
    + heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * CL p M

/-- The window second-derivative constant: dominates `G2profile A₂ t = A₂/t²` for
all `t ∈ [a',T]` (decreasing, sup at the left endpoint `a'`). -/
def G2win (A₂ a' : ℝ) : ℝ := A₂ / a' ^ 2

theorem G1win_nonneg {p : CM2Params} {M a' T : ℝ}
    (hM : 0 ≤ M) (_ha' : 0 < a') (_hT : 0 ≤ T) :
    0 ≤ G1win p M a' T := by
  unfold G1win
  have hCg : 0 ≤ heatGradientLinftyLinftyConstant := heatGradientLinftyLinftyConstant_nonneg
  have hCL : 0 ≤ CL p M := CL_nonneg hM
  have hsa : 0 ≤ Real.sqrt a' := Real.sqrt_nonneg _
  have hsT : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
  have h1 : 0 ≤ heatGradientLinftyLinftyConstant / Real.sqrt a' * M :=
    mul_nonneg (div_nonneg hCg hsa) hM
  have h2 : 0 ≤ heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * CL p M :=
    mul_nonneg (mul_nonneg hCg (by linarith)) hCL
  linarith

theorem G2win_nonneg {A₂ a' : ℝ} (hA₂ : 0 ≤ A₂) (ha' : 0 < a') :
    0 ≤ G2win A₂ a' := by
  unfold G2win; positivity

/-- **`G1profile p M t ≤ G1win p M a' T` on the window `[a',T]`.**  The first piece
`Cg/√t·M` is decreasing (bounded by its value at `a'`); the second `Cg·2√t·CL` is
increasing (bounded by its value at `T`). -/
theorem G1profile_le_G1win
    {p : CM2Params} {M a' T t : ℝ} (hM : 0 ≤ M) (ha' : 0 < a')
    (hat : a' ≤ t) (htT : t ≤ T) :
    G1profile p M t ≤ G1win p M a' T := by
  unfold G1profile G1win
  have hCg : 0 ≤ heatGradientLinftyLinftyConstant := heatGradientLinftyLinftyConstant_nonneg
  have hCL : 0 ≤ CL p M := CL_nonneg hM
  have ht : 0 < t := lt_of_lt_of_le ha' hat
  -- piece 1: Cg/√t·M ≤ Cg/√a'·M  (since √a' ≤ √t ⇒ 1/√t ≤ 1/√a').
  have hsa : 0 < Real.sqrt a' := Real.sqrt_pos.mpr ha'
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsqrt_le : Real.sqrt a' ≤ Real.sqrt t := Real.sqrt_le_sqrt hat
  have hp1 : heatGradientLinftyLinftyConstant / Real.sqrt t * M
      ≤ heatGradientLinftyLinftyConstant / Real.sqrt a' * M := by
    apply mul_le_mul_of_nonneg_right _ hM
    have hd : heatGradientLinftyLinftyConstant / Real.sqrt t
        ≤ heatGradientLinftyLinftyConstant / Real.sqrt a' :=
      div_le_div_of_nonneg_left hCg hsa hsqrt_le
    exact hd
  -- piece 2: Cg·2√t·CL ≤ Cg·2√T·CL  (since √t ≤ √T).
  have hsqrt_le2 : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt htT
  have hp2 : heatGradientLinftyLinftyConstant * (2 * Real.sqrt t) * CL p M
      ≤ heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * CL p M := by
    apply mul_le_mul_of_nonneg_right _ hCL
    apply mul_le_mul_of_nonneg_left _ hCg
    linarith
  linarith

/-- **`G2profile A₂ t ≤ G2win A₂ a'` on the window `[a',T]`.**  `A₂/t²` is
decreasing, so it is bounded by `A₂/a'²` (using `A₂ ≥ 0`). -/
theorem G2profile_le_G2win
    {A₂ a' t : ℝ} (hA₂ : 0 ≤ A₂) (ha' : 0 < a') (hat : a' ≤ t) :
    G2profile A₂ t ≤ G2win A₂ a' := by
  unfold G2profile G2win
  have ht : 0 < t := lt_of_lt_of_le ha' hat
  have ha2 : (0:ℝ) < a' ^ 2 := by positivity
  have ht2 : (0:ℝ) < t ^ 2 := by positivity
  have hsq_le : a' ^ 2 ≤ t ^ 2 := by
    have := mul_le_mul hat hat ha'.le ht.le
    simpa [pow_two] using this
  -- A₂/t² ≤ A₂/a'²
  exact div_le_div_of_nonneg_left hA₂ ha2 hsq_le

/-! ## §2 — Deliverable C: the `IterateWindowC2Data` assembler.

`wdata_of_wiring` fills the `IterateWindowC2Data` record on a fixed window `[a',T]`
from: a `UniformWiring` (→ G1/G2 via `picardIterateUniformData_all`, bounded onto the
window constants); the cosine representation triple of deliverable A (supplied per
`(n,σ)`); and the cone-exposable ball positivity/sup bounds. -/

/-- **Deliverable C — `IterateWindowC2Data` from a `UniformWiring` + representation +
ball bounds.**

The G1/G2 window-uniform sup bounds come from `picardIterateUniformData_all W`
(every level `n`, every `t ∈ (0,T]`), specialised to the window `[a',T]` and bounded
by the window constants `G1win`/`G2win`.  The representation triple `(bcfun, hbsum,
hagree)` and the ball bounds `hpos`/`hub` are supplied (the honest cone-exposable
boundary — deliverable A produces the triple, the cone the ball facts). -/
def wdata_of_wiring
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {M A₂ T a' : ℝ}
    (ha' : 0 < a') (haT : a' ≤ T)
    (W : UniformWiring p u₀ M A₂ T)
    (hA₂ : 0 ≤ A₂)
    -- representation triple (deliverable A), supplied per `(n, σ)` on the window:
    (bcfun : ℕ → ℝ → ℕ → ℝ)
    (hbsum : ∀ n σ, a' ≤ σ → σ ≤ T →
      Summable (fun m => unitIntervalCosineEigenvalue m * |bcfun n σ m|))
    (hagree : ∀ n σ, a' ≤ σ → σ ≤ T →
      Set.EqOn (intervalDomainLift (picardIter p u₀ n σ))
        (fun x => ∑' m, bcfun n σ m * cosineMode m x) (Set.Icc (0 : ℝ) 1))
    -- ball bounds (cone-exposable):
    (hpos : ∀ n σ, a' ≤ σ → σ ≤ T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (picardIter p u₀ n σ) x)
    (hub : ∀ n σ, a' ≤ σ → σ ≤ T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (picardIter p u₀ n σ) x ≤ M) :
    IterateWindowC2Data p u₀ a' T :=
  let hTpos : 0 < T := lt_of_lt_of_le ha' haT
  let Data := picardIterateUniformData_all p u₀ W
  { M := M
    G1 := G1win p M a' T
    G2 := G2win A₂ a'
    hMnn := W.hMnn
    hG1nn := G1win_nonneg W.hMnn ha' hTpos.le
    hG2nn := G2win_nonneg hA₂ ha'
    bc := bcfun
    hbsum := hbsum
    hagree := hagree
    hpos := hpos
    hub := hub
    hG1 := by
      intro n σ haσ hσT x _hx
      have ht : 0 < σ := lt_of_lt_of_le ha' haσ
      exact le_trans ((Data n).hG1 σ ht hσT x)
        (G1profile_le_G1win W.hMnn ha' haσ hσT)
    hG2 := by
      intro n σ haσ hσT x _hx
      have ht : 0 < σ := lt_of_lt_of_le ha' haσ
      exact le_trans ((Data n).hG2 σ ht hσT x)
        (G2profile_le_G2win hA₂ ha' haσ) }

/-! ## §3 — The `Wdata` family (the exact residual field).

`wdata_all_of_wiring` produces `∀ a', 0 < a' → IterateWindowC2Data p u₀ a' T`, the
exact shape of `PicardIterateResidualData.Wdata`.  The per-window inputs (repr triple
+ ball bounds) are supplied as window-indexed families; the `UniformWiring`, `A₂ ≥ 0`,
and the horizon are window-independent. -/

/-- **The `Wdata` family.**  Given the window-independent `UniformWiring`/`A₂ ≥ 0`, and
the per-window representation triple + ball bounds (valid on each `[a',T]` with `0 <
a' ≤ T`), produce the full `Wdata` field consumed by `hCwin_ex_of_residual`.

For windows `a' > T` (degenerate, empty), all the per-`σ` fields are vacuous, so any
representation/ball data works; we package the bundle with trivial constants there. -/
def wdata_all_of_wiring
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {M A₂ T : ℝ}
    (W : UniformWiring p u₀ M A₂ T)
    (hA₂ : 0 ≤ A₂)
    (bcfun : ℝ → ℕ → ℝ → ℕ → ℝ)
    (hbsum : ∀ a', 0 < a' → a' ≤ T → ∀ n σ, a' ≤ σ → σ ≤ T →
      Summable (fun m => unitIntervalCosineEigenvalue m * |bcfun a' n σ m|))
    (hagree : ∀ a', 0 < a' → a' ≤ T → ∀ n σ, a' ≤ σ → σ ≤ T →
      Set.EqOn (intervalDomainLift (picardIter p u₀ n σ))
        (fun x => ∑' m, bcfun a' n σ m * cosineMode m x) (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ a', 0 < a' → a' ≤ T → ∀ n σ, a' ≤ σ → σ ≤ T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (picardIter p u₀ n σ) x)
    (hub : ∀ a', 0 < a' → a' ≤ T → ∀ n σ, a' ≤ σ → σ ≤ T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (picardIter p u₀ n σ) x ≤ M) :
    ∀ a', 0 < a' → IterateWindowC2Data p u₀ a' T := by
  intro a' ha'
  by_cases haT : a' ≤ T
  · exact wdata_of_wiring p u₀ ha' haT W hA₂ (bcfun a')
      (hbsum a' ha' haT) (hagree a' ha' haT) (hpos a' ha' haT) (hub a' ha' haT)
  · -- degenerate window `a' > T`: every per-`σ` field is vacuous (`a' ≤ σ ≤ T`
    -- is unsatisfiable).  Fill the bundle with trivial constants.
    refine
      { M := M, G1 := 0, G2 := 0
        hMnn := W.hMnn, hG1nn := le_refl 0, hG2nn := le_refl 0
        bc := fun _ _ _ => 0
        hbsum := ?_, hagree := ?_, hpos := ?_, hub := ?_, hG1 := ?_, hG2 := ?_ } <;>
    · intro n σ haσ hσT
      exact absurd (le_trans haσ hσT) haT

end ShenWork.IntervalPicardWdataAssembly
