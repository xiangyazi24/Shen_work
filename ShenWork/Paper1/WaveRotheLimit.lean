/-
  Rothe monotone-limit brick for the B1 traveling-wave assembly.

  The implicit-Euler (Rothe) Green orbit for the cross-frozen traveling-wave
  operator produces, per step `z_{k+1} − h F_u(z_{k+1}) = z_k`, a sequence
  `z : ℕ → ℝ → ℝ` that (carried from `WaveRotheTrunc` /
  `WaveRotheMaxPrincipleClosers`) is:

    * antitone in `k` pointwise (monotone DECREASING in the step index),
    * trapped pointwise `U^- ≤ z_{k+1} ≤ z_k ≤ Ū`, hence bounded below, and
    * antitone in `x` for each fixed `k` (trap membership).

  This file assembles, ABSTRACTLY over such a sequence, the pointwise limit
  `rotheLimit z x = ⨅ k, z k x` and shows it inherits the monotone-wave-trap
  structure (pointwise convergence, the two-sided trap bounds, antitonicity in
  `x`, nonnegativity).  The concrete Rothe sequence supplies the carried
  hypotheses later.

  This is standard analysis (monotone bounded convergence, conditionally
  complete `ℝ`); it does NOT re-derive the Rothe step, only consumes its output.

  One piece that does NOT follow from the pointwise infimum is CONTINUITY of the
  limit: a pointwise `iInf` of continuous functions is only upper
  semicontinuous in general.  So the final trap-membership assembly
  (`rotheLimit_mem_trap`) carries continuity of `rotheLimit z` as an explicit
  hypothesis (to be discharged later from locally-uniform convergence / Dini).
-/
import ShenWork.Paper1.Statements

namespace ShenWork.Paper1

open Filter Topology Set

/-- The pointwise limit of the (decreasing-in-`k`) Rothe orbit:
the pointwise infimum over the step index. -/
noncomputable def rotheLimit (z : ℕ → ℝ → ℝ) : ℝ → ℝ :=
  fun x => ⨅ k, z k x

/-- Pointwise convergence: for `z` antitone in `k` and bounded below pointwise,
the orbit converges to `rotheLimit z` at each point.  This is the conditionally
complete monotone-convergence lemma `tendsto_atTop_ciInf`. -/
theorem rotheLimit_tendsto {z : ℕ → ℝ → ℝ}
    (hanti : ∀ x, Antitone (fun k => z k x))
    (hbdd : ∀ x, BddBelow (Set.range (fun k => z k x)))
    (x : ℝ) :
    Tendsto (fun k => z k x) atTop (𝓝 (rotheLimit z x)) :=
  tendsto_atTop_ciInf (hanti x) (hbdd x)

/-- Upper trap inheritance: if every iterate is `≤ B` pointwise, so is the
limit.  In particular with `B = Ū = upperBarrier` this gives the upper barrier
for the limit. -/
theorem rotheLimit_le_of_le {z : ℕ → ℝ → ℝ} {B : ℝ → ℝ}
    (hbdd : ∀ x, BddBelow (Set.range (fun k => z k x)))
    (hle : ∀ k x, z k x ≤ B x) (x : ℝ) :
    rotheLimit z x ≤ B x :=
  ciInf_le_of_le (hbdd x) 0 (hle 0 x)

/-- Lower trap inheritance: if every iterate is `≥ A` pointwise, so is the
limit.  In particular with `A = U^-` (lower barrier) this gives the lower
barrier for the limit; with `A = 0` it gives nonnegativity. -/
theorem rotheLimit_ge_of_ge {z : ℕ → ℝ → ℝ} {A : ℝ → ℝ}
    (hge : ∀ k x, A x ≤ z k x) (x : ℝ) :
    A x ≤ rotheLimit z x :=
  le_ciInf (fun k => hge k x)

/-- Nonnegativity of the limit, from nonnegativity of every iterate. -/
theorem rotheLimit_nonneg {z : ℕ → ℝ → ℝ}
    (hnn : ∀ k x, 0 ≤ z k x) (x : ℝ) :
    0 ≤ rotheLimit z x :=
  rotheLimit_ge_of_ge (A := fun _ => 0) hnn x

/-- The pointwise infimum of functions each antitone in `x` is antitone in `x`.
Needs the pointwise `BddBelow` side condition for the conditionally complete
`ciInf_mono`. -/
theorem rotheLimit_antitone {z : ℕ → ℝ → ℝ}
    (hanti_x : ∀ k, Antitone (z k))
    (hbdd : ∀ x, BddBelow (Set.range (fun k => z k x))) :
    Antitone (rotheLimit z) := by
  intro x y hxy
  -- `rotheLimit z y = ⨅ k, z k y ≤ ⨅ k, z k x = rotheLimit z x`
  exact ciInf_mono (hbdd y) (fun k => hanti_x k hxy)

/-- Boundedness (`IsBddFun`) of the limit: trapped between `0` and the (bounded)
upper barrier gives an absolute-value bound.  We use the iterate-0 upper bound
`z 0 ≤ Ū` and nonnegativity. -/
theorem rotheLimit_isBddFun {z : ℕ → ℝ → ℝ} {Ū : ℝ → ℝ}
    (hbdd : ∀ x, BddBelow (Set.range (fun k => z k x)))
    (hnn : ∀ k x, 0 ≤ z k x)
    (hUb : ∀ k x, z k x ≤ Ū x)
    (hŪbdd : IsBddFun Ū) :
    IsBddFun (rotheLimit z) := by
  rcases hŪbdd with ⟨M, hM⟩
  refine ⟨M, fun x => ?_⟩
  have h0 : 0 ≤ rotheLimit z x := rotheLimit_nonneg hnn x
  have hUp : rotheLimit z x ≤ Ū x := rotheLimit_le_of_le hbdd hUb x
  have hUpM : rotheLimit z x ≤ M :=
    le_trans hUp (le_trans (le_abs_self _) (hM x))
  rw [abs_of_nonneg h0]
  exact hUpM

/--
Full trap-membership assembly for the limit.

From the carried Rothe-orbit properties — antitone in `k` (so bounded below by
the lower barrier), antitone in `x` for each iterate, nonnegativity, and the
upper barrier on every iterate — the limit lands in `InMonotoneWaveTrapSet κ M`.

The one ingredient that does NOT follow from the pointwise infimum is
CONTINUITY of `rotheLimit z` (a pointwise `iInf` of continuous functions is only
upper semicontinuous in general); it is carried here as the explicit hypothesis
`hcont`, to be discharged later from locally-uniform convergence / Dini's
theorem on the concrete orbit.
-/
theorem rotheLimit_mem_trap {z : ℕ → ℝ → ℝ} {κ M : ℝ}
    (hcont : Continuous (rotheLimit z))
    (hbdd : ∀ x, BddBelow (Set.range (fun k => z k x)))
    (hanti_x : ∀ k, Antitone (z k))
    (hnn : ∀ k x, 0 ≤ z k x)
    (hUb : ∀ k x, z k x ≤ upperBarrier κ M x)
    (hŪbdd : IsBddFun (upperBarrier κ M)) :
    InMonotoneWaveTrapSet κ M (rotheLimit z) := by
  refine ⟨⟨⟨hcont, ?_⟩, fun x => ⟨?_, ?_⟩⟩, ?_⟩
  · -- IsBddFun (rotheLimit z)
    exact rotheLimit_isBddFun hbdd hnn hUb hŪbdd
  · -- 0 ≤ rotheLimit z x
    exact rotheLimit_nonneg hnn x
  · -- rotheLimit z x ≤ upperBarrier κ M x
    exact rotheLimit_le_of_le hbdd hUb x
  · -- NonincreasingProfile (rotheLimit z), i.e. Antitone
    exact rotheLimit_antitone hanti_x hbdd

end ShenWork.Paper1
