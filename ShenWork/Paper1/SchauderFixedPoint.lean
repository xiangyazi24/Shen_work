/-
# Compact fixed-point theory for the traveling-wave construction

This file collects the compact-fixed-point infrastructure used by the
traveling-wave existence argument of Paper 1.

## What Mathlib provides (verified, v4.29.1)

* Banach / contraction fixed point: `ContractingWith.exists_fixedPoint`.
* One-dimensional (interval) fixed point via the Intermediate Value Theorem:
  `exists_mem_Icc_isFixedPt`, `exists_mem_Icc_isFixedPt_of_mapsTo`.
* Schauder *bases* (`Mathlib/Analysis/Normed/Module/Bases.lean`) — unrelated to
  fixed points.

## What Mathlib does NOT provide

* **Brouwer's fixed point theorem** (finite-dimensional). Absent.
* The no-retraction theorem of the disk onto its boundary (the topological base
  for Brouwer). Absent — `Mathlib/Topology/Category/TopCat/Sphere.lean` only
  *defines* the disk/sphere and the boundary inclusion.
* **Sperner's lemma** (the combinatorial route to Brouwer). Absent.
  ("Sperner's theorem" in `Combinatorics/SetFamily/LYM.lean` is the antichain
  bound, unrelated.)
* The **Knaster–Kuratowski–Mazurkiewicz (KKM)** lemma. Absent.
* **Schauder–Tychonoff** fixed point for compact convex sets in a normed /
  locally convex space. Absent.

Consequently the general normed-space `schauder_fixedPoint` cannot be derived
from Mathlib today: the classical Schauder-projection proof bottoms out in
Brouwer in finite dimensions, and that base is missing. See the stall report at
the bottom of this file.

## What this file delivers (fully proved, axiom-clean)

* `schauder_fixedPoint_real` — the genuine one-dimensional special case of the
  Schauder–Tychonoff theorem: a continuous self-map of a nonempty compact convex
  subset of `ℝ` has a fixed point. This is exactly the trap-set fixed point when
  the trap set is a scalar interval (the monotone scalar-profile case of the
  traveling-wave construction).
* `exists_finite_eps_net` — Step 1 of the classical Schauder route: a compact set
  in a metric space admits a finite ε-net. This is the combinatorial input to the
  Schauder projection.
-/
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace ShenWork.Paper1

open Set Metric

/-- **One-dimensional Schauder–Tychonoff fixed point.**
A continuous self-map `T` of a nonempty compact convex subset `K ⊆ ℝ` has a fixed
point in `K`.

This is the `K = interval` special case of the general compact-convex fixed point
theorem; it is the relevant instance for the scalar monotone traveling-wave
profile, where the trap set is a bounded interval. It is proved directly from the
Intermediate Value Theorem (`exists_mem_Icc_isFixedPt`), so it needs no Brouwer
input. -/
theorem schauder_fixedPoint_real {K : Set ℝ} (hK_ne : K.Nonempty)
    (_hK_conv : Convex ℝ K) (hK_cpt : IsCompact K) {T : ℝ → ℝ}
    (hT_cont : ContinuousOn T K) (hT_maps : Set.MapsTo T K K) :
    ∃ U ∈ K, T U = U := by
  -- Endpoints of the compact set lie in `K`.
  set a := sInf K with ha_def
  set b := sSup K with hb_def
  have ha_mem : a ∈ K := hK_cpt.sInf_mem hK_ne
  have hb_mem : b ∈ K := hK_cpt.sSup_mem hK_ne
  -- `K ⊆ Icc a b` since `a`, `b` are the inf/sup of the (bounded) compact set.
  have hbdd_below : BddBelow K := hK_cpt.bddBelow
  have hbdd_above : BddAbove K := hK_cpt.bddAbove
  have hKsub : K ⊆ Icc a b := fun x hx =>
    ⟨csInf_le hbdd_below hx, le_csSup hbdd_above hx⟩
  have hab : a ≤ b := (hKsub ha_mem).2
  -- Convexity in `ℝ` is order-connectedness, so `Icc a b ⊆ K`; hence `Icc a b = K`.
  have hordc : K.OrdConnected := (convex_iff_ordConnected.mp _hK_conv)
  have hsub' : Icc a b ⊆ K := fun x hx => hordc.out ha_mem hb_mem hx
  have hKeq : Icc a b = K := le_antisymm hsub' hKsub
  -- `Icc a b` is forward-invariant and `T` is continuous on it.
  have hmaps_icc : Set.MapsTo T (Icc a b) (Icc a b) := by
    rw [hKeq]; exact hT_maps
  have hcont_icc : ContinuousOn T (Icc a b) := hKeq ▸ hT_cont
  -- Apply the IVT fixed-point theorem on the forward-invariant interval.
  obtain ⟨c, hc_mem, hc_fix⟩ :=
    exists_mem_Icc_isFixedPt_of_mapsTo hcont_icc hab hmaps_icc
  exact ⟨c, hsub' hc_mem, hc_fix⟩

/-- **Step 1 of the Schauder route: finite ε-nets.**
A compact set `K` in a (pseudo)metric space admits, for every `ε > 0`, a finite
set whose `ε`-balls cover `K`. This is the combinatorial input from which the
Schauder projection onto the convex hull of the net is built. -/
theorem exists_finite_eps_net {E : Type*} [PseudoMetricSpace E] {K : Set E}
    (hK_cpt : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ s ⊆ K, s.Finite ∧ K ⊆ ⋃ x ∈ s, ball x ε :=
  finite_cover_balls_of_compact hK_cpt hε

end ShenWork.Paper1
