import ShenWork.Paper1.InMonotoneWaveTrapSchauderPrinciple
import ShenWork.PaperOne.WholeLineWaveTrap
import ShenWork.PaperOne.WholeLineExponentialBarriers

/-!
# Schauder fixed-point principle for the headline `WaveTrap κ κt D`, via a retraction

We already have `inMonotoneWaveTrap_schauderPrinciple` : the principle on `InMonotoneWaveTrapSet κ M`
(antitone, `0 ≤ u ≤ Paper1.upperBarrier κ M`).  The headline uses `WaveTrap κ κt D`
(antitone, `lowerBarrier κ κt D ≤ u ≤ PaperOne.upperBarrier κ`).  Note `Paper1.upperBarrier κ 1 =
PaperOne.upperBarrier κ` (both `min 1 (exp (-κ·))`), so `WaveTrap κ κt D ⊆ InMonotoneWaveTrapSet κ 1`.

We bridge by a **continuous retraction** `r : InMonotoneWaveTrapSet κ 1 → WaveTrap κ κt D`, identity on
`WaveTrap`, built from the **antitone majorant** `Lstar` of `lowerBarrier`:
`r u = fun x => max (u x) (Lstar x)`.  Applying the `InMonotone` principle to `Tmap ∘ r` would yield a fixed
point `u = Tmap (r u) ∈ WaveTrap`, whence `r u = u` and `Tmap u = u`.

**OBSTRUCTION (genuine, found solo 2026-06-19):** the bridge does NOT close by this retraction alone, because
`InMonotoneWaveTrapSet κ M` requires `IsCUnifBdd` (= `Continuous ∧ IsBddFun`) of its members, while `WaveTrap
κ κt D` does NOT require continuity.  So `WaveTrap ⊄ InMonotoneWaveTrapSet`, and to apply the `InMonotone`
principle to `T' = Tmap ∘ r` one needs `T'` to map `InMonotone → InMonotone`, i.e. `Tmap (r u)` CONTINUOUS for
every `u`.  But `hmap` only gives `Tmap (r u) ∈ WaveTrap` (no continuity).  RESOLUTION (codex-shaped, when quota
returns): either (a) re-prove `ProjectedCubeApproxData` for the continuity-free `WaveTrap` directly (adapt
WaveTrapProjectedCubeApproxData, ~154 refs), or (b) add `Continuous` to the `WaveTrap` predicate (brick 3) so
`WaveTrap ⊆ InMonotoneWaveTrapSet κ 1` and THIS retraction closes it — then `Lstar` must also be proved
continuous (running-sup of a continuous bounded function; doable).  The retraction core below (the antitone
majorant + its order/Lipschitz facts) is CORRECT and reusable for route (b).
-/

open Set Filter Topology

namespace ShenWork.PaperOne

variable {κ κt D : ℝ}

/-- The antitone majorant of `lowerBarrier κ κt D`: `Lstar x = ⨆_{y ≥ x} lowerBarrier κ κt D y`. -/
noncomputable def lowerBarrierMajorant (κ κt D : ℝ) (x : ℝ) : ℝ :=
  sSup (lowerBarrier κ κt D '' Set.Ici x)

theorem lowerBarrierMajorant_bddAbove (hκ0 : 0 ≤ κ) (hκt : κ < κt) (hD : 1 ≤ D) (x : ℝ) :
    BddAbove (lowerBarrier κ κt D '' Set.Ici x) := by
  refine ⟨1, ?_⟩
  rintro z ⟨y, _, rfl⟩
  calc lowerBarrier κ κt D y ≤ upperBarrier κ y := lowerBarrier_le_upper hκ0 hκt hD
    _ ≤ 1 := upperBarrier_le_one _ _

theorem lowerBarrierMajorant_nonempty (κ κt D x : ℝ) :
    (lowerBarrier κ κt D '' Set.Ici x).Nonempty :=
  ⟨lowerBarrier κ κt D x, x, le_refl x, rfl⟩

/-- `lowerBarrier ≤ Lstar` pointwise. -/
theorem lowerBarrier_le_majorant (hκ0 : 0 ≤ κ) (hκt : κ < κt) (hD : 1 ≤ D) (x : ℝ) :
    lowerBarrier κ κt D x ≤ lowerBarrierMajorant κ κt D x :=
  le_csSup (lowerBarrierMajorant_bddAbove hκ0 hκt hD x) ⟨x, le_refl x, rfl⟩

/-- If `κ > 0`, `Lstar ≤ upperBarrier κ` pointwise (uses that `upperBarrier` is antitone). -/
theorem majorant_le_upper (hκ : 0 < κ) (hκt : κ < κt) (hD : 1 ≤ D) (x : ℝ) :
    lowerBarrierMajorant κ κt D x ≤ upperBarrier κ x := by
  refine csSup_le (lowerBarrierMajorant_nonempty κ κt D x) ?_
  rintro z ⟨y, hy, rfl⟩
  calc lowerBarrier κ κt D y ≤ upperBarrier κ y := lowerBarrier_le_upper hκ.le hκt hD
    _ ≤ upperBarrier κ x := upperBarrier_antitone hκ hy

/-- `Lstar` is antitone. -/
theorem lowerBarrierMajorant_antitone (hκ0 : 0 ≤ κ) (hκt : κ < κt) (hD : 1 ≤ D) :
    Antitone (lowerBarrierMajorant κ κt D) := by
  intro x₁ x₂ hx
  refine csSup_le_csSup (lowerBarrierMajorant_bddAbove hκ0 hκt hD x₁)
    (lowerBarrierMajorant_nonempty κ κt D x₂) ?_
  rintro z ⟨y, hy, rfl⟩
  exact ⟨y, le_trans hx hy, rfl⟩

/-- An antitone `u ≥ lowerBarrier` already dominates `Lstar`. -/
theorem majorant_le_of_antitone_ge_lower {u : ℝ → ℝ}
    (hu_anti : Antitone u) (hu_ge : ∀ y, lowerBarrier κ κt D y ≤ u y) (x : ℝ) :
    lowerBarrierMajorant κ κt D x ≤ u x := by
  refine csSup_le (lowerBarrierMajorant_nonempty κ κt D x) ?_
  rintro z ⟨y, hy, rfl⟩
  calc lowerBarrier κ κt D y ≤ u y := hu_ge y
    _ ≤ u x := hu_anti hy

/-- The retraction `r u = max (u ·) (Lstar ·)`. -/
noncomputable def waveTrapRetract (κ κt D : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun x => max (u x) (lowerBarrierMajorant κ κt D x)

/-- `r` is identity on `WaveTrap`. -/
theorem waveTrapRetract_eq_of_mem {u : ℝ → ℝ} (hu : u ∈ WaveTrap κ κt D) :
    waveTrapRetract κ κt D u = u := by
  funext x
  have hanti : Antitone u := hu.2
  have hge : ∀ y, lowerBarrier κ κt D y ≤ u y := fun y => (hu.1 y).1
  exact max_eq_left (majorant_le_of_antitone_ge_lower hanti hge x)

/-- `r` is 1-Lipschitz pointwise: `|r u x - r v x| ≤ |u x - v x|`. -/
theorem waveTrapRetract_dist_le (u v : ℝ → ℝ) (x : ℝ) :
    |waveTrapRetract κ κt D u x - waveTrapRetract κ κt D v x| ≤ |u x - v x| := by
  unfold waveTrapRetract
  exact abs_max_sub_max_le_abs _ _ _

end ShenWork.PaperOne
