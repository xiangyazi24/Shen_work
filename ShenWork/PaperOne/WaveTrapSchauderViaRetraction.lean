import ShenWork.Paper1.InMonotoneWaveTrapSchauderPrinciple
import ShenWork.Paper1.WaveRotheC1
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

/-- The two `upperBarrier`s agree at `M = 1`. -/
theorem paper1_upperBarrier_one_eq (κ : ℝ) :
    ShenWork.Paper1.upperBarrier κ 1 = upperBarrier κ := by
  funext x; simp [ShenWork.Paper1.upperBarrier, upperBarrier]

/-- `r` maps `InMonotoneWaveTrapSet κ 1` into `WaveTrap κ κt D`. -/
theorem waveTrapRetract_mem (hκ : 0 < κ) (hκt : κ < κt) (hD : 1 ≤ D)
    {u : ℝ → ℝ} (hu : ShenWork.Paper1.InMonotoneWaveTrapSet κ 1 u) :
    waveTrapRetract κ κt D u ∈ WaveTrap κ κt D := by
  obtain ⟨⟨_hbdd, hbounds⟩, hanti⟩ := hu
  have hu_anti : Antitone u := hanti
  have hLanti : Antitone (lowerBarrierMajorant κ κt D) :=
    lowerBarrierMajorant_antitone hκ.le hκt hD
  refine ⟨fun x => ⟨?_, ?_⟩, ?_⟩
  · -- lowerBarrier ≤ r u
    calc lowerBarrier κ κt D x ≤ lowerBarrierMajorant κ κt D x :=
          lowerBarrier_le_majorant hκ.le hκt hD x
      _ ≤ waveTrapRetract κ κt D u x := le_max_right _ _
  · -- r u ≤ upperBarrier κ
    refine max_le ?_ (majorant_le_upper hκ hκt hD x)
    have := (hbounds x).2
    rwa [paper1_upperBarrier_one_eq] at this
  · -- antitone
    exact fun a b hab => max_le_max (hu_anti hab) (hLanti hab)

/-- `r` preserves locally-uniform convergence (it is 1-Lipschitz). -/
theorem waveTrapRetract_locUnif {seq : ℕ → ℝ → ℝ} {u : ℝ → ℝ}
    (h : ShenWork.Paper1.LocallyUniformConverges seq u) :
    ShenWork.Paper1.LocallyUniformConverges (fun n => waveTrapRetract κ κt D (seq n))
      (waveTrapRetract κ κt D u) := by
  intro R hR ε hε
  filter_upwards [h R hR ε hε] with n hn x hx
  exact lt_of_le_of_lt (waveTrapRetract_dist_le _ _ x) (hn x hx)

/-- **Schauder fixed point on `WaveTrap κ κt D`, given that `Tmap` produces continuous outputs.**
The continuity hypothesis on the image is exactly what the long-time map `longTimeMap` satisfies, so this
discharges the headline's Schauder requirement WITHOUT modifying the (continuity-free) `WaveTrap` definition. -/
theorem waveTrap_fixedPoint_of_continuousImage (hκ : 0 < κ) (hκt : κ < κt) (hD : 1 ≤ D)
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hmap : ∀ u, u ∈ WaveTrap κ κt D → Tmap u ∈ WaveTrap κ κt D)
    (hcont : ShenWork.Paper1.LocalUniformContinuousOn (fun U => U ∈ WaveTrap κ κt D) Tmap)
    (hcompact : ShenWork.Paper1.LocalUniformSequentiallyCompactRange (fun U => U ∈ WaveTrap κ κt D) Tmap)
    (hTimg : ∀ u, u ∈ WaveTrap κ κt D → Continuous (Tmap u)) :
    ∃ U : ℝ → ℝ, U ∈ WaveTrap κ κt D ∧ Tmap U = U := by
  set r := waveTrapRetract κ κt D with hr
  set T' : (ℝ → ℝ) → ℝ → ℝ := fun u => Tmap (r u) with hT'
  -- `r u ∈ WaveTrap` for `u ∈ InMonotone κ 1`.
  have hr_mem : ∀ u, ShenWork.Paper1.InMonotoneWaveTrapSet κ 1 u → r u ∈ WaveTrap κ κt D :=
    fun u hu => waveTrapRetract_mem hκ hκt hD hu
  -- `T' u ∈ InMonotone κ 1` for `u ∈ InMonotone κ 1`:  `Tmap (r u) ∈ WaveTrap`, continuous, bounded.
  have hT'_maps : ∀ u, ShenWork.Paper1.InMonotoneWaveTrapSet κ 1 u →
      ShenWork.Paper1.InMonotoneWaveTrapSet κ 1 (T' u) := by
    intro u hu
    have hru : r u ∈ WaveTrap κ κt D := hr_mem u hu
    have hTru : Tmap (r u) ∈ WaveTrap κ κt D := hmap _ hru
    have hcontTru : Continuous (Tmap (r u)) := hTimg _ hru
    refine ⟨⟨⟨hcontTru, ?_⟩, fun x => ⟨waveTrap_mem_nonneg hTru x, ?_⟩⟩, hTru.2⟩
    · exact waveTrap_bounded hTru
    · have := waveTrap_mem_le_one hTru x
      have h1 : (Tmap (r u)) x ≤ ShenWork.Paper1.upperBarrier κ 1 x := by
        rw [paper1_upperBarrier_one_eq]; exact (hTru.1 x).2
      exact h1
  -- continuity of `T'` on `InMonotone κ 1`.
  have hT'_cont : ShenWork.Paper1.LocalUniformContinuousOn (ShenWork.Paper1.InMonotoneWaveTrapSet κ 1) T' := by
    intro seq u hseq hu hconv
    exact hcont (fun n => r (seq n)) (r u) (fun n => hr_mem _ (hseq n)) (hr_mem _ hu)
      (waveTrapRetract_locUnif hconv)
  -- compact range of `T'` on `InMonotone κ 1`.
  have hT'_compact : ShenWork.Paper1.LocalUniformSequentiallyCompactRange (ShenWork.Paper1.InMonotoneWaveTrapSet κ 1) T' := by
    intro seq hseq
    obtain ⟨sub, hsub, U, hU_mem, hU_conv⟩ :=
      hcompact (fun n => r (seq n)) (fun n => hr_mem _ (hseq n))
    -- `hU_conv : ShenWork.Paper1.LocallyUniformConverges (fun n => Tmap (r (seq (sub n)))) U`, each term continuous.
    have hUcont : Continuous U :=
      ShenWork.Paper1.continuous_of_locallyUniform
        (fun n => hTimg _ (hr_mem _ (hseq (sub n)))) hU_conv
    refine ⟨sub, hsub, U, ?_, hU_conv⟩
    refine ⟨⟨⟨hUcont, waveTrap_bounded hU_mem⟩, fun x => ⟨waveTrap_mem_nonneg hU_mem x, ?_⟩⟩, hU_mem.2⟩
    rw [paper1_upperBarrier_one_eq]; exact (hU_mem.1 x).2
  -- Apply the InMonotone principle, then transport the fixed point back to `WaveTrap`.
  obtain ⟨u, hu_inmono, hfix⟩ :=
    ShenWork.Paper1.inMonotoneWaveTrap_schauderPrinciple (κ := κ) (M := 1) (by norm_num)
      T' hT'_maps hT'_cont hT'_compact
  have hru : r u ∈ WaveTrap κ κt D := hr_mem u hu_inmono
  have hu_wave : u ∈ WaveTrap κ κt D := by
    have : Tmap (r u) = u := hfix
    rw [← this]; exact hmap _ hru
  have hru_eq : r u = u := waveTrapRetract_eq_of_mem hu_wave
  refine ⟨u, hu_wave, ?_⟩
  calc Tmap u = Tmap (r u) := by rw [hru_eq]
    _ = u := hfix

end ShenWork.PaperOne
