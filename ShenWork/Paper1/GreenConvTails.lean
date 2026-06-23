/-
  ShenWork/Paper1/GreenConvTails.lean

  Atom #4A-tails: the `greenConv`-tendsto tails feeding `RotheStepTails`.

  The residual carried by `RotheMaxDataImpl.lean` (the `RotheStepTails W B`
  packet: `φcont`, `La`/`Lb`, `hbot`/`hLa`/`htop`/`hLb`) is the two-sided
  ±∞ limit of `φ = W − B` where the produced iterate is a Green convolution
  `W = greenConv c lam R` of a bounded source `R`.

  This file closes that residual from the *landed* analytic bricks:

    * `greenConv_tendsto_atBot_of_source_tendsto`
      (WavePaperRotheProducer.lean:5570) — `R → L` at `atBot` ⟹
      `greenConv R → L · λ⁻¹` at `atBot`, via dominated convergence against the
      `L¹` Green kernel (mass `1/λ`, `greenKernel_l1_eq`).

  The mirror `greenConv_tendsto_atTop_of_source_tendsto` is proved here by the
  identical DCT route (only the translation filter flips `atBot → atTop`),
  reusing the same landed kernel-mass / translated-integral bricks.

  From the two one-sided limits we assemble the generic
  `rotheStepTails_of_limits` (any `W`, `B` with matched-and-ordered two-sided
  limits), then the Green-source specializations against an arbitrary barrier
  and against `upperBarrier κ M`.  No existing file is edited.
-/
import ShenWork.Paper1.WavePaperRotheProducer
import ShenWork.Paper1.RotheMaxDataImpl

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## 1. The `atTop` Green-convolution limit (mirror of the landed `atBot`)

`greenConv_tendsto_atBot_of_source_tendsto` is landed; the `atTop` version is
the same dominated-convergence argument with the translation `x ↦ x + t` driven
to `atTop` instead of `atBot`. The dominating function (`|K(−·)|·B`), the
measurability/bound clauses, and the limit integral `∫ K(−t)·L = L·λ⁻¹` are all
filter-independent and reuse the landed kernel bricks verbatim. -/

/-- **`atTop` Green-convolution limit.** If the bounded continuous source `H`
tends to `L` at `+∞`, then `greenConv c lam H` tends to `L · λ⁻¹` at `+∞`
(the Green kernel has total mass `λ⁻¹`). DCT mirror of
`greenConv_tendsto_atBot_of_source_tendsto`. -/
theorem greenConv_tendsto_atTop_of_source_tendsto
    (hlam : 0 < lam) {H : ℝ → ℝ} {B L : ℝ}
    (hH : Continuous H) (hB : ∀ y, |H y| ≤ B)
    (hlim : Tendsto H atTop (𝓝 L)) :
    Tendsto (greenConv c lam H) atTop (𝓝 (L * lam⁻¹)) := by
  let F : ℝ → ℝ → ℝ := fun x t => greenKernel c lam (-t) * H (x + t)
  let G : ℝ → ℝ := fun t => greenKernel c lam (-t) * L
  let bound : ℝ → ℝ := fun t => |greenKernel c lam (-t)| * B
  have hbound_int : Integrable bound := by
    have hK : Integrable (fun t => |greenKernel c lam (-t)|) :=
      ((greenKernel_integrable (c := c) hlam).abs).comp_neg
    simpa [bound] using hK.mul_const B
  have hF_meas :
      ∀ᶠ x in atTop, AEStronglyMeasurable (F x) volume := by
    refine Eventually.of_forall ?_
    intro x
    exact ((greenKernel_continuous (c := c) (lam := lam)).comp
        (continuous_neg.comp continuous_id) |>.mul
      (hH.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  have h_bound :
      ∀ᶠ x in atTop, ∀ᵐ t ∂volume, ‖F x t‖ ≤ bound t := by
    refine Eventually.of_forall ?_
    intro x
    refine Eventually.of_forall ?_
    intro t
    dsimp [F, bound]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hB (x + t)) (abs_nonneg _)
  have h_lim :
      ∀ᵐ t ∂volume, Tendsto (fun x => F x t) atTop (𝓝 (G t)) := by
    refine Eventually.of_forall ?_
    intro t
    have hshift : Tendsto (fun x : ℝ => x + t) atTop atTop :=
      tendsto_atTop_add_const_right atTop t tendsto_id
    exact hlim.comp hshift |>.const_mul (greenKernel c lam (-t))
  have hInt_tendsto :
      Tendsto (fun x => ∫ t, F x t) atTop (𝓝 (∫ t, G t)) :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := atTop) (F := F) (f := G)
      bound hF_meas h_bound hbound_int h_lim
  have hGint : (∫ t, G t) = L * lam⁻¹ := by
    dsimp [G]
    rw [show (fun t : ℝ => greenKernel c lam (-t) * L)
        = fun t : ℝ => L * greenKernel c lam (-t) by
          funext t; ring]
    rw [MeasureTheory.integral_const_mul]
    rw [integral_neg_eq_self (greenKernel c lam) volume]
    rw [greenKernel_integral_eq (c := c) hlam]
  have hrewrite :
      (fun x => ∫ t, F x t) = greenConv c lam H := by
    funext x
    exact (greenConv_eq_translated_integral_of_bounded
      (c := c) (lam := lam) hlam hH hB x).symm
  simpa [hrewrite, hGint] using hInt_tendsto

/-! ## 2. Generic `RotheStepTails` from matched-and-ordered two-sided limits

The clean max-principle consumes only: continuity of `φ = W − B`, the existence
of the two one-sided limits, and their signs `≤ 0`. Given the limits of `W` and
`B` separately at each end with `W`-limit `≤` `B`-limit, the difference limit and
its sign follow by `Tendsto.sub` + `sub_nonpos`. -/

/-- **Generic tails assembler.** From the two-sided limits of `W` and `B`, with
the `W`-limit `≤` the `B`-limit at each end, build `RotheStepTails W B`. The
carried `La`/`Lb` are the difference limits; non-vacuous (witnessed by the
supplied tendstos) and non-circular (no `W ≤ B` assumed). -/
def rotheStepTails_of_limits
    {W B : ℝ → ℝ} {Wbot Wtop Bbot Btop : ℝ}
    (hWcont : Continuous W) (hBcont : Continuous B)
    (hWbot : Tendsto W atBot (𝓝 Wbot)) (hBbot : Tendsto B atBot (𝓝 Bbot))
    (hWtop : Tendsto W atTop (𝓝 Wtop)) (hBtop : Tendsto B atTop (𝓝 Btop))
    (hbot_le : Wbot ≤ Bbot) (htop_le : Wtop ≤ Btop) :
    RotheStepTails W B where
  φcont := hWcont.sub hBcont
  La := Wbot - Bbot
  Lb := Wtop - Btop
  hbot := hWbot.sub hBbot
  hLa := sub_nonpos.mpr hbot_le
  htop := hWtop.sub hBtop
  hLb := sub_nonpos.mpr htop_le

/-! ## 3. Green-source specialization against an arbitrary barrier

The produced iterate is `W = greenConv c lam R` with bounded continuous source
`R` that has two-sided limits `Rbot`/`Rtop`; the barrier `B` has two-sided
limits `Bbot`/`Btop`. The Green limits are `Rbot·λ⁻¹` / `Rtop·λ⁻¹`. The
comparison signs are the genuine §3.3 content carried as the two scalar
ordering hypotheses (`Rbot·λ⁻¹ ≤ Bbot`, `Rtop·λ⁻¹ ≤ Btop`). -/

/-- **`RotheStepTails` for a Green-produced iterate vs. an arbitrary barrier.**
`W = greenConv c lam R`, `R` bounded continuous with two-sided limits; the
ordered Green/barrier endpoint limits give the tails. -/
def rotheStepTails_greenConv_of_barrier_limits
    {R B : ℝ → ℝ} {Rb Rbot Rtop Bbot Btop : ℝ}
    (hlam : 0 < lam)
    (hRcont : Continuous R) (hRb : ∀ y, |R y| ≤ Rb)
    (hRbot : Tendsto R atBot (𝓝 Rbot)) (hRtop : Tendsto R atTop (𝓝 Rtop))
    (hBcont : Continuous B)
    (hBbot : Tendsto B atBot (𝓝 Bbot)) (hBtop : Tendsto B atTop (𝓝 Btop))
    (hbot_le : Rbot * lam⁻¹ ≤ Bbot) (htop_le : Rtop * lam⁻¹ ≤ Btop) :
    RotheStepTails (fun x => greenConv c lam R x) B :=
  rotheStepTails_of_limits
    (W := fun x => greenConv c lam R x) (B := B)
    ((greenConv_contDiff_two (c := c) (lam := lam) hRcont
        (fun t => gWeight_integrableOn_Ioi_of_bounded
          (greenRootPlus_pos (c := c) hlam) hRcont hRb t)
        (fun t => gWeight_integrableOn_Iic_of_bounded
          (greenRootMinus_neg (c := c) hlam) hRcont hRb t)).continuous)
    hBcont
    (greenConv_tendsto_atBot_of_source_tendsto (c := c) (lam := lam)
      hlam hRcont hRb hRbot)
    hBbot
    (greenConv_tendsto_atTop_of_source_tendsto (c := c) (lam := lam)
      hlam hRcont hRb hRtop)
    hBtop hbot_le htop_le

/-! ## 4. Green-source specialization against `upperBarrier κ M`

`upperBarrier κ M = min M (exp(−κ·))` has the unconditional two-sided limits
`M` at `atBot` (the exponential blows up, the `min` plateaus at `M`) and `0` at
`atTop` (the landed `upperBarrier_tendsto_atTop_zero`). Hence the barrier
ordering reduces to `Rbot·λ⁻¹ ≤ M` and `Rtop·λ⁻¹ ≤ 0`. -/

/-- `upperBarrier κ M → M` at `−∞`: eventually `M ≤ exp(−κ x)`, so the `min`
collapses to the constant `M`. -/
theorem upperBarrier_tendsto_atBot_M {κ M : ℝ} (hκ : 0 < κ) :
    Tendsto (upperBarrier κ M) atBot (𝓝 M) := by
  have hexp : Tendsto (fun x : ℝ => Real.exp (-κ * x)) atBot atTop := by
    have hlin : Tendsto (fun x : ℝ => -κ * x) atBot atTop := by
      have hmul : Tendsto (fun x : ℝ => κ * x) atBot atBot :=
        Filter.Tendsto.const_mul_atBot hκ tendsto_id
      have hneg : Tendsto (fun x : ℝ => -(κ * x)) atBot atTop :=
        Filter.tendsto_neg_atTop_iff.mpr hmul
      simpa [neg_mul] using hneg
    exact Real.tendsto_exp_atTop.comp hlin
  have hev : ∀ᶠ x in atBot, M = upperBarrier κ M x := by
    have hmem := hexp.eventually_ge_atTop M
    filter_upwards [hmem] with x hx
    simp only [upperBarrier]
    exact (min_eq_left hx).symm
  exact tendsto_const_nhds.congr' hev

/-- **`RotheStepTails` for a Green-produced iterate vs. `upperBarrier κ M`.**
The barrier limits are `M` (`atBot`) and `0` (`atTop`); the ordering reduces to
`Rbot·λ⁻¹ ≤ M` and `Rtop·λ⁻¹ ≤ 0`. -/
def rotheStepTails_greenConv_upperBarrier
    {R : ℝ → ℝ} {Rb Rbot Rtop κ M : ℝ}
    (hlam : 0 < lam) (hκ : 0 < κ) (hM : 0 ≤ M)
    (hRcont : Continuous R) (hRb : ∀ y, |R y| ≤ Rb)
    (hRbot : Tendsto R atBot (𝓝 Rbot)) (hRtop : Tendsto R atTop (𝓝 Rtop))
    (hbot_le : Rbot * lam⁻¹ ≤ M) (htop_le : Rtop * lam⁻¹ ≤ 0) :
    RotheStepTails (fun x => greenConv c lam R x) (upperBarrier κ M) :=
  rotheStepTails_greenConv_of_barrier_limits
    (c := c) (lam := lam) (Bbot := M) (Btop := 0)
    hlam hRcont hRb hRbot hRtop
    (upperBarrier_continuous κ M)
    (upperBarrier_tendsto_atBot_M hκ)
    (upperBarrier_tendsto_atTop_zero hκ hM)
    hbot_le htop_le

section AxiomAudit
#print axioms greenConv_tendsto_atTop_of_source_tendsto
#print axioms rotheStepTails_of_limits
#print axioms rotheStepTails_greenConv_of_barrier_limits
#print axioms upperBarrier_tendsto_atBot_M
#print axioms rotheStepTails_greenConv_upperBarrier
end AxiomAudit

end ShenWork.Paper1
