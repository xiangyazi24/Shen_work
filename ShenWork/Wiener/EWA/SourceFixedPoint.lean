import ShenWork.Wiener.EWA.FluxLipschitzGraded
import ShenWork.Wiener.EWA.HeatFlow
import ShenWork.Paper2.Defs
import Mathlib.Topology.MetricSpace.Contracting

/-!
# EWA bricks 2–4 (χ₀<0 Route A′) — the source-form Picard map, self-map, contraction, fixed point

The grade-1 source-form fixed point on `EWA T 1`, built on top of BRICK 1
(`FluxLipschitzGraded.lean`: `chemFluxEWA_lipschitz`, `growthEWA_lipschitz`) and the
committed Duhamel/heat machinery.

The Picard map is
`Φ(u) = heatEWA u₀E + (−p.χ₀)•𝒟(Q(u)) + 𝒱(G(u))`,
with `Q(u) = chemFluxEWA μ ν p.β γ hμ u : EWA T 1`, `G(u) = growthEWA p.α p.a p.b u`,
`𝒟 = divDuhamelEWA hT` (the `C₀√T`-contraction divergence Duhamel) and
`𝒱 = valDuhamelEWA hT` (the `T`-contraction value Duhamel).

* **BRICK 2 (self-map / positivity).**  The iterates must stay in BRICK 1's positive
  domain (a `UniformFloor` on `u` and on `1+v`, the derivative bound, the radius).
  Heat preserves positivity and the Duhamel perturbation is `< δ/2` for small `T`, so the
  floor is preserved — but the heat-floor preservation lemma is *not* committed in the
  current tree.  We therefore take the forward-invariance of the *good ball* `B`
  (`Metric.closedBall (heatEWA u₀E) ρ`) as a **named hypothesis** `hself : MapsTo Φ B B`,
  together with the per-element BRICK-1 regularity data on `B` (floors / derivative bounds)
  as `hLipQ` / `hLipG`.  This is the honest conditional: everything else is proved.

* **BRICK 3 (contraction).**  On `B`, with `K = |χ₀|·C₀√T·L_Q + L_G·T`,
  `‖Φ(u) − Φ(w)‖ ≤ K·‖u − w‖`, from the divergence-Duhamel `√T` gain (`divDuhamelEWA_bound`)
  on the flux Lipschitz `L_Q` and the value-Duhamel `T` gain (`valDuhamelEWA_bound`) on the
  growth Lipschitz `L_G`.  The small-time lemma `exists_small_contraction_time` makes `K < 1`.

* **BRICK 4 (fixed point).**  `ContractingWith.exists_fixedPoint'` on the complete set
  `B` yields `∃ u* ∈ B, u* = Φ(u*)`.
-/

open scoped BigOperators NNReal ENNReal
open MeasureTheory Set Real Metric Filter Topology
open ShenWork.GWA ShenWork.Wiener

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### BRICK 2a — the source-form Picard map `Φ`. -/

/-- **The source-form Picard map** on `EWA T 1`:
`Φ(u) = heatEWA u₀E + (−χ₀)•𝒟(Q(u)) + 𝒱(G(u))`, with `Q = chemFluxEWA`, `G = growthEWA`,
`𝒟 = divDuhamelEWA` (the `C₀√T` divergence-Duhamel) and `𝒱 = valDuhamelEWA` (the `T`
value-Duhamel).  The chemotactic and growth nonlinearities live at grade 1. -/
def picardEWA (p : CM2Params) (μ ν γ : ℝ) (hμ : 0 < μ) (hT : 0 ≤ T)
    (u₀E : WA 1) (u : EWA T 1) : EWA T 1 :=
  heatEWA u₀E
    + ((-p.χ₀ : ℝ) : ℂ) • divDuhamelEWA hT (chemFluxEWA μ ν p.β γ hμ u)
    + valDuhamelEWA hT (growthEWA p.α p.a p.b u)

/-! ### BRICK 3 — the contraction estimate. -/

/-- **The Picard difference identity.**  `Φ(u) − Φ(w)` keeps only the two nonlinear
Duhamel terms; the heat datum cancels. -/
theorem picardEWA_sub (p : CM2Params) {μ ν γ : ℝ} (hμ : 0 < μ) (hT : 0 ≤ T)
    (u₀E : WA 1) (u w : EWA T 1) :
    picardEWA p μ ν γ hμ hT u₀E u - picardEWA p μ ν γ hμ hT u₀E w
      = ((-p.χ₀ : ℝ) : ℂ) •
          (divDuhamelEWA hT (chemFluxEWA μ ν p.β γ hμ u)
            - divDuhamelEWA hT (chemFluxEWA μ ν p.β γ hμ w))
        + (valDuhamelEWA hT (growthEWA p.α p.a p.b u)
            - valDuhamelEWA hT (growthEWA p.α p.a p.b w)) := by
  simp only [picardEWA, smul_sub]
  abel

/-- **BRICK 3 (contraction core).**  Given the BRICK-1 flux/growth Lipschitz bounds
`‖Q(u)−Q(w)‖ ≤ L_Q‖u−w‖` and `‖G(u)−G(w)‖ ≤ L_G‖u−w‖`, the Picard map contracts with
constant `K = |χ₀|·C₀√T·L_Q + L_G·T`:
`‖Φ(u) − Φ(w)‖ ≤ K · ‖u − w‖`. -/
theorem picardEWA_contraction {p : CM2Params} {μ ν γ L_Q L_G : ℝ} (hμ : 0 < μ) (hT : 0 ≤ T)
    (u₀E : WA 1) {u w : EWA T 1}
    (hQ : ‖chemFluxEWA μ ν p.β γ hμ u - chemFluxEWA μ ν p.β γ hμ w‖ ≤ L_Q * ‖u - w‖)
    (hG : ‖growthEWA p.α p.a p.b u - growthEWA p.α p.a p.b w‖ ≤ L_G * ‖u - w‖) :
    ‖picardEWA p μ ν γ hμ hT u₀E u - picardEWA p μ ν γ hμ hT u₀E w‖
      ≤ (|p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T) * ‖u - w‖ := by
  rw [picardEWA_sub p hμ hT u₀E u w]
  refine le_trans (norm_add_le _ _) ?_
  -- chemotaxis term: ‖(−χ₀)•(𝒟Q(u)−𝒟Q(w))‖ ≤ |χ₀|·C₀√T·L_Q·‖u−w‖.
  have hchem : ‖((-p.χ₀ : ℝ) : ℂ) •
        (divDuhamelEWA hT (chemFluxEWA μ ν p.β γ hμ u)
          - divDuhamelEWA hT (chemFluxEWA μ ν p.β γ hμ w))‖
      ≤ |p.χ₀| * (C₀ * Real.sqrt T) * L_Q * ‖u - w‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_neg, ← map_sub]
    have hdiv : ‖divDuhamelEWA hT (chemFluxEWA μ ν p.β γ hμ u
          - chemFluxEWA μ ν p.β γ hμ w)‖
        ≤ (C₀ * Real.sqrt T) * (L_Q * ‖u - w‖) := by
      refine le_trans (divDuhamelEWA_bound hT _) ?_
      exact mul_le_mul_of_nonneg_left hQ (by have := C₀_nonneg; positivity)
    calc |p.χ₀| * ‖divDuhamelEWA hT (chemFluxEWA μ ν p.β γ hμ u
              - chemFluxEWA μ ν p.β γ hμ w)‖
        ≤ |p.χ₀| * ((C₀ * Real.sqrt T) * (L_Q * ‖u - w‖)) :=
          mul_le_mul_of_nonneg_left hdiv (abs_nonneg _)
      _ = |p.χ₀| * (C₀ * Real.sqrt T) * L_Q * ‖u - w‖ := by ring
  -- growth term: ‖𝒱G(u)−𝒱G(w)‖ ≤ T·L_G·‖u−w‖.
  have hgr : ‖valDuhamelEWA hT (growthEWA p.α p.a p.b u)
          - valDuhamelEWA hT (growthEWA p.α p.a p.b w)‖
      ≤ L_G * T * ‖u - w‖ := by
    rw [← map_sub]
    refine le_trans (valDuhamelEWA_bound hT _) ?_
    calc T * ‖growthEWA p.α p.a p.b u - growthEWA p.α p.a p.b w‖
        ≤ T * (L_G * ‖u - w‖) := mul_le_mul_of_nonneg_left hG hT
      _ = L_G * T * ‖u - w‖ := by ring
  refine le_trans (add_le_add hchem hgr) ?_
  apply le_of_eq; ring

/-! ### BRICK 4 — the fixed point via the Banach contraction theorem.

The "good ball" `B := closedBall (heatEWA u₀E) ρ` is complete (closed in a complete space).
The BRICK-1 Lipschitz data on `B` (carried as `hLipQ`/`hLipG`) gives the contraction with
constant `K = |χ₀|·C₀√T·L_Q + L_G·T`; small-time makes `K < 1`.  The self-map
`hself : MapsTo Φ B B` is the BRICK-2 positivity/floor preservation (honest hypothesis). -/

/-- **BRICKS 2–4 assembled (conditional on the carried self-map + Lipschitz data).**
On the good ball `B = closedBall (heatEWA u₀E) ρ`, if

* `hself` : `Φ` maps `B` into `B` (BRICK-2 positivity / floor preservation), and
* `hLipQ` / `hLipG` : the BRICK-1 flux/growth Lipschitz bounds hold for every pair in `B`,
* `hK` : the contraction constant `K = |χ₀|·C₀√T·L_Q + L_G·T < 1` (BRICK-3 small-time),
* `hKnn` : `0 ≤ K`,

then `Φ` has a fixed point in `B`:  `∃ u* ∈ B, u* = Φ(u*)`. -/
theorem picardEWA_exists_fixedPoint {p : CM2Params} {μ ν γ ρ L_Q L_G : ℝ}
    (hμ : 0 < μ) (hT : 0 ≤ T) (u₀E : WA 1) (hρ : 0 ≤ ρ)
    (hself : MapsTo (picardEWA p μ ν γ hμ hT u₀E)
      (Metric.closedBall (heatEWA u₀E) ρ) (Metric.closedBall (heatEWA u₀E) ρ))
    (hLipQ : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      ∀ w ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      ‖chemFluxEWA μ ν p.β γ hμ u - chemFluxEWA μ ν p.β γ hμ w‖ ≤ L_Q * ‖u - w‖)
    (hLipG : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      ∀ w ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      ‖growthEWA p.α p.a p.b u - growthEWA p.α p.a p.b w‖ ≤ L_G * ‖u - w‖)
    (hKnn : (0 : ℝ) ≤ |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T)
    (hK : |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T < 1) :
    ∃ u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      u_star = picardEWA p μ ν γ hμ hT u₀E u_star := by
  set B : Set (EWA T 1) := Metric.closedBall (heatEWA u₀E) ρ with hB
  set Φ : EWA T 1 → EWA T 1 := picardEWA p μ ν γ hμ hT u₀E with hΦ
  set K : ℝ := |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T with hKdef
  -- The good ball is complete (closed in a complete space).
  have hBc : IsComplete B :=
    (Metric.isClosed_closedBall (x := heatEWA u₀E) (ε := ρ)).isComplete
  -- The restriction of `Φ` to `B` is `K`-Lipschitz, with `K < 1`.
  have hKnn' : (0 : ℝ) ≤ K := hKnn
  have hlip : ContractingWith K.toNNReal (hself.restrict Φ B B) := by
    refine ⟨?_, ?_⟩
    · -- `K.toNNReal < 1`.
      exact Real.toNNReal_lt_one.mpr hK
    · -- Lipschitz on the subtype, from the real contraction bound.
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      rw [Subtype.dist_eq, Subtype.dist_eq, MapsTo.val_restrict_apply, MapsTo.val_restrict_apply]
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal K hKnn']
      have hQ := hLipQ a.1 a.2 b.1 b.2
      have hG := hLipG a.1 a.2 b.1 b.2
      exact picardEWA_contraction hμ hT u₀E hQ hG
  -- Start from the centre `heatEWA u₀E ∈ B`; `edist` is finite in a metric space.
  have hx : (heatEWA (T := T) u₀E) ∈ B := by
    rw [hB]; exact Metric.mem_closedBall_self hρ
  have hedist : edist (heatEWA (T := T) u₀E) (Φ (heatEWA u₀E)) ≠ ⊤ := edist_ne_top _ _
  obtain ⟨u_star, hmem, hfix, _, _⟩ := hlip.exists_fixedPoint' hBc hself hx hedist
  exact ⟨u_star, hmem, hfix.eq.symm⟩

end ShenWork.EWA

#print axioms ShenWork.EWA.picardEWA_sub
#print axioms ShenWork.EWA.picardEWA_contraction
#print axioms ShenWork.EWA.picardEWA_exists_fixedPoint
