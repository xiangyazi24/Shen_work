/-
  ShenWork/Wiener/EWA/SourceFixedPointEvenReal.lean

  **The UNCONDITIONAL χ₀<0 EWA fixed point — no `hVdFloor` hypothesis.**

  This is a variant of `picardEWA_clean_fixedPoint` (`SourceFixedPointClean.lean`)
  that ELIMINATES the carried hypothesis `hVdFloor` entirely by:

  1. Restricting the Banach contraction to the EvenReal ball:
     `B' = closedBall(heatEWA u₀E, ρ) ∩ {u | EvenRealEWA u}`.
  2. Using `vdEWA_floor_of_evenReal` (`SourceVdFloorGeneric.lean`) to derive
     `UniformFloor (1 + vdEWA u) 1` for every EvenReal ball element.
  3. Setting `δv = 1` (the optimal value from the generic vd-floor theorem).

  The EvenReal ball `B'` is complete (intersection of two closed sets —
  `isClosed_closedBall` and `isClosed_evenReal`). The Picard map preserves
  EvenReal (`picardEWA_evenReal`) and the ball self-map + Lipschitz bounds
  hold on B' elements using the derived vd-floor.

  **Key architectural point:** the ball self-map proof is INLINED rather than
  delegating to `picardEWA_mapsTo`, because `mapsTo` needs M_Q bounds on
  ALL ball elements (including non-EvenReal), while we only have M_Q bounds
  for EvenReal ball elements. The inlined version applies M_Q directly to
  the specific EvenReal ball element u, avoiding the universal quantifier.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceFixedPointClean
import ShenWork.Wiener.EWA.SourceVdFloorGeneric
import ShenWork.Wiener.EWA.SourceFixedPointParity

open Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-- **THE UNCONDITIONAL CLEAN FIXED POINT on the EvenReal ball.**

From standard datum facts (continuous `u₀` with positive floor and ℓ¹ cosine
coefficients), the χ₀<0 Picard map has a fixed point — with NO carried
hypothesis on the `1+v` floor.

Compared to `picardEWA_clean_fixedPoint`:
- **REMOVED:** `δv` parameter and `hVdFloor` hypothesis
- **ADDED:** `hνpos : 0 ≤ p.ν` (always satisfied from `CM2Params`)
- `δv = 1` is computed internally (optimal value from `vdEWA_floor_of_evenReal`)
- Result additionally certifies `EvenRealEWA u_star` -/
theorem picardEWA_clean_fixedPoint_evenReal {p : CM2Params}
    (u₀ : ℝ → ℝ) (hu₀ : Continuous u₀) {δ : ℝ} (hδpos : 0 < δ)
    (hfloor : ∀ y, δ ≤ u₀ y)
    (hsum : Summable (fun k => |cosineCoeffs u₀ k|))
    (hmem : MemW 1 (ofCosineCoeffs (cosineCoeffs u₀)))
    (hβpos : 0 < p.β) (hνpos : 0 ≤ p.ν) :
    ∃ (T : ℝ) (hTpos : 0 < T),
      ∃ u_star ∈ Metric.closedBall
          (heatEWA (T := T) (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1)) (δ / 2),
        EvenRealEWA u_star ∧
        u_star = picardEWA p p.μ p.ν p.γ p.hμ hTpos.le
          (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1) u_star := by
  classical
  -- abbreviations for the realized datum.
  set u₀E : WA 1 := ⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ with hu₀E
  set ρ : ℝ := δ / 2 with hρ_def
  have hρpos : 0 < ρ := by rw [hρ_def]; linarith
  have hρnn : 0 ≤ ρ := hρpos.le
  have hδρpos : 0 < δ - ρ := by rw [hρ_def]; linarith
  -- δv = 1: the optimal value from vdEWA_floor_of_evenReal.
  set δv : ℝ := 1 with hδv_def
  have hδvpos : 0 < δv := by rw [hδv_def]; exact one_pos
  -- T-independent radius R = ‖u₀E‖ + ρ.
  set R : ℝ := ‖u₀E‖ + ρ with hR_def
  have hRnn : 0 ≤ R := by rw [hR_def]; positivity
  -- T-independent derivative bounds.
  set Md : ℝ := Real.pi * R with hMd_def
  have hMdnn : 0 ≤ Md := by rw [hMd_def]; positivity
  set Mdv : ℝ := Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
      (R ^ (Nat.floor p.γ + 1)
        * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md))) with hMdv_def
  have hCμnn : (0 : ℝ) ≤ GWA.resolverGainConst p.μ := by
    unfold GWA.resolverGainConst; have := p.hμ; positivity
  have hγnn : 0 ≤ p.γ := p.hγ.le
  have hαnn : 0 ≤ p.α := p.hα.le
  -- T-independent norm constants M_Q, M_G (with δv = 1).
  set M_Q : ℝ := R * (Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
        (R ^ (Nat.floor p.γ + 1)
          * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md))))
      * negNormConst p.β δv Mdv with hMQ_def
  set M_G : ℝ := R * (|p.a| * 1 + |p.b| *
      (R ^ (Nat.floor p.α + 1)
        * negNormConst ((Nat.floor p.α + 1 : ℝ) - p.α) (δ - ρ) Md)) with hMG_def
  -- T-independent Lipschitz constants L_Q, L_G (with δv = 1).
  set L_Q : ℝ := (Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
              (R ^ (Nat.floor p.γ + 1)
                * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md))))
            * negNormConst p.β δv Mdv * 1
          + R * negNormConst p.β δv Mdv * (Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
              ((Nat.floor p.γ + 1 : ℝ) * R ^ ((Nat.floor p.γ + 1) - 1)
                  * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md
                + R ^ (Nat.floor p.γ + 1)
                  * negLipConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md))))
          + R * (Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
              (R ^ (Nat.floor p.γ + 1)
                * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md))))
            * (negLipConst p.β δv Mdv * (GWA.resolverGainConst p.μ * (|p.ν| *
                ((Nat.floor p.γ + 1 : ℝ) * R ^ ((Nat.floor p.γ + 1) - 1)
                    * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md
                  + R ^ (Nat.floor p.γ + 1)
                    * negLipConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md)))) with hLQ_def
  set L_G : ℝ := R * (|p.b| * ((Nat.floor p.α + 1 : ℝ) * R ^ ((Nat.floor p.α + 1) - 1)
              * negNormConst ((Nat.floor p.α + 1 : ℝ) - p.α) (δ - ρ) Md
            + R ^ (Nat.floor p.α + 1)
              * negLipConst ((Nat.floor p.α + 1 : ℝ) - p.α) (δ - ρ) Md))
          + (|p.a| * 1 + |p.b| *
              (R ^ (Nat.floor p.α + 1)
                * negNormConst ((Nat.floor p.α + 1 : ℝ) - p.α) (δ - ρ) Md)) with hLG_def
  -- nonnegativity of the Γ-combination constants.
  have hsγ : 0 < (Nat.floor p.γ + 1 : ℝ) - p.γ := by
    have := Nat.lt_floor_add_one p.γ; linarith
  have hsα : 0 < (Nat.floor p.α + 1 : ℝ) - p.α := by
    have := Nat.lt_floor_add_one p.α; linarith
  have hnegNγ : (0 : ℝ) ≤ negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md :=
    negNormConst_nonneg hsγ hδρpos hMdnn
  have hnegLγ : (0 : ℝ) ≤ negLipConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md :=
    negLipConst_nonneg hsγ hδρpos hMdnn
  have hnegNα : (0 : ℝ) ≤ negNormConst ((Nat.floor p.α + 1 : ℝ) - p.α) (δ - ρ) Md :=
    negNormConst_nonneg hsα hδρpos hMdnn
  have hnegLα : (0 : ℝ) ≤ negLipConst ((Nat.floor p.α + 1 : ℝ) - p.α) (δ - ρ) Md :=
    negLipConst_nonneg hsα hδρpos hMdnn
  have hMdvnn : 0 ≤ Mdv := by rw [hMdv_def]; positivity
  have hnegNv : (0 : ℝ) ≤ negNormConst p.β δv Mdv := negNormConst_nonneg hβpos hδvpos hMdvnn
  have hnegLv : (0 : ℝ) ≤ negLipConst p.β δv Mdv := negLipConst_nonneg hβpos hδvpos hMdvnn
  have hMQnn : 0 ≤ M_Q := by rw [hMQ_def]; positivity
  have hMGnn : 0 ≤ M_G := by rw [hMG_def]; positivity
  have hLQnn : 0 ≤ L_Q := by rw [hLQ_def]; positivity
  have hLGnn : 0 ≤ L_G := by rw [hLG_def]; positivity
  -- choose T > 0 small for BOTH the contraction and the self-map.
  obtain ⟨T, hTpos, hKlt, hsmall⟩ :=
    exists_small_two_conditions (A := |p.χ₀| * C₀ * L_Q) (B := L_G)
      (A' := |p.χ₀| * C₀ * M_Q) (B' := M_G)
      (by have := C₀_nonneg; positivity) hLGnn
      (by have := C₀_nonneg; positivity) hMGnn hρpos
  have hT : (0 : ℝ) ≤ T := hTpos.le
  refine ⟨T, hTpos, ?_⟩
  -- the Picard map Φ and contraction constant K.
  set Φ : EWA T 1 → EWA T 1 := picardEWA p p.μ p.ν p.γ p.hμ hT u₀E with hΦ
  set K : ℝ := |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T with hKdef
  -- the heat floor from datum facts.
  have hheat : UniformFloor (heatEWA (T := T) u₀E) δ := by
    rw [hu₀E]; exact heatEWA_uniformFloor (T := T) hu₀ hfloor hsum hmem
  -- ball side-data (uniform on B = closedBall(heatEWA u₀E, ρ)).
  have hball_norm : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ, ‖u‖ ≤ R := by
    intro u hu
    rw [Metric.mem_closedBall, dist_eq_norm] at hu
    have htri : ‖u‖ ≤ ‖u - heatEWA (T := T) u₀E‖ + ‖heatEWA (T := T) u₀E‖ := by
      have := norm_add_le (u - heatEWA (T := T) u₀E) (heatEWA (T := T) u₀E); simpa using this
    have hhle : ‖heatEWA (T := T) u₀E‖ ≤ ‖u₀E‖ := heatEWA_norm_le u₀E
    rw [hR_def]; linarith
  have hball_floor : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      UniformFloor u (δ - ρ) := fun u hu => uniformFloor_on_ball hheat hu
  have hMD : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ, ‖GWA.gDeriv u‖ ≤ Md := by
    intro u hu
    refine le_trans (norm_gDeriv_apply_le u) ?_
    rw [hMd_def]; exact mul_le_mul_of_nonneg_left (hball_norm u hu) Real.pi_nonneg
  -- *** THE KEY STEP: vdFloor from vdEWA_floor_of_evenReal for EvenReal ball elements. ***
  have hVdF_er : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      EvenRealEWA u → UniformFloor (1 + vdEWA p.μ p.ν p.γ p.hμ u) 1 := by
    intro u hu huer
    exact vdEWA_floor_of_evenReal p u huer hδρpos (hball_floor u hu) hνpos
  -- vd derivative bound (no EvenReal needed).
  have hVdD : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      ‖GWA.gDeriv (vdEWA p.μ p.ν p.γ p.hμ u)‖ ≤ Mdv := by
    intro u hu
    rw [hMdv_def]
    exact vdEWA_gDeriv_norm_le p.hμ hγnn hδρpos hMdnn (hball_floor u hu) (hMD u hu)
      (hball_norm u hu) hRnn
  have hone : ‖(1 : EWA T 1)‖ = 1 := norm_one_EWA hT
  -- the self-map smallness.
  have hsmall' : |p.χ₀| * (C₀ * Real.sqrt T) * M_Q + T * M_G ≤ ρ := by
    have heq : |p.χ₀| * C₀ * M_Q * Real.sqrt T + M_G * T
        = |p.χ₀| * (C₀ * Real.sqrt T) * M_Q + T * M_G := by ring
    rw [heq] at hsmall; exact hsmall
  -- the EvenReal ball B' = B ∩ {EvenRealEWA}.
  set B : Set (EWA T 1) := Metric.closedBall (heatEWA u₀E) ρ with hB_def
  set B' : Set (EWA T 1) := B ∩ {u | EvenRealEWA u} with hB'_def
  -- B' is complete (intersection of two closed sets in a Banach space).
  have hB'c : IsComplete B' :=
    (Metric.isClosed_closedBall.inter isClosed_evenReal).isComplete
  -- the center heatEWA u₀E is in B'.
  have hcenter_ball : (heatEWA (T := T) u₀E) ∈ B := Metric.mem_closedBall_self hρnn
  have hcenter_er : EvenRealEWA (heatEWA (T := T) u₀E) := by
    rw [hu₀E]; exact heatEWA_evenReal (cosineCoeffs u₀) hmem
  have hcenter : (heatEWA (T := T) u₀E) ∈ B' := ⟨hcenter_ball, hcenter_er⟩
  -- Φ maps B' to B' (ball self-map + EvenReal preservation — INLINED, not via picardEWA_mapsTo).
  have hself : MapsTo Φ B' B' := by
    intro u ⟨hu_ball, hu_er⟩
    constructor
    · -- Φ(u) ∈ B: ‖Φ(u) − center‖ ≤ |χ₀|·C₀√T·‖Q(u)‖ + T·‖G(u)‖ ≤ ρ.
      rw [hB_def, Metric.mem_closedBall, dist_eq_norm]
      refine le_trans (picardEWA_perturbation_norm_le p p.hμ hT u₀E u) ?_
      refine le_trans (add_le_add ?_ ?_) hsmall'
      · -- |χ₀|·C₀√T·‖Q(u)‖ ≤ |χ₀|·C₀√T·M_Q (using vdFloor from EvenReal).
        refine mul_le_mul_of_nonneg_left ?_ (by have := C₀_nonneg; positivity)
        rw [hMQ_def]
        exact chemFluxEWA_norm_le p.hμ hγnn hβpos hδρpos hδvpos hMdnn hMdvnn
          (hball_floor u hu_ball) (hMD u hu_ball) (hball_norm u hu_ball) hRnn
          (hVdF_er u hu_ball hu_er) (hVdD u hu_ball)
      · -- T·‖G(u)‖ ≤ T·M_G (growth bound, no vdFloor needed).
        refine mul_le_mul_of_nonneg_left ?_ hT
        rw [hMG_def]
        have h := growthEWA_norm_le (α := p.α) (a := p.a) (b := p.b) (u := u)
          hαnn hδρpos hMdnn (hball_floor u hu_ball) (hMD u hu_ball) (hball_norm u hu_ball) hRnn
        rw [hone] at h; exact h
    · -- Φ(u) is EvenReal.
      rw [hΦ, hu₀E]
      exact picardEWA_evenReal p p.hμ hT (cosineCoeffs u₀) hmem hu_er
  -- Lipschitz bounds on B' (flux uses derived vdFloor from EvenReal).
  have hLipQ : ∀ a ∈ B', ∀ b ∈ B',
      ‖chemFluxEWA p.μ p.ν p.β p.γ p.hμ a - chemFluxEWA p.μ p.ν p.β p.γ p.hμ b‖
        ≤ L_Q * ‖a - b‖ := by
    intro u ⟨hu_ball, hu_er⟩ w ⟨hw_ball, hw_er⟩
    rw [hLQ_def]
    exact chemFluxEWA_lipschitz p.hμ hγnn hβpos hδρpos hδvpos hMdnn hMdvnn
      (hball_floor u hu_ball) (hball_floor w hw_ball)
      (hMD u hu_ball) (hMD w hw_ball)
      (hball_norm u hu_ball) (hball_norm w hw_ball) hRnn
      (hVdF_er u hu_ball hu_er) (hVdF_er w hw_ball hw_er)
      (hVdD u hu_ball) (hVdD w hw_ball)
  have hLipG : ∀ a ∈ B', ∀ b ∈ B',
      ‖growthEWA p.α p.a p.b a - growthEWA p.α p.a p.b b‖ ≤ L_G * ‖a - b‖ := by
    intro u ⟨hu_ball, _⟩ w ⟨hw_ball, _⟩
    have h := growthEWA_lipschitz hαnn hδρpos hMdnn
      (hball_floor u hu_ball) (hball_floor w hw_ball)
      (hMD u hu_ball) (hMD w hw_ball)
      (hball_norm u hu_ball) (hball_norm w hw_ball) hRnn
    rw [hone] at h; exact h
  -- contraction constant K and its bounds.
  have hKnn : (0 : ℝ) ≤ K := by
    rw [hKdef]; have := C₀_nonneg; have hsq : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T; positivity
  have hK : K < 1 := by
    rw [hKdef]
    have heq : |p.χ₀| * C₀ * L_Q * Real.sqrt T + L_G * T
        = |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T := by ring
    rw [heq] at hKlt; exact hKlt
  -- Φ restricted to B' is K-contracting.
  have hlip : ContractingWith K.toNNReal (hself.restrict Φ B' B') := by
    refine ⟨Real.toNNReal_lt_one.mpr hK, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Subtype.dist_eq, Subtype.dist_eq, MapsTo.val_restrict_apply, MapsTo.val_restrict_apply,
      dist_eq_norm, dist_eq_norm, Real.coe_toNNReal K hKnn]
    exact picardEWA_contraction p.hμ hT u₀E (hLipQ a.1 a.2 b.1 b.2) (hLipG a.1 a.2 b.1 b.2)
  -- Banach fixed point on B'.
  have hedist : edist (heatEWA (T := T) u₀E) (Φ (heatEWA u₀E)) ≠ ⊤ := edist_ne_top _ _
  obtain ⟨u_star, hmem, hfix, _, _⟩ := hlip.exists_fixedPoint' hB'c hself hcenter hedist
  exact ⟨u_star, hmem.1, hmem.2, hfix.eq.symm⟩

end ShenWork.EWA

#print axioms ShenWork.EWA.picardEWA_clean_fixedPoint_evenReal
