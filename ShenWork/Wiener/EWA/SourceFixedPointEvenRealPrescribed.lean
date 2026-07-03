/-
  ShenWork/Wiener/EWA/SourceFixedPointEvenRealPrescribed.lean

  **Prescribed-T variant of `picardEWA_clean_fixedPoint_evenReal`.**

  The original clean FP CHOOSES T internally. This variant takes T as input
  along with proof that the contraction and self-map conditions hold at T.

  Key design: takes `normBound ≥ ‖u₀E‖` and uses it for ALL ball estimates.
  The ball norm bound ‖u‖ ≤ normBound + δ/2 follows from ‖u₀E‖ ≤ normBound.
  All contraction/self-map constants are computed at (normBound, δ) — these are
  EXACTLY `CleanFPConst` at (normBound, δ), which are ≥ the per-datum constants.
  NO MONOTONICITY LEMMAS NEEDED: using normBound everywhere is consistent.

  This enables the UNIFORM datum construction:
  - `exists_uniform_EWA_lifespan` gives δ at bar-constants = CleanFPConst(WM, fm)
  - This theorem runs at T = δ with normBound = WM for EACH datum
  - All datums with ‖u₀E‖ ≤ WM get a fixed point at the SAME time T

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceFixedPointEvenReal
import ShenWork.Wiener.EWA.SourceCleanFPConstants

open Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

noncomputable section

namespace ShenWork.EWA

/-- **THE CLEAN FIXED POINT ON THE EVENREAL BALL AT A PRESCRIBED TIME T.**

Same Banach construction as `picardEWA_clean_fixedPoint_evenReal`, but T is
provided externally. Uses `normBound ≥ ‖u₀E‖` for ALL ball estimates (not
just the conditions), so no monotonicity lemmas are needed.

The proof is the same 110-line Banach construction as the original, with:
- `R = normBound + δ/2` (instead of `‖u₀E‖ + δ/2`)
- `T` given by parameter (instead of chosen by `exists_small_two_conditions`)
- The contraction/self-map conditions at T hold by hypothesis

Ball membership `‖u‖ ≤ R` follows from:
  `‖u‖ ≤ ‖heatEWA u₀E‖ + ρ ≤ ‖u₀E‖ + ρ ≤ normBound + ρ = R` ✓

The `EvenRealEWA` preservation and vdFloor from `vdEWA_floor_of_evenReal`
are T-independent and work at any prescribed T. -/
theorem picardEWA_clean_fixedPoint_evenReal_prescribedT (p : CM2Params)
    (u₀ : ℝ → ℝ) (hu₀ : Continuous u₀) {δ : ℝ} (hδpos : 0 < δ)
    (hfloor : ∀ y, δ ≤ u₀ y)
    (hsum : Summable (fun k => |cosineCoeffs u₀ k|))
    (hmem : MemW 1 (ofCosineCoeffs (cosineCoeffs u₀)))
    (hβpos : 0 < p.β) (hνpos : 0 ≤ p.ν)
    {normBound : ℝ} (hnormBound : 0 ≤ normBound)
    (hnorm : ‖(⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1)‖ ≤ normBound)
    (T : ℝ) (hTpos : 0 < T)
    (hKlt : |p.χ₀| * C₀ * CleanFPConst.L_Q p normBound δ * Real.sqrt T
        + CleanFPConst.L_G p normBound δ * T < 1)
    (hsmall : |p.χ₀| * C₀ * CleanFPConst.M_Q p normBound δ * Real.sqrt T
        + CleanFPConst.M_G p normBound δ * T ≤ δ / 2) :
    ∃ u_star ∈ Metric.closedBall
        (heatEWA (T := T) (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1)) (δ / 2),
      EvenRealEWA u_star ∧
      u_star = picardEWA p p.μ p.ν p.γ p.hμ hTpos.le
        (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1) u_star := by
  classical
  set u₀E : WA 1 := ⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ with hu₀E
  set ρ : ℝ := δ / 2 with hρ_def
  have hρpos : 0 < ρ := by rw [hρ_def]; linarith
  have hρnn : 0 ≤ ρ := hρpos.le
  have hδρpos : 0 < δ - ρ := by rw [hρ_def]; linarith
  set R : ℝ := normBound + ρ with hR_def
  have hRnn : 0 ≤ R := by rw [hR_def]; linarith
  have hR_is : R = CleanFPConst.R normBound δ := by unfold CleanFPConst.R; rw [hR_def, hρ_def]
  set Md : ℝ := Real.pi * R with hMd_def
  have hMdnn : 0 ≤ Md := by rw [hMd_def]; positivity
  set Mdv : ℝ := Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
      (R ^ (Nat.floor p.γ + 1)
        * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md))) with hMdv_def
  have hγnn : 0 ≤ p.γ := p.hγ.le
  have hαnn : 0 ≤ p.α := p.hα.le
  -- ball norm bound: uses normBound, NOT ‖u₀E‖.
  have hball_norm : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ, ‖u‖ ≤ R := by
    intro u hu
    rw [Metric.mem_closedBall, dist_eq_norm] at hu
    have htri : ‖u‖ ≤ ‖u - heatEWA (T := T) u₀E‖ + ‖heatEWA (T := T) u₀E‖ := by
      have := norm_add_le (u - heatEWA (T := T) u₀E) (heatEWA (T := T) u₀E); simpa using this
    have hhle : ‖heatEWA (T := T) u₀E‖ ≤ ‖u₀E‖ := heatEWA_norm_le u₀E
    rw [hR_def]; linarith
  -- heat floor: from datum floor (T-independent)
  have hheat : UniformFloor (heatEWA (T := T) u₀E) δ := by
    rw [hu₀E]; exact heatEWA_uniformFloor (T := T) hu₀ hfloor hsum hmem
  have hball_floor : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      UniformFloor u (δ - ρ) := fun u hu => uniformFloor_on_ball hheat hu
  -- derivative and vdFloor bounds (T-independent, from normBound)
  have hMD : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ, ‖GWA.gDeriv u‖ ≤ Md := by
    intro u hu
    refine le_trans (norm_gDeriv_apply_le u) ?_
    rw [hMd_def]; exact mul_le_mul_of_nonneg_left (hball_norm u hu) Real.pi_nonneg
  have hVdF_er : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      EvenRealEWA u → UniformFloor (1 + vdEWA p.μ p.ν p.γ p.hμ u) 1 := by
    intro u hu huer
    exact vdEWA_floor_of_evenReal p u huer hδρpos (hball_floor u hu) hνpos
  have hVdD : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      ‖GWA.gDeriv (vdEWA p.μ p.ν p.γ p.hμ u)‖ ≤ Mdv := by
    intro u hu
    rw [hMdv_def]
    exact vdEWA_gDeriv_norm_le p.hμ hγnn hδρpos hMdnn (hball_floor u hu) (hMD u hu)
      (hball_norm u hu) hRnn
  -- Set up L_Q, L_G, M_Q, M_G with the SAME expressions as CleanFPConst.
  -- R = normBound + δ/2, δ-ρ = δ/2, δv = 1, Md = π*R, Mdv defined above.
  have hδvpos : 0 < (1 : ℝ) := one_pos
  set M_Q : ℝ := R * (Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
        (R ^ (Nat.floor p.γ + 1)
          * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md))))
      * negNormConst p.β 1 Mdv with hMQ_def
  set M_G : ℝ := R * (|p.a| * 1 + |p.b| *
      (R ^ (Nat.floor p.α + 1)
        * negNormConst ((Nat.floor p.α + 1 : ℝ) - p.α) (δ - ρ) Md)) with hMG_def
  set L_Q : ℝ := (Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
              (R ^ (Nat.floor p.γ + 1)
                * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md))))
            * negNormConst p.β 1 Mdv * 1
          + R * negNormConst p.β 1 Mdv * (Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
              ((Nat.floor p.γ + 1 : ℝ) * R ^ ((Nat.floor p.γ + 1) - 1)
                  * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md
                + R ^ (Nat.floor p.γ + 1)
                  * negLipConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md))))
          + R * (Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
              (R ^ (Nat.floor p.γ + 1)
                * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md))))
            * (negLipConst p.β 1 Mdv * (GWA.resolverGainConst p.μ * (|p.ν| *
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
  -- These expressions equal CleanFPConst at (normBound, δ) because:
  -- R = normBound + δ/2, δ-ρ = δ/2, δv = 1.
  have hLQ_eq : L_Q = CleanFPConst.L_Q p normBound δ := by
    unfold_let L_Q R Md Mdv ρ; unfold CleanFPConst.L_Q CleanFPConst.R CleanFPConst.Md CleanFPConst.Mdv
    ring
  have hLG_eq : L_G = CleanFPConst.L_G p normBound δ := by
    unfold_let L_G R Md ρ; unfold CleanFPConst.L_G CleanFPConst.R CleanFPConst.Md
    ring
  have hMQ_eq : M_Q = CleanFPConst.M_Q p normBound δ := by
    unfold_let M_Q R Md Mdv ρ; unfold CleanFPConst.M_Q CleanFPConst.R CleanFPConst.Md CleanFPConst.Mdv
    ring
  have hMG_eq : M_G = CleanFPConst.M_G p normBound δ := by
    unfold_let M_G R Md ρ; unfold CleanFPConst.M_G CleanFPConst.R CleanFPConst.Md
    ring
  -- Nonnegativity of Γ-combination constants.
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
  have hnegNv : (0 : ℝ) ≤ negNormConst p.β 1 Mdv := negNormConst_nonneg hβpos hδvpos hMdvnn
  have hnegLv : (0 : ℝ) ≤ negLipConst p.β 1 Mdv := negLipConst_nonneg hβpos hδvpos hMdvnn
  have hone : ‖(1 : EWA T 1)‖ = 1 := norm_one_EWA hTpos.le
  -- Rewrite hypothesized conditions to use local variables.
  have hKlt' : |p.χ₀| * C₀ * L_Q * Real.sqrt T + L_G * T < 1 := by
    rw [hLQ_eq, hLG_eq]; exact hKlt
  have hsmall' : |p.χ₀| * C₀ * M_Q * Real.sqrt T + M_G * T ≤ ρ := by
    rw [hMQ_eq, hMG_eq]; exact hsmall
  -- Rewrite to the form expected by the Banach construction.
  have hsmall'' : |p.χ₀| * (C₀ * Real.sqrt T) * M_Q + T * M_G ≤ ρ := by
    have heq : |p.χ₀| * C₀ * M_Q * Real.sqrt T + M_G * T
        = |p.χ₀| * (C₀ * Real.sqrt T) * M_Q + T * M_G := by ring
    rw [heq] at hsmall'; exact hsmall'
  -- the EvenReal ball B' = B ∩ {EvenRealEWA}.
  set B : Set (EWA T 1) := Metric.closedBall (heatEWA u₀E) ρ with hB_def
  set B' : Set (EWA T 1) := B ∩ {u | EvenRealEWA u} with hB'_def
  set Φ : EWA T 1 → EWA T 1 := picardEWA p p.μ p.ν p.γ p.hμ hTpos.le u₀E with hΦ
  set K : ℝ := |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T with hKdef
  -- B' is complete (intersection of two closed sets in a Banach space).
  have hB'c : IsComplete B' :=
    (Metric.isClosed_closedBall.inter isClosed_evenReal).isComplete
  -- the center heatEWA u₀E is in B'.
  have hcenter_ball : (heatEWA (T := T) u₀E) ∈ B := Metric.mem_closedBall_self hρnn
  have hcenter_er : EvenRealEWA (heatEWA (T := T) u₀E) := by
    rw [hu₀E]; exact heatEWA_evenReal (cosineCoeffs u₀) hmem
  have hcenter : (heatEWA (T := T) u₀E) ∈ B' := ⟨hcenter_ball, hcenter_er⟩
  -- Φ maps B' to B' (INLINED self-map + EvenReal preservation).
  have hself : MapsTo Φ B' B' := by
    intro u ⟨hu_ball, hu_er⟩
    constructor
    · rw [hB_def, Metric.mem_closedBall, dist_eq_norm]
      refine le_trans (picardEWA_perturbation_norm_le p p.hμ hTpos.le u₀E u) ?_
      refine le_trans (add_le_add ?_ ?_) hsmall''
      · refine mul_le_mul_of_nonneg_left ?_ (by have := C₀_nonneg; positivity)
        rw [hMQ_def]
        exact chemFluxEWA_norm_le p.hμ hγnn hβpos hδρpos hδvpos hMdnn hMdvnn
          (hball_floor u hu_ball) (hMD u hu_ball) (hball_norm u hu_ball) hRnn
          (hVdF_er u hu_ball hu_er) (hVdD u hu_ball)
      · refine mul_le_mul_of_nonneg_left ?_ hTpos.le
        rw [hMG_def]
        have h := growthEWA_norm_le (α := p.α) (a := p.a) (b := p.b) (u := u)
          hαnn hδρpos hMdnn (hball_floor u hu_ball) (hMD u hu_ball) (hball_norm u hu_ball) hRnn
        rw [hone] at h; exact h
    · rw [hΦ, hu₀E]
      exact picardEWA_evenReal p p.hμ hTpos.le (cosineCoeffs u₀) hmem hu_er
  -- Lipschitz bounds on B'.
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
  -- Contraction constant K and its bounds.
  have hKnn : (0 : ℝ) ≤ K := by
    rw [hKdef]; have := C₀_nonneg; have hsq : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T; positivity
  have hK : K < 1 := by
    rw [hKdef]
    have heq : |p.χ₀| * C₀ * L_Q * Real.sqrt T + L_G * T
        = |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T := by ring
    rw [heq] at hKlt'; exact hKlt'
  -- Φ restricted to B' is K-contracting.
  have hlip : ContractingWith K.toNNReal (hself.restrict Φ B' B') := by
    refine ⟨Real.toNNReal_lt_one.mpr hK, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Subtype.dist_eq, Subtype.dist_eq, MapsTo.val_restrict_apply, MapsTo.val_restrict_apply,
      dist_eq_norm, dist_eq_norm, Real.coe_toNNReal K hKnn]
    exact picardEWA_contraction p.hμ hTpos.le u₀E (hLipQ a.1 a.2 b.1 b.2) (hLipG a.1 a.2 b.1 b.2)
  -- Banach fixed point on B'.
  have hedist : edist (heatEWA (T := T) u₀E) (Φ (heatEWA u₀E)) ≠ ⊤ := edist_ne_top _ _
  obtain ⟨u_star, hmem', hfix, _, _⟩ := hlip.exists_fixedPoint' hB'c hself hcenter hedist
  exact ⟨u_star, hmem'.1, hmem'.2, hfix.eq.symm⟩

end ShenWork.EWA
