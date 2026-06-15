import ShenWork.Wiener.EWA.SourceRealizesAssembly
import ShenWork.Wiener.EWA.SourceFixedPoint
import Mathlib.Topology.MetricSpace.Contracting

/-!
# EWA capstone (χ₀<0 Route A) — the Picard fixed point is even-real

`realizes_of_picardFixedPoint` (`SourceRealizesAssembly.lean`) carries the parity
hypothesis `hER_star : EvenRealEWA u_star` for a source-form Picard fixed point.  This
file DISCHARGES it.

## Architecture

* **`picardEWA_evenReal` (Φ-preservation, fully unconditional).**  The source Picard map
  `Φ(U) = heatEWA u₀E + (−χ₀)•𝒟(chemFluxEWA U) + 𝒱(growthEWA U)` sends even-real to
  even-real:
  - the heat term is even-real (`heatEWA_evenReal`);
  - `chemFluxEWA U` is odd-imaginary (`chemFluxEWA_oddImag`, via the committed
    `FnegEWA_evenReal_Hyp_proved`), so `𝒟(·)` of it is even-real
    (`OddImagEWA.divDuhamelEWA`), then `(−χ₀:ℝ)•(·)` even-real (`EvenRealEWA.smul_real`);
  - `growthEWA U` even-real (`growthEWA_evenReal`), so `𝒱(·)` even-real
    (`EvenRealEWA.valDuhamelEWA`);
  - the sum is even-real (`EvenRealEWA.add`).

* **`isClosed_evenReal` (closedness).**  `EvenRealEWA U` is an intersection of preimages
  of the closed singleton `{0}` / closed equalisers under the continuous functionals
  `U ↦ (sliceWA τ U).toFun n` (continuous as `‖(U.toFun n) τ‖ ≤ ‖U‖`), hence closed.

* **`picardEWA_evenReal_fixedPoint` (Route A assembly).**  Re-invoking the `ContractingWith`
  machinery of `picardEWA_exists_fixedPoint`, the Banach iterate `Φⁿ(heatEWA u₀E)` (each
  even-real by induction from the even-real `heatEWA u₀E`) tends to `efixedPoint'`, which is
  therefore even-real by `isClosed_evenReal`.  The carried fixed point `u_star` equals
  `efixedPoint'` by contraction uniqueness, so `EvenRealEWA u_star`.

NO `sorry`, `axiom`, `native_decide`, or `admit`.
-/

open scoped BigOperators NNReal ENNReal
open Set Metric Filter Topology Function
open ShenWork.GWA ShenWork.Wiener ShenWork.CosineSpectrum
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### Part 1 — `Φ` preserves even-real (unconditional). -/

/-- **`picardEWA` preserves even-real.**  For an even-real `u`, the Picard map applied to
it is even-real, where `u₀E = ⟨ofCosineCoeffs u₀cos, hmem⟩`.  The heat term is even-real
(`heatEWA_evenReal`), the chemotaxis-divergence term is even-real (`chemFluxEWA` is
odd-imaginary, `𝒟` flips it to even-real, the real scalar preserves it), and the growth
value term is even-real (`growthEWA` even-real, `𝒱` preserves it). -/
theorem picardEWA_evenReal (p : CM2Params) {μ ν γ : ℝ} (hμ : 0 < μ) (hT : (0 : ℝ) ≤ T)
    (u₀cos : ℕ → ℝ) (hmem : MemW 1 (ofCosineCoeffs u₀cos)) {u : EWA T 1}
    (hu : EvenRealEWA u) :
    EvenRealEWA (picardEWA p μ ν γ hμ hT (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1) u) := by
  rw [picardEWA]
  -- `(heat + (−χ₀)•𝒟(chemFlux)) + 𝒱(growth)`: each summand even-real.
  have hheat : EvenRealEWA (heatEWA (T := T) (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) :=
    heatEWA_evenReal u₀cos hmem
  have hchem : EvenRealEWA
      (((-p.χ₀ : ℝ) : ℂ) • divDuhamelEWA hT (chemFluxEWA μ ν p.β γ hμ u)) :=
    EvenRealEWA.smul_real (-p.χ₀)
      ((chemFluxEWA_oddImag FnegEWA_evenReal_Hyp_proved hμ hu).divDuhamelEWA hT)
  have hgrow : EvenRealEWA (valDuhamelEWA hT (growthEWA p.α p.a p.b u)) :=
    (growthEWA_evenReal FnegEWA_evenReal_Hyp_proved hu).valDuhamelEWA hT
  exact (hheat.add hchem).add hgrow

/-! ### Part 2 — `EvenRealEWA` is a closed predicate on `EWA T r`. -/

variable {r : ℕ}

/-- The slice-coefficient functional `U ↦ (sliceWA τ U).toFun n = (U.toFun n) τ` is
continuous on `EWA T r`: it is `1`-bounded via `‖(U.toFun n) τ‖ ≤ ‖U.toFun n‖ ≤ ‖U‖`. -/
theorem continuous_sliceCoeff (τ : TimeDom T) (n : ℤ) :
    Continuous (fun U : EWA T r => (sliceWA τ U).toFun n) := by
  have hcont : Continuous (fun U : EWA T r => (U.toFun n) τ) := by
    refine AddMonoidHomClass.continuous_of_bound
      ({ toFun := fun U : EWA T r => (U.toFun n) τ,
         map_add' := fun U V => by rw [GWA.add_toFun, Pi.add_apply, ContinuousMap.add_apply],
         map_zero' := by rw [GWA.zero_toFun, Pi.zero_apply, ContinuousMap.zero_apply] } :
        EWA T r →+ ℂ) 1 (fun U => ?_)
    have h1 : ‖(U.toFun n) τ‖ ≤ ‖U.toFun n‖ := ContinuousMap.norm_coe_le_norm (U.toFun n) τ
    have hw : (1 : ℝ) ≤ gWeight r n := by
      have hb : (1 : ℝ) ≤ 1 + |(n : ℝ)| := le_add_of_nonneg_right (abs_nonneg _)
      simpa only [gWeight] using one_le_pow₀ hb
    have hterm : ‖U.toFun n‖ ≤ gWeight r n * ‖U.toFun n‖ := by
      calc ‖U.toFun n‖ = 1 * ‖U.toFun n‖ := (one_mul _).symm
        _ ≤ gWeight r n * ‖U.toFun n‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    have h2 : ‖U.toFun n‖ ≤ ‖U‖ := by
      rw [GWA.norm_def, gNorm]
      exact le_trans hterm
        (U.mem.le_tsum n (fun m _ => gWeightedNorm_nonneg r U.toFun m))
    calc ‖(U.toFun n) τ‖ ≤ ‖U.toFun n‖ := h1
      _ ≤ ‖U‖ := h2
      _ = 1 * ‖U‖ := (one_mul _).symm
  simpa only [coeff_sliceWA] using hcont

/-- **`EvenRealEWA` is closed.**  It is the intersection over `(τ, n)` of the closed sets
`{U | (sliceWA τ U).toFun (-n) = (sliceWA τ U).toFun n}` and
`{U | ((sliceWA τ U).toFun n).im = 0}`, each a closed equaliser / preimage of a closed set
under the continuous slice-coefficient functionals. -/
theorem isClosed_evenReal : IsClosed {U : EWA T r | EvenRealEWA U} := by
  have hset : {U : EWA T r | EvenRealEWA U}
      = (⋂ (τ : TimeDom T) (n : ℤ),
          {U : EWA T r | (sliceWA τ U).toFun (-n) = (sliceWA τ U).toFun n})
        ∩ (⋂ (τ : TimeDom T) (n : ℤ), {U : EWA T r | ((sliceWA τ U).toFun n).im = 0}) := by
    ext U
    constructor
    · intro hU
      exact ⟨by simp only [mem_iInter, mem_setOf_eq]; exact fun τ n => hU.even τ n,
        by simp only [mem_iInter, mem_setOf_eq]; exact fun τ n => hU.real τ n⟩
    · rintro ⟨he, hr⟩
      simp only [mem_iInter, mem_setOf_eq] at he hr
      exact ⟨he, hr⟩
  rw [hset]
  refine IsClosed.inter ?_ ?_
  · refine isClosed_iInter (fun τ => isClosed_iInter (fun n => ?_))
    exact isClosed_eq (continuous_sliceCoeff τ (-n)) (continuous_sliceCoeff τ n)
  · refine isClosed_iInter (fun τ => isClosed_iInter (fun n => ?_))
    exact isClosed_eq (Complex.continuous_im.comp (continuous_sliceCoeff τ n)) continuous_const

/-! ### Part 3 — Route A: the Picard fixed point is even-real. -/

/-- **THE DISCHARGE — `EvenRealEWA u_star`.**  Re-invoking the `ContractingWith` machinery
on the good ball `B = closedBall (heatEWA u₀E) ρ` (the same contraction data the existence
theorem `picardEWA_exists_fixedPoint` carries), the Banach iterate from the even-real centre
`heatEWA u₀E` converges to `efixedPoint'`, which is even-real by `isClosed_evenReal`.  The
carried fixed point `u_star ∈ B` equals `efixedPoint'` by contraction uniqueness, so it is
even-real.

The hypotheses `hself`/`hLipQ`/`hLipG`/`hKnn`/`hK` are exactly those of
`picardEWA_exists_fixedPoint`; `hmem_star` places the given fixed point in the good ball. -/
theorem picardEWA_evenReal_fixedPoint (p : CM2Params) {μ ν γ ρ L_Q L_G : ℝ}
    (hμ : 0 < μ) (hT : (0 : ℝ) ≤ T) (u₀cos : ℕ → ℝ) (hmem : MemW 1 (ofCosineCoeffs u₀cos))
    (hρ : 0 ≤ ρ)
    (hself : MapsTo (picardEWA p μ ν γ hμ hT (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1))
      (Metric.closedBall (heatEWA (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ)
      (Metric.closedBall (heatEWA (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ))
    (hLipQ : ∀ a ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ∀ b ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ‖chemFluxEWA μ ν p.β γ hμ a - chemFluxEWA μ ν p.β γ hμ b‖ ≤ L_Q * ‖a - b‖)
    (hLipG : ∀ a ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ∀ b ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ‖growthEWA p.α p.a p.b a - growthEWA p.α p.a p.b b‖ ≤ L_G * ‖a - b‖)
    (hKnn : (0 : ℝ) ≤ |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T)
    (hK : |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T < 1)
    (u_star : EWA T 1)
    (hmem_star : u_star ∈ Metric.closedBall (heatEWA (T := T)
      (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ)
    (hfix : u_star = picardEWA p μ ν γ hμ hT (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1) u_star) :
    EvenRealEWA u_star := by
  set u₀E : WA 1 := ⟨ofCosineCoeffs u₀cos, hmem⟩ with hu₀E
  set B : Set (EWA T 1) := Metric.closedBall (heatEWA u₀E) ρ with hB
  set Φ : EWA T 1 → EWA T 1 := picardEWA p μ ν γ hμ hT u₀E with hΦ
  set K : ℝ := |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T with hKdef
  -- The good ball is complete (closed in a complete space).
  have hBc : IsComplete B :=
    (Metric.isClosed_closedBall (x := heatEWA u₀E) (ε := ρ)).isComplete
  have hKnn' : (0 : ℝ) ≤ K := hKnn
  -- The restriction of `Φ` to `B` is `K`-Lipschitz with `K < 1` (as in the existence proof).
  have hlip : ContractingWith K.toNNReal (hself.restrict Φ B B) := by
    refine ⟨Real.toNNReal_lt_one.mpr hK, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Subtype.dist_eq, Subtype.dist_eq, MapsTo.val_restrict_apply, MapsTo.val_restrict_apply,
      dist_eq_norm, dist_eq_norm, Real.coe_toNNReal K hKnn']
    exact picardEWA_contraction hμ hT u₀E (hLipQ a.1 a.2 b.1 b.2) (hLipG a.1 a.2 b.1 b.2)
  -- Start the iteration from the even-real centre `heatEWA u₀E ∈ B`.
  have hxB : (heatEWA (T := T) u₀E) ∈ B := Metric.mem_closedBall_self hρ
  have hedist : edist (heatEWA (T := T) u₀E) (Φ (heatEWA u₀E)) ≠ ⊤ := edist_ne_top _ _
  -- `efixedPoint'` is the iterate limit.
  set w : EWA T 1 := ContractingWith.efixedPoint' Φ hBc hself hlip (heatEWA u₀E) hxB hedist
    with hw
  have htend : Tendsto (fun n => Φ^[n] (heatEWA u₀E)) atTop (𝓝 w) :=
    hlip.tendsto_iterate_efixedPoint' hBc hself hxB hedist
  -- Each iterate `Φⁿ(heatEWA u₀E)` is even-real (induction from the even-real centre).
  have hiter : ∀ n : ℕ, EvenRealEWA (Φ^[n] (heatEWA u₀E)) := by
    intro n
    induction n with
    | zero => simpa using heatEWA_evenReal u₀cos hmem
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact picardEWA_evenReal p hμ hT u₀cos hmem ih
  -- The limit `w` is even-real (closedness).
  have hwER : EvenRealEWA w :=
    isClosed_evenReal.mem_of_tendsto htend (Filter.Eventually.of_forall hiter)
  -- `u_star = w` by contraction uniqueness on `B`.
  have hfixΦ : Φ u_star = u_star := hfix.symm
  have hfixw : Φ w = w := hlip.efixedPoint_isFixedPt' hBc hself hxB hedist
  -- Lift both to the subtype `B` and apply `ContractingWith.fixedPoint_unique'`.
  have hus : IsFixedPt (hself.restrict Φ B B) ⟨u_star, hmem_star⟩ := by
    apply Subtype.ext
    rw [MapsTo.val_restrict_apply]; exact hfixΦ
  have hws : IsFixedPt (hself.restrict Φ B B)
      ⟨w, hlip.efixedPoint_mem' hBc hself hxB hedist⟩ := by
    apply Subtype.ext
    rw [MapsTo.val_restrict_apply]; exact hfixw
  have heq : (⟨u_star, hmem_star⟩ : B) = ⟨w, _⟩ := hlip.fixedPoint_unique' hus hws
  have huw : u_star = w := congrArg Subtype.val heq
  rw [huw]; exact hwER

end ShenWork.EWA

#print axioms ShenWork.EWA.picardEWA_evenReal
#print axioms ShenWork.EWA.isClosed_evenReal
#print axioms ShenWork.EWA.picardEWA_evenReal_fixedPoint
