/-
  ShenWork/PDE/IntervalCoupledC1ResolverBallBridge.lean

  The C¹-ball ⇒ resolver-ball STRUCTURAL ASSEMBLY (χ₀<0 existence half #2).

  Bridge `IntervalCoupledResolverBallEstimates p (intervalNeumannResolverR p) u₀
  T M K` — the single-constant resolver-ball Prop the
  `CoupledFluxResolverAnalyticData` consumes — from:

    * the committed single-constant chemDiv flux Lipschitz `K·D` on the
      trajectory ball (interior `chemDivFlux_physical_KD_collapse` + the boundary
      residual, packaged as `hchem_KD`);
    * the committed integrability/measurability assembly
      `intervalCoupledResolver_hchem_hint_hlift` (gives hchem, hint, hlift_int);
    * the committed `intervalCoupledDuhamelOperator_bound_of_source_bound`
      (gives hmap, the sup-ball self-map, from the source sup + the
      constant choice `H_init + C·T ≤ M`).

  The four sup-ball conjuncts are assembled HERE; the genuine remaining honest
  input is `hchem_KD` (the C¹-snapshot regularity / parabolic-Schauder content,
  already collapsed to single-constant by the committed
  `chemDivFlux_physical_KD_collapse` + `gradDuhamel_hDg_le`), the source sup
  bounds, and the horizon/constant choices.

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.PDE.IntervalCoupledBallEstimates
import ShenWork.PDE.IntervalChemDivFluxC1PhysicalBridge
import ShenWork.PDE.IntervalChemDivFluxHDgWiring

open ShenWork.Paper2 ShenWork.IntervalDomain ShenWork.PDE MeasureTheory
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalCoupledBallEstimates
open ShenWork.IntervalResolverLaplacianBridge
open ShenWork.IntervalCoupledClassicalBallEstimates

noncomputable section

namespace ShenWork.IntervalCoupledC1ResolverBallBridge

/-- **C¹-ball ⇒ resolver-ball structural assembly.**

From the single-constant chemDiv flux Lipschitz `K·D` on the trajectory ball
(`hchem_KD`, the collapsed C¹-snapshot content), the source-sup data, and the
measurability inputs, assemble all four conjuncts of
`IntervalCoupledResolverBallEstimates p R u₀ T M K`.

The `hmap` conjunct (sup-ball self-map) is discharged from the committed
`intervalCoupledDuhamelOperator_bound_of_source_bound` with the source sup `C`,
the initial sup `H_init`, and the constant choice `H_init + C·T ≤ M`; `hchem` is
`hchem_KD`; `hint`/`hlift_int` are assembled by the committed
`intervalCoupledResolver_hchem_hint_hlift`. -/
theorem intervalCoupledResolverBallEstimates_of_chemKD
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    {T M K : ℝ}
    {H_init C Kc Lc : ℝ}
    (hH_init : 0 ≤ H_init) (hC : 0 ≤ C) (hKc : 0 ≤ Kc) (hLc : 0 ≤ Lc)
    (hMbound : H_init + C * T ≤ M)
    (hu₀ : ∀ y : intervalDomainPoint, |u₀ y| ≤ H_init)
    -- (hchem) committed single-constant chemDiv flux Lipschitz on the ball
    (hchem_KD : ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
      0 ≤ D →
      intervalTrajectoryBoundedOn T M u₁ →
      intervalTrajectoryBoundedOn T M u₂ →
      (∀ s y, 0 ≤ s → s ≤ T → |u₁ s y - u₂ s y| ≤ D) →
        ∀ (s : ℝ) (y : intervalDomainPoint), 0 ≤ s → s ≤ T →
          |intervalDomainChemotaxisDiv p (u₁ s) (R (u₁ s)) y -
            intervalDomainChemotaxisDiv p (u₂ s) (R (u₂ s)) y| ≤ K * D)
    -- source sup on the ball (gives the L∞ integrand bound and hmap's `C`)
    (hsource_sup : ∀ u : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u →
        ∀ s, 0 ≤ s → s ≤ T → ∀ y,
          |intervalDomainLift (intervalCoupledSource p (u s) (R (u s))) y| ≤ C)
    (hchem_sup : ∀ u : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u →
        ∀ s y, 0 ≤ s → s ≤ T →
          |intervalDomainChemotaxisDiv p (u s) (R (u s)) y| ≤ Kc)
    (hlog_sup : ∀ u : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u →
        ∀ s y, 0 ≤ s → s ≤ T →
          |intervalLogisticSource p (u s) y| ≤ Lc)
    (hsemigroup_meas : ∀ u : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u →
        ∀ (t : ℝ) (x : intervalDomainPoint), 0 ≤ t → t ≤ T →
          AEStronglyMeasurable
            (fun s => intervalSemigroupOperator 1 (t - s)
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1)
            (volume.restrict (Set.Icc 0 t)))
    (hlift_meas : ∀ u : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u →
        ∀ s, 0 ≤ s → s ≤ T →
          AEStronglyMeasurable
            (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
            (intervalMeasure 1)) :
    IntervalCoupledResolverBallEstimates p R u₀ T M K := by
  obtain ⟨_hchem, hint, hlift_int⟩ :=
    intervalCoupledResolver_hchem_hint_hlift p R hchem_KD hsemigroup_meas
      hlift_meas hKc hLc hchem_sup hlog_sup
  refine ⟨?_, hchem_KD, hint, hlift_int⟩
  -- (hmap): sup-ball self-map from the committed source-sup Duhamel bound.
  intro u hu t x ht0 htT
  have hbound :
      |intervalCoupledDuhamelOperator p R u₀ u t x| ≤ H_init + C * T :=
    intervalCoupledDuhamelOperator_bound_of_source_bound p R u₀ u
      hH_init hC hu₀
      (fun s hs0 hsT y => hsource_sup u hu s hs0 hsT y)
      ht0 htT x
      (hint u hu t x ht0 htT)
      (fun s hs0 hsT => hlift_int u hu s hs0 hsT)
  exact le_trans hbound hMbound

/-- The explicit single chemDiv-flux Lipschitz constant produced by the
two-constant K-form (`_uniformG`) collapsed by the gradient wiring
`D_g ≤ L_u · D`.  `K = K_u + G · L_u`, with `K_u` the explicit physical
constant of `intervalDomainChemotaxisDiv_classical_K_D_form_interior_uniformG`. -/
def chemKDConst (p : CM2Params) (M G_u G H L_V L_R L_H L_u : ℝ) : ℝ :=
  ((H + p.β * G ^ 2)
      + (G_u + 2 * p.β * M * G) * L_R
      + M * L_H
      + (G_u * G + M * H) * p.β * L_V
      + p.β * (M * G ^ 2) * (p.β + 1) * L_V)
    + G * L_u

theorem chemKDConst_nonneg {p : CM2Params} {M G_u G H L_V L_R L_H L_u : ℝ}
    (hMnn : 0 ≤ M) (hGunn : 0 ≤ G_u) (hGnn : 0 ≤ G) (hHnn : 0 ≤ H)
    (hLVnn : 0 ≤ L_V) (hLRnn : 0 ≤ L_R) (hLHnn : 0 ≤ L_H) (hLunn : 0 ≤ L_u) :
    0 ≤ chemKDConst p M G_u G H L_V L_R L_H L_u := by
  have hβnn : 0 ≤ p.β := p.hβ
  unfold chemKDConst; positivity

/-- **Interior single-constant chemDiv flux Lipschitz from the C¹ snapshot.**

Assembles the interior `K·D` flux Lipschitz at one time `τ` from the explicit
two-constant K-form (`_uniformG`) + the committed gradient wiring `hdu_diff`
(`|∂ₓ(lift u₁) − ∂ₓ(lift u₂)| ≤ L_u · D`, the `D_g ≤ L_u · D` collapse).
The constant is the uniform `chemKDConst`. -/
theorem chemKD_interior_of_C1Snapshot
    {p : CM2Params} {T M G_u : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsnap₁ : IntervalDomainClassicalC1Snapshot p T M G_u u₁ v₁)
    (hsnap₂ : IntervalDomainClassicalC1Snapshot p T M G_u u₂ v₂)
    (hMnn : 0 ≤ M) (hGunn : 0 ≤ G_u)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    {G H L_V L_R L_H L_u D : ℝ} (hGnn : 0 ≤ G) (hHnn : 0 ≤ H)
    (hG₁ : ∀ x ∈ Set.Icc (0 : ℝ) 1, |resolverGradReal p (u₁ τ) x| ≤ G)
    (hG₂ : ∀ x ∈ Set.Icc (0 : ℝ) 1, |resolverGradReal p (u₂ τ) x| ≤ G)
    (hH₁ : ∀ y : intervalDomainPoint, y.1 ∈ Set.Icc (0 : ℝ) 1 →
      |intervalNeumannResolverRLap p (u₁ τ) y| ≤ H)
    (hH₂ : ∀ y : intervalDomainPoint, y.1 ∈ Set.Icc (0 : ℝ) 1 →
      |intervalNeumannResolverRLap p (u₂ τ) y| ≤ H)
    (hDnn : 0 ≤ D) (hLVnn : 0 ≤ L_V) (hLRnn : 0 ≤ L_R) (hLHnn : 0 ≤ L_H)
    (hu_diff : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x| ≤ D)
    (hdu_diff : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (u₁ τ)) x
        - deriv (intervalDomainLift (u₂ τ)) x| ≤ L_u * D)
    (hv_diff : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |intervalDomainLift (v₁ τ) x - intervalDomainLift (v₂ τ) x| ≤ L_V * D)
    (hg_diff : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |resolverGradReal p (u₁ τ) x - resolverGradReal p (u₂ τ) x| ≤ L_R * D)
    (hH_diff : ∀ y : intervalDomainPoint, y.1 ∈ Set.Icc (0 : ℝ) 1 →
      |intervalNeumannResolverRLap p (u₁ τ) y
        - intervalNeumannResolverRLap p (u₂ τ) y| ≤ L_H * D)
    (hLunn : 0 ≤ L_u) :
    ∀ y : intervalDomainPoint, y.1 ∈ Set.Ioo (0 : ℝ) 1 →
      |intervalDomainChemotaxisDiv p (u₁ τ) (v₁ τ) y
        - intervalDomainChemotaxisDiv p (u₂ τ) (v₂ τ) y|
        ≤ chemKDConst p M G_u G H L_V L_R L_H L_u * D := by
  have hDg_nn : 0 ≤ L_u * D := mul_nonneg hLunn hDnn
  have hbase := intervalDomainChemotaxisDiv_classical_K_D_form_interior_uniformG
    hsnap₁ hsnap₂ hMnn hGunn hτ hGnn hHnn hG₁ hG₂ hH₁ hH₂
    hDnn hDg_nn hLVnn hLRnn hLHnn hu_diff hdu_diff hv_diff hg_diff hH_diff
  intro y hy
  refine (hbase y hy).trans ?_
  apply le_of_eq
  unfold chemKDConst
  ring

/-! ### Capstone: the C¹-snapshot ball ⇒ resolver-ball structural bridge -/

/-- **C¹-ball ⇒ resolver-ball structural assembly (existence half #2).**

From the honest C¹-snapshot regularity (`hSnap`: every trajectory in the
sup-ball is a C¹ classical solution with `v = R u` — the parabolic-Schauder
input, i.e. `hSol`), the per-time resolver legs (`hG_sup/hH_sup/hv_lip/hg_lip/
hH_lip`, the committed bounded-weight resolver estimates), the committed
gradient wiring `hdu_lip` (`D_g ≤ L_u · D`, from
`IntervalChemDivFluxHDgWiring`), and the regularity closure `hchem_closure`
(extending the interior `K·D` flux Lipschitz to closed time and all `y` — the
continuity-up-to-boundary content of the classical solution), the bridge builds
ALL FOUR conjuncts of `IntervalCoupledResolverBallEstimates p R u₀ T M K` with
`K = chemKDConst …`.

The single-constant chemotaxis Lipschitz (`hchem`) is ASSEMBLED interior-wise by
`chemKD_interior_of_C1Snapshot` (the explicit physical K-form `_uniformG`
collapsed by `hdu_lip`), then closed to all `(s, y)` by `hchem_closure`; `hint`,
`hlift_int`, `hmap` are assembled by `intervalCoupledResolverBallEstimates_of_chemKD`. -/
theorem intervalCoupledResolverBallEstimates_of_C1Snapshot
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    {T M G_u G H L_V L_R L_H L_u H_init C Kc Lc : ℝ}
    (hMnn : 0 ≤ M) (hGunn : 0 ≤ G_u) (hGnn : 0 ≤ G) (hHnn : 0 ≤ H)
    (hLVnn : 0 ≤ L_V) (hLRnn : 0 ≤ L_R) (hLHnn : 0 ≤ L_H) (hLunn : 0 ≤ L_u)
    (hH_init : 0 ≤ H_init) (hC : 0 ≤ C) (hKc : 0 ≤ Kc) (hLc : 0 ≤ Lc)
    (hMbound : H_init + C * T ≤ M)
    (hu₀ : ∀ y : intervalDomainPoint, |u₀ y| ≤ H_init)
    -- honest C¹-snapshot regularity (hSol): every ball trajectory is a C¹
    -- classical solution with v = R u.
    (hSnap : ∀ u : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u →
        IntervalDomainClassicalC1Snapshot p T M G_u u (fun s => R (u s)))
    -- committed bounded-weight resolver legs (per interior time, on the ball)
    (hG_sup : ∀ u : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u →
        ∀ τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) T →
          ∀ x ∈ Set.Icc (0 : ℝ) 1, |resolverGradReal p (u τ) x| ≤ G)
    (hH_sup : ∀ u : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u →
        ∀ τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) T →
          ∀ y : intervalDomainPoint, y.1 ∈ Set.Icc (0 : ℝ) 1 →
            |intervalNeumannResolverRLap p (u τ) y| ≤ H)
    (hv_lip : ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
      ∀ τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) T →
        ∀ x ∈ Set.Icc (0 : ℝ) 1,
          |intervalDomainLift (R (u₁ τ)) x - intervalDomainLift (R (u₂ τ)) x|
            ≤ L_V * D)
    (hg_lip : ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
      ∀ τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) T →
        ∀ x ∈ Set.Icc (0 : ℝ) 1,
          |resolverGradReal p (u₁ τ) x - resolverGradReal p (u₂ τ) x| ≤ L_R * D)
    (hH_lip : ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
      ∀ τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) T →
        ∀ y : intervalDomainPoint, y.1 ∈ Set.Icc (0 : ℝ) 1 →
          |intervalNeumannResolverRLap p (u₁ τ) y
            - intervalNeumannResolverRLap p (u₂ τ) y| ≤ L_H * D)
    -- committed gradient wiring (D_g ≤ L_u · D), per interior time
    (hdu_lip : ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
      ∀ τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) T →
        ∀ x ∈ Set.Icc (0 : ℝ) 1,
          |deriv (intervalDomainLift (u₁ τ)) x
            - deriv (intervalDomainLift (u₂ τ)) x| ≤ L_u * D)
    -- regularity closure: interior K·D flux Lipschitz extends to closed time
    -- and all y (continuity up to the closure — classical-solution content).
    (hchem_closure : ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
      0 ≤ D →
      intervalTrajectoryBoundedOn T M u₁ →
      intervalTrajectoryBoundedOn T M u₂ →
      (∀ τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) T → ∀ y : intervalDomainPoint,
        y.1 ∈ Set.Ioo (0 : ℝ) 1 →
          |intervalDomainChemotaxisDiv p (u₁ τ) (R (u₁ τ)) y -
            intervalDomainChemotaxisDiv p (u₂ τ) (R (u₂ τ)) y|
            ≤ chemKDConst p M G_u G H L_V L_R L_H L_u * D) →
        ∀ (s : ℝ) (y : intervalDomainPoint), 0 ≤ s → s ≤ T →
          |intervalDomainChemotaxisDiv p (u₁ s) (R (u₁ s)) y -
            intervalDomainChemotaxisDiv p (u₂ s) (R (u₂ s)) y|
            ≤ chemKDConst p M G_u G H L_V L_R L_H L_u * D)
    -- source sup + integrability inputs (for hmap, hint, hlift_int)
    (hsource_sup : ∀ u : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u →
        ∀ s, 0 ≤ s → s ≤ T → ∀ y,
          |intervalDomainLift (intervalCoupledSource p (u s) (R (u s))) y| ≤ C)
    (hchem_sup : ∀ u : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u →
        ∀ s y, 0 ≤ s → s ≤ T →
          |intervalDomainChemotaxisDiv p (u s) (R (u s)) y| ≤ Kc)
    (hlog_sup : ∀ u : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u →
        ∀ s y, 0 ≤ s → s ≤ T →
          |intervalLogisticSource p (u s) y| ≤ Lc)
    (hsemigroup_meas : ∀ u : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u →
        ∀ (t : ℝ) (x : intervalDomainPoint), 0 ≤ t → t ≤ T →
          AEStronglyMeasurable
            (fun s => intervalSemigroupOperator 1 (t - s)
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1)
            (volume.restrict (Set.Icc 0 t)))
    (hlift_meas : ∀ u : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u →
        ∀ s, 0 ≤ s → s ≤ T →
          AEStronglyMeasurable
            (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
            (intervalMeasure 1)) :
    IntervalCoupledResolverBallEstimates p R u₀ T M
      (chemKDConst p M G_u G H L_V L_R L_H L_u) := by
  -- Assemble the single-constant chemDiv flux Lipschitz on the ball.
  have hchem_KD : ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
      0 ≤ D →
      intervalTrajectoryBoundedOn T M u₁ →
      intervalTrajectoryBoundedOn T M u₂ →
      (∀ s y, 0 ≤ s → s ≤ T → |u₁ s y - u₂ s y| ≤ D) →
        ∀ (s : ℝ) (y : intervalDomainPoint), 0 ≤ s → s ≤ T →
          |intervalDomainChemotaxisDiv p (u₁ s) (R (u₁ s)) y -
            intervalDomainChemotaxisDiv p (u₂ s) (R (u₂ s)) y|
            ≤ chemKDConst p M G_u G H L_V L_R L_H L_u * D := by
    intro u₁ u₂ D hDnn hb₁ hb₂ hdiff
    -- interior bound at every interior time τ, via the explicit K-form collapse.
    have hint_bound : ∀ τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) T →
        ∀ y : intervalDomainPoint, y.1 ∈ Set.Ioo (0 : ℝ) 1 →
          |intervalDomainChemotaxisDiv p (u₁ τ) (R (u₁ τ)) y -
            intervalDomainChemotaxisDiv p (u₂ τ) (R (u₂ τ)) y|
            ≤ chemKDConst p M G_u G H L_V L_R L_H L_u * D := by
      intro τ hτ
      -- lift point-diff ⇒ lift diff on [0,1].
      have hu_diff : ∀ x ∈ Set.Icc (0 : ℝ) 1,
          |intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x| ≤ D := by
        intro x hx
        have := hdiff τ ⟨x, hx⟩ hτ.1.le hτ.2.le
        simpa [intervalDomainLift, hx] using this
      exact chemKD_interior_of_C1Snapshot
        (hSnap u₁ hb₁) (hSnap u₂ hb₂) hMnn hGunn hτ hGnn hHnn
        (hG_sup u₁ hb₁ τ hτ) (hG_sup u₂ hb₂ τ hτ)
        (hH_sup u₁ hb₁ τ hτ) (hH_sup u₂ hb₂ τ hτ)
        hDnn hLVnn hLRnn hLHnn hu_diff
        (hdu_lip u₁ u₂ D τ hτ) (hv_lip u₁ u₂ D τ hτ)
        (hg_lip u₁ u₂ D τ hτ) (hH_lip u₁ u₂ D τ hτ) hLunn
    exact hchem_closure u₁ u₂ D hDnn hb₁ hb₂ hint_bound
  exact intervalCoupledResolverBallEstimates_of_chemKD p R u₀
    hH_init hC hKc hLc hMbound hu₀ hchem_KD
    hsource_sup hchem_sup hlog_sup hsemigroup_meas hlift_meas

end ShenWork.IntervalCoupledC1ResolverBallBridge
