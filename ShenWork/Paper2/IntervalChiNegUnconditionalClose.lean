/-
# Unconditional χ-negative resolver-C² close: the source tail is DERIVED

`ShenWork.Paper2.ChiNegFloorClosure.chiNeg_close_C7_of_joint_positive` closes the
χ₀ < 0 resolver-C² branch (`ResolverHasSpectralAgreementC2Coeff`) but TAKES the
eigen-cube source tail (`SourceEigenCubeTailFields` for every restart `mkL σ`) as a
hypothesis.  This file removes that hypothesis: the per-restart source tail is
**DERIVED** from the source's honest `C⁶`-Neumann spatial regularity by composing

  * `NeumannTowerOfC6.neumannTower_three_of_contDiff_six`  (piece 3:
      `ContDiff ℝ 6 (fSrc)` + odd-deriv Neumann vanishing  ⇒  depth-3 `NeumannTower`),
  * `EigenCubeTailFromTower.SourceEigenCubeTailFields_of_neumannTower`  (piece 2:
      towers for `L.aC`/`L.srcC.adot` + top/zero bounds  ⇒  `SourceEigenCubeTailFields`).

The IBP coefficient decay `IntervalIBPCoeffExtraction.cosineCoeffs_decay` (piece 1) is
internal to piece 2.

The remaining honest inputs to the top theorem are exactly the genuine forward data:
the committed base regularity (`baseC2`), joint continuity + positivity of the profile
(`hjoint`/`hpos`), the chemotaxis-divergence atom (`hchem`), the resolver
summability (`hsrcCube`), the Duhamel C7 data, the spectral-agreement/restart data
(`H`/`mkL`), and the source spatial regularity supplied per restart: the smooth
representatives `fSrc σ`/`fAdot σ` with `ContDiff ℝ 6`, the cosine-coefficient
identification `L.aC = cosineCoeffs (fSrc σ)` (the source IS a Neumann-cosine-series
object), the odd-derivative Neumann vanishing (its odd derivatives are sine series,
vanishing at the no-flux endpoints), and the top-mode / zero-mode coefficient bounds.

`SourceEigenCubeTailFields` is **NOT** a hypothesis of the top theorem — it is built
inside.  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalChiNegFloorClosure
import ShenWork.Paper2.IntervalEigenCubeTailFromTower
import ShenWork.Paper2.IntervalNeumannTowerOfC6

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.Paper2.ChiNegConcreteConnectors
open ShenWork.Paper2.ParabolicGainInduction
open ShenWork.Paper2.ChiNegSourceTail
open ShenWork.Paper2.ChiNegFloorClosure
open ShenWork.Paper2.EigenCubeTailFromTower
open ShenWork.Paper2.NeumannTowerOfC6
open ShenWork.Paper2.PicardLimitK1 (LocalRestart)
open ShenWork.IntervalIBPCoeffExtraction (NeumannTower rawCoeff)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

noncomputable section

namespace ShenWork.Paper2.ChiNegUnconditionalClose

open Set Filter Topology

/-- Witness-exposing depth-`3` Neumann tower: from `ContDiff ℝ 6 f` plus the odd-deriv
Neumann vanishing of `gTower f`, the **explicit** tower `gTower f` is a `NeumannTower`.
(Piece 3 packs the witness existentially; this exposes it as `gTower f` so the
top-coefficient hypothesis can be stated on `gTower f 3`.) -/
theorem neumannTower_gTower_three_of_contDiff_six
    {f : ℝ → ℝ} (hf : ContDiff ℝ (6 : ℕ) f)
    (hN0 : ∀ i, i < 3 → deriv (gTower f i) 0 = 0)
    (hN1 : ∀ i, i < 3 → deriv (gTower f i) 1 = 0) :
    NeumannTower (gTower f) 3 := by
  have hcd : ∀ i, i < 3 → ContDiff ℝ 2 (gTower f i) := by
    intro i hi
    refine contDiff_gTower (hf.of_le ?_)
    have : (2 + 2 * i : ℕ) ≤ 6 := by omega
    exact_mod_cast this
  have hcont : ∀ i, i < 3 → Continuous (deriv (gTower f i)) := by
    intro i hi
    refine continuous_deriv_gTower (hf.of_le ?_)
    have : (2 * i + 1 : ℕ) ≤ 6 := by omega
    exact_mod_cast this
  refine
    { step := fun i _ => gTower_step f i
      contDiff := fun i hi => (hcd i hi).contDiffOn
      tend0 := fun i hi => ?_
      tend1 := fun i hi => ?_
      bc0 := hN0
      bc1 := hN1 }
  · have hc := (hcont i hi).continuousAt (x := (0 : ℝ))
    have hT : Tendsto (deriv (gTower f i)) (nhds 0) (nhds (deriv (gTower f i) 0)) := hc
    rw [hN0 i hi] at hT
    exact hT.mono_left nhdsWithin_le_nhds
  · have hc := (hcont i hi).continuousAt (x := (1 : ℝ))
    have hT : Tendsto (deriv (gTower f i)) (nhds 1) (nhds (deriv (gTower f i) 1)) := hc
    rw [hN1 i hi] at hT
    exact hT.mono_left nhdsWithin_le_nhds

/-- **Derived eigen-cube source tail from honest `C⁶`-Neumann source regularity.**

For a single restart `L = mkL σ …`, build `SourceEigenCubeTailFields` purely from the
source's spatial smoothness: smooth representatives `fSrc`/`fAdot` of `L.aC`/`L.srcC.adot`
that are `ContDiff ℝ 6`, with their odd derivatives vanishing at the endpoints
(the cosine-series / no-flux structure), and the top-mode / zero-mode coefficient bounds.

Pieces 3 → 2 are composed here; `SourceEigenCubeTailFields` is the conclusion, not an
input. -/
theorem sourceEigenCubeTailFields_of_sourceRegularity
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T σ : ℝ}
    (L : LocalRestart p u T σ)
    {fSrc fAdot : ℝ → ℝ → ℝ} {C0 C0dot M Mdot : ℝ}
    (hC0 : 0 ≤ C0) (hC0dot : 0 ≤ C0dot)
    -- source coefficient is the normalized cosine coefficient of the smooth rep `fSrc s`:
    (hSrcCoeff : ∀ s, 0 ≤ s → ∀ n, L.aC s n = cosineCoeffs (fSrc s) n)
    (hSrcCD6 : ∀ s, 0 ≤ s → ContDiff ℝ (6 : ℕ) (fSrc s))
    (hSrcN0 : ∀ s, 0 ≤ s → ∀ i, i < 3 → deriv (gTower (fSrc s) i) 0 = 0)
    (hSrcN1 : ∀ s, 0 ≤ s → ∀ i, i < 3 → deriv (gTower (fSrc s) i) 1 = 0)
    (hSrcTop : ∀ s, 0 ≤ s → ∀ n, 1 ≤ n → |rawCoeff n (gTower (fSrc s) 3)| ≤ M)
    -- time-derivative coefficient is the normalized cosine coefficient of `fAdot s`:
    (hAdotCoeff : ∀ s, 0 ≤ s → ∀ n, L.srcC.adot s n = cosineCoeffs (fAdot s) n)
    (hAdotCD6 : ∀ s, 0 ≤ s → ContDiff ℝ (6 : ℕ) (fAdot s))
    (hAdotN0 : ∀ s, 0 ≤ s → ∀ i, i < 3 → deriv (gTower (fAdot s) i) 0 = 0)
    (hAdotN1 : ∀ s, 0 ≤ s → ∀ i, i < 3 → deriv (gTower (fAdot s) i) 1 = 0)
    (hAdotTop : ∀ s, 0 ≤ s → ∀ n, 1 ≤ n → |rawCoeff n (gTower (fAdot s) 3)| ≤ Mdot)
    -- zero-mode bounds (the tower is silent on `n = 0`):
    (hSrcZero : ∀ s, 0 ≤ s → |L.aC s 0| ≤ C0)
    (hAdotZero : ∀ s, 0 ≤ s → |L.srcC.adot s 0| ≤ C0dot) :
    SourceEigenCubeTailFields L C0 (2 * M) C0dot (2 * Mdot) := by
  -- Piece 3: depth-3 Neumann towers for the source and its time derivative.
  -- We use `gTower (fSrc s)` / `gTower (fAdot s)` as the explicit towers; piece 3
  -- supplies that they form genuine `NeumannTower`s (with base `= fSrc s` / `fAdot s`).
  have hSrcTower : ∀ s, 0 ≤ s → NeumannTower (gTower (fSrc s)) 3 := fun s hs =>
    neumannTower_gTower_three_of_contDiff_six (hSrcCD6 s hs) (hSrcN0 s hs) (hSrcN1 s hs)
  have hAdotTower : ∀ s, 0 ≤ s → NeumannTower (gTower (fAdot s)) 3 := fun s hs =>
    neumannTower_gTower_three_of_contDiff_six (hAdotCD6 s hs) (hAdotN0 s hs) (hAdotN1 s hs)
  -- Piece 2: assemble `SourceEigenCubeTailFields` from the towers + bounds.
  exact SourceEigenCubeTailFields_of_neumannTower L hC0 hC0dot
    hSrcCoeff (fun s => gTower_zero (fSrc s)) hSrcTower hSrcTop
    hAdotCoeff (fun s => gTower_zero (fAdot s)) hAdotTower hAdotTop
    hSrcZero hAdotZero

/-- **Unconditional χ-negative resolver-C² close.**

`ResolverHasSpectralAgreementC2Coeff T utraj` from honest forward inputs only:
base regularity, joint continuity + positivity, the chem-div atom, resolver
summability, the Duhamel C7 data, the spectral-agreement / restart data, and the
source's per-restart `C⁶`-Neumann spatial regularity (smooth representatives,
cosine-coeff identification, odd-deriv Neumann vanishing, top/zero coeff bounds).

`SourceEigenCubeTailFields` is **DERIVED** (via
`sourceEigenCubeTailFields_of_sourceRegularity`, pieces 3 → 2), **not assumed**. -/
theorem chiNeg_resolverC2Coeff_unconditional
    {p : CM2Params} {T lo hi t : ℝ}
    {utraj : ℝ → intervalDomainPoint → ℝ}
    -- committed base regularity:
    (baseC2 : SpatialSlice 2 ((concreteU (utraj t)) 2))
    -- joint continuity + positivity of the profile on the time window:
    (hlohi : lo ≤ hi)
    (hjoint : ContinuousOn
      (Function.uncurry (fun s x => intervalDomainLift (utraj s) x))
      (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1))
    (hpos : ∀ s ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (utraj s) x)
    (ht : t ∈ Set.Icc lo hi)
    -- chemotaxis-divergence atom:
    (hchem : ∀ k, 2 ≤ k → k < 7 →
      CoupledSlice k ((concreteU (utraj t)) k)
        ((concreteV p (utraj t)) k) →
        SpatialSlice (k - 1)
          (ShenWork.IntervalDomain.intervalDomainChemotaxisDiv p
            ((concreteU (utraj t)) k)
            ((concreteV p (utraj t)) k)))
    -- resolver summability:
    (hsrcCube : Summable fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            |(ShenWork.PDE.intervalNeumannResolverSourceCoeff
              p (utraj t) n).re|)))
    -- Duhamel C7 data:
    (data : ConcreteDuhamelDataC7Fields p (utraj t))
    -- spectral-agreement / restart data:
    (H : ShenWork.IntervalResolverTimeRegularity.ResolverHasSpectralAgreement
      T utraj)
    (mkL : ∀ σ, 0 < σ → σ < T → LocalRestart p utraj T σ)
    -- source spatial regularity, per restart (the honest `C⁶`-Neumann source data):
    (fSrc fAdot : ℝ → ℝ → ℝ → ℝ)
    (C0 C0dot M Mdot : ℝ → ℝ)
    (hC0 : ∀ σ, 0 ≤ C0 σ) (hC0dot : ∀ σ, 0 ≤ C0dot σ)
    (hSrcCoeff : ∀ σ (hσ0 : 0 < σ) (hσT : σ < T),
      ∀ s, 0 ≤ s → ∀ n, (mkL σ hσ0 hσT).aC s n = cosineCoeffs (fSrc σ s) n)
    (hSrcCD6 : ∀ σ, ∀ s, 0 ≤ s → ContDiff ℝ (6 : ℕ) (fSrc σ s))
    (hSrcN0 : ∀ σ, ∀ s, 0 ≤ s → ∀ i, i < 3 → deriv (gTower (fSrc σ s) i) 0 = 0)
    (hSrcN1 : ∀ σ, ∀ s, 0 ≤ s → ∀ i, i < 3 → deriv (gTower (fSrc σ s) i) 1 = 0)
    (hSrcTop : ∀ σ, ∀ s, 0 ≤ s → ∀ n, 1 ≤ n →
      |rawCoeff n (gTower (fSrc σ s) 3)| ≤ M σ)
    (hAdotCoeff : ∀ σ (hσ0 : 0 < σ) (hσT : σ < T),
      ∀ s, 0 ≤ s → ∀ n, (mkL σ hσ0 hσT).srcC.adot s n = cosineCoeffs (fAdot σ s) n)
    (hAdotCD6 : ∀ σ, ∀ s, 0 ≤ s → ContDiff ℝ (6 : ℕ) (fAdot σ s))
    (hAdotN0 : ∀ σ, ∀ s, 0 ≤ s → ∀ i, i < 3 → deriv (gTower (fAdot σ s) i) 0 = 0)
    (hAdotN1 : ∀ σ, ∀ s, 0 ≤ s → ∀ i, i < 3 → deriv (gTower (fAdot σ s) i) 1 = 0)
    (hAdotTop : ∀ σ, ∀ s, 0 ≤ s → ∀ n, 1 ≤ n →
      |rawCoeff n (gTower (fAdot σ s) 3)| ≤ Mdot σ)
    (hSrcZero : ∀ σ (hσ0 : 0 < σ) (hσT : σ < T),
      ∀ s, 0 ≤ s → |(mkL σ hσ0 hσT).aC s 0| ≤ C0 σ)
    (hAdotZero : ∀ σ (hσ0 : 0 < σ) (hσT : σ < T),
      ∀ s, 0 ≤ s → |(mkL σ hσ0 hσT).srcC.adot s 0| ≤ C0dot σ) :
    ShenWork.IntervalResolverJointC2.ResolverHasSpectralAgreementC2Coeff
      T utraj := by
  -- DERIVE the per-restart eigen-cube source tail (pieces 3 → 2).
  have tail : ∀ σ (hσ0 : 0 < σ) (hσT : σ < T),
      SourceEigenCubeTailFields
        (mkL σ hσ0 hσT) (C0 σ) (2 * M σ) (C0dot σ) (2 * Mdot σ) := by
    intro σ hσ0 hσT
    exact sourceEigenCubeTailFields_of_sourceRegularity (mkL σ hσ0 hσT)
      (hC0 σ) (hC0dot σ)
      (hSrcCoeff σ hσ0 hσT) (hSrcCD6 σ) (hSrcN0 σ) (hSrcN1 σ) (hSrcTop σ)
      (hAdotCoeff σ hσ0 hσT) (hAdotCD6 σ) (hAdotN0 σ) (hAdotN1 σ) (hAdotTop σ)
      (hSrcZero σ hσ0 hσT) (hAdotZero σ hσ0 hσT)
  -- nonnegativity of the packaged `max`-constants consumed by the close.
  have hC6 : ∀ σ, 0 ≤ max (C0 σ) (64 * (2 * M σ)) := fun σ =>
    le_max_of_le_left (hC0 σ)
  have hCdot6 : ∀ σ, 0 ≤ max (C0dot σ) (64 * (2 * Mdot σ)) := fun σ =>
    le_max_of_le_left (hC0dot σ)
  -- Feed the DERIVED tail into the committed close.
  exact chiNeg_close_C7_of_joint_positive
    baseC2 hlohi hjoint hpos ht hchem hsrcCube data H mkL
    (fun σ => C0 σ) (fun σ => 2 * M σ) (fun σ => C0dot σ) (fun σ => 2 * Mdot σ)
    hC6 hCdot6 tail

#print axioms sourceEigenCubeTailFields_of_sourceRegularity
#print axioms chiNeg_resolverC2Coeff_unconditional

end ShenWork.Paper2.ChiNegUnconditionalClose
