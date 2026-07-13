import ShenWork.Paper1.WaveNegativePinnedOrbit
import ShenWork.Paper1.WaveControlledConstruction

open Filter Set Topology

noncomputable section

namespace ShenWork.Paper1

/-- Common spatial modulus of the kinked initial barrier and every smooth
successor in the genuine negative-branch Rothe orbit. -/
def paperNegativePinnedOrbitModulus
    {p : CMParams} {c D : ℝ}
    (s : Paper1NegativeLocalStepScalarData p c D) : ℝ :=
  max 1 s.Λ

theorem paperNegativePinnedOrbitModulus_nonneg
    {p : CMParams} {c D : ℝ}
    (s : Paper1NegativeLocalStepScalarData p c D) :
    0 ≤ paperNegativePinnedOrbitModulus s :=
  le_trans zero_le_one (le_max_left 1 s.Λ)

theorem one_le_paperNegativePinnedOrbitModulus
    {p : CMParams} {c D : ℝ}
    (s : Paper1NegativeLocalStepScalarData p c D) :
    1 ≤ paperNegativePinnedOrbitModulus s :=
  le_max_left 1 s.Λ

theorem lambda_le_paperNegativePinnedOrbitModulus
    {p : CMParams} {c D : ℝ}
    (s : Paper1NegativeLocalStepScalarData p c D) :
    s.Λ ≤ paperNegativePinnedOrbitModulus s :=
  le_max_right 1 s.Λ

/-- Totalize the genuine lower-pinned orbit by the upper barrier outside its
Schauder domain.  Every theorem below rewrites this definition with an actual
domain witness before using analytic data. -/
noncomputable def paperNegativePinnedRotheSeqFromTrap
    {p : CMParams} {c D : ℝ}
    (hcond : PaperLemma42ExactConditions
      p c (kappa c) (negativeBranchTailCap p c) 1)
    (hD : paperDMin p.χ 1 (kappa c) (negativeBranchTailCap p c)
      p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (s : Paper1NegativeLocalStepScalarData p c D) :
    (ℝ → ℝ) → ℕ → ℝ → ℝ :=
  fun u => by
    classical
    exact if hu : InLowerPinnedMonotoneTrap (kappa c) 1
        (lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D) u then
      paperNegativePinnedRotheSeq hcond hD hD1 s u hu
    else fun _ => upperBarrier (kappa c) 1

@[simp] theorem paperNegativePinnedRotheSeqFromTrap_eq
    {p : CMParams} {c D : ℝ}
    (hcond : PaperLemma42ExactConditions
      p c (kappa c) (negativeBranchTailCap p c) 1)
    (hD : paperDMin p.χ 1 (kappa c) (negativeBranchTailCap p c)
      p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (s : Paper1NegativeLocalStepScalarData p c D)
    {u : ℝ → ℝ}
    (hu : InLowerPinnedMonotoneTrap (kappa c) 1
      (lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D) u) :
    paperNegativePinnedRotheSeqFromTrap hcond hD hD1 s u =
      paperNegativePinnedRotheSeq hcond hD hD1 s u hu := by
  simp [paperNegativePinnedRotheSeqFromTrap, hu]

/-- The selected local Green source retained at every successor is exactly the
analytic payload required by the moving-index whole-line closed graph. -/
noncomputable def paperNegativePinnedRotheSeq_stepAnalytic
    {p : CMParams} {c D : ℝ}
    (hcond : PaperLemma42ExactConditions
      p c (kappa c) (negativeBranchTailCap p c) 1)
    (hD : paperDMin p.χ 1 (kappa c) (negativeBranchTailCap p c)
      p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (s : Paper1NegativeLocalStepScalarData p c D)
    (u : ℝ → ℝ)
    (hu : InLowerPinnedMonotoneTrap (kappa c) 1
      (lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D) u)
    (n : ℕ) :
    PaperStepAnalytic p c s.lam 1 (kappa c) s.Λ u
      (paperNegativePinnedRotheSeq hcond hD hD1 s u hu n)
      (paperNegativePinnedRotheSeq hcond hD hD1 s u hu (n + 1)) := by
  cases n with
  | zero =>
      exact paperStepAnalytic_of_core s.hlam
        (paperNegativePinnedStepState hcond hD hD1 s u hu 0).data.fixed.analyticCore
  | succ n =>
      exact paperStepAnalytic_of_core s.hlam
        (paperNegativePinnedStepState hcond hD hD1 s u hu (n + 1)).data.fixed.analyticCore

/-- Every iterate of the genuine orbit stays above the raw lower barrier. -/
theorem paperNegativePinnedRotheSeq_lower
    {p : CMParams} {c D : ℝ}
    (hcond : PaperLemma42ExactConditions
      p c (kappa c) (negativeBranchTailCap p c) 1)
    (hD : paperDMin p.χ 1 (kappa c) (negativeBranchTailCap p c)
      p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (s : Paper1NegativeLocalStepScalarData p c D)
    (u : ℝ → ℝ)
    (hu : InLowerPinnedMonotoneTrap (kappa c) 1
      (lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D) u) :
    ∀ n x, lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D x ≤
      paperNegativePinnedRotheSeq hcond hD hD1 s u hu n x := by
  intro n x
  cases n with
  | zero =>
      exact (hu.lower x).trans (hu.bare.le_upperBarrier x)
  | succ n =>
      exact (paperNegativePinnedStepState hcond hD hD1 s u hu n).pinned.lower x

/-- All compactness data of the genuine negative orbit, with amplitude one
and its Green derivative modulus kept independent. -/
theorem paperNegativePinnedRotheSeq_orbitData
    {p : CMParams} {c D : ℝ}
    (hcond : PaperLemma42ExactConditions
      p c (kappa c) (negativeBranchTailCap p c) 1)
    (hD : paperDMin p.χ 1 (kappa c) (negativeBranchTailCap p c)
      p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (s : Paper1NegativeLocalStepScalarData p c D)
    (u : ℝ → ℝ)
    (hu : InLowerPinnedMonotoneTrap (kappa c) 1
      (lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D) u) :
    PaperRotheOrbitDataWithModulus p c s.lam 1 (kappa c)
      (paperNegativePinnedOrbitModulus s)
      (paperNegativePinnedRotheSeq hcond hD hD1 s u hu) := by
  let z := paperNegativePinnedRotheSeq hcond hD hD1 s u hu
  have hstep : ∀ n, PaperRotheStepFacts p c s.lam 1 (kappa c) s.Λ u
      (z n) (z (n + 1)) := by
    intro n
    exact paperNegativePinnedRotheSeq_stepFacts hcond hD hD1 s u hu n
  have hantiK : ∀ x, Antitone (fun n => z n x) := by
    intro x
    exact antitone_nat_of_succ_le (fun n => (hstep n).le_old x)
  have hbdd : ∀ x, BddBelow (Set.range (fun n => z n x)) := by
    intro x
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    cases n with
    | zero => exact upperBarrier_nonneg (κ := kappa c) zero_le_one x
    | succ n => exact (hstep n).nonneg x
  have hLip : ∀ n x y,
      |z n x - z n y| ≤ paperNegativePinnedOrbitModulus s * |x - y| := by
    intro n x y
    cases n with
    | zero =>
        exact (hcond.upperBarrier_barLip x y).trans
          (mul_le_mul_of_nonneg_right
            (one_le_paperNegativePinnedOrbitModulus s) (abs_nonneg _))
    | succ n =>
        have hLipschitz : LipschitzWith (Real.toNNReal s.Λ) (z (n + 1)) :=
          crossImplicitStep_lipschitz s.hΛ0 (hstep n).diff (hstep n).deriv_le
        have hxy := hLipschitz.dist_le_mul x y
        rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ s.hΛ0] at hxy
        exact hxy.trans (mul_le_mul_of_nonneg_right
          (lambda_le_paperNegativePinnedOrbitModulus s) (abs_nonneg _))
  have hlimitLip : ∀ x y,
      |rotheLimit z x - rotheLimit z y| ≤
        paperNegativePinnedOrbitModulus s * |x - y| := by
    intro x y
    have hx : Tendsto (fun n => z n x) atTop (nhds (rotheLimit z x)) :=
      rotheLimit_tendsto hantiK hbdd x
    have hy : Tendsto (fun n => z n y) atTop (nhds (rotheLimit z y)) :=
      rotheLimit_tendsto hantiK hbdd y
    refine le_of_tendsto ((hx.sub hy).abs) ?_
    exact Eventually.of_forall (fun n => hLip n x y)
  refine
    { iterate_cont := ?_
      anti_k := hantiK
      anti_x := ?_
      nonneg := ?_
      le_M := ?_
      le_upperBarrier := ?_
      bddBelow := hbdd
      equiLip := hLip
      limitLip := hlimitLip }
  · intro n
    cases n with
    | zero => exact upperBarrier_continuous (kappa c) 1
    | succ n => exact (hstep n).cont
  · intro n
    cases n with
    | zero => exact upperBarrier_antitone hcond.hκ0.le
    | succ n => exact (hstep n).anti
  · intro n x
    cases n with
    | zero => exact upperBarrier_nonneg (κ := kappa c) zero_le_one x
    | succ n => exact (hstep n).nonneg x
  · intro n x
    cases n with
    | zero => exact upperBarrier_le_M (kappa c) 1 x
    | succ n => exact (hstep n).le_barrier x |>.trans (upperBarrier_le_M _ _ _)
  · intro n x
    cases n with
    | zero => exact le_rfl
    | succ n => exact (hstep n).le_barrier x

section AxiomAudit

#print axioms paperNegativePinnedRotheSeq_stepAnalytic
#print axioms paperNegativePinnedRotheSeq_lower
#print axioms paperNegativePinnedRotheSeq_orbitData

end AxiomAudit

end ShenWork.Paper1
