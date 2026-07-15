import ShenWork.Paper1.WholeLineWeightedRegularityCap

open Filter MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Cap-weighted nonlinear source bounds

This file supplies the nonlinear estimates used by the cap-weighted Henry
argument.  The weight is `sqrt (capWeight eta R)`.  Its two-point ratio is
controlled by `exp (eta * |x-y|)` uniformly in the cap radius `R`; hence all
constants below are independent of `R`.
-/

/-- Cap-conjugated nonlinear flux difference. -/
def capWeightedFluxDifference
    (p : CMParams) (eta R : ℝ) (u₂ u₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  capWeightSqrt eta R x *
    (u₂ x ^ p.m * deriv (frozenElliptic p u₂) x -
      u₁ x ^ p.m * deriv (frozenElliptic p u₁) x)

/-- The cap-flux constant.  It is independent of the cap radius `R`. -/
def capWeightedFluxSquareConstant
    (p : CMParams) (M eta : ℝ) : ℝ :=
  2 * (M ^ p.m * ((1 / (1 - eta)) *
      (p.γ * M ^ (p.γ - 1)))) ^ 2 +
    2 * ((p.m * M ^ (p.m - 1)) * M ^ p.γ) ^ 2

/-- Cap-conjugated chemotaxis operator difference, including `-chi`. -/
def capWeightedChemotaxisOperatorDifference
    (p : CMParams) (eta R : ℝ) (u₂ u₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (-p.χ) * capWeightedFluxDifference p eta R u₂ u₁ x

def capWeightedChemotaxisOperatorSquareConstant
    (p : CMParams) (M eta : ℝ) : ℝ :=
  p.χ ^ 2 * capWeightedFluxSquareConstant p M eta

/-- Cap-conjugated logistic reaction difference. -/
def capWeightedReactionDifference
    (p : CMParams) (eta R : ℝ) (u₂ u₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  capWeightSqrt eta R x *
    (reactionFun p.α (u₂ x) - reactionFun p.α (u₁ x))

private theorem capWeighted_raw_difference_sq_integrable
    {eta R : ℝ} {u₂ u₁ : ℝ → ℝ}
    (hclose : Integrable (fun x =>
      capWeight eta R x * |u₂ x - u₁ x| ^ 2)) :
    Integrable (fun x =>
      (capWeightSqrt eta R x * (u₂ x - u₁ x)) ^ 2) := by
  refine hclose.congr (Eventually.of_forall fun x => ?_)
  exact (capWeightSqrt_mul_sq_eq eta R x (u₂ x - u₁ x)).symm

private theorem capWeighted_raw_difference_sq_integral_eq
    {eta R : ℝ} {u₂ u₁ : ℝ → ℝ} :
    (∫ x : ℝ, (capWeightSqrt eta R x * (u₂ x - u₁ x)) ^ 2) =
      ∫ x : ℝ, capWeight eta R x * |u₂ x - u₁ x| ^ 2 := by
  apply integral_congr_ae
  exact Eventually.of_forall fun x =>
    capWeightSqrt_mul_sq_eq eta R x (u₂ x - u₁ x)

/-- The nonlinear population-flux difference is cap-weighted `L²` bounded
by the population difference.  The estimate is uniform in `R`. -/
theorem capWeighted_flux_difference_l2_bounded
    (p : CMParams) {M eta R : ℝ}
    (hM : 0 ≤ M) (heta_nonneg : 0 ≤ eta) (heta_one : eta < 1)
    {u₂ u₁ : ℝ → ℝ}
    (hu₂ : IsCUnifBdd u₂) (hu₁ : IsCUnifBdd u₁)
    (hu₂_mem : ∀ x, u₂ x ∈ Set.Icc (0 : ℝ) M)
    (hu₁_mem : ∀ x, u₁ x ∈ Set.Icc (0 : ℝ) M)
    (hclose : Integrable (fun x =>
      capWeight eta R x * |u₂ x - u₁ x| ^ 2)) :
    Integrable (fun x =>
        capWeightedFluxDifference p eta R u₂ u₁ x ^ 2) ∧
      (∫ x : ℝ,
          capWeightedFluxDifference p eta R u₂ u₁ x ^ 2) ≤
        capWeightedFluxSquareConstant p M eta *
          ∫ x : ℝ, capWeight eta R x * |u₂ x - u₁ x| ^ 2 := by
  let A : ℝ := M ^ p.m
  let B : ℝ := (p.m * M ^ (p.m - 1)) * M ^ p.γ
  let K : ℝ := (1 / (1 - eta)) * (p.γ * M ^ (p.γ - 1))
  let dV : ℝ → ℝ := fun x =>
    capWeightSqrt eta R x *
      (deriv (frozenElliptic p u₂) x -
        deriv (frozenElliptic p u₁) x)
  let q : ℝ → ℝ := fun x =>
    capWeightSqrt eta R x * (u₂ x - u₁ x)
  have hgrad := capWeight_frozenElliptic_gradient_difference_l2_bounded
    p hM heta_nonneg heta_one hu₁ hu₂ hu₁_mem hu₂_mem hclose
  have hq : Integrable (fun x => q x ^ 2) := by
    simpa only [q] using capWeighted_raw_difference_sq_integrable hclose
  have hA0 : 0 ≤ A := Real.rpow_nonneg hM _
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg (le_trans zero_le_one p.hm)
        (Real.rpow_nonneg hM _))
      (Real.rpow_nonneg hM _)
  have hpoint : ∀ x,
      |capWeightedFluxDifference p eta R u₂ u₁ x| ≤
        A * |dV x| + B * |q x| := by
    intro x
    have hu₂m : u₂ x ^ p.m ≤ M ^ p.m :=
      Real.rpow_le_rpow (hu₂_mem x).1 (hu₂_mem x).2
        (le_trans zero_le_one p.hm)
    have hpow := abs_rpow_sub_rpow_le_of_mem_Icc
      p.hm hM (hu₂_mem x) (hu₁_mem x)
    have hV := frozenElliptic_deriv_abs_le_rpow_of_Icc
      p hM hu₁ hu₁_mem x
    have hweight0 : 0 ≤ capWeightSqrt eta R x :=
      (capWeightSqrt_pos eta R x).le
    have hsplit :
        u₂ x ^ p.m * deriv (frozenElliptic p u₂) x -
            u₁ x ^ p.m * deriv (frozenElliptic p u₁) x =
          u₂ x ^ p.m *
              (deriv (frozenElliptic p u₂) x -
                deriv (frozenElliptic p u₁) x) +
            (u₂ x ^ p.m - u₁ x ^ p.m) *
              deriv (frozenElliptic p u₁) x := by ring
    rw [capWeightedFluxDifference, hsplit, abs_mul,
      abs_of_nonneg hweight0]
    calc
      capWeightSqrt eta R x *
          |u₂ x ^ p.m *
              (deriv (frozenElliptic p u₂) x -
                deriv (frozenElliptic p u₁) x) +
            (u₂ x ^ p.m - u₁ x ^ p.m) *
              deriv (frozenElliptic p u₁) x| ≤
          capWeightSqrt eta R x *
            (|u₂ x ^ p.m| *
                |deriv (frozenElliptic p u₂) x -
                  deriv (frozenElliptic p u₁) x| +
              |u₂ x ^ p.m - u₁ x ^ p.m| *
                |deriv (frozenElliptic p u₁) x|) := by
        gcongr
        simpa only [abs_mul] using abs_add_le
          (u₂ x ^ p.m *
            (deriv (frozenElliptic p u₂) x -
              deriv (frozenElliptic p u₁) x))
          ((u₂ x ^ p.m - u₁ x ^ p.m) *
            deriv (frozenElliptic p u₁) x)
      _ ≤ A * |dV x| + B * |q x| := by
        rw [abs_of_nonneg (Real.rpow_nonneg (hu₂_mem x).1 _)]
        dsimp [A, B, dV, q]
        rw [abs_mul, abs_mul, abs_of_nonneg hweight0]
        calc
          capWeightSqrt eta R x *
              (u₂ x ^ p.m *
                  |deriv (frozenElliptic p u₂) x -
                    deriv (frozenElliptic p u₁) x| +
                |u₂ x ^ p.m - u₁ x ^ p.m| *
                  |deriv (frozenElliptic p u₁) x|) ≤
            capWeightSqrt eta R x *
              (M ^ p.m *
                  |deriv (frozenElliptic p u₂) x -
                    deriv (frozenElliptic p u₁) x| +
                (p.m * M ^ (p.m - 1) * |u₂ x - u₁ x|) *
                  M ^ p.γ) := by
            apply mul_le_mul_of_nonneg_left _ hweight0
            apply add_le_add
            · exact mul_le_mul_of_nonneg_right hu₂m (abs_nonneg _)
            · exact mul_le_mul hpow hV (abs_nonneg _)
                (mul_nonneg
                  (mul_nonneg (le_trans zero_le_one p.hm)
                    (Real.rpow_nonneg hM _))
                  (abs_nonneg _))
          _ = M ^ p.m *
                (capWeightSqrt eta R x *
                  |deriv (frozenElliptic p u₂) x -
                    deriv (frozenElliptic p u₁) x|) +
              p.m * M ^ (p.m - 1) * M ^ p.γ *
                (capWeightSqrt eta R x * |u₂ x - u₁ x|) := by ring
  have hpoint_sq : ∀ x,
      capWeightedFluxDifference p eta R u₂ u₁ x ^ 2 ≤
        2 * A ^ 2 * dV x ^ 2 + 2 * B ^ 2 * q x ^ 2 := by
    intro x
    have hs := (sq_le_sq₀ (abs_nonneg _)
      (add_nonneg (mul_nonneg hA0 (abs_nonneg _))
        (mul_nonneg hB0 (abs_nonneg _)))).2 (hpoint x)
    rw [sq_abs] at hs
    calc
      capWeightedFluxDifference p eta R u₂ u₁ x ^ 2 ≤
          (A * |dV x| + B * |q x|) ^ 2 := hs
      _ ≤ 2 * (A * |dV x|) ^ 2 + 2 * (B * |q x|) ^ 2 := by
        nlinarith [sq_nonneg (A * |dV x| - B * |q x|)]
      _ = 2 * A ^ 2 * dV x ^ 2 + 2 * B ^ 2 * q x ^ 2 := by
        rw [mul_pow, mul_pow, sq_abs, sq_abs]
        ring
  have hdV : Integrable (fun x => dV x ^ 2) := by
    refine hgrad.1.congr (Eventually.of_forall fun x => ?_)
    dsimp [dV]
    exact (capWeightSqrt_mul_sq_eq eta R x
      (deriv (frozenElliptic p u₂) x -
        deriv (frozenElliptic p u₁) x)).symm
  have hdom : Integrable (fun x =>
      2 * A ^ 2 * dV x ^ 2 + 2 * B ^ 2 * q x ^ 2) :=
    (hdV.const_mul (2 * A ^ 2)).add
      (hq.const_mul (2 * B ^ 2))
  have hflux_cont :
      Continuous (capWeightedFluxDifference p eta R u₂ u₁) := by
    unfold capWeightedFluxDifference
    have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
    have hp₂ : Continuous (fun x => u₂ x ^ p.m) :=
      hu₂.1.rpow_const (fun _ => Or.inr hm0)
    have hp₁ : Continuous (fun x => u₁ x ^ p.m) :=
      hu₁.1.rpow_const (fun _ => Or.inr hm0)
    have hd₂ : Continuous (deriv (frozenElliptic p u₂)) :=
      (frozenElliptic_deriv_lipschitz_of_Icc
        p hM hu₂ hu₂_mem).continuous
    have hd₁ : Continuous (deriv (frozenElliptic p u₁)) :=
      (frozenElliptic_deriv_lipschitz_of_Icc
        p hM hu₁ hu₁_mem).continuous
    exact (capWeightSqrt_continuous eta R).mul
      ((hp₂.mul hd₂).sub (hp₁.mul hd₁))
  have hout : Integrable (fun x =>
      capWeightedFluxDifference p eta R u₂ u₁ x ^ 2) := by
    refine Integrable.mono' hdom
      (hflux_cont.pow 2).aestronglyMeasurable ?_
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint_sq x
  refine ⟨hout, ?_⟩
  calc
    (∫ x : ℝ, capWeightedFluxDifference p eta R u₂ u₁ x ^ 2) ≤
        ∫ x : ℝ, 2 * A ^ 2 * dV x ^ 2 + 2 * B ^ 2 * q x ^ 2 :=
      integral_mono hout hdom hpoint_sq
    _ = 2 * A ^ 2 * (∫ x : ℝ, dV x ^ 2) +
        2 * B ^ 2 * (∫ x : ℝ, q x ^ 2) := by
      rw [integral_add (hdV.const_mul _) (hq.const_mul _),
        integral_const_mul, integral_const_mul]
    _ ≤ 2 * A ^ 2 *
          (K ^ 2 * ∫ x : ℝ,
            capWeight eta R x * |u₂ x - u₁ x| ^ 2) +
        2 * B ^ 2 * ∫ x : ℝ,
          capWeight eta R x * |u₂ x - u₁ x| ^ 2 := by
      have hgrad_le : (∫ x : ℝ, dV x ^ 2) ≤
          K ^ 2 * ∫ x : ℝ,
            capWeight eta R x * |u₂ x - u₁ x| ^ 2 := by
        calc
          (∫ x : ℝ, dV x ^ 2) =
              ∫ x : ℝ, capWeight eta R x *
                |deriv (frozenElliptic p u₂) x -
                  deriv (frozenElliptic p u₁) x| ^ 2 := by
            apply integral_congr_ae
            exact Eventually.of_forall fun x => by
              dsimp [dV]
              exact capWeightSqrt_mul_sq_eq eta R x _
          _ ≤ K ^ 2 * ∫ x : ℝ,
              capWeight eta R x * |u₂ x - u₁ x| ^ 2 := by
            simpa only [K] using hgrad.2
      have hq_eq : (∫ x : ℝ, q x ^ 2) =
          ∫ x : ℝ, capWeight eta R x * |u₂ x - u₁ x| ^ 2 := by
        simpa only [q] using
          (capWeighted_raw_difference_sq_integral_eq
            (eta := eta) (R := R) (u₂ := u₂) (u₁ := u₁))
      rw [hq_eq]
      exact add_le_add
        (mul_le_mul_of_nonneg_left hgrad_le (by positivity)) le_rfl
    _ = capWeightedFluxSquareConstant p M eta *
        ∫ x : ℝ, capWeight eta R x * |u₂ x - u₁ x| ^ 2 := by
      dsimp [A, B, K, capWeightedFluxSquareConstant]
      ring

/-- The same cap estimate with the physical chemotaxis coefficient `-chi`
included. -/
theorem capWeighted_chemotaxis_operator_l2_bounded
    (p : CMParams) {M eta R : ℝ}
    (hM : 0 ≤ M) (heta_nonneg : 0 ≤ eta) (heta_one : eta < 1)
    {u₂ u₁ : ℝ → ℝ}
    (hu₂ : IsCUnifBdd u₂) (hu₁ : IsCUnifBdd u₁)
    (hu₂_mem : ∀ x, u₂ x ∈ Set.Icc (0 : ℝ) M)
    (hu₁_mem : ∀ x, u₁ x ∈ Set.Icc (0 : ℝ) M)
    (hclose : Integrable (fun x =>
      capWeight eta R x * |u₂ x - u₁ x| ^ 2)) :
    Integrable (fun x =>
        capWeightedChemotaxisOperatorDifference p eta R u₂ u₁ x ^ 2) ∧
      (∫ x : ℝ,
          capWeightedChemotaxisOperatorDifference p eta R u₂ u₁ x ^ 2) ≤
        capWeightedChemotaxisOperatorSquareConstant p M eta *
          ∫ x : ℝ, capWeight eta R x * |u₂ x - u₁ x| ^ 2 := by
  have hflux := capWeighted_flux_difference_l2_bounded
    p hM heta_nonneg heta_one hu₂ hu₁ hu₂_mem hu₁_mem hclose
  have hout : Integrable (fun x =>
      capWeightedChemotaxisOperatorDifference p eta R u₂ u₁ x ^ 2) := by
    have hscaled := hflux.1.const_mul (p.χ ^ 2)
    simpa [capWeightedChemotaxisOperatorDifference, mul_pow] using hscaled
  refine ⟨hout, ?_⟩
  calc
    (∫ x : ℝ,
        capWeightedChemotaxisOperatorDifference p eta R u₂ u₁ x ^ 2) =
        p.χ ^ 2 * ∫ x : ℝ,
          capWeightedFluxDifference p eta R u₂ u₁ x ^ 2 := by
      simp_rw [capWeightedChemotaxisOperatorDifference, mul_pow]
      rw [integral_const_mul]
      congr 1
      ring
    _ ≤ p.χ ^ 2 *
        (capWeightedFluxSquareConstant p M eta *
          ∫ x : ℝ, capWeight eta R x * |u₂ x - u₁ x| ^ 2) :=
      mul_le_mul_of_nonneg_left hflux.2 (sq_nonneg _)
    _ = capWeightedChemotaxisOperatorSquareConstant p M eta *
        ∫ x : ℝ, capWeight eta R x * |u₂ x - u₁ x| ^ 2 := by
      unfold capWeightedChemotaxisOperatorSquareConstant
      ring

/-- A general cap-weighted Lipschitz multiplication estimate.  Keeping this
atom separate lets the physical and shifted reactions share the same
integrability proof. -/
theorem capWeighted_lipschitz_difference_l2_bounded
    {eta R L : ℝ} (hL : 0 ≤ L)
    {u₂ u₁ F₂ F₁ : ℝ → ℝ}
    (hF₂ : Continuous F₂) (hF₁ : Continuous F₁)
    (hpoint : ∀ x, |F₂ x - F₁ x| ≤ L * |u₂ x - u₁ x|)
    (hclose : Integrable (fun x =>
      capWeight eta R x * |u₂ x - u₁ x| ^ 2)) :
    Integrable (fun x =>
        (capWeightSqrt eta R x * (F₂ x - F₁ x)) ^ 2) ∧
      (∫ x : ℝ,
          (capWeightSqrt eta R x * (F₂ x - F₁ x)) ^ 2) ≤
        L ^ 2 * ∫ x : ℝ,
          capWeight eta R x * |u₂ x - u₁ x| ^ 2 := by
  let q : ℝ → ℝ := fun x =>
    capWeightSqrt eta R x * (u₂ x - u₁ x)
  have hq : Integrable (fun x => q x ^ 2) := by
    simpa only [q] using capWeighted_raw_difference_sq_integrable hclose
  have hpoint' : ∀ x,
      |capWeightSqrt eta R x * (F₂ x - F₁ x)| ≤ L * |q x| := by
    intro x
    have hw : 0 ≤ capWeightSqrt eta R x :=
      (capWeightSqrt_pos eta R x).le
    rw [abs_mul, abs_of_nonneg hw]
    dsimp [q]
    rw [abs_mul, abs_of_nonneg hw]
    calc
      capWeightSqrt eta R x * |F₂ x - F₁ x| ≤
          capWeightSqrt eta R x * (L * |u₂ x - u₁ x|) :=
        mul_le_mul_of_nonneg_left (hpoint x) hw
      _ = L * (capWeightSqrt eta R x * |u₂ x - u₁ x|) := by ring
  have hpoint_sq : ∀ x,
      (capWeightSqrt eta R x * (F₂ x - F₁ x)) ^ 2 ≤
        L ^ 2 * q x ^ 2 := by
    intro x
    have hs := (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg hL (abs_nonneg _))).2 (hpoint' x)
    simpa [sq_abs, mul_pow] using hs
  have hdom : Integrable (fun x => L ^ 2 * q x ^ 2) :=
    hq.const_mul _
  have hout_cont : Continuous (fun x =>
      capWeightSqrt eta R x * (F₂ x - F₁ x)) :=
    (capWeightSqrt_continuous eta R).mul (hF₂.sub hF₁)
  have hout : Integrable (fun x =>
      (capWeightSqrt eta R x * (F₂ x - F₁ x)) ^ 2) := by
    refine Integrable.mono' hdom
      (hout_cont.pow 2).aestronglyMeasurable ?_
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint_sq x
  refine ⟨hout, ?_⟩
  calc
    (∫ x : ℝ,
        (capWeightSqrt eta R x * (F₂ x - F₁ x)) ^ 2) ≤
        ∫ x : ℝ, L ^ 2 * q x ^ 2 :=
      integral_mono hout hdom hpoint_sq
    _ = L ^ 2 * ∫ x : ℝ, q x ^ 2 := by rw [integral_const_mul]
    _ = L ^ 2 * ∫ x : ℝ,
        capWeight eta R x * |u₂ x - u₁ x| ^ 2 := by
      rw [show (∫ x : ℝ, q x ^ 2) =
          ∫ x : ℝ, capWeight eta R x * |u₂ x - u₁ x| ^ 2 by
        simpa only [q] using
          (capWeighted_raw_difference_sq_integral_eq
            (eta := eta) (R := R) (u₂ := u₂) (u₁ := u₁))]

/-- The physical logistic reaction difference is cap-weighted `L²` bounded,
uniformly in `R`. -/
theorem capWeighted_reaction_difference_l2_bounded
    (p : CMParams) {M eta R : ℝ} (hM : 0 ≤ M)
    {u₂ u₁ : ℝ → ℝ}
    (hu₂ : IsCUnifBdd u₂) (hu₁ : IsCUnifBdd u₁)
    (hu₂_mem : ∀ x, u₂ x ∈ Set.Icc (0 : ℝ) M)
    (hu₁_mem : ∀ x, u₁ x ∈ Set.Icc (0 : ℝ) M)
    (hclose : Integrable (fun x =>
      capWeight eta R x * |u₂ x - u₁ x| ^ 2)) :
    Integrable (fun x =>
        capWeightedReactionDifference p eta R u₂ u₁ x ^ 2) ∧
      (∫ x : ℝ,
          capWeightedReactionDifference p eta R u₂ u₁ x ^ 2) ≤
        reactionLip p.α M ^ 2 *
          ∫ x : ℝ, capWeight eta R x * |u₂ x - u₁ x| ^ 2 := by
  have hL : 0 ≤ reactionLip p.α M := reactionLip_nonneg p.hα hM
  have hcore := capWeighted_lipschitz_difference_l2_bounded hL
    (u₂ := u₂) (u₁ := u₁)
    (F₂ := fun x => reactionFun p.α (u₂ x))
    (F₁ := fun x => reactionFun p.α (u₁ x))
    ((continuous_reactionFun (le_trans zero_le_one p.hα)).comp hu₂.1)
    ((continuous_reactionFun (le_trans zero_le_one p.hα)).comp hu₁.1)
    (fun x => reaction_increment_abs_le p.hα hM
      (hu₁_mem x) (hu₂_mem x))
    hclose
  simpa only [capWeightedReactionDifference] using hcore

/-- Cap-conjugated source difference for the shifted generator `Delta-I`. -/
def capWeightedShiftedReactionDifference
    (p : CMParams) (eta R : ℝ) (u₂ u₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  capWeightSqrt eta R x *
    (wholeLineCauchyShiftedReaction p u₂ x -
      wholeLineCauchyShiftedReaction p u₁ x)

/-- The shifted reaction source used by the Henry restart is cap-weighted
`L²` bounded.  Its constant is independent of `R`. -/
theorem capWeighted_shiftedReaction_difference_l2_bounded
    (p : CMParams) {M eta R : ℝ} (hM : 0 ≤ M)
    {u₂ u₁ : ℝ → ℝ}
    (hu₂ : IsCUnifBdd u₂) (hu₁ : IsCUnifBdd u₁)
    (hu₂_mem : ∀ x, u₂ x ∈ Set.Icc (0 : ℝ) M)
    (hu₁_mem : ∀ x, u₁ x ∈ Set.Icc (0 : ℝ) M)
    (hclose : Integrable (fun x =>
      capWeight eta R x * |u₂ x - u₁ x| ^ 2)) :
    Integrable (fun x =>
        capWeightedShiftedReactionDifference p eta R u₂ u₁ x ^ 2) ∧
      (∫ x : ℝ,
          capWeightedShiftedReactionDifference p eta R u₂ u₁ x ^ 2) ≤
        (1 + reactionLip p.α M) ^ 2 *
          ∫ x : ℝ, capWeight eta R x * |u₂ x - u₁ x| ^ 2 := by
  have hL : 0 ≤ 1 + reactionLip p.α M := by
    linarith [reactionLip_nonneg p.hα hM]
  have hpoint : ∀ x,
      |wholeLineCauchyShiftedReaction p u₂ x -
          wholeLineCauchyShiftedReaction p u₁ x| ≤
        (1 + reactionLip p.α M) * |u₂ x - u₁ x| := by
    intro x
    have hr := reaction_increment_abs_le p.hα hM
      (hu₁_mem x) (hu₂_mem x)
    have hsplit :
        wholeLineCauchyShiftedReaction p u₂ x -
            wholeLineCauchyShiftedReaction p u₁ x =
          (u₂ x - u₁ x) +
            (reactionFun p.α (u₂ x) - reactionFun p.α (u₁ x)) := by
      simp only [wholeLineCauchyShiftedReaction, wholeLineLogisticSource]
      ring
    rw [hsplit]
    calc
      |(u₂ x - u₁ x) +
          (reactionFun p.α (u₂ x) - reactionFun p.α (u₁ x))| ≤
          |u₂ x - u₁ x| +
            |reactionFun p.α (u₂ x) - reactionFun p.α (u₁ x)| :=
        abs_add_le _ _
      _ ≤ |u₂ x - u₁ x| +
          reactionLip p.α M * |u₂ x - u₁ x| :=
        add_le_add le_rfl hr
      _ = (1 + reactionLip p.α M) * |u₂ x - u₁ x| := by ring
  have hcore := capWeighted_lipschitz_difference_l2_bounded hL
    (u₂ := u₂) (u₁ := u₁)
    (F₂ := wholeLineCauchyShiftedReaction p u₂)
    (F₁ := wholeLineCauchyShiftedReaction p u₁)
    (wholeLineCauchyShiftedReaction_continuous p hu₂.1)
    (wholeLineCauchyShiftedReaction_continuous p hu₁.1)
    hpoint hclose
  simpa only [capWeightedShiftedReactionDifference] using hcore

section AxiomAudit

#print axioms capWeighted_flux_difference_l2_bounded
#print axioms capWeighted_chemotaxis_operator_l2_bounded
#print axioms capWeighted_reaction_difference_l2_bounded
#print axioms capWeighted_shiftedReaction_difference_l2_bounded

end AxiomAudit

end ShenWork.Paper1
