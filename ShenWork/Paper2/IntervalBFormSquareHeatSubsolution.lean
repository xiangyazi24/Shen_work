import ShenWork.Paper2.IntervalBFormNegPartStrictPosBarrier

open Filter Topology Set

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData conjugatePicardLimit)
open ShenWork.IntervalMildToClassical
  (mildChemicalConcentration)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator)
open ShenWork.IntervalMildPicardThreshold
  (unitClip unitClip_of_mem)
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- The squared heat lower barrier
`w(t,x) = exp (-M t) * (S_N(t) f x)^2`. -/
def squareHeatBarrier (M : ℝ) (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  Real.exp (-M * t) * (intervalFullSemigroupOperator t f x) ^ 2

/-- Seed data for the squared heat barrier.  The final field is the initial
comparison `f^2 ≤ u₀`. -/
structure SquareHeatSeed (u₀ f : ℝ → ℝ) : Prop where
  continuousOn : ContinuousOn f (Set.Icc (0 : ℝ) 1)
  nonneg : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f y
  pos_somewhere : ∃ y₀ ∈ Set.Icc (0 : ℝ) 1, 0 < f y₀
  square_le_initial : ∀ y ∈ Set.Icc (0 : ℝ) 1, f y ^ 2 ≤ u₀ y

/-- The semigroup positivity banked in `IntervalSemigroupConeAtoms` makes the
squared heat barrier strictly positive for every positive time. -/
theorem squareHeatBarrier_pos
    {M t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hf_nonneg : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f y)
    (hf_pos_somewhere : ∃ y₀ ∈ Set.Icc (0 : ℝ) 1, 0 < f y₀)
    (x : ℝ) :
    0 < squareHeatBarrier M f t x := by
  unfold squareHeatBarrier
  have hS : 0 < intervalFullSemigroupOperator t f x :=
    intervalFullSemigroupOperator_pos_of_nonneg_nonzero
      ht hf_cont hf_nonneg hf_pos_somewhere x
  exact mul_pos (Real.exp_pos _) (sq_pos_of_pos hS)

/-- Residual of the linear drift-reaction operator
`∂ₜw - ∂ₓₓw - B ∂ₓw - Cw`. -/
def neumannLinearDriftResidual
    (B C w : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  deriv (fun τ : ℝ => w τ x) t
    - deriv (fun z : ℝ => deriv (fun y : ℝ => w t y) z) x
    - B t x * deriv (fun y : ℝ => w t y) x
    - C t x * w t x

/-- Algebraic core of the squared-barrier residual after using `h_t = h_xx`. -/
def squareHeatResidualCore (M b c h hx : ℝ) : ℝ :=
  -M * h ^ 2 - 2 * hx ^ 2 - 2 * b * h * hx - c * h ^ 2

/-- The completing-the-square estimate:
`-2 hx^2 - 2 b h hx ≤ (A^2 / 2) h^2`, and hence the whole residual core is
nonpositive when `M ≥ A^2/2 + D` and `-c ≤ D`. -/
theorem squareHeatResidualCore_nonpos_of_bounds
    {A D M b c h hx : ℝ}
    (hb : |b| ≤ A) (hc : -c ≤ D) (hM : A ^ 2 / 2 + D ≤ M) :
    squareHeatResidualCore M b c h hx ≤ 0 := by
  unfold squareHeatResidualCore
  have hcross :
      -2 * hx ^ 2 - 2 * b * h * hx ≤ (A ^ 2 / 2) * h ^ 2 := by
    have hcross_b :
        -2 * hx ^ 2 - 2 * b * h * hx ≤ (b ^ 2 / 2) * h ^ 2 := by
      have hsq : 0 ≤ (2 * hx + b * h) ^ 2 :=
        sq_nonneg (2 * hx + b * h)
      nlinarith
    have hA_nonneg : 0 ≤ A := le_trans (abs_nonneg b) hb
    have hb_absA : |b| ≤ |A| := by
      rwa [abs_of_nonneg hA_nonneg]
    have hbsq : b ^ 2 ≤ A ^ 2 := sq_le_sq.mpr hb_absA
    have hh : 0 ≤ h ^ 2 := sq_nonneg h
    have hscale : (b ^ 2 / 2) * h ^ 2 ≤ (A ^ 2 / 2) * h ^ 2 := by
      nlinarith
    linarith
  have hh : 0 ≤ h ^ 2 := sq_nonneg h
  nlinarith

/-- Classical PDE identity package for the target linear equation
`u_t = u_xx + B u_x + C u` with homogeneous Neumann boundary data. -/
structure NeumannLinearDriftSolution
    (T : ℝ) (B C : ℝ → ℝ → ℝ) (u₀ : ℝ → ℝ)
    (u : ℝ → ℝ → ℝ) : Prop where
  initial :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, u 0 x = u₀ x
  pde :
    ∀ t x, 0 < t → t < T → x ∈ Set.Ioo (0 : ℝ) 1 →
      neumannLinearDriftResidual B C u t x = 0
  neumann :
    ∀ t, 0 < t → t < T →
      deriv (fun z : ℝ => u t z) 0 = 0 ∧
      deriv (fun z : ℝ => u t z) 1 = 0

/-- Minimal Neumann comparison principle needed here.  It is deliberately a
named hypothesis because the repository's existing comparison theorem is the
whole-line reaction form, not this interval drift-reaction form. -/
def NeumannLinearDriftComparison
    (T : ℝ) (B C : ℝ → ℝ → ℝ) (u₀ : ℝ → ℝ)
    (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ w : ℝ → ℝ → ℝ,
    0 < T →
    NeumannLinearDriftSolution T B C u₀ u →
    (∀ x ∈ Set.Icc (0 : ℝ) 1, w 0 x ≤ u₀ x) →
    (∀ t x, 0 < t → t < T → x ∈ Set.Ioo (0 : ℝ) 1 →
      neumannLinearDriftResidual B C w t x ≤ 0) →
    (∀ t, 0 < t → t < T →
      deriv (fun z : ℝ => w t z) 0 = 0 ∧
      deriv (fun z : ℝ => w t z) 1 = 0) →
    ∀ t x, 0 < t → t < T → x ∈ Set.Icc (0 : ℝ) 1 →
      w t x ≤ u t x

/-- The calculus identity for the squared heat barrier after using the heat
equation for `h = S_N(t) f`, together with its initial trace and Neumann
boundary condition. -/
structure SquareHeatSubsolutionCalculus
    (T M : ℝ) (f : ℝ → ℝ) (B C : ℝ → ℝ → ℝ) : Prop where
  residual_eq :
    ∀ t x, 0 < t → t < T →
      neumannLinearDriftResidual B C (squareHeatBarrier M f) t x =
        Real.exp (-M * t) *
          squareHeatResidualCore M (B t x) (C t x)
            (intervalFullSemigroupOperator t f x)
            (deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x)
  initial_eq :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      squareHeatBarrier M f 0 x = f x ^ 2
  neumann :
    ∀ t, 0 < t → t < T →
      deriv (fun z : ℝ => squareHeatBarrier M f t z) 0 = 0 ∧
      deriv (fun z : ℝ => squareHeatBarrier M f t z) 1 = 0

/-- The squared heat barrier is a genuine sub-solution of
`w_t = w_xx + B w_x + C w` under the drift/reaction bounds. -/
theorem squareHeatBarrier_subsolution_residual_nonpos
    {T A D M : ℝ} {f : ℝ → ℝ} {B C : ℝ → ℝ → ℝ}
    (hcalc : SquareHeatSubsolutionCalculus T M f B C)
    (hM : A ^ 2 / 2 + D ≤ M)
    (hB_bound :
      ∀ t x, 0 < t → t < T → x ∈ Set.Ioo (0 : ℝ) 1 → |B t x| ≤ A)
    (hC_neg_bound :
      ∀ t x, 0 < t → t < T → x ∈ Set.Ioo (0 : ℝ) 1 → -C t x ≤ D) :
    ∀ t x, 0 < t → t < T → x ∈ Set.Ioo (0 : ℝ) 1 →
      neumannLinearDriftResidual B C (squareHeatBarrier M f) t x ≤ 0 := by
  intro t x ht htT hx
  rw [hcalc.residual_eq t x ht htT]
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    (squareHeatResidualCore_nonpos_of_bounds
      (hB_bound t x ht htT hx) (hC_neg_bound t x ht htT hx) hM)

/-- The comparison-produced lower barrier
`exp (-M t) (S_N(t) f)^2 ≤ u(t)`. -/
theorem square_heat_hbarrier_of_neumann_linear_drift_square_heat_subsolution
    {T A D M : ℝ} {u₀ f : ℝ → ℝ} {B C u : ℝ → ℝ → ℝ}
    (hT : 0 < T)
    (hu : NeumannLinearDriftSolution T B C u₀ u)
    (hcompare : NeumannLinearDriftComparison T B C u₀ u)
    (hcalc : SquareHeatSubsolutionCalculus T M f B C)
    (hM : A ^ 2 / 2 + D ≤ M)
    (hB_bound :
      ∀ t x, 0 < t → t < T → x ∈ Set.Ioo (0 : ℝ) 1 → |B t x| ≤ A)
    (hC_neg_bound :
      ∀ t x, 0 < t → t < T → x ∈ Set.Ioo (0 : ℝ) 1 → -C t x ≤ D)
    (hseed : SquareHeatSeed u₀ f) :
    ∀ t x, 0 < t → t < T → x ∈ Set.Icc (0 : ℝ) 1 →
      squareHeatBarrier M f t x ≤ u t x := by
  have hinit :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        squareHeatBarrier M f 0 x ≤ u₀ x := by
    intro x hx
    rw [hcalc.initial_eq x hx]
    exact hseed.square_le_initial x hx
  exact hcompare (squareHeatBarrier M f) hT hu hinit
    (squareHeatBarrier_subsolution_residual_nonpos
      hcalc hM hB_bound hC_neg_bound)
    hcalc.neumann

/-- Strict positivity from the squared heat sub-solution and Neumann linear
comparison. -/
theorem strict_pos_of_neumann_linear_drift_square_heat_subsolution
    {T A D M : ℝ} {u₀ f : ℝ → ℝ} {B C u : ℝ → ℝ → ℝ}
    (hT : 0 < T)
    (hu : NeumannLinearDriftSolution T B C u₀ u)
    (hcompare : NeumannLinearDriftComparison T B C u₀ u)
    (hcalc : SquareHeatSubsolutionCalculus T M f B C)
    (hM : A ^ 2 / 2 + D ≤ M)
    (hB_bound :
      ∀ t x, 0 < t → t < T → x ∈ Set.Ioo (0 : ℝ) 1 → |B t x| ≤ A)
    (hC_neg_bound :
      ∀ t x, 0 < t → t < T → x ∈ Set.Ioo (0 : ℝ) 1 → -C t x ≤ D)
    (hseed : SquareHeatSeed u₀ f) :
    ∀ t x, 0 < t → t < T → x ∈ Set.Icc (0 : ℝ) 1 →
      0 < u t x := by
  intro t x ht htT hx
  exact lt_of_lt_of_le
    (squareHeatBarrier_pos (M := M) ht
      hseed.continuousOn hseed.nonneg hseed.pos_somewhere x)
    (square_heat_hbarrier_of_neumann_linear_drift_square_heat_subsolution
      hT hu hcompare hcalc hM hB_bound hC_neg_bound hseed t x ht htT hx)

/-- The real-line lift of the B-form Picard limit, used to feed the abstract
linear comparison interface on `[0,1]`. -/
def bformConjugatePicardLift
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) : ℝ → ℝ → ℝ :=
  fun t x => conjugatePicardLimit p u₀ DB.T t (unitClip x)

/-- B-form hbarrier produced by the abstract squared-heat subsolution route. -/
theorem bform_square_heat_hbarrier_of_neumann_linear_drift_square_heat_subsolution
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    {A D M : ℝ} {f : ℝ → ℝ} {drift react : ℝ → ℝ → ℝ}
    (hu :
      NeumannLinearDriftSolution DB.T drift react (intervalDomainLift u₀)
        (bformConjugatePicardLift p DB))
    (hcompare :
      NeumannLinearDriftComparison DB.T drift react (intervalDomainLift u₀)
        (bformConjugatePicardLift p DB))
    (hcalc : SquareHeatSubsolutionCalculus DB.T M f drift react)
    (hM : A ^ 2 / 2 + D ≤ M)
    (hB_bound :
      ∀ t x, 0 < t → t < DB.T → x ∈ Set.Ioo (0 : ℝ) 1 →
        |drift t x| ≤ A)
    (hC_neg_bound :
      ∀ t x, 0 < t → t < DB.T → x ∈ Set.Ioo (0 : ℝ) 1 →
        -react t x ≤ D)
    (hseed : SquareHeatSeed (intervalDomainLift u₀) f) :
    ∀ t x, 0 < t → t < DB.T →
      squareHeatBarrier M f t x.1 ≤
        conjugatePicardLimit p u₀ DB.T t x := by
  intro t x ht htT
  have hx : x.1 ∈ Set.Icc (0 : ℝ) 1 := x.2
  have hreal :=
    square_heat_hbarrier_of_neumann_linear_drift_square_heat_subsolution
      (T := DB.T) (A := A) (D := D) (M := M)
      (u₀ := intervalDomainLift u₀) (f := f)
      (B := drift) (C := react)
      (u := bformConjugatePicardLift p DB)
      DB.hT hu hcompare hcalc hM hB_bound hC_neg_bound hseed
      t x.1 ht htT hx
  simpa [bformConjugatePicardLift, unitClip_of_mem hx] using hreal

/-- B-form strict positivity from a squared heat hbarrier. -/
theorem bform_strictPos_of_square_heat_subsolution
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀} {M : ℝ} {f : ℝ → ℝ}
    (hseed : SquareHeatSeed (intervalDomainLift u₀) f)
    (hbarrier :
      ∀ t x, 0 < t → t < DB.T →
        squareHeatBarrier M f t x.1 ≤
          conjugatePicardLimit p u₀ DB.T t x) :
    ∀ t x, 0 < t → t < DB.T →
      0 < conjugatePicardLimit p u₀ DB.T t x := by
  intro t x ht htT
  exact lt_of_lt_of_le
    (squareHeatBarrier_pos (M := M) ht
      hseed.continuousOn hseed.nonneg hseed.pos_somewhere x.1)
    (hbarrier t x ht htT)

/-- Route constructor using the squared heat hbarrier. -/
def bform_negpart_route_of_square_heat_lower_barrier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀} {M : ℝ} {f : ℝ → ℝ}
    (datum : PositiveInitialDatum intervalDomain u₀)
    (Bbank : ShenWork.Paper2.BFormDirectClassical.BFormBankedInputs p DB)
    (hnegativePart_zero :
      ∀ t, 0 < t → t ≤ DB.T → ∀ x : intervalDomainPoint,
        negativePart (conjugatePicardLimit p u₀ DB.T t x) = 0)
    (hseed : SquareHeatSeed (intervalDomainLift u₀) f)
    (hbarrier :
      ∀ t x, 0 < t → t < DB.T →
        squareHeatBarrier M f t x.1 ≤
          conjugatePicardLimit p u₀ DB.T t x) :
    BFormNegativePartPositivityRoute p DB where
  datum := datum
  negativePart_zero := hnegativePart_zero
  strictPos := bform_strictPos_of_square_heat_subsolution hseed hbarrier
  hpde_u := bform_negpart_hpde_u_of_bank Bbank

/-- Route constructor with the hbarrier discharged by the squared heat
subsolution plus the named Neumann linear comparison principle. -/
def bform_negpart_route_of_square_heat_subsolution
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    {A D M : ℝ} {f : ℝ → ℝ} {drift react : ℝ → ℝ → ℝ}
    (datum : PositiveInitialDatum intervalDomain u₀)
    (Bbank : ShenWork.Paper2.BFormDirectClassical.BFormBankedInputs p DB)
    (hnegativePart_zero :
      ∀ t, 0 < t → t ≤ DB.T → ∀ x : intervalDomainPoint,
        negativePart (conjugatePicardLimit p u₀ DB.T t x) = 0)
    (hu :
      NeumannLinearDriftSolution DB.T drift react (intervalDomainLift u₀)
        (bformConjugatePicardLift p DB))
    (hcompare :
      NeumannLinearDriftComparison DB.T drift react (intervalDomainLift u₀)
        (bformConjugatePicardLift p DB))
    (hcalc : SquareHeatSubsolutionCalculus DB.T M f drift react)
    (hM : A ^ 2 / 2 + D ≤ M)
    (hB_bound :
      ∀ t x, 0 < t → t < DB.T → x ∈ Set.Ioo (0 : ℝ) 1 →
        |drift t x| ≤ A)
    (hC_neg_bound :
      ∀ t x, 0 < t → t < DB.T → x ∈ Set.Ioo (0 : ℝ) 1 →
        -react t x ≤ D)
    (hseed : SquareHeatSeed (intervalDomainLift u₀) f) :
    BFormNegativePartPositivityRoute p DB :=
  bform_negpart_route_of_square_heat_lower_barrier datum Bbank
    hnegativePart_zero hseed
    (bform_square_heat_hbarrier_of_neumann_linear_drift_square_heat_subsolution
      hu hcompare hcalc hM hB_bound hC_neg_bound hseed)

end ShenWork.Paper2.BFormPositiveDatumNegPart
