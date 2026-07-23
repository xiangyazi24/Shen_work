import ShenWork.Paper1.WholeLineChiPosWeightedEntropyDissipation
import ShenWork.Paper1.WholeLineWeightedRegularityCoMovingComparisonNatural
import ShenWork.Paper1.WholeLineWeightedRegularityGlobalStrictPositivityNatural

open MeasureTheory Real Set
open scoped Interval

set_option maxHeartbeats 1000000

noncomputable section

namespace ShenWork.Paper1

/-!
# Weighted entropy dissipation for the canonical co-moving orbit

This file instantiates `ChiOneWeightedEntropySlice` with an actual positive-time
slice of `wholeLineCauchyGlobalU`.  The shifted elliptic resolver is normalized
around the equilibrium one, so its equation has source `u - 1`.
-/

/-- The population slice in the frame moving with speed `c`. -/
def wholeLineCauchyGlobalCoMovingU
    (p : CMParams) (u₀ : WholeLineBUC) (c t : ℝ) : ℝ → ℝ :=
  coMovingPath c (wholeLineCauchyGlobalU p u₀) t

/-- The first spatial derivative of the co-moving population slice. -/
def wholeLineCauchyGlobalCoMovingUx
    (p : CMParams) (u₀ : WholeLineBUC) (c t : ℝ) : ℝ → ℝ :=
  deriv (wholeLineCauchyGlobalCoMovingU p u₀ c t)

/-- The second spatial derivative of the co-moving population slice. -/
def wholeLineCauchyGlobalCoMovingUxx
    (p : CMParams) (u₀ : WholeLineBUC) (c t : ℝ) : ℝ → ℝ :=
  deriv (wholeLineCauchyGlobalCoMovingUx p u₀ c t)

/-- The co-moving elliptic resolver, shifted by its equilibrium value one. -/
def wholeLineCauchyGlobalCoMovingR
    (p : CMParams) (u₀ : WholeLineBUC) (c t : ℝ) : ℝ → ℝ :=
  fun x ↦
    frozenElliptic p (wholeLineCauchyGlobalCoMovingU p u₀ c t) x - 1

/-- The first spatial derivative of the shifted co-moving resolver. -/
def wholeLineCauchyGlobalCoMovingRx
    (p : CMParams) (u₀ : WholeLineBUC) (c t : ℝ) : ℝ → ℝ :=
  deriv (frozenElliptic p (wholeLineCauchyGlobalCoMovingU p u₀ c t))

/-- The resolver second derivative in its normalized `γ = 1` form. -/
def wholeLineCauchyGlobalCoMovingRxx
    (p : CMParams) (u₀ : WholeLineBUC) (c t : ℝ) : ℝ → ℝ :=
  fun x ↦
    frozenElliptic p (wholeLineCauchyGlobalCoMovingU p u₀ c t) x -
      wholeLineCauchyGlobalCoMovingU p u₀ c t x

/-- The genuine time derivative of the population along the co-moving path. -/
def wholeLineCauchyGlobalCoMovingUt
    (p : CMParams) (u₀ : WholeLineBUC) (c t : ℝ) : ℝ → ℝ :=
  fun x ↦
    deriv (fun s ↦ coMovingPath c (wholeLineCauchyGlobalU p u₀) s x) t

/-- Every positive canonical co-moving orbit slice supplies all fields of the
abstract weighted entropy engine when `m = γ = α = 1`. -/
theorem wholeLineCauchyGlobalU_chiOneWeightedEntropySlice
    (p : CMParams) (u₀ : WholeLineBUC)
    (hregime : WholeLineCauchyCeilingRegime p)
    (hu₀ : ∀ x, 0 ≤ u₀.1 x) (hleft : StrictlyPositiveAtLeft u₀.1)
    (hp : p.m = 1 ∧ p.γ = 1 ∧ p.α = 1)
    (a b c ell : ℝ) (w w' : ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hw_pos : ∀ x, 0 < w x)
    (hw_deriv : ∀ x, HasDerivAt w (w' x) x)
    (hw'_cont : Continuous w')
    (hw_slow : ∀ x, |w' x| ≤ (1 / ell) * w x)
    (hab : a ≤ b) (hell : 0 < ell) :
    ChiOneWeightedEntropySlice a b c p.χ ell w w'
      (wholeLineCauchyGlobalCoMovingU p u₀ c t)
      (wholeLineCauchyGlobalCoMovingUx p u₀ c t)
      (wholeLineCauchyGlobalCoMovingUxx p u₀ c t)
      (wholeLineCauchyGlobalCoMovingR p u₀ c t)
      (wholeLineCauchyGlobalCoMovingRx p u₀ c t)
      (wholeLineCauchyGlobalCoMovingRxx p u₀ c t)
      (wholeLineCauchyGlobalCoMovingUt p u₀ c t) := by
  rcases hp with ⟨hm, hgamma, halpha⟩
  let q : ℝ → ℝ := wholeLineCauchyGlobalCoMovingU p u₀ c t
  have hq_cub : IsCUnifBdd q := by
    simpa [q, wholeLineCauchyGlobalCoMovingU] using
      wholeLineCauchyGlobal_coMoving_slice_isCUnifBdd p u₀ c t
  have hq_nonneg : ∀ x, 0 ≤ q x := by
    intro x
    simpa [q, wholeLineCauchyGlobalCoMovingU, coMovingPath] using
      wholeLineCauchyGlobal_nonnegative
        p hregime u₀ hu₀ ht.le (x + c * t)
  have hq_pos : ∀ x, 0 < q x := by
    intro x
    simpa [q, wholeLineCauchyGlobalCoMovingU, coMovingPath] using
      wholeLineCauchyGlobal_pos_of_posAtBot
        p hregime u₀ hu₀ hleft ht (x + c * t)
  have hq_two : ContDiff ℝ 2 q := by
    simpa [q, wholeLineCauchyGlobalCoMovingU] using
      wholeLineCauchyGlobalU_coMoving_contDiff_two_positive
        p hregime u₀ hu₀ (c := c) ht
  have hq_cont : Continuous q := hq_two.continuous
  have hqx_cont : Continuous (deriv q) :=
    hq_two.continuous_deriv (by norm_num)
  have hqxx_cont : Continuous (deriv (deriv q)) := by
    simpa [iteratedDeriv_succ] using
      hq_two.continuous_iteratedDeriv' 2
  have hV_cont : Continuous (frozenElliptic p q) :=
    frozenElliptic_continuous p hq_cub hq_nonneg
  have hVx_diff : Differentiable ℝ (deriv (frozenElliptic p q)) := by
    intro x
    exact frozenElliptic_deriv_differentiableAt p hq_cub hq_nonneg x
  have hVx_cont : Continuous (deriv (frozenElliptic p q)) :=
    hVx_diff.continuous
  have hrxx_cont : Continuous (fun x ↦ frozenElliptic p q x - q x) :=
    hV_cont.sub hq_cont
  have hpde : ∀ x,
      wholeLineCauchyGlobalCoMovingUt p u₀ c t x =
        wholeLineCauchyGlobalCoMovingUxx p u₀ c t x +
          c * wholeLineCauchyGlobalCoMovingUx p u₀ c t x -
          p.χ *
            (wholeLineCauchyGlobalCoMovingUx p u₀ c t x *
                wholeLineCauchyGlobalCoMovingRx p u₀ c t x +
              wholeLineCauchyGlobalCoMovingU p u₀ c t x *
                wholeLineCauchyGlobalCoMovingRxx p u₀ c t x) +
          wholeLineCauchyGlobalCoMovingU p u₀ c t x *
            (1 - wholeLineCauchyGlobalCoMovingU p u₀ c t x) := by
    intro x
    have htime :=
      wholeLineCauchyGlobal_coMovingPath_hasDerivAt_paperWaveOperator
        p hregime u₀ hu₀ c ht x
    have htime_eq :
        wholeLineCauchyGlobalCoMovingUt p u₀ c t x =
          paperWaveOperator p c q q x := by
      simpa [wholeLineCauchyGlobalCoMovingUt, q,
        wholeLineCauchyGlobalCoMovingU] using htime.deriv
    rw [htime_eq]
    simp [paperWaveOperator, wholeLineCauchyGlobalCoMovingU,
      wholeLineCauchyGlobalCoMovingUx,
      wholeLineCauchyGlobalCoMovingUxx,
      wholeLineCauchyGlobalCoMovingRx,
      wholeLineCauchyGlobalCoMovingRxx, q, hm, hgamma, halpha,
      iteratedDeriv_succ]
    ring
  have hut_cont :
      Continuous (wholeLineCauchyGlobalCoMovingUt p u₀ c t) := by
    rw [show wholeLineCauchyGlobalCoMovingUt p u₀ c t = fun x ↦
        wholeLineCauchyGlobalCoMovingUxx p u₀ c t x +
          c * wholeLineCauchyGlobalCoMovingUx p u₀ c t x -
          p.χ *
            (wholeLineCauchyGlobalCoMovingUx p u₀ c t x *
                wholeLineCauchyGlobalCoMovingRx p u₀ c t x +
              wholeLineCauchyGlobalCoMovingU p u₀ c t x *
                wholeLineCauchyGlobalCoMovingRxx p u₀ c t x) +
          wholeLineCauchyGlobalCoMovingU p u₀ c t x *
            (1 - wholeLineCauchyGlobalCoMovingU p u₀ c t x) by
      funext x
      exact hpde x]
    change Continuous (fun x ↦
      deriv (deriv q) x + c * deriv q x -
        p.χ *
          (deriv q x * deriv (frozenElliptic p q) x +
            q x * (frozenElliptic p q x - q x)) +
        q x * (1 - q x))
    fun_prop
  refine
    { hab := hab
      hell := hell
      u_pos := ?_
      w_pos := hw_pos
      w_deriv := hw_deriv
      w'_cont := hw'_cont
      w_slow := hw_slow
      u_deriv := ?_
      ux_deriv := ?_
      r_deriv := ?_
      rx_deriv := ?_
      uxx_continuous := ?_
      rxx_continuous := ?_
      ut_continuous := hut_cont
      population_pde := hpde
      resolver_pde := ?_ }
  · simpa [q] using hq_pos
  · intro x
    simpa [q, wholeLineCauchyGlobalCoMovingUx] using
      (hq_two.differentiable (by norm_num)).differentiableAt.hasDerivAt
  · intro x
    simpa [q, wholeLineCauchyGlobalCoMovingUx,
      wholeLineCauchyGlobalCoMovingUxx] using
      (hq_two.differentiable_deriv_two x).hasDerivAt
  · intro x
    have hV := (frozenElliptic_differentiable p hq_cub hq_nonneg x).hasDerivAt
    change HasDerivAt (fun y ↦ frozenElliptic p q y - 1)
      (deriv (frozenElliptic p q) x) x
    exact hV.sub_const 1
  · intro x
    have hVx :=
      (frozenElliptic_deriv_differentiableAt
        p hq_cub hq_nonneg x).hasDerivAt
    rw [frozenElliptic_deriv_deriv_eq p hq_cub hq_nonneg x] at hVx
    simpa [q, wholeLineCauchyGlobalCoMovingRx,
      wholeLineCauchyGlobalCoMovingRxx, hgamma] using hVx
  · simpa [q, wholeLineCauchyGlobalCoMovingUxx] using hqxx_cont
  · simpa [q, wholeLineCauchyGlobalCoMovingRxx] using hrxx_cont
  · intro x
    simp [wholeLineCauchyGlobalCoMovingR,
      wholeLineCauchyGlobalCoMovingRxx]

/-- The sharp weighted entropy-production inequality for the actual canonical
co-moving Cauchy orbit. -/
theorem wholeLineCauchyGlobalU_weighted_sharp_dissipation
    (p : CMParams) (u₀ : WholeLineBUC)
    (hregime : WholeLineCauchyCeilingRegime p)
    (hu₀ : ∀ x, 0 ≤ u₀.1 x) (hleft : StrictlyPositiveAtLeft u₀.1)
    (hp : p.m = 1 ∧ p.γ = 1 ∧ p.α = 1) (hchi : 0 ≤ p.χ)
    (a b c ell : ℝ) (w w' : ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hw_pos : ∀ x, 0 < w x)
    (hw_deriv : ∀ x, HasDerivAt w (w' x) x)
    (hw'_cont : Continuous w')
    (hw_slow : ∀ x, |w' x| ≤ (1 / ell) * w x)
    (hab : a ≤ b) (hell : 0 < ell) :
    (∫ x in a..b,
        w x *
          chiOneEntropyMultiplier
            (wholeLineCauchyGlobalCoMovingU p u₀ c t x) *
          wholeLineCauchyGlobalCoMovingUt p u₀ c t x) ≤
      -(1 - p.χ ^ 2 / 16) *
          (∫ x in a..b,
            w x * (wholeLineCauchyGlobalCoMovingU p u₀ c t x - 1) ^ 2) +
        ((|c| + p.χ + 2) / ell) *
          ((∫ x in a..b,
              w x *
                chiOneRelativeEntropy
                  (wholeLineCauchyGlobalCoMovingU p u₀ c t x)) +
            (∫ x in a..b,
              w x *
                ((wholeLineCauchyGlobalCoMovingUx p u₀ c t x /
                      wholeLineCauchyGlobalCoMovingU p u₀ c t x) ^ 2 +
                  (wholeLineCauchyGlobalCoMovingU p u₀ c t x - 1) ^ 2))) +
        (p.χ ^ 2 / 4 + p.χ / (2 * ell)) *
          ((1 / (2 * ell)) *
              ((∫ x in a..b,
                  w x * (wholeLineCauchyGlobalCoMovingR p u₀ c t x) ^ 2) +
                ∫ x in a..b,
                  w x *
                    (wholeLineCauchyGlobalCoMovingRx p u₀ c t x) ^ 2) +
            |w b * wholeLineCauchyGlobalCoMovingR p u₀ c t b *
                  wholeLineCauchyGlobalCoMovingRx p u₀ c t b -
              w a * wholeLineCauchyGlobalCoMovingR p u₀ c t a *
                  wholeLineCauchyGlobalCoMovingRx p u₀ c t a|) +
        ((w b *
              chiOneEntropyMultiplier
                (wholeLineCauchyGlobalCoMovingU p u₀ c t b) *
              wholeLineCauchyGlobalCoMovingUx p u₀ c t b -
            w a *
              chiOneEntropyMultiplier
                (wholeLineCauchyGlobalCoMovingU p u₀ c t a) *
              wholeLineCauchyGlobalCoMovingUx p u₀ c t a) +
          c *
            (w b *
                chiOneRelativeEntropy
                  (wholeLineCauchyGlobalCoMovingU p u₀ c t b) -
              w a *
                chiOneRelativeEntropy
                  (wholeLineCauchyGlobalCoMovingU p u₀ c t a)) -
          p.χ *
            (w b *
                (wholeLineCauchyGlobalCoMovingU p u₀ c t b - 1) *
                wholeLineCauchyGlobalCoMovingRx p u₀ c t b -
              w a *
                (wholeLineCauchyGlobalCoMovingU p u₀ c t a - 1) *
                wholeLineCauchyGlobalCoMovingRx p u₀ c t a)) := by
  let d := wholeLineCauchyGlobalU_chiOneWeightedEntropySlice
    p u₀ hregime hu₀ hleft hp a b c ell w w' t ht
      hw_pos hw_deriv hw'_cont hw_slow hab hell
  exact d.weighted_sharp_entropy_production_le hchi

#print axioms wholeLineCauchyGlobalU_weighted_sharp_dissipation

end ShenWork.Paper1
