/-
  ShenWork/Paper3/LyapunovFunction.lean

  Lyapunov and entropy estimates for Paper3.
-/
import ShenWork.Paper3.Statements
import ShenWork.PDE.IntervalDomain
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Filter Topology
open Set
open ShenWork.IntervalDomain
open scoped Interval

namespace ShenWork.Paper3

noncomputable section

/-- The scalar integrand in Paper3's entropy density
`h_m(s) = ∫_{u*}^{s} (1 - (u*/tau)^(2m-1)) d tau`. -/
def chemotaxisEntropyIntegrand (m uStar tau : ℝ) : ℝ :=
  1 - (uStar / tau) ^ (2 * m - 1)

/-- Paper3's entropy density for the nonminimal Lyapunov functional:
`h_m(s) = ∫_{u*}^{s} (1 - (u*/tau)^(2m-1)) d tau`.

The paper uses this on positive solution values.  The definition is total
because Lean functions are total, but the mathematically intended region is
`0 < uStar` and `0 < s`. -/
def chemotaxisEntropyDensity (m uStar s : ℝ) : ℝ :=
  ∫ tau in uStar..s, chemotaxisEntropyIntegrand m uStar tau

/-- The entropy integrand vanishes at the equilibrium density. -/
theorem chemotaxisEntropyIntegrand_self
    {m uStar : ℝ} (huStar : uStar ≠ 0) :
    chemotaxisEntropyIntegrand m uStar uStar = 0 := by
  simp [chemotaxisEntropyIntegrand, div_self huStar]

/-- The scalar entropy-density derivative has the Lyapunov sign:
`(s-u*) h_m'(s) ≥ 0` on the positive axis when `2m-1 ≥ 0`. -/
theorem chemotaxisEntropyIntegrand_mul_sub_nonneg
    {m uStar s : ℝ} (hm : (1 / 2 : ℝ) ≤ m)
    (huStar : 0 < uStar) (hs : 0 < s) :
    0 ≤ (s - uStar) * chemotaxisEntropyIntegrand m uStar s := by
  have hq : 0 ≤ 2 * m - 1 := by linarith
  by_cases hle : s ≤ uStar
  · have hratio : 1 ≤ uStar / s := by
      rw [le_div_iff₀ hs]
      simpa using hle
    have hpow :
        (1 : ℝ) ≤ (uStar / s) ^ (2 * m - 1) := by
      simpa using Real.rpow_le_rpow zero_le_one hratio hq
    have hintegrand : chemotaxisEntropyIntegrand m uStar s ≤ 0 := by
      unfold chemotaxisEntropyIntegrand
      exact sub_nonpos.mpr hpow
    exact mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr hle) hintegrand
  · have hlt : uStar < s := lt_of_not_ge hle
    have hratio : uStar / s ≤ 1 := by
      rw [div_le_iff₀ hs]
      simpa using hlt.le
    have hratio_nonneg : 0 ≤ uStar / s := div_nonneg huStar.le hs.le
    have hpow :
        (uStar / s) ^ (2 * m - 1) ≤ (1 : ℝ) := by
      simpa using Real.rpow_le_rpow hratio_nonneg hratio hq
    have hintegrand : 0 ≤ chemotaxisEntropyIntegrand m uStar s := by
      unfold chemotaxisEntropyIntegrand
      exact sub_nonneg.mpr hpow
    exact mul_nonneg (sub_nonneg.mpr hlt.le) hintegrand

/-- The entropy-density derivative is nonnegative to the right of `u*`. -/
theorem chemotaxisEntropyIntegrand_nonneg_of_ge
    {m uStar s : ℝ} (hm : (1 / 2 : ℝ) ≤ m)
    (huStar : 0 < uStar) (hs : 0 < s) (huStar_le : uStar ≤ s) :
    0 ≤ chemotaxisEntropyIntegrand m uStar s := by
  have hq : 0 ≤ 2 * m - 1 := by linarith
  have hratio : uStar / s ≤ 1 := by
    rw [div_le_iff₀ hs]
    simpa using huStar_le
  have hratio_nonneg : 0 ≤ uStar / s := div_nonneg huStar.le hs.le
  have hpow : (uStar / s) ^ (2 * m - 1) ≤ (1 : ℝ) := by
    simpa using Real.rpow_le_rpow hratio_nonneg hratio hq
  unfold chemotaxisEntropyIntegrand
  exact sub_nonneg.mpr hpow

/-- The entropy-density derivative is nonpositive to the left of `u*`. -/
theorem chemotaxisEntropyIntegrand_nonpos_of_le
    {m uStar s : ℝ} (hm : (1 / 2 : ℝ) ≤ m)
    (_huStar : 0 < uStar) (hs : 0 < s) (hs_le : s ≤ uStar) :
    chemotaxisEntropyIntegrand m uStar s ≤ 0 := by
  have hq : 0 ≤ 2 * m - 1 := by linarith
  have hratio : 1 ≤ uStar / s := by
    rw [le_div_iff₀ hs]
    simpa using hs_le
  have hpow : (1 : ℝ) ≤ (uStar / s) ^ (2 * m - 1) := by
    simpa using Real.rpow_le_rpow zero_le_one hratio hq
  unfold chemotaxisEntropyIntegrand
  exact sub_nonpos.mpr hpow

/-- The entropy density is normalized to vanish at the equilibrium density. -/
theorem chemotaxisEntropyDensity_self (m uStar : ℝ) :
    chemotaxisEntropyDensity m uStar uStar = 0 := by
  simp [chemotaxisEntropyDensity]

/-- The scalar entropy density is nonnegative on the positive axis when
`2m-1 ≥ 0`.  This is the one-dimensional Lyapunov positivity statement. -/
theorem chemotaxisEntropyDensity_nonneg
    {m uStar s : ℝ} (hm : (1 / 2 : ℝ) ≤ m)
    (huStar : 0 < uStar) (hs : 0 < s) :
    0 ≤ chemotaxisEntropyDensity m uStar s := by
  by_cases hright : uStar ≤ s
  · unfold chemotaxisEntropyDensity
    exact intervalIntegral.integral_nonneg hright
      (fun tau ht =>
        chemotaxisEntropyIntegrand_nonneg_of_ge hm huStar
          (lt_of_lt_of_le huStar ht.1) ht.1)
  · have hleft : s ≤ uStar := le_of_not_ge hright
    unfold chemotaxisEntropyDensity
    rw [intervalIntegral.integral_symm]
    rw [neg_nonneg]
    rw [← neg_nonneg]
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_nonneg hleft
      (fun tau ht =>
        neg_nonneg.mpr
          (chemotaxisEntropyIntegrand_nonpos_of_le hm huStar
            (lt_of_lt_of_le hs ht.1) ht.2))

/-- Away from `tau = 0`, the Paper3 entropy integrand is continuous. -/
theorem chemotaxisEntropyIntegrand_continuousAt_of_ne
    {m uStar tau : ℝ} (huStar : uStar ≠ 0) (htau : tau ≠ 0) :
    ContinuousAt (chemotaxisEntropyIntegrand m uStar) tau := by
  unfold chemotaxisEntropyIntegrand
  exact continuousAt_const.sub
    ((continuousAt_const.div continuousAt_id htau).rpow_const
      (Or.inl (div_ne_zero huStar htau)))

/-- The Paper3 entropy integrand is locally strongly measurable away from
`tau = 0`. -/
theorem chemotaxisEntropyIntegrand_stronglyMeasurableAtFilter_of_ne
    {m uStar tau : ℝ} (huStar : uStar ≠ 0) (htau : tau ≠ 0) :
    StronglyMeasurableAtFilter
      (chemotaxisEntropyIntegrand m uStar) (𝓝 tau) MeasureTheory.volume := by
  have hcont :
      ContinuousOn (chemotaxisEntropyIntegrand m uStar) ({0}ᶜ : Set ℝ) := by
    intro x hx
    exact (chemotaxisEntropyIntegrand_continuousAt_of_ne
      (m := m) (uStar := uStar) huStar (by simpa using hx)).continuousWithinAt
  exact hcont.stronglyMeasurableAtFilter isOpen_compl_singleton tau (by simpa using htau)

/-- On a positive interval, the Paper3 entropy integrand is interval
integrable. -/
theorem chemotaxisEntropyIntegrand_intervalIntegrable_of_pos
    {m uStar s : ℝ} (huStar : 0 < uStar) (hs : 0 < s) :
    IntervalIntegrable
      (chemotaxisEntropyIntegrand m uStar) MeasureTheory.volume uStar s := by
  refine ContinuousOn.intervalIntegrable ?_
  intro x hx
  have hxne : x ≠ 0 := by
    rw [Set.mem_uIcc] at hx
    rcases hx with hx | hx
    · exact ne_of_gt (lt_of_lt_of_le huStar hx.1)
    · exact ne_of_gt (lt_of_lt_of_le hs hx.1)
  exact (chemotaxisEntropyIntegrand_continuousAt_of_ne
    (m := m) (uStar := uStar) huStar.ne' hxne).continuousWithinAt

/-- Fundamental theorem of calculus for the Paper3 entropy density.  This is
the one-dimensional derivative of `h_m`; it does not use any PDE input. -/
theorem chemotaxisEntropyDensity_hasDerivAt
    {m uStar s : ℝ} (huStar : 0 < uStar) (hs : 0 < s) :
    HasDerivAt
      (fun r => chemotaxisEntropyDensity m uStar r)
      (chemotaxisEntropyIntegrand m uStar s) s := by
  simpa [chemotaxisEntropyDensity] using
    intervalIntegral.integral_hasDerivAt_right
      (chemotaxisEntropyIntegrand_intervalIntegrable_of_pos
        (m := m) huStar hs)
      (chemotaxisEntropyIntegrand_stronglyMeasurableAtFilter_of_ne
        (m := m) huStar.ne' hs.ne')
      (chemotaxisEntropyIntegrand_continuousAt_of_ne
        (m := m) huStar.ne' hs.ne')

/-- Derivative form of the entropy-density FTC formula. -/
theorem deriv_chemotaxisEntropyDensity
    {m uStar s : ℝ} (huStar : 0 < uStar) (hs : 0 < s) :
    deriv (fun r => chemotaxisEntropyDensity m uStar r) s =
      chemotaxisEntropyIntegrand m uStar s :=
  (chemotaxisEntropyDensity_hasDerivAt
    (m := m) (uStar := uStar) (s := s) huStar hs).deriv

/-- The entropy density has zero first derivative at the equilibrium density. -/
theorem chemotaxisEntropyDensity_hasDerivAt_self
    {m uStar : ℝ} (huStar : 0 < uStar) :
    HasDerivAt (fun r => chemotaxisEntropyDensity m uStar r) 0 uStar := by
  simpa [chemotaxisEntropyIntegrand_self huStar.ne'] using
    chemotaxisEntropyDensity_hasDerivAt
      (m := m) (uStar := uStar) (s := uStar) huStar huStar

/-- Chain rule for the scalar entropy density along a positive scalar path.
This discharges the pointwise scalar chain-rule part of the entropy estimate;
the spatial integral/time-interchange step remains a separate analytic input. -/
theorem chemotaxisEntropyDensity_comp_hasDerivAt
    {m uStar : ℝ} {y : ℝ → ℝ} {ySlope t : ℝ}
    (huStar : 0 < uStar) (hy_pos : 0 < y t)
    (hy : HasDerivAt y ySlope t) :
    HasDerivAt
      (fun tau => chemotaxisEntropyDensity m uStar (y tau))
      (chemotaxisEntropyIntegrand m uStar (y t) * ySlope) t :=
  (chemotaxisEntropyDensity_hasDerivAt
    (m := m) (uStar := uStar) (s := y t) huStar hy_pos).comp t hy

/-- The Paper3 entropy functional `F(t)=∫ h_m(u(t,x)) dx`, expressed through
the bounded-domain integral interface already used in Paper2/Paper3. -/
def chemotaxisEntropyFunctional
    (D : BoundedDomainData) (m uStar : ℝ)
    (u : ℝ → D.Point → ℝ) (t : ℝ) : ℝ :=
  D.integral fun x => chemotaxisEntropyDensity m uStar (u t x)

/-- The entropy functional is nonnegative once the domain integral preserves
nonnegative functions.  The scalar positivity is fully proved above; this is
the standard abstract-domain lifting step. -/
theorem chemotaxisEntropyFunctional_nonneg_of_integral_nonneg
    {D : BoundedDomainData} {m uStar : ℝ}
    {u : ℝ → D.Point → ℝ} {t : ℝ}
    (hintegral_nonneg :
      ∀ f : D.Point → ℝ, (∀ x, 0 ≤ f x) → 0 ≤ D.integral f)
    (hm : (1 / 2 : ℝ) ≤ m) (huStar : 0 < uStar)
    (hu_pos : ∀ x, 0 < u t x) :
    0 ≤ chemotaxisEntropyFunctional D m uStar u t := by
  exact hintegral_nonneg _
    (fun x => chemotaxisEntropyDensity_nonneg hm huStar (hu_pos x))

/-- The theta/entropy-production moment appearing in Paper3's stabilization
arguments.  With `theta = p.alpha`, this is the paper's
`∫ (u-u*) (u^alpha-(u*)^alpha)`. -/
def chemotaxisThetaDissipation
    (D : BoundedDomainData) (uStar theta : ℝ)
    (uSlice : D.Point → ℝ) : ℝ :=
  D.integral fun x => (uSlice x - uStar) * (uSlice x ^ theta - uStar ^ theta)

/-- Pointwise algebra behind the theta-dissipation nonnegativity:
`s ↦ s^theta` is monotone on `[0,∞)` when `theta ≥ 0`. -/
theorem thetaDissipationIntegrand_nonneg
    {uStar theta s : ℝ}
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta) (hs : 0 ≤ s) :
    0 ≤ (s - uStar) * (s ^ theta - uStar ^ theta) := by
  by_cases hle : s ≤ uStar
  · have hpow : s ^ theta ≤ uStar ^ theta :=
      Real.rpow_le_rpow hs hle htheta
    exact mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr hle) (sub_nonpos.mpr hpow)
  · have hlt : uStar < s := lt_of_not_ge hle
    have hpow : uStar ^ theta ≤ s ^ theta :=
      Real.rpow_le_rpow huStar hlt.le htheta
    exact mul_nonneg
      (sub_nonneg.mpr hlt.le) (sub_nonneg.mpr hpow)

/-- Theta dissipation is nonnegative once the domain integral preserves
nonnegative functions.

Point 17 status: conditional theorem, state ③.  The algebraic positivity is
proved here; positivity of the abstract `BoundedDomainData.integral` is an
honest domain-interface frontier because the current structure does not expose
measure-theoretic positivity fields. -/
theorem chemotaxisThetaDissipation_nonneg_of_integral_nonneg
    {D : BoundedDomainData} {uStar theta : ℝ} {uSlice : D.Point → ℝ}
    (hintegral_nonneg :
      ∀ f : D.Point → ℝ, (∀ x, 0 ≤ f x) → 0 ≤ D.integral f)
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (huSlice : ∀ x, 0 ≤ uSlice x) :
    0 ≤ chemotaxisThetaDissipation D uStar theta uSlice := by
  exact hintegral_nonneg _
    (fun x => thetaDissipationIntegrand_nonneg huStar htheta (huSlice x))

/-- The Lyapunov theta-dissipation functional is exactly the moment functional
used in the statement layer. -/
theorem thetaMomentConvergesToZero_of_chemotaxisThetaDissipation
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {uStar theta : ℝ}
    (h :
      Tendsto
        (fun t => chemotaxisThetaDissipation D uStar theta (u t))
        atTop (𝓝 0)) :
    ThetaMomentConvergesToZero D u uStar theta := by
  simpa [ThetaMomentConvergesToZero, chemotaxisThetaDissipation] using h

/-- Signal energy for the `w = v-v*` Lyapunov functional from the minimal-model
argument:
`∫ (mu w^2 + |∇w|^2)`.

The abstract domain API only exposes a gradient norm, not a vector gradient or
integration-by-parts theorem, so the actual PDE identity is kept as an explicit
hypothesis in the theorems below. -/
def chemotaxisSignalEnergy
    (D : BoundedDomainData) (mu vStar : ℝ)
    (v : ℝ → D.Point → ℝ) (t : ℝ) : ℝ :=
  D.integral fun x =>
    mu * (v t x - vStar) ^ 2 +
      (D.gradNorm (fun y => v t y - vStar) x) ^ 2

/-- The gradient part of the signal-energy dissipation. -/
def chemotaxisSignalGradientDissipation
    (D : BoundedDomainData) (vStar : ℝ)
    (v : ℝ → D.Point → ℝ) (t : ℝ) : ℝ :=
  D.integral fun x => (D.gradNorm (fun y => v t y - vStar) x) ^ 2

/-- Pointwise nonnegativity of the signal-energy integrand. -/
theorem signalEnergyIntegrand_nonneg
    {mu w grad : ℝ} (hmu : 0 ≤ mu) :
    0 ≤ mu * w ^ 2 + grad ^ 2 := by
  nlinarith [mul_nonneg hmu (sq_nonneg w), sq_nonneg grad]

/-- The signal energy is nonnegative once the domain integral preserves
nonnegative functions.

Point 17 status: conditional theorem, state ③, for the same abstract-domain
reason as `chemotaxisThetaDissipation_nonneg_of_integral_nonneg`. -/
theorem chemotaxisSignalEnergy_nonneg_of_integral_nonneg
    {D : BoundedDomainData} {mu vStar : ℝ}
    {v : ℝ → D.Point → ℝ} {t : ℝ}
    (hintegral_nonneg :
      ∀ f : D.Point → ℝ, (∀ x, 0 ≤ f x) → 0 ≤ D.integral f)
    (hmu : 0 ≤ mu) :
    0 ≤ chemotaxisSignalEnergy D mu vStar v t := by
  exact hintegral_nonneg _ (fun x =>
    signalEnergyIntegrand_nonneg (mu := mu)
      (w := v t x - vStar)
      (grad := D.gradNorm (fun y => v t y - vStar) x) hmu)

/-- Signal-gradient dissipation is nonnegative once the domain integral
preserves nonnegative functions. -/
theorem chemotaxisSignalGradientDissipation_nonneg_of_integral_nonneg
    {D : BoundedDomainData} {vStar : ℝ}
    {v : ℝ → D.Point → ℝ} {t : ℝ}
    (hintegral_nonneg :
      ∀ f : D.Point → ℝ, (∀ x, 0 ≤ f x) → 0 ≤ D.integral f) :
    0 ≤ chemotaxisSignalGradientDissipation D vStar v t := by
  exact hintegral_nonneg _ (fun x =>
    sq_nonneg (D.gradNorm (fun y => v t y - vStar) x))

/-- The concrete unit interval integral preserves nonnegative functions. -/
theorem intervalDomain_integral_nonneg
    (f : intervalDomain.Point → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    0 ≤ intervalDomain.integral f := by
  change 0 ≤ intervalDomainIntegral f
  unfold intervalDomainIntegral
  refine intervalIntegral_nonneg (L := 1) (by norm_num) ?_
  intro x hx
  unfold intervalDomainLift
  simpa [hx] using hf ⟨x, hx⟩

/-- The concrete unit-interval integral only needs nonnegativity on the
interior; endpoint values are ignored by Lebesgue integration. -/
theorem intervalDomain_integral_nonneg_of_inside_nonneg
    (f : intervalDomain.Point → ℝ)
    (hf : ∀ x : intervalDomain.Point, x ∈ intervalDomain.inside → 0 ≤ f x) :
    0 ≤ intervalDomain.integral f := by
  change 0 ≤ intervalDomainIntegral f
  unfold intervalDomainIntegral
  refine intervalIntegral.integral_nonneg_of_ae_restrict
    (a := (0 : ℝ)) (b := 1) (μ := MeasureTheory.volume) (by norm_num) ?_
  rw [← MeasureTheory.restrict_Ioo_eq_restrict_Icc
    (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 1)]
  exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr <|
    Eventually.of_forall fun x hx => by
      have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
      unfold intervalDomainLift
      simpa [hxIcc] using hf ⟨x, hxIcc⟩ hx

/-- Every point of the concrete unit interval is either an interior point or a
boundary point for `intervalDomain`. -/
theorem intervalDomain_mem_inside_or_boundary
    (x : intervalDomain.Point) :
    x ∈ intervalDomain.inside ∨ x ∈ intervalDomain.boundary := by
  rcases x with ⟨x, hx⟩
  rcases hx with ⟨h0, h1⟩
  by_cases hx0 : x = 0
  · right
    change x = 0 ∨ x = 1
    exact Or.inl hx0
  by_cases hx1 : x = 1
  · right
    change x = 0 ∨ x = 1
    exact Or.inr hx1
  · left
    change x ∈ Set.Ioo (0 : ℝ) 1
    have hx_pos : 0 < x := by
      rcases lt_or_eq_of_le h0 with hlt | heq
      · exact hlt
      · exact False.elim (hx0 heq.symm)
    have hx_lt_one : x < 1 := by
      rcases lt_or_eq_of_le h1 with hlt | heq
      · exact hlt
      · exact False.elim (hx1 heq)
    exact ⟨hx_pos, hx_lt_one⟩

/-- `PositiveGlobalBoundedSolution` gives positivity on `inside`; for the
current pointwise interval-integral interface, endpoint positivity is the
remaining explicit boundary frontier. -/
theorem intervalDomain_positiveGlobalBoundedSolution_pos_of_boundary_pos
    {p : CM2Params}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hboundary_pos :
      ∀ t, 0 < t → ∀ x : intervalDomain.Point,
        x ∈ intervalDomain.boundary → 0 < u t x) :
    ∀ t, 0 < t → ∀ x : intervalDomain.Point, 0 < u t x := by
  intro t ht x
  rcases intervalDomain_mem_inside_or_boundary x with hx_inside | hx_boundary
  · exact huv.pos ht hx_inside
  · exact hboundary_pos t ht x hx_boundary

/-- Concrete interval-domain entropy-functional nonnegativity. -/
theorem intervalDomain_chemotaxisEntropyFunctional_nonneg
    {m uStar : ℝ} {u : ℝ → intervalDomain.Point → ℝ} {t : ℝ}
    (hm : (1 / 2 : ℝ) ≤ m) (huStar : 0 < uStar)
    (hu_pos : ∀ x, 0 < u t x) :
    0 ≤ chemotaxisEntropyFunctional intervalDomain m uStar u t :=
  chemotaxisEntropyFunctional_nonneg_of_integral_nonneg
    intervalDomain_integral_nonneg hm huStar hu_pos

/-- Concrete interval-domain entropy-functional nonnegativity from positivity
only on the interior.  Endpoint values are irrelevant to the interval integral. -/
theorem intervalDomain_chemotaxisEntropyFunctional_nonneg_of_inside_pos
    {m uStar : ℝ} {u : ℝ → intervalDomain.Point → ℝ} {t : ℝ}
    (hm : (1 / 2 : ℝ) ≤ m) (huStar : 0 < uStar)
    (hu_pos : ∀ x, x ∈ intervalDomain.inside → 0 < u t x) :
    0 ≤ chemotaxisEntropyFunctional intervalDomain m uStar u t := by
  exact intervalDomain_integral_nonneg_of_inside_nonneg _
    (fun x hx => chemotaxisEntropyDensity_nonneg hm huStar (hu_pos x hx))

/-- Concrete interval-domain entropy-functional nonnegativity discharged from a
positive global bounded solution.  No endpoint positivity hypothesis is needed
because the interval integral ignores endpoints. -/
theorem
    intervalDomain_chemotaxisEntropyFunctional_nonneg_of_positiveGlobalBoundedSolution
    {p : CM2Params} {m uStar t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hm : (1 / 2 : ℝ) ≤ m) (huStar : 0 < uStar)
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (ht : 0 < t) :
    0 ≤ chemotaxisEntropyFunctional intervalDomain m uStar u t :=
  intervalDomain_chemotaxisEntropyFunctional_nonneg_of_inside_pos
    hm huStar (fun x hx => huv.pos (t := t) (x := x) ht hx)

/-- Concrete interval-domain theta dissipation nonnegativity. -/
theorem intervalDomain_chemotaxisThetaDissipation_nonneg
    {uStar theta : ℝ} {uSlice : intervalDomain.Point → ℝ}
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (huSlice : ∀ x, 0 ≤ uSlice x) :
    0 ≤ chemotaxisThetaDissipation intervalDomain uStar theta uSlice :=
  chemotaxisThetaDissipation_nonneg_of_integral_nonneg
    intervalDomain_integral_nonneg huStar htheta huSlice

/-- Concrete interval-domain theta dissipation nonnegativity from
nonnegativity only on the interior. -/
theorem intervalDomain_chemotaxisThetaDissipation_nonneg_of_inside_nonneg
    {uStar theta : ℝ} {uSlice : intervalDomain.Point → ℝ}
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (huSlice : ∀ x, x ∈ intervalDomain.inside → 0 ≤ uSlice x) :
    0 ≤ chemotaxisThetaDissipation intervalDomain uStar theta uSlice := by
  exact intervalDomain_integral_nonneg_of_inside_nonneg _
    (fun x hx => thetaDissipationIntegrand_nonneg huStar htheta (huSlice x hx))

/-- Concrete interval-domain theta-dissipation nonnegativity discharged from a
positive global bounded solution.  Endpoint values are irrelevant here as well. -/
theorem
    intervalDomain_chemotaxisThetaDissipation_nonneg_of_positiveGlobalBoundedSolution
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    {uStar theta t : ℝ}
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (ht : 0 < t) :
    0 ≤ chemotaxisThetaDissipation intervalDomain uStar theta (u t) :=
  intervalDomain_chemotaxisThetaDissipation_nonneg_of_inside_nonneg
    huStar htheta
    (fun x hx => (huv.pos (t := t) (x := x) ht hx).le)

/-- Concrete interval-domain signal-energy nonnegativity. -/
theorem intervalDomain_chemotaxisSignalEnergy_nonneg
    {mu vStar : ℝ} {v : ℝ → intervalDomain.Point → ℝ} {t : ℝ}
    (hmu : 0 ≤ mu) :
    0 ≤ chemotaxisSignalEnergy intervalDomain mu vStar v t :=
  chemotaxisSignalEnergy_nonneg_of_integral_nonneg
    intervalDomain_integral_nonneg hmu

/-- Concrete interval-domain signal-gradient dissipation nonnegativity. -/
theorem intervalDomain_chemotaxisSignalGradientDissipation_nonneg
    {vStar : ℝ} {v : ℝ → intervalDomain.Point → ℝ} {t : ℝ} :
    0 ≤ chemotaxisSignalGradientDissipation intervalDomain vStar v t :=
  chemotaxisSignalGradientDissipation_nonneg_of_integral_nonneg
    intervalDomain_integral_nonneg

/-- If a differentiable energy has nonpositive time derivative on `(0,∞)`,
then it is antitone there. -/
theorem energy_antitoneOn_Ioi_of_hasDerivAt_nonpos
    {E E' : ℝ → ℝ}
    (hderiv : ∀ t, 0 < t → HasDerivAt E (E' t) t)
    (hnonpos : ∀ t, 0 < t → E' t ≤ 0) :
    AntitoneOn E (Ioi (0 : ℝ)) := by
  have hdiff : DifferentiableOn ℝ E (Ioi (0 : ℝ)) := by
    intro t ht
    exact (hderiv t ht).differentiableAt.differentiableWithinAt
  have hcont : ContinuousOn E (Ioi (0 : ℝ)) := hdiff.continuousOn
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) hcont ?_ ?_
  · simpa using hdiff
  · intro t ht
    have ht' : 0 < t := by simpa using ht
    rw [(hderiv t ht').deriv]
    exact hnonpos t ht'

/-- If `E'(t) ≤ -rate E(t)` on `(0,∞)`, then
`exp(rate t) E(t)` is antitone on `(0,∞)`. -/
theorem weighted_energy_antitoneOn_Ioi_of_hasDerivAt_le_neg_mul
    {E E' : ℝ → ℝ} {rate : ℝ}
    (hderiv : ∀ t, 0 < t → HasDerivAt E (E' t) t)
    (hle : ∀ t, 0 < t → E' t ≤ -rate * E t) :
    AntitoneOn (fun t => Real.exp (rate * t) * E t) (Ioi (0 : ℝ)) := by
  apply energy_antitoneOn_Ioi_of_hasDerivAt_nonpos
      (E := fun t => Real.exp (rate * t) * E t)
      (E' := fun t => Real.exp (rate * t) * (rate * E t + E' t))
  · intro t ht
    have hlin : HasDerivAt (fun tau : ℝ => rate * tau) rate t := by
      simpa using (hasDerivAt_id t).const_mul rate
    have hexp : HasDerivAt (fun tau : ℝ => Real.exp (rate * tau))
        (Real.exp (rate * t) * rate) t := hlin.exp
    convert hexp.mul (hderiv t ht) using 1
    ring_nf
  · intro t ht
    have hsum : rate * E t + E' t ≤ 0 := by
      linarith [hle t ht]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hsum

/-- Exponential decay estimate obtained from the differential inequality
`E'(t) ≤ -rate E(t)`. -/
theorem energy_decay_estimate_of_hasDerivAt_le_neg_mul
    {E E' : ℝ → ℝ} {rate : ℝ}
    (hderiv : ∀ t, 0 < t → HasDerivAt E (E' t) t)
    (hle : ∀ t, 0 < t → E' t ≤ -rate * E t) :
    ∀ s t, 0 < s → s ≤ t →
      E t ≤ E s * Real.exp (-rate * (t - s)) := by
  intro s t hs hst
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hweighted :=
    weighted_energy_antitoneOn_Ioi_of_hasDerivAt_le_neg_mul hderiv hle
  have hW :
      Real.exp (rate * t) * E t ≤ Real.exp (rate * s) * E s :=
    hweighted hs ht hst
  have hpos : 0 < Real.exp (rate * t) := Real.exp_pos _
  calc
    E t = (Real.exp (rate * t) * E t) / Real.exp (rate * t) := by
      field_simp [ne_of_gt hpos]
    _ ≤ (Real.exp (rate * s) * E s) / Real.exp (rate * t) :=
      div_le_div_of_nonneg_right hW hpos.le
    _ = E s * Real.exp (-rate * (t - s)) := by
      rw [mul_div_assoc, div_eq_mul_inv, ← Real.exp_neg]
      calc
        Real.exp (rate * s) * (E s * Real.exp (-(rate * t)))
            = E s * (Real.exp (rate * s) * Real.exp (-(rate * t))) := by
              ring_nf
        _ = E s * Real.exp (rate * s + -(rate * t)) := by
              rw [← Real.exp_add]
        _ = E s * Real.exp (-rate * (t - s)) := by
              congr 1
              ring_nf

/-- If a nonnegative energy satisfies `E'(t) ≤ -rate E(t)` with `rate > 0`,
then it tends to zero.  The start time `s` is explicit so this lemma can be used
after a solution becomes regular or persistent only eventually. -/
theorem energy_tendsto_zero_of_hasDerivAt_le_neg_mul
    {E E' : ℝ → ℝ} {rate s : ℝ}
    (hrate : 0 < rate) (hs : 0 < s)
    (hderiv : ∀ t, 0 < t → HasDerivAt E (E' t) t)
    (hle : ∀ t, 0 < t → E' t ≤ -rate * E t)
    (hnonneg : ∀ t, s ≤ t → 0 ≤ E t) :
    Tendsto E atTop (𝓝 0) := by
  have hdecay := energy_decay_estimate_of_hasDerivAt_le_neg_mul hderiv hle
  have hexp0 :
      Tendsto (fun t : ℝ => Real.exp (-rate * (t - s))) atTop (𝓝 0) := by
    have hlinear :
        Tendsto (fun t : ℝ => (-rate) * t + rate * s) atTop atBot := by
      exact tendsto_atBot_add_const_right _ (rate * s)
        (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hrate))
    refine (Real.tendsto_exp_atBot.comp hlinear).congr' ?_
    filter_upwards with t
    apply congrArg Real.exp
    ring
  have hupper0 :
      Tendsto (fun t : ℝ => E s * Real.exp (-rate * (t - s))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hexp0)
  refine squeeze_zero' ?_ ?_ hupper0
  · exact eventually_atTop.mpr ⟨s, fun t ht => hnonneg t ht⟩
  · exact eventually_atTop.mpr
      ⟨s, fun t ht => hdecay s t hs ht⟩

/-- Differential dissipation plus a Poincare-type control implies the weighted
energy is decreasing.

Point 17 status: conditional theorem, state ③.  The unproved analytic inputs are
exactly the hypotheses `hderiv`, `hdiss`, and `hcontrol`: they package the
chain rule, Neumann integration by parts, the chemotaxis term estimate, and the
Poincare control for the particular PDE/domain.  `BoundedDomainData` does not
yet expose enough structure to derive those facts.  Given them, the Lyapunov
decay conclusion is proved here without new axioms or proof holes. -/
theorem energy_weighted_antitoneOn_Ioi_of_dissipation_control
    {E E' G : ℝ → ℝ} {c K : ℝ}
    (hc : 0 < c) (hK : 0 < K)
    (hderiv : ∀ t, 0 < t → HasDerivAt E (E' t) t)
    (hdiss : ∀ t, 0 < t → (1 / 2 : ℝ) * E' t + c * G t ≤ 0)
    (hcontrol : ∀ t, 0 < t → E t ≤ K * G t) :
    AntitoneOn (fun t => Real.exp ((2 * c / K) * t) * E t) (Ioi (0 : ℝ)) := by
  refine weighted_energy_antitoneOn_Ioi_of_hasDerivAt_le_neg_mul hderiv ?_
  intro t ht
  have hd : E' t + 2 * c * G t ≤ 0 := by
    linarith [hdiss t ht]
  have hcoef_nonneg : 0 ≤ 2 * c / K := by positivity
  have hcontrol' :
      (2 * c / K) * E t ≤ (2 * c / K) * (K * G t) :=
    mul_le_mul_of_nonneg_left (hcontrol t ht) hcoef_nonneg
  have hright : (2 * c / K) * (K * G t) = 2 * c * G t := by
    field_simp [ne_of_gt hK]
  have hrateE : (2 * c / K) * E t ≤ 2 * c * G t := by
    simpa [hright] using hcontrol'
  linarith

/-- Exponential energy decay from a differential dissipation inequality and a
Poincare-type control.  This is the abstract core of the Paper3 estimate
`(8.14) -> (8.15)`.

Point 17 status: conditional theorem, state ③, for the same reason as
`energy_weighted_antitoneOn_Ioi_of_dissipation_control`. -/
theorem energy_exponential_decay_of_dissipation_control
    {E E' G : ℝ → ℝ} {c K : ℝ}
    (hc : 0 < c) (hK : 0 < K)
    (hderiv : ∀ t, 0 < t → HasDerivAt E (E' t) t)
    (hdiss : ∀ t, 0 < t → (1 / 2 : ℝ) * E' t + c * G t ≤ 0)
    (hcontrol : ∀ t, 0 < t → E t ≤ K * G t) :
    ∀ s t, 0 < s → s ≤ t →
      E t ≤ E s * Real.exp (-(2 * c / K) * (t - s)) := by
  refine energy_decay_estimate_of_hasDerivAt_le_neg_mul hderiv ?_
  intro t ht
  have hd : E' t + 2 * c * G t ≤ 0 := by
    linarith [hdiss t ht]
  have hcoef_nonneg : 0 ≤ 2 * c / K := by positivity
  have hcontrol' :
      (2 * c / K) * E t ≤ (2 * c / K) * (K * G t) :=
    mul_le_mul_of_nonneg_left (hcontrol t ht) hcoef_nonneg
  have hright : (2 * c / K) * (K * G t) = 2 * c * G t := by
    field_simp [ne_of_gt hK]
  have hrateE : (2 * c / K) * E t ≤ 2 * c * G t := by
    simpa [hright] using hcontrol'
  linarith

/-- The dissipation-control form of the Paper3 Lyapunov estimate implies
decay to zero for nonnegative energies. -/
theorem energy_tendsto_zero_of_dissipation_control
    {E E' G : ℝ → ℝ} {c K s : ℝ}
    (hc : 0 < c) (hK : 0 < K) (hs : 0 < s)
    (hderiv : ∀ t, 0 < t → HasDerivAt E (E' t) t)
    (hdiss : ∀ t, 0 < t → (1 / 2 : ℝ) * E' t + c * G t ≤ 0)
    (hcontrol : ∀ t, 0 < t → E t ≤ K * G t)
    (hnonneg : ∀ t, s ≤ t → 0 ≤ E t) :
    Tendsto E atTop (𝓝 0) := by
  refine energy_tendsto_zero_of_hasDerivAt_le_neg_mul
    (rate := 2 * c / K) (s := s) ?_ hs hderiv ?_ hnonneg
  · positivity
  · intro t ht
    have hd : E' t + 2 * c * G t ≤ 0 := by
      linarith [hdiss t ht]
    have hcoef_nonneg : 0 ≤ 2 * c / K := by positivity
    have hcontrol' :
        (2 * c / K) * E t ≤ (2 * c / K) * (K * G t) :=
      mul_le_mul_of_nonneg_left (hcontrol t ht) hcoef_nonneg
    have hright : (2 * c / K) * (K * G t) = 2 * c * G t := by
      field_simp [ne_of_gt hK]
    have hrateE : (2 * c / K) * E t ≤ 2 * c * G t := by
      simpa [hright] using hcontrol'
    linarith

/-- If a nonnegative production term is eventually bounded by a decaying energy,
then the production term also tends to zero. -/
theorem tendsto_zero_of_eventually_nonneg_le_const_mul
    {E G : ℝ → ℝ} {K : ℝ}
    (hE : Tendsto E atTop (𝓝 0))
    (hG_nonneg : ∀ᶠ t in atTop, 0 ≤ G t)
    (hbound : ∀ᶠ t in atTop, G t ≤ K * E t) :
    Tendsto G atTop (𝓝 0) := by
  have hupper : Tendsto (fun t => K * E t) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hE)
  exact squeeze_zero' hG_nonneg hbound hupper

/-- Theta moment convergence from a decaying Lyapunov energy plus an eventual
comparison of theta production by that energy.

Point 17 status: conditional theorem, state ③.  This proves the post-processing
only; the comparison estimate is the named analytic input `hbound`. -/
theorem thetaMomentConvergesToZero_of_energy_tendsto_zero_and_eventual_bound
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {uStar theta : ℝ} {E : ℝ → ℝ} {K : ℝ}
    (hE : Tendsto E atTop (𝓝 0))
    (hnonneg :
      ∀ᶠ t in atTop,
        0 ≤ chemotaxisThetaDissipation D uStar theta (u t))
    (hbound :
      ∀ᶠ t in atTop,
        chemotaxisThetaDissipation D uStar theta (u t) ≤ K * E t) :
    ThetaMomentConvergesToZero D u uStar theta :=
  thetaMomentConvergesToZero_of_chemotaxisThetaDissipation
    (tendsto_zero_of_eventually_nonneg_le_const_mul hE hnonneg hbound)

/-- Same energy-comparison bridge, with theta-production nonnegativity
discharged from pointwise positivity and positivity of the abstract integral. -/
theorem thetaMomentConvergesToZero_of_energy_tendsto_zero_and_integral_nonneg_bound
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {uStar theta : ℝ} {E : ℝ → ℝ} {K : ℝ}
    (hE : Tendsto E atTop (𝓝 0))
    (hintegral_nonneg :
      ∀ f : D.Point → ℝ, (∀ x, 0 ≤ f x) → 0 ≤ D.integral f)
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (hu_nonneg : ∀ᶠ t in atTop, ∀ x, 0 ≤ u t x)
    (hbound :
      ∀ᶠ t in atTop,
        chemotaxisThetaDissipation D uStar theta (u t) ≤ K * E t) :
    ThetaMomentConvergesToZero D u uStar theta := by
  refine thetaMomentConvergesToZero_of_energy_tendsto_zero_and_eventual_bound
    hE ?_ hbound
  exact hu_nonneg.mono fun t ht =>
    chemotaxisThetaDissipation_nonneg_of_integral_nonneg
      hintegral_nonneg huStar htheta ht

/-- Concrete interval-domain version of the energy-comparison bridge for theta
moment convergence. -/
theorem intervalDomain_thetaMomentConvergesToZero_of_energy_tendsto_zero_and_bound
    {u : ℝ → intervalDomain.Point → ℝ}
    {uStar theta : ℝ} {E : ℝ → ℝ} {K : ℝ}
    (hE : Tendsto E atTop (𝓝 0))
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (hu_nonneg : ∀ᶠ t in atTop, ∀ x, 0 ≤ u t x)
    (hbound :
      ∀ᶠ t in atTop,
        chemotaxisThetaDissipation intervalDomain uStar theta (u t) ≤
          K * E t) :
    ThetaMomentConvergesToZero intervalDomain u uStar theta :=
  thetaMomentConvergesToZero_of_energy_tendsto_zero_and_integral_nonneg_bound
    hE intervalDomain_integral_nonneg huStar htheta hu_nonneg hbound

/-- Concrete interval-domain energy-comparison bridge for theta moment
convergence, requiring eventual nonnegativity only on the interior. -/
theorem intervalDomain_thetaMomentConvergesToZero_of_energy_tendsto_zero_and_inside_bound
    {u : ℝ → intervalDomain.Point → ℝ}
    {uStar theta : ℝ} {E : ℝ → ℝ} {K : ℝ}
    (hE : Tendsto E atTop (𝓝 0))
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (hu_nonneg :
      ∀ᶠ t in atTop,
        ∀ x, x ∈ intervalDomain.inside → 0 ≤ u t x)
    (hbound :
      ∀ᶠ t in atTop,
        chemotaxisThetaDissipation intervalDomain uStar theta (u t) ≤
          K * E t) :
    ThetaMomentConvergesToZero intervalDomain u uStar theta := by
  refine thetaMomentConvergesToZero_of_energy_tendsto_zero_and_eventual_bound
    hE ?_ hbound
  exact hu_nonneg.mono fun t ht =>
    intervalDomain_chemotaxisThetaDissipation_nonneg_of_inside_nonneg
      huStar htheta ht

/-- Concrete interval-domain energy-comparison bridge with theta-production
nonnegativity discharged directly from `PositiveGlobalBoundedSolution`. -/
theorem
    intervalDomain_thetaMomentConvergesToZero_of_energy_bound_positiveGlobalBoundedSolution
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    {uStar theta : ℝ} {E : ℝ → ℝ} {K : ℝ}
    (hE : Tendsto E atTop (𝓝 0))
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hbound :
      ∀ᶠ t in atTop,
        chemotaxisThetaDissipation intervalDomain uStar theta (u t) ≤
          K * E t) :
    ThetaMomentConvergesToZero intervalDomain u uStar theta :=
  intervalDomain_thetaMomentConvergesToZero_of_energy_tendsto_zero_and_inside_bound
    hE huStar htheta
    (eventually_atTop.mpr
      ⟨1, fun t ht x hx => (huv.pos (t := t) (x := x)
        (lt_of_lt_of_le zero_lt_one ht) hx).le⟩)
    hbound

/-- Two-time estimate for theta dissipation from a direct differential decay
inequality, with nonnegativity discharged by the domain integral.

Point 17 status: conditional theorem, state ③.  The only remaining analytic
frontier is the named differential estimate `hderiv`/`hle`; the positivity of
the production integrand and the integral lifting are proved here. -/
theorem thetaDissipation_two_time_bound_of_hasDerivAt_le_neg_mul_and_integral_nonneg
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {uStar theta rate : ℝ} {momentSlope : ℝ → ℝ}
    (hintegral_nonneg :
      ∀ f : D.Point → ℝ, (∀ x, 0 ≤ f x) → 0 ≤ D.integral f)
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (hu_nonneg : ∀ t, 0 < t → ∀ x, 0 ≤ u t x)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisThetaDissipation D uStar theta (u tau))
          (momentSlope t) t)
    (hle :
      ∀ t, 0 < t →
        momentSlope t ≤
          -rate * chemotaxisThetaDissipation D uStar theta (u t)) :
    ∀ s t, 0 < s → s ≤ t →
      0 ≤ chemotaxisThetaDissipation D uStar theta (u t) ∧
        chemotaxisThetaDissipation D uStar theta (u t) ≤
          chemotaxisThetaDissipation D uStar theta (u s) *
            Real.exp (-rate * (t - s)) := by
  intro s t hs hst
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hdecay := energy_decay_estimate_of_hasDerivAt_le_neg_mul hderiv hle
  exact
    ⟨chemotaxisThetaDissipation_nonneg_of_integral_nonneg
        hintegral_nonneg huStar htheta (hu_nonneg t ht),
      hdecay s t hs hst⟩

/-- Concrete unit-interval theta-dissipation two-time estimate. -/
theorem intervalDomain_thetaDissipation_two_time_bound_of_hasDerivAt_le_neg_mul
    {u : ℝ → intervalDomain.Point → ℝ}
    {uStar theta rate : ℝ} {momentSlope : ℝ → ℝ}
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (hu_nonneg : ∀ t, 0 < t → ∀ x, 0 ≤ u t x)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau =>
            chemotaxisThetaDissipation intervalDomain uStar theta (u tau))
          (momentSlope t) t)
    (hle :
      ∀ t, 0 < t →
        momentSlope t ≤
          -rate * chemotaxisThetaDissipation intervalDomain uStar theta (u t)) :
    ∀ s t, 0 < s → s ≤ t →
      0 ≤ chemotaxisThetaDissipation intervalDomain uStar theta (u t) ∧
        chemotaxisThetaDissipation intervalDomain uStar theta (u t) ≤
          chemotaxisThetaDissipation intervalDomain uStar theta (u s) *
            Real.exp (-rate * (t - s)) :=
  thetaDissipation_two_time_bound_of_hasDerivAt_le_neg_mul_and_integral_nonneg
    intervalDomain_integral_nonneg huStar htheta hu_nonneg hderiv hle

/-- Concrete unit-interval theta-dissipation two-time estimate requiring
nonnegativity only on the interior. -/
theorem
    intervalDomain_thetaDissipation_two_time_bound_of_hasDerivAt_le_neg_mul_and_inside_nonneg
    {u : ℝ → intervalDomain.Point → ℝ}
    {uStar theta rate : ℝ} {momentSlope : ℝ → ℝ}
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (hu_nonneg :
      ∀ t, 0 < t → ∀ x, x ∈ intervalDomain.inside → 0 ≤ u t x)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau =>
            chemotaxisThetaDissipation intervalDomain uStar theta (u tau))
          (momentSlope t) t)
    (hle :
      ∀ t, 0 < t →
        momentSlope t ≤
          -rate * chemotaxisThetaDissipation intervalDomain uStar theta (u t)) :
    ∀ s t, 0 < s → s ≤ t →
      0 ≤ chemotaxisThetaDissipation intervalDomain uStar theta (u t) ∧
        chemotaxisThetaDissipation intervalDomain uStar theta (u t) ≤
          chemotaxisThetaDissipation intervalDomain uStar theta (u s) *
            Real.exp (-rate * (t - s)) := by
  intro s t hs hst
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hdecay := energy_decay_estimate_of_hasDerivAt_le_neg_mul hderiv hle
  exact
    ⟨intervalDomain_chemotaxisThetaDissipation_nonneg_of_inside_nonneg
        huStar htheta (hu_nonneg t ht),
      hdecay s t hs hst⟩

/-- Concrete theta-dissipation two-time estimate with nonnegativity discharged
from `PositiveGlobalBoundedSolution` on the interior and an explicit endpoint
positivity frontier. -/
theorem intervalDomain_thetaDissipation_two_time_bound_of_solution_positivity
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    {uStar theta rate : ℝ} {momentSlope : ℝ → ℝ}
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hboundary_pos :
      ∀ t, 0 < t → ∀ x : intervalDomain.Point,
        x ∈ intervalDomain.boundary → 0 < u t x)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau =>
            chemotaxisThetaDissipation intervalDomain uStar theta (u tau))
          (momentSlope t) t)
    (hle :
      ∀ t, 0 < t →
        momentSlope t ≤
          -rate * chemotaxisThetaDissipation intervalDomain uStar theta (u t)) :
    ∀ s t, 0 < s → s ≤ t →
      0 ≤ chemotaxisThetaDissipation intervalDomain uStar theta (u t) ∧
        chemotaxisThetaDissipation intervalDomain uStar theta (u t) ≤
          chemotaxisThetaDissipation intervalDomain uStar theta (u s) *
            Real.exp (-rate * (t - s)) :=
  intervalDomain_thetaDissipation_two_time_bound_of_hasDerivAt_le_neg_mul
    huStar htheta
    (fun t ht x =>
      (intervalDomain_positiveGlobalBoundedSolution_pos_of_boundary_pos
        huv hboundary_pos t ht x).le)
    hderiv hle

/-- Concrete theta-dissipation two-time estimate with nonnegativity discharged
directly from `PositiveGlobalBoundedSolution`; no endpoint positivity hypothesis
is needed. -/
theorem intervalDomain_thetaDissipation_two_time_bound_of_positiveGlobalBoundedSolution
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    {uStar theta rate : ℝ} {momentSlope : ℝ → ℝ}
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau =>
            chemotaxisThetaDissipation intervalDomain uStar theta (u tau))
          (momentSlope t) t)
    (hle :
      ∀ t, 0 < t →
        momentSlope t ≤
          -rate * chemotaxisThetaDissipation intervalDomain uStar theta (u t)) :
    ∀ s t, 0 < s → s ≤ t →
      0 ≤ chemotaxisThetaDissipation intervalDomain uStar theta (u t) ∧
        chemotaxisThetaDissipation intervalDomain uStar theta (u t) ≤
          chemotaxisThetaDissipation intervalDomain uStar theta (u s) *
            Real.exp (-rate * (t - s)) :=
  intervalDomain_thetaDissipation_two_time_bound_of_hasDerivAt_le_neg_mul_and_inside_nonneg
    huStar htheta
    (fun t ht x hx => (huv.pos (t := t) (x := x) ht hx).le)
    hderiv hle

/-- A direct theta-production differential decay estimate makes the weighted
theta production decreasing on `(0,∞)`. -/
theorem thetaDissipation_weighted_antitoneOn_of_hasDerivAt_le_neg_mul
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {uStar theta rate : ℝ} {momentSlope : ℝ → ℝ}
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisThetaDissipation D uStar theta (u tau))
          (momentSlope t) t)
    (hle :
      ∀ t, 0 < t →
        momentSlope t ≤
          -rate * chemotaxisThetaDissipation D uStar theta (u t)) :
    AntitoneOn
      (fun t =>
        Real.exp (rate * t) *
          chemotaxisThetaDissipation D uStar theta (u t))
      (Ioi (0 : ℝ)) :=
  weighted_energy_antitoneOn_Ioi_of_hasDerivAt_le_neg_mul hderiv hle

/-- Concrete interval-domain weighted theta-production monotonicity. -/
theorem intervalDomain_thetaDissipation_weighted_antitoneOn_of_hasDerivAt_le_neg_mul
    {u : ℝ → intervalDomain.Point → ℝ}
    {uStar theta rate : ℝ} {momentSlope : ℝ → ℝ}
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau =>
            chemotaxisThetaDissipation intervalDomain uStar theta (u tau))
          (momentSlope t) t)
    (hle :
      ∀ t, 0 < t →
        momentSlope t ≤
          -rate * chemotaxisThetaDissipation intervalDomain uStar theta (u t)) :
    AntitoneOn
      (fun t =>
        Real.exp (rate * t) *
          chemotaxisThetaDissipation intervalDomain uStar theta (u t))
      (Ioi (0 : ℝ)) :=
  thetaDissipation_weighted_antitoneOn_of_hasDerivAt_le_neg_mul hderiv hle

/-- A direct theta-moment differential decay estimate gives the statement-layer
`ThetaMomentConvergesToZero` conclusion.

Point 17 status: conditional theorem, state ③.  The theorem does not derive the
PDE differential inequality; it packages the exact post-processing from that
analytic estimate to the Paper3 moment-convergence statement. -/
theorem thetaMomentConvergesToZero_of_hasDerivAt_le_neg_mul
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {uStar theta rate s : ℝ} {momentSlope : ℝ → ℝ}
    (hrate : 0 < rate) (hs : 0 < s)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisThetaDissipation D uStar theta (u tau))
          (momentSlope t) t)
    (hle :
      ∀ t, 0 < t →
        momentSlope t ≤
          -rate * chemotaxisThetaDissipation D uStar theta (u t))
    (hnonneg :
      ∀ t, s ≤ t →
        0 ≤ chemotaxisThetaDissipation D uStar theta (u t)) :
    ThetaMomentConvergesToZero D u uStar theta :=
  thetaMomentConvergesToZero_of_chemotaxisThetaDissipation
    (energy_tendsto_zero_of_hasDerivAt_le_neg_mul
      hrate hs hderiv hle hnonneg)

/-- Same theta-moment convergence bridge, with the eventual nonnegativity
condition discharged from pointwise positivity and positivity of the domain
integral.

Point 17 status: conditional theorem, state ③.  The remaining hypotheses are
named frontiers: the PDE differential decay estimate and positivity of the
abstract domain integral. -/
theorem thetaMomentConvergesToZero_of_hasDerivAt_le_neg_mul_and_integral_nonneg
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {uStar theta rate s : ℝ} {momentSlope : ℝ → ℝ}
    (hrate : 0 < rate) (hs : 0 < s)
    (hintegral_nonneg :
      ∀ f : D.Point → ℝ, (∀ x, 0 ≤ f x) → 0 ≤ D.integral f)
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (hu_nonneg : ∀ t, s ≤ t → ∀ x, 0 ≤ u t x)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisThetaDissipation D uStar theta (u tau))
          (momentSlope t) t)
    (hle :
      ∀ t, 0 < t →
        momentSlope t ≤
          -rate * chemotaxisThetaDissipation D uStar theta (u t)) :
    ThetaMomentConvergesToZero D u uStar theta := by
  refine thetaMomentConvergesToZero_of_hasDerivAt_le_neg_mul
    hrate hs hderiv hle ?_
  intro t ht
  exact chemotaxisThetaDissipation_nonneg_of_integral_nonneg
    hintegral_nonneg huStar htheta (hu_nonneg t ht)

/-- Concrete interval-domain theta-moment convergence from a direct differential
decay estimate.  The nonnegativity side condition is discharged by the
unit-interval integral positivity theorem above. -/
theorem intervalDomain_thetaMomentConvergesToZero_of_hasDerivAt_le_neg_mul
    {u : ℝ → intervalDomain.Point → ℝ}
    {uStar theta rate s : ℝ} {momentSlope : ℝ → ℝ}
    (hrate : 0 < rate) (hs : 0 < s)
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (hu_nonneg : ∀ t, s ≤ t → ∀ x, 0 ≤ u t x)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisThetaDissipation intervalDomain uStar theta (u tau))
          (momentSlope t) t)
    (hle :
      ∀ t, 0 < t →
        momentSlope t ≤
          -rate * chemotaxisThetaDissipation intervalDomain uStar theta (u t)) :
    ThetaMomentConvergesToZero intervalDomain u uStar theta :=
  thetaMomentConvergesToZero_of_hasDerivAt_le_neg_mul_and_integral_nonneg
    hrate hs intervalDomain_integral_nonneg huStar htheta hu_nonneg
    hderiv hle

/-- Concrete interval-domain theta-moment convergence from a direct
differential decay estimate, requiring nonnegativity only on the interior. -/
theorem
    intervalDomain_thetaMomentConvergesToZero_of_hasDerivAt_le_neg_mul_and_inside_nonneg
    {u : ℝ → intervalDomain.Point → ℝ}
    {uStar theta rate s : ℝ} {momentSlope : ℝ → ℝ}
    (hrate : 0 < rate) (hs : 0 < s)
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (hu_nonneg :
      ∀ t, s ≤ t → ∀ x, x ∈ intervalDomain.inside → 0 ≤ u t x)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau =>
            chemotaxisThetaDissipation intervalDomain uStar theta (u tau))
          (momentSlope t) t)
    (hle :
      ∀ t, 0 < t →
        momentSlope t ≤
          -rate * chemotaxisThetaDissipation intervalDomain uStar theta (u t)) :
    ThetaMomentConvergesToZero intervalDomain u uStar theta := by
  refine thetaMomentConvergesToZero_of_hasDerivAt_le_neg_mul
    hrate hs hderiv hle ?_
  intro t ht
  exact intervalDomain_chemotaxisThetaDissipation_nonneg_of_inside_nonneg
    huStar htheta (hu_nonneg t ht)

/-- Concrete interval-domain theta-moment convergence with pointwise
nonnegativity discharged from solution positivity plus the explicit endpoint
frontier. -/
theorem
    intervalDomain_thetaMomentConvergesToZero_of_hasDerivAt_le_neg_mul_of_solution_positivity
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    {uStar theta rate s : ℝ} {momentSlope : ℝ → ℝ}
    (hrate : 0 < rate) (hs : 0 < s)
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hboundary_pos :
      ∀ t, 0 < t → ∀ x : intervalDomain.Point,
        x ∈ intervalDomain.boundary → 0 < u t x)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau =>
            chemotaxisThetaDissipation intervalDomain uStar theta (u tau))
          (momentSlope t) t)
    (hle :
      ∀ t, 0 < t →
        momentSlope t ≤
          -rate * chemotaxisThetaDissipation intervalDomain uStar theta (u t)) :
    ThetaMomentConvergesToZero intervalDomain u uStar theta :=
  intervalDomain_thetaMomentConvergesToZero_of_hasDerivAt_le_neg_mul
    hrate hs huStar htheta
    (fun t ht x =>
      (intervalDomain_positiveGlobalBoundedSolution_pos_of_boundary_pos
        huv hboundary_pos t (lt_of_lt_of_le hs ht) x).le)
    hderiv hle

/-- Concrete interval-domain theta-moment convergence with nonnegativity
discharged directly from `PositiveGlobalBoundedSolution`; no endpoint positivity
hypothesis is needed. -/
theorem
    intervalDomain_thetaMomentConvergesToZero_of_derivative_positiveGlobalBoundedSolution
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    {uStar theta rate s : ℝ} {momentSlope : ℝ → ℝ}
    (hrate : 0 < rate) (hs : 0 < s)
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau =>
            chemotaxisThetaDissipation intervalDomain uStar theta (u tau))
          (momentSlope t) t)
    (hle :
      ∀ t, 0 < t →
        momentSlope t ≤
          -rate * chemotaxisThetaDissipation intervalDomain uStar theta (u t)) :
    ThetaMomentConvergesToZero intervalDomain u uStar theta :=
  intervalDomain_thetaMomentConvergesToZero_of_hasDerivAt_le_neg_mul_and_inside_nonneg
    hrate hs huStar htheta
    (fun t ht x hx => (huv.pos (t := t) (x := x) (lt_of_lt_of_le hs ht) hx).le)
    hderiv hle

/-- Full interval-domain theta-production Lyapunov package from a positive
global bounded solution: nonnegativity, exponential two-time decay, and the
statement-layer `ThetaMomentConvergesToZero` conclusion.

Point 17 status: conditional theorem, state ③.  The positivity and endpoint-null
integral side conditions are discharged here.  The remaining named frontier is
the direct PDE differential decay estimate `hderiv`/`hle` for the theta
production functional. -/
theorem intervalDomain_thetaDissipation_lyapunovPackage_of_positiveGlobalBoundedSolution
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    {uStar theta rate s : ℝ} {momentSlope : ℝ → ℝ}
    (hrate : 0 < rate) (hs : 0 < s)
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau =>
            chemotaxisThetaDissipation intervalDomain uStar theta (u tau))
          (momentSlope t) t)
    (hle :
      ∀ t, 0 < t →
        momentSlope t ≤
          -rate * chemotaxisThetaDissipation intervalDomain uStar theta (u t)) :
    (∀ t, 0 < t →
        0 ≤ chemotaxisThetaDissipation intervalDomain uStar theta (u t)) ∧
      (∀ a b, 0 < a → a ≤ b →
        0 ≤ chemotaxisThetaDissipation intervalDomain uStar theta (u b) ∧
          chemotaxisThetaDissipation intervalDomain uStar theta (u b) ≤
            chemotaxisThetaDissipation intervalDomain uStar theta (u a) *
              Real.exp (-rate * (b - a))) ∧
      ThetaMomentConvergesToZero intervalDomain u uStar theta := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact
      intervalDomain_chemotaxisThetaDissipation_nonneg_of_positiveGlobalBoundedSolution
        (t := t) huStar htheta huv ht
  · exact
      intervalDomain_thetaDissipation_two_time_bound_of_positiveGlobalBoundedSolution
        huStar htheta huv hderiv hle
  · exact
      intervalDomain_thetaMomentConvergesToZero_of_derivative_positiveGlobalBoundedSolution
        hrate hs huStar htheta huv hderiv hle

/-- Full interval-domain theta-production Lyapunov package including the
weighted monotonicity form of the dissipation estimate.

Point 17 status: conditional theorem, state ③.  This adds no new analytic
assumption beyond `hderiv`/`hle`; it only exposes the standard weighted-energy
monotonicity consequence alongside nonnegativity, two-time decay, and
`ThetaMomentConvergesToZero`. -/
theorem
    intervalDomain_thetaDissipation_fullLyapunovPackage_of_positiveGlobalBoundedSolution
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    {uStar theta rate s : ℝ} {momentSlope : ℝ → ℝ}
    (hrate : 0 < rate) (hs : 0 < s)
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau =>
            chemotaxisThetaDissipation intervalDomain uStar theta (u tau))
          (momentSlope t) t)
    (hle :
      ∀ t, 0 < t →
        momentSlope t ≤
          -rate * chemotaxisThetaDissipation intervalDomain uStar theta (u t)) :
    (∀ t, 0 < t →
        0 ≤ chemotaxisThetaDissipation intervalDomain uStar theta (u t)) ∧
      AntitoneOn
        (fun t =>
          Real.exp (rate * t) *
            chemotaxisThetaDissipation intervalDomain uStar theta (u t))
        (Ioi (0 : ℝ)) ∧
      (∀ a b, 0 < a → a ≤ b →
        0 ≤ chemotaxisThetaDissipation intervalDomain uStar theta (u b) ∧
          chemotaxisThetaDissipation intervalDomain uStar theta (u b) ≤
            chemotaxisThetaDissipation intervalDomain uStar theta (u a) *
              Real.exp (-rate * (b - a))) ∧
      ThetaMomentConvergesToZero intervalDomain u uStar theta := by
  have hpack :=
    intervalDomain_thetaDissipation_lyapunovPackage_of_positiveGlobalBoundedSolution
      hrate hs huStar htheta huv hderiv hle
  refine ⟨hpack.1, ?_, hpack.2.1, hpack.2.2⟩
  exact
    intervalDomain_thetaDissipation_weighted_antitoneOn_of_hasDerivAt_le_neg_mul
      hderiv hle

/-- Entropy dissipation makes the Paper3 entropy functional decrease.

Point 17 status: conditional theorem, state ③.  The missing upstream analytic
input is the PDE derivation of `hderiv` and `hdiss` from the chemotaxis-logistic
system.  The theorem does not assume the conclusion; it turns the genuine
differential entropy-production estimate into Lyapunov monotonicity. -/
theorem chemotaxisEntropyFunctional_antitoneOn_of_dissipation
    {D : BoundedDomainData} {m uStar theta c : ℝ}
    {u : ℝ → D.Point → ℝ} {entropySlope : ℝ → ℝ}
    (hc : 0 ≤ c)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisEntropyFunctional D m uStar u tau)
          (entropySlope t) t)
    (hdiss :
      ∀ t, 0 < t →
        entropySlope t ≤
          -c * chemotaxisThetaDissipation D uStar theta (u t))
    (hprod_nonneg :
      ∀ t, 0 < t →
        0 ≤ chemotaxisThetaDissipation D uStar theta (u t)) :
    AntitoneOn
      (fun t => chemotaxisEntropyFunctional D m uStar u t)
      (Ioi (0 : ℝ)) := by
  refine energy_antitoneOn_Ioi_of_hasDerivAt_nonpos hderiv ?_
  intro t ht
  have hnonpos :
      -c * chemotaxisThetaDissipation D uStar theta (u t) ≤ 0 := by
    simpa [neg_mul] using
      neg_nonpos.mpr (mul_nonneg hc (hprod_nonneg t ht))
  exact le_trans (hdiss t ht) hnonpos

/-- Entropy monotonicity with the theta-production nonnegativity discharged from
pointwise positivity and positivity of the abstract integral.

Point 17 status: conditional theorem, state ③.  This removes the algebraic
`hprod_nonneg` burden from the caller; the remaining analytic frontier is the
PDE derivation of `hderiv`/`hdiss` and the domain-integral positivity field. -/
theorem chemotaxisEntropyFunctional_antitoneOn_of_dissipation_and_integral_nonneg
    {D : BoundedDomainData} {m uStar theta c : ℝ}
    {u : ℝ → D.Point → ℝ} {entropySlope : ℝ → ℝ}
    (hc : 0 ≤ c)
    (hintegral_nonneg :
      ∀ f : D.Point → ℝ, (∀ x, 0 ≤ f x) → 0 ≤ D.integral f)
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (hu_nonneg : ∀ t, 0 < t → ∀ x, 0 ≤ u t x)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisEntropyFunctional D m uStar u tau)
          (entropySlope t) t)
    (hdiss :
      ∀ t, 0 < t →
        entropySlope t ≤
          -c * chemotaxisThetaDissipation D uStar theta (u t)) :
    AntitoneOn
      (fun t => chemotaxisEntropyFunctional D m uStar u t)
      (Ioi (0 : ℝ)) :=
  chemotaxisEntropyFunctional_antitoneOn_of_dissipation
    hc hderiv hdiss
    (fun t ht =>
      chemotaxisThetaDissipation_nonneg_of_integral_nonneg
        hintegral_nonneg huStar htheta (hu_nonneg t ht))

/-- Concrete interval-domain entropy monotonicity with theta-production
nonnegativity discharged. -/
theorem intervalDomain_chemotaxisEntropyFunctional_antitoneOn_of_dissipation
    {m uStar theta c : ℝ}
    {u : ℝ → intervalDomain.Point → ℝ} {entropySlope : ℝ → ℝ}
    (hc : 0 ≤ c)
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (hu_nonneg : ∀ t, 0 < t → ∀ x, 0 ≤ u t x)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisEntropyFunctional intervalDomain m uStar u tau)
          (entropySlope t) t)
    (hdiss :
      ∀ t, 0 < t →
        entropySlope t ≤
          -c * chemotaxisThetaDissipation intervalDomain uStar theta (u t)) :
    AntitoneOn
      (fun t => chemotaxisEntropyFunctional intervalDomain m uStar u t)
      (Ioi (0 : ℝ)) :=
  chemotaxisEntropyFunctional_antitoneOn_of_dissipation_and_integral_nonneg
    hc intervalDomain_integral_nonneg huStar htheta hu_nonneg hderiv hdiss

/-- Concrete interval-domain entropy monotonicity with theta-production
nonnegativity discharged from interior nonnegativity.  Endpoint values are not
needed for the interval integral. -/
theorem
    intervalDomain_chemotaxisEntropyFunctional_antitoneOn_of_dissipation_and_inside_nonneg
    {m uStar theta c : ℝ}
    {u : ℝ → intervalDomain.Point → ℝ} {entropySlope : ℝ → ℝ}
    (hc : 0 ≤ c)
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (hu_nonneg :
      ∀ t, 0 < t → ∀ x, x ∈ intervalDomain.inside → 0 ≤ u t x)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisEntropyFunctional intervalDomain m uStar u tau)
          (entropySlope t) t)
    (hdiss :
      ∀ t, 0 < t →
        entropySlope t ≤
          -c * chemotaxisThetaDissipation intervalDomain uStar theta (u t)) :
    AntitoneOn
      (fun t => chemotaxisEntropyFunctional intervalDomain m uStar u t)
      (Ioi (0 : ℝ)) :=
  chemotaxisEntropyFunctional_antitoneOn_of_dissipation
    hc hderiv hdiss
    (fun t ht =>
      intervalDomain_chemotaxisThetaDissipation_nonneg_of_inside_nonneg
        huStar htheta (hu_nonneg t ht))

/-- Concrete interval-domain entropy monotonicity with theta-production
nonnegativity discharged directly from `PositiveGlobalBoundedSolution`.

Point 17 status: conditional theorem, state ③.  The solution positivity and
endpoint-null integral side conditions are discharged here.  The remaining
frontier is the PDE entropy-production estimate `hderiv`/`hdiss`. -/
theorem
    intervalDomain_chemotaxisEntropyFunctional_antitoneOn_of_positiveGlobalBoundedSolution
    {p : CM2Params} {m uStar theta c : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ} {entropySlope : ℝ → ℝ}
    (hc : 0 ≤ c)
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisEntropyFunctional intervalDomain m uStar u tau)
          (entropySlope t) t)
    (hdiss :
      ∀ t, 0 < t →
        entropySlope t ≤
          -c * chemotaxisThetaDissipation intervalDomain uStar theta (u t)) :
    AntitoneOn
      (fun t => chemotaxisEntropyFunctional intervalDomain m uStar u t)
      (Ioi (0 : ℝ)) :=
  chemotaxisEntropyFunctional_antitoneOn_of_dissipation
    hc hderiv hdiss
    (fun t ht =>
      intervalDomain_chemotaxisThetaDissipation_nonneg_of_positiveGlobalBoundedSolution
        (t := t) huStar htheta huv ht)

/-- Nonnegative free energy and entropy monotonicity from the conditional
Paper3 entropy-production estimate.

Point 17 status: conditional theorem, state ③.  The positivity of the scalar
entropy density and the domain-integral lifting are proved here.  The remaining
analytic frontier is exactly the named PDE estimate `hderiv`/`hdiss`: deriving
the entropy derivative and dissipation inequality from the chemotaxis-logistic
system. -/
theorem
    chemotaxisEntropyFunctional_nonneg_and_antitoneOn_of_dissipation_and_integral_nonneg
    {D : BoundedDomainData} {m uStar theta c : ℝ}
    {u : ℝ → D.Point → ℝ} {entropySlope : ℝ → ℝ}
    (hc : 0 ≤ c)
    (hintegral_nonneg :
      ∀ f : D.Point → ℝ, (∀ x, 0 ≤ f x) → 0 ≤ D.integral f)
    (hm : (1 / 2 : ℝ) ≤ m) (huStar : 0 < uStar)
    (htheta : 0 ≤ theta)
    (hu_pos : ∀ t, 0 < t → ∀ x, 0 < u t x)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisEntropyFunctional D m uStar u tau)
          (entropySlope t) t)
    (hdiss :
      ∀ t, 0 < t →
        entropySlope t ≤
          -c * chemotaxisThetaDissipation D uStar theta (u t)) :
    (∀ t, 0 < t → 0 ≤ chemotaxisEntropyFunctional D m uStar u t) ∧
      AntitoneOn
        (fun t => chemotaxisEntropyFunctional D m uStar u t)
        (Ioi (0 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    exact chemotaxisEntropyFunctional_nonneg_of_integral_nonneg
      hintegral_nonneg hm huStar (hu_pos t ht)
  · exact chemotaxisEntropyFunctional_antitoneOn_of_dissipation_and_integral_nonneg
      hc hintegral_nonneg huStar.le htheta
      (fun t ht x => (hu_pos t ht x).le) hderiv hdiss

/-- Concrete unit-interval version of the nonnegative decreasing entropy
functional theorem. -/
theorem
    intervalDomain_chemotaxisEntropyFunctional_nonneg_and_antitoneOn_of_dissipation
    {m uStar theta c : ℝ}
    {u : ℝ → intervalDomain.Point → ℝ} {entropySlope : ℝ → ℝ}
    (hc : 0 ≤ c)
    (hm : (1 / 2 : ℝ) ≤ m) (huStar : 0 < uStar)
    (htheta : 0 ≤ theta)
    (hu_pos : ∀ t, 0 < t → ∀ x, 0 < u t x)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisEntropyFunctional intervalDomain m uStar u tau)
          (entropySlope t) t)
    (hdiss :
      ∀ t, 0 < t →
        entropySlope t ≤
          -c * chemotaxisThetaDissipation intervalDomain uStar theta (u t)) :
    (∀ t, 0 < t →
        0 ≤ chemotaxisEntropyFunctional intervalDomain m uStar u t) ∧
      AntitoneOn
        (fun t => chemotaxisEntropyFunctional intervalDomain m uStar u t)
        (Ioi (0 : ℝ)) :=
  chemotaxisEntropyFunctional_nonneg_and_antitoneOn_of_dissipation_and_integral_nonneg
    hc intervalDomain_integral_nonneg hm huStar htheta hu_pos hderiv hdiss

/-- Two-time Lyapunov estimate for the Paper3 entropy functional:
`0 ≤ F(t) ≤ F(s)` whenever `0 < s ≤ t`.

Point 17 status: conditional theorem, state ③.  This is the free-energy
decrease statement after all scalar positivity and integral-positivity
side-conditions have been discharged.  The remaining named frontier is the PDE
entropy-production derivation `hderiv`/`hdiss`. -/
theorem chemotaxisEntropyFunctional_two_time_bound_of_dissipation_and_integral_nonneg
    {D : BoundedDomainData} {m uStar theta c : ℝ}
    {u : ℝ → D.Point → ℝ} {entropySlope : ℝ → ℝ}
    (hc : 0 ≤ c)
    (hintegral_nonneg :
      ∀ f : D.Point → ℝ, (∀ x, 0 ≤ f x) → 0 ≤ D.integral f)
    (hm : (1 / 2 : ℝ) ≤ m) (huStar : 0 < uStar)
    (htheta : 0 ≤ theta)
    (hu_pos : ∀ t, 0 < t → ∀ x, 0 < u t x)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisEntropyFunctional D m uStar u tau)
          (entropySlope t) t)
    (hdiss :
      ∀ t, 0 < t →
        entropySlope t ≤
          -c * chemotaxisThetaDissipation D uStar theta (u t)) :
    ∀ s t, 0 < s → s ≤ t →
      0 ≤ chemotaxisEntropyFunctional D m uStar u t ∧
        chemotaxisEntropyFunctional D m uStar u t ≤
          chemotaxisEntropyFunctional D m uStar u s := by
  intro s t hs hst
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have henergy :=
    chemotaxisEntropyFunctional_nonneg_and_antitoneOn_of_dissipation_and_integral_nonneg
      hc hintegral_nonneg hm huStar htheta hu_pos hderiv hdiss
  exact ⟨henergy.1 t ht, henergy.2 hs ht hst⟩

/-- Concrete unit-interval two-time Lyapunov estimate for the Paper3 entropy
functional. -/
theorem intervalDomain_chemotaxisEntropyFunctional_two_time_bound_of_dissipation
    {m uStar theta c : ℝ}
    {u : ℝ → intervalDomain.Point → ℝ} {entropySlope : ℝ → ℝ}
    (hc : 0 ≤ c)
    (hm : (1 / 2 : ℝ) ≤ m) (huStar : 0 < uStar)
    (htheta : 0 ≤ theta)
    (hu_pos : ∀ t, 0 < t → ∀ x, 0 < u t x)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisEntropyFunctional intervalDomain m uStar u tau)
          (entropySlope t) t)
    (hdiss :
      ∀ t, 0 < t →
        entropySlope t ≤
          -c * chemotaxisThetaDissipation intervalDomain uStar theta (u t)) :
    ∀ s t, 0 < s → s ≤ t →
      0 ≤ chemotaxisEntropyFunctional intervalDomain m uStar u t ∧
        chemotaxisEntropyFunctional intervalDomain m uStar u t ≤
          chemotaxisEntropyFunctional intervalDomain m uStar u s :=
  chemotaxisEntropyFunctional_two_time_bound_of_dissipation_and_integral_nonneg
    hc intervalDomain_integral_nonneg hm huStar htheta hu_pos hderiv hdiss

/-- Concrete unit-interval two-time Lyapunov estimate requiring positivity only
on the interior. -/
theorem
    intervalDomain_chemotaxisEntropyFunctional_two_time_bound_of_dissipation_and_inside_pos
    {m uStar theta c : ℝ}
    {u : ℝ → intervalDomain.Point → ℝ} {entropySlope : ℝ → ℝ}
    (hc : 0 ≤ c)
    (hm : (1 / 2 : ℝ) ≤ m) (huStar : 0 < uStar)
    (htheta : 0 ≤ theta)
    (hu_pos :
      ∀ t, 0 < t → ∀ x, x ∈ intervalDomain.inside → 0 < u t x)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisEntropyFunctional intervalDomain m uStar u tau)
          (entropySlope t) t)
    (hdiss :
      ∀ t, 0 < t →
        entropySlope t ≤
          -c * chemotaxisThetaDissipation intervalDomain uStar theta (u t)) :
    ∀ s t, 0 < s → s ≤ t →
      0 ≤ chemotaxisEntropyFunctional intervalDomain m uStar u t ∧
        chemotaxisEntropyFunctional intervalDomain m uStar u t ≤
          chemotaxisEntropyFunctional intervalDomain m uStar u s := by
  intro s t hs hst
  have ht : 0 < t := lt_of_lt_of_le hs hst
  refine ⟨?_, ?_⟩
  · exact intervalDomain_chemotaxisEntropyFunctional_nonneg_of_inside_pos
      hm huStar (hu_pos t ht)
  · exact
      (intervalDomain_chemotaxisEntropyFunctional_antitoneOn_of_dissipation_and_inside_nonneg
        hc huStar.le htheta
        (fun r hr x hx => (hu_pos r hr x hx).le) hderiv hdiss)
        hs ht hst

/-- Interval-domain entropy two-time estimate with positivity discharged from
`PositiveGlobalBoundedSolution` on the interior and an explicit endpoint
positivity frontier.

Point 17 status: conditional theorem, state ③.  The current statement-layer
solution structure gives `u > 0` only on `D.inside`; since
`intervalDomain_integral_nonneg` is pointwise rather than a.e., endpoint
positivity is kept as the named boundary hypothesis `hboundary_pos`. -/
theorem
    intervalDomain_chemotaxisEntropyFunctional_two_time_bound_of_solution_positivity
    {p : CM2Params} {m uStar theta c : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ} {entropySlope : ℝ → ℝ}
    (hc : 0 ≤ c)
    (hm : (1 / 2 : ℝ) ≤ m) (huStar : 0 < uStar)
    (htheta : 0 ≤ theta)
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hboundary_pos :
      ∀ t, 0 < t → ∀ x : intervalDomain.Point,
        x ∈ intervalDomain.boundary → 0 < u t x)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisEntropyFunctional intervalDomain m uStar u tau)
          (entropySlope t) t)
    (hdiss :
      ∀ t, 0 < t →
        entropySlope t ≤
          -c * chemotaxisThetaDissipation intervalDomain uStar theta (u t)) :
    ∀ s t, 0 < s → s ≤ t →
      0 ≤ chemotaxisEntropyFunctional intervalDomain m uStar u t ∧
        chemotaxisEntropyFunctional intervalDomain m uStar u t ≤
          chemotaxisEntropyFunctional intervalDomain m uStar u s :=
  intervalDomain_chemotaxisEntropyFunctional_two_time_bound_of_dissipation
    hc hm huStar htheta
    (intervalDomain_positiveGlobalBoundedSolution_pos_of_boundary_pos
      huv hboundary_pos)
    hderiv hdiss

/-- Interval-domain entropy two-time estimate with positivity discharged
directly from `PositiveGlobalBoundedSolution`.  No endpoint positivity
hypothesis is needed because the interval integral ignores endpoints. -/
theorem
    intervalDomain_chemotaxisEntropyFunctional_two_time_bound_of_positiveGlobalBoundedSolution
    {p : CM2Params} {m uStar theta c : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ} {entropySlope : ℝ → ℝ}
    (hc : 0 ≤ c)
    (hm : (1 / 2 : ℝ) ≤ m) (huStar : 0 < uStar)
    (htheta : 0 ≤ theta)
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisEntropyFunctional intervalDomain m uStar u tau)
          (entropySlope t) t)
    (hdiss :
      ∀ t, 0 < t →
        entropySlope t ≤
          -c * chemotaxisThetaDissipation intervalDomain uStar theta (u t)) :
    ∀ s t, 0 < s → s ≤ t →
      0 ≤ chemotaxisEntropyFunctional intervalDomain m uStar u t ∧
        chemotaxisEntropyFunctional intervalDomain m uStar u t ≤
          chemotaxisEntropyFunctional intervalDomain m uStar u s :=
  intervalDomain_chemotaxisEntropyFunctional_two_time_bound_of_dissipation_and_inside_pos
    hc hm huStar htheta
    (fun t ht x hx => huv.pos (t := t) (x := x) ht hx) hderiv hdiss

/-- Direct free-energy Lyapunov package from a positive global bounded solution:
the entropy functional is nonnegative and antitone on `(0,∞)`.

Point 17 status: conditional theorem, state ③.  Positivity side conditions are
discharged from `PositiveGlobalBoundedSolution` and the endpoint-null
unit-interval integral theorem.  The remaining frontier is still exactly the
PDE entropy-production estimate `hderiv`/`hdiss`. -/
theorem intervalDomain_entropyFunctional_nonneg_antitone_of_positiveGlobalBoundedSolution
    {p : CM2Params} {m uStar theta c : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ} {entropySlope : ℝ → ℝ}
    (hc : 0 ≤ c)
    (hm : (1 / 2 : ℝ) ≤ m) (huStar : 0 < uStar)
    (htheta : 0 ≤ theta)
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisEntropyFunctional intervalDomain m uStar u tau)
          (entropySlope t) t)
    (hdiss :
      ∀ t, 0 < t →
        entropySlope t ≤
          -c * chemotaxisThetaDissipation intervalDomain uStar theta (u t)) :
    (∀ t, 0 < t →
        0 ≤ chemotaxisEntropyFunctional intervalDomain m uStar u t) ∧
      AntitoneOn
        (fun t => chemotaxisEntropyFunctional intervalDomain m uStar u t)
        (Ioi (0 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    exact
      intervalDomain_chemotaxisEntropyFunctional_nonneg_of_positiveGlobalBoundedSolution
        hm huStar huv ht
  · exact
      intervalDomain_chemotaxisEntropyFunctional_antitoneOn_of_positiveGlobalBoundedSolution
        hc huStar.le htheta huv hderiv hdiss

/-- Full interval-domain free-energy Lyapunov package from a positive global
bounded solution: nonnegativity, monotonicity on `(0,∞)`, and the two-time
estimate `0 ≤ F(t) ≤ F(s)` for `0 < s ≤ t`.

Point 17 status: conditional theorem, state ③.  This is the complete
post-processing theorem in this file.  Positivity and endpoint-null integral
side conditions are discharged; the only remaining named frontier is the PDE
entropy-production derivation `hderiv`/`hdiss`. -/
theorem intervalDomain_entropyFunctional_lyapunovPackage_of_positiveGlobalBoundedSolution
    {p : CM2Params} {m uStar theta c : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ} {entropySlope : ℝ → ℝ}
    (hc : 0 ≤ c)
    (hm : (1 / 2 : ℝ) ≤ m) (huStar : 0 < uStar)
    (htheta : 0 ≤ theta)
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisEntropyFunctional intervalDomain m uStar u tau)
          (entropySlope t) t)
    (hdiss :
      ∀ t, 0 < t →
        entropySlope t ≤
          -c * chemotaxisThetaDissipation intervalDomain uStar theta (u t)) :
    (∀ t, 0 < t →
        0 ≤ chemotaxisEntropyFunctional intervalDomain m uStar u t) ∧
      AntitoneOn
        (fun t => chemotaxisEntropyFunctional intervalDomain m uStar u t)
        (Ioi (0 : ℝ)) ∧
      ∀ s t, 0 < s → s ≤ t →
        0 ≤ chemotaxisEntropyFunctional intervalDomain m uStar u t ∧
          chemotaxisEntropyFunctional intervalDomain m uStar u t ≤
            chemotaxisEntropyFunctional intervalDomain m uStar u s := by
  have hmono :=
    intervalDomain_entropyFunctional_nonneg_antitone_of_positiveGlobalBoundedSolution
      hc hm huStar htheta huv hderiv hdiss
  refine ⟨hmono.1, hmono.2, ?_⟩
  exact
    intervalDomain_chemotaxisEntropyFunctional_two_time_bound_of_positiveGlobalBoundedSolution
      hc hm huStar htheta huv hderiv hdiss

/-- Weighted signal-energy Lyapunov monotonicity for the Paper3 minimal-model
functional `∫ (mu (v-v*)^2 + |∇(v-v*)|^2)`.

Point 17 status: conditional theorem, state ③.  The theorem is conditional on
the named assumptions in its signature:
* `hderiv`: differentiability of the signal energy;
* `hdiss`: the integrated PDE identity/estimate corresponding to Paper3 (8.14);
* `hcontrol`: the Poincare control corresponding to the step after (8.14).
These are not derivable yet from `BoundedDomainData`. -/
theorem chemotaxisSignalEnergy_weighted_antitoneOn
    {D : BoundedDomainData} {mu vStar c K : ℝ}
    {v : ℝ → D.Point → ℝ} {energySlope : ℝ → ℝ}
    (hc : 0 < c) (hK : 0 < K)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisSignalEnergy D mu vStar v tau)
          (energySlope t) t)
    (hdiss :
      ∀ t, 0 < t →
        (1 / 2 : ℝ) * energySlope t +
          c * chemotaxisSignalGradientDissipation D vStar v t ≤ 0)
    (hcontrol :
      ∀ t, 0 < t →
        chemotaxisSignalEnergy D mu vStar v t ≤
          K * chemotaxisSignalGradientDissipation D vStar v t) :
    AntitoneOn
      (fun t =>
        Real.exp ((2 * c / K) * t) *
          chemotaxisSignalEnergy D mu vStar v t)
      (Ioi (0 : ℝ)) :=
  energy_weighted_antitoneOn_Ioi_of_dissipation_control
    hc hK hderiv hdiss hcontrol

/-- Signal-energy exponential decay for the Paper3 minimal-model Lyapunov
functional `∫ (mu (v-v*)^2 + |∇(v-v*)|^2)`. -/
theorem chemotaxisSignalEnergy_exponential_decay
    {D : BoundedDomainData} {mu vStar c K : ℝ}
    {v : ℝ → D.Point → ℝ} {energySlope : ℝ → ℝ}
    (hc : 0 < c) (hK : 0 < K)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisSignalEnergy D mu vStar v tau)
          (energySlope t) t)
    (hdiss :
      ∀ t, 0 < t →
        (1 / 2 : ℝ) * energySlope t +
          c * chemotaxisSignalGradientDissipation D vStar v t ≤ 0)
    (hcontrol :
      ∀ t, 0 < t →
        chemotaxisSignalEnergy D mu vStar v t ≤
          K * chemotaxisSignalGradientDissipation D vStar v t) :
    ∀ s t, 0 < s → s ≤ t →
      chemotaxisSignalEnergy D mu vStar v t ≤
        chemotaxisSignalEnergy D mu vStar v s *
          Real.exp (-(2 * c / K) * (t - s)) :=
  energy_exponential_decay_of_dissipation_control hc hK hderiv hdiss hcontrol

/-- Concrete interval-domain weighted Lyapunov monotonicity for signal energy.

Point 17 status: conditional theorem, state ③.  The remaining named frontiers
are the signal-energy derivative identity, PDE dissipation estimate, and
Poincare control packaged as `hderiv`, `hdiss`, and `hcontrol`. -/
theorem intervalDomain_chemotaxisSignalEnergy_weighted_antitoneOn
    {mu vStar c K : ℝ}
    {v : ℝ → intervalDomain.Point → ℝ} {energySlope : ℝ → ℝ}
    (hc : 0 < c) (hK : 0 < K)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisSignalEnergy intervalDomain mu vStar v tau)
          (energySlope t) t)
    (hdiss :
      ∀ t, 0 < t →
        (1 / 2 : ℝ) * energySlope t +
          c * chemotaxisSignalGradientDissipation intervalDomain vStar v t ≤ 0)
    (hcontrol :
      ∀ t, 0 < t →
        chemotaxisSignalEnergy intervalDomain mu vStar v t ≤
          K * chemotaxisSignalGradientDissipation intervalDomain vStar v t) :
    AntitoneOn
      (fun t =>
        Real.exp ((2 * c / K) * t) *
          chemotaxisSignalEnergy intervalDomain mu vStar v t)
      (Ioi (0 : ℝ)) :=
  chemotaxisSignalEnergy_weighted_antitoneOn
    hc hK hderiv hdiss hcontrol

/-- Nonnegative signal energy together with the Paper3 exponential two-time
decay estimate.

Point 17 status: conditional theorem, state ③.  The pointwise positivity and
abstract integral lifting are proved here.  The remaining named frontiers are
the signal-energy derivative identity, PDE dissipation estimate, and Poincare
control packaged as `hderiv`, `hdiss`, and `hcontrol`. -/
theorem chemotaxisSignalEnergy_nonneg_and_exponential_decay
    {D : BoundedDomainData} {mu vStar c K : ℝ}
    {v : ℝ → D.Point → ℝ} {energySlope : ℝ → ℝ}
    (hc : 0 < c) (hK : 0 < K)
    (hintegral_nonneg :
      ∀ f : D.Point → ℝ, (∀ x, 0 ≤ f x) → 0 ≤ D.integral f)
    (hmu : 0 ≤ mu)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisSignalEnergy D mu vStar v tau)
          (energySlope t) t)
    (hdiss :
      ∀ t, 0 < t →
        (1 / 2 : ℝ) * energySlope t +
          c * chemotaxisSignalGradientDissipation D vStar v t ≤ 0)
    (hcontrol :
      ∀ t, 0 < t →
        chemotaxisSignalEnergy D mu vStar v t ≤
          K * chemotaxisSignalGradientDissipation D vStar v t) :
    (∀ t, 0 ≤ chemotaxisSignalEnergy D mu vStar v t) ∧
      ∀ s t, 0 < s → s ≤ t →
        chemotaxisSignalEnergy D mu vStar v t ≤
          chemotaxisSignalEnergy D mu vStar v s *
            Real.exp (-(2 * c / K) * (t - s)) := by
  refine ⟨?_, ?_⟩
  · intro t
    exact chemotaxisSignalEnergy_nonneg_of_integral_nonneg
      hintegral_nonneg hmu
  · exact chemotaxisSignalEnergy_exponential_decay
      hc hK hderiv hdiss hcontrol

/-- Signal-energy convergence to zero from the Paper3 dissipation-control
estimate, with nonnegativity discharged by the domain-integral positivity
frontier. -/
theorem chemotaxisSignalEnergy_tendsto_zero
    {D : BoundedDomainData} {mu vStar c K s : ℝ}
    {v : ℝ → D.Point → ℝ} {energySlope : ℝ → ℝ}
    (hc : 0 < c) (hK : 0 < K) (hs : 0 < s)
    (hintegral_nonneg :
      ∀ f : D.Point → ℝ, (∀ x, 0 ≤ f x) → 0 ≤ D.integral f)
    (hmu : 0 ≤ mu)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisSignalEnergy D mu vStar v tau)
          (energySlope t) t)
    (hdiss :
      ∀ t, 0 < t →
        (1 / 2 : ℝ) * energySlope t +
          c * chemotaxisSignalGradientDissipation D vStar v t ≤ 0)
    (hcontrol :
      ∀ t, 0 < t →
        chemotaxisSignalEnergy D mu vStar v t ≤
          K * chemotaxisSignalGradientDissipation D vStar v t) :
    Tendsto
      (fun t => chemotaxisSignalEnergy D mu vStar v t)
      atTop (𝓝 0) := by
  refine energy_tendsto_zero_of_dissipation_control
    hc hK hs hderiv hdiss hcontrol ?_
  intro t _ht
  exact chemotaxisSignalEnergy_nonneg_of_integral_nonneg
    hintegral_nonneg hmu

/-- Concrete interval-domain signal-energy convergence to zero from the Paper3
dissipation-control estimate. -/
theorem intervalDomain_chemotaxisSignalEnergy_tendsto_zero
    {mu vStar c K s : ℝ}
    {v : ℝ → intervalDomain.Point → ℝ} {energySlope : ℝ → ℝ}
    (hc : 0 < c) (hK : 0 < K) (hs : 0 < s)
    (hmu : 0 ≤ mu)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisSignalEnergy intervalDomain mu vStar v tau)
          (energySlope t) t)
    (hdiss :
      ∀ t, 0 < t →
        (1 / 2 : ℝ) * energySlope t +
          c * chemotaxisSignalGradientDissipation intervalDomain vStar v t ≤ 0)
    (hcontrol :
      ∀ t, 0 < t →
        chemotaxisSignalEnergy intervalDomain mu vStar v t ≤
          K * chemotaxisSignalGradientDissipation intervalDomain vStar v t) :
    Tendsto
      (fun t => chemotaxisSignalEnergy intervalDomain mu vStar v t)
      atTop (𝓝 0) :=
  chemotaxisSignalEnergy_tendsto_zero
    hc hK hs intervalDomain_integral_nonneg hmu hderiv hdiss hcontrol

/-- Concrete interval-domain nonnegative signal energy and exponential two-time
decay estimate. -/
theorem intervalDomain_chemotaxisSignalEnergy_nonneg_and_exponential_decay
    {mu vStar c K : ℝ}
    {v : ℝ → intervalDomain.Point → ℝ} {energySlope : ℝ → ℝ}
    (hc : 0 < c) (hK : 0 < K)
    (hmu : 0 ≤ mu)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisSignalEnergy intervalDomain mu vStar v tau)
          (energySlope t) t)
    (hdiss :
      ∀ t, 0 < t →
        (1 / 2 : ℝ) * energySlope t +
          c * chemotaxisSignalGradientDissipation intervalDomain vStar v t ≤ 0)
    (hcontrol :
      ∀ t, 0 < t →
        chemotaxisSignalEnergy intervalDomain mu vStar v t ≤
          K * chemotaxisSignalGradientDissipation intervalDomain vStar v t) :
    (∀ t, 0 ≤ chemotaxisSignalEnergy intervalDomain mu vStar v t) ∧
      ∀ s t, 0 < s → s ≤ t →
        chemotaxisSignalEnergy intervalDomain mu vStar v t ≤
          chemotaxisSignalEnergy intervalDomain mu vStar v s *
            Real.exp (-(2 * c / K) * (t - s)) :=
  chemotaxisSignalEnergy_nonneg_and_exponential_decay
    hc hK intervalDomain_integral_nonneg hmu hderiv hdiss hcontrol

/-- Full interval-domain signal-energy Lyapunov package: nonnegativity,
weighted monotonicity, exponential two-time decay, and convergence to zero.

Point 17 status: conditional theorem, state ③.  The interval integral
positivity and pointwise square positivity side conditions are discharged here.
The remaining named frontiers are the signal-energy derivative identity,
the PDE dissipation estimate, and the Poincare control packaged as
`hderiv`, `hdiss`, and `hcontrol`. -/
theorem intervalDomain_chemotaxisSignalEnergy_lyapunovPackage
    {mu vStar c K s : ℝ}
    {v : ℝ → intervalDomain.Point → ℝ} {energySlope : ℝ → ℝ}
    (hc : 0 < c) (hK : 0 < K) (hs : 0 < s)
    (hmu : 0 ≤ mu)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisSignalEnergy intervalDomain mu vStar v tau)
          (energySlope t) t)
    (hdiss :
      ∀ t, 0 < t →
        (1 / 2 : ℝ) * energySlope t +
          c * chemotaxisSignalGradientDissipation intervalDomain vStar v t ≤ 0)
    (hcontrol :
      ∀ t, 0 < t →
        chemotaxisSignalEnergy intervalDomain mu vStar v t ≤
          K * chemotaxisSignalGradientDissipation intervalDomain vStar v t) :
    (∀ t, 0 ≤ chemotaxisSignalEnergy intervalDomain mu vStar v t) ∧
      AntitoneOn
        (fun t =>
          Real.exp ((2 * c / K) * t) *
            chemotaxisSignalEnergy intervalDomain mu vStar v t)
        (Ioi (0 : ℝ)) ∧
      (∀ a b, 0 < a → a ≤ b →
        chemotaxisSignalEnergy intervalDomain mu vStar v b ≤
          chemotaxisSignalEnergy intervalDomain mu vStar v a *
            Real.exp (-(2 * c / K) * (b - a))) ∧
      Tendsto
        (fun t => chemotaxisSignalEnergy intervalDomain mu vStar v t)
        atTop (𝓝 0) := by
  have hnonneg_decay :=
    intervalDomain_chemotaxisSignalEnergy_nonneg_and_exponential_decay
      hc hK hmu hderiv hdiss hcontrol
  refine ⟨hnonneg_decay.1, ?_, hnonneg_decay.2, ?_⟩
  · exact intervalDomain_chemotaxisSignalEnergy_weighted_antitoneOn
      hc hK hderiv hdiss hcontrol
  · exact intervalDomain_chemotaxisSignalEnergy_tendsto_zero
      hc hK hs hmu hderiv hdiss hcontrol

end

end ShenWork.Paper3
