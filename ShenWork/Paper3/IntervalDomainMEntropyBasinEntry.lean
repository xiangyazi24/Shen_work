import ShenWork.Paper3.IntervalDomainMEntropyStrongDissipation
import ShenWork.Paper3.IntervalDomainEntropyStrong1Dynamics
import ShenWork.Paper3.IntervalDomainGlobalTailHolderM
import ShenWork.Paper3.IntervalDomainThetaMomentUniform
import ShenWork.Paper3.IntervalDomainTailReactionCoercivity

/-!
# Basin entry from general-`m` entropy dissipation on the faithful equation

The general-`m` entropy functional of every positive bounded global orbit of
the faithful `u^m`-flux equation decays with dissipation controlled by the
`θ = α` moment (Files `IntervalDomainMEntropySlopeIdentity` /
`IntervalDomainMEntropyStrongDissipation`).  A short real-analysis lemma then
produces arbitrarily late slices with arbitrarily small theta dissipation.

Those slices are converted into sup-norm basin entry by an Arzelà–Ascoli
argument: along any subsequence of late slices the proved general-`m`
Hölder-`1/2` tail compactness (`intervalDomainM_globalBounded_tailSlices_subseq`)
extracts a uniform limit, whose theta dissipation vanishes, forcing the limit
to be the equilibrium; uniform convergence to the constant limit contradicts
a supposed uniform sup-distance from it.  Unlike the legacy `m = 1` route, no
positive-time Lipschitz producer is needed.
-/

namespace ShenWork.Paper3

open Filter Topology Set MeasureTheory
open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

/-- The general-`m` entropy functional of every positive bounded global orbit
of the faithful equation has the proved classical derivative at every positive
time. -/
theorem intervalDomainM_strongMEntropy_hasDerivAt
    (p : CM2Params) {uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v) :
    ∀ t, 0 < t →
      HasDerivAt
        (fun s => chemotaxisEntropyFunctional intervalDomain p.m uStar u s)
        (intervalDomain.integral (fun x =>
          chemotaxisEntropyIntegrand p.m uStar (u t x) *
            intervalDomain.timeDeriv u t x)) t := by
  intro t ht
  have hT : 0 < t + 1 := by linarith
  exact intervalDomainM_entropy_hasDerivAt
    (huv.classical (t + 1) hT) heq.u_pos ⟨ht, by linarith⟩

/-- The exact general-`m` entropy derivative controls theta dissipation with
the concrete coefficient along every positive bounded global orbit. -/
theorem intervalDomainM_strongMEntropy_dissipative
    (p : CM2Params) (hm : 1 ≤ p.m)
    {uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hrel : 2 * p.γ ≤ p.α + 1)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v) :
    ∀ t, 0 < t →
      intervalDomain.integral (fun x =>
          chemotaxisEntropyIntegrand p.m uStar (u t x) *
            intervalDomain.timeDeriv u t x) ≤
        -strongMEntropyCoefficient p uStar vStar *
          chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
  intro t ht
  have hT : 0 < t + 1 := by linarith
  exact intervalDomainM_entropySlope_le_strongMCoefficient
    hm (huv.classical (t + 1) hT) ht (by linarith) heq hrel

/-- In the first strict general-`m` formula branch, theta dissipation is
arbitrarily small at arbitrarily late times along every positive bounded
global orbit of the faithful equation. -/
theorem intervalDomainM_strongM_exists_late_thetaDissipation_lt
    (p : CM2Params) (hm : 1 ≤ p.m)
    {uStar vStar : ℝ}
    (hb : 0 < p.b)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hrel : 2 * p.γ ≤ p.α + 1)
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiStrong1Formula p uStar vStar)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    {T q : ℝ} (hT : 0 < T) (hq : 0 < q) :
    ∃ t, T ≤ t ∧
      chemotaxisThetaDissipation intervalDomain uStar p.α (u t) < q := by
  have hc : 0 < strongMEntropyCoefficient p uStar vStar :=
    strongMEntropyCoefficient_pos_of_chi_lt
      p hm hb heq.u_pos heq.v_nonneg hχpos hχ
  exact exists_late_dissipation_lt_of_nonnegative_energy
    (E := fun t => chemotaxisEntropyFunctional intervalDomain p.m uStar u t)
    (D := fun t => chemotaxisThetaDissipation intervalDomain uStar p.α (u t))
    (slope := fun t => intervalDomain.integral (fun x =>
      chemotaxisEntropyIntegrand p.m uStar (u t x) *
        intervalDomain.timeDeriv u t x))
    hc hT hq
    (fun t ht =>
      intervalDomain_chemotaxisEntropyFunctional_nonneg_of_inside_pos
        (by linarith : (1 / 2 : ℝ) ≤ p.m) heq.u_pos
        (fun x hx => huv.pos (t := t) (x := x) ht hx))
    (intervalDomainM_strongMEntropy_hasDerivAt p heq huv)
    (intervalDomainM_strongMEntropy_dissipative p hm heq hrel huv)

/-- Arzelà–Ascoli basin entry for the faithful general-`m` equation: any
positive bounded global orbit whose theta dissipation gets arbitrarily small
arbitrarily late enters every sup neighborhood of the positive equilibrium at
an arbitrarily late classical slice.  The dissipation producer is abstract, so
every strong-logistic branch can consume this theorem. -/
theorem intervalDomainM_exists_late_supClose_of_thetaDissipation
    (p : CM2Params) {uStar : ℝ}
    (huStar : 0 < uStar)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    (hlateTheta : ∀ T q : ℝ, 0 < T → 0 < q → ∃ t, T ≤ t ∧
      chemotaxisThetaDissipation intervalDomain uStar p.α (u t) < q)
    (T : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∃ t, T ≤ t ∧ SupCloseToConstant intervalDomainM (u t) uStar eps := by
  by_contra hnone
  push_neg at hnone
  have hfar : ∀ t, T ≤ t →
      eps ≤ intervalDomainM.supNorm (fun x => u t x - uStar) :=
    fun t ht => not_lt.mp (hnone t ht)
  obtain ⟨M0, hM0⟩ := huv.bounded.eventually_bound
  rcases eventually_atTop.1 hM0 with ⟨Tbdd, hTbdd⟩
  set K : ℝ := max M0 1 with hKdef
  have hlate : ∀ n : ℕ, ∃ t,
      max (max T Tbdd) (max (n : ℝ) 1) ≤ t ∧
      chemotaxisThetaDissipation intervalDomain uStar p.α (u t) <
        1 / ((n : ℝ) + 1) := by
    intro n
    refine hlateTheta _ _ ?_ ?_
    · exact lt_of_lt_of_le one_pos
        ((le_max_right (n : ℝ) 1).trans (le_max_right _ _))
    · positivity
  choose times htimes hsmall using hlate
  have htimesT : ∀ n, T ≤ times n := fun n =>
    ((le_max_left T Tbdd).trans (le_max_left _ _)).trans (htimes n)
  have htimesBdd : ∀ n, Tbdd ≤ times n := fun n =>
    ((le_max_right T Tbdd).trans (le_max_left _ _)).trans (htimes n)
  have htimesPos : ∀ n, 0 < times n := fun n =>
    lt_of_lt_of_le one_pos
      (((le_max_right (n : ℝ) 1).trans (le_max_right _ _)).trans (htimes n))
  have htimes_ge : ∀ n : ℕ, (n : ℝ) ≤ times n := fun n =>
    ((le_max_left (n : ℝ) 1).trans (le_max_right _ _)).trans (htimes n)
  have htend : Tendsto times atTop atTop :=
    tendsto_atTop_mono htimes_ge tendsto_natCast_atTop_atTop
  obtain ⟨g, phi, hphi, hunif⟩ :=
    intervalDomainM_globalBounded_tailSlices_subseq p huv times htend
  have hslice_cont : ∀ n : ℕ, Continuous (u (times n)) := by
    intro n
    have hsol := huv.classical (times n + 1) (by linarith [htimesPos n])
    exact ShenWork.Paper2.IntervalDomainM.solutionSlice_continuous hsol
      ⟨htimesPos n, by linarith⟩
  have hnonneg : ∀ (n : ℕ) (x : intervalDomainPoint), 0 ≤ u (times n) x := by
    intro n x
    have hsol := huv.classical (times n + 1) (by linarith [htimesPos n])
    exact (hsol.u_pos' (htimesPos n) (by linarith)).le
  have habs : ∀ (n : ℕ) (x : intervalDomainPoint), |u (times n) x| ≤ K := by
    intro n x
    have hsol := huv.classical (times n + 1) (by linarith [htimesPos n])
    have hbdd := ShenWork.Paper2.IntervalDomainM.solution_slice_abs_bddAbove
      hsol ⟨htimesPos n, by linarith⟩
    have hle : |u (times n) x| ≤ intervalDomainM.supNorm (u (times n)) :=
      le_csSup hbdd ⟨x, rfl⟩
    exact hle.trans ((hTbdd _ (htimesBdd n)).trans (le_max_left _ _))
  have hg_nonneg : ∀ x, 0 ≤ g x := by
    intro x
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (hunif.tendsto_at x)
      (Filter.Eventually.of_forall fun n => hnonneg (phi n) x)
  have hg_le : ∀ x, g x ≤ K := by
    intro x
    exact le_of_tendsto (hunif.tendsto_at x)
      (Filter.Eventually.of_forall fun n =>
        le_trans (le_abs_self _) (habs (phi n) x))
  have htheta_uniform : TendstoUniformly
      (fun n x =>
        intervalDomainThetaDissipationIntegrand uStar p.α (u (times (phi n)) x))
      (fun x => intervalDomainThetaDissipationIntegrand uStar p.α (g x))
      atTop := by
    apply UniformContinuousOn.comp_tendstoUniformly
      (s := Set.Icc (0 : ℝ) K)
    · intro n x
      exact ⟨hnonneg (phi n) x, (le_abs_self _).trans (habs (phi n) x)⟩
    · exact fun x => ⟨hg_nonneg x, hg_le x⟩
    · exact isCompact_Icc.uniformContinuousOn_of_continuous
        (continuous_intervalDomainThetaDissipationIntegrand p.hα.le).continuousOn
    · exact hunif
  let F : ℕ → C(intervalDomainPoint, ℝ) := fun n =>
    ⟨fun x => intervalDomainThetaDissipationIntegrand uStar p.α
        (u (times (phi n)) x),
      (continuous_intervalDomainThetaDissipationIntegrand p.hα.le).comp
        (hslice_cont (phi n))⟩
  let Fg : C(intervalDomainPoint, ℝ) :=
    ⟨fun x => intervalDomainThetaDissipationIntegrand uStar p.α (g x),
      (continuous_intervalDomainThetaDissipationIntegrand p.hα.le).comp
        g.continuous⟩
  have hint_tendsto : Tendsto
      (fun n => intervalDomain.integral (F n)) atTop
      (𝓝 (intervalDomain.integral Fg)) :=
    intervalDomain_integral_tendsto_of_tendstoUniformly
      (f := F) (g := Fg) (by simpa [F, Fg] using htheta_uniform)
  have hq_zero : Tendsto (fun n : ℕ => 1 / ((phi n : ℝ) + 1)) atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact hbase.comp hphi.tendsto_atTop
  have hFn_le : ∀ n, intervalDomain.integral (F n) ≤ 1 / ((phi n : ℝ) + 1) := by
    intro n
    have hlt := hsmall (phi n)
    have : intervalDomain.integral (F n) <
        1 / ((phi n : ℝ) + 1) := by
      simpa [F, chemotaxisThetaDissipation,
        intervalDomainThetaDissipationIntegrand] using hlt
    exact this.le
  have hint_nonpos : intervalDomain.integral Fg ≤ 0 :=
    le_of_tendsto_of_tendsto hint_tendsto hq_zero
      (Filter.Eventually.of_forall hFn_le)
  have hFg_nonneg : ∀ x, 0 ≤ Fg x := by
    intro x
    exact intervalDomainThetaDissipationIntegrand_nonneg
      huStar.le p.hα.le (hg_nonneg x)
  have hFg_zero : ∀ x, Fg x = 0 := by
    intro x
    apply le_antisymm
    · by_contra hx
      have hxpos : 0 < Fg x := lt_of_not_ge hx
      have hint_pos :=
        intervalDomain_integral_pos_of_continuous_nonneg_of_exists_pos
          Fg hFg_nonneg ⟨x, hxpos⟩
      exact (not_lt_of_ge hint_nonpos) hint_pos
    · exact hFg_nonneg x
  have hg_eq : ∀ x, g x = uStar := by
    intro x
    exact (intervalDomainThetaDissipationIntegrand_eq_zero_iff
      huStar p.hα (hg_nonneg x)).mp (by simpa [Fg] using hFg_zero x)
  have huniform := Metric.tendstoUniformly_iff.mp hunif (eps / 2) (by linarith)
  rcases eventually_atTop.1 huniform with ⟨N, hN⟩
  have hptwise : ∀ x : intervalDomainPoint,
      |u (times (phi N)) x - uStar| ≤ eps / 2 := by
    intro x
    have hclose := hN N le_rfl x
    rw [Real.dist_eq, hg_eq x] at hclose
    rw [abs_sub_comm] at hclose
    exact hclose.le
  have hsup_le : intervalDomain.supNorm
      (fun x => u (times (phi N)) x - uStar) ≤ eps / 2 :=
    intervalDomain_supNorm_le_of_pointwise_abs_le hptwise
  have hfarN := hfar (times (phi N)) (htimesT (phi N))
  have hconv : intervalDomainM.supNorm
      (fun x => u (times (phi N)) x - uStar) =
      intervalDomain.supNorm (fun x => u (times (phi N)) x - uStar) := rfl
  rw [hconv] at hfarN
  linarith

/-- Every positive bounded global orbit of the faithful general-`m` equation
in the first strict formula branch enters every sup neighborhood of the
positive equilibrium at an arbitrarily late classical slice. -/
theorem intervalDomainM_strongM_exists_late_supClose
    (p : CM2Params) (hm : 1 ≤ p.m)
    {uStar vStar : ℝ}
    (hb : 0 < p.b)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hrel : 2 * p.γ ≤ p.α + 1)
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiStrong1Formula p uStar vStar)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    (T : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∃ t, T ≤ t ∧ SupCloseToConstant intervalDomainM (u t) uStar eps :=
  intervalDomainM_exists_late_supClose_of_thetaDissipation
    p heq.u_pos huv
    (fun T' q hT' hq =>
      intervalDomainM_strongM_exists_late_thetaDissipation_lt
        p hm hb heq hrel hχpos hχ huv hT' hq)
    T heps

#print axioms intervalDomainM_strongMEntropy_hasDerivAt
#print axioms intervalDomainM_strongMEntropy_dissipative
#print axioms intervalDomainM_strongM_exists_late_thetaDissipation_lt
#print axioms intervalDomainM_exists_late_supClose_of_thetaDissipation
#print axioms intervalDomainM_strongM_exists_late_supClose

end

end ShenWork.Paper3
