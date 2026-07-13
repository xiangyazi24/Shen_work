/- A stationary Liouville theorem for the positive-attraction left cluster. -/
import ShenWork.Paper1.WavePositiveSelfStepClosedGraph

open Filter Set Topology Real

noncomputable section

namespace ShenWork.Paper1

/-! The positive construction is not spatially monotone.  Its left endpoint is
selected by translating to the left, extracting an entire uniformly-positive
stationary cluster, and applying the following Liouville theorem.  The proof is
the stationary rectangle argument behind Proposition 1.2: approximate global
maxima and minima give two algebraic inequalities, and `2 * chi < 1` collapses
the rectangle to the equilibrium `(1,1)`. -/

/-- A bounded `C²` function has an Omori point above any prescribed reference
value.  Centering the quadratic penalty at the reference point preserves that
value exactly. -/
theorem exists_approx_max_ge_reference_deriv_data
    {f : ℝ → ℝ} {A eta x₁ : ℝ}
    (hf : ContDiff ℝ 2 f) (hA : ∀ x, |f x| ≤ A) (heta : 0 < eta) :
    ∃ x₀,
      f x₁ ≤ f x₀ ∧
      |deriv f x₀| < eta ∧
      deriv (deriv f) x₀ < eta := by
  have hA0 : 0 ≤ A := le_trans (abs_nonneg (f 0)) (hA 0)
  let eps : ℝ :=
    min (eta / 4) (eta ^ 2 / (16 * (A + 1)))
  have hA1 : 0 < A + 1 := by linarith
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  have heps_eta : 2 * eps < eta := by
    have hle : eps ≤ eta / 4 := by
      dsimp [eps]
      exact min_le_left _ _
    linarith
  obtain ⟨x₀, hmax, hvalue⟩ :=
    exists_isMaxOn_sub_mul_sq_center_of_bounded
      (f := f) (A := A) (eps := eps) (a := x₁) (x₁ := x₁)
      hf.continuous hA heps
  have hvalue_ge : f x₁ ≤ f x₀ := by
    have hsquare : 0 ≤ eps * (x₀ - x₁) ^ 2 :=
      mul_nonneg heps.le (sq_nonneg _)
    simpa only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
      sub_zero] using hvalue.trans (sub_le_self _ hsquare)
  have hlocal : IsLocalMax (fun x => f x - eps * (x - x₁) ^ 2) x₀ :=
    hmax.isLocalMax Filter.univ_mem
  have hpen : HasDerivAt (fun x : ℝ => eps * (x - x₁) ^ 2)
      (2 * eps * (x₀ - x₁)) x₀ := by
    convert (((hasDerivAt_id x₀).sub_const x₁).pow 2).const_mul eps using 1
    simp only [id_eq]
    ring
  have hfirst : deriv f x₀ = 2 * eps * (x₀ - x₁) := by
    have hzero : deriv (fun x => f x - eps * (x - x₁) ^ 2) x₀ = 0 :=
      hlocal.deriv_eq_zero
    have heq : deriv (fun x => f x - eps * (x - x₁) ^ 2) x₀ =
        deriv f x₀ - 2 * eps * (x₀ - x₁) :=
      ((hf.differentiable (by norm_num) x₀).hasDerivAt.sub hpen).deriv
    rw [heq] at hzero
    linarith
  have hdistance : eps * (x₀ - x₁) ^ 2 ≤ 2 * A := by
    have hfx₀ : f x₀ ≤ A := (le_abs_self (f x₀)).trans (hA x₀)
    have hfx₁ : -A ≤ f x₁ := neg_le_of_abs_le (hA x₁)
    simpa only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
      sub_zero] using (show eps * (x₀ - x₁) ^ 2 ≤ f x₀ - f x₁ by
        linarith [hvalue]) |>.trans (by linarith)
  have heps_sq : 8 * A * eps < eta ^ 2 := by
    have hle : eps ≤ eta ^ 2 / (16 * (A + 1)) := by
      dsimp [eps]
      exact min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_left hle (show 0 ≤ 8 * A by positivity)
    have hratio : 8 * A * (eta ^ 2 / (16 * (A + 1))) < eta ^ 2 := by
      have heta2 : 0 < eta ^ 2 := sq_pos_of_pos heta
      have hfrac : 8 * A / (16 * (A + 1)) < 1 := by
        rw [div_lt_one (by positivity)]
        nlinarith
      calc
        8 * A * (eta ^ 2 / (16 * (A + 1))) =
            eta ^ 2 * (8 * A / (16 * (A + 1))) := by
              field_simp [ne_of_gt hA1]
              <;> ring
        _ < eta ^ 2 * 1 := mul_lt_mul_of_pos_left hfrac heta2
        _ = eta ^ 2 := mul_one _
    exact lt_of_le_of_lt (by simpa [mul_assoc] using hmul) hratio
  have hderiv_sq : (deriv f x₀) ^ 2 < eta ^ 2 := by
    rw [hfirst]
    calc
      (2 * eps * (x₀ - x₁)) ^ 2 =
          4 * eps * (eps * (x₀ - x₁) ^ 2) := by ring
      _ ≤ 4 * eps * (2 * A) :=
        mul_le_mul_of_nonneg_left hdistance (by positivity)
      _ = 8 * A * eps := by ring
      _ < eta ^ 2 := heps_sq
  have hderiv : |deriv f x₀| < eta := by
    rw [← sq_lt_sq₀ (abs_nonneg (deriv f x₀)) heta.le, sq_abs]
    exact hderiv_sq
  have hpenC2 : ContDiff ℝ 2 (fun x : ℝ => eps * (x - x₁) ^ 2) := by
    fun_prop
  have hsecond_raw :
      iteratedDeriv 2 (fun x => f x - eps * (x - x₁) ^ 2) x₀ ≤ 0 :=
    iteratedDeriv2_nonpos_of_isLocalMax hlocal
      (hf.continuous.continuousAt.sub hpenC2.continuous.continuousAt)
  have hlin :
      iteratedDeriv 2 (fun x => f x - eps * (x - x₁) ^ 2) x₀ =
        iteratedDeriv 2 f x₀ -
          iteratedDeriv 2 (fun x : ℝ => eps * (x - x₁) ^ 2) x₀ :=
    iteratedDeriv_fun_sub hf.contDiffAt hpenC2.contDiffAt
  have hpen2 :
      iteratedDeriv 2 (fun x : ℝ => eps * (x - x₁) ^ 2) x₀ = 2 * eps := by
    have hpenderiv : deriv (fun x : ℝ => eps * (x - x₁) ^ 2) =
        fun x => 2 * eps * (x - x₁) := by
      funext x
      convert ((((hasDerivAt_id x).sub_const x₁).pow 2).const_mul eps).deriv using 1 <;>
        simp only [id_eq] <;> ring
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_one, hpenderiv]
    have hd : HasDerivAt (fun x : ℝ => 2 * eps * (x - x₁)) (2 * eps) x₀ := by
      simpa using (((hasDerivAt_id x₀).sub_const x₁).const_mul (2 * eps))
    exact hd.deriv
  have hf2 : iteratedDeriv 2 f x₀ = deriv (deriv f) x₀ := by
    simp [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [hlin, hpen2, hf2] at hsecond_raw
  exact ⟨x₀, hvalue_ge, hderiv, by linarith⟩

/-- The whole-line elliptic Green field lies between the powers of any global
lower and upper bounds for its source profile. -/
theorem frozenElliptic_between_global_rpow
    (p : CMParams) {u : ℝ → ℝ} {a b : ℝ}
    (hu : IsCUnifBdd u) (ha : 0 ≤ a)
    (hab : ∀ x, a ≤ u x ∧ u x ≤ b) (x : ℝ) :
    a ^ p.γ ≤ frozenElliptic p u x ∧ frozenElliptic p u x ≤ b ^ p.γ := by
  have hb : 0 ≤ b := le_trans ha (hab 0).1 |>.trans (hab 0).2
  have huγ : IsCUnifBdd (fun y => (u y) ^ p.γ) :=
    rpow_cunif_bdd_of_nonneg p hu (fun y => le_trans ha (hab y).1)
  have haC : IsCUnifBdd (fun _ : ℝ => a ^ p.γ) :=
    ⟨continuous_const, ⟨|a ^ p.γ|, fun _ => le_rfl⟩⟩
  have hbC : IsCUnifBdd (fun _ : ℝ => b ^ p.γ) :=
    ⟨continuous_const, ⟨|b ^ p.γ|, fun _ => le_rfl⟩⟩
  have hγ0 : 0 ≤ p.γ := le_trans zero_le_one p.hγ
  have hlo : Psi (fun _ : ℝ => a ^ p.γ) 1 1 x ≤
      Psi (fun y => (u y) ^ p.γ) 1 1 x :=
    Psi_sub_le one_pos one_pos
      (fun y => Real.rpow_le_rpow ha (hab y).1 hγ0)
      haC.1 huγ.1 haC.2 huγ.2 x
  have hhi : Psi (fun y => (u y) ^ p.γ) 1 1 x ≤
      Psi (fun _ : ℝ => b ^ p.γ) 1 1 x :=
    Psi_sub_le one_pos one_pos
      (fun y => Real.rpow_le_rpow (le_trans ha (hab y).1) (hab y).2 hγ0)
      huγ.1 hbC.1 huγ.2 hbC.2 x
  simpa [frozenElliptic, Psi_const (Real.rpow_nonneg ha p.γ) x,
    Psi_const (Real.rpow_nonneg hb p.γ) x] using And.intro hlo hhi

/-- Positive stationary rectangle Liouville theorem.  Spatial monotonicity is
not assumed. -/
theorem positiveStationary_eq_one_of_uniformlyPositive
    (p : CMParams) {c M d : ℝ} {U : ℝ → ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ0 : 0 ≤ p.χ) (hχhalf : p.χ < 1 / 2)
    (hM : 0 < M) (hd : 0 < d)
    (hU : IsCUnifBdd U) (hU0 : ∀ x, 0 ≤ U x)
    (hUM : ∀ x, U x ≤ M) (hlower : ∀ x, d ≤ U x)
    (hU2 : ContDiff ℝ 2 U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0) :
    U = fun _ => (1 : ℝ) := by
  let L : ℝ := sSup (Set.range U)
  let N : ℝ := sSup (Set.range fun x => -U x)
  let l : ℝ := -N
  have hUbdd : BddAbove (Set.range U) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hUM x
  have hNbdd : BddAbove (Set.range fun x => -U x) := by
    refine ⟨-d, ?_⟩
    rintro _ ⟨x, rfl⟩
    linarith [hlower x]
  have hUL : ∀ x, U x ≤ L := fun x => by
    simpa [L] using le_csSup hUbdd (Set.mem_range_self x)
  have hlU : ∀ x, l ≤ U x := fun x => by
    have h := le_csSup hNbdd (Set.mem_range_self x)
    dsimp [l, N]
    linarith
  have hdl : d ≤ l := by
    have hN : N ≤ -d := by
      refine csSup_le (Set.range_nonempty _) ?_
      rintro _ ⟨x, rfl⟩
      linarith [hlower x]
    dsimp [l]
    linarith
  have hlL : l ≤ L := (hlU 0).trans (hUL 0)
  have hLM : L ≤ M := by
    refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨x, rfl⟩
    exact hUM x
  have hlpos : 0 < l := lt_of_lt_of_le hd hdl
  have hLpos : 0 < L := lt_of_lt_of_le hlpos hlL
  have hL0 : 0 ≤ L := hLpos.le
  have hl0 : 0 ≤ l := hlpos.le
  have hUabs : ∀ x, |U x| ≤ M := by
    intro x
    rw [abs_of_nonneg (hU0 x)]
    exact hUM x
  let eta : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have heta_pos : ∀ n, 0 < eta n := by
    intro n
    dsimp [eta]
    positivity
  have heta_lim : Tendsto eta atTop (nhds 0) := by
    simpa [eta] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hrefMax : ∀ n, ∃ y, L - eta n < U y := by
    intro n
    obtain ⟨z, hz, hlt⟩ := exists_lt_of_lt_csSup
      (Set.range_nonempty U) (show L - eta n < L by linarith [heta_pos n])
    rcases hz with ⟨y, rfl⟩
    exact ⟨y, hlt⟩
  choose yMax hyMax using hrefMax
  have homax : ∀ n, ∃ x,
      U (yMax n) ≤ U x ∧ |deriv U x| < eta n ∧
        deriv (deriv U) x < eta n := fun n =>
    exists_approx_max_ge_reference_deriv_data
      hU2 hUabs (heta_pos n)
  choose xMax hxMaxVal hxMaxD hxMaxDD using homax
  have hxMax_lo : ∀ n, L - eta n < U (xMax n) := fun n =>
    (hyMax n).trans_le (hxMaxVal n)
  have hUxMax : Tendsto (fun n => U (xMax n)) atTop (nhds L) := by
    simpa using
      (tendsto_const_nhds.sub heta_lim).squeeze tendsto_const_nhds
        (fun n => (hxMax_lo n).le) (fun n => by simpa using hUL (xMax n))
  have hrefMin : ∀ n, ∃ y, N - eta n < -U y := by
    intro n
    obtain ⟨z, hz, hlt⟩ := exists_lt_of_lt_csSup
      (Set.range_nonempty fun x => -U x)
      (show N - eta n < N by linarith [heta_pos n])
    rcases hz with ⟨y, rfl⟩
    exact ⟨y, hlt⟩
  choose yMin hyMin using hrefMin
  have hneg2 : ContDiff ℝ 2 (fun x => -U x) := hU2.neg
  have hnegabs : ∀ x, |(-U x)| ≤ M := by intro x; simpa using hUabs x
  have homin : ∀ n, ∃ x,
      -U (yMin n) ≤ -U x ∧
      |deriv (fun y => -U y) x| < eta n ∧
      deriv (deriv (fun y => -U y)) x < eta n := fun n =>
    exists_approx_max_ge_reference_deriv_data
      hneg2 hnegabs (heta_pos n)
  choose xMin hxMinVal hxMinDneg hxMinDDneg using homin
  have hnegDeriv : deriv (fun y => -U y) = fun y => -deriv U y := by
    funext x
    exact ((hU2.differentiable (by norm_num) x).hasDerivAt.neg).deriv
  have hnegSecond : deriv (deriv (fun y => -U y)) =
      fun y => -deriv (deriv U) y := by
    rw [hnegDeriv]
    have hUdC1 : ContDiff ℝ 1 (deriv U) := by
      have hU2' : ContDiff ℝ ((1 : ℕ∞) + 1) U := by simpa using hU2
      exact (contDiff_succ_iff_deriv.mp hU2').2.2
    funext x
    exact ((hUdC1.differentiable (by norm_num) x).hasDerivAt.neg).deriv
  have hxMinD : ∀ n, |deriv U (xMin n)| < eta n := by
    intro n
    simpa [hnegDeriv] using hxMinDneg n
  have hxMinDD : ∀ n, -eta n < deriv (deriv U) (xMin n) := by
    intro n
    have h := hxMinDDneg n
    simpa [hnegSecond] using (show -eta n < deriv (deriv U) (xMin n) by
      rw [hnegSecond] at h
      linarith)
  have hxMin_hi : ∀ n, U (xMin n) < l + eta n := by
    intro n
    have hnear := hyMin n
    have hval := hxMinVal n
    dsimp [l]
    linarith
  have hUxMin : Tendsto (fun n => U (xMin n)) atTop (nhds l) := by
    simpa using
      tendsto_const_nhds.squeeze (tendsto_const_nhds.add heta_lim)
        (fun n => by simpa using hlU (xMin n)) (fun n => (hxMin_hi n).le)
  have hVbounds : ∀ x,
      l ^ p.γ ≤ frozenElliptic p U x ∧
        frozenElliptic p U x ≤ L ^ p.γ :=
    frozenElliptic_between_global_rpow p hU hl0
      (fun x => ⟨hlU x, hUL x⟩)
  have hVdBound : ∀ x, |deriv (frozenElliptic p U) x| ≤ M ^ p.γ := by
    intro x
    exact (frozenElliptic_deriv_abs_le p hU hU0 x).trans
      ((hVbounds x).2.trans
        (Real.rpow_le_rpow hL0 hLM (le_trans zero_le_one p.hγ)))
  let C : ℝ := |c| + |p.χ| * |p.m| * M ^ (p.m - 1) * M ^ p.γ
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have htransport : ∀ x,
      |c * deriv U x -
          p.χ * p.m * (U x) ^ (p.m - 1) *
            deriv (frozenElliptic p U) x * deriv U x| ≤
        C * |deriv U x| := by
    intro x
    have hm10 : 0 ≤ p.m - 1 := by linarith [p.hm]
    have hpow : (U x) ^ (p.m - 1) ≤ M ^ (p.m - 1) :=
      Real.rpow_le_rpow (hU0 x) (hUM x) hm10
    have hchem :
        |p.χ * p.m * (U x) ^ (p.m - 1) *
            deriv (frozenElliptic p U) x * deriv U x| ≤
          (|p.χ| * |p.m| * M ^ (p.m - 1) * M ^ p.γ) *
            |deriv U x| := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (hU0 x) _)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul
          (mul_le_mul_of_nonneg_left hpow
            (mul_nonneg (abs_nonneg p.χ) (abs_nonneg p.m)))
          (hVdBound x) (abs_nonneg _) (by positivity))
        (abs_nonneg _)
    calc
      |c * deriv U x - p.χ * p.m * (U x) ^ (p.m - 1) *
          deriv (frozenElliptic p U) x * deriv U x|
          ≤ |c * deriv U x| +
              |p.χ * p.m * (U x) ^ (p.m - 1) *
                deriv (frozenElliptic p U) x * deriv U x| :=
            by
              simpa only [abs_neg] using
                (abs_add_le (c * deriv U x)
                  (-(p.χ * p.m * (U x) ^ (p.m - 1) *
                    deriv (frozenElliptic p U) x * deriv U x)))
      _ ≤ |c| * |deriv U x| +
          (|p.χ| * |p.m| * M ^ (p.m - 1) * M ^ p.γ) *
            |deriv U x| := by
        rw [abs_mul]
        exact add_le_add le_rfl hchem
      _ = C * |deriv U x| := by dsimp [C]; ring
  have hpaper : ∀ x, paperWaveOperator p c U U x = 0 := by
    intro x
    rw [paperWaveOperator_eq_frozenWaveOperator_at_fixed_point p x
      hU hU0
      (hU2.differentiable (by norm_num) x)
      (frozenElliptic_deriv_differentiableAt p hU hU0 x)
      ((hU2.differentiable (by norm_num) x).rpow_const (Or.inr p.hm))]
    exact hstat x
  have hiter : ∀ x, iteratedDeriv 2 U x = deriv (deriv U) x := by
    intro x
    simp [iteratedDeriv_succ, iteratedDeriv_zero]
  let Gmax : ℝ → ℝ := fun t =>
    t * (1 - t ^ p.α + p.χ * t ^ (p.m - 1) * (t ^ p.γ - l ^ p.γ))
  let Gmin : ℝ → ℝ := fun t =>
    t * (1 - t ^ p.α + p.χ * t ^ (p.m - 1) * (t ^ p.γ - L ^ p.γ))
  have hGmax : ∀ n, -(1 + C) * eta n ≤ Gmax (U (xMax n)) := by
    intro n
    have hp := hpaper (xMax n)
    unfold paperWaveOperator at hp
    rw [hiter] at hp
    let T := c * deriv U (xMax n) -
      p.χ * p.m * (U (xMax n)) ^ (p.m - 1) *
        deriv (frozenElliptic p U) (xMax n) * deriv U (xMax n)
    have hT : |T| ≤ C * eta n :=
      (htransport (xMax n)).trans
        (mul_le_mul_of_nonneg_left (hxMaxD n).le hC0)
    have hreact :
        U (xMax n) *
          (1 - p.χ * (U (xMax n)) ^ (p.m - 1) *
              frozenElliptic p U (xMax n) -
            ((U (xMax n)) ^ p.α -
              p.χ * (U (xMax n)) ^ (p.m + p.γ - 1))) =
          -deriv (deriv U) (xMax n) - T := by
      dsimp [T]
      linarith
    have hpow :
        (U (xMax n)) ^ (p.m + p.γ - 1) =
          (U (xMax n)) ^ (p.m - 1) * (U (xMax n)) ^ p.γ := by
      rw [← Real.rpow_add (lt_of_lt_of_le hd (hlower _))]
      congr 1
      ring
    have htarget :
        U (xMax n) *
          (1 - p.χ * (U (xMax n)) ^ (p.m - 1) *
              frozenElliptic p U (xMax n) -
            ((U (xMax n)) ^ p.α -
              p.χ * (U (xMax n)) ^ (p.m + p.γ - 1))) ≤
          Gmax (U (xMax n)) := by
      dsimp [Gmax]
      rw [hpow]
      have hv := (hVbounds (xMax n)).1
      have hcoef : 0 ≤ p.χ * (U (xMax n)) ^ (p.m - 1) :=
        mul_nonneg hχ0 (Real.rpow_nonneg (hU0 _) _)
      nlinarith [mul_nonneg (hU0 (xMax n))
        (mul_nonneg hcoef (sub_nonneg.mpr hv))]
    rw [hreact] at htarget
    have hTupper : T ≤ C * eta n := le_of_abs_le hT
    linarith [hxMaxDD n]
  have hGmin : ∀ n, Gmin (U (xMin n)) ≤ (1 + C) * eta n := by
    intro n
    have hp := hpaper (xMin n)
    unfold paperWaveOperator at hp
    rw [hiter] at hp
    let T := c * deriv U (xMin n) -
      p.χ * p.m * (U (xMin n)) ^ (p.m - 1) *
        deriv (frozenElliptic p U) (xMin n) * deriv U (xMin n)
    have hT : |T| ≤ C * eta n :=
      (htransport (xMin n)).trans
        (mul_le_mul_of_nonneg_left (hxMinD n).le hC0)
    have hreact :
        U (xMin n) *
          (1 - p.χ * (U (xMin n)) ^ (p.m - 1) *
              frozenElliptic p U (xMin n) -
            ((U (xMin n)) ^ p.α -
              p.χ * (U (xMin n)) ^ (p.m + p.γ - 1))) =
          -deriv (deriv U) (xMin n) - T := by
      dsimp [T]
      linarith
    have hpow :
        (U (xMin n)) ^ (p.m + p.γ - 1) =
          (U (xMin n)) ^ (p.m - 1) * (U (xMin n)) ^ p.γ := by
      rw [← Real.rpow_add (lt_of_lt_of_le hd (hlower _))]
      congr 1
      ring
    have htarget : Gmin (U (xMin n)) ≤
        U (xMin n) *
          (1 - p.χ * (U (xMin n)) ^ (p.m - 1) *
              frozenElliptic p U (xMin n) -
            ((U (xMin n)) ^ p.α -
              p.χ * (U (xMin n)) ^ (p.m + p.γ - 1))) := by
      dsimp [Gmin]
      rw [hpow]
      have hv := (hVbounds (xMin n)).2
      have hcoef : 0 ≤ p.χ * (U (xMin n)) ^ (p.m - 1) :=
        mul_nonneg hχ0 (Real.rpow_nonneg (hU0 _) _)
      nlinarith [mul_nonneg (hU0 (xMin n))
        (mul_nonneg hcoef (sub_nonneg.mpr hv))]
    rw [hreact] at htarget
    have hThi : -T ≤ C * eta n := (le_abs_self (-T)).trans (by simpa using hT)
    linarith [hxMinDD n]
  have hGmaxLim : Tendsto (fun n => Gmax (U (xMax n))) atTop (nhds (Gmax L)) := by
    apply Tendsto.mul hUxMax
    apply Tendsto.add (Tendsto.sub tendsto_const_nhds
      (hUxMax.rpow_const (Or.inr (le_trans zero_le_one p.hα))))
    apply Tendsto.mul
    · exact Tendsto.mul tendsto_const_nhds
        (hUxMax.rpow_const (Or.inr (by linarith [p.hm] : 0 ≤ p.m - 1)))
    · exact Tendsto.sub
        (hUxMax.rpow_const (Or.inr (le_trans zero_le_one p.hγ)))
        tendsto_const_nhds
  have hGminLim : Tendsto (fun n => Gmin (U (xMin n))) atTop (nhds (Gmin l)) := by
    apply Tendsto.mul hUxMin
    apply Tendsto.add (Tendsto.sub tendsto_const_nhds
      (hUxMin.rpow_const (Or.inr (le_trans zero_le_one p.hα))))
    apply Tendsto.mul
    · exact Tendsto.mul tendsto_const_nhds
        (hUxMin.rpow_const (Or.inr (by linarith [p.hm] : 0 ≤ p.m - 1)))
    · exact Tendsto.sub
        (hUxMin.rpow_const (Or.inr (le_trans zero_le_one p.hγ)))
        tendsto_const_nhds
  have hzeroErr : Tendsto (fun n => (1 + C) * eta n) atTop (nhds 0) := by
    simpa using heta_lim.const_mul (1 + C)
  have hmaxAlg : 0 ≤
      1 - L ^ p.α + p.χ * L ^ (p.m - 1) * (L ^ p.γ - l ^ p.γ) := by
    have hzeroNeg : Tendsto (fun n => -(1 + C) * eta n) atTop (nhds 0) := by
      simpa only [neg_mul, neg_zero] using hzeroErr.neg
    have hnonnegG : 0 ≤ Gmax L :=
      le_of_tendsto_of_tendsto hzeroNeg hGmaxLim
        (Eventually.of_forall hGmax)
    dsimp [Gmax] at hnonnegG
    exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hnonnegG) hLpos
  have hminAlg :
      1 - l ^ p.α + p.χ * l ^ (p.m - 1) * (l ^ p.γ - L ^ p.γ) ≤ 0 := by
    have hnonposG : Gmin l ≤ 0 :=
      le_of_tendsto_of_tendsto hGminLim hzeroErr
        (Eventually.of_forall hGmin)
    dsimp [Gmin] at hnonposG
    exact nonpos_of_mul_nonpos_left (by simpa [mul_comm] using hnonposG) hlpos
  have hm10 : 0 ≤ p.m - 1 := by linarith [p.hm]
  have hγ0 : 0 ≤ p.γ := le_trans zero_le_one p.hγ
  have hα0 : 0 ≤ p.α := le_trans zero_le_one p.hα
  have hlmPow : l ^ (p.m - 1) ≤ L ^ (p.m - 1) :=
    Real.rpow_le_rpow hl0 hlL hm10
  have hlγ : l ^ p.γ ≤ L ^ p.γ := Real.rpow_le_rpow hl0 hlL hγ0
  have hlα : l ^ p.α ≤ L ^ p.α := Real.rpow_le_rpow hl0 hlL hα0
  let Dα : ℝ := L ^ p.α - l ^ p.α
  let Dγ : ℝ := L ^ p.γ - l ^ p.γ
  have hDα0 : 0 ≤ Dα := sub_nonneg.mpr hlα
  have hDγ0 : 0 ≤ Dγ := sub_nonneg.mpr hlγ
  have hrect : Dα ≤ p.χ *
      (L ^ (p.m - 1) + l ^ (p.m - 1)) * Dγ := by
    dsimp [Dα, Dγ]
    linarith
  have hpowSplitL : L ^ p.α = L ^ (p.m - 1) * L ^ p.γ := by
    rw [hα, ← Real.rpow_add hLpos]
    congr 1
    ring
  have hpowSplitl : l ^ p.α = l ^ (p.m - 1) * l ^ p.γ := by
    rw [hα, ← Real.rpow_add hlpos]
    congr 1
    ring
  have hLDγ : L ^ (p.m - 1) * Dγ ≤ Dα := by
    dsimp [Dα, Dγ]
    rw [hpowSplitL, hpowSplitl]
    nlinarith [mul_le_mul_of_nonneg_right hlmPow
      (Real.rpow_nonneg hl0 p.γ)]
  have hlDγ : l ^ (p.m - 1) * Dγ ≤ Dα := by
    calc
      l ^ (p.m - 1) * Dγ ≤ L ^ (p.m - 1) * Dγ :=
        mul_le_mul_of_nonneg_right hlmPow hDγ0
      _ ≤ Dα := hLDγ
  have htwo : p.χ *
      (L ^ (p.m - 1) + l ^ (p.m - 1)) * Dγ ≤ 2 * p.χ * Dα := by
    have hsum :
        (L ^ (p.m - 1) + l ^ (p.m - 1)) * Dγ ≤ 2 * Dα := by
      rw [add_mul]
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hsum hχ0]
  have hDzero : Dα = 0 := by
    by_contra hne
    have hDpos : 0 < Dα := lt_of_le_of_ne hDα0 (Ne.symm hne)
    have hstrict : 2 * p.χ * Dα < Dα := by
      have : 2 * p.χ < 1 := by linarith
      nlinarith
    linarith [hrect, htwo]
  have hlEqL : l = L := by
    have hpEq : l ^ p.α = L ^ p.α := by dsimp [Dα] at hDzero; linarith
    exact (Real.rpow_left_inj hl0 hL0
      (ne_of_gt (lt_of_lt_of_le zero_lt_one p.hα))).mp hpEq
  have hUconst : U = fun _ => L := by
    funext x
    exact le_antisymm (hUL x) (by simpa [hlEqL] using hlU x)
  have hroot : reactionFun p.α L = 0 := by
    have hs := hstat 0
    rw [hUconst] at hs
    rw [frozenWaveOperator_const_eq p
      (show IsCUnifBdd (fun _ : ℝ => L) from
        ⟨continuous_const, ⟨|L|, fun _ => le_rfl⟩⟩) (fun _ => hL0) 0,
      frozenElliptic_const_eq p hL0 0] at hs
    simp only [sub_self, mul_zero, neg_zero, zero_add] at hs
    unfold reactionFun
    linarith
  have hLone : L = 1 :=
    reactionFun_root_eq_one_of_pos
      (lt_of_lt_of_le zero_lt_one p.hα) hLpos hroot
  simpa [hLone] using hUconst

section AxiomAudit

#print axioms exists_approx_max_ge_reference_deriv_data
#print axioms frozenElliptic_between_global_rpow
#print axioms positiveStationary_eq_one_of_uniformlyPositive

end AxiomAudit

end ShenWork.Paper1
