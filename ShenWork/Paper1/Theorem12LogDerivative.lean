import ShenWork.Paper1.WaveApproxMaximum

open Filter Topology Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# The absolute logarithmic-derivative bound in Paper 1 Lemma 5.2

The paper's stability estimate for the singular range `1 < m < 2` uses an
absolute bound on `U' / U`.  The first lemma below isolates the whole-line
Riccati maximum argument from the traveling-wave coefficients.
-/

/-- A bounded differentiable solution of a Riccati equation is controlled by
the nonnegative root of the corresponding constant-coefficient quadratic.

The proof uses a vanishing quadratic penalty.  This avoids assuming that the
absolute maximum is attained and also avoids the translated-tail compactness
argument used informally in the paper. -/
theorem abs_le_of_bounded_riccati_root
    {w a b : ℝ → ℝ} {A B R : ℝ}
    (hw_cont : Continuous w)
    (hw_diff : Differentiable ℝ w)
    (hw_bdd : ∃ C : ℝ, ∀ x, |w x| ≤ C)
    (hA : 0 ≤ A)
    (ha : ∀ x, |a x| ≤ A)
    (hb : ∀ x, |b x| ≤ B)
    (hode : ∀ x, deriv w x + w x ^ 2 + a x * w x + b x = 0)
    (hR : 0 ≤ R)
    (hroot : R ^ 2 = A * R + B)
    (hvertex : A ≤ 2 * R) :
    ∀ x, |w x| ≤ R := by
  rcases hw_bdd with ⟨C, hC⟩
  have hC_nonneg : 0 ≤ C := le_trans (abs_nonneg (w 0)) (hC 0)
  intro x₁
  by_contra hnot
  have hbad : R < |w x₁| := lt_of_not_ge hnot
  let delta : ℝ := (|w x₁| - R) / 2
  have hdelta : 0 < delta := by
    dsimp [delta]
    linarith
  let f : ℝ → ℝ := fun x => |w x| - R
  have hf_cont : Continuous f := by
    dsimp [f]
    fun_prop
  have hf_bdd : ∀ x, |f x| ≤ C + |R| := by
    intro x
    calc
      |f x| = |(|w x| - R)| := rfl
      _ ≤ |(|w x|)| + |R| := abs_sub _ _
      _ = |w x| + |R| := by rw [abs_abs]
      _ ≤ C + |R| := add_le_add (hC x) (le_refl _)
  have hf_pos : 0 < f x₁ := by
    dsimp [f]
    linarith
  let eta : ℝ := delta ^ 2 / 2
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  obtain ⟨eps, x₀, heps, hmax, hvalue, hpenalty, _⟩ :=
    exists_penalized_max_small_quadratic_errors
      hf_cont hf_bdd hf_pos heta
  have hfx₀_pos : 0 < f x₀ := lt_trans (half_pos hf_pos) hvalue
  have hq_gt_R : R < |w x₀| := by
    dsimp [f] at hfx₀_pos
    linarith
  have hwx₀_ne : w x₀ ≠ 0 := by
    intro hw0
    rw [hw0, abs_zero] at hq_gt_R
    exact (not_lt_of_ge hR) hq_gt_R
  have hf_diff : DifferentiableAt ℝ f x₀ := by
    dsimp [f]
    exact ((hw_diff x₀).abs hwx₀_ne).sub (differentiableAt_const R)
  have hpen_at :
      HasDerivAt (fun x : ℝ => eps * x ^ 2) (2 * eps * x₀) x₀ := by
    simpa [id, mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id x₀).pow 2).const_mul eps
  have hsub_at := hf_diff.hasDerivAt.sub hpen_at
  have hzero : deriv (fun x => f x - eps * x ^ 2) x₀ = 0 :=
    (hmax.isLocalMax univ_mem).deriv_eq_zero
  have hf_deriv : deriv f x₀ = 2 * eps * x₀ := by
    change deriv (f - fun x => eps * x ^ 2) x₀ = 0 at hzero
    rw [hsub_at.deriv] at hzero
    linarith
  have habs_deriv : |deriv w x₀| = |deriv f x₀| := by
    rcases lt_or_gt_of_ne hwx₀_ne with hwneg | hwpos
    · have habs_at : HasDerivAt (fun x => |w x|) (-deriv w x₀) x₀ :=
        by
          simpa using (hasDerivAt_abs_neg hwneg).comp x₀ (hw_diff x₀).hasDerivAt
      have hf_at : HasDerivAt f (-deriv w x₀) x₀ := by
        simpa [f] using habs_at.sub_const R
      rw [hf_at.deriv, abs_neg]
    · have habs_at : HasDerivAt (fun x => |w x|) (deriv w x₀) x₀ :=
        by
          simpa using (hasDerivAt_abs_pos hwpos).comp x₀ (hw_diff x₀).hasDerivAt
      have hf_at : HasDerivAt f (deriv w x₀) x₀ := by
        simpa [f] using habs_at.sub_const R
      rw [hf_at.deriv]
  have hw_deriv_small : |deriv w x₀| < eta := by
    rw [habs_deriv, hf_deriv]
    exact hpenalty
  let q : ℝ := |w x₀|
  have hq_nonneg : 0 ≤ q := abs_nonneg _
  have hq_gap : delta < q - R := by
    have hdelta_eq : f x₁ / 2 = delta := by
      dsimp [f, delta]
    have : delta < f x₀ := by simpa [hdelta_eq] using hvalue
    simpa [f, q] using this
  have hq_second : delta < q + R - A := by
    linarith
  have hprod : delta ^ 2 < (q - R) * (q + R - A) := by
    have hleft : delta * delta < (q - R) * delta :=
      mul_lt_mul_of_pos_right hq_gap hdelta
    have hright : (q - R) * delta < (q - R) * (q + R - A) :=
      mul_lt_mul_of_pos_left hq_second (by linarith)
    nlinarith
  have hquad_lower : delta ^ 2 < q ^ 2 - A * q - B := by
    nlinarith [hprod, hroot]
  have hquad_upper : q ^ 2 - A * q - B < eta := by
    have ha_prod : |a x₀ * w x₀| ≤ A * q := by
      rw [abs_mul]
      exact mul_le_mul (ha x₀) (le_rfl : |w x₀| ≤ q)
        (abs_nonneg _) hA
    have hode₀ := hode x₀
    have hsquare : w x₀ ^ 2 = q ^ 2 := by
      dsimp [q]
      rw [sq_abs]
    have htri :
        w x₀ ^ 2 ≤ |deriv w x₀| + |a x₀ * w x₀| + |b x₀| := by
      have habs_eq :
          w x₀ ^ 2 = |-(deriv w x₀ + a x₀ * w x₀ + b x₀)| := by
        have : w x₀ ^ 2 = -(deriv w x₀ + a x₀ * w x₀ + b x₀) := by
          linarith
        calc
          w x₀ ^ 2 = |w x₀ ^ 2| := (abs_of_nonneg (sq_nonneg (w x₀))).symm
          _ = |-(deriv w x₀ + a x₀ * w x₀ + b x₀)| := congrArg abs this
      rw [habs_eq, abs_neg]
      have hfirst := abs_add_le (deriv w x₀) (a x₀ * w x₀)
      have hsecond := abs_add_le (deriv w x₀ + a x₀ * w x₀) (b x₀)
      linarith
    rw [hsquare] at htri
    nlinarith [ha_prod, hb x₀, hw_deriv_small]
  dsimp [eta] at hquad_upper
  nlinarith

/-- A scalar trajectory converging to zero at the left end cannot cross a
strict inward-pointing lower barrier.  This is the native right-derivative
fencing theorem, so no bespoke Dini-derivative object is introduced. -/
theorem lower_barrier_of_tendsto_atBot
    {w : ℝ → ℝ} {K : ℝ}
    (hK : 0 < K)
    (hw_cont : Continuous w)
    (hw_diff : Differentiable ℝ w)
    (hw_bot : Tendsto w atBot (𝓝 0))
    (hlevel : ∀ x, w x = -K → 0 < deriv w x) :
    ∀ x, -K ≤ w x := by
  intro x
  have hstart_event : ∀ᶠ y in atBot, -K < w y :=
    hw_bot.eventually (Ioi_mem_nhds (by linarith))
  obtain ⟨L, hL⟩ := eventually_atBot.1 hstart_event
  by_cases hxL : x ≤ L
  · exact (hL x hxL).le
  · have hLx : L < x := lt_of_not_ge hxL
    have hf := image_le_of_deriv_right_lt_deriv_boundary
      (f := fun y => -w y) (f' := fun y => -deriv w y)
      (B := fun _ => K) (B' := fun _ => 0)
      (a := L) (b := x)
      hw_cont.neg.continuousOn
      (fun y _ => (hw_diff y).hasDerivAt.neg.hasDerivWithinAt)
      (by linarith [hL L (le_refl L)])
      (fun y => hasDerivAt_const y K)
      (by
        intro y _ hy
        have hwy : w y = -K := by linarith
        linarith [hlevel y hwy])
      (show x ∈ Icc L x from ⟨hLx.le, le_refl x⟩)
    linarith

/-- The coefficient of the linear Riccati term in Lemma 5.2. -/
def paper52RiccatiA (p : CMParams) (c : ℝ) : ℝ :=
  c + |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1)

/-- The uniform zeroth-order Riccati budget in Lemma 5.2. -/
def paper52RiccatiB (p : CMParams) : ℝ :=
  |p.χ| * (MChi p) ^ (p.m + p.γ - 1) + (MChi p) ^ p.α

/-- A sufficient speed for the fixed interval `[-1,0]` to be inward
pointing for the logarithmic Riccati equation of a monotone wave. -/
def paper52MonotoneBarrierSpeed (p : CMParams) : ℝ :=
  |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) +
    1 + paper52RiccatiB p

theorem logDerivativeBoundFormula_eq_riccati_root (p : CMParams) (c : ℝ) :
    logDerivativeBoundFormula p c =
      (paper52RiccatiA p c +
        Real.sqrt (paper52RiccatiA p c ^ 2 + 4 * paper52RiccatiB p)) / 2 := by
  unfold logDerivativeBoundFormula paper52RiccatiA paper52RiccatiB
  ring

theorem paper52RiccatiA_nonneg
    (p : CMParams) {c : ℝ} (hc : 0 ≤ c) (hM : 0 ≤ MChi p) :
    0 ≤ paper52RiccatiA p c := by
  unfold paper52RiccatiA
  exact add_nonneg hc <|
    mul_nonneg
      (mul_nonneg (abs_nonneg _) (le_trans zero_le_one p.hm))
      (Real.rpow_nonneg hM _)

theorem paper52RiccatiB_nonneg
    (p : CMParams) (hM : 0 ≤ MChi p) :
    0 ≤ paper52RiccatiB p := by
  unfold paper52RiccatiB
  exact add_nonneg
    (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hM _))
    (Real.rpow_nonneg hM _)

theorem logDerivativeBoundFormula_root_data
    (p : CMParams) {c : ℝ} (hc : 0 ≤ c) (hM : 0 ≤ MChi p) :
    0 ≤ logDerivativeBoundFormula p c ∧
    logDerivativeBoundFormula p c ^ 2 =
      paper52RiccatiA p c * logDerivativeBoundFormula p c + paper52RiccatiB p ∧
    paper52RiccatiA p c ≤ 2 * logDerivativeBoundFormula p c := by
  let A := paper52RiccatiA p c
  let B := paper52RiccatiB p
  let R := logDerivativeBoundFormula p c
  have hA : 0 ≤ A := paper52RiccatiA_nonneg p hc hM
  have hB : 0 ≤ B := paper52RiccatiB_nonneg p hM
  have hrad : 0 ≤ A ^ 2 + 4 * B := by positivity
  have hsqrt_sq : Real.sqrt (A ^ 2 + 4 * B) ^ 2 = A ^ 2 + 4 * B :=
    Real.sq_sqrt hrad
  have hR : R = (A + Real.sqrt (A ^ 2 + 4 * B)) / 2 := by
    dsimp [R, A, B]
    exact logDerivativeBoundFormula_eq_riccati_root p c
  have hsqrt : 0 ≤ Real.sqrt (A ^ 2 + 4 * B) := Real.sqrt_nonneg _
  constructor
  · change 0 ≤ R
    rw [hR]
    positivity
  constructor
  · change R ^ 2 = A * R + B
    rw [hR]
    nlinarith
  · change A ≤ 2 * R
    rw [hR]
    linarith

/-- The logarithmic derivative used in Paper 1 Lemma 5.2. -/
def waveLogDerivative (U : ℝ → ℝ) : ℝ → ℝ := deriv U / U

/-- The variable coefficient multiplying the logarithmic derivative. -/
def waveLogRiccatiA (p : CMParams) (c : ℝ) (U V : ℝ → ℝ) (x : ℝ) : ℝ :=
  c - p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x

/-- The zeroth-order coefficient in the logarithmic Riccati equation. -/
def waveLogRiccatiB (p : CMParams) (U V : ℝ → ℝ) (x : ℝ) : ℝ :=
  -p.χ * (U x) ^ (p.m - 1) * (V x - (U x) ^ p.γ) +
    (1 - (U x) ^ p.α)

theorem waveLogDerivative_riccati
    (p : CMParams) (c : ℝ) (U V : ℝ → ℝ)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V) (x : ℝ) :
    deriv (waveLogDerivative U) x + waveLogDerivative U x ^ 2 +
      waveLogRiccatiA p c U V x * waveLogDerivative U x +
      waveLogRiccatiB p U V x = 0 := by
  have hU_pos : 0 < U x := hTW.U_pos x
  have hU_ne : U x ≠ 0 := ne_of_gt hU_pos
  have hquot :=
    (hreg.deriv_U_diff x).hasDerivAt.div (hreg.U_diff x).hasDerivAt hU_ne
  have hquot_deriv :
      deriv (waveLogDerivative U) x =
        (deriv (deriv U) x * U x - deriv U x * deriv U x) / U x ^ 2 := by
    simpa [waveLogDerivative] using hquot.deriv
  have hchem := wave_chemotaxis_deriv_expand p (hreg.U_diff x)
    (hreg.V_deriv_diff x) hU_pos.le
    (by have := hTW.ode_V x; linarith)
  have hiD2 : iteratedDeriv 2 U x = deriv (deriv U) x := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_one]
  have hode_U := hTW.ode_U x
  rw [hchem, hiD2] at hode_U
  have hdd : deriv (deriv U) x =
      -(c - p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x) * deriv U x +
        (p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ) -
          U x * (1 - (U x) ^ p.α)) := by
    linarith
  have hpow : U x * (U x) ^ (p.m - 1) = (U x) ^ p.m :=
    mul_rpow_sub_one p.m p.hm hU_pos.le
  have hpow2 : U x ^ 2 * (U x) ^ (p.m - 1) = U x * (U x) ^ p.m := by
    calc
      U x ^ 2 * (U x) ^ (p.m - 1) =
          U x * (U x * (U x) ^ (p.m - 1)) := by ring
      _ = U x * (U x) ^ p.m := by rw [hpow]
  rw [hquot_deriv, hdd]
  unfold waveLogDerivative waveLogRiccatiA waveLogRiccatiB
  simp only [Pi.div_apply]
  field_simp [hU_ne]
  ring_nf
  rw [show -1 + p.m = p.m - 1 by ring]
  linear_combination -p.χ * (V x - (U x) ^ p.γ) * hpow2

theorem abs_waveLogRiccatiA_le
    (p : CMParams) {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U) (x : ℝ) :
    |waveLogRiccatiA p c U V x| ≤ paper52RiccatiA p c := by
  have hM_pos : 0 < MChi p :=
    lt_of_lt_of_le (hbound.pos 0) (hbound.le_MChi 0)
  have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hpow0 : 0 ≤ (U x) ^ (p.m - 1) :=
    Real.rpow_nonneg (hbound.pos x).le _
  have hpow_le : (U x) ^ (p.m - 1) ≤ (MChi p) ^ (p.m - 1) :=
    Real.rpow_le_rpow (hbound.pos x).le (hbound.le_MChi x)
      (sub_nonneg.mpr p.hm)
  have hMpow0 : 0 ≤ (MChi p) ^ (p.m - 1) :=
    Real.rpow_nonneg hM_pos.le _
  have htail :
      (U x) ^ (p.m - 1) * |deriv V x| ≤
        (MChi p) ^ (p.m + p.γ - 1) := by
    calc
      (U x) ^ (p.m - 1) * |deriv V x| ≤
          (MChi p) ^ (p.m - 1) * (MChi p) ^ p.γ :=
        mul_le_mul hpow_le (hreg.V_bound x).2 (abs_nonneg _) hMpow0
      _ = (MChi p) ^ (p.m + p.γ - 1) := by
        rw [← Real.rpow_add hM_pos]
        congr 1
        ring
  have hchem :
      |p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x| ≤
        |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) := by
    calc
      |p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x| =
          (|p.χ| * p.m) * ((U x) ^ (p.m - 1) * |deriv V x|) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hm0,
          abs_of_nonneg hpow0]
        ring
      _ ≤ (|p.χ| * p.m) * (MChi p) ^ (p.m + p.γ - 1) :=
        mul_le_mul_of_nonneg_left htail
          (mul_nonneg (abs_nonneg _) hm0)
      _ = |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) := by ring
  unfold waveLogRiccatiA paper52RiccatiA
  calc
    |c - p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x| ≤
        |c| + |p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x| := abs_sub _ _
    _ ≤ c + |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) := by
      rw [abs_of_pos hTW.hc]
      exact add_le_add (le_refl c) hchem

/-- Lower, rather than absolute, control of the Riccati drift.  This is the
estimate needed by the monotone-wave invariant interval. -/
theorem waveLogRiccatiA_ge_speed_sub
    (p : CMParams) {c : ℝ} {U V : ℝ → ℝ}
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U) (x : ℝ) :
    c - |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) ≤
      waveLogRiccatiA p c U V x := by
  have hM_pos : 0 < MChi p :=
    lt_of_lt_of_le (hbound.pos 0) (hbound.le_MChi 0)
  have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hpow0 : 0 ≤ (U x) ^ (p.m - 1) :=
    Real.rpow_nonneg (hbound.pos x).le _
  have hpow_le : (U x) ^ (p.m - 1) ≤ (MChi p) ^ (p.m - 1) :=
    Real.rpow_le_rpow (hbound.pos x).le (hbound.le_MChi x)
      (sub_nonneg.mpr p.hm)
  have htail :
      (U x) ^ (p.m - 1) * |deriv V x| ≤
        (MChi p) ^ (p.m + p.γ - 1) := by
    calc
      (U x) ^ (p.m - 1) * |deriv V x| ≤
          (MChi p) ^ (p.m - 1) * (MChi p) ^ p.γ :=
        mul_le_mul hpow_le (hreg.V_bound x).2 (abs_nonneg _)
          (Real.rpow_nonneg hM_pos.le _)
      _ = (MChi p) ^ (p.m + p.γ - 1) := by
        rw [← Real.rpow_add hM_pos]
        congr 1
        ring
  have hchem :
      p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x ≤
        |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) := by
    calc
      p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x
          ≤ |p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x| :=
        le_abs_self _
      _ = |p.χ| * p.m *
          ((U x) ^ (p.m - 1) * |deriv V x|) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hm0,
          abs_of_nonneg hpow0]
        ring
      _ ≤ |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) :=
        mul_le_mul_of_nonneg_left htail
          (mul_nonneg (abs_nonneg _) hm0)
  unfold waveLogRiccatiA
  linarith

theorem abs_waveLogRiccatiB_le
    (p : CMParams) {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U) (x : ℝ) :
    |waveLogRiccatiB p U V x| ≤ paper52RiccatiB p := by
  have hM_pos : 0 < MChi p :=
    lt_of_lt_of_le (hbound.pos 0) (hbound.le_MChi 0)
  have hM_one : 1 ≤ MChi p := MChi_ge_one_of_travelingWave hTW hbound
  have hU0 : 0 ≤ U x := (hbound.pos x).le
  have hUm0 : 0 ≤ (U x) ^ (p.m - 1) := Real.rpow_nonneg hU0 _
  have hUm_le : (U x) ^ (p.m - 1) ≤ (MChi p) ^ (p.m - 1) :=
    Real.rpow_le_rpow hU0 (hbound.le_MChi x) (sub_nonneg.mpr p.hm)
  have hUg0 : 0 ≤ (U x) ^ p.γ := Real.rpow_nonneg hU0 _
  have hUg_le : (U x) ^ p.γ ≤ (MChi p) ^ p.γ :=
    Real.rpow_le_rpow hU0 (hbound.le_MChi x) (le_trans zero_le_one p.hγ)
  have hV_le : V x ≤ (MChi p) ^ p.γ :=
    le_trans (le_abs_self _) (hreg.V_bound x).1
  have hdiff : |V x - (U x) ^ p.γ| ≤ (MChi p) ^ p.γ := by
    rw [abs_le]
    constructor <;> linarith [hreg.V_nn x]
  have hMpow0 : 0 ≤ (MChi p) ^ (p.m - 1) := Real.rpow_nonneg hM_pos.le _
  have hmul :
      (U x) ^ (p.m - 1) * |V x - (U x) ^ p.γ| ≤
        (MChi p) ^ (p.m + p.γ - 1) := by
    calc
      (U x) ^ (p.m - 1) * |V x - (U x) ^ p.γ| ≤
          (MChi p) ^ (p.m - 1) * (MChi p) ^ p.γ :=
        mul_le_mul hUm_le hdiff (abs_nonneg _) hMpow0
      _ = (MChi p) ^ (p.m + p.γ - 1) := by
        rw [← Real.rpow_add hM_pos]
        congr 1
        ring
  have hchem :
      |-p.χ * (U x) ^ (p.m - 1) * (V x - (U x) ^ p.γ)| ≤
        |p.χ| * (MChi p) ^ (p.m + p.γ - 1) := by
    calc
      |-p.χ * (U x) ^ (p.m - 1) * (V x - (U x) ^ p.γ)| =
          |p.χ| * ((U x) ^ (p.m - 1) * |V x - (U x) ^ p.γ|) := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hUm0]
        ring
      _ ≤ |p.χ| * (MChi p) ^ (p.m + p.γ - 1) :=
        mul_le_mul_of_nonneg_left hmul (abs_nonneg _)
  have hUa0 : 0 ≤ (U x) ^ p.α := Real.rpow_nonneg hU0 _
  have hUa_le : (U x) ^ p.α ≤ (MChi p) ^ p.α :=
    Real.rpow_le_rpow hU0 (hbound.le_MChi x) (le_trans zero_le_one p.hα)
  have hMa_one : 1 ≤ (MChi p) ^ p.α :=
    Real.one_le_rpow hM_one (le_trans zero_le_one p.hα)
  have hreact : |1 - (U x) ^ p.α| ≤ (MChi p) ^ p.α := by
    rw [abs_le]
    constructor <;> linarith
  unfold waveLogRiccatiB paper52RiccatiB
  exact le_trans (abs_add_le _ _) (add_le_add hchem hreact)

/-- Corrected speed-independent absolute logarithmic-derivative bound at the
stronger explicit speed threshold.  The Riccati vector field points inward
at both endpoints of `[-1,1]`, and the logarithmic derivative tends to zero
at the left end.  No wave monotonicity is needed. -/
theorem abs_waveLogDerivative_le_one_of_barrier_speed
    (p : CMParams) {c : ℝ} {U V : ℝ → ℝ}
    (hspeed : paper52MonotoneBarrierSpeed p < c)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U) :
    ∀ x, |deriv U x / U x| ≤ 1 := by
  have hwcont : Continuous (waveLogDerivative U) := by
    unfold waveLogDerivative
    exact hreg.deriv_U_cont.div hreg.U_cont
      (fun x => ne_of_gt (hTW.U_pos x))
  have hwdiff : Differentiable ℝ (waveLogDerivative U) := by
    intro x
    unfold waveLogDerivative
    exact (hreg.deriv_U_diff x).div (hreg.U_diff x)
      (ne_of_gt (hTW.U_pos x))
  have hwbot : Tendsto (waveLogDerivative U) atBot (𝓝 0) := by
    unfold waveLogDerivative
    simpa using hreg.deriv_U_tendszero.2.div hTW.lim_neg_inf.1
      (by norm_num : (1 : ℝ) ≠ 0)
  have hlevel : ∀ x, waveLogDerivative U x = -(1 : ℝ) →
      0 < deriv (waveLogDerivative U) x := by
    intro x hx
    have hA := waveLogRiccatiA_ge_speed_sub p hreg hbound x
    have hb := abs_waveLogRiccatiB_le p hTW hreg hbound x
    have hode := waveLogDerivative_riccati p c U V hTW hreg x
    have hstrict :
        1 + paper52RiccatiB p <
          c - |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) := by
      unfold paper52MonotoneBarrierSpeed at hspeed
      linarith
    rw [hx] at hode
    have hb_upper : waveLogRiccatiB p U V x ≤ paper52RiccatiB p :=
      (abs_le.mp hb).2
    nlinarith
  have hlower : ∀ x, -(1 : ℝ) ≤ waveLogDerivative U x :=
    lower_barrier_of_tendsto_atBot one_pos hwcont hwdiff hwbot hlevel
  have hlevel_upper : ∀ x, -waveLogDerivative U x = -(1 : ℝ) →
      0 < deriv (fun y => -waveLogDerivative U y) x := by
    intro x hx
    have hwx : waveLogDerivative U x = 1 := by linarith
    have hA := waveLogRiccatiA_ge_speed_sub p hreg hbound x
    have hb := abs_waveLogRiccatiB_le p hTW hreg hbound x
    have hode := waveLogDerivative_riccati p c U V hTW hreg x
    have hstrict :
        1 + paper52RiccatiB p <
          c - |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) := by
      unfold paper52MonotoneBarrierSpeed at hspeed
      linarith
    rw [hwx] at hode
    have hb_lower : -paper52RiccatiB p ≤ waveLogRiccatiB p U V x :=
      (abs_le.mp hb).1
    have hneg_deriv :
        deriv (fun y => -waveLogDerivative U y) x =
          -deriv (waveLogDerivative U) x :=
      (hwdiff x).hasDerivAt.neg.deriv
    rw [hneg_deriv]
    nlinarith
  have hupper_neg : ∀ x, -(1 : ℝ) ≤ -waveLogDerivative U x := by
    apply lower_barrier_of_tendsto_atBot one_pos hwcont.neg hwdiff.neg
    · simpa using hwbot.neg
    · exact hlevel_upper
  intro x
  change |waveLogDerivative U x| ≤ 1
  exact abs_le.2 ⟨hlower x, by linarith [hupper_neg x]⟩

/-- Compatibility wrapper for the monotone Theorem 1.1(1) branch. -/
theorem abs_waveLogDerivative_le_one_of_monotone
    (p : CMParams) {c : ℝ} {U V : ℝ → ℝ}
    (hspeed : paper52MonotoneBarrierSpeed p < c)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (_hmono : Antitone U) :
    ∀ x, |deriv U x / U x| ≤ 1 :=
  abs_waveLogDerivative_le_one_of_barrier_speed p hspeed hTW hreg hbound

theorem two_le_gamma_add_inv (p : CMParams) :
    2 ≤ p.γ + p.γ⁻¹ := by
  have hγpos : 0 < p.γ := lt_of_lt_of_le zero_lt_one p.hγ
  have hγne : p.γ ≠ 0 := ne_of_gt hγpos
  have hid : p.γ + p.γ⁻¹ - 2 = (p.γ - 1) ^ 2 / p.γ := by
    field_simp [hγne]
    ring
  have hnonneg : 0 ≤ p.γ + p.γ⁻¹ - 2 := by
    rw [hid]
    exact div_nonneg (sq_nonneg _) hγpos.le
  linarith

/-- On the right half-line the exponentially weighted wave derivative is
bounded.  The drift is eventually positive because `m > 1` makes the
chemotactic perturbation vanish, while the source is controlled by the
existing exponential Neumann-resolver estimate. -/
theorem waveWeightedDerivative_eventually_bounded
    (p : CMParams) {c : ℝ} {U V : ℝ → ℝ}
    (hm1 : 1 < p.m)
    (hspeed :
      c > max (p.γ + p.γ⁻¹)
        (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)))
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U) :
    ∃ X C : ℝ, 0 ≤ C ∧ ∀ x, X ≤ x →
      |deriv U x * Real.exp (kappa c * x)| ≤ C := by
  have hγspeed : p.γ + p.γ⁻¹ < c :=
    lt_of_le_of_lt (le_max_left _ _) hspeed
  have hc2 : 2 < c := lt_of_le_of_lt (two_le_gamma_add_inv p) hγspeed
  have hκpos : 0 < kappa c := kappa_pos_of_two_lt hc2
  have hκlt : kappa c < 1 := kappa_lt_one_of_two_lt hc2
  have hckpos : 0 < c - kappa c := by linarith
  let a0 : ℝ := (c - kappa c) / 2
  have ha0pos : 0 < a0 := by dsimp [a0]; linarith
  have hMpos : 0 < MChi p :=
    lt_of_lt_of_le (hbound.pos 0) (hbound.le_MChi 0)
  have hMone : 1 ≤ MChi p := MChi_ge_one_of_travelingWave hTW hbound
  have hVeq : V = frozenElliptic p U :=
    IsTravelingWave.V_eq_frozenElliptic_full hTW hbound hreg
  have hFE := Lemma_5_1_exponential_signal_bound_for_frozenElliptic_of_continuous
    p hc2 hγspeed hreg.U_cont hbound
  have hVexp : ∀ x,
      |V x| ≤ (1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
          Real.exp (-(kappa c) * p.γ * x) ∧
      |deriv V x| ≤ (1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
          Real.exp (-(kappa c) * p.γ * x) := by
    intro x
    rw [hVeq]
    exact ⟨(hFE x).1.trans (min_le_right _ _),
      (hFE x).2.trans (min_le_right _ _)⟩
  let w : ℝ → ℝ := fun x => deriv U x * Real.exp (kappa c * x)
  let aw : ℝ → ℝ := fun x =>
    c - kappa c - p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x
  let gw : ℝ → ℝ := fun x =>
    (p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ) -
      U x * (1 - (U x) ^ p.α)) * Real.exp (kappa c * x)
  let G : ℝ := max (remark51MPrime p) (max 0
    (|p.χ| * (1 / (1 - kappa c ^ 2 * p.γ ^ 2) + 1) + 2))
  have hGnonneg : 0 ≤ G := by
    dsimp [G]
    exact le_trans (le_max_left 0 _) (le_max_right _ _)
  have hgbound : ∀ x, |gw x| ≤ G := by
    exact wave_weighted_source_upper_bound_global
      (fun x => (hbound.pos x).le) (fun x => hbound.le_MChi x)
      hMpos hMone hreg.V_nn (fun x => (hreg.V_bound x).1)
      hbound (fun x => (hVexp x).1) hκpos
  let chem : ℝ → ℝ := fun x =>
    p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x
  let Cchem : ℝ := |p.χ| * p.m * (MChi p) ^ p.γ
  have hCchem0 : 0 ≤ Cchem := by
    dsimp [Cchem]
    positivity
  have hchem_bound : ∀ x, |chem x| ≤ Cchem * (U x) ^ (p.m - 1) := by
    intro x
    have hUpow0 : 0 ≤ (U x) ^ (p.m - 1) :=
      Real.rpow_nonneg (hbound.pos x).le _
    dsimp [chem, Cchem]
    rw [abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (le_trans zero_le_one p.hm), abs_of_nonneg hUpow0]
    calc
      |p.χ| * p.m * (U x) ^ (p.m - 1) * |deriv V x| ≤
          |p.χ| * p.m * (U x) ^ (p.m - 1) * (MChi p) ^ p.γ :=
        mul_le_mul_of_nonneg_left (hreg.V_bound x).2
          (mul_nonneg (mul_nonneg (abs_nonneg _)
            (le_trans zero_le_one p.hm)) hUpow0)
      _ = |p.χ| * p.m * (MChi p) ^ p.γ * (U x) ^ (p.m - 1) := by
        ring
  have hUpow_top : Tendsto (fun x => (U x) ^ (p.m - 1)) atTop (𝓝 0) := by
    have hpow := hTW.lim_pos_inf.1.rpow_const (Or.inr (by linarith : 0 ≤ p.m - 1))
    simpa [Real.zero_rpow (by linarith : p.m - 1 ≠ 0)] using hpow
  have hupper_top : Tendsto (fun x => Cchem * (U x) ^ (p.m - 1))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hUpow_top
  have hchem_top : Tendsto (fun x => |chem x|) atTop (𝓝 0) :=
    squeeze_zero (fun x => abs_nonneg _) hchem_bound hupper_top
  have hevent : ∀ᶠ x in atTop, |chem x| < a0 :=
    hchem_top.eventually (Iio_mem_nhds ha0pos)
  obtain ⟨X, hX⟩ := eventually_atTop.1 hevent
  have hwode : ∀ x, deriv w x = -aw x * w x + gw x := by
    intro x
    exact wave_weighted_derivative_ode p c U V hTW hreg x
  have hwdiff : Differentiable ℝ w := by
    intro x
    exact (hreg.deriv_U_diff x).mul (by fun_prop)
  let C : ℝ := |w X| + G / a0
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (abs_nonneg _) (div_nonneg hGnonneg ha0pos.le)
  refine ⟨X, C, hC0, ?_⟩
  intro x hx
  have hduh := first_order_ode_duhamel_bound_on_Icc
    (v := w) (a := aw) (g := gw) (a₀ := a0) (G := G)
    X x ha0pos hGnonneg
    (fun y hy => by
      have hsmall := hX y hy.1
      have hchemle : chem y ≤ a0 :=
        (le_abs_self _).trans hsmall.le
      dsimp [aw, chem, a0] at *
      linarith)
    (fun y _ => hgbound y) (fun y _ => hwode y) hwdiff hx
  have hexp_le : Real.exp (-a0 * (x - X)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha0pos.le)
      (sub_nonneg.mpr hx)
  have hone_sub : 1 - Real.exp (-a0 * (x - X)) ≤ 1 := by
    linarith [Real.exp_pos (-a0 * (x - X))]
  dsimp [C]
  calc
    |w x| ≤ |w X| * Real.exp (-a0 * (x - X)) +
        G / a0 * (1 - Real.exp (-a0 * (x - X))) := hduh
    _ ≤ |w X| * 1 + G / a0 * 1 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hexp_le (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hone_sub
          (div_nonneg hGnonneg ha0pos.le))
    _ = |w X| + G / a0 := by ring

/-- The logarithmic derivative is globally bounded once the wave has the
right-tail asymptotic carried by the corrected stability headline.  The
left tail uses `U → 1` and `U' → 0`; the middle is compact; the right tail
uses `waveWeightedDerivative_eventually_bounded`. -/
theorem waveLogDerivative_isBounded
    (p : CMParams) {c κ₁ : ℝ} {U V : ℝ → ℝ}
    (hm1 : 1 < p.m)
    (hspeed :
      c > max (p.γ + p.γ⁻¹)
        (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)))
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hκ₁ : kappa c < κ₁)
    (htail : HasWaveRightTailAsymptotic c κ₁ U) :
    ∃ W : ℝ, ∀ x, |waveLogDerivative U x| ≤ W := by
  obtain ⟨X, C, hC0, hweighted⟩ :=
    waveWeightedDerivative_eventually_bounded p hm1 hspeed hTW hreg hbound
  have hratio_top := htail.ratio_tendsto_one hκ₁
  have hratio_event : ∀ᶠ x in atTop,
      (1 / 2 : ℝ) < U x / Real.exp (-(kappa c) * x) :=
    hratio_top.eventually (Ioi_mem_nhds (by norm_num))
  obtain ⟨R, hR⟩ := eventually_atTop.1 hratio_event
  let XR : ℝ := max X R
  have hright : ∀ x, XR ≤ x → |waveLogDerivative U x| ≤ 2 * C := by
    intro x hx
    have hxX : X ≤ x := le_trans (le_max_left _ _) hx
    have hxR : R ≤ x := le_trans (le_max_right _ _) hx
    have hw := hweighted x hxX
    have hd : 0 < U x / Real.exp (-(kappa c) * x) :=
      lt_trans (by norm_num : (0 : ℝ) < 1 / 2) (hR x hxR)
    have hid : waveLogDerivative U x =
        (deriv U x * Real.exp (kappa c * x)) /
          (U x / Real.exp (-(kappa c) * x)) := by
      unfold waveLogDerivative
      simp only [Pi.div_apply]
      field_simp [ne_of_gt (hTW.U_pos x), Real.exp_ne_zero]
      rw [mul_assoc, ← Real.exp_add]
      simp
    rw [hid, abs_div, abs_of_pos hd]
    apply (div_le_iff₀ hd).2
    have hhalf := hR x hxR
    nlinarith [hw]
  have hUleft_event : ∀ᶠ x in atBot, (1 / 2 : ℝ) < U x :=
    hTW.lim_neg_inf.1.eventually (Ioi_mem_nhds (by norm_num))
  have hDleft_event : ∀ᶠ x in atBot, |deriv U x| < 1 := by
    have hball : Metric.ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
      Metric.ball_mem_nhds _ one_pos
    filter_upwards [hreg.deriv_U_tendszero.2 hball] with x hx
    change deriv U x ∈ Metric.ball (0 : ℝ) 1 at hx
    simpa [Metric.mem_ball, Real.dist_eq] using hx
  have hleft_event : ∀ᶠ x in atBot,
      (1 / 2 : ℝ) < U x ∧ |deriv U x| < 1 :=
    hUleft_event.and hDleft_event
  obtain ⟨L, hL⟩ := eventually_atBot.1 hleft_event
  let A : ℝ := min L XR
  have hleft : ∀ x, x ≤ A → |waveLogDerivative U x| ≤ 2 := by
    intro x hx
    have hxL : x ≤ L := le_trans hx (min_le_left _ _)
    have hdata := hL x hxL
    unfold waveLogDerivative
    simp only [Pi.div_apply]
    rw [abs_div, abs_of_pos (hTW.U_pos x)]
    apply (div_le_iff₀ (hTW.U_pos x)).2
    nlinarith
  have hlog_cont : Continuous (waveLogDerivative U) := by
    unfold waveLogDerivative
    exact hreg.deriv_U_cont.div hreg.U_cont
      (fun x => ne_of_gt (hTW.U_pos x))
  obtain ⟨Bmid, hBmid⟩ :=
    isCompact_Icc.bddAbove_image hlog_cont.abs.continuousOn
  let W : ℝ := max (2 * C) (max 2 Bmid)
  refine ⟨W, ?_⟩
  intro x
  by_cases hxA : x ≤ A
  · exact (hleft x hxA).trans
      (le_trans (le_max_left _ _) (le_max_right _ _))
  · by_cases hxR : XR ≤ x
    · exact (hright x hxR).trans (le_max_left _ _)
    · have hxIcc : x ∈ Set.Icc A XR :=
        ⟨le_of_not_ge hxA, le_of_not_ge hxR⟩
      have hxmid : |waveLogDerivative U x| ≤ Bmid :=
        hBmid (Set.mem_image_of_mem _ hxIcc)
      exact hxmid.trans
        (le_trans (le_max_right _ _) (le_max_right _ _))

/-- Absolute, nonmonotone form of Paper 1 Lemma 5.2 on the corrected
traveling-wave branch. -/
theorem abs_waveLogDerivative_le_logDerivativeBoundFormula
    (p : CMParams) {c κ₁ : ℝ} {U V : ℝ → ℝ}
    (hm1 : 1 < p.m)
    (hspeed :
      c > max (p.γ + p.γ⁻¹)
        (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)))
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hκ₁ : kappa c < κ₁)
    (htail : HasWaveRightTailAsymptotic c κ₁ U) :
    ∀ x, |deriv U x / U x| ≤ logDerivativeBoundFormula p c := by
  have hwcont : Continuous (waveLogDerivative U) := by
    unfold waveLogDerivative
    exact hreg.deriv_U_cont.div hreg.U_cont
      (fun x => ne_of_gt (hTW.U_pos x))
  have hwdiff : Differentiable ℝ (waveLogDerivative U) := by
    intro x
    unfold waveLogDerivative
    exact (hreg.deriv_U_diff x).div (hreg.U_diff x)
      (ne_of_gt (hTW.U_pos x))
  have hwbound := waveLogDerivative_isBounded p hm1 hspeed hTW hreg hbound
    hκ₁ htail
  have hM0 : 0 ≤ MChi p :=
    le_trans (hbound.pos 0).le (hbound.le_MChi 0)
  obtain ⟨hR0, hroot, hvertex⟩ :=
    logDerivativeBoundFormula_root_data p hTW.hc.le hM0
  intro x
  exact abs_le_of_bounded_riccati_root hwcont hwdiff hwbound
    (paper52RiccatiA_nonneg p hTW.hc.le hM0)
    (abs_waveLogRiccatiA_le p hTW hreg hbound)
    (abs_waveLogRiccatiB_le p hTW hreg hbound)
    (waveLogDerivative_riccati p c U V hTW hreg)
    hR0 hroot hvertex x

section AxiomAudit

#print axioms abs_le_of_bounded_riccati_root
#print axioms lower_barrier_of_tendsto_atBot
#print axioms logDerivativeBoundFormula_root_data
#print axioms waveLogRiccatiA_ge_speed_sub
#print axioms abs_waveLogDerivative_le_one_of_barrier_speed
#print axioms abs_waveLogDerivative_le_one_of_monotone
#print axioms waveWeightedDerivative_eventually_bounded
#print axioms waveLogDerivative_isBounded
#print axioms abs_waveLogDerivative_le_logDerivativeBoundFormula

end AxiomAudit

end ShenWork.Paper1
