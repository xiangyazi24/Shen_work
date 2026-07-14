import ShenWork.Paper1.WholeLineCauchyC1HolderBootstrap

open Filter Topology MeasureTheory Real Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Positive-time C1 regularity of the whole-line chemotaxis flux

The clamp is not differentiated.  On a physical slice it is first removed,
and the ordinary product rule is applied to the unclamped flux.  A global
bound for the population derivative follows from boundedness of the slice,
its Holder derivative, and the mean value theorem on unit intervals.
-/

/-- A bounded global Holder estimate may be lowered to any smaller positive
exponent. -/
theorem holder_lower_exponent_of_bounded_cauchy
    {f : ℝ → ℝ} {C H eta rho : ℝ}
    (hH : 0 ≤ H)
    (hrho0 : 0 < rho) (hrhoeta : rho ≤ eta)
    (hbound : ∀ x, |f x| ≤ C)
    (hholder : ∀ x y, |f x - f y| ≤ H * |x - y| ^ eta) :
    ∀ x y, |f x - f y| ≤ max H (2 * C) * |x - y| ^ rho := by
  intro x y
  let d : ℝ := |x - y|
  have hd : 0 ≤ d := by dsimp [d]; positivity
  by_cases hd1 : d ≤ 1
  · have hpow : d ^ eta ≤ d ^ rho :=
      Real.rpow_le_rpow_of_exponent_ge' hd hd1 hrho0.le hrhoeta
    calc
      |f x - f y| ≤ H * d ^ eta := by simpa [d] using hholder x y
      _ ≤ H * d ^ rho := mul_le_mul_of_nonneg_left hpow hH
      _ ≤ max H (2 * C) * d ^ rho :=
        mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg hd _)
  · have hdge : 1 ≤ d := le_of_not_ge hd1
    have hdpow : 1 ≤ d ^ rho := by
      simpa using Real.rpow_le_rpow zero_le_one hdge hrho0.le
    calc
      |f x - f y| ≤ |f x| + |f y| := abs_sub _ _
      _ ≤ C + C := add_le_add (hbound x) (hbound y)
      _ = 2 * C := by ring
      _ ≤ max H (2 * C) := le_max_right _ _
      _ = max H (2 * C) * 1 := by ring
      _ ≤ max H (2 * C) * d ^ rho := by
        gcongr

/-- The fractional real-power inequality at the origin. -/
theorem abs_nonneg_rpow_sub_rpow_le_abs_sub_rpow
    {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    |a ^ q - b ^ q| ≤ |a - b| ^ q := by
  rcases le_total a b with hab | hba
  · have hpab : a ^ q ≤ b ^ q := Real.rpow_le_rpow ha hab hq0
    have hsub : 0 ≤ b - a := sub_nonneg.mpr hab
    have hadd := Real.rpow_add_le_add_rpow ha hsub hq0 hq1
    have hrewrite : a + (b - a) = b := by ring
    rw [hrewrite] at hadd
    rw [abs_of_nonpos (sub_nonpos.mpr hpab),
      abs_of_nonpos (sub_nonpos.mpr hab)]
    rw [show -(a - b) = b - a by ring]
    linarith
  · have hpba : b ^ q ≤ a ^ q := Real.rpow_le_rpow hb hba hq0
    have hsub : 0 ≤ a - b := sub_nonneg.mpr hba
    have hadd := Real.rpow_add_le_add_rpow hb hsub hq0 hq1
    have hrewrite : b + (a - b) = a := by ring
    rw [hrewrite] at hadd
    rw [abs_of_nonneg (sub_nonneg.mpr hpba), abs_of_nonneg hsub]
    linarith

/-- A nonnegative bounded globally Lipschitz function raised to any positive
power `q` is globally `rho`-Holder for `rho <= min 1 q`. -/
theorem wholeLine_rpow_holder_of_nonneg_bounded_lipschitz
    {f : ℝ → ℝ} {M L q rho : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hq : 0 < q)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hrhoq : rho ≤ q)
    (hrange : ∀ x, f x ∈ Set.Icc (0 : ℝ) M)
    (hlip : ∀ x y, |f x - f y| ≤ L * |x - y|) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ x y,
      |(f x) ^ q - (f y) ^ q| ≤ H * |x - y| ^ rho := by
  let A : ℝ := L ^ q + q * M ^ (q - 1) * L
  let H : ℝ := max A (2 * M ^ q)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hH : 0 ≤ H := le_trans hA (le_max_left _ _)
  refine ⟨H, hH, ?_⟩
  intro x y
  let d : ℝ := |x - y|
  have hd : 0 ≤ d := by dsimp [d]; positivity
  by_cases hd1 : d ≤ 1
  · have hpowrho : d ^ q ≤ d ^ rho :=
      Real.rpow_le_rpow_of_exponent_ge' hd hd1 hrho.le hrhoq
    rcases le_total q 1 with hq1 | hqge
    · have hfrac := abs_nonneg_rpow_sub_rpow_le_abs_sub_rpow
        (hrange x).1 (hrange y).1 hq.le hq1
      have hbase : |f x - f y| ^ q ≤ (L * d) ^ q :=
        Real.rpow_le_rpow (abs_nonneg _) (by simpa [d] using hlip x y) hq.le
      calc
        |(f x) ^ q - (f y) ^ q| ≤ |f x - f y| ^ q := hfrac
        _ ≤ (L * d) ^ q := hbase
        _ = L ^ q * d ^ q := Real.mul_rpow hL hd
        _ ≤ L ^ q * d ^ rho :=
          mul_le_mul_of_nonneg_left hpowrho (Real.rpow_nonneg hL _)
        _ ≤ A * d ^ rho := by
          exact mul_le_mul_of_nonneg_right
            (by dsimp [A]; exact le_add_of_nonneg_right (by positivity))
            (Real.rpow_nonneg hd _)
        _ ≤ H * d ^ rho :=
          mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.rpow_nonneg hd _)
    · have hpowLip : |(f x) ^ q - (f y) ^ q| ≤
          q * M ^ (q - 1) * |f x - f y| := by
        simpa [rpowLip] using
          abs_rpow_sub_rpow_le_of_mem_Icc hqge hM (hrange x) (hrange y)
      have hdRho : d ≤ d ^ rho := by
        simpa [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_ge' hd hd1 hrho.le hrho1
      calc
        |(f x) ^ q - (f y) ^ q| ≤
            q * M ^ (q - 1) * |f x - f y| := hpowLip
        _ ≤ q * M ^ (q - 1) * (L * d) :=
          mul_le_mul_of_nonneg_left (by simpa [d] using hlip x y)
            (mul_nonneg hq.le (Real.rpow_nonneg hM _))
        _ = (q * M ^ (q - 1) * L) * d := by ring
        _ ≤ (q * M ^ (q - 1) * L) * d ^ rho :=
          mul_le_mul_of_nonneg_left hdRho (by positivity)
        _ ≤ A * d ^ rho := by
          exact mul_le_mul_of_nonneg_right
            (by dsimp [A]; exact le_add_of_nonneg_left (by positivity))
            (Real.rpow_nonneg hd _)
        _ ≤ H * d ^ rho :=
          mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.rpow_nonneg hd _)
  · have hdge : 1 ≤ d := le_of_not_ge hd1
    have hdpow : 1 ≤ d ^ rho := by
      simpa using Real.rpow_le_rpow zero_le_one hdge hrho.le
    have hpowBound : ∀ z, |(f z) ^ q| ≤ M ^ q := by
      intro z
      rw [abs_of_nonneg (Real.rpow_nonneg (hrange z).1 _)]
      exact Real.rpow_le_rpow (hrange z).1 (hrange z).2 hq.le
    calc
      |(f x) ^ q - (f y) ^ q| ≤ |(f x) ^ q| + |(f y) ^ q| :=
        abs_sub _ _
      _ ≤ M ^ q + M ^ q := add_le_add (hpowBound x) (hpowBound y)
      _ = 2 * M ^ q := by ring
      _ ≤ H := le_max_right _ _
      _ = H * 1 := by ring
      _ ≤ H * d ^ rho := mul_le_mul_of_nonneg_left hdpow hH

/-- Quantitative global Holder data used to assemble the differentiated
physical flux. -/
structure WholeLineCauchyHolderQuant (eta : ℝ) (f : ℝ → ℝ) where
  C : ℝ
  H : ℝ
  C_nonneg : 0 ≤ C
  H_nonneg : 0 ≤ H
  bound : ∀ x, |f x| ≤ C
  holder : ∀ x y, |f x - f y| ≤ H * |x - y| ^ eta

namespace WholeLineCauchyHolderQuant

def add {eta : ℝ} {f g : ℝ → ℝ}
    (hf : WholeLineCauchyHolderQuant eta f)
    (hg : WholeLineCauchyHolderQuant eta g) :
    WholeLineCauchyHolderQuant eta (fun x => f x + g x) where
  C := hf.C + hg.C
  H := hf.H + hg.H
  C_nonneg := add_nonneg hf.C_nonneg hg.C_nonneg
  H_nonneg := add_nonneg hf.H_nonneg hg.H_nonneg
  bound := by intro x; exact (abs_add_le _ _).trans (add_le_add (hf.bound x) (hg.bound x))
  holder := by
    intro x y
    calc
      |(f x + g x) - (f y + g y)| =
          |(f x - f y) + (g x - g y)| := by ring_nf
      _ ≤ |f x - f y| + |g x - g y| := abs_add_le _ _
      _ ≤ hf.H * |x - y| ^ eta + hg.H * |x - y| ^ eta :=
        add_le_add (hf.holder x y) (hg.holder x y)
      _ = (hf.H + hg.H) * |x - y| ^ eta := by ring

def neg {eta : ℝ} {f : ℝ → ℝ}
    (hf : WholeLineCauchyHolderQuant eta f) :
    WholeLineCauchyHolderQuant eta (fun x => -f x) where
  C := hf.C
  H := hf.H
  C_nonneg := hf.C_nonneg
  H_nonneg := hf.H_nonneg
  bound := by intro x; simpa using hf.bound x
  holder := by
    intro x y
    simpa only [neg_sub_neg, abs_neg, abs_sub_comm] using hf.holder x y

def sub {eta : ℝ} {f g : ℝ → ℝ}
    (hf : WholeLineCauchyHolderQuant eta f)
    (hg : WholeLineCauchyHolderQuant eta g) :
    WholeLineCauchyHolderQuant eta (fun x => f x - g x) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

def const_mul {eta a : ℝ} {f : ℝ → ℝ}
    (hf : WholeLineCauchyHolderQuant eta f) :
    WholeLineCauchyHolderQuant eta (fun x => a * f x) where
  C := |a| * hf.C
  H := |a| * hf.H
  C_nonneg := mul_nonneg (abs_nonneg a) hf.C_nonneg
  H_nonneg := mul_nonneg (abs_nonneg a) hf.H_nonneg
  bound := by
    intro x
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hf.bound x) (abs_nonneg a)
  holder := by
    intro x y
    rw [← mul_sub, abs_mul]
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_left (hf.holder x y) (abs_nonneg a)

def mul {eta : ℝ} {f g : ℝ → ℝ}
    (hf : WholeLineCauchyHolderQuant eta f)
    (hg : WholeLineCauchyHolderQuant eta g) :
    WholeLineCauchyHolderQuant eta (fun x => f x * g x) where
  C := hf.C * hg.C
  H := hf.C * hg.H + hg.C * hf.H
  C_nonneg := mul_nonneg hf.C_nonneg hg.C_nonneg
  H_nonneg := add_nonneg (mul_nonneg hf.C_nonneg hg.H_nonneg)
    (mul_nonneg hg.C_nonneg hf.H_nonneg)
  bound := by
    intro x
    rw [abs_mul]
    exact mul_le_mul (hf.bound x) (hg.bound x) (abs_nonneg _) hf.C_nonneg
  holder := by
    intro x y
    calc
      |f x * g x - f y * g y| =
          |f x * (g x - g y) + g y * (f x - f y)| := by ring_nf
      _ ≤ |f x| * |g x - g y| + |g y| * |f x - f y| := by
        simpa only [abs_mul] using abs_add_le
          (f x * (g x - g y)) (g y * (f x - f y))
      _ ≤ hf.C * (hg.H * |x - y| ^ eta) +
          hg.C * (hf.H * |x - y| ^ eta) :=
        add_le_add
          (mul_le_mul (hf.bound x) (hg.holder x y)
            (abs_nonneg _) hf.C_nonneg)
          (mul_le_mul (hg.bound y) (hf.holder x y)
            (abs_nonneg _) hg.C_nonneg)
      _ = (hf.C * hg.H + hg.C * hf.H) * |x - y| ^ eta := by ring

end WholeLineCauchyHolderQuant

/-- A globally bounded Lipschitz function carries quantitative Holder data at
every exponent in `(0,1]`. -/
def wholeLineCauchyHolderQuant_of_lipschitz
    {f : ℝ → ℝ} {C L eta : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hbound : ∀ x, |f x| ≤ C)
    (hlip : ∀ x y, |f x - f y| ≤ L * |x - y|) :
    WholeLineCauchyHolderQuant eta f where
  C := C
  H := max L (2 * C)
  C_nonneg := hC
  H_nonneg := le_trans hL (le_max_left _ _)
  bound := hbound
  holder := holder_of_local_lipschitz_of_bounded_cauchy heta0 heta1 hL hbound
    (fun x y _ => hlip x y)

/-- Lower the exponent of quantitative Holder data. -/
def WholeLineCauchyHolderQuant.lowerExponent
    {f : ℝ → ℝ} {eta rho : ℝ}
    (hf : WholeLineCauchyHolderQuant eta f)
    (hrho0 : 0 < rho) (hrhoeta : rho ≤ eta) :
    WholeLineCauchyHolderQuant rho f where
  C := hf.C
  H := max hf.H (2 * hf.C)
  C_nonneg := hf.C_nonneg
  H_nonneg := le_trans hf.H_nonneg (le_max_left _ _)
  bound := hf.bound
  holder := holder_lower_exponent_of_bounded_cauchy hf.H_nonneg
    hrho0 hrhoeta hf.bound hf.holder

/-- Powers at least one preserve the exponent of bounded nonnegative Holder
data. -/
def WholeLineCauchyHolderQuant.rpowOfOneLe
    {f : ℝ → ℝ} {eta q M : ℝ}
    (hf : WholeLineCauchyHolderQuant eta f)
    (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hrange : ∀ x, f x ∈ Set.Icc (0 : ℝ) M) :
    WholeLineCauchyHolderQuant eta (fun x => (f x) ^ q) where
  C := M ^ q
  H := rpowLip q M * hf.H
  C_nonneg := Real.rpow_nonneg hM _
  H_nonneg := mul_nonneg (rpowLip_nonneg hq hM) hf.H_nonneg
  bound := by
    intro x
    rw [abs_of_nonneg (Real.rpow_nonneg (hrange x).1 _)]
    exact Real.rpow_le_rpow (hrange x).1 (hrange x).2 (zero_le_one.trans hq)
  holder := by
    intro x y
    calc
      |(f x) ^ q - (f y) ^ q| ≤ rpowLip q M * |f x - f y| :=
        abs_rpow_sub_rpow_le_of_mem_Icc hq hM (hrange x) (hrange y)
      _ ≤ rpowLip q M * (hf.H * |x - y| ^ eta) :=
        mul_le_mul_of_nonneg_left (hf.holder x y) (rpowLip_nonneg hq hM)
      _ = rpowLip q M * hf.H * |x - y| ^ eta := by ring

/-- A globally bounded differentiable function with a globally Holder
derivative has a globally bounded derivative. -/
theorem deriv_abs_le_of_bounded_of_deriv_holder
    {f : ℝ → ℝ} {M H eta : ℝ}
    (hH : 0 ≤ H) (heta0 : 0 < eta)
    (hbound : ∀ x, |f x| ≤ M)
    (hdiff : ∀ x, DifferentiableAt ℝ f x)
    (hholder : ∀ x y, |deriv f x - deriv f y| ≤ H * |x - y| ^ eta) :
    ∀ x, |deriv f x| ≤ H + 2 * M := by
  intro x
  have hxx : x < x + 1 := by linarith
  have hcont : Continuous f := continuous_iff_continuousAt.2 fun q =>
    (hdiff q).continuousAt
  obtain ⟨c, hc, hcEq⟩ := exists_deriv_eq_slope f hxx
    hcont.continuousOn (fun q _ => (hdiff q).differentiableWithinAt)
  have hcEq' : deriv f c = f (x + 1) - f x := by
    convert hcEq using 1 <;> ring
  have hcBound : |deriv f c| ≤ 2 * M := by
    rw [hcEq']
    calc
      |f (x + 1) - f x| ≤ |f (x + 1)| + |f x| := abs_sub _ _
      _ ≤ M + M := add_le_add (hbound _) (hbound _)
      _ = 2 * M := by ring
  have hxc : |x - c| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hc.1.le)]
    linarith [hc.2]
  have hxcpow : |x - c| ^ eta ≤ 1 :=
    Real.rpow_le_one (abs_nonneg _) hxc heta0.le
  calc
    |deriv f x| = |(deriv f x - deriv f c) + deriv f c| := by ring_nf
    _ ≤ |deriv f x - deriv f c| + |deriv f c| := abs_add_le _ _
    _ ≤ H * |x - c| ^ eta + 2 * M :=
      add_le_add (hholder x c) hcBound
    _ ≤ H * 1 + 2 * M :=
      add_le_add (mul_le_mul_of_nonneg_left hxcpow hH) le_rfl
    _ = H + 2 * M := by ring

/-- On a physical positive-time slice, the canonical population derivative
is globally bounded. -/
theorem wholeLineCauchyBUCMildFixedPoint_spatial_deriv_bounded_positive
    (p : CMParams) {M T theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
      |deriv (fun w : ℝ =>
        (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 w) x| ≤ B := by
  let f : ℝ → ℝ := fun w =>
    (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 w
  rcases wholeLineCauchyBUCMildFixedPoint_spatial_deriv_Ceta
      p hM hT u₀ hsmall z hz htheta0 htheta1 heta0 heta1 hrel with
    ⟨H, hH, hholder⟩
  let B : ℝ := H + 2 * M
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  have hbound : ∀ x, |f x| ≤ M := by
    intro x
    rw [abs_of_nonneg (hstrip x).1]
    exact (hstrip x).2
  have hdiff : ∀ x, DifferentiableAt ℝ f x := by
    intro x
    exact (wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
      p hM hT u₀ hsmall z hz x).differentiableAt
  intro x
  exact deriv_abs_le_of_bounded_of_deriv_holder hH heta0
    hbound hdiff hholder x

/-- Product-rule derivative of the physical whole-line chemotaxis flux. -/
theorem wholeLineChemotaxisFlux_hasDerivAt
    (p : CMParams) {u : ℝ → ℝ} {x ux : ℝ}
    (hu : IsCUnifBdd u) (hu0 : ∀ y, 0 ≤ u y)
    (hux : HasDerivAt u ux x) :
    HasDerivAt (wholeLineChemotaxisFlux p u)
      (p.m * (u x) ^ (p.m - 1) * ux * deriv (frozenElliptic p u) x +
        (u x) ^ p.m * (frozenElliptic p u x - (u x) ^ p.γ)) x := by
  have hpow : HasDerivAt (fun y : ℝ => (u y) ^ p.m)
      (ux * p.m * (u x) ^ (p.m - 1)) x :=
    hux.rpow_const (Or.inr p.hm)
  have hresolver : HasDerivAt (deriv (frozenElliptic p u))
      (deriv (deriv (frozenElliptic p u)) x) x :=
    (frozenElliptic_deriv_differentiableAt p hu hu0 x).hasDerivAt
  have hmul := hpow.mul hresolver
  have hode := frozenElliptic_deriv_deriv_eq p hu hu0 x
  convert hmul using 1
  rw [hode]
  ring

/-- Once the clamp is inactive, the actual flux-source slice is genuinely
differentiable and obeys the physical product/elliptic derivative formula. -/
theorem wholeLineCauchyFluxSourceTrajectory_slice_hasDerivAt_positive
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1)
    (hstrip : ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) (x : ℝ) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    HasDerivAt
      (wholeLineCauchyFluxSourceTrajectory p hM hT U z.1).1
      (p.m * ((U z).1 x) ^ (p.m - 1) * deriv (U z).1 x *
          deriv (frozenElliptic p (U z).1) x +
        ((U z).1 x) ^ p.m *
          (frozenElliptic p (U z).1 x - ((U z).1 x) ^ p.γ)) x := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  have hext : wholeLineBUCTrajectoryExtend hT U z.1 = U z :=
    wholeLineBUCTrajectoryExtend_eq hT U z.2
  have hfluxEq :
      (wholeLineCauchyFluxSourceTrajectory p hM hT U z.1).1 =
        wholeLineChemotaxisFlux p (U z).1 := by
    funext y
    simpa [wholeLineCauchyFluxSourceTrajectory, hext] using congrFun
      (wholeLineCauchyTruncatedFlux_eq_of_mem_Icc p hM hstrip) y
  have huDeriv : HasDerivAt (U z).1 (deriv (U z).1 x) x := by
    exact (wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
      p hM hT u₀ hsmall z hz x).differentiableAt.hasDerivAt
  rw [hfluxEq]
  exact wholeLineChemotaxisFlux_hasDerivAt p
    (WholeLineBUC.isCUnifBdd (U z)) (fun y => (hstrip y).1) huDeriv

/-- The differentiated physical flux has some positive global Holder
exponent.  For `m=1` the coefficient `u^(m-1)` is constant.  For `m>1` the
output exponent is lowered below both the population exponent and `m-1`,
which handles the fractional range `1<m<2` at `u=0`. -/
theorem wholeLineCauchyFluxSourceTrajectory_slice_deriv_holder_positive
    (p : CMParams) {M T theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) :
    ∃ rho H : ℝ, 0 < rho ∧ rho < 1 ∧ 0 ≤ H ∧ ∀ x y,
      |deriv
          (wholeLineCauchyFluxSourceTrajectory p hM hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) z.1).1 x -
        deriv
          (wholeLineCauchyFluxSourceTrajectory p hM hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) z.1).1 y| ≤
        H * |x - y| ^ rho := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let f : ℝ → ℝ := (U z).1
  let V : ℝ → ℝ := frozenElliptic p f
  let F : ℝ → ℝ :=
    (wholeLineCauchyFluxSourceTrajectory p hM hT U z.1).1
  have hfIs : IsCUnifBdd f := WholeLineBUC.isCUnifBdd (U z)
  have hf0 : ∀ x, 0 ≤ f x := fun x => (hstrip x).1
  have hfM : ∀ x, f x ∈ Set.Icc (0 : ℝ) M := hstrip
  rcases wholeLineCauchyBUCMildFixedPoint_spatial_deriv_Ceta
      p hM hT u₀ hsmall z hz htheta0 htheta1 heta0 heta1 hrel with
    ⟨Hux, hHux, huxHolder⟩
  rcases wholeLineCauchyBUCMildFixedPoint_spatial_deriv_bounded_positive
      p hM hT u₀ hsmall z hz htheta0 htheta1 heta0 heta1 hrel hstrip with
    ⟨Bux, hBux, huxBound⟩
  have hfdiff : ∀ x, DifferentiableAt ℝ f x := by
    intro x
    exact (wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
      p hM hT u₀ hsmall z hz x).differentiableAt
  have hfLip : ∀ x y, |f x - f y| ≤ Bux * |x - y| := by
    intro x y
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Set.univ) (f := f) (C := Bux)
      (fun q _ => hfdiff q)
      (fun q _ => by rw [Real.norm_eq_abs]; exact huxBound q)
      convex_univ (Set.mem_univ x) (Set.mem_univ y)
    simpa [Real.norm_eq_abs, abs_sub_comm] using hmv
  by_cases hmEq : p.m = 1
  · let rho : ℝ := eta
    have hrho0 : 0 < rho := heta0
    have hrho1 : rho < 1 := heta1
    let hU : WholeLineCauchyHolderQuant rho f :=
      wholeLineCauchyHolderQuant_of_lipschitz hM hBux hrho0 hrho1.le
        (fun x => by rw [abs_of_nonneg (hf0 x)]; exact (hfM x).2) hfLip
    let hUxEta : WholeLineCauchyHolderQuant eta (deriv f) :=
      { C := Bux
        H := Hux
        C_nonneg := hBux
        H_nonneg := hHux
        bound := huxBound
        holder := huxHolder }
    let hUx : WholeLineCauchyHolderQuant rho (deriv f) := hUxEta
    let Mγ : ℝ := M ^ p.γ
    have hMγ : 0 ≤ Mγ := by dsimp [Mγ]; positivity
    have hV0 : ∀ x, 0 ≤ V x := fun x => frozenElliptic_nonneg p hf0 x
    have hVM : ∀ x, V x ≤ Mγ := by
      intro x
      exact frozenElliptic_le_of_rpow_le p hMγ hfIs.1 hf0
        (fun y => Real.rpow_le_rpow (hfM y).1 (hfM y).2
          (zero_le_one.trans p.hγ)) x
    have hVxBound : ∀ x, |deriv V x| ≤ Mγ := by
      intro x
      exact frozenElliptic_deriv_abs_le_rpow_of_Icc p hM hfIs hfM x
    have hVxLip : ∀ x y, |deriv V x - deriv V y| ≤
        (2 * Mγ) * |x - y| := by
      intro x y
      have h := (frozenElliptic_deriv_lipschitz_of_Icc p hM hfIs hfM).dist_le_mul x y
      rw [Real.dist_eq, Real.dist_eq,
        Real.coe_toNNReal _ (mul_nonneg (by norm_num) hMγ)] at h
      exact h
    let hVx : WholeLineCauchyHolderQuant rho (deriv V) :=
      wholeLineCauchyHolderQuant_of_lipschitz hMγ
        (mul_nonneg (by norm_num) hMγ) hrho0 hrho1.le hVxBound hVxLip
    have hVLip : ∀ x y, |V x - V y| ≤ Mγ * |x - y| := by
      intro x y
      have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
        (s := Set.univ) (f := V) (C := Mγ)
        (fun q _ => frozenElliptic_differentiable p hfIs hf0 q)
        (fun q _ => by rw [Real.norm_eq_abs]; exact hVxBound q)
        convex_univ (Set.mem_univ x) (Set.mem_univ y)
      simpa [Real.norm_eq_abs, abs_sub_comm] using hmv
    let hV : WholeLineCauchyHolderQuant rho V :=
      wholeLineCauchyHolderQuant_of_lipschitz hMγ hMγ hrho0 hrho1.le
        (fun x => by rw [abs_of_nonneg (hV0 x)]; exact hVM x) hVLip
    let hUm := hU.rpowOfOneLe p.hm hM hfM
    let hUg := hU.rpowOfOneLe p.hγ hM hfM
    let hUq : WholeLineCauchyHolderQuant rho
        (fun x => (f x) ^ (p.m - 1)) :=
      { C := 1
        H := 0
        C_nonneg := by norm_num
        H_nonneg := le_rfl
        bound := by intro x; simp [hmEq]
        holder := by intro x y; simp [hmEq] }
    let hA := ((hUq.mul hUx).mul hVx).const_mul (a := p.m)
    let hB := hUm.mul (hV.sub hUg)
    let hQ := hA.add hB
    have hformula : ∀ x, deriv F x =
        p.m * (f x) ^ (p.m - 1) * deriv f x * deriv V x +
          (f x) ^ p.m * (V x - (f x) ^ p.γ) := by
      intro x
      exact (wholeLineCauchyFluxSourceTrajectory_slice_hasDerivAt_positive
        p hM hT u₀ hsmall z hz hstrip x).deriv
    refine ⟨rho, hQ.H, hrho0, hrho1, hQ.H_nonneg, ?_⟩
    intro x y
    rw [hformula x, hformula y]
    simpa [hQ, hA, hB, hUq, hUx, hUxEta, hVx, hV, hUm, hUg,
      hU, f, V, mul_assoc] using hQ.holder x y
  · have hmgt : 1 < p.m := lt_of_le_of_ne p.hm (Ne.symm hmEq)
    have hmq : 0 < p.m - 1 := by linarith
    let rho : ℝ := min eta (p.m - 1) / 2
    have hmin0 : 0 < min eta (p.m - 1) := lt_min heta0 hmq
    have hrho0 : 0 < rho := by dsimp [rho]; linarith
    have hrhoEta : rho ≤ eta := by
      dsimp [rho]
      linarith [min_le_left eta (p.m - 1)]
    have hrhoQ : rho ≤ p.m - 1 := by
      dsimp [rho]
      linarith [min_le_right eta (p.m - 1)]
    have hrho1 : rho < 1 := lt_of_le_of_lt hrhoEta heta1
    let hU : WholeLineCauchyHolderQuant rho f :=
      wholeLineCauchyHolderQuant_of_lipschitz hM hBux hrho0 hrho1.le
        (fun x => by rw [abs_of_nonneg (hf0 x)]; exact (hfM x).2) hfLip
    let hUxEta : WholeLineCauchyHolderQuant eta (deriv f) :=
      { C := Bux
        H := Hux
        C_nonneg := hBux
        H_nonneg := hHux
        bound := huxBound
        holder := huxHolder }
    let hUx := hUxEta.lowerExponent hrho0 hrhoEta
    let Mγ : ℝ := M ^ p.γ
    have hMγ : 0 ≤ Mγ := by dsimp [Mγ]; positivity
    have hV0 : ∀ x, 0 ≤ V x := fun x => frozenElliptic_nonneg p hf0 x
    have hVM : ∀ x, V x ≤ Mγ := by
      intro x
      exact frozenElliptic_le_of_rpow_le p hMγ hfIs.1 hf0
        (fun y => Real.rpow_le_rpow (hfM y).1 (hfM y).2
          (zero_le_one.trans p.hγ)) x
    have hVxBound : ∀ x, |deriv V x| ≤ Mγ := by
      intro x
      exact frozenElliptic_deriv_abs_le_rpow_of_Icc p hM hfIs hfM x
    have hVxLip : ∀ x y, |deriv V x - deriv V y| ≤
        (2 * Mγ) * |x - y| := by
      intro x y
      have h := (frozenElliptic_deriv_lipschitz_of_Icc p hM hfIs hfM).dist_le_mul x y
      rw [Real.dist_eq, Real.dist_eq,
        Real.coe_toNNReal _ (mul_nonneg (by norm_num) hMγ)] at h
      exact h
    let hVx : WholeLineCauchyHolderQuant rho (deriv V) :=
      wholeLineCauchyHolderQuant_of_lipschitz hMγ
        (mul_nonneg (by norm_num) hMγ) hrho0 hrho1.le hVxBound hVxLip
    have hVLip : ∀ x y, |V x - V y| ≤ Mγ * |x - y| := by
      intro x y
      have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
        (s := Set.univ) (f := V) (C := Mγ)
        (fun q _ => frozenElliptic_differentiable p hfIs hf0 q)
        (fun q _ => by rw [Real.norm_eq_abs]; exact hVxBound q)
        convex_univ (Set.mem_univ x) (Set.mem_univ y)
      simpa [Real.norm_eq_abs, abs_sub_comm] using hmv
    let hV : WholeLineCauchyHolderQuant rho V :=
      wholeLineCauchyHolderQuant_of_lipschitz hMγ hMγ hrho0 hrho1.le
        (fun x => by rw [abs_of_nonneg (hV0 x)]; exact hVM x) hVLip
    let hUm := hU.rpowOfOneLe p.hm hM hfM
    let hUg := hU.rpowOfOneLe p.hγ hM hfM
    rcases wholeLine_rpow_holder_of_nonneg_bounded_lipschitz
        hM hBux hmq hrho0 hrho1.le hrhoQ hfM hfLip with
      ⟨HUq, hHUq, hUqHolder⟩
    let hUq : WholeLineCauchyHolderQuant rho
        (fun x => (f x) ^ (p.m - 1)) :=
      { C := M ^ (p.m - 1)
        H := HUq
        C_nonneg := Real.rpow_nonneg hM _
        H_nonneg := hHUq
        bound := by
          intro x
          rw [abs_of_nonneg (Real.rpow_nonneg (hfM x).1 _)]
          exact Real.rpow_le_rpow (hfM x).1 (hfM x).2 hmq.le
        holder := hUqHolder }
    let hA := ((hUq.mul hUx).mul hVx).const_mul (a := p.m)
    let hB := hUm.mul (hV.sub hUg)
    let hQ := hA.add hB
    have hformula : ∀ x, deriv F x =
        p.m * (f x) ^ (p.m - 1) * deriv f x * deriv V x +
          (f x) ^ p.m * (V x - (f x) ^ p.γ) := by
      intro x
      exact (wholeLineCauchyFluxSourceTrajectory_slice_hasDerivAt_positive
        p hM hT u₀ hsmall z hz hstrip x).deriv
    refine ⟨rho, hQ.H, hrho0, hrho1, hQ.H_nonneg, ?_⟩
    intro x y
    rw [hformula x, hformula y]
    simpa [hQ, hA, hB, hUq, hUx, hUxEta, hVx, hV, hUm, hUg,
      hU, f, V, mul_assoc] using hQ.holder x y

section WholeLineCauchyFluxC1BootstrapAxiomAudit

#print axioms deriv_abs_le_of_bounded_of_deriv_holder
#print axioms wholeLineCauchyBUCMildFixedPoint_spatial_deriv_bounded_positive
#print axioms wholeLineChemotaxisFlux_hasDerivAt
#print axioms wholeLineCauchyFluxSourceTrajectory_slice_hasDerivAt_positive
#print axioms wholeLineCauchyFluxSourceTrajectory_slice_deriv_holder_positive

end WholeLineCauchyFluxC1BootstrapAxiomAudit

end ShenWork.Paper1
