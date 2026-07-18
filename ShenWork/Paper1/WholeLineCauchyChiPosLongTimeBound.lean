import ShenWork.Paper1.WholeLineCauchyLongTimeBound
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open Filter Function MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# χ>0 eventual pointwise ceiling — relaxing barrier to MChi

For χ>0 in the critical case α = m+γ-1, the ceiling function
`MChi + (C - MChi) * exp(-α * t)` is a supersolution of the reaction
ODE at a spatial maximum. This gives `limsup sup_x u(t,x) ≤ MChi`.

The proof follows the constructive approach:
1. Define `wholeLineCauchyChiPosCeiling p C t := MChi p + (C - MChi p) * exp(-p.α * t)`
2. Show it is a supersolution via the Bernoulli inequality for rpow
3. Apply the slab maximum principle to get u ≤ ceiling on each slab
4. Chain to get the global bound
5. Take limsup to get UniformLimsupLe MChi
-/

/-- The χ>0 relaxing ceiling: decays exponentially from C to MChi at rate α. -/
def wholeLineCauchyChiPosCeiling (p : CMParams) (C t : ℝ) : ℝ :=
  MChi p + (C - MChi p) * Real.exp (-p.α * t)

theorem wholeLineCauchyChiPosCeiling_zero (p : CMParams) (C : ℝ) :
    wholeLineCauchyChiPosCeiling p C 0 = C := by
  simp [wholeLineCauchyChiPosCeiling]

theorem wholeLineCauchyChiPosCeiling_hasDerivAt (p : CMParams) (C t : ℝ) :
    HasDerivAt (wholeLineCauchyChiPosCeiling p C)
      (-p.α * (C - MChi p) * Real.exp (-p.α * t)) t := by
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-p.α * s))
      (-p.α * Real.exp (-p.α * t)) t := by
    have := (hasDerivAt_id t).const_mul (-p.α) |>.exp
    simp only [id] at this
    convert this using 1; ring
  convert (hasDerivAt_const t (MChi p)).add (hexp.const_mul (C - MChi p)) using 1 <;> ring

theorem wholeLineCauchyChiPosCeiling_deriv_eq
    (p : CMParams) (C t : ℝ) :
    deriv (wholeLineCauchyChiPosCeiling p C) t =
      -p.α * (wholeLineCauchyChiPosCeiling p C t - MChi p) := by
  rw [(wholeLineCauchyChiPosCeiling_hasDerivAt p C t).deriv]
  simp [wholeLineCauchyChiPosCeiling]
  ring

theorem wholeLineCauchyChiPosCeiling_MChi_le
    {p : CMParams} {C : ℝ} (hC : MChi p ≤ C) (t : ℝ) :
    MChi p ≤ wholeLineCauchyChiPosCeiling p C t := by
  unfold wholeLineCauchyChiPosCeiling
  have hmul : 0 ≤ (C - MChi p) * Real.exp (-p.α * t) :=
    mul_nonneg (sub_nonneg.mpr hC) (Real.exp_nonneg _)
  linarith

theorem wholeLineCauchyChiPosCeiling_le
    {p : CMParams} {C t : ℝ} (hC : MChi p ≤ C) (ht : 0 ≤ t) :
    wholeLineCauchyChiPosCeiling p C t ≤ C := by
  have hexp : Real.exp (-p.α * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [p.hα]
  unfold wholeLineCauchyChiPosCeiling
  nlinarith [sub_nonneg.mpr hC, Real.exp_pos (-p.α * t)]

theorem wholeLineCauchyChiPosCeiling_restart (p : CMParams) (C a s : ℝ) :
    wholeLineCauchyChiPosCeiling p (wholeLineCauchyChiPosCeiling p C a) s =
      wholeLineCauchyChiPosCeiling p C (a + s) := by
  simp only [wholeLineCauchyChiPosCeiling]
  have hexp : Real.exp (-p.α * a) * Real.exp (-p.α * s) = Real.exp (-p.α * (a + s)) := by
    rw [← Real.exp_add]; ring_nf
  have : (C - MChi p) * Real.exp (-p.α * a) * Real.exp (-p.α * s) =
         (C - MChi p) * Real.exp (-p.α * (a + s)) := by
    rw [mul_assoc, hexp]
  linarith

/-- Bernoulli inequality for rpow: for r ≥ 1 and n ≥ 2, r^n ≥ n*r - (n-1).
Proved via convexity of x^n and the tangent line bound at x = 1. -/
theorem rpow_bernoulli {r n : ℝ} (hr : 1 ≤ r) (hn : 2 ≤ n) :
    n * r - (n - 1) ≤ r ^ n := by
  by_cases hrr : r = 1
  · subst hrr; simp [Real.one_rpow]
  have hr1 : 1 < r := lt_of_le_of_ne hr (Ne.symm hrr)
  have hn1 : 1 ≤ n := le_trans (by norm_num : (1 : ℝ) ≤ 2) hn
  have hconv := convexOn_rpow hn1
  have h1mem : (1 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr zero_le_one
  have hrmem : r ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (zero_le_one.trans hr)
  have hderiv : HasDerivAt (fun x : ℝ => x ^ n) (n * 1 ^ (n - 1)) 1 :=
    hasDerivAt_rpow_const (Or.inl one_ne_zero)
  rw [Real.one_rpow, mul_one] at hderiv
  have hslope := hconv.le_slope_of_hasDerivAt h1mem hrmem hr1 hderiv
  simp only [Real.one_rpow, slope_def_field] at hslope
  have hr_pos : 0 < r - 1 := sub_pos.mpr hr1
  rw [le_div_iff₀ hr_pos] at hslope
  linarith

/-- The supersolution property for the χ>0 ceiling at the ceiling value.
For B ≥ MChi (with (1-χ)MChi^α = 1):
  B(1 - (1-χ)B^α) + α(B - MChi) ≤ 0
i.e., the ceiling reaction + ceiling derivative ≤ 0. -/
theorem chiPosCeiling_supersolution
    {p : CMParams} (hχ_pos : 0 < p.χ) (hχ_lt : p.χ < 1)
    (halpha : p.α = p.m + p.γ - 1) {B : ℝ} (hB : MChi p ≤ B) :
    B * (1 - (1 - p.χ) * B ^ p.α) + p.α * (B - MChi p) ≤ 0 := by
  have hα_pos : 0 < p.α := by linarith [p.hα]
  have hMChi_pos : 0 < MChi p := MChi_pos_of_chi_lt_one p hχ_lt
  have hMChi_nonneg : 0 ≤ MChi p := hMChi_pos.le
  have hB_pos : 0 < B := lt_of_lt_of_le hMChi_pos hB
  have hone_chi : 0 < 1 - p.χ := by linarith
  have hMChi_rpow : (1 - p.χ) * (MChi p) ^ p.α = 1 := by
    rw [MChi_eq_rpow_of_chi_pos p hχ_pos]
    have hbase : 0 ≤ 1 / (1 - p.χ) := div_nonneg one_pos.le hone_chi.le
    rw [← Real.rpow_mul hbase, div_mul_cancel₀ 1 (ne_of_gt hα_pos)]
    rw [Real.rpow_one]
    field_simp
  set r := B / MChi p with hr_def
  have hr1 : 1 ≤ r := le_div_iff₀ hMChi_pos |>.mpr (by linarith)
  have hB_eq : B = MChi p * r := by rw [hr_def]; field_simp
  rw [hB_eq]
  have hα1 : 2 ≤ p.α + 1 := by linarith [p.hα]
  have hBα : (MChi p * r) ^ p.α = (MChi p) ^ p.α * r ^ p.α :=
    Real.mul_rpow hMChi_nonneg (zero_le_one.trans hr1)
  rw [hBα, ← mul_assoc (1 - p.χ), hMChi_rpow]
  -- Target: MChi*r * (1 - r^α) + α*(MChi*r - MChi) ≤ 0
  -- = MChi * [(α+1)*r - α - r^{α+1}] ≤ 0
  -- Bernoulli: (α+1)*r - α ≤ r^{α+1}
  have hkey := rpow_bernoulli hr1 hα1
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hrα1 : r ^ p.α * r = r ^ (p.α + 1) := by
    conv_rhs => rw [show p.α + 1 = p.α + (1 : ℝ) from rfl]
    rw [Real.rpow_add hr_pos, Real.rpow_one]
  nlinarith [hMChi_pos]

/-! ### Effective reaction Lipschitz bound

For the χ>0 slab principle, we bound the effective reaction
`f(s) = s*(1 - (1-χ)*s^α)` minus the ceiling value using the rpow Lipschitz
constant and the supersolution property.
-/

/-- The effective reaction Lipschitz constant on [0, A]. -/
def effectiveReactionLip (p : CMParams) (A : ℝ) : ℝ :=
  1 + (p.α + 1) * A ^ p.α

theorem effectiveReactionLip_nonneg {p : CMParams} {A : ℝ} (hA : 0 ≤ A) :
    0 ≤ effectiveReactionLip p A := by
  unfold effectiveReactionLip
  have : 0 ≤ (p.α + 1) * A ^ p.α :=
    mul_nonneg (by linarith [p.hα]) (Real.rpow_nonneg hA _)
  linarith

/-- The effective reaction difference bound for the w < 0 case:
  f(u) - f(B) ≤ effectiveReactionLip * (B - u) for u ≤ B ∈ [0, A]. -/
theorem effectiveReaction_sub_le
    {p : CMParams} (hχ_nonneg : 0 ≤ p.χ) (hχ_lt : p.χ < 1)
    {u B A : ℝ} (hu : 0 ≤ u) (huB : u ≤ B) (hBA : B ≤ A) (hA : 0 ≤ A) :
    u * (1 - (1 - p.χ) * u ^ p.α) - B * (1 - (1 - p.χ) * B ^ p.α) ≤
      effectiveReactionLip p A * (B - u) := by
  have hone_chi : 0 ≤ 1 - p.χ := by linarith
  have hchi_le : 1 - p.χ ≤ 1 := by linarith
  have hα1 : 1 ≤ p.α + 1 := by linarith [p.hα]
  have huA : u ≤ A := huB.trans hBA
  have humα : u * u ^ p.α = u ^ (p.α + 1) := by
    by_cases hu0 : u = 0
    · subst hu0; simp [Real.zero_rpow (by linarith [p.hα] : p.α + 1 ≠ 0)]
    · have := Real.rpow_add (lt_of_le_of_ne hu (Ne.symm hu0)) p.α 1
      rw [Real.rpow_one] at this; linarith
  have hBmα : B * B ^ p.α = B ^ (p.α + 1) := by
    by_cases hB0 : B = 0
    · subst hB0; simp [Real.zero_rpow (by linarith [p.hα] : p.α + 1 ≠ 0)]
    · have := Real.rpow_add (lt_of_le_of_ne (hu.trans huB) (Ne.symm hB0)) p.α 1
      rw [Real.rpow_one] at this; linarith
  have hLip := (rpow_m_lipschitz_on_Icc hα1 hA).dist_le_mul
    u ⟨hu, huA⟩ B ⟨hu.trans huB, hBA⟩
  rw [Real.coe_toNNReal _ (rpowLip_nonneg hα1 hA)] at hLip
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr
    (Real.rpow_le_rpow hu huB (by linarith [p.hα]))),
    Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr huB)] at hLip
  simp only [neg_sub] at hLip
  -- hLip : B^{α+1} - u^{α+1} ≤ rpowLip(α+1, A) * (B - u)
  have hBu : 0 ≤ B - u := sub_nonneg.mpr huB
  have hLipBu : 0 ≤ rpowLip (p.α + 1) A * (B - u) :=
    mul_nonneg (rpowLip_nonneg hα1 hA) hBu
  calc u * (1 - (1 - p.χ) * u ^ p.α) - B * (1 - (1 - p.χ) * B ^ p.α)
      = (u - B) + (1 - p.χ) * (B ^ (p.α + 1) - u ^ (p.α + 1)) := by
        rw [← humα, ← hBmα]; ring
    _ ≤ 0 + rpowLip (p.α + 1) A * (B - u) := by
        have h1 : u - B ≤ 0 := sub_nonpos.mpr huB
        have h2 : (1 - p.χ) * (B ^ (p.α + 1) - u ^ (p.α + 1)) ≤
            (1 - p.χ) * (rpowLip (p.α + 1) A * (B - u)) :=
          mul_le_mul_of_nonneg_left hLip hone_chi
        have h3 : (1 - p.χ) * (rpowLip (p.α + 1) A * (B - u)) ≤
            1 * (rpowLip (p.α + 1) A * (B - u)) :=
          mul_le_mul_of_nonneg_right hchi_le hLipBu
        linarith
    _ = rpowLip (p.α + 1) A * (B - u) := by ring
    _ ≤ effectiveReactionLip p A * (B - u) := by
        have hRpowLipLe : rpowLip (p.α + 1) A ≤ effectiveReactionLip p A := by
          unfold effectiveReactionLip rpowLip
          have : (p.α + 1) - 1 = p.α := by ring
          rw [this]; linarith
        exact mul_le_mul_of_nonneg_right hRpowLipLe hBu

/-! ### Slab maximum principle for χ>0

Core theorem: the solution u on a time slab [0,T] is bounded above by the
relaxing ceiling MChi + (C - MChi)*exp(-α*t), provided:
- χ > 0, χ < 1, α = m + γ - 1 (critical case)
- u ≥ 0, u ≤ A on the slab
- u(0,·) ≤ C with MChi ≤ C
- u satisfies the PDE with reaction + chemotaxis
-/

theorem wholeLineSlab_le_chiPosCeiling_of_positive_resolver_pde
    (p : CMParams) (hχ_pos : 0 < p.χ) (hχ_lt : p.χ < 1)
    (halpha : p.α = p.m + p.γ - 1)
    {T C A : ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0 < T) (hC : MChi p ≤ C)
    (hcont : Continuous (fun q : ℝ × ℝ => u q.1 q.2))
    (hnonneg : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 ≤ u t x)
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, u t x ≤ A)
    (hinit : ∀ x, u 0 x ≤ C)
    (htime : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => u s x)
        (deriv (fun s : ℝ => u s x) t) t)
    (hspace1 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => u t y)
        (deriv (fun y : ℝ => u t y) x) x)
    (hspace2 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => u t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x) x)
    (hpde : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      deriv (fun s : ℝ => u s x) t =
        deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x -
          p.χ *
            (p.m * (u t x) ^ (p.m - 1) *
                deriv (fun y : ℝ => u t y) x *
                deriv (frozenElliptic p (u t)) x +
              (u t x) ^ p.m *
                (frozenElliptic p (u t) x - (u t x) ^ p.γ)) +
          reactionFun p.α (u t x)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      u t x ≤ wholeLineCauchyChiPosCeiling p C t := by
  let B : ℝ → ℝ := wholeLineCauchyChiPosCeiling p C
  let w : ℝ → ℝ → ℝ := fun t x => u t x - B t
  have hA0 : 0 ≤ A := by
    linarith [hnonneg 0 ⟨le_rfl, hT.le⟩ 0,
      hupper 0 ⟨le_rfl, hT.le⟩ 0]
  have hα_pos : 0 < p.α := by linarith [p.hα]
  have hMChi_pos : 0 < MChi p := MChi_pos_of_chi_lt_one p hχ_lt
  have hC0 : 0 ≤ C := (hMChi_pos.le).trans hC
  have hBMChi : ∀ t, MChi p ≤ B t := fun t => wholeLineCauchyChiPosCeiling_MChi_le hC t
  have hBC : ∀ t ∈ Set.Icc (0 : ℝ) T, B t ≤ C := by
    intro t ht
    exact wholeLineCauchyChiPosCeiling_le hC ht.1
  have hcontw : Continuous (fun q : ℝ × ℝ => w q.1 q.2) := by
    have hBcont : Continuous B := by
      show Continuous fun t =>
        MChi p + (C - MChi p) * Real.exp (-p.α * t)
      fun_prop
    exact hcont.sub (hBcont.comp continuous_fst)
  have hupperw : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, w t x ≤ A := by
    intro t ht x; dsimp [w]
    linarith [hupper t ht x, hBMChi t]
  have hinitw : ∀ x, w 0 x ≤ 0 := by
    intro x
    simpa [w, B, wholeLineCauchyChiPosCeiling_zero] using hinit x
  have hBderiv : ∀ t, HasDerivAt B (-p.α * (B t - MChi p)) t := by
    intro t
    have := wholeLineCauchyChiPosCeiling_hasDerivAt p C t
    convert this using 1
    simp [B, wholeLineCauchyChiPosCeiling]; ring
  have hdtw : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => w s x)
        (deriv (fun s : ℝ => u s x) t + p.α * (B t - MChi p)) t := by
    intro t x ht; dsimp [w]
    convert (htime ht).sub (hBderiv t) using 1; ring
  have htimew : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => w s x)
        (deriv (fun s : ℝ => w s x) t) t := by
    intro t x ht
    exact (hdtw ht).differentiableAt.hasDerivAt
  have hspace1w : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => w t y)
        (deriv (fun y : ℝ => w t y) x) x := by
    intro t x ht
    have hd := (hspace1 (t := t) (x := x) ht).sub_const (B t)
    simpa [w] using hd.differentiableAt.hasDerivAt
  have hderivw : ∀ t,
      (fun y : ℝ => deriv (fun z : ℝ => w t z) y) =
        fun y : ℝ => deriv (fun z : ℝ => u t z) y := by
    intro t; funext y; simp [w, deriv_sub_const]
  have hspace2w : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => w t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => w t z) y) x) x := by
    intro t x ht; rw [hderivw]; exact hspace2 ht
  let L : ℝ := wholeLineSlabSup T w
  let K : ℝ := p.χ * p.m * A ^ (p.m - 1) * A ^ p.γ
  let R : ℝ := max C A
  have hR0 : 0 ≤ R := le_max_of_le_left hC0
  let Kreact : ℝ := effectiveReactionLip p R
  let G : ℝ → ℝ := fun r =>
    Kreact * max (-r) 0 - p.α * max r 0
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (mul_nonneg hχ_pos.le
      (zero_le_one.trans p.hm)) (Real.rpow_nonneg hA0 _))
      (Real.rpow_nonneg hA0 _)
  have hKreact : 0 ≤ Kreact := effectiveReactionLip_nonneg hR0
  have hGcont : Continuous G := by dsimp [G]; fun_prop
  have hGstrict : 0 < wholeLineSlabSup T w →
      G (wholeLineSlabSup T w) < 0 := by
    intro hL
    have hL0 : 0 ≤ L := hL.le
    have hnegL : -L ≤ 0 := neg_nonpos.mpr hL0
    dsimp [G]
    rw [max_eq_right hnegL, max_eq_left hL0]
    simp [L]
    exact mul_pos hα_pos hL
  have hpdew : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      deriv (fun s : ℝ => w s x) t ≤
        deriv (fun y : ℝ => deriv (fun z : ℝ => w t z) y) x +
          K * |deriv (fun y : ℝ => w t y) x| + G (w t x) := by
    intro t x ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
    have hu0 : 0 ≤ u t x := hnonneg t htIcc x
    have huA : u t x ≤ A := hupper t htIcc x
    have hwL : w t x ≤ L := le_wholeLineSlabSup hT.le hupperw htIcc x
    have hsliceCont : Continuous (u t) :=
      hcont.comp (continuous_const.prodMk continuous_id)
    -- Step 1: gradient drift bound
    have hvxA : |deriv (frozenElliptic p (u t)) x| ≤ A ^ p.γ := by
      have hvA : frozenElliptic p (u t) x ≤ A ^ p.γ :=
        frozenElliptic_le_of_rpow_le p (Real.rpow_nonneg hA0 _) hsliceCont
          (hnonneg t htIcc) (fun y => Real.rpow_le_rpow (hnonneg t htIcc y)
            (hupper t htIcc y) (zero_le_one.trans p.hγ)) x
      exact (frozenElliptic_deriv_abs_le p
        ⟨hsliceCont, ⟨A, fun y => by
          rw [abs_of_nonneg (hnonneg t htIcc y)]; exact hupper t htIcc y⟩⟩
        (hnonneg t htIcc) x).trans hvA
    have humA : (u t x) ^ (p.m - 1) ≤ A ^ (p.m - 1) :=
      Real.rpow_le_rpow hu0 huA (sub_nonneg.mpr p.hm)
    have hdrift :
        -(p.χ * (p.m * (u t x) ^ (p.m - 1) *
            deriv (fun y : ℝ => u t y) x *
            deriv (frozenElliptic p (u t)) x)) ≤
          K * |deriv (fun y : ℝ => u t y) x| := by
      calc
        -(p.χ * (p.m * (u t x) ^ (p.m - 1) *
              deriv (fun y : ℝ => u t y) x *
              deriv (frozenElliptic p (u t)) x))
            ≤ |p.χ * (p.m * (u t x) ^ (p.m - 1) *
              deriv (fun y : ℝ => u t y) x *
              deriv (frozenElliptic p (u t)) x)| :=
              (le_abs_self _).trans_eq (abs_neg _)
        _ = p.χ * p.m * (u t x) ^ (p.m - 1) *
              |deriv (fun y : ℝ => u t y) x| *
              |deriv (frozenElliptic p (u t)) x| := by
              rw [abs_mul, abs_mul, abs_mul, abs_mul,
                abs_of_pos hχ_pos,
                abs_of_nonneg (zero_le_one.trans p.hm),
                abs_of_nonneg (Real.rpow_nonneg hu0 _)]
              ring
        _ ≤ K * |deriv (fun y : ℝ => u t y) x| := by
              dsimp [K]
              have hux0 : 0 ≤ |deriv (fun y : ℝ => u t y) x| := abs_nonneg _
              have huv :
                  (u t x) ^ (p.m - 1) *
                      |deriv (frozenElliptic p (u t)) x| ≤
                    A ^ (p.m - 1) * A ^ p.γ :=
                mul_le_mul humA hvxA (abs_nonneg _)
                  (Real.rpow_nonneg hA0 _)
              have hcoef : 0 ≤ p.χ * p.m :=
                mul_nonneg hχ_pos.le (zero_le_one.trans p.hm)
              calc
                p.χ * p.m * (u t x) ^ (p.m - 1) *
                      |deriv (fun y : ℝ => u t y) x| *
                      |deriv (frozenElliptic p (u t)) x|
                    = (p.χ * p.m) *
                        |deriv (fun y : ℝ => u t y) x| *
                        ((u t x) ^ (p.m - 1) *
                          |deriv (frozenElliptic p (u t)) x|) := by ring
                _ ≤ (p.χ * p.m) *
                        |deriv (fun y : ℝ => u t y) x| *
                        (A ^ (p.m - 1) * A ^ p.γ) :=
                  mul_le_mul_of_nonneg_left huv (mul_nonneg hcoef hux0)
                _ = p.χ * p.m * A ^ (p.m - 1) * A ^ p.γ *
                      |deriv (fun y : ℝ => u t y) x| := by ring
    -- Step 2: chemotaxis zeroth order is favorable (dropped)
    have hv_nonneg : 0 ≤ frozenElliptic p (u t) x :=
      frozenElliptic_nonneg p (hnonneg t htIcc) x
    have hchem_favorable :
        -(p.χ * ((u t x) ^ p.m *
            (frozenElliptic p (u t) x - (u t x) ^ p.γ))) ≤
          p.χ * (u t x) ^ p.m * (u t x) ^ p.γ := by
      have hum : 0 ≤ (u t x) ^ p.m := Real.rpow_nonneg hu0 _
      have : 0 ≤ p.χ * (u t x) ^ p.m * frozenElliptic p (u t) x :=
        mul_nonneg (mul_nonneg hχ_pos.le hum) hv_nonneg
      nlinarith
    -- Step 3: combine chemotaxis with reaction using α = m+γ-1
    have humγ : (u t x) ^ p.m * (u t x) ^ p.γ = (u t x) ^ (p.m + p.γ) := by
      by_cases hu00 : u t x = 0
      · simp only [hu00, Real.zero_rpow (by linarith [p.hm] : p.m ≠ 0),
          Real.zero_rpow (by linarith [p.hγ] : p.γ ≠ 0),
          Real.zero_rpow (by linarith [p.hm, p.hγ] : p.m + p.γ ≠ 0),
          zero_mul]
      · exact (Real.rpow_add (lt_of_le_of_ne hu0 (Ne.symm hu00)) p.m p.γ).symm
    have hmγα : p.m + p.γ = p.α + 1 := by linarith [halpha]
    have hchiMG : p.χ * (u t x) ^ p.m * (u t x) ^ p.γ =
        p.χ * (u t x) ^ (p.α + 1) := by
      rw [mul_assoc, humγ, hmγα]
    have heff_react :
        p.χ * (u t x) ^ p.m * (u t x) ^ p.γ + reactionFun p.α (u t x) =
          (u t x) * (1 - (1 - p.χ) * (u t x) ^ p.α) := by
      rw [hchiMG]
      unfold reactionFun
      by_cases hu00 : u t x = 0
      · simp only [hu00, Real.zero_rpow (by linarith [p.hα] : p.α ≠ 0),
          Real.zero_rpow (by linarith [p.hα] : p.α + 1 ≠ 0),
          mul_zero, sub_zero, mul_one]
        ring
      · have hu_pos : 0 < u t x := lt_of_le_of_ne hu0 (Ne.symm hu00)
        have huα1 : (u t x) * (u t x) ^ p.α = (u t x) ^ (p.α + 1) := by
          have := Real.rpow_add hu_pos p.α 1
          rw [Real.rpow_one] at this; linarith
        rw [← huα1]; ring
    -- Step 4: reaction bound using supersolution
    have hreaction :
        (u t x) * (1 - (1 - p.χ) * (u t x) ^ p.α) +
          p.α * (B t - MChi p) ≤ G (w t x) := by
      by_cases hw0 : 0 ≤ w t x
      · -- u ≥ B ≥ MChi, so supersolution applies to u
        have huMChi : MChi p ≤ u t x := by dsimp [w] at hw0; linarith [hBMChi t]
        have hsuper := chiPosCeiling_supersolution hχ_pos hχ_lt halpha huMChi
        -- supersolution gives: u*(1-(1-χ)*u^α) + α*(u-MChi) ≤ 0
        -- So: u*(1-(1-χ)*u^α) + α*(B-MChi) = [above] - α*(u-B) ≤ -α*w
        have hcalc :
            (u t x) * (1 - (1 - p.χ) * (u t x) ^ p.α) + p.α * (B t - MChi p)
            = ((u t x) * (1 - (1 - p.χ) * (u t x) ^ p.α) +
                p.α * (u t x - MChi p)) -
              p.α * (u t x - B t) := by ring
        dsimp [G]
        rw [max_eq_right (neg_nonpos.mpr hw0), max_eq_left hw0]
        linarith [hcalc]
      · -- u < B, use Lipschitz bound
        have hwneg : w t x < 0 := lt_of_not_ge hw0
        have huB : u t x ≤ B t := by dsimp [w] at hwneg; linarith
        have hBtR : B t ≤ R := (hBC t htIcc).trans (le_max_left C A)
        have hsuper_B := chiPosCeiling_supersolution hχ_pos hχ_lt halpha (hBMChi t)
        have hLip := effectiveReaction_sub_le hχ_pos.le hχ_lt hu0 huB hBtR hR0
        dsimp [G]
        rw [max_eq_left (neg_nonneg.mpr hwneg.le),
          max_eq_right hwneg.le]
        dsimp [w] at hwneg ⊢
        linarith
    -- Assemble the PDE inequality for w
    have hdt : deriv (fun s : ℝ => w s x) t =
        deriv (fun s : ℝ => u s x) t + p.α * (B t - MChi p) := (hdtw ht).deriv
    have hd1 : deriv (fun y : ℝ => w t y) x =
        deriv (fun y : ℝ => u t y) x := by
      simp [w, deriv_sub_const]
    have hd2 : deriv (fun y : ℝ => deriv (fun z : ℝ => w t z) y) x =
        deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x := by
      rw [hderivw]
    rw [hdt, hpde ht, hd1, hd2]
    dsimp [G] at hreaction ⊢
    -- The PDE decomposes as:
    -- uxx + [-χ*gradient*drift] + [-χ*u^m*(v-u^γ)] + reaction + α*(B-MChi)
    -- ≤ wxx + K|wx| + [χ*u^m*u^γ + reaction] + α*(B-MChi)
    -- = wxx + K|wx| + effective_reaction + α*(B-MChi)
    -- ≤ wxx + K|wx| + G(w)
    have hkey :
        -(p.χ * (p.m * (u t x) ^ (p.m - 1) *
            deriv (fun y : ℝ => u t y) x *
            deriv (frozenElliptic p (u t)) x +
          (u t x) ^ p.m *
            (frozenElliptic p (u t) x - (u t x) ^ p.γ))) +
        reactionFun p.α (u t x) + p.α * (B t - MChi p) ≤
          K * |deriv (fun y : ℝ => u t y) x| + G (w t x) := by
      have hsplit :
          -(p.χ * (p.m * (u t x) ^ (p.m - 1) *
              deriv (fun y : ℝ => u t y) x *
              deriv (frozenElliptic p (u t)) x +
            (u t x) ^ p.m *
              (frozenElliptic p (u t) x - (u t x) ^ p.γ)))
          = -(p.χ * (p.m * (u t x) ^ (p.m - 1) *
              deriv (fun y : ℝ => u t y) x *
              deriv (frozenElliptic p (u t)) x)) +
            -(p.χ * ((u t x) ^ p.m *
              (frozenElliptic p (u t) x - (u t x) ^ p.γ))) := by ring
      rw [hsplit]
      have h1 := hdrift
      have h2 := hchem_favorable
      have h3 : p.χ * (u t x) ^ p.m * (u t x) ^ p.γ +
          reactionFun p.α (u t x) + p.α * (B t - MChi p) ≤
          G (w t x) := by
        rw [heff_react]; exact hreaction
      linarith
    linarith
  have hwslab : wholeLineSlabSup T w ≤ 0 :=
    wholeLineSlabSup_le_of_scalar_pde hT hK hcontw hupperw hinitw
      hGcont hGstrict htimew hspace1w hspace2w hpdew
  intro t ht x
  have hwle : w t x ≤ wholeLineSlabSup T w :=
    le_wholeLineSlabSup hT.le hupperw ht x
  dsimp [w, B] at hwle ⊢
  linarith

section AxiomAudit

-- #print axioms effectiveReaction_sub_le
-- #print axioms wholeLineSlab_le_chiPosCeiling_of_positive_resolver_pde

end AxiomAudit

end ShenWork.Paper1
