import ShenWork.Paper1.WaveFrozenEllipticDep

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-- The frozen elliptic values obey the same exponential-kernel difference
bound as their derivatives. -/
theorem frozenElliptic_diff_abs_le
    (p : CMParams) {u v : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ x, 0 ≤ u x)
    (hv : IsCUnifBdd v) (hv_nonneg : ∀ x, 0 ≤ v x) (x : ℝ) :
    |frozenElliptic p u x - frozenElliptic p v x| ≤
      1 / 2 * ∫ y, Real.exp (-|x - y|) *
        |(u y) ^ p.γ - (v y) ^ p.γ| := by
  have hgu : IsCUnifBdd (fun y => (u y) ^ p.γ) :=
    rpow_cunif_bdd_of_nonneg p hu hu_nonneg
  have hgv : IsCUnifBdd (fun y => (v y) ^ p.γ) :=
    rpow_cunif_bdd_of_nonneg p hv hv_nonneg
  have hintu : Integrable
      (fun y => Real.exp (-1 * |x - y|) * (u y) ^ p.γ) :=
    by simpa [Real.sqrt_one] using
      (Psi_kernel_integrable_of_isCUnifBdd one_pos hgu x)
  have hintv : Integrable
      (fun y => Real.exp (-1 * |x - y|) * (v y) ^ p.γ) :=
    by simpa [Real.sqrt_one] using
      (Psi_kernel_integrable_of_isCUnifBdd one_pos hgv x)
  have hdiff :
      frozenElliptic p u x - frozenElliptic p v x =
        1 / 2 * ∫ y, Real.exp (-|x - y|) *
          ((u y) ^ p.γ - (v y) ^ p.γ) := by
    rw [frozenElliptic_eq_kernel_integral,
      frozenElliptic_eq_kernel_integral, ← mul_sub]
    rw [← integral_sub hintu hintv]
    congr 1
    apply integral_congr_ae
    filter_upwards with y
    have hexp : Real.exp (-1 * |x - y|) = Real.exp (-|x - y|) := by
      congr 1
      ring
    rw [hexp]
    ring
  rw [hdiff, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hdiff_cunif :
      IsCUnifBdd (fun y => (u y) ^ p.γ - (v y) ^ p.γ) := by
    refine ⟨hgu.1.sub hgv.1, ?_⟩
    rcases hgu.2 with ⟨Bu, hBu⟩
    rcases hgv.2 with ⟨Bv, hBv⟩
    exact ⟨Bu + Bv, fun y =>
      le_trans (abs_sub _ _) (add_le_add (hBu y) (hBv y))⟩
  have habs_cunif :
      IsCUnifBdd (fun y => |(u y) ^ p.γ - (v y) ^ p.γ|) := by
    refine ⟨hdiff_cunif.1.abs, ?_⟩
    rcases hdiff_cunif.2 with ⟨B, hB⟩
    exact ⟨B, fun y => by simpa using hB y⟩
  have henv_int : Integrable
      (fun y => Real.exp (-|x - y|) *
        |(u y) ^ p.γ - (v y) ^ p.γ|) := by
    rcases habs_cunif.2 with ⟨B, hB⟩
    have hdom : Integrable (fun y => Real.exp (-|x - y|) * B) :=
      (exp_neg_abs_sub_integrable x).mul_const B
    have hmeas : AEStronglyMeasurable
        (fun y => Real.exp (-|x - y|) *
          |(u y) ^ p.γ - (v y) ^ p.γ|) volume :=
      ((by fun_prop : Continuous fun y : ℝ =>
          Real.exp (-|x - y|)).aestronglyMeasurable).mul
        habs_cunif.1.aestronglyMeasurable
    refine Integrable.mono' hdom hmeas (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_abs]
    exact mul_le_mul_of_nonneg_left (by simpa only [abs_abs] using hB y)
      (Real.exp_nonneg _)
  calc
    |∫ y, Real.exp (-|x - y|) *
        ((u y) ^ p.γ - (v y) ^ p.γ)|
        = ‖∫ y, Real.exp (-|x - y|) *
            ((u y) ^ p.γ - (v y) ^ p.γ)‖ :=
          (Real.norm_eq_abs _).symm
    _ ≤ ∫ y, ‖Real.exp (-|x - y|) *
          ((u y) ^ p.γ - (v y) ^ p.γ)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ y, Real.exp (-|x - y|) *
          |(u y) ^ p.γ - (v y) ^ p.γ| := by
        apply integral_congr_ae
        filter_upwards with y
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]

/-- Local-uniform continuous dependence of the frozen elliptic value on a
trapped profile.  The proof reuses the same inner/tail kernel split as the
already proved derivative dependence. -/
theorem frozenEllipticDependence (p : CMParams) {κ M : ℝ} (hM : 0 ≤ M) :
    ∀ (seq : ℕ → ℝ → ℝ) (u : ℝ → ℝ),
      (∀ n, InMonotoneWaveTrapSet κ M (seq n)) →
      InMonotoneWaveTrapSet κ M u →
      LocallyUniformConverges seq u →
      LocallyUniformConverges (fun n => frozenElliptic p (seq n))
        (frozenElliptic p u) := by
  intro seq u hseq hu hconv
  have hu_cunif : IsCUnifBdd u := hu.trap.cunif_bdd
  have hu_nn : ∀ x, 0 ≤ u x := hu.nonneg
  have hu_le : ∀ x, u x ≤ M := hu.le_M
  have hsn_cunif : ∀ n, IsCUnifBdd (seq n) :=
    fun n => (hseq n).trap.cunif_bdd
  have hsn_nn : ∀ n x, 0 ≤ seq n x := fun n => (hseq n).nonneg
  have hsn_le : ∀ n x, seq n x ≤ M := fun n => (hseq n).le_M
  set L := rpowLip p.γ M
  have hL0 : 0 ≤ L := rpowLip_nonneg p.hγ hM
  intro R hR ε hε
  set K : ℝ := 2 * M ^ p.γ * Real.exp R
  have hK0 : 0 ≤ K := by positivity
  have hexp0 : Tendsto (fun R' : ℝ => Real.exp (-R')) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have htail_small : ∀ᶠ R' : ℝ in atTop,
      K * Real.exp (-R') < ε / 2 := by
    have hKtail : Tendsto (fun R' : ℝ => K * Real.exp (-R')) atTop (𝓝 0) := by
      simpa using hexp0.const_mul K
    exact hKtail.eventually (eventually_lt_nhds (by linarith))
  obtain ⟨R', htailR', hRR'⟩ :=
    (htail_small.and (eventually_ge_atTop R)).exists
  have hR'0 : 0 < R' := lt_of_lt_of_le hR hRR'
  have hLp1 : 0 < L + 1 := by linarith
  let s0 : ℝ := ε / (2 * (L + 1))
  have hs0 : 0 < s0 := by dsimp [s0]; positivity
  filter_upwards [hconv R' hR'0 s0 hs0] with n hn
  intro x hx
  have hs_bd : ∀ y ∈ Set.Icc (-R') R', |seq n y - u y| ≤ s0 :=
    fun y hy => (hn y hy).le
  have habs := frozenElliptic_diff_abs_le p
    (hsn_cunif n) (hsn_nn n) hu_cunif hu_nn x
  have hsplit := deriv_diff_integral_split_le p
    (M := M) (R := R) (R' := R') (s := s0)
    hM (hsn_nn n) (hsn_le n) hu_nn hu_le hs_bd hR hRR' hx
    (hsn_cunif n) hu_cunif
  have hchain :
      |frozenElliptic p (seq n) x - frozenElliptic p u x| ≤
        L * s0 + K * Real.exp (-R') := by
    refine le_trans habs ?_
    have h2 := mul_le_mul_of_nonneg_left hsplit
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    calc
      1 / 2 * ∫ y, Real.exp (-|x - y|) *
            |(seq n y) ^ p.γ - (u y) ^ p.γ|
          ≤ 1 / 2 *
              (2 * (rpowLip p.γ M * s0) +
                4 * (M ^ p.γ * (Real.exp R * Real.exp (-R')))) := h2
      _ = L * s0 + K * Real.exp (-R') := by
        dsimp [L, K]
        ring
  have hinner_le : L * s0 ≤ ε / 2 := by
    have hstep : L * s0 ≤ (L + 1) * s0 :=
      mul_le_mul_of_nonneg_right (by linarith) hs0.le
    have heq : (L + 1) * s0 = ε / 2 := by
      dsimp [s0]
      field_simp [ne_of_gt hLp1]
    linarith
  calc
    |frozenElliptic p (seq n) x - frozenElliptic p u x|
        ≤ L * s0 + K * Real.exp (-R') := hchain
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

section AxiomAudit

#print axioms frozenElliptic_diff_abs_le
#print axioms frozenEllipticDependence

end AxiomAudit

end ShenWork.Paper1
