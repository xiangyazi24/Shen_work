/- Frozen Green-field dependence on the nonmonotone positive wave trap. -/
import ShenWork.Paper1.WaveFrozenEllipticValueDep
import ShenWork.Paper1.WavePaperAdaptiveSourceCompactness

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

theorem frozenEllipticDependence_inWaveTrap
    (p : CMParams) {κ M : ℝ} (hM : 0 ≤ M) :
    ∀ (seq : ℕ → ℝ → ℝ) (u : ℝ → ℝ),
      (∀ n, InWaveTrapSet κ M (seq n)) → InWaveTrapSet κ M u →
      LocallyUniformConverges seq u →
      LocallyUniformConverges (fun n => frozenElliptic p (seq n))
        (frozenElliptic p u) := by
  intro seq u hseq hu hconv
  have hu_cunif : IsCUnifBdd u := hu.cunif_bdd
  have hu_nn : ∀ x, 0 ≤ u x := hu.nonneg
  have hu_le : ∀ x, u x ≤ M := hu.le_M
  have hsn_cunif : ∀ n, IsCUnifBdd (seq n) := fun n => (hseq n).cunif_bdd
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
            |(seq n y) ^ p.γ - (u y) ^ p.γ| ≤
          1 / 2 * (2 * (rpowLip p.γ M * s0) +
            4 * (M ^ p.γ * (Real.exp R * Real.exp (-R')))) := h2
      _ = L * s0 + K * Real.exp (-R') := by dsimp [L, K]; ring
  have hinner_le : L * s0 ≤ ε / 2 := by
    have hstep : L * s0 ≤ (L + 1) * s0 :=
      mul_le_mul_of_nonneg_right (by linarith) hs0.le
    have heq : (L + 1) * s0 = ε / 2 := by
      dsimp [s0]
      field_simp [ne_of_gt hLp1]
    linarith
  calc
    |frozenElliptic p (seq n) x - frozenElliptic p u x| ≤
        L * s0 + K * Real.exp (-R') := hchain
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

theorem frozenEllipticDerivDependence_inWaveTrap
    (p : CMParams) {κ M : ℝ} (hM : 0 ≤ M) :
    FrozenEllipticDerivDependence p (InWaveTrapSet κ M) := by
  intro seq u hseq hu hconv
  have hu_cunif : IsCUnifBdd u := hu.cunif_bdd
  have hu_nn : ∀ x, 0 ≤ u x := hu.nonneg
  have hu_le : ∀ x, u x ≤ M := hu.le_M
  have hsn_cunif : ∀ n, IsCUnifBdd (seq n) := fun n => (hseq n).cunif_bdd
  have hsn_nn : ∀ n x, 0 ≤ seq n x := fun n => (hseq n).nonneg
  have hsn_le : ∀ n x, seq n x ≤ M := fun n => (hseq n).le_M
  have hγ1 : (1 : ℝ) ≤ p.γ := p.hγ
  set L := rpowLip p.γ M with hL
  have hL0 : 0 ≤ L := rpowLip_nonneg hγ1 hM
  have hMγ0 : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM p.γ
  intro R hR ε hε
  set K : ℝ := 2 * M ^ p.γ * Real.exp R with hK
  have hK0 : 0 ≤ K := by positivity
  have hexp0 : Tendsto (fun R' : ℝ => Real.exp (-R')) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have htail_small : ∀ᶠ R' : ℝ in atTop,
      K * Real.exp (-R') < ε / 2 := by
    have hKtail : Tendsto (fun R' : ℝ => K * Real.exp (-R')) atTop (𝓝 0) := by
      simpa using hexp0.const_mul K
    exact hKtail.eventually (eventually_lt_nhds (by linarith))
  obtain ⟨R', htailR', hR'ge⟩ :=
    (htail_small.and (eventually_ge_atTop R)).exists
  have hRR' : R ≤ R' := hR'ge
  have hR'0 : 0 < R' := lt_of_lt_of_le hR hRR'
  have hLp1 : 0 < L + 1 := by linarith
  set s0 : ℝ := ε / (2 * (L + 1)) with hs0def
  have hs0pos : 0 < s0 := by rw [hs0def]; positivity
  filter_upwards [hconv R' hR'0 s0 hs0pos] with n hn
  intro x hx
  have hs_bd : ∀ y ∈ Set.Icc (-R') R', |seq n y - u y| ≤ s0 :=
    fun y hy => (hn y hy).le
  have habs := frozenElliptic_deriv_diff_abs_le p
    (hsn_cunif n) (hsn_nn n) hu_cunif hu_nn x
  have hsplit := deriv_diff_integral_split_le p
    (M := M) (R := R) (R' := R') (s := s0)
    hM (hsn_nn n) (hsn_le n) hu_nn hu_le hs_bd hR hRR' hx
    (hsn_cunif n) hu_cunif
  have hchain :
      |deriv (frozenElliptic p (seq n)) x - deriv (frozenElliptic p u) x| ≤
        L * s0 + K * Real.exp (-R') := by
    refine le_trans habs ?_
    have h2 : (1 : ℝ) / 2 * (∫ y, Real.exp (-|x - y|) *
        |(seq n y) ^ p.γ - (u y) ^ p.γ|) ≤
      1 / 2 * (2 * (L * s0) +
        4 * (M ^ p.γ * (Real.exp R * Real.exp (-R')))) :=
      mul_le_mul_of_nonneg_left hsplit (by norm_num)
    refine le_trans h2 (le_of_eq ?_)
    rw [hK]
    ring
  have hinner_le : L * s0 ≤ ε / 2 := by
    have hstep : L * s0 ≤ (L + 1) * s0 :=
      mul_le_mul_of_nonneg_right (by linarith) hs0pos.le
    have heq : (L + 1) * s0 = ε / 2 := by rw [hs0def]; field_simp
    linarith
  calc
    |deriv (frozenElliptic p (seq n)) x - deriv (frozenElliptic p u) x| ≤
        L * s0 + K * Real.exp (-R') := hchain
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-! Translation clusters no longer satisfy the exponentially weighted wave
trap, but they retain exactly the source-box data used by the two kernel
proofs above.  These box-level variants expose that actual dependency. -/

theorem frozenEllipticDependence_of_nonneg_le
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M)
    {seq : ℕ → ℝ → ℝ} {u : ℝ → ℝ}
    (hsn_cunif : ∀ n, IsCUnifBdd (seq n))
    (hsn_nn : ∀ n x, 0 ≤ seq n x) (hsn_le : ∀ n x, seq n x ≤ M)
    (hu_cunif : IsCUnifBdd u) (hu_nn : ∀ x, 0 ≤ u x)
    (hu_le : ∀ x, u x ≤ M)
    (hconv : LocallyUniformConverges seq u) :
    LocallyUniformConverges (fun n => frozenElliptic p (seq n))
      (frozenElliptic p u) := by
  set L := rpowLip p.γ M
  have hL0 : 0 ≤ L := rpowLip_nonneg p.hγ hM
  intro R hR ε hε
  set K : ℝ := 2 * M ^ p.γ * Real.exp R
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
            |(seq n y) ^ p.γ - (u y) ^ p.γ| ≤
          1 / 2 * (2 * (rpowLip p.γ M * s0) +
            4 * (M ^ p.γ * (Real.exp R * Real.exp (-R')))) := h2
      _ = L * s0 + K * Real.exp (-R') := by dsimp [L, K]; ring
  have hinner_le : L * s0 ≤ ε / 2 := by
    have hstep : L * s0 ≤ (L + 1) * s0 :=
      mul_le_mul_of_nonneg_right (by linarith) hs0.le
    have heq : (L + 1) * s0 = ε / 2 := by
      dsimp [s0]
      field_simp [ne_of_gt hLp1]
    linarith
  calc
    |frozenElliptic p (seq n) x - frozenElliptic p u x| ≤
        L * s0 + K * Real.exp (-R') := hchain
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

theorem frozenEllipticDerivDependence_of_nonneg_le
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M)
    {seq : ℕ → ℝ → ℝ} {u : ℝ → ℝ}
    (hsn_cunif : ∀ n, IsCUnifBdd (seq n))
    (hsn_nn : ∀ n x, 0 ≤ seq n x) (hsn_le : ∀ n x, seq n x ≤ M)
    (hu_cunif : IsCUnifBdd u) (hu_nn : ∀ x, 0 ≤ u x)
    (hu_le : ∀ x, u x ≤ M)
    (hconv : LocallyUniformConverges seq u) :
    LocallyUniformConverges
      (fun n x => deriv (frozenElliptic p (seq n)) x)
      (fun x => deriv (frozenElliptic p u) x) := by
  set L := rpowLip p.γ M
  have hL0 : 0 ≤ L := rpowLip_nonneg p.hγ hM
  intro R hR ε hε
  set K : ℝ := 2 * M ^ p.γ * Real.exp R
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
  have habs := frozenElliptic_deriv_diff_abs_le p
    (hsn_cunif n) (hsn_nn n) hu_cunif hu_nn x
  have hsplit := deriv_diff_integral_split_le p
    (M := M) (R := R) (R' := R') (s := s0)
    hM (hsn_nn n) (hsn_le n) hu_nn hu_le hs_bd hR hRR' hx
    (hsn_cunif n) hu_cunif
  have hchain :
      |deriv (frozenElliptic p (seq n)) x - deriv (frozenElliptic p u) x| ≤
        L * s0 + K * Real.exp (-R') := by
    refine le_trans habs ?_
    have h2 : (1 : ℝ) / 2 * (∫ y, Real.exp (-|x - y|) *
        |(seq n y) ^ p.γ - (u y) ^ p.γ|) ≤
      1 / 2 * (2 * (L * s0) +
        4 * (M ^ p.γ * (Real.exp R * Real.exp (-R')))) :=
      mul_le_mul_of_nonneg_left hsplit (by norm_num)
    refine le_trans h2 (le_of_eq ?_)
    dsimp [K]
    ring
  have hinner_le : L * s0 ≤ ε / 2 := by
    have hstep : L * s0 ≤ (L + 1) * s0 :=
      mul_le_mul_of_nonneg_right (by linarith) hs0.le
    have heq : (L + 1) * s0 = ε / 2 := by
      dsimp [s0]
      field_simp [ne_of_gt hLp1]
    linarith
  calc
    |deriv (frozenElliptic p (seq n)) x - deriv (frozenElliptic p u) x| ≤
        L * s0 + K * Real.exp (-R') := hchain
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-- Non-diagonal continuity of the genuine paper source on the nonmonotone
positive trap. -/
theorem paperStepSource_locallyUniform_nonDiagonal_inWaveTrap
    (p : CMParams) {c lam M κ : ℝ}
    {us Zs Ws : ℕ → ℝ → ℝ} {u Z W : ℝ → ℝ}
    (hM : 0 < M)
    (husTrap : ∀ n, InWaveTrapSet κ M (us n))
    (huTrap : InWaveTrapSet κ M u)
    (hWs0 : ∀ n x, 0 ≤ Ws n x) (hWsM : ∀ n x, Ws n x ≤ M)
    (hW0 : ∀ x, 0 ≤ W x) (hWM : ∀ x, W x ≤ M)
    (hus : LocallyUniformConverges us u)
    (hZs : LocallyUniformConverges Zs Z)
    (hWs : LocallyUniformConverges Ws W)
    (hWds : LocallyUniformConverges
      (fun n x => deriv (Ws n) x) (fun x => deriv W x))
    (hbddDerivW : LocallyBoundedOnCompacts (fun x => deriv W x)) :
    LocallyUniformConverges
      (fun n => paperStepSource p c lam (us n) (Zs n) (Ws n))
      (paperStepSource p c lam u Z W) := by
  have hM0 : 0 ≤ M := hM.le
  have hV : LocallyUniformConverges
      (fun n => frozenElliptic p (us n)) (frozenElliptic p u) :=
    frozenEllipticDependence_inWaveTrap p hM0 us u husTrap huTrap hus
  have hVd : LocallyUniformConverges
      (fun n x => deriv (frozenElliptic p (us n)) x)
      (fun x => deriv (frozenElliptic p u) x) :=
    frozenEllipticDerivDependence_inWaveTrap p hM0 us u husTrap huTrap hus
  have hpowM1 : LocallyUniformConverges
      (fun n x => (Ws n x) ^ (p.m - 1))
      (fun x => (W x) ^ (p.m - 1)) :=
    hWs.rpow_of_nonneg_le (by linarith [p.hm]) hM0 hWs0 hWsM hW0 hWM
  have hpowA : LocallyUniformConverges
      (fun n x => (Ws n x) ^ p.α) (fun x => (W x) ^ p.α) :=
    hWs.rpow_of_nonneg_le (by linarith [p.hα]) hM0 hWs0 hWsM hW0 hWM
  have hpowMG : LocallyUniformConverges
      (fun n x => (Ws n x) ^ (p.m + p.γ - 1))
      (fun x => (W x) ^ (p.m + p.γ - 1)) :=
    hWs.rpow_of_nonneg_le (by linarith [p.hm, p.hγ]) hM0
      hWs0 hWsM hW0 hWM
  have hbddW : LocallyBoundedOnCompacts W :=
    LocallyBoundedOnCompacts.of_global_bound hM0 (fun x => by
      rw [abs_of_nonneg (hW0 x)]
      exact hWM x)
  have hMγ0 : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM0 p.γ
  have hbddV : LocallyBoundedOnCompacts (frozenElliptic p u) :=
    LocallyBoundedOnCompacts.of_global_bound hMγ0 (fun x => by
      rw [abs_of_nonneg (frozenElliptic_nonneg p huTrap.nonneg x)]
      exact frozenElliptic_le_rpow_of_inWaveTrapSet p hM huTrap x)
  have hbddVd : LocallyBoundedOnCompacts
      (fun x => deriv (frozenElliptic p u) x) :=
    LocallyBoundedOnCompacts.of_global_bound hMγ0 (fun x =>
      (frozenElliptic_deriv_abs_le p huTrap.cunif_bdd huTrap.nonneg x).trans
        (frozenElliptic_le_rpow_of_inWaveTrapSet p hM huTrap x))
  have hMm10 : 0 ≤ M ^ (p.m - 1) := Real.rpow_nonneg hM0 _
  have hbddPowM1 : LocallyBoundedOnCompacts
      (fun x => (W x) ^ (p.m - 1)) :=
    LocallyBoundedOnCompacts.of_global_bound hMm10 (fun x => by
      rw [abs_of_nonneg (Real.rpow_nonneg (hW0 x) _)]
      exact Real.rpow_le_rpow (hW0 x) (hWM x) (by linarith [p.hm]))
  have hMα0 : 0 ≤ M ^ p.α := Real.rpow_nonneg hM0 _
  have hbddPowA : LocallyBoundedOnCompacts (fun x => (W x) ^ p.α) :=
    LocallyBoundedOnCompacts.of_global_bound hMα0 (fun x => by
      rw [abs_of_nonneg (Real.rpow_nonneg (hW0 x) _)]
      exact Real.rpow_le_rpow (hW0 x) (hWM x) (by linarith [p.hα]))
  have hMmg0 : 0 ≤ M ^ (p.m + p.γ - 1) := Real.rpow_nonneg hM0 _
  have hbddPowMG : LocallyBoundedOnCompacts
      (fun x => (W x) ^ (p.m + p.γ - 1)) :=
    LocallyBoundedOnCompacts.of_global_bound hMmg0 (fun x => by
      rw [abs_of_nonneg (Real.rpow_nonneg (hW0 x) _)]
      exact Real.rpow_le_rpow (hW0 x) (hWM x)
        (by linarith [p.hm, p.hγ]))
  have hVdWd : LocallyUniformConverges
      (fun n x => deriv (frozenElliptic p (us n)) x * deriv (Ws n) x)
      (fun x => deriv (frozenElliptic p u) x * deriv W x) :=
    hVd.mul hWds hbddVd hbddDerivW
  have hbddVdWd : LocallyBoundedOnCompacts
      (fun x => deriv (frozenElliptic p u) x * deriv W x) :=
    hbddVd.mul hbddDerivW
  have hchemCore : LocallyUniformConverges
      (fun n => paperWaveChemCore p (us n) (Ws n))
      (paperWaveChemCore p u W) := by
    have hmul := hpowM1.mul hVdWd hbddPowM1 hbddVdWd
    simpa [paperWaveChemCore, mul_assoc] using hmul
  have hchem : LocallyUniformConverges
      (fun n => paperWaveChemTerm p (us n) (Ws n))
      (paperWaveChemTerm p u W) := by
    simpa [paperWaveChemTerm] using hchemCore.const_mul (-(p.χ * p.m))
  have hpowM1V : LocallyUniformConverges
      (fun n x => (Ws n x) ^ (p.m - 1) * frozenElliptic p (us n) x)
      (fun x => (W x) ^ (p.m - 1) * frozenElliptic p u x) :=
    hpowM1.mul hV hbddPowM1 hbddV
  have hleft : LocallyUniformConverges
      (fun n x => 1 - p.χ *
        ((Ws n x) ^ (p.m - 1) * frozenElliptic p (us n) x))
      (fun x => 1 - p.χ * ((W x) ^ (p.m - 1) * frozenElliptic p u x)) :=
    hpowM1V.const_mul p.χ |>.const_sub 1
  have hright : LocallyUniformConverges
      (fun n x => (Ws n x) ^ p.α - p.χ * (Ws n x) ^ (p.m + p.γ - 1))
      (fun x => (W x) ^ p.α - p.χ * (W x) ^ (p.m + p.γ - 1)) :=
    hpowA.sub (hpowMG.const_mul p.χ)
  have hbracket : LocallyUniformConverges
      (fun n => paperWaveReactionBracket p (us n) (Ws n))
      (paperWaveReactionBracket p u W) := by
    simpa [paperWaveReactionBracket] using hleft.sub hright
  have hbddM1V : LocallyBoundedOnCompacts
      (fun x => (W x) ^ (p.m - 1) * frozenElliptic p u x) :=
    hbddPowM1.mul hbddV
  have hbddLeft : LocallyBoundedOnCompacts
      (fun x => 1 - p.χ * ((W x) ^ (p.m - 1) * frozenElliptic p u x)) :=
    (hbddM1V.const_mul p.χ).const_sub 1
  have hbddRight : LocallyBoundedOnCompacts
      (fun x => (W x) ^ p.α - p.χ * (W x) ^ (p.m + p.γ - 1)) :=
    hbddPowA.sub (hbddPowMG.const_mul p.χ)
  have hbddBracket : LocallyBoundedOnCompacts
      (paperWaveReactionBracket p u W) := by
    simpa [paperWaveReactionBracket] using hbddLeft.sub hbddRight
  have hreaction : LocallyUniformConverges
      (fun n => paperWaveReactionTerm p (us n) (Ws n))
      (paperWaveReactionTerm p u W) := by
    have hmul := hWs.mul hbracket hbddW hbddBracket
    simpa [paperWaveReactionTerm] using hmul
  have hnonlinear : LocallyUniformConverges
      (fun n x => paperWaveChemTerm p (us n) (Ws n) x +
        paperWaveReactionTerm p (us n) (Ws n) x)
      (fun x => paperWaveChemTerm p u W x + paperWaveReactionTerm p u W x) :=
    hchem.add hreaction
  have hlinear : LocallyUniformConverges
      (fun n x => lam * Zs n x) (fun x => lam * Z x) := hZs.const_mul lam
  have hsum := hnonlinear.add hlinear
  have hseqEq :
      (fun n => paperStepSource p c lam (us n) (Zs n) (Ws n)) =
        fun n x => paperWaveChemTerm p (us n) (Ws n) x +
          paperWaveReactionTerm p (us n) (Ws n) x + lam * Zs n x := by
    funext n x
    unfold paperStepSource paperStepNonlinearity paperWaveChemTerm
      paperWaveChemCore paperWaveReactionTerm paperWaveReactionBracket
    ring
  have hlimitEq : paperStepSource p c lam u Z W =
      fun x => paperWaveChemTerm p u W x +
        paperWaveReactionTerm p u W x + lam * Z x := by
    funext x
    unfold paperStepSource paperStepNonlinearity paperWaveChemTerm
      paperWaveChemCore paperWaveReactionTerm paperWaveReactionBracket
    ring
  rw [hseqEq, hlimitEq]
  exact hsum

section AxiomAudit

#print axioms frozenEllipticDependence_inWaveTrap
#print axioms frozenEllipticDerivDependence_inWaveTrap
#print axioms paperStepSource_locallyUniform_nonDiagonal_inWaveTrap

end AxiomAudit

end ShenWork.Paper1
