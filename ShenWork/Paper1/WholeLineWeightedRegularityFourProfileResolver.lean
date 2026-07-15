import ShenWork.Paper1.WholeLineWeightedRegularityCapResolverValue

open Filter MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

def fourProfilePowerSource (p : CMParams)
    (u₂ u₁ v₂ v₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (u₂ x ^ p.γ - u₁ x ^ p.γ) -
    (v₂ x ^ p.γ - v₁ x ^ p.γ)

def fourProfileResolverValue (p : CMParams)
    (u₂ u₁ v₂ v₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (frozenElliptic p u₂ x - frozenElliptic p u₁ x) -
    (frozenElliptic p v₂ x - frozenElliptic p v₁ x)

def fourProfileResolverGradient (p : CMParams)
    (u₂ u₁ v₂ v₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (deriv (frozenElliptic p u₂) x - deriv (frozenElliptic p u₁) x) -
    (deriv (frozenElliptic p v₂) x - deriv (frozenElliptic p v₁) x)

private theorem isCUnifBdd_sub {f g : ℝ → ℝ}
    (hf : IsCUnifBdd f) (hg : IsCUnifBdd g) :
    IsCUnifBdd (fun x => f x - g x) := by
  refine ⟨hf.1.sub hg.1, ?_⟩
  rcases hf.2 with ⟨Bf, hBf⟩
  rcases hg.2 with ⟨Bg, hBg⟩
  exact ⟨Bf + Bg, fun x => le_trans (abs_sub _ _) (add_le_add (hBf x) (hBg x))⟩

/-- A cap-weighted four-profile power-source estimate transfers verbatim
through both the frozen resolver value and gradient. -/
theorem capWeight_fourProfile_resolver_commutator_of_source_bound
    (p : CMParams) {M eta R B : ℝ}
    (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    {u₂ u₁ v₂ v₁ : ℝ → ℝ}
    (hu₂ : IsCUnifBdd u₂) (hu₁ : IsCUnifBdd u₁)
    (hv₂ : IsCUnifBdd v₂) (hv₁ : IsCUnifBdd v₁)
    (hu₂_mem : ∀ x, u₂ x ∈ Set.Icc (0 : ℝ) M)
    (hu₁_mem : ∀ x, u₁ x ∈ Set.Icc (0 : ℝ) M)
    (hv₂_mem : ∀ x, v₂ x ∈ Set.Icc (0 : ℝ) M)
    (hv₁_mem : ∀ x, v₁ x ∈ Set.Icc (0 : ℝ) M)
    (hsource : Integrable (fun x => capWeight eta R x *
      |fourProfilePowerSource p u₂ u₁ v₂ v₁ x| ^ 2))
    (hsourceBound :
      (∫ x : ℝ, capWeight eta R x *
        |fourProfilePowerSource p u₂ u₁ v₂ v₁ x| ^ 2) ≤ B) :
    (Integrable (fun x => capWeight eta R x *
        |fourProfileResolverValue p u₂ u₁ v₂ v₁ x| ^ 2) ∧
      (∫ x : ℝ, capWeight eta R x *
        |fourProfileResolverValue p u₂ u₁ v₂ v₁ x| ^ 2) ≤
          (1 / (1 - eta)) ^ 2 * B) ∧
    (Integrable (fun x => capWeight eta R x *
        |fourProfileResolverGradient p u₂ u₁ v₂ v₁ x| ^ 2) ∧
      (∫ x : ℝ, capWeight eta R x *
        |fourProfileResolverGradient p u₂ u₁ v₂ v₁ x| ^ 2) ≤
          (1 / (1 - eta)) ^ 2 * B) := by
  let s₂₁ : ℝ → ℝ := fun x => u₂ x ^ p.γ - u₁ x ^ p.γ
  let sᵥ₂₁ : ℝ → ℝ := fun x => v₂ x ^ p.γ - v₁ x ^ p.γ
  let s : ℝ → ℝ := fun x => s₂₁ x - sᵥ₂₁ x
  have hs₂₁ : IsCUnifBdd s₂₁ := by
    dsimp [s₂₁]
    exact rpow_difference_isCUnifBdd p.hγ hu₁ hu₂ hu₁_mem hu₂_mem
  have hsᵥ₂₁ : IsCUnifBdd sᵥ₂₁ := by
    dsimp [sᵥ₂₁]
    exact rpow_difference_isCUnifBdd p.hγ hv₁ hv₂ hv₁_mem hv₂_mem
  have hs : IsCUnifBdd s := by
    dsimp [s]
    exact isCUnifBdd_sub hs₂₁ hsᵥ₂₁
  have hsource' : Integrable (fun x =>
      (capWeightSqrt eta R x * s x) ^ 2) := by
    refine hsource.congr (Eventually.of_forall fun x => ?_)
    change capWeight eta R x *
      |fourProfilePowerSource p u₂ u₁ v₂ v₁ x| ^ 2 =
        (capWeightSqrt eta R x * s x) ^ 2
    rw [capWeightSqrt_mul_sq_eq]
    rfl
  have hsourceBound' :
      (∫ x : ℝ, (capWeightSqrt eta R x * s x) ^ 2) ≤ B := by
    rw [show (∫ x : ℝ, (capWeightSqrt eta R x * s x) ^ 2) =
        ∫ x : ℝ, capWeight eta R x *
          |fourProfilePowerSource p u₂ u₁ v₂ v₁ x| ^ 2 by
      apply integral_congr_ae
      filter_upwards with x
      rw [capWeightSqrt_mul_sq_eq]
      rfl]
    exact hsourceBound
  have hvalue := weighted_resolver_value_of_ratio_bound
    heta1
    (capWeightSqrt_continuous eta R)
    (capWeightSqrt_pos eta R)
    (capWeightSqrt_le_exp_abs_mul heta0 R)
    hs hsource'
  have hgrad := weighted_resolver_gradient_of_ratio_bound
    heta0 heta1
    (capWeightSqrt_continuous eta R)
    (capWeightSqrt_pos eta R)
    (capWeightSqrt_le_exp_abs_mul heta0 R)
    hs hsource'
  have hpow_u₂ : IsCUnifBdd (fun x => u₂ x ^ p.γ) :=
    rpow_cunif_bdd_of_nonneg p hu₂ (fun x => (hu₂_mem x).1)
  have hpow_u₁ : IsCUnifBdd (fun x => u₁ x ^ p.γ) :=
    rpow_cunif_bdd_of_nonneg p hu₁ (fun x => (hu₁_mem x).1)
  have hpow_v₂ : IsCUnifBdd (fun x => v₂ x ^ p.γ) :=
    rpow_cunif_bdd_of_nonneg p hv₂ (fun x => (hv₂_mem x).1)
  have hpow_v₁ : IsCUnifBdd (fun x => v₁ x ^ p.γ) :=
    rpow_cunif_bdd_of_nonneg p hv₁ (fun x => (hv₁_mem x).1)
  have hpair_u : ∀ x,
      frozenElliptic p u₂ x - frozenElliptic p u₁ x = Psi s₂₁ 1 1 x := by
    intro x
    dsimp [s₂₁]
    unfold frozenElliptic
    exact (Psi_sub x
      (by simpa [Real.sqrt_one] using
        (Psi_kernel_integrable_of_isCUnifBdd one_pos hpow_u₂ x))
      (by simpa [Real.sqrt_one] using
        (Psi_kernel_integrable_of_isCUnifBdd one_pos hpow_u₁ x))).symm
  have hpair_v : ∀ x,
      frozenElliptic p v₂ x - frozenElliptic p v₁ x = Psi sᵥ₂₁ 1 1 x := by
    intro x
    dsimp [sᵥ₂₁]
    unfold frozenElliptic
    exact (Psi_sub x
      (by simpa [Real.sqrt_one] using
        (Psi_kernel_integrable_of_isCUnifBdd one_pos hpow_v₂ x))
      (by simpa [Real.sqrt_one] using
        (Psi_kernel_integrable_of_isCUnifBdd one_pos hpow_v₁ x))).symm
  have hvalueEq : ∀ x,
      fourProfileResolverValue p u₂ u₁ v₂ v₁ x = Psi s 1 1 x := by
    intro x
    rw [show fourProfileResolverValue p u₂ u₁ v₂ v₁ x =
        (frozenElliptic p u₂ x - frozenElliptic p u₁ x) -
          (frozenElliptic p v₂ x - frozenElliptic p v₁ x) by rfl,
      hpair_u x, hpair_v x]
    exact (Psi_sub x
      (by simpa [Real.sqrt_one] using
        (Psi_kernel_integrable_of_isCUnifBdd one_pos hs₂₁ x))
      (by simpa [Real.sqrt_one] using
        (Psi_kernel_integrable_of_isCUnifBdd one_pos hsᵥ₂₁ x))).symm
  have hsourceSubFun :
      (fun x => Psi s₂₁ 1 1 x - Psi sᵥ₂₁ 1 1 x) = Psi s 1 1 := by
    funext x
    exact (Psi_sub x
      (by simpa [Real.sqrt_one] using
        (Psi_kernel_integrable_of_isCUnifBdd one_pos hs₂₁ x))
      (by simpa [Real.sqrt_one] using
        (Psi_kernel_integrable_of_isCUnifBdd one_pos hsᵥ₂₁ x))).symm
  have hgradEq : ∀ x,
      fourProfileResolverGradient p u₂ u₁ v₂ v₁ x = deriv (Psi s 1 1) x := by
    intro x
    have hgrad_u : deriv (frozenElliptic p u₂) x -
        deriv (frozenElliptic p u₁) x = deriv (Psi s₂₁ 1 1) x := by
      rw [frozenElliptic_deriv_diff_eq p hu₂
        (fun y => (hu₂_mem y).1) hu₁ (fun y => (hu₁_mem y).1) x,
        Psi_deriv_eq_frozenEllipticDerivKernel hs₂₁ x]
    have hgrad_v : deriv (frozenElliptic p v₂) x -
        deriv (frozenElliptic p v₁) x = deriv (Psi sᵥ₂₁ 1 1) x := by
      rw [frozenElliptic_deriv_diff_eq p hv₂
        (fun y => (hv₂_mem y).1) hv₁ (fun y => (hv₁_mem y).1) x,
        Psi_deriv_eq_frozenEllipticDerivKernel hsᵥ₂₁ x]
    rw [fourProfileResolverGradient, hgrad_u, hgrad_v, ← hsourceSubFun]
    exact (deriv_sub (Psi_differentiable one_pos one_pos hs₂₁ x)
      (Psi_differentiable one_pos one_pos hsᵥ₂₁ x)).symm
  have hvalueInt : Integrable (fun x => capWeight eta R x *
      |fourProfileResolverValue p u₂ u₁ v₂ v₁ x| ^ 2) := by
    refine hvalue.1.congr (Eventually.of_forall fun x => ?_)
    change (capWeightSqrt eta R x * Psi s 1 1 x) ^ 2 =
      capWeight eta R x *
        |fourProfileResolverValue p u₂ u₁ v₂ v₁ x| ^ 2
    rw [← hvalueEq x, capWeightSqrt_mul_sq_eq]
  have hgradInt : Integrable (fun x => capWeight eta R x *
      |fourProfileResolverGradient p u₂ u₁ v₂ v₁ x| ^ 2) := by
    refine hgrad.1.congr (Eventually.of_forall fun x => ?_)
    change (capWeightSqrt eta R x * deriv (Psi s 1 1) x) ^ 2 =
      capWeight eta R x *
        |fourProfileResolverGradient p u₂ u₁ v₂ v₁ x| ^ 2
    rw [← hgradEq x, capWeightSqrt_mul_sq_eq]
  refine ⟨⟨hvalueInt, ?_⟩, ⟨hgradInt, ?_⟩⟩
  · calc
      (∫ x : ℝ, capWeight eta R x *
          |fourProfileResolverValue p u₂ u₁ v₂ v₁ x| ^ 2) =
          ∫ x : ℝ, (capWeightSqrt eta R x * Psi s 1 1 x) ^ 2 := by
            apply integral_congr_ae
            filter_upwards with x
            rw [hvalueEq x, capWeightSqrt_mul_sq_eq]
      _ ≤ (1 / (1 - eta)) ^ 2 *
          ∫ x : ℝ, (capWeightSqrt eta R x * s x) ^ 2 := hvalue.2
      _ ≤ (1 / (1 - eta)) ^ 2 * B :=
        mul_le_mul_of_nonneg_left hsourceBound' (sq_nonneg _)
  · calc
      (∫ x : ℝ, capWeight eta R x *
          |fourProfileResolverGradient p u₂ u₁ v₂ v₁ x| ^ 2) =
          ∫ x : ℝ, (capWeightSqrt eta R x * deriv (Psi s 1 1) x) ^ 2 := by
            apply integral_congr_ae
            filter_upwards with x
            rw [hgradEq x, capWeightSqrt_mul_sq_eq]
      _ ≤ (1 / (1 - eta)) ^ 2 *
          ∫ x : ℝ, (capWeightSqrt eta R x * s x) ^ 2 := hgrad.2
      _ ≤ (1 / (1 - eta)) ^ 2 * B :=
        mul_le_mul_of_nonneg_left hsourceBound' (sq_nonneg _)

/-- Pointwise-source version tailored to a matched four-profile estimate.
The two input fields can be instantiated by the matched perturbation increment
and by the unshifted perturbation, respectively. -/
theorem capWeight_fourProfile_resolver_commutator_of_pointwise_source_bound
    (p : CMParams) {M eta R CΔ C₀ : ℝ}
    (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    {u₂ u₁ v₂ v₁ delta base : ℝ → ℝ}
    (hu₂ : IsCUnifBdd u₂) (hu₁ : IsCUnifBdd u₁)
    (hv₂ : IsCUnifBdd v₂) (hv₁ : IsCUnifBdd v₁)
    (hu₂_mem : ∀ x, u₂ x ∈ Set.Icc (0 : ℝ) M)
    (hu₁_mem : ∀ x, u₁ x ∈ Set.Icc (0 : ℝ) M)
    (hv₂_mem : ∀ x, v₂ x ∈ Set.Icc (0 : ℝ) M)
    (hv₁_mem : ∀ x, v₁ x ∈ Set.Icc (0 : ℝ) M)
    (hdelta : Integrable (fun x =>
      capWeight eta R x * |delta x| ^ 2))
    (hbase : Integrable (fun x =>
      capWeight eta R x * |base x| ^ 2))
    (hsourcePoint : ∀ x,
      |fourProfilePowerSource p u₂ u₁ v₂ v₁ x| ^ 2 ≤
        CΔ ^ 2 * |delta x| ^ 2 + C₀ ^ 2 * |base x| ^ 2) :
    (Integrable (fun x => capWeight eta R x *
        |fourProfileResolverValue p u₂ u₁ v₂ v₁ x| ^ 2) ∧
      (∫ x : ℝ, capWeight eta R x *
        |fourProfileResolverValue p u₂ u₁ v₂ v₁ x| ^ 2) ≤
          (1 / (1 - eta)) ^ 2 *
            (CΔ ^ 2 * (∫ x : ℝ, capWeight eta R x * |delta x| ^ 2) +
              C₀ ^ 2 * (∫ x : ℝ, capWeight eta R x * |base x| ^ 2))) ∧
    (Integrable (fun x => capWeight eta R x *
        |fourProfileResolverGradient p u₂ u₁ v₂ v₁ x| ^ 2) ∧
      (∫ x : ℝ, capWeight eta R x *
        |fourProfileResolverGradient p u₂ u₁ v₂ v₁ x| ^ 2) ≤
          (1 / (1 - eta)) ^ 2 *
            (CΔ ^ 2 * (∫ x : ℝ, capWeight eta R x * |delta x| ^ 2) +
              C₀ ^ 2 * (∫ x : ℝ, capWeight eta R x * |base x| ^ 2))) := by
  let s : ℝ → ℝ := fourProfilePowerSource p u₂ u₁ v₂ v₁
  let major : ℝ → ℝ := fun x =>
    CΔ ^ 2 * (capWeight eta R x * |delta x| ^ 2) +
      C₀ ^ 2 * (capWeight eta R x * |base x| ^ 2)
  have hs : IsCUnifBdd s := by
    let s₂₁ : ℝ → ℝ := fun x => u₂ x ^ p.γ - u₁ x ^ p.γ
    let sᵥ₂₁ : ℝ → ℝ := fun x => v₂ x ^ p.γ - v₁ x ^ p.γ
    have hs₂₁ : IsCUnifBdd s₂₁ := by
      dsimp [s₂₁]
      exact rpow_difference_isCUnifBdd p.hγ hu₁ hu₂ hu₁_mem hu₂_mem
    have hsᵥ₂₁ : IsCUnifBdd sᵥ₂₁ := by
      dsimp [sᵥ₂₁]
      exact rpow_difference_isCUnifBdd p.hγ hv₁ hv₂ hv₁_mem hv₂_mem
    change IsCUnifBdd (fun x => s₂₁ x - sᵥ₂₁ x)
    exact isCUnifBdd_sub hs₂₁ hsᵥ₂₁
  have hmajor : Integrable major := by
    dsimp [major]
    exact (hdelta.const_mul (CΔ ^ 2)).add (hbase.const_mul (C₀ ^ 2))
  have hpointWeighted : ∀ x,
      capWeight eta R x * |s x| ^ 2 ≤ major x := by
    intro x
    dsimp [s, major]
    calc
      capWeight eta R x *
          |fourProfilePowerSource p u₂ u₁ v₂ v₁ x| ^ 2 ≤
          capWeight eta R x *
            (CΔ ^ 2 * |delta x| ^ 2 + C₀ ^ 2 * |base x| ^ 2) :=
        mul_le_mul_of_nonneg_left (hsourcePoint x) (capWeight_pos eta R x).le
      _ = CΔ ^ 2 * (capWeight eta R x * |delta x| ^ 2) +
          C₀ ^ 2 * (capWeight eta R x * |base x| ^ 2) := by ring
  have hsource : Integrable (fun x => capWeight eta R x *
      |fourProfilePowerSource p u₂ u₁ v₂ v₁ x| ^ 2) := by
    refine Integrable.mono' hmajor
      (((capWeight_continuous eta R).mul (hs.1.abs.pow 2)).aestronglyMeasurable) ?_
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (capWeight_pos eta R x).le (sq_nonneg _))]
      exact hpointWeighted x
  have hsourceBound :
      (∫ x : ℝ, capWeight eta R x *
        |fourProfilePowerSource p u₂ u₁ v₂ v₁ x| ^ 2) ≤
        CΔ ^ 2 * (∫ x : ℝ, capWeight eta R x * |delta x| ^ 2) +
          C₀ ^ 2 * (∫ x : ℝ, capWeight eta R x * |base x| ^ 2) := by
    calc
      (∫ x : ℝ, capWeight eta R x *
          |fourProfilePowerSource p u₂ u₁ v₂ v₁ x| ^ 2) ≤
          ∫ x : ℝ, major x :=
        integral_mono hsource hmajor hpointWeighted
      _ = CΔ ^ 2 * (∫ x : ℝ, capWeight eta R x * |delta x| ^ 2) +
          C₀ ^ 2 * (∫ x : ℝ, capWeight eta R x * |base x| ^ 2) := by
        dsimp [major]
        rw [integral_add (hdelta.const_mul (CΔ ^ 2))
          (hbase.const_mul (C₀ ^ 2)), integral_const_mul, integral_const_mul]
  exact capWeight_fourProfile_resolver_commutator_of_source_bound
    p heta0 heta1 hu₂ hu₁ hv₂ hv₁
      hu₂_mem hu₁_mem hv₂_mem hv₁_mem hsource hsourceBound

#print axioms capWeight_fourProfile_resolver_commutator_of_source_bound
#print axioms capWeight_fourProfile_resolver_commutator_of_pointwise_source_bound

end ShenWork.Paper1

