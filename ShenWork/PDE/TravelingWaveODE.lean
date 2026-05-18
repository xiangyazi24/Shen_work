import Mathlib

noncomputable section

open Set Filter Topology

namespace ShenWork
namespace PDE
namespace TravelingWaveODE

abbrev Idx : Type := Fin 4
abbrev State : Type := Idx → ℝ

structure Params where
c : ℝ
chi : ℝ
m : ℕ
alpha : ℕ
gamma : ℕ
hm : 0 < m
halpha : 0 < alpha
hgamma : 0 < gamma

def E1 : State := ![1, 0, 1, 0]
def E0 : State := ![0, 0, 0, 0]

def vectorField (p : Params) (x : State) : State :=
![
x 1,
-p.c * x 1
+ p.chi *
((p.m : ℝ) * (x 0) ^ (p.m - 1) * x 1 * x 3
+ (x 0) ^ p.m * (x 2 - (x 0) ^ p.gamma))
- x 0 * (1 - (x 0) ^ p.alpha),
x 3,
x 2 - (x 0) ^ p.gamma
]

def IsEquilibrium (p : Params) (x : State) : Prop :=
vectorField p x = 0

@[simp]
theorem vectorField_E1 (p : Params) :
    vectorField p E1 = 0 := by
  funext i; fin_cases i <;> simp [vectorField, E1, one_pow] <;> ring

@[simp]
theorem vectorField_E0 (p : Params) :
    vectorField p E0 = 0 := by
  funext i; fin_cases i <;>
    simp [vectorField, E0, Nat.ne_of_gt p.hm, Nat.ne_of_gt p.hgamma, zero_pow] <;> ring

theorem E1_equilibrium (p : Params) :
IsEquilibrium p E1 := by
exact vectorField_E1 p

theorem E0_equilibrium (p : Params) :
IsEquilibrium p E0 := by
exact vectorField_E0 p

def powSlopeAtZero (n : ℕ) : ℝ :=
if n = 1 then 1 else 0

def jacobianAtOne (p : Params) : Matrix Idx Idx ℝ :=
!![
0, 1, 0, 0;
(p.alpha : ℝ) - p.chi * (p.gamma : ℝ), -p.c, p.chi, 0;
0, 0, 0, 1;
-(p.gamma : ℝ), 0, 1, 0
]

def jacobianAtZero (p : Params) : Matrix Idx Idx ℝ :=
!![
0, 1, 0, 0;
-1, -p.c, 0, 0;
0, 0, 0, 1;
-powSlopeAtZero p.gamma, 0, 1, 0
]

def matVec4 (A : Matrix Idx Idx ℝ) (x : State) : State :=
fun i =>
A i 0 * x 0
+ A i 1 * x 1
+ A i 2 * x 2
+ A i 3 * x 3

def jacobianAtOneLin (p : Params) (x : State) : State :=
![
x 1,
((p.alpha : ℝ) - p.chi * (p.gamma : ℝ)) * x 0
- p.c * x 1
+ p.chi * x 2,
x 3,
-(p.gamma : ℝ) * x 0 + x 2
]

def jacobianAtZeroLin (p : Params) (x : State) : State :=
![
x 1,
-x 0 - p.c * x 1,
x 3,
-powSlopeAtZero p.gamma * x 0 + x 2
]

@[simp]
theorem matVec4_jacobianAtOne (p : Params) (x : State) :
matVec4 (jacobianAtOne p) x = jacobianAtOneLin p x := by
ext i <;> fin_cases i <;>
simp [matVec4, jacobianAtOne, jacobianAtOneLin] <;>
ring

@[simp]
theorem matVec4_jacobianAtZero (p : Params) (x : State) :
matVec4 (jacobianAtZero p) x = jacobianAtZeroLin p x := by
ext i <;> fin_cases i <;>
simp [matVec4, jacobianAtZero, jacobianAtZeroLin] <;>
ring

theorem vectorField_contDiffAt (p : Params) (x : State) :
    ContDiffAt ℝ 1 (vectorField p) x := by
  apply ContDiffAt.of_le _ le_top
  have hi : ∀ i : Idx, ContDiffAt ℝ ⊤ (fun x : State => x i) x :=
    fun i => (ContinuousLinearMap.proj i : (Idx → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt
  have h0 := hi 0; have h1 := hi 1; have h2 := hi 2; have h3 := hi 3
  unfold vectorField
  refine contDiffAt_pi.mpr fun i => ?_
  fin_cases i <;> dsimp
  · exact h1
  · have hchem :
        ContDiffAt ℝ ⊤
          (fun x : State =>
            (p.m : ℝ) * x 0 ^ (p.m - 1) * x 1 * x 3
              + x 0 ^ p.m * (x 2 - x 0 ^ p.gamma)) x :=
      (((contDiffAt_const (c := (p.m : ℝ))).mul (h0.pow (p.m - 1))).mul h1 |>.mul h3).add
        ((h0.pow p.m).mul (h2.sub (h0.pow p.gamma)))
    have hrep :
        ContDiffAt ℝ ⊤
          (fun x : State =>
            p.chi *
              ((p.m : ℝ) * x 0 ^ (p.m - 1) * x 1 * x 3
                + x 0 ^ p.m * (x 2 - x 0 ^ p.gamma))) x :=
      (contDiffAt_const (c := p.chi)).mul hchem
    have hgrowth :
        ContDiffAt ℝ ⊤
          (fun x : State => x 0 * (1 - x 0 ^ p.alpha)) x :=
      h0.mul ((contDiffAt_const (c := (1 : ℝ))).sub (h0.pow p.alpha))
    simpa [neg_mul] using (((contDiffAt_const (c := p.c)).mul h1).neg.add hrep).sub hgrowth
  · exact h3
  · exact h2.sub (h0.pow p.gamma)

theorem picardLindelofData (p : Params) (x₀ : State) :
∃ (eps : ℝ) (heps : 0 < eps) (a r L K : NNReal) (_ : 0 < r),
∀ t₀ : ℝ,
IsPicardLindelof
(fun _ : ℝ => vectorField p)
(⟨t₀, by constructor <;> linarith [heps]⟩ :
Set.Icc (t₀ - eps) (t₀ + eps))
x₀ a r L K := by
simpa using IsPicardLindelof.of_contDiffAt_one (vectorField_contDiffAt p x₀)

theorem localSolutionExists (p : Params) (x₀ : State) (t₀ : ℝ) :
    ∃ r > 0, ∃ eps > 0, ∀ x ∈ Metric.closedBall x₀ r,
    ∃ z : ℝ → State,
    z t₀ = x ∧ ∀ t ∈ Ioo (t₀ - eps) (t₀ + eps),
      HasDerivAt z (vectorField p (z t)) t := by
  obtain ⟨eps, heps, a, r, L, K, hr, hPL⟩ := picardLindelofData p x₀
  refine ⟨r, by exact_mod_cast hr, eps, heps, fun x hx => ?_⟩
  obtain ⟨α, hα⟩ := (hPL t₀).exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt
  refine ⟨α x, (hα x hx).1, fun t ht => ?_⟩
  exact ((hα x hx).2 t (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))

structure PhasePortrait (p : Params) where
source : State
target : State
source_eq : IsEquilibrium p source
target_eq : IsEquilibrium p target
sourceJacobian : Matrix Idx Idx ℝ
targetJacobian : Matrix Idx Idx ℝ

def phasePortrait (p : Params) : PhasePortrait p where
source := E1
target := E0
source_eq := E1_equilibrium p
target_eq := E0_equilibrium p
sourceJacobian := jacobianAtOne p
targetJacobian := jacobianAtZero p

def HasEigenpair (A : Matrix Idx Idx ℝ) (lam : ℝ) (v : State) : Prop :=
matVec4 A v = lam • v ∧ v ≠ 0

def LinearUnstable (A : Matrix Idx Idx ℝ) : Prop :=
  ∃ lam : ℝ, 0 < lam ∧ ∃ v : State, HasEigenpair A lam v

def characteristicAtOne (p : Params) (lam : ℝ) : Prop :=
(lam ^ 2 + p.c * lam - (p.alpha : ℝ) + p.chi * (p.gamma : ℝ))
* (lam ^ 2 - 1)
+ p.chi * (p.gamma : ℝ) = 0

def unstableVectorAtOne (p : Params) (lam : ℝ) : State :=
![
-(lam ^ 2 - 1),
lam * (-(lam ^ 2 - 1)),
(p.gamma : ℝ),
lam * (p.gamma : ℝ)
]

theorem unstableVectorAtOne_ne_zero (p : Params) (lam : ℝ) :
    unstableVectorAtOne p lam ≠ 0 := by
  intro h
  have h2 : (p.gamma : ℝ) = 0 := by
    simpa [unstableVectorAtOne] using congr_fun h (2 : Idx)
  have hg : (0 : ℝ) < (p.gamma : ℝ) := by exact_mod_cast p.hgamma
  linarith

theorem jacobianAtOne_unstableVector_eigen
    (p : Params) {lam : ℝ}
    (hchar : characteristicAtOne p lam) :
    matVec4 (jacobianAtOne p) (unstableVectorAtOne p lam)
    = lam • unstableVectorAtOne p lam := by
  unfold characteristicAtOne at hchar
  ext i; fin_cases i <;>
    simp [matVec4, jacobianAtOne, unstableVectorAtOne, Pi.smul_apply, smul_eq_mul] <;>
    (try ring) <;>
    linear_combination hchar

theorem jacobianAtOne_eigenpair_of_characteristic
(p : Params) {lam : ℝ}
(hchar : characteristicAtOne p lam) :
HasEigenpair (jacobianAtOne p) lam (unstableVectorAtOne p lam) := by
constructor
· exact jacobianAtOne_unstableVector_eigen p hchar
· exact unstableVectorAtOne_ne_zero p lam

theorem jacobianAtOne_linearUnstable_of_root
(p : Params) {lam : ℝ}
(hpos : 0 < lam)
(hchar : characteristicAtOne p lam) :
LinearUnstable (jacobianAtOne p) := by
refine ⟨lam, hpos, unstableVectorAtOne p lam, ?_⟩
exact jacobianAtOne_eigenpair_of_characteristic p hchar

def OneDimUnstableRoot (p : Params) : Prop :=
∃! lam : ℝ, 0 < lam ∧ characteristicAtOne p lam

theorem jacobianAtOne_linearUnstable_of_oneDimRoot
(p : Params)
(hroot : OneDimUnstableRoot p) :
LinearUnstable (jacobianAtOne p) := by
rcases hroot with ⟨lam, hlam, _huniq⟩
exact jacobianAtOne_linearUnstable_of_root p hlam.1 hlam.2

def stableVectorAtZero : State :=
![0, 0, 1, -1]

theorem stableVectorAtZero_ne_zero :
    stableVectorAtZero ≠ 0 := by
  intro h
  have h2 : (1 : ℝ) = 0 := by
    simpa [stableVectorAtZero] using congr_fun h (2 : Idx)
  norm_num at h2

theorem jacobianAtZero_stable_eigenpair (p : Params) :
    HasEigenpair (jacobianAtZero p) (-1) stableVectorAtZero := by
  refine ⟨?_, stableVectorAtZero_ne_zero⟩
  ext i; fin_cases i <;>
    simp [matVec4, jacobianAtZero, stableVectorAtZero, powSlopeAtZero,
      Pi.smul_apply, smul_eq_mul]

def SolvesTWODE (p : Params) (z : ℝ → State) : Prop :=
∀ t : ℝ, HasDerivAt z (vectorField p (z t)) t

structure TravelingWave (p : Params) where
z : ℝ → State
ode : SolvesTWODE p z
leftLimit : Tendsto z atBot (nhds E1)
rightLimit : Tendsto z atTop (nhds E0)

theorem local_shooting_segment_from_E1_positive_eigenpair
    (p : Params) {lam δ t₀ : ℝ}
    (hpos : 0 < lam)
    (hchar : characteristicAtOne p lam) :
    ∃ v : State,
      0 < lam ∧
      HasEigenpair (jacobianAtOne p) lam v ∧
      ∃ r > 0, ∃ eps > 0,
        (E1 + δ • v ∈ Metric.closedBall E1 r →
          ∃ z : ℝ → State,
            z t₀ = E1 + δ • v ∧
            ∀ t ∈ Ioo (t₀ - eps) (t₀ + eps),
              HasDerivAt z (vectorField p (z t)) t) := by
  let v : State := unstableVectorAtOne p lam
  have hv : HasEigenpair (jacobianAtOne p) lam v := by
    simpa [v] using jacobianAtOne_eigenpair_of_characteristic p hchar
  obtain ⟨r, hr, eps, heps, hloc⟩ := localSolutionExists p E1 t₀
  refine ⟨v, hpos, hv, r, hr, eps, heps, ?_⟩
  intro hnear
  exact hloc (E1 + δ • v) hnear

theorem local_shooting_segment_from_E1_oneDimRoot
    (p : Params) (hroot : OneDimUnstableRoot p) {δ t₀ : ℝ} :
    ∃ lam : ℝ,
      0 < lam ∧
      characteristicAtOne p lam ∧
      ∃ v : State,
        HasEigenpair (jacobianAtOne p) lam v ∧
        ∃ r > 0, ∃ eps > 0,
          (E1 + δ • v ∈ Metric.closedBall E1 r →
            ∃ z : ℝ → State,
              z t₀ = E1 + δ • v ∧
              ∀ t ∈ Ioo (t₀ - eps) (t₀ + eps),
                HasDerivAt z (vectorField p (z t)) t) := by
  rcases hroot with ⟨lam, ⟨hpos, hchar⟩, _huniq⟩
  obtain ⟨v, _hpos, hv, r, hr, eps, heps, hseg⟩ :=
    local_shooting_segment_from_E1_positive_eigenpair
      (p := p) (lam := lam) (δ := δ) (t₀ := t₀) hpos hchar
  exact ⟨lam, hpos, hchar, v, hv, r, hr, eps, heps, hseg⟩

def HasHeteroclinicE1E0 (p : Params) : Prop :=
  ∃ z : ℝ → State,
    SolvesTWODE p z ∧
    Tendsto z atBot (nhds E1) ∧
    Tendsto z atTop (nhds E0)

theorem travelingWave_of_heteroclinic
    (p : Params)
    (h : HasHeteroclinicE1E0 p) :
    Nonempty (TravelingWave p) := by
  rcases h with ⟨z, hzode, hleft, hright⟩
  exact ⟨⟨z, hzode, hleft, hright⟩⟩

end TravelingWaveODE
end PDE
end ShenWork
