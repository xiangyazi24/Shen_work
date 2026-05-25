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

theorem IsEquilibrium.eq_zero {p : Params} {x : State} (h : IsEquilibrium p x) :
vectorField p x = 0 :=
h

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

theorem vectorField_contDiff (p : Params) :
    ContDiff ℝ 1 (vectorField p) := by
  rw [contDiff_iff_contDiffAt]
  exact vectorField_contDiffAt p

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

theorem localFlowExists (p : Params) (x₀ : State) (t₀ : ℝ) :
    ∃ r > 0, ∃ eps > 0, ∃ flow : State → ℝ → State,
    ∀ x ∈ Metric.closedBall x₀ r,
      flow x t₀ = x ∧
      ∀ t ∈ Ioo (t₀ - eps) (t₀ + eps),
        HasDerivAt (flow x) (vectorField p (flow x t)) t := by
  obtain ⟨eps, heps, a, r, L, K, hr, hPL⟩ := picardLindelofData p x₀
  refine ⟨r, by exact_mod_cast hr, eps, heps, ?_⟩
  obtain ⟨flow, hflow⟩ :=
    (hPL t₀).exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt
  refine ⟨flow, fun x hx => ?_⟩
  refine ⟨(hflow x hx).1, fun t ht => ?_⟩
  exact ((hflow x hx).2 t (Ioo_subset_Icc_self ht)).hasDerivAt
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

theorem HasEigenpair.eigen_eq
    {A : Matrix Idx Idx ℝ} {lam : ℝ} {v : State}
    (h : HasEigenpair A lam v) :
matVec4 A v = lam • v :=
h.1

theorem HasEigenpair.ne_zero
    {A : Matrix Idx Idx ℝ} {lam : ℝ} {v : State}
    (h : HasEigenpair A lam v) :
v ≠ 0 :=
h.2

def LinearUnstable (A : Matrix Idx Idx ℝ) : Prop :=
  ∃ lam : ℝ, 0 < lam ∧ ∃ v : State, HasEigenpair A lam v

theorem LinearUnstable.exists_positive_eigenpair
    {A : Matrix Idx Idx ℝ} (h : LinearUnstable A) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ v : State, HasEigenpair A lam v :=
  h

def characteristicAtOne (p : Params) (lam : ℝ) : Prop :=
(lam ^ 2 + p.c * lam - (p.alpha : ℝ) + p.chi * (p.gamma : ℝ))
* (lam ^ 2 - 1)
+ p.chi * (p.gamma : ℝ) = 0

theorem characteristicAtOne.eq_zero
    {p : Params} {lam : ℝ} (h : characteristicAtOne p lam) :
    (lam ^ 2 + p.c * lam - (p.alpha : ℝ) + p.chi * (p.gamma : ℝ))
    * (lam ^ 2 - 1)
    + p.chi * (p.gamma : ℝ) = 0 :=
  h

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

theorem OneDimUnstableRoot.exists_unique
    {p : Params} (h : OneDimUnstableRoot p) :
∃! lam : ℝ, 0 < lam ∧ characteristicAtOne p lam :=
h

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

theorem SolvesTWODE.hasDerivAt
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) (t : ℝ) :
    HasDerivAt z (vectorField p (z t)) t :=
  h t

theorem SolvesTWODE.differentiable
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) :
    Differentiable ℝ z :=
  fun t => (h.hasDerivAt t).differentiableAt

theorem SolvesTWODE.deriv_eq_vectorField
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) :
    deriv z = fun t => vectorField p (z t) := by
  funext t
  exact (h.hasDerivAt t).deriv

theorem SolvesTWODE.contDiff_one
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) :
    ContDiff ℝ 1 z := by
  rw [contDiff_one_iff_deriv]
  refine ⟨h.differentiable, ?_⟩
  rw [h.deriv_eq_vectorField]
  exact (vectorField_contDiff p).continuous.comp h.differentiable.continuous

theorem SolvesTWODE.contDiff_two
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) :
    ContDiff ℝ 2 z := by
  rw [show (2 : WithTop ℕ∞) = (1 : WithTop ℕ∞) + 1 by norm_num,
    contDiff_succ_iff_deriv]
  refine ⟨h.differentiable, by simp, ?_⟩
  rw [h.deriv_eq_vectorField]
  simpa [Function.comp_def] using (vectorField_contDiff p).comp h.contDiff_one

theorem SolvesTWODE.component_contDiff_two
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) (i : Idx) :
    ContDiff ℝ 2 (fun t => z t i) :=
  contDiff_pi.mp h.contDiff_two i

theorem SolvesTWODE.hasDerivAt_component
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) (i : Idx) (t : ℝ) :
    HasDerivAt (fun s => z s i) ((vectorField p (z t)) i) t := by
  simpa only [ContinuousLinearMap.proj_apply] using
    ((ContinuousLinearMap.proj i : State →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
      (h.hasDerivAt t))

theorem SolvesTWODE.deriv_component
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) (i : Idx) (t : ℝ) :
    deriv (fun s => z s i) t = (vectorField p (z t)) i :=
  (h.hasDerivAt_component i t).deriv

theorem SolvesTWODE.hasDerivAt_U
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) (t : ℝ) :
    HasDerivAt (fun s => z s 0) (z t 1) t := by
  simpa [vectorField] using h.hasDerivAt_component (0 : Idx) t

theorem SolvesTWODE.hasDerivAt_V
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) (t : ℝ) :
    HasDerivAt (fun s => z s 2) (z t 3) t := by
  simpa [vectorField] using h.hasDerivAt_component (2 : Idx) t

theorem SolvesTWODE.hasDerivAt_deriv_U
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) (t : ℝ) :
    HasDerivAt (deriv (fun s => z s 0))
      (-p.c * z t 1
        + p.chi *
          ((p.m : ℝ) * (z t 0) ^ (p.m - 1) * z t 1 * z t 3
            + (z t 0) ^ p.m * (z t 2 - (z t 0) ^ p.gamma))
        - z t 0 * (1 - (z t 0) ^ p.alpha)) t := by
  have hderiv : deriv (fun s => z s 0) = fun s => z s 1 := by
    funext s
    exact (h.hasDerivAt_U s).deriv
  rw [hderiv]
  simpa [vectorField] using h.hasDerivAt_component (1 : Idx) t

theorem SolvesTWODE.hasDerivAt_deriv_V
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) (t : ℝ) :
    HasDerivAt (deriv (fun s => z s 2)) (z t 2 - (z t 0) ^ p.gamma) t := by
  have hderiv : deriv (fun s => z s 2) = fun s => z s 3 := by
    funext s
    exact (h.hasDerivAt_V s).deriv
  rw [hderiv]
  simpa [vectorField] using h.hasDerivAt_component (3 : Idx) t

theorem SolvesTWODE.profile_c2_bootstrap
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) :
    ContDiff ℝ 2 (fun t => z t 0) ∧
    ContDiff ℝ 2 (fun t => z t 2) ∧
    (∀ t : ℝ,
      HasDerivAt (deriv (fun s => z s 0))
        (-p.c * z t 1
          + p.chi *
            ((p.m : ℝ) * (z t 0) ^ (p.m - 1) * z t 1 * z t 3
              + (z t 0) ^ p.m * (z t 2 - (z t 0) ^ p.gamma))
          - z t 0 * (1 - (z t 0) ^ p.alpha)) t) ∧
    (∀ t : ℝ, HasDerivAt (deriv (fun s => z s 2))
      (z t 2 - (z t 0) ^ p.gamma) t) := by
  exact ⟨h.component_contDiff_two 0, h.component_contDiff_two 2,
    h.hasDerivAt_deriv_U, h.hasDerivAt_deriv_V⟩

theorem SolvesTWODE.chemotaxis_deriv
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) (t : ℝ) :
    deriv (fun y => (z y 0) ^ p.m * deriv (fun s => z s 2) y) t =
      (p.m : ℝ) * (z t 0) ^ (p.m - 1) * z t 1 * z t 3
        + (z t 0) ^ p.m * (z t 2 - (z t 0) ^ p.gamma) := by
  have hpow :
      HasDerivAt (fun y => (z y 0) ^ p.m)
        ((p.m : ℝ) * (z t 0) ^ (p.m - 1) * z t 1) t := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (h.hasDerivAt_U t).pow p.m
  have hV' : deriv (fun s => z s 2) t = z t 3 :=
    (h.hasDerivAt_V t).deriv
  simpa [hV', mul_assoc, mul_left_comm, mul_comm] using
    (hpow.mul (h.hasDerivAt_deriv_V t)).deriv

theorem SolvesTWODE.profile_U_equation
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) (t : ℝ) :
    iteratedDeriv 2 (fun s => z s 0) t
      + p.c * deriv (fun s => z s 0) t
      - p.chi * deriv (fun y => (z y 0) ^ p.m * deriv (fun s => z s 2) y) t
      + z t 0 * (1 - (z t 0) ^ p.alpha) = 0 := by
  have hU' : deriv (fun s => z s 0) t = z t 1 :=
    (h.hasDerivAt_U t).deriv
  have hU'' :
      iteratedDeriv 2 (fun s => z s 0) t =
        -p.c * z t 1
          + p.chi *
            ((p.m : ℝ) * (z t 0) ^ (p.m - 1) * z t 1 * z t 3
              + (z t 0) ^ p.m * (z t 2 - (z t 0) ^ p.gamma))
          - z t 0 * (1 - (z t 0) ^ p.alpha) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact (h.hasDerivAt_deriv_U t).deriv
  rw [hU'', hU', h.chemotaxis_deriv t]
  ring

theorem SolvesTWODE.profile_V_equation
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) (t : ℝ) :
    iteratedDeriv 2 (fun s => z s 2) t - z t 2 + (z t 0) ^ p.gamma = 0 := by
  have hV'' :
      iteratedDeriv 2 (fun s => z s 2) t =
        z t 2 - (z t 0) ^ p.gamma := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact (h.hasDerivAt_deriv_V t).deriv
  rw [hV'']
  ring

theorem SolvesTWODE.profile_equations
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) :
    (∀ t : ℝ,
      iteratedDeriv 2 (fun s => z s 0) t
        + p.c * deriv (fun s => z s 0) t
        - p.chi * deriv (fun y => (z y 0) ^ p.m * deriv (fun s => z s 2) y) t
        + z t 0 * (1 - (z t 0) ^ p.alpha) = 0) ∧
    (∀ t : ℝ,
      iteratedDeriv 2 (fun s => z s 2) t - z t 2 + (z t 0) ^ p.gamma = 0) :=
  ⟨h.profile_U_equation, h.profile_V_equation⟩

structure TravelingWave (p : Params) where
z : ℝ → State
ode : SolvesTWODE p z
leftLimit : Tendsto z atBot (nhds E1)
rightLimit : Tendsto z atTop (nhds E0)

theorem TravelingWave.profile_c2_bootstrap
    {p : Params} (w : TravelingWave p) :
    ContDiff ℝ 2 (fun t => w.z t 0) ∧
    ContDiff ℝ 2 (fun t => w.z t 2) ∧
    (∀ t : ℝ,
      HasDerivAt (deriv (fun s => w.z s 0))
        (-p.c * w.z t 1
          + p.chi *
            ((p.m : ℝ) * (w.z t 0) ^ (p.m - 1) * w.z t 1 * w.z t 3
              + (w.z t 0) ^ p.m * (w.z t 2 - (w.z t 0) ^ p.gamma))
          - w.z t 0 * (1 - (w.z t 0) ^ p.alpha)) t) ∧
    (∀ t : ℝ, HasDerivAt (deriv (fun s => w.z s 2))
      (w.z t 2 - (w.z t 0) ^ p.gamma) t) :=
  w.ode.profile_c2_bootstrap

theorem TravelingWave.profile_equations
    {p : Params} (w : TravelingWave p) :
    (∀ t : ℝ,
      iteratedDeriv 2 (fun s => w.z s 0) t
        + p.c * deriv (fun s => w.z s 0) t
        - p.chi * deriv
            (fun y => (w.z y 0) ^ p.m * deriv (fun s => w.z s 2) y) t
        + w.z t 0 * (1 - (w.z t 0) ^ p.alpha) = 0) ∧
    (∀ t : ℝ,
      iteratedDeriv 2 (fun s => w.z s 2) t - w.z t 2
        + (w.z t 0) ^ p.gamma = 0) :=
  w.ode.profile_equations

theorem TravelingWave.profile_U_equation
    {p : Params} (w : TravelingWave p) (t : ℝ) :
    iteratedDeriv 2 (fun s => w.z s 0) t
      + p.c * deriv (fun s => w.z s 0) t
      - p.chi * deriv
          (fun y => (w.z y 0) ^ p.m * deriv (fun s => w.z s 2) y) t
      + w.z t 0 * (1 - (w.z t 0) ^ p.alpha) = 0 :=
  w.ode.profile_U_equation t

theorem TravelingWave.profile_V_equation
    {p : Params} (w : TravelingWave p) (t : ℝ) :
    iteratedDeriv 2 (fun s => w.z s 2) t - w.z t 2
      + (w.z t 0) ^ p.gamma = 0 :=
  w.ode.profile_V_equation t

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

theorem local_shooting_segment_from_E0_stable_eigenpair
    (p : Params) {δ t₀ : ℝ} :
    ∃ v : State,
      (-1 : ℝ) < 0 ∧
      HasEigenpair (jacobianAtZero p) (-1) v ∧
      ∃ r > 0, ∃ eps > 0,
        (E0 + δ • v ∈ Metric.closedBall E0 r →
          ∃ z : ℝ → State,
            z t₀ = E0 + δ • v ∧
            ∀ t ∈ Ioo (t₀ - eps) (t₀ + eps),
              HasDerivAt z (vectorField p (z t)) t) := by
  let v : State := stableVectorAtZero
  have hv : HasEigenpair (jacobianAtZero p) (-1) v := by
    simpa [v] using jacobianAtZero_stable_eigenpair p
  obtain ⟨r, hr, eps, heps, hloc⟩ := localSolutionExists p E0 t₀
  refine ⟨v, by norm_num, hv, r, hr, eps, heps, ?_⟩
  intro hnear
  exact hloc (E0 + δ • v) hnear

def HasHeteroclinicE1E0 (p : Params) : Prop :=
  ∃ z : ℝ → State,
    SolvesTWODE p z ∧
    Tendsto z atBot (nhds E1) ∧
    Tendsto z atTop (nhds E0)

theorem HasHeteroclinicE1E0.exists_solution
    {p : Params} (h : HasHeteroclinicE1E0 p) :
    ∃ z : ℝ → State,
      SolvesTWODE p z ∧
      Tendsto z atBot (nhds E1) ∧
      Tendsto z atTop (nhds E0) :=
  h

theorem travelingWave_of_heteroclinic
    (p : Params)
    (h : HasHeteroclinicE1E0 p) :
    Nonempty (TravelingWave p) := by
  rcases h with ⟨z, hzode, hleft, hright⟩
  exact ⟨⟨z, hzode, hleft, hright⟩⟩

end TravelingWaveODE
end PDE
end ShenWork
