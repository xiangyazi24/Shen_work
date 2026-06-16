/-
  ShenWork/Paper1/WaveRotheHelly.lean

  **Helly pointwise selection — the combinatorial kernel of the B1 Rothe
  compactness field, PROVED axiom-clean.**

  `WaveRotheSchauderData.lean` carries `HellyPointwiseSelection M` as an explicit,
  satisfiable hypothesis of `Tmap_compactRange`:

      `HellyPointwiseSelection (Λ : ℝ) : Prop :=`
      `  ∀ gs : ℕ → ℝ → ℝ,`
      `    (∀ k, ∀ x y, |gs k x - gs k y| ≤ Λ * |x - y|) →`
      `    (∀ k x, |gs k x| ≤ Λ) →`
      `      ∃ subseq : ℕ → ℕ, StrictMono subseq ∧`
      `        ∃ g : ℝ → ℝ,`
      `          (∀ x, Tendsto (fun n => gs (subseq n) x) atTop (𝓝 (g x))) ∧`
      `          (∀ x y, |g x - g y| ≤ Λ * |x - y|)`

  This file DISCHARGES that hypothesis: `helly_pointwise_selection M`.

  ## Route (Helly / Cantor diagonal, via Tychonoff seq-compactness)

  The Cantor diagonal over a countable dense set is realised here *without any
  hand-rolled nested-subsequence recursion*: it is exactly the sequential
  compactness of the Tychonoff cube `[-Λ,Λ]^ℚ`.

  1. Pack the iterates as points of the product space `ℚ → ℝ`:
     `F k := fun q : ℚ => gs k (q : ℝ)`.  Each `F k` lies in the compact set
     `S := Set.pi univ (fun _ => Icc (-Λ) Λ)` (Tychonoff, `isCompact_univ_pi`).
  2. `IsCompact.isSeqCompact` extracts a `StrictMono` subsequence `φ` with
     `F ∘ φ → f₀` in the product topology.  Product convergence is *pointwise*
     (`tendsto_pi_nhds`), i.e. `gs (φ n) q → f₀ q` for **every rational** `q` —
     this is the diagonal.
  3. Equi-Lipschitz upgrades rational pointwise convergence to convergence at
     every real `x`: `n ↦ gs (φ n) x` is `CauchySeq` (squeeze through a nearby
     rational, `exists_rat_near` + the uniform Lipschitz constant), so it
     converges; define `g x` as that limit.
  4. The Lipschitz bound passes to the limit (`le_of_tendsto`).

  Only the standard `Classical/propext/Quot` axioms are used; verified by
  `#print axioms`.  NO `sorry` / `admit` / `native_decide` / extra `axiom`.
-/
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Sequences
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Algebra.Order.Archimedean.Basic
import ShenWork.Paper1.WaveRotheSchauderData

open Filter Topology Set

namespace ShenWork.Paper1

/-- **Diagonal extraction (Tychonoff seq-compactness packaging).**
From a uniformly `[-Λ,Λ]`-bounded sequence `gs`, there is a `StrictMono`
subsequence `φ` together with a limit-on-rationals `f₀ : ℚ → ℝ` such that
`gs (φ n) q → f₀ q` for every rational `q`.  This is the genuine Cantor diagonal,
realised as the sequential compactness of the cube `[-Λ,Λ]^ℚ`. -/
theorem helly_rational_diagonal {Λ : ℝ}
    (gs : ℕ → ℝ → ℝ) (hB : ∀ k x, |gs k x| ≤ Λ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f₀ : ℚ → ℝ,
      ∀ q : ℚ, Tendsto (fun n => gs (φ n) (q : ℝ)) atTop (𝓝 (f₀ q)) := by
  -- the compact Tychonoff cube `[-Λ,Λ]^ℚ`
  set S : Set (ℚ → ℝ) := Set.pi univ (fun _ : ℚ => Icc (-Λ) Λ) with hS
  have hScompact : IsCompact S := isCompact_univ_pi (fun _ => isCompact_Icc)
  -- iterate `k` as a point of the cube
  set F : ℕ → (ℚ → ℝ) := fun k q => gs k (q : ℝ) with hF
  have hFmem : ∀ k, F k ∈ S := by
    intro k
    intro q _
    have hk := hB k (q : ℝ)
    rw [abs_le] at hk
    exact ⟨hk.1, hk.2⟩
  -- sequential compactness extracts the diagonal subsequence
  obtain ⟨f₀, _hf₀S, φ, hφ, hconv⟩ := hScompact.isSeqCompact hFmem
  refine ⟨φ, hφ, f₀, ?_⟩
  -- product-topology convergence is pointwise convergence at each rational
  have hpt := (tendsto_pi_nhds (f := F ∘ φ) (g := f₀) (u := atTop)).1 hconv
  intro q
  exact hpt q

/-- **Helly pointwise selection — PROVED.**
Discharges the carried `HellyPointwiseSelection Λ` hypothesis.  From any
uniformly `Λ`-Lipschitz, uniformly `Λ`-bounded sequence `gs`, a `StrictMono`
subsequence converges *pointwise at every real `x`* to a limit `g` inheriting the
Lipschitz bound `Λ`. -/
theorem helly_pointwise_selection (Λ : ℝ) : HellyPointwiseSelection Λ := by
  intro gs hLip hB
  -- diagonal subsequence converging at every rational
  obtain ⟨φ, hφ, f₀, hrat⟩ := helly_rational_diagonal gs hB
  -- a nonnegative Lipschitz constant is needed for the squeeze
  have hΛ0 : 0 ≤ Λ := le_trans (abs_nonneg _) (hB 0 0)
  -- STEP 1: the subsequence is `CauchySeq` at every real `x`
  have hcauchy : ∀ x : ℝ, CauchySeq (fun n => gs (φ n) x) := by
    intro x
    rw [Metric.cauchySeq_iff]
    intro ε hε
    -- pick a rational `q` close to `x`: `|x - q| < ε / (4Λ + 4)`
    set δ : ℝ := ε / (4 * Λ + 4) with hδ
    have hden : (0 : ℝ) < 4 * Λ + 4 := by linarith
    have hδpos : 0 < δ := by positivity
    obtain ⟨q, hq⟩ := exists_rat_near x hδpos
    -- the rational sequence is itself Cauchy (it converges)
    have hqCauchy : CauchySeq (fun n => gs (φ n) (q : ℝ)) :=
      (hrat q).cauchySeq
    rw [Metric.cauchySeq_iff] at hqCauchy
    obtain ⟨N, hN⟩ := hqCauchy (ε / 3) (by linarith)
    refine ⟨N, ?_⟩
    intro m hm n hn
    -- the three-term Lipschitz squeeze
    have hxm : |gs (φ m) x - gs (φ m) (q : ℝ)| ≤ Λ * |x - q| := hLip (φ m) x q
    have hxn : |gs (φ n) x - gs (φ n) (q : ℝ)| ≤ Λ * |x - q| := hLip (φ n) x q
    have hmid : dist (gs (φ m) (q : ℝ)) (gs (φ n) (q : ℝ)) < ε / 3 := hN m hm n hn
    rw [Real.dist_eq] at hmid ⊢
    -- bound `Λ * |x - q|` by `ε / 4`
    have hLqbound : Λ * |x - q| ≤ ε / 4 := by
      have hqlt : |x - (q : ℝ)| < δ := hq
      have : Λ * |x - (q : ℝ)| ≤ Λ * δ := by
        apply mul_le_mul_of_nonneg_left (le_of_lt hqlt) hΛ0
      have hδeq : δ * (4 * Λ + 4) = ε := by
        rw [hδ]; field_simp
      have hΛδ : Λ * δ ≤ ε / 4 := by
        have hδ0 : 0 ≤ δ := hδpos.le
        nlinarith [hδeq, hδ0, hΛ0]
      linarith
    -- triangle inequality
    have htri : |gs (φ m) x - gs (φ n) x|
        ≤ |gs (φ m) x - gs (φ m) (q : ℝ)|
          + |gs (φ m) (q : ℝ) - gs (φ n) (q : ℝ)|
          + |gs (φ n) (q : ℝ) - gs (φ n) x| := by
      calc |gs (φ m) x - gs (φ n) x|
          = |(gs (φ m) x - gs (φ m) (q : ℝ))
              + (gs (φ m) (q : ℝ) - gs (φ n) (q : ℝ))
              + (gs (φ n) (q : ℝ) - gs (φ n) x)| := by ring_nf
        _ ≤ |(gs (φ m) x - gs (φ m) (q : ℝ))
              + (gs (φ m) (q : ℝ) - gs (φ n) (q : ℝ))|
              + |gs (φ n) (q : ℝ) - gs (φ n) x| := abs_add_le _ _
        _ ≤ (|gs (φ m) x - gs (φ m) (q : ℝ)|
              + |gs (φ m) (q : ℝ) - gs (φ n) (q : ℝ)|)
              + |gs (φ n) (q : ℝ) - gs (φ n) x| := by
              gcongr; exact abs_add_le _ _
    -- rewrite the last term as a flipped distance
    have hxn' : |gs (φ n) (q : ℝ) - gs (φ n) x| ≤ Λ * |x - q| := by
      rw [abs_sub_comm]; exact hxn
    have hmid' : |gs (φ m) (q : ℝ) - gs (φ n) (q : ℝ)| < ε / 3 := hmid
    -- assemble: ≤ ε/4 + ε/3 + ε/4 < ε
    calc |gs (φ m) x - gs (φ n) x|
        ≤ |gs (φ m) x - gs (φ m) (q : ℝ)|
            + |gs (φ m) (q : ℝ) - gs (φ n) (q : ℝ)|
            + |gs (φ n) (q : ℝ) - gs (φ n) x| := htri
      _ < ε / 4 + ε / 3 + ε / 4 := by
            have h1 : |gs (φ m) x - gs (φ m) (q : ℝ)| ≤ ε / 4 := le_trans hxm hLqbound
            have h3 : |gs (φ n) (q : ℝ) - gs (φ n) x| ≤ ε / 4 := le_trans hxn' hLqbound
            linarith
      _ ≤ ε := by linarith
  -- STEP 2: define the pointwise limit `g`
  choose g hg using fun x => cauchySeq_tendsto_of_complete (hcauchy x)
  refine ⟨φ, hφ, g, hg, ?_⟩
  -- STEP 3: the Lipschitz bound passes to the limit
  intro x y
  have htend : Tendsto (fun n => |gs (φ n) x - gs (φ n) y|) atTop
      (𝓝 (|g x - g y|)) := by
    have := ((hg x).sub (hg y)).abs
    simpa using this
  refine le_of_tendsto htend ?_
  filter_upwards with n
  exact hLip (φ n) x y

end ShenWork.Paper1
