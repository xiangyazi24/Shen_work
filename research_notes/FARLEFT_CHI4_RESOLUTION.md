# Far-left stability of the chemotaxis front: the sharp threshold χ<4 and its resolution

**Status:** beyond-paper research, fully resolved. All theorems below are formalized in Lean 4
(Mathlib 4.29.1) on `main`, clean-3 (`[propext, Classical.choice, Quot.sound]`), 0 sorry/axiom.

## Setting

Shen's traveling-wave paper proves stability of the invading front for the co-moving
chemotaxis–logistic system only for the chemotactic sensitivity `χ` near a threshold `χ*≈1`.
Normalized case `m=γ=α=1`, co-moving frame `z=x−ct`:
```
u_t = u_zz + (c − χ v_z) u_z + u(1 − χv + (χ−1)u),   −v_zz + v = u.
```
Behind the front (`z→−∞`) the solution approaches the plateau `u≡1`. The question this note
resolves: **how far can far-left stability of the plateau be pushed in χ, and what is the sharp
threshold?**

## 1. The sharp LINEAR threshold is χ = 4, not χ* ≈ 1

Linearizing about the plateau `(u,v)=(1,1)` and testing with a Fourier mode gives the growth
rate (dispersion relation), `s=k²`:
```
Re λ(s) = −s + (χ−1) − χ/(1+s)   [general: dispersion α χγ s = −α − s + χγ·s/(1+s)]
max_{s≥0} Re λ = χ − 2√χ = −(2√χ − χ) < 0  ⟺  χ < 4    (general: χγ < (1+√α)²)
```
So the plateau is linearly (essential-spectrum) stable exactly for `χ < 4` — the sharp Turing
threshold — with the critical mode `k*=1` at `χ=4`. No unstable band exists below 4.
**Lean:** `ShenWork/Paper1/WholeLineChiPosDispersionSharp.lean` —
`dispersion_le_of_lt_turing` (stable below), `dispersion_pos_of_gt_turing` (unstable above),
`dispersion_attains_at_sqrt` (sharpness). The threshold `(1+√α)²` appears identically in the
sharp entropy coefficient `1 − χ²/16 > 0 ⟺ χ < 4`.

## 2. A whole-line-localized sharp entropy engine

New tool (whole-line analog of the periodic sharp entropy), with a strictly-positive
slowly-varying weight `w` and all boundary/flux terms explicit — the moving-window relative
entropy `E = ∫ w·(u−1−log u)` dissipates at the sharp rate:
```
∫ w·M(u)·u_t ≤ −(1 − χ²/16)·∫ w·(u−1)²  +  (C/ℓ)(E + ∫w(A²+W²))  +  explicit boundary
```
with `C=|c|+χ+2`, `A=u_z/u`, `W=u−1`. The sharp constant `1/4` in the resolver step survives
the weighting via a **real-space IBP** (no Fourier / no Mathlib multiplier wall).
**Lean:** `WholeLineChiPosWeightedEntropyDissipation.lean` (`weighted_sharp_entropy_production_le`,
`weighted_resolver_le`), instantiated for the real orbit in `...WeightedEntropyOrbit.lean`
(`wholeLineCauchyGlobalU_weighted_sharp_dissipation`) with the literal `dE/dt` in
`...WeightedEntropyOrbitDeriv.lean`.

## 3. Basin-conditional convergence for the full sharp range χ < 4

For a global front-like orbit that stays in the plateau basin (a uniform far-left lower band
`EventualCoMovingLeftBand`), the sharp entropy + first-order compactness give convergence to
`u≡1` on the moving far-left, for **every** `0 ≤ χ < 4`.
**Lean:** `WholeLineChiPosEntropyFarLeftBasinConditional.lean` —
`uniformCoMovingLeftEquilibriumConvergence_chiPos_upto_four_basinConditional`
(+ the canonical-orbit form). The basin floor discharges all zeroth-order compactness
(equiboundedness, equicontinuity via MVT); the residual is floor-free, first-order.

## 4. UNCONDITIONAL far-left χ<4 is FALSE — convective escape

The basin/closeness hypothesis is **necessary, not a technical limitation**. Reason (formalized
counterexample): take any traveling wave `(U,W)` of the system with lab speed `s`, and view it
in a FASTER co-moving frame `z = x − ct` with `c > s`:
```
q(t,z) = U(z + (c−s)t)   solves the co-moving equation exactly, and
lim_{z→−∞} q(t,z) = 1  for every t   (per-slice StrictlyPositiveAtLeft),   BUT
q(t,R) = U(R + (c−s)t) → 0  as t→∞   for every fixed R   (no uniform floor).
```
The front **retreats** in the too-fast frame — a *convective escape / speed mismatch*, not a
bistability failure, and it occurs already at `χ=0`. So no uniform far-left floor exists for
broad front-like data + arbitrary frame speed; the `WeightedL2InitialCloseness` hypothesis is
exactly what pins `c` to the wave speed.
**Lean:** `WholeLineChiPosFloorQuantifierObstruction.lean`
(`convectiveEscapeProfile_no_uniform_left_floor`, per-slice positivity + fixed-z decay),
wired to a genuine PDE wave in `WholeLineConvectiveEscapePDE.lean`.

## 5. Why the "obvious" routes to unconditional χ<4 fail (recorded, so they are not re-tried)

- **L¹ local-mass balance:** the drift/chemotaxis cutoff leak is L-INDEPENDENT (the `1/L` in
  `φ'` cancels the `O(L)` annular mass) — a wide window does not stop mass draining.
- **Bare L² deficit energy:** coercive in the shallow regime (spectral gap `2√χ−χ`, matching §1),
  but at intermediate amplitude the nonlinear quadratic energy can INCREASE for `χ>2`.
  Machinery built anyway: `WholeLineChiPosL2SpectralCoercivity/…L2DeficitEnergy/…L2FarLeftDecay`.
- **Deep-hole KPP refill:** deep holes self-heal (V is local ⇒ V≤2ε ⇒ reaction ≥ ½q, χ-robust),
  built in `WholeLineChiPosDeepHoleRefill.lean` — but it only sees symmetric interior minima,
  not monotone boundary escape.
- **Front-anchor / convergence-to-the-wave:** circular — `UniformMovingFrameConvergence` is
  proved only in the basin sub-range; the χ<4 maximal orbit has no proved wave-closeness.
- **Parabolic Harnack:** would convert a uniform local-mass seed into a floor, but the seed is
  the substantive open estimate, and Harnack is absent from Mathlib.

## Bottom line

The far-left threshold is **sharp at χ=4** (linear + entropy), the **basin-conditional χ<4
convergence theorem is the optimal statement**, and **unconditional χ<4 is provably false**
(convective escape). This closes the far-left question: theorem where it holds, formalized
counterexample where it fails.
