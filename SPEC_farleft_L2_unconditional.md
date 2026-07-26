# SPEC — unconditional far-left χ<4 via L² deficit energy (Fable breakthrough, 2026-07-25)

THE headline research target: remove the basin hypothesis from far-left χ<4, giving an
UNCONDITIONAL theorem for front-like data (StrictlyPositiveAtLeft). Existence past χ=1 is
DONE (exists_global_maximalBUCOrbit_with_uniform_band_upto_four_atLeft). Fable's reframing:
the anti-escape is a TURING-stability problem for the q≡1 plateau, invisible to L¹; use an
L² deficit energy and χ<4 falls out of a spectral gap. NO parabolic Harnack needed.

## The mechanism (Fable, verified-consistent with the landed dispersion)
Deficit p=q−1, q(t,z)=u(t,z+ct), ψ=(1−∂zz)⁻¹p. Linear symbol
  Re σ(k) = −k²+(χ−1)−χ/(1+k²),  max over k = χ−2√χ = −γ(χ),  γ(χ)=√χ(2−√χ)>0 ⟺ χ<4.
(Same γ as the landed WholeLineChiPosDispersionSharp — dispersion_le_of_lt_turing.)
Drift enters as ick (Re 0); e^{cz/2} conjugation shifts spectrum down by c²/4 — drift is
STABILIZING (this is why the L¹ leak was a mirage). Two regimes, glued:
- SHALLOW (q≈1): L² deficit energy E=½∫θ p², coercivity
    −∫ p[∂zz + c∂z + (χ−1) − χ(1−∂zz)⁻¹] p ≥ γ(χ)‖p‖²  (Plancherel of the dispersion),
  edge terms O(θ',θ'') near the front anchor, nonlinear remainder absorbed once ‖p‖∞ small.
  ⟹ E'≤−γ(χ)E + edge ⟹ (via WholeLineAbstractEnergyDecay) E→0, i.e. q→1 in far-left L².
- DEEP HOLE (q≤ε on width ≥1): SELF-DEFEATING. V=½e^{−|·|}*q local ⟹ V≤ε+Me^{−K}≤2ε for
  K≳log M ⟹ g=1−χV+(χ−1)q ≥ ½ ⟹ q_t ≥ q_zz+b q_z+½q, KPP refills the hole. χ-ROBUST
  (chemotaxis vanishes with q). Use ReactionPlateauCoercive / LeftFloorProducer / NoSmallLeftPocket.
- GLUE (intermediate amplitude): the compact 1D check bridging deep-hole floor ↔ shallow gap.
  Fable's flagged hard sub-point — grounded ChatGPT/Fable question if it resists.
Then far-left L² convergence + parabolic regularity ⟹ POINTWISE floor ⟹ EventualCoMovingLeftBand
⟹ the ALREADY-LANDED basin-conditional theorem
(uniformCoMovingLeftEquilibriumConvergence_chiPos_upto_four_basinConditional) ⟹ UNCONDITIONAL χ<4.

## Build order (Codex; Fable for the gluing if it resists; verify each with lake)
1. L² spectral coercivity lemma: quadratic form ≥ γ(χ)‖p‖² — Plancherel-integrate the landed
   dispersion (WholeLineChiPosDispersionSharp). REUSE dispersion_le_of_lt_turing.
2. L² deficit energy E=½∫θp² + its E'≤−γ(χ)E+edge identity/inequality (mirror the weighted
   entropy IBP style in WholeLineChiPosWeightedEntropyDissipation; θ = far-left cutoff).
3. Fit into WholeLineAbstractEnergyDecay ⟹ E→0 ⟹ far-left L² convergence.
4. Deep-hole KPP refill floor (reuse ReactionPlateauCoercive + LeftFloorProducer + NoSmallLeftPocket).
5. Gluing lemma (intermediate amplitude).
6. L² convergence + parabolic regularity (the C1 uniform-u_zz, tier-1) ⟹ pointwise floor
   ⟹ EventualCoMovingLeftBand ⟹ feed basinConditional theorem ⟹ unconditional χ<4 capstone.

## Refs to stand on (grep before rebuilding): Salako–Shen, Nadin–Perthame–Ryzhik (plateau/Turing
## stability for parabolic-elliptic KS-logistic). Reuse the landed dispersion + weighted-entropy IBP.
