# Q2203 audit: CETerminal boundedness core

I audited the requested Lean regions on `main` at commit `dd1f0a6d`.

## 1. Recoverability

Yes, all five conjuncts of `IntervalDomainBoundednessHyp p` are recoverable from the proposed two-field core plus existing wrapper/parameter facts, provided the conversion has access to `hb : 0 < p.b`.

The reconstruction is direct:

- `IntervalDomainSharpL2AbsorptionThreshold p` follows by the right branch of its definition, using `Or.inr alphaAbsorption`.
- `0 < p.b` is exactly the theorem-wrapper hypothesis `hb`.
- `2 * p.γ < p.α` is `alphaAbsorption`.
- `0 < p.γ` is already `p.hγ` from `CM2Params`.
- `p.γ * (p.N : ℝ) < 2` is `gammaDimension`.

If the current no-argument conversion shape `to_CERawGradResiduals h` is kept, the missing fact at that local point is `hb : 0 < p.b`. So `hb` must be threaded into that conversion, or reconstruction must be delayed until a wrapper that already has `hb`.

## 2. Helper to add

Add this beside `IntervalDomainBoundednessHyp` in `ShenWork/PDE/IntervalDomainAPrioriGlobal.lean`.

```lean
import ShenWork.PDE.IntervalDomainAPrioriGlobal

namespace ShenWork.IntervalDomainExistence

structure IntervalDomainBoundednessParameterCore (p : CM2Params) : Prop where
  alphaAbsorption : 2 * p.γ < p.α
  gammaDimension : p.γ * (p.N : ℝ) < 2

theorem IntervalDomainBoundednessParameterCore.to_boundednessHyp
    {p : CM2Params}
    (h : IntervalDomainBoundednessParameterCore p)
    (hb : 0 < p.b) :
    IntervalDomainBoundednessHyp p :=
  ⟨Or.inr h.alphaAbsorption, hb, h.alphaAbsorption, p.hγ, h.gammaDimension⟩

end ShenWork.IntervalDomainExistence
```

Then replace the terminal residual field with a core field such as `boundednessCore : IntervalDomainBoundednessParameterCore p`. The conversion to the older residual interface should rebuild the full bundle with `h.boundednessCore.to_boundednessHyp hb`, so `to_CERawGradResiduals` and the sectorial terminal-facts conversion above it need an `hb` argument unless reconstruction is delayed to the final statement wrapper.

## 3. Residual-assumption status

This removes a real interface over-assumption, but it mostly repackages the mathematics. It removes duplicate residual proof fields for the sharp threshold, strict `b` positivity, and strict `γ` positivity. It does not remove the two genuine parameter assumptions that still have to be supplied:

- `alphaAbsorption : 2 * p.γ < p.α`;
- `gammaDimension : p.γ * (p.N : ℝ) < 2`.

## 4. Paper-facing caveat

`alphaAbsorption` is not already part of the advertised actual-linear-small wrapper signature in the inspected regions. Those wrappers expose `ha`, `hb`, `hχ0`, `hm`, `hβ`, and the small-sensitivity condition `hχ`, while `CM2Params` only gives positivity of `α` and `γ`, not a relation `2 * p.γ < p.α`.

Therefore `alphaAbsorption` must remain visible as an extra boundedness-side or Moser-route condition, either in the terminal residual/frontier data or as an explicit theorem hypothesis if this route is made more paper-facing. The same caveat applies to `gammaDimension`.
