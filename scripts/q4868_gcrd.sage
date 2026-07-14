from sage.all import *
from ore_algebra import OreAlgebra

# Q4868: greatest common RIGHT divisor of the corrected CMF Euler
# operator and the symmetric-square Delannoy differential operator.

Rn.<n> = PolynomialRing(QQ)

c_coeffs = [
    [-170972650800, -826494925500, -1792449886332, -2317972607944,
     -2000297648936, -1219354055500, -541255279788, -177419351856,
     -43002662976, -7620091136, -960400960, -81589760, -4190208,
     -98304],
    [8781630505200, 38850314624124, 78557994908508, 96136040496551,
     79442239242197, 46814452218572, 20241514501104, 6502490145168,
     1552168938336, 271943188864, 33995217088, 2871763456,
     146952192, 3440640],
    [-21132458248680, -87529225645944, -165451256319618,
     -189073879129764, -145809619841418, -80164318460172,
     -32338316008004, -9694892892592, -2160716677664,
     -353683596544, -41340724928, -3268370944, -156684288,
     -3440640],
    [587448626688, 2442715444224, 4635428285664, 5317694979920,
     4116150568664, 2270943978716, 919036676572, 276298241680,
     61721801728, 10120470656, 1184128064, 93632000, 4485120,
     98304],
]

c0, c1, c2, c3 = [Rn(v) for v in c_coeffs]

# Corrected normalized Poincare polynomial.
Rx.<xi> = PolynomialRing(QQ)
chi = (c3.leading_coefficient()*xi^3
       + c2.leading_coefficient()*xi^2
       + c1.leading_coefficient()*xi
       + c0.leading_coefficient()) / c3.leading_coefficient()
print("POINCARE =", chi.factor())
assert chi == xi^3 - 35*xi^2 + 35*xi - 1

Rz.<z> = PolynomialRing(QQ)
A.<Dz> = OreAlgebra(Rz)
theta = z*Dz


def peval(p, T):
    """Evaluate a commutative QQ[n] polynomial at an Ore operator T."""
    return sum(QQ(p[k]) * T^k for k in range(p.degree() + 1))


Lrec = (z^3 * peval(c0, theta)
        + z^2 * peval(c1, theta - 1)
        + z * peval(c2, theta - 2)
        + peval(c3, theta - 3))

LD = ((2*theta - 3)*theta^2
      - z*(2*theta + 1)*(35*theta^2 - 9)
      + z^2*(2*theta + 1)*(35*theta^2 + 70*theta + 26)
      - z^3*(2*theta + 5)*(theta + 1)^2)

print("ORDER_LREC =", Lrec.order())
print("ORDER_LD =", LD.order())
print("HEAD_LREC =", factor(Lrec.leading_coefficient()))
print("HEAD_LD =", factor(LD.leading_coefficient()))

assert Lrec.order() == 13
assert LD.order() == 3
assert Lrec.leading_coefficient() == \
       98304*z^13*(1-z)*(1-34*z+z^2)
assert LD.leading_coefficient() == \
       2*z^3*(1-z)*(1-34*z+z^2)

# Exact quick certificate that the Brafman solution D_n^2 is not
# annihilated by Lrec: this is the n=0 recurrence residual.
Dsq = [ZZ(1), ZZ(9), ZZ(169), ZZ(3969)]
res0 = c0(0)*Dsq[0] + c1(0)*Dsq[1] + c2(0)*Dsq[2] + c3(0)*Dsq[3]
print("DELANN0_RESIDUAL =", res0)
assert res0 == -1160938142806248

# gcrd means greatest common RIGHT divisor. ore_algebra implicitly
# localizes QQ[z] to QQ(z) for this operation.
G = Lrec.gcrd(LD).normalize()
print("GCRD_ORDER =", G.order())
print("GCRD =", G)

assert G.order() == 0
print("RESULT = RIGHT_GCD_IS_A_UNIT")
