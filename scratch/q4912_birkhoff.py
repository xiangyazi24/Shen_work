#!/usr/bin/env python3
"""High-precision projective dominant Birkhoff functional for P2.5.

This script uses only mpmath.  It computes the initial-point column functional
V_+(0) paired with the printed initial rows.  Because this functional is
projective, the reported normalization is V_3=1.
"""
from mpmath import mp

mp.dps = 350


def M_raw(n):
    n = mp.mpf(n)
    m11 = (-2*n-5)*(n+3)**2*(136*n**4+1424*n**3+5548*n**2+9551*n+6141)
    m12 = 384*n**6+6384*n**5+44168*n**4+162698*n**3+336377*n**2+369933*n+169011
    m13 = -(480*n**4+4980*n**3+19210*n**2+32690*n+20730)
    m21 = (n+2)**2*(n+3)**2*(4*n+10)*(48*n**3+386*n**2+1017*n+879)
    m22 = (n+2)**2*(-272*n**5-3848*n**4-21732*n**3-61184*n**2-85761*n-47808)
    m23 = (n+2)**2*(320*n**3+2540*n**2+6610*n+5640)
    m31 = (-4*n-10)*(n+2)**2*(n+3)**2*(32*n**4+302*n**3+1037*n**2+1530*n+813)
    m32 = (n+2)**2*(192*n**6+2984*n**5+19116*n**4+64452*n**3+120256*n**2+117279*n+46476)
    m33 = (n+2)**2*(-16*n**5-408*n**4-2912*n**3-8884*n**2-12254*n-6240)
    return mp.matrix([[m11,m12,m13],[m21,m22,m23],[m31,m32,m33]])


def delta_H(n):
    n = mp.mpf(n)
    return -2*(n+2)**2*(n+3)**2*(2*n+5)*(2*n+7)**2


def M_H(n):
    return M_raw(n) / delta_H(n)


def A_bal(n):
    """A_n=D_n^{-1} M_H(n) D_{n+1}, D_n=diag(1,n+1,(n+1)^2)."""
    H = M_H(n)
    dn = [mp.mpf(1), mp.mpf(n+1), mp.mpf(n+1)**2]
    dnp = [mp.mpf(1), mp.mpf(n+2), mp.mpf(n+2)**2]
    return mp.matrix(3, 3, lambda i, j: H[i,j] * dnp[j] / dn[i])


rt2 = mp.sqrt(2)
lam = 17 + 12*rt2
rho = 1/lam
rinf = mp.matrix([2, -rt2, 1])  # C rinf = lam rinf


def normalize_max(v):
    s = max(abs(v[i]) for i in range(3))
    return v / s


def projective_V(N, seed="e1"):
    # P_N e_1 = A_0 A_1 ... A_{N-1} e_1, evaluated by reverse nesting.
    if seed == "e1":
        v = mp.matrix([1,0,0])
    elif seed == "rinf":
        v = mp.matrix(rinf)
    else:
        raise ValueError(seed)
    for n in range(N-1, -1, -1):
        v = A_bal(n) * v
        v = normalize_max(v)
    # Projective normalization.  The third component is safely nonzero.
    v = v / v[2]
    return v


def dot(a, v):
    return sum(mp.mpf(a[i])*v[i] for i in range(3))


def fmt(x, digits=240):
    return mp.nstr(x, digits)


print("mp.dps =", mp.dps)
print("lambda_plus =", fmt(lam, 100))
print("rho =", fmt(rho, 100))
print()

Ns = [60, 90, 120, 150, 180, 220, 260]
Vs_e1 = {}
Vs_r = {}
for N in Ns:
    Vs_e1[N] = projective_V(N, "e1")
    Vs_r[N] = projective_V(N, "rinf")

V = Vs_r[Ns[-1]]
print("CONVERGENCE CHECKS (max projective component difference)")
for N in Ns[:-1]:
    de = max(abs(Vs_e1[N][i]-V[i]) for i in range(3))
    dr = max(abs(Vs_r[N][i]-V[i]) for i in range(3))
    print("N=", N, " seed=e1 diff=", mp.nstr(de, 12), " seed=rinf diff=", mp.nstr(dr, 12))
print("terminal seed agreement at N=", Ns[-1], ":",
      mp.nstr(max(abs(Vs_e1[Ns[-1]][i]-V[i]) for i in range(3)), 12))
print()

print("PROJECTIVE V_PLUS(0), normalization V[2]=1")
for i in range(3):
    print(f"V[{i}] = {fmt(V[i], 250)}")
print()

p = [30921, -32972, 8240]
q = [33750, -36000, 9000]
pV = dot(p, V)
qV = dot(q, V)
ratio = pV/qV
res = pV - mp.catalan*qV
print("PAIRINGS, same V[2]=1 normalization")
print("p dot V =", fmt(pV, 250))
print("q dot V =", fmt(qV, 250))
print("(p dot V)/(q dot V) =", fmt(ratio, 250))
print("Catalan G =", fmt(mp.catalan, 250))
print("ratio-G =", fmt(ratio-mp.catalan, 80))
print("pV-G*qV =", fmt(res, 80))
print()

# A direct finite-N ratio check, independent of the choice V[2]=1.
print("DIRECT FINITE-N RATIOS")
for N in [40, 80, 120, 160, 200, 240]:
    VN = projective_V(N, "e1")
    rr = dot(p, VN)/dot(q, VN)
    print(N, mp.nstr(rr-mp.catalan, 12))
print()


def do_pslq(label, values, tol_exp=220, maxcoeff=10**8, maxsteps=10000):
    try:
        rel = mp.pslq(mp.matrix(values), tol=mp.mpf(10)**(-tol_exp),
                      maxcoeff=maxcoeff, maxsteps=maxsteps)
    except Exception as exc:
        rel = "ERROR: %s" % (exc,)
    print(label, "=>", rel)
    if isinstance(rel, (list, tuple)):
        rr = sum(mp.mpf(rel[i])*values[i] for i in range(len(values)))
        print("  residual =", mp.nstr(rr, 30))
    return rel

print("PSLQ TESTS")
do_pslq("[pV, G*qV]", [pV, mp.catalan*qV], tol_exp=220, maxcoeff=10**4)
do_pslq("[ratio, G]", [ratio, mp.catalan], tol_exp=220, maxcoeff=10**4)

linear_basis = [mp.mpf(1), mp.catalan, mp.pi, mp.log(2), rt2]
quadratic_basis = [
    mp.mpf(1), mp.catalan, mp.pi, mp.log(2), rt2,
    mp.pi**2, mp.catalan**2, mp.catalan*mp.pi,
    mp.catalan*mp.log(2), mp.pi*mp.log(2), mp.log(2)**2
]
for name, x in [("V0", V[0]), ("V1", V[1]), ("qV", qV), ("pV", pV)]:
    do_pslq(name+" linear basis", [x]+linear_basis,
            tol_exp=200, maxcoeff=10**8, maxsteps=50000)
    do_pslq(name+" quadratic basis", [x]+quadratic_basis,
            tol_exp=180, maxcoeff=10**6, maxsteps=100000)

# Low-degree algebraic checks over Q(sqrt(2)).
for name, x in [("V0", V[0]), ("V1", V[1]), ("qV", qV), ("pV", pV)]:
    do_pslq(name+" in span{1,sqrt2}", [x, mp.mpf(1), rt2],
            tol_exp=220, maxcoeff=10**20, maxsteps=10000)

print("DONE")
