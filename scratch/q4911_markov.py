#!/usr/bin/env python3
from fractions import Fraction as F
from math import sqrt
import sympy as sp

NS = 30
NM = 30
x = sp.Symbol('x')


def rat(q):
    return sp.Rational(q.numerator, q.denominator) if isinstance(q, F) else sp.Rational(q)


def m_sigma(k): return sp.Rational(1, (2*k+1)**2)
def m_base(k): return sp.Rational(1, 2*k+1)


def solve_exact(A, b):
    # SymPy's fraction-free DomainMatrix solver is much faster than generic inversion.
    from sympy.polys.matrices import DomainMatrix
    dA = DomainMatrix.from_Matrix(sp.Matrix(A))
    db = DomainMatrix.from_Matrix(sp.Matrix(b))
    num, den = dA.solve_den(db, method='rref')
    return [sp.cancel(v/den) for v in num.to_Matrix()]


def monic_op(n, moment):
    if n == 0: return sp.Poly(1, x, domain=sp.QQ)
    A = [[moment(i+j) for j in range(n)] for i in range(n)]
    b = [[-moment(n+i)] for i in range(n)]
    c = solve_exact(A,b)
    return sp.Poly(x**n + sum(c[j]*x**j for j in range(n)), x, domain=sp.QQ)


def inner(p,q,moment):
    pc=list(reversed(p.all_coeffs())); qc=list(reversed(q.all_coeffs()))
    return sp.cancel(sum(a*b*moment(i+j) for i,a in enumerate(pc) for j,b in enumerate(qc)))

Q=[monic_op(n,m_sigma) for n in range(NS+1)]
qm=[sp.cancel(q.eval(-1)) for q in Q]

norm=[inner(q,q,m_sigma) for q in Q]
a=[]; bb=[None]
for n in range(NS):
    a.append(sp.cancel(inner(sp.Poly(x*Q[n].as_expr(),x),Q[n],m_sigma)/norm[n]))
    if n: bb.append(sp.cancel(norm[n]/norm[n-1]))


def M(n):
    return sp.Matrix([
      [(-2*n-5)*(n+3)**2*(136*n**4+1424*n**3+5548*n**2+9551*n+6141), 384*n**6+6384*n**5+44168*n**4+162698*n**3+336377*n**2+369933*n+169011, -480*n**4-4980*n**3-19210*n**2-32690*n-20730],
      [(n+2)**2*(n+3)**2*(4*n+10)*(48*n**3+386*n**2+1017*n+879), (n+2)**2*(-272*n**5-3848*n**4-21732*n**3-61184*n**2-85761*n-47808), (n+2)**2*(320*n**3+2540*n**2+6610*n+5640)],
      [(-4*n-10)*(n+2)**2*(n+3)**2*(32*n**4+302*n**3+1037*n**2+1530*n+813), (n+2)**2*(192*n**6+2984*n**5+19116*n**4+64452*n**3+120256*n**2+117279*n+46476), (n+2)**2*(-16*n**5-408*n**4-2912*n**3-8884*n**2-12254*n-6240)]])

def delta(n): return -2*(n+2)**2*(n+3)**2*(2*n+5)*(2*n+7)**2
qrow=sp.Matrix([[33750,-36000,9000]])
qh=[]
for n in range(NS+1):
    qh.append(sp.cancel(qrow[0,0]))
    if n<NS: qrow=sp.cancel(qrow*M(n)/delta(n))


def mop(n0,n1):
    n=n0+n1
    if n==0: return sp.Poly(1,x,domain=sp.QQ)
    A=[]; b=[]
    for j in range(n0): A.append([m_base(j+k) for k in range(n)]); b.append([-m_base(j+n)])
    for j in range(n1): A.append([m_sigma(j+k) for k in range(n)]); b.append([-m_sigma(j+n)])
    c=solve_exact(A,b)
    return sp.Poly(x**n+sum(c[k]*x**k for k in range(n)),x,domain=sp.QQ)

T=[]
for d in range(NM+1):
    idx=(d//2,d//2) if d%2==0 else ((d+1)//2,(d-1)//2)
    T.append(mop(*idx))
tm=[sp.cancel(p.eval(-1)) for p in T]

# Exact four-term support check by monic elimination.
rec=[]
for d in range(NM):
    rem=sp.Poly(x*T[d].as_expr()-T[d+1].as_expr(),x,domain=sp.QQ)
    co={}
    for j in range(d,-1,-1):
        cj=rem.nth(j)
        if cj:
            co[j]=cj
            rem=sp.Poly(rem.as_expr()-cj*T[j].as_expr(),x,domain=sp.QQ)
    assert rem.is_zero
    assert all(j>=d-2 for j in co)
    rec.append(co)

rho=sp.Integer(17)-12*sp.sqrt(2)
lam=sp.Integer(17)+12*sp.sqrt(2)
print('Q4911 PORTABLE EXACT RESULT')
print('rho',sp.N(rho,40),'lambda+',sp.N(lam,40))
print('FIRST OPS')
for n in range(8): print(n,Q[n].as_expr())
print('EVALUATIONS n Q(-1) Q(rho)')
for n in range(NS+1): print(n,qm[n],sp.N(Q[n].eval(rho),45))
print('LAST ORDINARY RATIOS')
limit=-(sp.Integer(3)+2*sp.sqrt(2))/4
for n in range(20,30): print(n,sp.N(qm[n+1]/qm[n],40),sp.N(qm[n+1]/qm[n]-limit,25))
print('LAST REC COEFF')
for n in range(22,30): print(n,a[n],bb[n],sp.N(a[n],22),sp.N(bb[n],22))
print('CMF COMPARISON')
for n in range(NS+1):
    step='' if n==NS else str(sp.N(qh[n+1]/qh[n],30))
    print(n,qh[n],step,sp.cancel(qh[n]/qm[n]))
print('TWO WEIGHT FOUR TERM COEFF')
for d in list(range(2,9))+list(range(24,30)):
    co=rec[d]; print(d,co.get(d,0),co.get(d-1,0),co.get(d-2,0))
print('MACRO COMPARISON')
for n in range(NM//2+1):
    mr='' if n==NM//2 else str(sp.N(16*tm[2*n+2]/tm[2*n],35))
    gauge=sp.cancel(qh[n]/(sp.Integer(16)**n*tm[2*n]))
    print(n,tm[2*n],mr,gauge,sp.N(gauge,30))
print('DONE')
