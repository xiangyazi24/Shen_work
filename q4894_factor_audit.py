#!/usr/bin/env python3
import sympy as sp
from sympy.solvers.recurr import rsolve_hyper
n=sp.symbols('n', integer=True)
def sh(e,k=1): return sp.expand(e.subs(n,n+k))
def shmat(A,k=1): return A.applyfunc(lambda e: sh(e,k))
m11=(-2*n-5)*(n+3)**2*(136*n**4+1424*n**3+5548*n**2+9551*n+6141)
m12=384*n**6+6384*n**5+44168*n**4+162698*n**3+336377*n**2+369933*n+169011
m13=-480*n**4-4980*n**3-19210*n**2-32690*n-20730
m21=(n+2)**2*(n+3)**2*(4*n+10)*(48*n**3+386*n**2+1017*n+879)
m22=(n+2)**2*(-272*n**5-3848*n**4-21732*n**3-61184*n**2-85761*n-47808)
m23=(n+2)**2*(320*n**3+2540*n**2+6610*n+5640)
m31=(-4*n-10)*(n+2)**2*(n+3)**2*(32*n**4+302*n**3+1037*n**2+1530*n+813)
m32=(n+2)**2*(192*n**6+2984*n**5+19116*n**4+64452*n**3+120256*n**2+117279*n+46476)
m33=(n+2)**2*(-16*n**5-408*n**4-2912*n**3-8884*n**2-12254*n-6240)
M=sp.Matrix([[m11,m12,m13],[m21,m22,m23],[m31,m32,m33]])
print('BEGIN_Q4894',flush=True)
print('detM',sp.factor(M.det()),flush=True)
e=sp.Matrix([1,0,0]); v=[e,M*e,M*shmat(M,1)*e,M*shmat(M,1)*shmat(M,2)*e]
c=[]
for j in range(4):
    c.append(sp.expand((-1)**j*sp.Matrix.hstack(*[v[k] for k in range(4) if k!=j]).det()))
g=sp.gcd_list(c); c=[sp.cancel(x/g) for x in c]
cont=sp.gcd_list([sp.Poly(x,n,domain=sp.QQ).content() for x in c]); c=[sp.cancel(x/cont) for x in c]
if sp.LC(sp.Poly(c[3],n))>0: c=[-x for x in c]
print('rawdegrees',[sp.degree(x,n) for x in c],flush=True)
delta=-2*(n+2)**2*(n+3)**2*(2*n+5)*(2*n+7)**2
ell=[]; pr=sp.Integer(1)
for j in range(4):
    if j: pr=sp.expand(pr*sh(delta,j-1))
    ell.append(sp.expand(c[j]*pr))
g=sp.gcd_list(ell); ell=[sp.cancel(x/g) for x in ell]
cont=sp.gcd_list([sp.Poly(x,n,domain=sp.QQ).content() for x in ell]); ell=[sp.cancel(x/cont) for x in ell]
if sp.LC(sp.Poly(ell[3],n))<0: ell=[-x for x in ell]
print('degrees',[sp.degree(x,n) for x in ell],flush=True)
for j,x in enumerate(ell):
    print('ell%d'%j,sp.expand(x),flush=True)
    print('ell%d_factor'%j,sp.factor(x),flush=True)
xi=sp.symbols('xi'); lead=[sp.LC(sp.Poly(x,n)) for x in ell]
print('poincare',sp.factor(sum(lead[j]*xi**j for j in range(4))),flush=True)
def sr(r,k): return sp.cancel(r.subs(n,n+k))
def ric(coeff,r):
    a=0; q=1
    for j in range(4): a+=coeff[j]*q; q=sp.cancel(q*sr(r,j))
    return sp.cancel(a)
for name,r in {'one':1,'nminus3':(n+1)**3/(n+2)**3,'det':(n+2)**3*(2*n+3)**2/((n+1)**2*(n+3)*(2*n+7)**2)}.items():
    num=sp.factor(sp.together(ric(ell,sp.sympify(r))).as_numer_denom()[0]); print('candidate',name,'zero',num==0,flush=True); print('res',num,flush=True)
adj=[sp.expand(sh(ell[3-k],k)) for k in range(4)]
for label,coef in [('RIGHT',ell),('LEFT_VIA_ADJOINT',adj)]:
    print('HYPER_BEGIN',label,flush=True)
    try:
        sol=rsolve_hyper(coef,sp.Integer(0),n)
        print('HYPER_RESULT',label,repr(sol),flush=True)
        if sol not in (None,0,sp.Integer(0)):
            rr=sp.factor(sp.cancel(sol.subs(n,n+1)/sol)); print('RATIO',rr,flush=True); print('CHECK',sp.factor(sp.together(ric(coef,rr)).as_numer_denom()[0]),flush=True)
    except BaseException as ex: print('HYPER_ERROR',label,type(ex).__name__,str(ex),flush=True)
print('END_Q4894',flush=True)
