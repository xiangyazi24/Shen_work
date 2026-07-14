#!/usr/bin/env python3
"""Q4912 high-precision projective dominant Birkhoff functional."""
from mpmath import mp

mp.dps = 350


def M_raw(n):
    n = mp.mpf(n)
    return mp.matrix([
        [(-2*n-5)*(n+3)**2*(136*n**4+1424*n**3+5548*n**2+9551*n+6141),
         384*n**6+6384*n**5+44168*n**4+162698*n**3+336377*n**2+369933*n+169011,
         -(480*n**4+4980*n**3+19210*n**2+32690*n+20730)],
        [(n+2)**2*(n+3)**2*(4*n+10)*(48*n**3+386*n**2+1017*n+879),
         (n+2)**2*(-272*n**5-3848*n**4-21732*n**3-61184*n**2-85761*n-47808),
         (n+2)**2*(320*n**3+2540*n**2+6610*n+5640)],
        [(-4*n-10)*(n+2)**2*(n+3)**2*(32*n**4+302*n**3+1037*n**2+1530*n+813),
         (n+2)**2*(192*n**6+2984*n**5+19116*n**4+64452*n**3+120256*n**2+117279*n+46476),
         (n+2)**2*(-16*n**5-408*n**4-2912*n**3-8884*n**2-12254*n-6240)]
    ])


def delta_H(n):
    n = mp.mpf(n)
    return -2*(n+2)**2*(n+3)**2*(2*n+5)*(2*n+7)**2


def A_bal(n):
    H = M_raw(n) / delta_H(n)
    dn = [mp.mpf(1), mp.mpf(n+1), mp.mpf(n+1)**2]
    dnp = [mp.mpf(1), mp.mpf(n+2), mp.mpf(n+2)**2]
    return mp.matrix(3, 3, lambda i, j: H[i,j]*dnp[j]/dn[i])


rt2 = mp.sqrt(2)
lam = 17 + 12*rt2
rho = 1/lam
rinf = mp.matrix([2, -rt2, 1])


def projective_V(N, seed):
    v = mp.matrix([1,0,0]) if seed == "e1" else mp.matrix(rinf)
    for n in range(N-1, -1, -1):
        v = A_bal(n)*v
        scale = max(abs(v[i]) for i in range(3))
        v = v / scale
    return v / v[2]


def dot(a,v):
    return sum(mp.mpf(a[i])*v[i] for i in range(3))


def s(x,d=250):
    return mp.nstr(x,d)


Ns=[60,90,120,150,180,220,260]
Ve={N: projective_V(N,"e1") for N in Ns}
Vr={N: projective_V(N,"rinf") for N in Ns}
V=Vr[260]
print("lambda_plus =",s(lam,100))
print("rho =",s(rho,100))
print("CONVERGENCE")
for N in Ns[:-1]:
    de=max(abs(Ve[N][i]-V[i]) for i in range(3))
    dr=max(abs(Vr[N][i]-V[i]) for i in range(3))
    print(N, "e1",mp.nstr(de,15),"rinf",mp.nstr(dr,15))
print("seed agreement 260",mp.nstr(max(abs(Ve[260][i]-V[i]) for i in range(3)),15))
print("V_NORMALIZED_V2_EQ_1")
for i in range(3): print(i,s(V[i]))

p=[30921,-32972,8240]
q=[33750,-36000,9000]
pV=dot(p,V); qV=dot(q,V); ratio=pV/qV
print("pV",s(pV))
print("qV",s(qV))
print("ratio",s(ratio))
print("G",s(mp.catalan))
print("ratio_minus_G",s(ratio-mp.catalan,100))
print("pV_minus_GqV",s(pV-mp.catalan*qV,100))


def pslq(label, vals, tol_exp, maxcoeff, maxsteps=30000):
    try:
        rel=mp.pslq(mp.matrix(vals),tol=mp.mpf(10)**(-tol_exp),maxcoeff=maxcoeff,maxsteps=maxsteps)
    except Exception as e:
        rel="ERROR "+repr(e)
    print("PSLQ",label,rel)
    if isinstance(rel,(list,tuple)):
        print("PSLQ_RES",label,s(sum(mp.mpf(rel[i])*vals[i] for i in range(len(vals))),50))

pslq("pV_vs_GqV",[pV,mp.catalan*qV],220,10**4)
pslq("ratio_vs_G",[ratio,mp.catalan],220,10**4)
linear=[mp.mpf(1),mp.catalan,mp.pi,mp.log(2),rt2]
for name,x in [("V0",V[0]),("V1",V[1]),("qV",qV),("pV",pV)]:
    pslq(name+"_linear",[x]+linear,200,10**8,50000)
    pslq(name+"_Qsqrt2",[x,mp.mpf(1),rt2],220,10**20,20000)

quad=[mp.mpf(1),mp.catalan,mp.pi,mp.log(2),rt2,mp.pi**2,mp.catalan**2,
      mp.catalan*mp.pi,mp.catalan*mp.log(2),mp.pi*mp.log(2),mp.log(2)**2]
for name,x in [("V0",V[0]),("V1",V[1]),("qV",qV),("pV",pV)]:
    pslq(name+"_quadratic",[x]+quad,180,10**6,100000)
print("DONE")
