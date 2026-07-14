#!/usr/bin/env python3
"""Q4912 high-precision projective dominant Birkhoff functional."""
from mpmath import mp

mp.dps = 350


def col(a, b, c):
    out = mp.matrix(3, 1)
    out[0, 0], out[1, 0], out[2, 0] = a, b, c
    return out


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
    raw = M_raw(n)
    dh = delta_H(n)
    dn = [mp.mpf(1), mp.mpf(n+1), mp.mpf(n+1)**2]
    dnp = [mp.mpf(1), mp.mpf(n+2), mp.mpf(n+2)**2]
    out = mp.matrix(3, 3)
    for i in range(3):
        for j in range(3):
            out[i, j] = (raw[i, j] / dh) * dnp[j] / dn[i]
    return out


rt2 = mp.sqrt(2)
lam = 17 + 12*rt2
rho = 1/lam
rinf = col(mp.mpf(2), -rt2, mp.mpf(1))
generic = col(mp.mpf(1), mp.mpf(1), mp.mpf(1))


def scaled_column(v, scale):
    out = mp.matrix(3, 1)
    for i in range(3):
        out[i, 0] = v[i, 0] / scale
    return out


def canonicalize(v):
    chart = max(range(3), key=lambda i: abs(v[i,0]))
    if v[chart,0] == 0:
        raise ZeroDivisionError("zero projective vector")
    return scaled_column(v, v[chart,0]), chart


def projective_V(N, seed):
    v = col(seed[0,0], seed[1,0], seed[2,0])
    for n in range(N-1, -1, -1):
        v = A_bal(n)*v
        scale = max(abs(v[i,0]) for i in range(3))
        if scale == 0:
            raise ZeroDivisionError(f"zero vector after multiplying A_bal({n})")
        v = scaled_column(v, scale)
    return canonicalize(v)


def dot(a,v):
    return sum(mp.mpf(a[i])*v[i,0] for i in range(3))


def align_to_chart(v, chart):
    if v[chart,0] == 0:
        raise ZeroDivisionError("comparison chart vanished")
    return scaled_column(v, v[chart,0])


def s(x,d=250):
    return mp.nstr(x,d)


Ns=[60,90,120,150,180,220,260]
Vr={N: projective_V(N,rinf) for N in Ns}
Vg={N: projective_V(N,generic) for N in Ns}
V,chart=Vr[260]
print("lambda_plus =",s(lam,100))
print("rho =",s(rho,100))
print("chart =",chart)
print("CONVERGENCE")
for N in Ns[:-1]:
    rN=align_to_chart(Vr[N][0],chart)
    gN=align_to_chart(Vg[N][0],chart)
    dr=max(abs(rN[i,0]-V[i,0]) for i in range(3))
    dg=max(abs(gN[i,0]-V[i,0]) for i in range(3))
    print(N,"rinf",mp.nstr(dr,15),"generic",mp.nstr(dg,15))
g260=align_to_chart(Vg[260][0],chart)
print("seed agreement 260",mp.nstr(max(abs(g260[i,0]-V[i,0]) for i in range(3)),15))
print("V_NORMALIZED_CHART_EQ_1")
for i in range(3): print(i,s(V[i,0]))

p=[30921,-32972,8240]
q=[33750,-36000,9000]
pV=dot(p,V); qV=dot(q,V); ratio=pV/qV
print("pV",s(pV))
print("qV",s(qV))
print("ratio",s(ratio))
print("G",s(mp.catalan))
print("ratio_minus_G",s(ratio-mp.catalan,100))
print("pV_minus_GqV",s(pV-mp.catalan*qV,100))


def pslq_vector(vals):
    out=mp.matrix(len(vals),1)
    for i,value in enumerate(vals): out[i,0]=value
    return out


def pslq(label, vals, tol_exp, maxcoeff, maxsteps=30000):
    try:
        rel=mp.pslq(pslq_vector(vals),tol=mp.mpf(10)**(-tol_exp),maxcoeff=maxcoeff,maxsteps=maxsteps)
    except Exception as e:
        rel="ERROR "+repr(e)
    print("PSLQ",label,rel)
    if isinstance(rel,(list,tuple)):
        print("PSLQ_RES",label,s(sum(mp.mpf(rel[i])*vals[i] for i in range(len(vals))),50))

pslq("pV_vs_GqV",[pV,mp.catalan*qV],220,10**4)
pslq("ratio_vs_G",[ratio,mp.catalan],220,10**4)
linear=[mp.mpf(1),mp.catalan,mp.pi,mp.log(2),rt2]
for name,x in [("V0",V[0,0]),("V1",V[1,0]),("V2",V[2,0]),("qV",qV),("pV",pV)]:
    pslq(name+"_linear",[x]+linear,200,10**8,50000)
    pslq(name+"_Qsqrt2",[x,mp.mpf(1),rt2],220,10**20,20000)

quad=[mp.mpf(1),mp.catalan,mp.pi,mp.log(2),rt2,mp.pi**2,mp.catalan**2,
      mp.catalan*mp.pi,mp.catalan*mp.log(2),mp.pi*mp.log(2),mp.log(2)**2]
for name,x in [("V0",V[0,0]),("V1",V[1,0]),("V2",V[2,0]),("qV",qV),("pV",pV)]:
    pslq(name+"_quadratic",[x]+quad,180,10**6,100000)
print("DONE")
