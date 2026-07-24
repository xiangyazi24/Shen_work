#!/usr/bin/env python3
from __future__ import annotations
from math import comb, gcd, log
from functools import reduce
from sympy import Matrix, ilcm, Poly, symbols, nroots

TARGETS = [24, 36, 48, 60, 84, 120]


def apery(N):
    A=[0]*(N+1); A[0]=1
    if N>=1: A[1]=5
    for n in range(1,N):
        num=(34*n**3+51*n**2+27*n+5)*A[n]-n**3*A[n-1]
        den=(n+1)**3
        assert num%den==0
        A[n+1]=num//den
    return A


def diff_table(A, N):
    tab=[A[:N+1]]
    for r in range(1,N+1):
        prev=tab[-1]
        tab.append([prev[i+1]-prev[i] for i in range(len(prev)-1)])
    return tab


def primitive_kernel(M):
    ns=M.nullspace(); assert len(ns)==1, (M.shape,len(ns))
    v=ns[0]; den=1
    for z in v: den=ilcm(den,int(z.q))
    w=[int(z*den) for z in v]
    g=reduce(gcd,(abs(x) for x in w if x),0)
    w=[x//g for x in w]
    for x in w:
        if x:
            if x<0: w=[-y for y in w]
            break
    return w


def logint(x):
    x=abs(int(x))
    if not x: return float('-inf')
    s=str(x); take=min(16,len(s))
    return (len(s)-take)*log(10.0)+log(int(s[:take]))


def audit(n,A,D,a):
    H=(n-1)//3; b=H-a
    rows=[]
    for k in range(a+1,H+1):
        rows.append([comb(k,l)*D[k-l][l] if l<=k else 0 for l in range(b+1)])
    M=Matrix(rows)
    q=primitive_kernel(M) if b else [1]
    # p coefficients are Newton coefficients of A_j Q(j), j=0..H, only 0..a survive.
    vals=[]
    for j in range(H+1):
        Qj=sum(q[l]*comb(j,l) for l in range(b+1))
        vals.append(A[j]*Qj)
    cur=vals[:]; pc=[]
    for k in range(H+1):
        pc.append(cur[0])
        cur=[cur[i+1]-cur[i] for i in range(len(cur)-1)]
    assert all(x==0 for x in pc[a+1:])
    pc=pc[:a+1]
    allc=pc+q
    gg=reduce(gcd,(abs(x) for x in allc if x),0)
    # q was primitive, so full vector should already be primitive, but verify.
    assert gg==1
    Pn=sum(pc[i]*comb(n,i) for i in range(a+1))
    Qn=sum(q[l]*comb(n,l) for l in range(b+1))
    # sign patterns
    qs=''.join('+' if x>0 else '-' if x<0 else '0' for x in q)
    qvals=[sum(q[l]*comb(j,l) for l in range(b+1)) for j in range(H+1)]
    qvs=''.join('+' if x>0 else '-' if x<0 else '0' for x in qvals)
    # maximal minors sign test, only if modest
    minor_signs=set()
    minors=[]
    if b and b<=12:
        for omit in range(b+1):
            mm=int(M[:,[j for j in range(b+1) if j!=omit]].det())
            minors.append(mm)
            if mm: minor_signs.add(1 if ((-1)**omit)*mm>0 else -1)
    # roots in ordinary-power representation of Q(x)
    x=symbols('x')
    qexpr=sum(q[l]*Poly(1,x).as_expr()*prod(x-r for r in range(l))/__import__('math').factorial(l) for l in range(b+1))
    roots=[]
    if 1<=b<=12:
        try:
            roots=[complex(r) for r in nroots(qexpr,maxsteps=200)]
        except Exception:
            roots=[]
    realroots=sum(1 for z in roots if abs(z.imag)<1e-8)
    intervalroots=sum(1 for z in roots if abs(z.imag)<1e-8 and -1e-8<=z.real<=H+1e-8)
    return {
        'a':a,'b':b,'rateP':logint(Pn)/n,'rateQ':logint(Qn)/n,
        'qCoeffSigns':qs,'qValueSigns':qvs,'q0bits':abs(q[0]).bit_length(),
        'qMaxBits':max(abs(z).bit_length() for z in q),
        'minorSignSet':sorted(minor_signs),'realRoots':realroots,'intervalRoots':intervalroots,
        'Pn':Pn,'Qn':Qn,
    }


def prod(it):
    z=1
    for x in it: z*=x
    return z

A=apery(max(TARGETS))
D=diff_table(A,max(TARGETS))
print('Q754 SIGNED KERNEL AUDIT')
for n in TARGETS:
    H=(n-1)//3
    if H<=20: splits=range(H+1)
    else: splits=sorted(set([0,1,H//6,H//4,H//3,H//2,2*H//3,3*H//4,5*H//6,H-1,H]))
    recs=[audit(n,A,D,a) for a in splits]
    print('N',n,'H',H)
    for r in recs:
        print('SPLIT',r['a'],r['b'],f"rateP={r['rateP']:.9f}",f"rateQ={r['rateQ']:.9f}",
              'qcoeff='+r['qCoeffSigns'],'qvals='+r['qValueSigns'],
              'q0bits='+str(r['q0bits']),'qmaxbits='+str(r['qMaxBits']),
              'minorSigns='+repr(r['minorSignSet']),
              'roots='+str(r['realRoots'])+'/'+str(r['intervalRoots']))
