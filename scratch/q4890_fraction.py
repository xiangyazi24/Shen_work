#!/usr/bin/env python3
from __future__ import annotations

from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
from math import comb, factorial, gcd
from typing import Callable, Dict, Iterable, List, Sequence, Tuple

print('Q4890 pure-Python exact/modular contiguous-band search')

Pair = Tuple[F, F]

# ------------------------------------------------------------------
# Basic arithmetic
# ------------------------------------------------------------------
def rf(a: F, m: int) -> F:
    z = F(1)
    for j in range(m):
        z *= a + j
    return z


def mat_mul(A, B):
    nr, nk, nc = len(A), len(B), len(B[0])
    return [[sum(A[i][k] * B[k][j] for k in range(nk)) for j in range(nc)] for i in range(nr)]


def row_mul(v, A):
    return [sum(v[k] * A[k][j] for k in range(len(v))) for j in range(len(A[0]))]


def mat_vec(A, v):
    return [sum(A[i][k] * v[k] for k in range(len(v))) for i in range(len(A))]


def det3(A):
    return (
        A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1])
        - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0])
        + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0])
    )


def transpose(A):
    return [list(x) for x in zip(*A)]


# ------------------------------------------------------------------
# Printed CMF and H normalization
# ------------------------------------------------------------------
def M_int(n: int):
    m11 = (-2*n-5)*(n+3)**2*(136*n**4+1424*n**3+5548*n**2+9551*n+6141)
    m12 = 384*n**6+6384*n**5+44168*n**4+162698*n**3+336377*n**2+369933*n+169011
    m13 = -(480*n**4+4980*n**3+19210*n**2+32690*n+20730)
    m21 = (n+2)**2*(n+3)**2*(4*n+10)*(48*n**3+386*n**2+1017*n+879)
    m22 = -(n+2)**2*(272*n**5+3848*n**4+21732*n**3+61184*n**2+85761*n+47808)
    m23 = (n+2)**2*(320*n**3+2540*n**2+6610*n+5640)
    m31 = -(4*n+10)*(n+2)**2*(n+3)**2*(32*n**4+302*n**3+1037*n**2+1530*n+813)
    m32 = (n+2)**2*(192*n**6+2984*n**5+19116*n**4+64452*n**3+120256*n**2+117279*n+46476)
    m33 = -(n+2)**2*(16*n**5+408*n**4+2912*n**3+8884*n**2+12254*n+6240)
    return [[m11,m12,m13],[m21,m22,m23],[m31,m32,m33]]


def delta_H(n: int) -> int:
    return -2*(n+2)**2*(n+3)**2*(2*n+5)*(2*n+7)**2


def MH(n: int):
    d = delta_H(n)
    return [[F(x,d) for x in row] for row in M_int(n)]


@lru_cache(None)
def ell_exact(n: int) -> Tuple[F,F,F,F]:
    e = [F(1),F(0),F(0)]
    vectors = [e]
    P = [[F(int(i==j)) for j in range(3)] for i in range(3)]
    for j in range(1,4):
        P = mat_mul(P, MH(n+j-1))
        vectors.append(mat_vec(P,e))
    coeffs=[]
    for j in range(4):
        cols=[vectors[r] for r in range(4) if r != j]
        coeffs.append(((-1)**j)*det3(transpose(cols)))
    return tuple(coeffs)


# ------------------------------------------------------------------
# Exact target CMF moment pairs q*G-p
# ------------------------------------------------------------------
def target_pairs(Nmax: int) -> List[Pair]:
    p=[F(30921),F(-32972),F(8240)]
    q=[F(33750),F(-36000),F(9000)]
    ans=[]
    for n in range(Nmax+1):
        ans.append((q[0],p[0]))
        if n < Nmax:
            A=MH(n)
            p=row_mul(p,A)
            q=row_mul(q,A)
    return ans

TARGET_MAX=180
TARGET=target_pairs(TARGET_MAX)
print('target initial pairs:',TARGET[:3])
print('first exact recurrence coefficients:',ell_exact(0))


# ------------------------------------------------------------------
# Polynomial utilities
# ------------------------------------------------------------------
def p_trim(a: List[F]) -> List[F]:
    while len(a)>1 and a[-1]==0:
        a.pop()
    return a


def p_add(a: Sequence[F], b: Sequence[F]) -> List[F]:
    n=max(len(a),len(b)); c=[F(0)]*n
    for i,x in enumerate(a): c[i]+=x
    for i,x in enumerate(b): c[i]+=x
    return p_trim(c)


def p_scale(a: Sequence[F], c: F) -> List[F]:
    return p_trim([c*x for x in a])


def p_shift(a: Sequence[F], k: int=1) -> List[F]:
    return [F(0)]*k+list(a)


def p_mul_linear_xplus1(a: Sequence[F]) -> List[F]:
    return p_add(a,p_shift(a))


def div_xplus1(a: Sequence[F]) -> Tuple[List[F],F]:
    # Ascending coefficients. Synthetic division at root -1.
    d=len(a)-1
    if d<1: return [F(0)], a[0] if a else F(0)
    q=[F(0)]*d
    q[d-1]=a[d]
    for k in range(d-1,0,-1):
        q[k-1]=a[k]-q[k]
    rem=a[0]-q[0]
    return p_trim(q),rem


def p_derivative(a: Sequence[F]) -> List[F]:
    if len(a)<=1: return [F(0)]
    return p_trim([F(i)*a[i] for i in range(1,len(a))])


def p_eval(a: Sequence[F], x: F) -> F:
    s=F(0)
    for c in reversed(a): s=s*x+c
    return s


# ------------------------------------------------------------------
# Jacobi / CD families and Catalan moment pairs
# ------------------------------------------------------------------
def odd_harmonic(m: int) -> F:
    return sum((F(1,2*r+1) for r in range(m)),F(0))


@lru_cache(None)
def J_and_dJ(N: int):
    pref=rf(F(1,2),N)/factorial(N)
    J=[F(0)]*(N+1); dJ=[F(0)]*(N+1)
    for k in range(N+1):
        c=F((-1)**k*comb(N,k))*pref*rf(F(N)+F(1,2),k)/rf(F(1,2),k)
        dlog=(2*odd_harmonic(N)
              +2*sum((F(1,2*N+2*r+1) for r in range(k)),F(0))
              -2*odd_harmonic(k))
        J[k]=c; dJ[k]=c*dlog
    return tuple(J),tuple(dJ)


@lru_cache(None)
def R_poly(N: int):
    J,dJ=J_and_dJ(N); J=list(J); dJ=list(dJ)
    B=p_eval(J,F(-1)); dB=p_eval(dJ,F(-1))
    num=p_add(p_scale(dJ,B),p_scale(J,-dB))
    C,rem=div_xplus1(num)
    assert rem==0
    term=p_add(p_scale(p_shift(p_derivative(C)),F(2)),C)  # 2 X C' + C
    term=p_mul_linear_xplus1(term)
    ans=p_add(p_scale(J,B),p_scale(term,F(-1,2)))
    return tuple(p_scale(ans,F(4*N+1,2)))


@lru_cache(None)
def P_poly(N: int):
    J,_=J_and_dJ(N); J=list(J)
    return tuple(p_scale(J,F(4*N+1,2)*p_eval(J,F(-1))))


@lru_cache(None)
def K_poly(N: int):
    if N==0: return P_poly(0)
    return tuple(p_add(K_poly(N-1),P_poly(N)))


@lru_cache(None)
def catalan_monomial_pair(k: int) -> Pair:
    q=F((-1)**k)
    partial=sum((F((-1)**j,(2*j+1)**2) for j in range(k)),F(0))
    return q,q*partial


def moment_pair(poly: Sequence[F]) -> Pair:
    q=p=F(0)
    for k,a in enumerate(poly):
        qk,pk=catalan_monomial_pair(k)
        q+=a*qk; p+=a*pk
    return q,p

FAMILIES={'R':R_poly,'K':K_poly,'P':P_poly}


@lru_cache(None)
def family_pair(name: str,N: int) -> Pair:
    return moment_pair(FAMILIES[name](N))

for name in FAMILIES:
    print(name,'initial pairs:',[family_pair(name,j) for j in range(3)])

for name in FAMILIES:
    bad=None
    for m in range(8):
        for comp in (0,1):
            z=sum(ell_exact(m)[j]*family_pair(name,m+j)[comp] for j in range(4))
            if z:
                bad=(m,comp,z); break
        if bad: break
    print(name,'first recurrence residual:',bad)


# ------------------------------------------------------------------
# Modular arithmetic and Gaussian ranks
# ------------------------------------------------------------------
def fmod(x: F,p: int) -> int:
    return (x.numerator%p)*pow(x.denominator%p,-1,p)%p


def rank_aug_mod(rows: Sequence[Sequence[F]], rhs: Sequence[F], p: int):
    A=[[fmod(x,p) for x in row]+[fmod(b,p)] for row,b in zip(rows,rhs)]
    nr=len(A); nc=len(A[0])-1
    r=0; piv=[]
    for c in range(nc):
        pivot=next((i for i in range(r,nr) if A[i][c]),None)
        if pivot is None: continue
        A[r],A[pivot]=A[pivot],A[r]
        inv=pow(A[r][c],-1,p)
        A[r]=[(x*inv)%p for x in A[r]]
        for i in range(nr):
            if i!=r and A[i][c]:
                z=A[i][c]
                A[i]=[(A[i][j]-z*A[r][j])%p for j in range(nc+1)]
        piv.append(c); r+=1
        if r==nr: break
    rankA=r
    inconsistent=any(all(A[i][c]==0 for c in range(nc)) and A[i][nc]!=0 for i in range(nr))
    return rankA,rankA+(1 if inconsistent else 0),A,piv


def solve_fraction(rows: Sequence[Sequence[F]], rhs: Sequence[F]):
    A=[list(row)+[b] for row,b in zip(rows,rhs)]
    nr=len(A); nc=len(A[0])-1; r=0; piv=[]
    for c in range(nc):
        pivot=next((i for i in range(r,nr) if A[i][c]),None)
        if pivot is None: continue
        A[r],A[pivot]=A[pivot],A[r]
        inv=1/A[r][c]
        A[r]=[x*inv for x in A[r]]
        for i in range(nr):
            if i!=r and A[i][c]:
                z=A[i][c]
                A[i]=[A[i][j]-z*A[r][j] for j in range(nc+1)]
        piv.append(c); r+=1
    if any(all(A[i][c]==0 for c in range(nc)) and A[i][nc]!=0 for i in range(nr)):
        return None
    sol=[F(0)]*nc
    for i,c in enumerate(piv): sol[c]=A[i][nc]
    return sol


# ------------------------------------------------------------------
# Band system
# ------------------------------------------------------------------
DENS: Dict[str,Callable[[int],int]]={
 'one':lambda n:1,
 'matrix':lambda n:(n+2)**2*(n+3)**2*(2*n+5)*(2*n+7)**2,
 'det':lambda n:(n+1)**5*(n+2)**3*(2*n+3)**2*(2*n+5)**2,
 'shift':lambda n:(n+1)*(n+2)*(n+3)*(n+4)*(2*n+1)*(2*n+3)*(2*n+5)*(2*n+7)*(2*n+9)*(2*n+11),
}
DEN_DEG={'one':0,'matrix':7,'det':12,'shift':10}
PRIMES=(1000003,1000033,1000037)


def build_system(names: Tuple[str,...],width: int,degree: int,dname: str,Nrec: int):
    D=DENS[dname]
    labels=[(nm,r,d) for nm in names for r in range(width+1) for d in range(degree+1)]
    rows=[]; rhs=[]
    def weight(m,d): return F(m**d,D(m))
    for m in range(Nrec+1):
        ell=ell_exact(m)
        for comp in (0,1):
            row=[]
            for nm,r,d in labels:
                z=F(0)
                for j in range(4):
                    z += ell[j]*weight(m+j,d)*family_pair(nm,m+j+r)[comp]
                row.append(z)
            rows.append(row); rhs.append(F(0))
    for m in range(3):
        for comp in (0,1):
            rows.append([weight(m,d)*family_pair(nm,m+r)[comp] for nm,r,d in labels])
            rhs.append(TARGET[m][comp])
    return labels,rows,rhs


def verify(sol,labels,dname,Nmax=120):
    D=DENS[dname]
    coeff: Dict[Tuple[str,int],List[F]]={}
    for c,(nm,r,d) in zip(sol,labels):
        if c:
            arr=coeff.setdefault((nm,r),[])
            while len(arr)<=d: arr.append(F(0))
            arr[d]+=c
    def cp(m):
        q=p=F(0)
        for (nm,r),arr in coeff.items():
            w=sum(arr[d]*m**d for d in range(len(arr)))/D(m)
            qq,pp=family_pair(nm,m+r); q+=w*qq; p+=w*pp
        return q,p
    for m in range(min(Nmax,len(TARGET)-1)+1):
        if cp(m)!=TARGET[m]: return False,coeff,('target',m,cp(m),TARGET[m])
    return True,coeff,None


def print_coeff(coeff,dname):
    print('COMMON DENOMINATOR:',dname)
    for key in sorted(coeff):
        arr=coeff[key]
        terms=[]
        for d,c in enumerate(arr):
            if c: terms.append('(%s)*n^%d'%(c,d))
        print('%s_%d(n) = (%s) / D_%s(n)'%(key[0],key[1],' + '.join(terms) or '0',dname))


def run(names,width,degree,dname):
    unknowns=len(names)*(width+1)*(degree+1)
    Nrec=max(12,(unknowns+14)//2)
    print('\nSEARCH',names,'width',width,'degree',degree,'den',dname,'unknowns',unknowns,'Nrec',Nrec,flush=True)
    labels,rows,rhs=build_system(names,width,degree,dname,Nrec)
    survived=True
    for p in PRIMES:
        ra,rg,_,_=rank_aug_mod(rows,rhs,p)
        print(' mod',p,'rank',ra,'aug',rg,flush=True)
        if ra!=rg:
            survived=False; break
    if not survived: return None
    print(' survived modular screens: solving over Q',flush=True)
    sol=solve_fraction(rows,rhs)
    if sol is None:
        print(' exact system inconsistent',flush=True); return None
    good,coeff,why=verify(sol,labels)
    print(' exact held-out verification',good,why,flush=True)
    if good:
        print('FOUND EXACT BAND',flush=True); print_coeff(coeff,dname); return coeff
    return None


FOUND=None
# Polynomial R/K bands through degree 10.
for width in (2,3):
    for degree in range(0,11):
        FOUND=run(('R','K'),width,degree,'one')
        if FOUND: break
    if FOUND: break

# Standard CMF-derived common denominator classes, allowing numerator degree Ddeg-3 ... Ddeg+2.
if FOUND is None:
    for width in (2,3):
        for dname in ('matrix','det','shift'):
            for growth in range(-3,3):
                degree=max(0,DEN_DEG[dname]+growth)
                if len(('R','K'))*(width+1)*(degree+1)>240:
                    continue
                FOUND=run(('R','K'),width,degree,dname)
                if FOUND: break
            if FOUND: break
        if FOUND: break

# Small enlargement by the non-derivative product family.
if FOUND is None:
    for width in (2,3):
        for degree in range(0,7):
            FOUND=run(('R','K','P'),width,degree,'one')
            if FOUND: break
        if FOUND: break

print('\n============================================================',flush=True)
if FOUND:
    print('FINAL RESULT: exact band found and verified.',flush=True)
else:
    print('FINAL RESULT: NO solution in tested polynomial and standard-denominator bands.',flush=True)
    print('Scope: R/K widths 2,3 polynomial degrees <=10; matrix/det/shift common denominators with numerator growth -3..+2; R/K/P polynomial degree <=6.',flush=True)
print('============================================================',flush=True)
