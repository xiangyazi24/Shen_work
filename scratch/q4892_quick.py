#!/usr/bin/env python3
from fractions import Fraction as Q
from math import comb
import sympy as sp

NMAX=45; TRAIN=32

def M(n):
 return (( (-2*n-5)*(n+3)**2*(136*n**4+1424*n**3+5548*n**2+9551*n+6141), 384*n**6+6384*n**5+44168*n**4+162698*n**3+336377*n**2+369933*n+169011, -480*n**4-4980*n**3-19210*n**2-32690*n-20730),
 ((n+2)**2*(n+3)**2*(4*n+10)*(48*n**3+386*n**2+1017*n+879), (n+2)**2*(-272*n**5-3848*n**4-21732*n**3-61184*n**2-85761*n-47808), (n+2)**2*(320*n**3+2540*n**2+6610*n+5640)),
 ((-4*n-10)*(n+2)**2*(n+3)**2*(32*n**4+302*n**3+1037*n**2+1530*n+813), (n+2)**2*(192*n**6+2984*n**5+19116*n**4+64452*n**3+120256*n**2+117279*n+46476), (n+2)**2*(-16*n**5-408*n**4-2912*n**3-8884*n**2-12254*n-6240)))

def delta(n): return -2*(n+2)**2*(n+3)**2*(2*n+5)*(2*n+7)**2
def rowmul(v,A): return tuple(sum(v[i]*A[i][j] for i in range(3)) for j in range(3))
def qhats(N):
 q=(Q(33750),Q(-36000),Q(9000)); out=[]
 for n in range(N+1):
  out.append(q[0])
  if n<N:
   qM=rowmul(q,M(n)); q=tuple(x/Q(delta(n)) for x in qM)
 return out
QH=qhats(NMAX); assert QH[1]==Q(5295375,4)

def F(n,k): return 2**k*comb(2*k,k)*comb(n,k)*comb(n+k,k)
L=2*NMAX+4
H=[Q(0)]*L; H2=[Q(0)]*L; O=[Q(0)]*L; O2=[Q(0)]*L; C=[Q(0)]*L
for m in range(1,L):
 H[m]=H[m-1]+Q(1,m); H2[m]=H2[m-1]+Q(1,m*m)
 O[m]=O[m-1]+Q(1,2*m-1); O2[m]=O2[m-1]+Q(1,(2*m-1)**2)
 C[m]=C[m-1]+Q((-1)**(m-1),(2*m-1)**2)
print('FIRST20')
for n,x in enumerate(QH[:20]): print(n,x,sp.N(sp.Rational(x.numerator,x.denominator),25))
W=[]
for n in range(NMAX+1): W.append((QH[n]-sum(F(n,k)*W[k] for k in range(n)))/F(n,n))
print('WEIGHTS20')
for k,x in enumerate(W[:20]): print(k,x)

def S(q): return sp.Rational(q.numerator,q.denominator)
def fit(cols,target):
 A=sp.Matrix([[S(c[n]) for c in cols] for n in range(TRAIN+1)]); b=sp.Matrix([S(x) for x in target[:TRAIN+1]])
 if A.rank()!=A.row_join(b).rank(): return None
 sol=sp.linsolve((A,b)); tup=next(iter(sol)); free=set().union(*(x.free_symbols for x in tup)); sub={x:0 for x in free}; tup=[sp.cancel(x.subs(sub)) for x in tup]
 for n in range(NMAX+1):
  if sp.cancel(sum(tup[j]*S(cols[j][n]) for j in range(len(cols)))-S(target[n]))!=0: return None
 return tup

def mons(d): return [(a,b) for a in range(d+1) for b in range(d+1-a)]
def moment(phi,a,b,den=lambda n,k:Q(1)):
 return [sum(Q(F(n,k))*Q(n**a)*Q(k**b)*phi(n,k)/den(n,k) for k in range(n+1)) for n in range(NMAX+1)]

def search(label,phis,d,den=lambda n,k:Q(1)):
 labs=[]; cols=[]
 for name,phi in phis:
  for a,b in mons(d): labs.append((name,a,b)); cols.append(moment(phi,a,b,den))
 if len(cols)>TRAIN+1: return None
 sol=fit(cols,QH)
 if sol is not None:
  nz=[(labs[i],sol[i]) for i in range(len(sol)) if sol[i]!=0]; print('FOUND',label,nz); return nz
 print('NO',label); return None

one=('1',lambda n,k:Q(1)); found=None
for d in range(7):
 found=search('polynomial degree %d'%d,[one],d)
 if found: break
for dn,den in [('2k+1',lambda n,k:Q(2*k+1)),('n+k+1',lambda n,k:Q(n+k+1)),('n-k+1',lambda n,k:Q(n-k+1))]:
 if found: break
 for d in range(5):
  found=search('%s degree %d'%(dn,d),[one],d,den)
  if found: break
features=[
 [('1',lambda n,k:Q(1)),('Ok',lambda n,k:O[k])],
 [('1',lambda n,k:Q(1)),('dO',lambda n,k:O[n+k]-O[k])],
 [('1',lambda n,k:Q(1)),('dO',lambda n,k:O[n+k]-O[k]),('dO2',lambda n,k:O2[n+k]-O2[k]),('dO_sq',lambda n,k:(O[n+k]-O[k])**2)],
 [('1',lambda n,k:Q(1)),('Ck',lambda n,k:C[k])],
 [('1',lambda n,k:Q(1)),('Hk',lambda n,k:H[k]),('Hk2',lambda n,k:H2[k])]]
for phis in features:
 if found: break
 for d in range(3):
  found=search(str([x[0] for x in phis])+' degree %d'%d,phis,d)
  if found: break
print('FINAL', 'FOUND' if found else 'NO QUICK FORMULA')
