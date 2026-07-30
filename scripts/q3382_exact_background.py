#!/usr/bin/env python3
from __future__ import annotations
from fractions import Fraction
from math import factorial


def lam(h: int) -> int:
    return h*(h+1)


def apery_values(nmax: int) -> list[int]:
    b=[0]*(nmax+1); b[0]=1
    if nmax>=1: b[1]=5
    for n in range(1,nmax):
        P=34*n**3+51*n**2+27*n+5
        num=P*b[n]-n**3*b[n-1]
        den=(n+1)**3
        assert num%den==0
        b[n+1]=num//den
    return b


def padd(a,b):
    n=max(len(a),len(b)); c=[Fraction(0) for _ in range(n)]
    for i,x in enumerate(a): c[i]+=x
    for i,x in enumerate(b): c[i]+=x
    while len(c)>1 and c[-1]==0: c.pop()
    return c


def pscale(a,s):
    return [x*s for x in a]


def pmul(a,b):
    c=[Fraction(0) for _ in range(len(a)+len(b)-1)]
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    while len(c)>1 and c[-1]==0: c.pop()
    return c


def peval(a,x):
    y=Fraction(0)
    for c in reversed(a): y=y*x+c
    return y


def pdiv_monic_quadratic(a, r1, r2):
    # divide by (T-r1)(T-r2)=T^2-(r1+r2)T+r1*r2
    q=[Fraction(0) for _ in range(max(1,len(a)-2))]
    rem=a[:]
    for k in range(len(a)-1,1,-1):
        coeff=rem[k]
        q[k-2]=coeff
        rem[k]-=coeff
        rem[k-1]+=coeff*(r1+r2)
        rem[k-2]-=coeff*r1*r2
    assert all(x==0 for x in rem[:2]), rem[:2]
    return q


def compose_affine(a, u, v):
    # a(u+vX)
    out=[Fraction(0)]
    power=[Fraction(1)]
    for c in a:
        out=padd(out,pscale(power,c))
        power=pmul(power,[Fraction(u),Fraction(v)])
    return out


def delta(J,h):
    return Fraction(((-1)**(J-h))*factorial(J-h)*factorial(J+h+1),2*h+1)


def lagrange_poly(J,h):
    p=[Fraction(1)]
    for r in range(J+1):
        if r!=h: p=pmul(p,[Fraction(-lam(r)),Fraction(1)])
    d=delta(J,h)
    assert d.denominator==1
    return pscale(p,Fraction(1,d.numerator))


def mod_fraction(x: Fraction,q:int,exp:int=1)->int:
    m=q**exp
    assert x.denominator%q
    return x.numerator*pow(x.denominator,-1,m)%m


def vp_frac(x:Fraction,q:int)->int:
    def v(n):
        n=abs(n); e=0
        while n and n%q==0: n//=q; e+=1
        return e
    return v(x.numerator)-v(x.denominator)


def derivative(a,order=1):
    out=a[:]
    for _ in range(order): out=[(i+1)*out[i+1] for i in range(len(out)-1)]
    return out


def reconstruct(q=37,i=16,J=20):
    s=q-1-i; t=q-1-2*i; e=2*i+1
    b=apery_values(J)
    L=[lagrange_poly(J,h) for h in range(J+1)]
    S=[Fraction(0)]
    for h in range(J+1): S=padd(S,pscale(L[h],b[h]))
    pair=padd(pscale(L[i],b[i]),pscale(L[s],b[s]))
    H=padd(S,pscale(pair,-1))
    G=pdiv_monic_quadratic(H,lam(i),lam(s))
    assert all(c.denominator%q for c in H)
    assert all(c.denominator%q for c in G)
    Hx=compose_affine(H,lam(i),q)
    Gx=compose_affine(G,lam(i),q)
    rhs=pscale(pmul([Fraction(0),Fraction(-t),Fraction(1)],Gx),q*q)
    assert Hx==rhs

    # full direct Taylor coefficients
    Sp=peval(derivative(S),lam(i)); Spp=peval(derivative(S,2),lam(i))
    beta=Fraction(b[i],q); assert beta.denominator==1
    a0=mod_fraction(beta,q); a1=mod_fraction(Sp,q)
    c0=mod_fraction((beta-a0)/q,q)
    c1=mod_fraction((Sp-a1)/q,q)
    c2=mod_fraction(Spp/2,q)

    # Q3326 pair+background formulas with exact g
    di=delta(J,i)/q; ds=delta(J,s)/q
    assert di.denominator==ds.denominator==1
    di=int(di); ds=int(ds); assert (di+ds)%q==0
    kappa=(di+ds)//q
    nu=pow(di,-1,q*q); u0=nu%q; u1=((nu-u0)//q)%q
    beta_int=b[i]//q; beta0=beta_int%q; beta1=((beta_int-beta0)//q)%q
    D=(b[s]-b[i])//q; D0=D%q; D1=((D-D0)//q)%q
    R=[Fraction(1)]
    for h in range(J+1):
        if h not in (i,s): R=pmul(R,[Fraction(-lam(h)),Fraction(1)])
    Rli=peval(R,lam(i)); Rp=peval(derivative(R),lam(i))
    assert Rli.denominator==Rp.denominator==1
    Rli=int(Rli); Rp=int(Rp)
    r0=Rli%q; r1=((Rli-r0)//q)%q; rp=Rp%q
    g=mod_fraction(peval(G,lam(i)),q)
    s0=(e*(beta1*u0+beta0*u1)-beta0*u0)%q
    s1=(-(beta0+D0)*kappa*u0*u0-D1*u0-D0*u1)%q
    pred=(
      r0*u0*e*beta0%q,
      -r0*u0*D0%q,
      (r0*s0+r1*u0*e*beta0)%q,
      (r0*s1-r1*u0*D0+rp*u0*e*beta0+e*g)%q,
      (-rp*u0*D0+g)%q,
    )
    direct=(a0,a1,c0,c1,c2)

    # pair-only Taylor + exact background check
    pairp=peval(derivative(pair),lam(i)); pairpp=peval(derivative(pair,2),lam(i))
    pair_direct=(
      mod_fraction(Fraction(b[i],q),q),
      mod_fraction(pairp,q),
      mod_fraction((Fraction(b[i],q)-a0)/q,q),
      mod_fraction((pairp-mod_fraction(pairp,q))/q,q),
      mod_fraction(pairpp/2,q),
    )
    bg_contrib=(0,0,0,e*g%q,g)
    print('Q3382_Q37_COEFFICIENTWISE')
    print('q_i_s_J_t',q,i,s,J,t)
    print('b_i_b_s_D',b[i],b[s],D)
    print('H_degree_G_degree',len(H)-1,len(G)-1)
    print('H_coefficients: degree numerator denominator vq')
    for k,c in enumerate(H): print(k,c.numerator,c.denominator,vp_frac(c,q))
    print('G_coefficients: degree numerator denominator vq residue')
    for k,c in enumerate(G): print(k,c.numerator,c.denominator,vp_frac(c,q),mod_fraction(c,q))
    print('G_at_lambda_i',peval(G,lam(i)),'g_mod_q',g)
    print('direct_coeffs',direct)
    print('predicted_coeffs',pred)
    print('pair_direct',pair_direct,'background_contrib',bg_contrib)
    print('coefficient_formula_pass',direct==pred)
    assert direct==pred
    print('factor_exact_pass',True)

if __name__=='__main__': reconstruct()
