from sage.all import *

print("Q4859 exact factor audit starting")

R = PolynomialRing(QQ, 'n')
n = R.gen()


def sh_poly(p, k):
    return R(p(n=n+k))


def sh_mat(A, k):
    return A.apply_map(lambda x: sh_poly(x, k))

# Problem 2.5 polynomial trajectory matrix.
m11 = (-2*n-5)*(n+3)^2*(136*n^4+1424*n^3+5548*n^2+9551*n+6141)
m12 = 384*n^6+6384*n^5+44168*n^4+162698*n^3+336377*n^2+369933*n+169011
m13 = -480*n^4-4980*n^3-19210*n^2-32690*n-20730
m21 = (n+2)^2*(n+3)^2*(4*n+10)*(48*n^3+386*n^2+1017*n+879)
m22 = (n+2)^2*(-272*n^5-3848*n^4-21732*n^3-61184*n^2-85761*n-47808)
m23 = (n+2)^2*(320*n^3+2540*n^2+6610*n+5640)
m31 = (-4*n-10)*(n+2)^2*(n+3)^2*(32*n^4+302*n^3+1037*n^2+1530*n+813)
m32 = (n+2)^2*(192*n^6+2984*n^5+19116*n^4+64452*n^3+120256*n^2+117279*n+46476)
m33 = (n+2)^2*(-16*n^5-408*n^4-2912*n^3-8884*n^2-12254*n-6240)
M = matrix(R, [[m11,m12,m13],[m21,m22,m23],[m31,m32,m33]])

print("det M factor:", factor(M.det()))

# Scalarization for the first output column.  For a row solution x_{n+1}=x_n M(n),
# y_n=x_n e, the transported columns v_j give y_{n+j}=x_n v_j.
e = vector(R, [1,0,0])
v0 = e
v1 = M*e
v2 = M*sh_mat(M,1)*e
v3 = M*sh_mat(M,1)*sh_mat(M,2)*e
vs = [v0,v1,v2,v3]
cs = []
for k in range(4):
    cols = [vs[j] for j in range(4) if j != k]
    C = matrix(R, 3, 3, cols).transpose()  # columns are the transported vectors
    cs.append((-1)^k*C.det())

# Verify alternating-minor relation.
rel = sum((cs[k]*vs[k] for k in range(4)), vector(R,[0,0,0]))
assert rel == vector(R,[0,0,0])

g = gcd(cs)
cs = [R(c/g) for c in cs]
if cs[3].leading_coefficient() > 0:
    cs = [-c for c in cs]
print("raw primitive degrees:", [c.degree() for c in cs])
print("raw endpoint factors:")
print("c0 =", factor(cs[0]))
print("c3 =", factor(cs[3]))

# Hypergeometric rank-one twist H_{n+1}/H_n.
delta = -2*(n+2)^2*(n+3)^2*(2*n+5)*(2*n+7)^2
nh = []
prod = R.one()
for j in range(4):
    if j > 0:
        prod *= sh_poly(delta,j-1)
    nh.append(R(cs[j]*prod))
gh = gcd(nh)
nh = [R(c/gh) for c in nh]
cont = gcd([ZZ(c.content()) for c in nh])
if cont != 0 and abs(cont) != 1:
    nh = [R(c/cont) for c in nh]
if nh[3].leading_coefficient() < 0:
    nh = [-c for c in nh]

print("normalized primitive degrees:", [c.degree() for c in nh])
print("normalized coefficients begin")
for j,c in enumerate(nh):
    print("ell%d = %s" % (j,c))
    print("ell%d factor = %s" % (j,factor(c)))
print("normalized coefficients end")
print("sum coefficients factor (S-1 test):", factor(sum(nh)))

K = FractionField(R)


def shift_rat(f,k):
    num = R(f.numerator())
    den = R(f.denominator())
    return K(sh_poly(num,k))/K(sh_poly(den,k))


def riccati_residual(coeffs, r):
    ans = K.zero()
    q = K.one()
    for j in range(4):
        ans += K(coeffs[j])*q
        q *= shift_rat(r,j)
    return K(ans)

r_candidates = {
    "one": K.one(),
    "simple_nminus3": K((n+1)^3)/K((n+2)^3),
    "det_MH": K((n+1)*(2*n+3)^2)/K((n+3)*(2*n+7)^2),
    "det_balanced": K((n+2)^3*(2*n+3)^2)/K((n+1)^2*(n+3)*(2*n+7)^2),
}
for name,r in r_candidates.items():
    res = riccati_residual(nh,r)
    print("candidate", name, "r=", r)
    print("candidate residual zero?", res == 0)
    if res != 0:
        print("candidate residual factor num:", factor(R(res.numerator())))
        print("candidate residual factor den:", factor(R(res.denominator())))

# First-order LEFT factors of L correspond to hypergeometric solutions of the
# shifted formal adjoint S^3 L^*.  Its coefficient of S^k is ell_{3-k}(n+k).
adj = [sh_poly(nh[3-k], k) for k in range(4)]
print("adjoint-shifted degrees:", [c.degree() for c in adj])
print("adjoint-shifted endpoints:", factor(adj[0]), factor(adj[3]))

# SymPy's rsolve_hyper is an independent implementation of Petkovsek's
# complete hypergeometric-solution algorithm.  Run it on L and the adjoint.
try:
    import sympy as sp
    from sympy.solvers.recurr import rsolve_hyper
    x = sp.symbols('n', integer=True)

    def to_sp(p):
        return sp.sympify(str(p).replace('^','**'), locals={'n':x})

    for label, coeffs in [('RIGHT_ORIGINAL',nh),('RIGHT_ADJOINT_FOR_LEFT_FACTOR',adj)]:
        sp_coeffs = [to_sp(c) for c in coeffs]
        print("SYMPY_RSOLVE_HYPER_CALL",label)
        try:
            sol = rsolve_hyper(sp_coeffs, sp.Integer(0), x)
            print("SYMPY_RSOLVE_HYPER_RESULT",label,repr(sol))
        except Exception as ex:
            print("SYMPY_RSOLVE_HYPER_ERROR",label,type(ex).__name__,str(ex))
except Exception as ex:
    print("SYMPY_SETUP_ERROR",type(ex).__name__,str(ex))

# Build the Ore operator and inspect/call all available exact factor routines.
try:
    from ore_algebra import OreAlgebra
    OA = OreAlgebra(R)
    S = OA.gen()
    L = sum((OA(nh[j])*S^j for j in range(4)), OA.zero())
    print("Ore operator:", L)
    methods = [x for x in dir(L) if any(key in x.lower() for key in ['factor','hypergeom','solution','riccati'])]
    print("relevant Ore methods:", methods)
    for meth in ['factor','right_factors','left_factors','hypergeometric_solutions','solutions']:
        if hasattr(L,meth):
            print("CALL",meth,"over QQ(n)")
            try:
                out = getattr(L,meth)()
                print("RESULT",meth,out)
            except Exception as ex:
                print("ERROR",meth,type(ex).__name__,str(ex))

    # Test the shifted adjoint as an Ore operator too.
    Ladj = sum((OA(adj[j])*S^j for j in range(4)), OA.zero())
    print("Shifted adjoint Ore operator:", Ladj)
    for meth in ['factor','right_factors','left_factors','hypergeometric_solutions','solutions']:
        if hasattr(Ladj,meth):
            print("CALL_ADJOINT",meth,"over QQ(n)")
            try:
                out = getattr(Ladj,meth)()
                print("RESULT_ADJOINT",meth,out)
            except Exception as ex:
                print("ERROR_ADJOINT",meth,type(ex).__name__,str(ex))

    # Repeat over Q(sqrt(2)).
    K2 = QuadraticField(2, 'a')
    R2 = PolynomialRing(K2, 'n')
    OA2 = OreAlgebra(R2)
    S2 = OA2.gen()
    nh2 = [R2(str(c)) for c in nh]
    adj2 = [R2(str(c)) for c in adj]
    L2 = sum((OA2(nh2[j])*S2^j for j in range(4)), OA2.zero())
    L2adj = sum((OA2(adj2[j])*S2^j for j in range(4)), OA2.zero())
    print("Ore operators over Qsqrt2 constructed")
    methods2 = [x for x in dir(L2) if any(key in x.lower() for key in ['factor','hypergeom','solution','riccati'])]
    print("relevant Ore methods Qsqrt2:", methods2)
    for label,op in [('ORIGINAL',L2),('ADJOINT',L2adj)]:
        for meth in ['factor','right_factors','left_factors','hypergeometric_solutions','solutions']:
            if hasattr(op,meth):
                print("CALL_QSQRT2",label,meth)
                try:
                    out = getattr(op,meth)()
                    print("RESULT_QSQRT2",label,meth,out)
                except Exception as ex:
                    print("ERROR_QSQRT2",label,meth,type(ex).__name__,str(ex))
except Exception as ex:
    print("ORE_SETUP_ERROR",type(ex).__name__,str(ex))

print("Q4859 exact factor audit finished")
