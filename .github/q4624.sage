print('BEGIN_Q4624')

# Raw Kubert X_1(16) polynomial and Tate-normal-form invariants.
R.<r,s> = PolynomialRing(QQ)
F16 = (r^3*s^2 - 4*r^3*s + 2*r^3
       + 3*r^2*s^2 + 2*r^2*s - 2*r^2
       - r*s^5 + 4*r*s^4 - 10*r*s^3
       + 6*r*s^2 - 3*r*s + r + s^4)
b = r*s*(r-1)
c = s*(r-1)
M = 16*b^2 - 8*b*c^2 - 20*b*c + b + c*(c-1)^3
D = b*M
m8 = r*s - 2*r + 1
print('F16=',F16)
print('TATE_M_RS_FACTOR=',factor(M))
print('DISC_RS_FACTOR=',factor(D))

# Work in the optimized model y^2 + (x^3+x^2-x+1)y + x^2 = 0.
Kx.<x> = FunctionField(QQ)
PY.<Y> = PolynomialRing(Kx)
A = x^3+x^2-x+1
K.<y> = Kx.extension(Y^2 + A*Y + x^2)
rxy = (x^2-x*y+y^2+y)/(x^2+x-y-1)
sxy = (x-y)/(x+1)
bxy = rxy*sxy*(rxy-1)
cxy = sxy*(rxy-1)
Mxy = 16*bxy^2 - 8*bxy*cxy^2 - 20*bxy*cxy + bxy + cxy*(cxy-1)^3
Dxy = bxy*Mxy
print('F16_XY=',F16(r=rxy,s=sxy))
print('B_XY=',bxy)
print('C_XY=',cxy)
print('M_XY=',Mxy)
print('D_XY=',Dxy)
print('D_XY_LIST=',Dxy.list())

# Standard hyperelliptic coordinates V^2=U(U^2+1)(U^2+2U-1).
KU.<U> = FunctionField(QQ)
PV.<VV> = PolynomialRing(KU)
hU = U*(U^2+1)*(U^2+2*U-1)
L.<V> = KU.extension(VV^2-hU)
xUV = (1-U)/(1+U)
AUV = xUV^3+xUV^2-xUV+1
zUV = 4*V/(1+U)^3
yUV = (zUV-AUV)/2
rUV = (xUV^2-xUV*yUV+yUV^2+yUV)/(xUV^2+xUV-yUV-1)
sUV = (xUV-yUV)/(xUV+1)
bUV = rUV*sUV*(rUV-1)
cUV = sUV*(rUV-1)
MUV = 16*bUV^2 - 8*bUV*cUV^2 - 20*bUV*cUV + bUV + cUV*(cUV-1)^3
DUV = bUV*MUV
print('R_UV=',rUV)
print('S_UV=',sUV)
print('B_UV=',bUV)
print('C_UV=',cUV)
print('M_UV=',MUV)
print('D_UV=',DUV)
print('D_UV_LIST=',DUV.list())

def print_elem(label,q):
    coeff=q.list()
    while len(coeff)<2: coeff.append(KU(0))
    for i,ci in enumerate(coeff[:2]):
        print(label,'COEFF',i,'NUM_FACTOR',factor(ci.numerator()),'DEN_FACTOR',factor(ci.denominator()))
    print(label,'NORM_FACTOR',factor(q.norm()))
print_elem('DUV',DUV)
print_elem('BUV',bUV)
print_elem('MUV',MUV)
print('END_Q4624')
