# I17 C^-1 closed form vs the LR96/L01 target setELaurentI17 (numerical check)
from mpmath import mp, gamma, pi, zeta, mpf, taylor
mp.dps = 40
def I17C(e):
    return (gamma(1-e)**3*gamma(2*e-1)*gamma(3*e-2)*gamma(5-6*e)
            /(gamma(3-3*e)*gamma(4-4*e)))/gamma(1+e)**3
z3=zeta(3)
L = [mpf(-1)/6, mpf(-35)/36, -pi**2/3-mpf(559)/216, -16*z3/3-35*pi**2/18+mpf(2737)/1296]
# also LR96 eps^2 for info
f = lambda e: e**2*I17C(e)
c = taylor(f, mpf('1e-30'), 4)
for k in range(4): print(k-2, c[k], L[k], c[k]-L[k])
print('eps^2 coeff', c[4], -37*pi**4/45-280*z3/9-559*pi**2/108+mpf(552041)/7776)
