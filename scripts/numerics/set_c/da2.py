from num1 import *
for t in [mpf(-3),mpf(-0.01),mpf(-100)]:
    b=sqrt(1-4/t)
    L=log((b+1)/(b-1))
    c=-mpf(5)/9 + (b**2)/3*0 + 0
    # try standard: (1/3)[ -5/3 + ... ] search: Delta = -8/9 + b^2/3 - b(3-b^2)/6 * L  sign variants
    for s1 in (1,-1):
      for s2 in (1,-1):
        v=-mpf(8)/9*s1 + b**2/3*s1 + s2*b*(3-b**2)/6*L
        print(s1,s2,v)
    print(dalpha_q(t))
