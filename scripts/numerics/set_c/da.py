from num1 import *
for t in [mpf(-3),mpf(-0.01),mpf(-100)]:
    b=sqrt(1-4/t)
    c=(mpf(1)/3)*(-mpf(8)/3 + b**2 - b*(3-b**2)/2*log((b+1)/(b-1)))
    print(c, dalpha_q(t))
