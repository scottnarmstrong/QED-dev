import numpy as np
from lean_ladder import *
zA, Y, za, zb = 0.3, 0.35, 0.25, 0.1
def t(s1, s2):
    z = np.array([s1 * zA, s2 * Y, (1 - s2) * Y, (1 - s1) * zA, za, zb, 0, 0])
    return parts_c2(z, 1.0)[:2]
for s1 in (0.0, 0.25, 0.5, 0.75, 1.0):
    print(s1, [np.round(v.imag, 10) for v in t(s1, 0.5)])
print('inner split:')
for s2 in (0.0, 0.25, 0.5, 0.75, 1.0):
    print(s2, [np.round(v.imag, 10) for v in t(0.5, s2)])
