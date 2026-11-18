import math
import numpy as np
from lean_ladder import *
K = 16 * math.pi ** 4 / (64j)
for (zA, Y, za) in ((0.3, 0.35, 0.25), (1.7, 0.8, 0.4), (0.05, 0.1, 2.0)):
    zb = 1 - Y
    z = np.array([zA / 2, Y / 2, Y / 2, zA / 2, za, zb, 0, 0])
    t1, t2, t3 = parts_c2(z, 1.0)
    c = Y * (1 - Y); a = zA + c; U = a + za
    Q0 = (3 * Y - 2) * a ** 2 + (4 * Y - Y ** 2 - 2) * a * za - 2 * c * za ** 2
    p1 = (6 / K) * za * Q0 / (2 * U ** 5)
    p2 = (2 / K) * za * (9 * c + a) / (2 * U ** 4)
    print(t1 / p1, t2 / p2)
