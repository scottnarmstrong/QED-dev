import sympy as sp, pickle, re
exec(open('gen1lean.py').read().split("out=[]")[0].replace("H,rho,K,pref=pickle.load(open('gen1.pkl','rb'))",""))
exec(open('wraplib.py').read())
LA=['log x','log (1 - x)','log (1 + x)','Li 2 x','Li 2 (-x)']
def monlean(m,var='x'):
    fs=[]
    for e,s in zip(m,LA):
        s=s.replace('x',var)
        if e==1: fs.append(s)
        elif e>1: fs.append(f'{s} ^ {e}')
    return ' * '.join(fs)
def wrapall(txt):
    out=[]
    for ln in txt.split('\n'): out+=wrap(ln)
    return '\n'.join(out)
HDR='''/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
'''
