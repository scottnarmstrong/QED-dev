import sympy as sp, pickle
u=sp.symbols('u',positive=True)
H,rho,K,pref=pickle.load(open('gen1.pkl','rb'))
def nm(m): return ''.join(map(str,m))
def frac_parts(e):
    e=sp.factor(sp.together(e))
    n,d=sp.fraction(e)
    c,fl=sp.factor_list(d)
    a=b=0; extra=1
    for f,k in fl:
        if f==u: a=k
        elif sp.expand(f-(u+1))==0: b=k
        elif sp.expand(f-(u-1))==0:
            extra*= f**k
        else: raise Exception(f)
    # handle (u-1) in den: write as (1-u)
    s=1
    m1=0
    if extra!=1:
        m1=sp.degree(extra,u);
        if m1%2==1: s=-1
    n=sp.expand(n*s)
    if c<0: c=-c; n=-n
    return sp.Poly(n,u), c, a, b, m1
def lnum(q):
    s=str(q)
    return s
def poly_lean(P, var='x'):
    terms=[]
    for (k,),c in sorted(P.terms(), key=lambda t:t[0][0]):
        terms.append((k,c))
    out=''
    for i,(k,c) in enumerate(terms):
        ac=abs(c); sg='-' if c<0 else '+'
        base = (f'{ac}' if k==0 else (f'{ac} * {var}' if k==1 else f'{ac} * {var} ^ {k}'))
        if k>0 and ac==1: base = var if k==1 else f'{var} ^ {k}'
        if i==0: out = ('-' if c<0 else '') + (f'({base})' if c<0 and k>0 else base) if c>=0 else f'-{base}' if k==0 else f'-({base})'
        else: out += f' {sg} {base}'
    return out
def den_lean(c,a,b,m1,var='x'):
    parts=[]
    if c!=1: parts.append(str(c))
    if a: parts.append(var if a==1 else f'{var} ^ {a}')
    if b: parts.append(f'(1 + {var})' if b==1 else f'(1 + {var}) ^ {b}')
    if m1: parts.append(f'(1 - {var})' if m1==1 else f'(1 - {var}) ^ {m1}')
    return ' * '.join(parts) if parts else '1'
def rat_lean(e,var='x'):
    P,c,a,b,m1=frac_parts(e)
    num=poly_lean(P,var); den=den_lean(c,a,b,m1,var)
    if den=='1': return f'({num})'
    return f'({num}) / ({den})'
def poly_deriv_code(P, var='u'):
    # combinator chain for numerator polynomial, mirroring poly_lean
    terms=sorted(P.terms(), key=lambda t:t[0][0])
    code=None
    for i,((k,),c) in enumerate(terms):
        ac=abs(c)
        if k==0: t=f'(hasDerivAt_const {var} ({ac} : ℝ))'
        elif k==1: t=f'(hasDerivAt_id\' {var})' if ac==1 else f'((hasDerivAt_id\' {var}).const_mul ({ac} : ℝ))'
        else: t=f'(hasDerivAt_pow {k} {var})' if ac==1 else f'((hasDerivAt_pow {k} {var}).const_mul ({ac} : ℝ))'
        if i==0:
            code = t if c>0 else f'{t}.neg'
        else:
            code = f'({code}.{"add" if c>0 else "sub"} {t})'
    return code
def den_deriv_code(c,a,b,var='u'):
    pa = None
    if a: pa = f"(hasDerivAt_id' {var})" if a==1 else f'(hasDerivAt_pow {a} {var})'
    pb = None
    if b: pb = f"((hasDerivAt_id' {var}).const_add 1)" if b==1 else f"(((hasDerivAt_id' {var}).const_add 1).pow {b})"
    first = pa if pa else pb
    if c!=1: first=f'({first}.const_mul ({c} : ℝ))'
    if pa and pb: return f'({first}.mul {pb})'
    return first
out=[]
ms=sorted(H.keys(), reverse=True)
out.append('/-! ### Rational coefficients -/\n')
for m in ms:
    out.append(f'/-- Coefficient of the monomial `{nm(m)}` in `G₁`. -/')
    out.append(f'noncomputable def h{nm(m)} (x : ℝ) : ℝ :=\n  {rat_lean(H[m])}\n')
    out.append(f'/-- Derivative of `h{nm(m)}`. -/')
    out.append(f'noncomputable def hd{nm(m)} (x : ℝ) : ℝ :=\n  {rat_lean(sp.diff(H[m],u))}\n')
for m in sorted(rho, reverse=True):
    out.append(f'/-- Coefficient of `{nm(m)}` in `ρ⁽⁴⁾((1-u)/(1+u))`. -/')
    out.append(f'noncomputable def r{nm(m)} (x : ℝ) : ℝ :=\n  {rat_lean(rho[m])}\n')
for m in sorted(K, reverse=True):
    out.append(f'/-- Coefficient of `{nm(m)}` in `K̃((1-u)/(1+u))`. -/')
    out.append(f'noncomputable def k{nm(m)} (x : ℝ) : ℝ :=\n  {rat_lean(K[m])}\n')
out.append(f'/-- The prefactor of `setAJ`. -/')
out.append(f'noncomputable def pref (x : ℝ) : ℝ :=\n  {rat_lean(pref)}\n')
# derivative lemmas
for m in ms:
    P,c,a,b,m1=frac_parts(H[m])
    assert m1==0
    nc=poly_deriv_code(P)
    if a==0 and b==0 and c==1:
        code=nc
        out.append(f'theorem hasDerivAt_h{nm(m)} {{u : ℝ}} (h0 : 0 < u) :\n    HasDerivAt h{nm(m)} (hd{nm(m)} u) u := by\n  have h := {code}\n  refine h.congr_deriv ?_\n  unfold hd{nm(m)}\n  push_cast\n  field_simp\n  ring\n')
    else:
        dc=den_deriv_code(c,a,b)
        out.append(f'theorem hasDerivAt_h{nm(m)} {{u : ℝ}} (h0 : 0 < u) :\n    HasDerivAt h{nm(m)} (hd{nm(m)} u) u := by\n  have h := {nc}.div\n    {dc}\n    (by simp only [Pi.pow_apply, Pi.mul_apply]; positivity)\n  refine h.congr_deriv ?_\n  unfold hd{nm(m)}\n  simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]\n  push_cast\n  field_simp\n  ring\n')
open('w1defs.lean','w').write('\n'.join(out))
pickle.dump(ms,open('ms.pkl','wb'))
