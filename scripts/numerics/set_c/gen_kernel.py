exec(open('common.py').read())
terms=pickle.load(open('terms.pkl','rb'))
ms=sorted(terms.keys(),reverse=True)
defs=[]
for m in ms:
    defs.append(f'/-- Coefficient of the monomial `{nm(m)}` of `setCJ`. -/\nnoncomputable def j{nm(m)} (x : ℝ) : ℝ :=\n  {rat_lean(terms[m])}\n')
J=' +\n    '.join(f'j{nm(m)} x' + (f' * ({monlean(m)})' if any(m) else '') for m in ms)
out='\n'.join(defs)+f'''
end SetCKernel

open SetCKernel

/-- **The set (c) integrand in `s = 1 - x`**, in the atoms
`log s, log (1 - s), log (1 + s), Li 2 s, Li 2 (-s)` (exponents in the coefficient names). -/
noncomputable def setCJ (x : ℝ) : ℝ :=
  {J}
'''
open('kernel_defs.lean','w').write(wrapall(out))
print(' '.join('j'+nm(m) for m in ms))
