import sympy as sp, pickle, re
exec(open('gen1lean.py').read())
H,rho,K,pref=pickle.load(open('gen1.pkl','rb'))
mons,checks=pickle.load(open('checks.pkl','rb'))
ms=sorted(H.keys(), reverse=True)
LA=['log x','log (1 - x)','log (1 + x)','Li 2 x','Li 2 (-x)']
def monlean(m,var='x'):
    fs=[]
    for e,s in zip(m,LA):
        s=s.replace('x',var)
        if e==1: fs.append(s)
        elif e>1: fs.append(f'{s} ^ {e}')
    return ' * '.join(fs)
AN=['e0','e1','em','qP','qM']
def chain(m):
    fs=[]
    for e,s in zip(m,AN):
        if e==1: fs.append(s)
        elif e>1: fs.append(f'({s}.pow {e})')
    code=fs[0]
    for f in fs[1:]: code=f'({code}.mul {f})'
    return code
def wrap(line, maxlen=100):
    if len(line)<=maxlen: return [line]
    ind=len(line)-len(line.lstrip())
    cont=' '*(ind+4)
    out=[]; cur=line
    first=True
    while len(cur)>maxlen:
        # find last break point (space before + - * ) or after '(' ) within limit
        cut=-1
        for mt in re.finditer(r' (?=[\+\-\*] )| (?=\()',cur[:maxlen]):
            if mt.start()>len(cur)-len(cur.lstrip())+8: cut=mt.start()
        if cut==-1:
            for mt in re.finditer(r' ',cur[:maxlen]):
                if mt.start()>len(cur)-len(cur.lstrip())+8: cut=mt.start()
        out.append(cur[:cut]); cur=cont+cur[cut+1:]
    out.append(cur)
    return out
L=[]
L.append(open('w1defs.lean').read())
# rho/K/pref lemmas
rhosum=' + '.join(f'r{nm(m)} u' + (f' * {monlean(m,"u")}' if any(m) else '') for m in sorted(rho,reverse=True))
ksum=' + '.join(f'k{nm(m)} u' + (f' * {monlean(m,"u")}' if any(m) else '') for m in sorted(K,reverse=True))
rdefs=' '.join(f'r{nm(m)}' for m in rho); kdefs=' '.join(f'k{nm(m)}' for m in K)
L.append(f'''
private theorem ksDelta_aux {{u : ℝ}} (hu : u ∈ Ioo (0 : ℝ) 1) :
    1 - ksDelta u = 2 * u / (1 + u) ∧ 1 + ksDelta u = 2 / (1 + u) ∧
      1 - ksDelta u ^ 2 = 4 * u / (1 + u) ^ 2 := by
  have hp : 1 + u ≠ 0 := by linarith [hu.1]
  unfold ksDelta
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

theorem ksRhoU_eq {{u : ℝ}} (hu : u ∈ Ioo (0 : ℝ) 1) :
    ksRhoU u = {rhosum} := by
  have hp : 1 + u ≠ 0 := by linarith [hu.1]
  unfold ksRhoU ksDelta {rdefs}
  simp only [Li_two]
  field_simp
  ring

theorem setAKtU_eq {{u : ℝ}} (hu : u ∈ Ioo (0 : ℝ) 1) :
    setAKtU u = {ksum} := by
  obtain ⟨e1, e2, e3⟩ := ksDelta_aux hu
  have h0 : u ≠ 0 := hu.1.ne'
  have hp : 1 + u ≠ 0 := by linarith [hu.1]
  have hm : 1 - u ≠ 0 := by linarith [hu.2]
  unfold setAKtU
  rw [e1, e2, e3]
  unfold ksDelta {kdefs}
  field_simp
  ring

theorem setAJ_eq_atoms {{u : ℝ}} (hu : u ∈ Ioo (0 : ℝ) 1) :
    setAJ u = pref u * ({rhosum}) *
      ({ksum}) := by
  obtain ⟨e1, e2, e3⟩ := ksDelta_aux hu
  have h0 : u ≠ 0 := hu.1.ne'
  have hp : 1 + u ≠ 0 := by linarith [hu.1]
  have hpref : 2 / (1 + u) ^ 2 * (2 * ksDelta u / (1 - ksDelta u ^ 2)) = pref u := by
    rw [e3]
    unfold ksDelta pref
    field_simp
    ring
  unfold setAJ
  rw [hpref, ksRhoU_eq hu, setAKtU_eq hu]

end SetAW1

open SetAW1
''')
g1=' +\n    '.join(f'h{nm(m)} x' + (f' * ({monlean(m)})' if any(m) else '') for m in ms)
L.append(f'''/-- The rational-coefficient antiderivative `G₁`. -/
noncomputable def setAG1 (x : ℝ) : ℝ :=
  {g1}

/-- The derivative of `G₁`: `setAJ - g₃ - g₄` with `g₄ = -(8/3) Φ ψ'`. -/
noncomputable def setAg1 (u : ℝ) : ℝ :=
  setAJ u - setAg3 u + 8 / 3 * (setAPhi u * setAPsiD u)
''')
pr=[]
pr.append('theorem hasDerivAt_setAG1 {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :\n    HasDerivAt setAG1 (setAg1 u) u := by')
pr.append('  obtain ⟨h0, h1⟩ := hu\n  have hu : u ∈ Ioo (0 : ℝ) 1 := ⟨h0, h1⟩')
pr.append('  obtain ⟨di, ai, ni, li, -, gi1⟩ := PM.data_id h0 h1')
pr.append('  obtain ⟨dA, aA, nA, lA, -, gA1⟩ := PM.data_neg h0 h1')
pr.append('  obtain ⟨dB, -, nB, lB, -, -⟩ := PM.data_oneSub h0 h1')
pr.append('  have e0 := hasDerivAt_log_of di ni li\n  have e1 := hasDerivAt_log_of dB nB lB')
pr.append('  have em : HasDerivAt (fun x : ℝ => log (1 + x)) (1 / (1 + u)) u := by\n    have := ((hasDerivAt_id\' u).const_add 1).log (by linarith)\n    simpa [one_div] using this')
pr.append('  have qP := hasDerivAt_Li_two_of di ai ni li gi1\n  have qM := hasDerivAt_Li_two_of dA aA nA lA gA1')
for i,m in enumerate(ms):
    if any(m): pr.append(f'  have t{i} := (hasDerivAt_h{nm(m)} h0).mul {chain(m)}')
    else: pr.append(f'  have t{i} := hasDerivAt_h{nm(m)} h0')
code='t0'
for i in range(1,len(ms)): code=f'({code}.add t{i})'
pr.append(f'  have h := {code}')
pr.append('  refine h.congr_deriv ?_')
pr.append('  simp only [Pi.mul_apply, Pi.pow_apply, Pi.add_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]')
pr.append('  have hp : 1 + u ≠ 0 := by linarith\n  have hm : 1 - u ≠ 0 := by linarith\n  have hz : u ≠ 0 := h0.ne\'')
alldefs=' '.join([f'h{nm(m)} hd{nm(m)}' for m in ms]+[f'r{nm(m)}' for m in rho]+[f'k{nm(m)}' for m in K]+['pref'])
for j,(mo,cl,cr) in enumerate(checks):
    used=sorted(set(re.findall(r'\b(h\d{5}|hd\d{5}|r\d{5}|k\d{5}|pref)\b',cl+' '+cr)))
    pr.append(f'  have c{j} : {cl} = {cr} := by')
    if used: pr.append(f'    simp only [{", ".join(used)}]')
    pr.append('    field_simp\n    ring')
pr.append('  rw [setAg1, setAJ_eq_atoms hu]\n  unfold setAg3 setAPhi setAPsiD')
lc=' + '.join((f'{monlean(mo,"u")} * c{j}' if any(mo) else f'c{j}') for j,(mo,cl,cr) in enumerate(checks))
pr.append(f'  linear_combination {lc}')
L.append('\n'.join(pr))
body='\n'.join(L)
hdr='''/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.SetASubst
public import QED.Chain.SetAW3
public import QED.Chain.SetAW4
import QED.Polylog.AlphabetPM
import QED.Polylog.LiCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Set (a): the rational-coefficient part

Helper analysis for the sixth-order set (a) of `docs/HIGHER-LOOP-PLAN.md`. It is **not** frozen.

In the atoms `log u, log (1 - u), log (1 + u), Li 2 u, Li 2 (-u)` the set (a) integrand
`QED.Chain.setAJ` is `G₁' + g₃ + g₄`, where `g₃ = QED.Chain.setAg3`, `g₄ = -(8/3) Φ ψ'`
(`QED.Chain.setAPhi`, `QED.Chain.setAPsiD`) and `G₁ = QED.Chain.setAG1` is a combination of
the atom monomials of weight at most three with rational coefficients in `u` whose denominators
are powers of `u` and `1 + u`. The coefficients (`QED.Chain.SetAW1.h21000`, ...) are indexed by
the exponents of the five atoms.

## Main statements

* `QED.Chain.SetAW1.setAJ_eq_atoms`: `setAJ` as a product of its prefactor, `ρ⁽⁴⁾` and `K̃` in atoms.
* `QED.Chain.hasDerivAt_setAG1`: `G₁' = setAJ - g₃ + (8/3) Φ ψ'` on `(0, 1)`.
-/

@[expose] public section

open Real Set QED.Polylog

namespace QED.Chain

namespace SetAW1

'''
full=hdr+body+'\n\nend QED.Chain\n'
lines=[]
for ln in full.split('\n'): lines+=wrap(ln)
open('/home/scott/QED-dev/QED/Chain/SetAW1.lean','w').write('\n'.join(lines))
print(len(lines))
