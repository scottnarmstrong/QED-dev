#!/usr/bin/env python3
"""Generator of the per-class sections of QED/TwoLoop/LimitMirrorClasses.lean (provenance only;
the Lean file is checked by the kernel, not by this script).

Run: python3 scripts/numerics/two_loop_limit_mirror_gen.py OUTFILE
"""
import sys
def section(N, c, cp, C, Cp, line, linep, phot, photp, extA, extAp, photPerm, photMap, photFacts, photFactsP, title):
    # N: suffix, c/cp: Class5 constructor names, C/Cp: abbrevs, photMap: (j0, j1) images of phot 0, phot 1
    j0, j1 = photMap
    (a0, h0, a1, h1) = photFacts
    (b0, k0, b1, k1) = photFactsP
    same = (C == Cp)
    s = f'''
/-! ### {title} -/

section {N}

theorem inl_{N} (i : Fin 1) (t : FV) : {C}.1.1 (.inl i) = .inr t ↔ t = fv5 4 := by
  revert i t
  decide +kernel

theorem inr_inl_{N} (t : FV) (i : Fin 1) : {C}.1.1 (.inr t) = .inl i ↔ t = fv5 0 := by
  revert t i
  decide +kernel

theorem ph_{N} (j : Fin 1) (a : PS) : {C}.1.2 (.inl j) = .inr a ↔ a = ps5 {extA} := by
  revert j a
  decide +kernel

theorem tail_{line} : ({line} 0).tail = fv5 0 ∧ ({line} 1).tail = fv5 1 ∧
    ({line} 2).tail = fv5 2 ∧ ({line} 3).tail = fv5 3 := by decide +kernel

theorem val_{line} : ({line} 0).1 = fv5 1 ∧ ({line} 1).1 = fv5 2 ∧ ({line} 2).1 = fv5 3 ∧
    ({line} 3).1 = fv5 4 := ⟨rfl, rfl, rfl, rfl⟩

theorem facts_{phot} : ({phot} 0).1 = ps5 {a0} ∧ ({phot} 0).head = ps5 {h0} ∧
    ({phot} 1).1 = ps5 {a1} ∧ ({phot} 1).head = ps5 {h1} := by decide +kernel
'''
    if not same:
        s += f'''
theorem inl_{N}' (i : Fin 1) (t : FV) : {Cp}.1.1 (.inl i) = .inr t ↔ t = fv5 4 := by
  revert i t
  decide +kernel

theorem inr_inl_{N}' (t : FV) (i : Fin 1) : {Cp}.1.1 (.inr t) = .inl i ↔ t = fv5 0 := by
  revert t i
  decide +kernel

theorem ph_{N}' (j : Fin 1) (a : PS) : {Cp}.1.2 (.inl j) = .inr a ↔ a = ps5 {extAp} := by
  revert j a
  decide +kernel

theorem tail_{linep} : ({linep} 0).tail = fv5 0 ∧ ({linep} 1).tail = fv5 1 ∧
    ({linep} 2).tail = fv5 2 ∧ ({linep} 3).tail = fv5 3 := by decide +kernel

theorem val_{linep} : ({linep} 0).1 = fv5 1 ∧ ({linep} 1).1 = fv5 2 ∧ ({linep} 2).1 = fv5 3 ∧
    ({linep} 3).1 = fv5 4 := ⟨rfl, rfl, rfl, rfl⟩

theorem facts_{photp} : ({photp} 0).1 = ps5 {b0} ∧ ({photp} 0).head = ps5 {k0} ∧
    ({photp} 1).1 = ps5 {b1} ∧ ({photp} 1).head = ps5 {k1} := by decide +kernel
'''
    if same:
        inlist = f"inl_{N}, inr_inl_{N}, ph_{N}"
        obtainM = ""
        prodlist = f"prod_fermionLine_{N0(C)}, prod_photonLine_{N0(C)}"
        mlist = ""
    else:
        inlist = f"inl_{N}, inl_{N}', inr_inl_{N}, inr_inl_{N}', ph_{N}, ph_{N}'"
        obtainM = f"""
  obtain ⟨tM0, tM1, tM2, tM3⟩ := tail_{linep}
  obtain ⟨vM0, vM1, vM2, vM3⟩ := val_{linep}
  obtain ⟨gM0, gM0', gM1, gM1'⟩ := facts_{photp}"""
        prodlist = f"prod_fermionLine_{N0(C)}, prod_fermionLine_{N0(Cp)}, prod_photonLine_{N0(C)},\n      prod_photonLine_{N0(Cp)}"
        mlist = "\n      tM0, tM1, tM2, tM3, vM0, vM1, vM2, vM3, gM0, gM0', gM1, gM1',"
    inlp = f"inl_{N}'" if not same else f"inl_{N}"
    inrp = f"inr_inl_{N}'" if not same else f"inr_inl_{N}"
    php = f"ph_{N}'" if not same else f"ph_{N}"
    s += f'''
def fermEquiv{N} : FermionLine {C} ≃ FermionLine {Cp} :=
  Equiv.subtypeEquiv (fvPerm headPermC) (by decide +kernel)

def photEquiv{N} : PhotonLine {C} ≃ PhotonLine {Cp} :=
  Equiv.subtypeEquiv (psPerm ({photPerm})) (by decide +kernel)

theorem ends_corr{N} : ∀ f : Line {C},
    Line.ends (Equiv.sumCongr fermEquiv{N} photEquiv{N} f : Line {Cp}) =
      (revV f.ends.2, revV f.ends.1) := by
  decide +kernel

/-- The line correspondence of the reversed open line: vertices `v ↦ 4 - v`, every line reversed. -/
def corr{N} : LineCorr {C} {Cp} where
  vtx := revV
  line := Equiv.sumCongr fermEquiv{N} photEquiv{N}
  rev := fun _ => true
  ends_line f := by
    simp only [ite_true]
    exact ends_corr{N} f

theorem line_corr{N} : fermEquiv{N} ({line} 0) = {linep} 3 ∧ fermEquiv{N} ({line} 1) = {linep} 2 ∧
    fermEquiv{N} ({line} 2) = {linep} 1 ∧ fermEquiv{N} ({line} 3) = {linep} 0 ∧
    photEquiv{N} ({phot} 0) = {photp} {j0} ∧ photEquiv{N} ({phot} 1) = {photp} {j1} := by decide +kernel

theorem pull_corr{N} (k' : Line {Cp} → Fin 4 → ℝ) :
    corr{N}.pull k' (.inl ({line} 0)) = -k' (.inl ({linep} 3)) ∧
      corr{N}.pull k' (.inl ({line} 1)) = -k' (.inl ({linep} 2)) ∧
      corr{N}.pull k' (.inl ({line} 2)) = -k' (.inl ({linep} 1)) ∧
      corr{N}.pull k' (.inl ({line} 3)) = -k' (.inl ({linep} 0)) ∧
      corr{N}.pull k' (.inr ({phot} 0)) = -k' (.inr ({photp} {j0})) ∧
      corr{N}.pull k' (.inr ({phot} 1)) = -k' (.inr ({photp} {j1})) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := line_corr{N}
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [LineCorr.pull, corr{N}, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, h0, h1,
      h2, h3, h4, h5, ite_true]

theorem iff_indicator_{N} (α β : FV → Fin 4) (lor : PS → Fin 4) (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, {Cp}.1.1 (.inl i) = .inr t → (swapC (α, β)).1 t = ccIdx (βIn i)) ∧
        (∀ t i, {Cp}.1.1 (.inr t) = .inl i → (swapC (α, β)).2 t = ccIdx (αOut i)) ∧
        (∀ j a, {Cp}.1.2 (.inl j) = .inr a → lorC lor a = μ j)) ↔
      ((∀ i t, {C}.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, {C}.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, {C}.1.2 (.inl j) = .inr a → lor a = μ j)) := by
  simp only [{inlist}, Fin.forall_fin_one,
    forall_eq]
  simp only [ps5, lorC_ps]
  simp only [swapC, fvPerm_revV, fv5, rev5, ccIdx_injective.eq_iff]
  exact ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1, h.2.2⟩⟩

open scoped Classical in
/-- **Charge conjugation of the amplitude** (T₇) along the reversed open line. -/
theorem contractionAmplitude₂_cc_{N} (P : Params) (pIn kIn pIn' kIn' : Fin 1 → Fin 4 → ℝ)
    (k' : Line {Cp} → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P {Cp} zeroFlavoring pIn' kIn' k' (fun i => ccIdx (βIn i))
        (fun i => ccIdx (αOut i)) μ =
      -(ccSign (αOut 0) * ccSign (βIn 0)) *
        contractionAmplitude₂ P {C} zeroFlavoring pIn kIn (corr{N}.pull k') αOut βIn μ := by
  obtain ⟨tP0, tP1, tP2, tP3⟩ := tail_{line}
  obtain ⟨vP0, vP1, vP2, vP3⟩ := val_{line}
  obtain ⟨gP0, gP0', gP1, gP1'⟩ := facts_{phot}{obtainM}
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := pull_corr{N} k'
  unfold contractionAmplitude₂
  refine sum_reindexC _ _ _ fun α β lor => ?_
  beta_reduce
  conv_rhs => rw [mul_left_comm]
  have hiff := iff_indicator_{N} α β lor αOut βIn μ
  split_ifs with h1 h2 h2
  · have ha : α ⟨4, fun h => Wick.VertexKind.noConfusion h⟩ = αOut 0 := by
      simpa [fv5] using h2.1 0 _ ((inl_{N} 0 _).mpr rfl)
    have hb : β ⟨0, fun h => Wick.VertexKind.noConfusion h⟩ = βIn 0 := by
      simpa [fv5] using h2.2.1 _ 0 ((inr_inl_{N} _ 0).mpr rfl)
    rw [one_mul, one_mul]
    simp only [Relabel.vertexFactor_gauges, Fin.prod_univ_five,
      {prodlist},
      tP0, tP1, tP2, tP3, vP0, vP1, vP2, vP3, gP0, gP0', gP1, gP1',{mlist}
      p0, p1, p2, p3, p4, p5]
    obtain ⟨l0, l1, l2, l3, l4⟩ := lorC_ps lor
    simp only [ps5, l0, l1, l2, l3, l4]
    simp only [swapC, fvPerm_revV, fv5, rev5, zeroFlavoring]
    rw [gamma_ccIdx, gamma_ccIdx, gamma_ccIdx, gamma_ccIdx, gamma_ccIdx,
      QED.OneLoop.electronPropagator_ccIdx, QED.OneLoop.electronPropagator_ccIdx,
      QED.OneLoop.electronPropagator_ccIdx, QED.OneLoop.electronPropagator_ccIdx,
      ← photonPropagator_neg_swap _ _ _ (k' (.inr ({photp} 0))),
      ← photonPropagator_neg_swap _ _ _ (k' (.inr ({photp} 1))), ← ha, ← hb]
    ring_nf
    simp only [ccSign_sq]
    ring
  · exact absurd (hiff.mp h1) h2
  · exact absurd (hiff.mpr h2) h1
  · simp

theorem externalMomentum_cc_{N} (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (v : Fin 5) :
    externalMomentum {Cp} (fun i => -pIn i) (fun i => -pOut i) kIn (corr{N}.vtx v) =
      externalMomentum {C} pOut pIn kIn v := by
  change externalMomentum {Cp} _ _ _ (Fin.rev v) = _
  rw [externalMomentum_{Cp}, externalMomentum_{C}]
  fin_cases v <;> simp

open scoped Classical in
/-- **Charge conjugation of the values** (T₁₀) along the reversed open line. -/
theorem contractionValue₂_cc_{N} (P : Params) {{pOut pIn kIn : Fin 1 → Fin 4 → ℝ}}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P Class5.{cp}.rep (fun i => -pIn i) (fun i => -pOut i) kIn
        (fun i => ccIdx (βIn i)) (fun i => ccIdx (αOut i)) μ =
      -(ccSign (αOut 0) * ccSign (βIn 0)) *
        contractionValue₂ P Class5.{c}.rep pOut pIn kIn αOut βIn μ := by
  have hP := rep_isOnePI .{c}
  have hM := rep_isOnePI .{cp}
  have hsum : ∑ v, externalMomentum {C} pOut pIn kIn v = 0 := by
    rw [sum_externalMomentum hP.1]
    simp only [Fin.sum_univ_one, hmom, sub_self]
  obtain ⟨M, hMdet, a, h⟩ := exists_routing_change_of_ext corr{N} hP.2.1 hM.2.1
    (externalMomentum_cc_{N} pOut pIn kIn) hsum (loopCount_rep .{c}) (loopCount_rep .{cp})
  rw [contractionValue₂_eq_of_loopCount P (loopCount_rep .{cp}),
    contractionValue₂_eq_of_loopCount P (loopCount_rep .{c})]
  have e : (fun ℓ : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P {Cp} (fun i => -pOut i) kIn
        (lineMomentum₂ {Cp} (fun i => -pIn i) (fun i => -pOut i) kIn ℓ)
        (fun i => ccIdx (βIn i)) (fun i => ccIdx (αOut i)) μ) =
      fun ℓ => -(ccSign (αOut 0) * ccSign (βIn 0)) *
        ((fun ℓ' : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
          regulatedAmplitude₂ P {C} pIn kIn (lineMomentum₂ {C} pOut pIn kIn ℓ') αOut βIn μ)
          ((fun s => ∑ r, M s r • ℓ r) + a)) := by
    funext ℓ
    beta_reduce
    rw [regulatedAmplitude₂_{Cp}, regulatedAmplitude₂_{C},
      contractionAmplitude₂_cc_{N} P pIn kIn (fun i => -pOut i) kIn, h]
    exact mul_left_comm _ _ _
  rw [e, jointEnergyFirstIntegral_const_mul]
  exact congrArg _
    (JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add 2
      (fun ℓ' : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P {C} pIn kIn (lineMomentum₂ {C} pOut pIn kIn ℓ') αOut βIn μ) M hMdet a)

end {N}
'''
    return s
def N0(C): return C[1:]
import builtins
builtins.N0 = N0
header = '''/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.LimitMirror
public import QED.TwoLoop.ParametricBridgeS

/-!
# Charge conjugation of the classes `L`, `X`, `S₊`, `S₋`

Part of obligation O2-21 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4), continuing
`QED/TwoLoop/LimitMirror.lean`. Relabelling the vertices by `v ↦ 4 - v`, the reversed open line of

* `L` (external photon at `2`, internal photons `(0 4)`, `(1 3)`) is the line of `L`;
* `X` (external photon at `2`, internal photons `(0 3)`, `(1 4)`) is the line of `X`;
* `S₊` (external photon at `1`, internal photons `(0 4)`, `(2 3)`) is the line of `S₋` (external
  photon at `3`, internal photons `(0 4)`, `(1 2)`),

with all six internal lines reversed. As for `C₊ ↔ C₋`
(`QED.TwoLoop.LimitMirror.contractionValue₂_Cm_cc`), the value (T₁₀) of the image class with the
charge-conjugate external data `(-p_in, -p_out, k)` and spinor indices `(p(b), p(a))` is
`-s(a) s(b)` times the value of the original class with `(p_out, p_in, k)` and `(a, b)`, at every
parameter set (`contractionValue₂_cc_L`, `contractionValue₂_cc_X`, `contractionValue₂_cc_S`).
-/

@[expose] public section

namespace QED.TwoLoop.LimitMirror

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Relabel QED.TwoLoop.Routing QED.Dirac
  QED.TwoLoop.Bridge Complex

/-- The fermion fields of the five gauge vertices. -/
local notation "FV" => Wick.FermionVertex (gauges 5)

/-- The photon fields of the five gauge vertices. -/
local notation "PS" => Wick.PhotonSlot (gauges 5)
'''
body = header
body += section("L", "L", "L", "cL", "cL", "lineL", "lineL", "photL", "photL", 2, 2, "1", (0,1), (0,4,1,3), (0,4,1,3), "The ladder `L` is self-conjugate")
body += section("X", "X", "X", "cX", "cX", "lineX", "lineX", "photX", "photX", 2, 2, "Equiv.swap 0 1", (1,0), (0,3,1,4), (0,3,1,4), "The crossed ladder `X` is self-conjugate")
body += section("S", "Sp", "Sm", "cSp", "cSm", "lineSp", "lineSm", "photSp", "photSm", 1, 3, "Equiv.swap 1 2", (0,1), (0,4,2,3), (0,4,1,2), "`S₊ ↔ S₋`")
body += '''
end QED.TwoLoop.LimitMirror

end
'''
open(sys.argv[1],'w').write(body)
