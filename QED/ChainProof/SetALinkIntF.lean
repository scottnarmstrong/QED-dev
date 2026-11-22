/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetALinkIntFAmp

/-!
# The class obligations of (HA₀) for the fermion counterterm classes

Helper for the Phase 5 Stage 3a goal (HA₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setA`
(decision D-58): `classIntA_repFA`, `classIntA_repFB`, the class obligations `ClassIntA repFA 0`
and `ClassIntA repFB 0` for the two-loop representatives with the level-`0` `δ₂`, `δm`
counterterm (vertex `5`) on one or the other line of the one-loop bubble.

## Proof

`QED.ChainProof.SetALink.classIntA_of_fc`, with `fo` the loop line leaving the vertex `5`; its
hypotheses on the concrete contractions (the kinds, the closed loop, the loop number and the
decidable test `FCrit`) hold by kernel evaluation.
-/

@[expose] public section

namespace QED.ChainProof.SetALink

open QED.GradedProof.X0 QED.WickModel QED.ChainProof.Enum

theorem kF_ct : kF (fv kF 5).1 = .fermionCt := rfl

theorem kF_gauge : ∀ t, t ≠ (fv kF 5).1 → kF t = .gauge := by decide

/-! ### `FA`: the counterterm on the line `w → u` -/

/-- The loop line of `FA` leaving the counterterm vertex. -/
def foFA : FermionLine repFA :=
  ⟨fv kF 5, by decide +kernel⟩

theorem zOf_foFA : zOf repFA foFA.1 := by decide +kernel

theorem closedShape_repFA : ClosedShape repFA (zOf repFA) :=
  ⟨isZ_zOf_apply repFA, fun _ ht => not_not.mp ht, ⟨foFA.1, zOf_foFA, by decide +kernel⟩⟩

theorem fCrit_repFA : FCrit repFA foFA := by decide +kernel

/-- **The class obligation for `FA`.** -/
theorem classIntA_repFA : ClassIntA repFA 0 :=
  classIntA_of_fc repFA foFA kF_ct kF_gauge zOf_foFA closedShape_repFA loopCount_repFA
    fCrit_repFA

/-! ### `FB`: the counterterm on the line `u → w` -/

/-- The loop line of `FB` leaving the counterterm vertex. -/
def foFB : FermionLine repFB :=
  ⟨fv kF 5, by decide +kernel⟩

theorem zOf_foFB : zOf repFB foFB.1 := by decide +kernel

theorem closedShape_repFB : ClosedShape repFB (zOf repFB) :=
  ⟨isZ_zOf_apply repFB, fun _ ht => not_not.mp ht, ⟨foFB.1, zOf_foFB, by decide +kernel⟩⟩

theorem fCrit_repFB : FCrit repFB foFB := by decide +kernel

/-- **The class obligation for `FB`.** -/
theorem classIntA_repFB : ClassIntA repFB 0 :=
  classIntA_of_fc repFB foFB kF_ct kF_gauge zOf_foFB closedShape_repFB loopCount_repFB
    fCrit_repFB

end QED.ChainProof.SetALink

end
