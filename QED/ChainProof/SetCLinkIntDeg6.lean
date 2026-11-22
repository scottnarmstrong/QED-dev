/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.X0Deg6Crit
public import QED.ChainProof.SetCLinkReps
public import QED.ChainProof.SetALinkInt
public import QED.TwoLoop.CountertermInsertionBasic
public import Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
# The class obligations of (HS₀) for the one-loop classes `CD0` and `CD1`

Helper for the Phase 5 Stage 3 goal (HS₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setC`
(decision D-58): the class obligations `ClassIntA` for the four one-loop graphs `repCD0 s`,
`repCD1 s` (a level-`0` `fermionCt` vertex on an internal line of the open line and a level-`0`
`photonCt` vertex on the photon line).

## Proof

The numerator degree is `3 + 1 + 2 = 6` (three loop fermion lines, the `fermionCt` vertex, the
`photonCt` vertex), so the one-loop test `OneCrit` fails; the convergence count `4 + 6 < 14`
holds. The `fermionCt` vertex sits between two loop fermion lines `fi`, `fo` of the same loop
coefficient and external part (for `CD0`: `fi` is the chord and the side of `fo` carries
`pIn + kIn - pOut = 0`; for `CD1`: the sides of `fi` and `fo` differ by the counterterm vertex,
which carries no external momentum): a doubled line. The doubled-line test `DblCrit` holds
(kernel evaluation), and `QED.GradedProof.X0Deg6.jointEnergyFirstIntegrable_openCtDbl` gives
(T₉′) for `ε > 0`, any masses and any counterterm data.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetCLinkDeg6

open QED.WickModel QED.ChainProof.SetALink QED.ChainProof.SetCLink
open QED.ChainProof.Enum (fv)
open QED.GradedProof.X0 (edgeChord edgeSide edgeOf extPart loopCoeff)
open QED.GradedProof.X0Deg6 (DblCrit jointEnergyFirstIntegrable_openCtDbl)
open QED.TwoLoop.Enumeration (lineData loopCount_eq_card)

theorem extPart_of_chord {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (f : Line C)
    (h : edgeChord (lineData C) (edgeOf f) = true) : extPart C pOut pIn kIn f = 0 := by
  unfold extPart
  rw [h]
  rfl

theorem extPart_of_not_chord {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    {C : Contraction nf nA κ} (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (f : Line C) (h : edgeChord (lineData C) (edgeOf f) = false) :
    extPart C pOut pIn kIn f = ∑ v ∈ edgeSide (lineData C) (edgeOf f),
      externalMomentum C pOut pIn kIn v := by
  unfold extPart
  rw [h]
  rfl

/-! ### `CD0` -/

theorem isRight_CD0 : ∀ s, ((repCD0 s).1.1 (.inr (fv kCD0 0))).isRight ∧
    ((repCD0 s).1.1 (.inr (fv kCD0 1))).isRight := by
  decide +kernel

/-- The line `0 → 1` into the counterterm vertex `1`. -/
def fiCD0 (s : Fin 2) : FermionLine (repCD0 s) := ⟨fv kCD0 0, (isRight_CD0 s).1⟩

/-- The line `1 → 2` out of the counterterm vertex `1`. -/
def foCD0 (s : Fin 2) : FermionLine (repCD0 s) := ⟨fv kCD0 1, (isRight_CD0 s).2⟩

theorem data_CD0 : ∀ s, (fiCD0 s).tail = (foCD0 s).1 ∧ (fiCD0 s).1 ≠ (foCD0 s).1 ∧
    (foCD0 s).tail ≠ (foCD0 s).1 ∧
    loopCoeff (repCD0 s) (.inl (fiCD0 s)) 0 = loopCoeff (repCD0 s) (.inl (foCD0 s)) 0 ∧
    loopCoeff (repCD0 s) (.inl (foCD0 s)) 0 ≠ 0 := by
  decide +kernel

theorem chord_CD0 : ∀ s, edgeChord (lineData (repCD0 s)) (edgeOf (.inl (fiCD0 s))) = true ∧
    edgeChord (lineData (repCD0 s)) (edgeOf (.inl (foCD0 s))) = false ∧
    edgeSide (lineData (repCD0 s)) (edgeOf (.inl (foCD0 s))) = {0, 2, 3, 4} := by
  decide +kernel

theorem ext_CD0 : ∀ s v,
    ((∃ t : Wick.FermionVertex kCD0, t.1 = v ∧ (repCD0 s).1.1 (.inr t) = .inl 0) ↔ v = 3) ∧
    ((∃ a : Wick.PhotonSlot kCD0, a.1 = v ∧ (repCD0 s).1.2 (.inl 0) = .inr a) ↔ v = 2) ∧
    ((∃ t : Wick.FermionVertex kCD0, t.1 = v ∧ (repCD0 s).1.1 (.inl 0) = .inr t) ↔ v = 0) := by
  decide +kernel

theorem externalMomentum_CD0 (s : Fin 2) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (v : Fin 5) :
    externalMomentum (repCD0 s) pOut pIn kIn v =
      (if v = 3 then pIn 0 else 0) + (if v = 2 then kIn 0 else 0) -
        (if v = 0 then pOut 0 else 0) := by
  rw [QED.TwoLoop.Insertion.externalMomentum_one_one]
  simp only [(ext_CD0 s v).1, (ext_CD0 s v).2.1, (ext_CD0 s v).2.2]

theorem extPart_CD0 (s : Fin 2) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (hmom : pOut 0 = pIn 0 + kIn 0) :
    extPart (repCD0 s) pOut pIn kIn (.inl (fiCD0 s)) =
      extPart (repCD0 s) pOut pIn kIn (.inl (foCD0 s)) := by
  rw [extPart_of_chord _ _ _ _ (chord_CD0 s).1, extPart_of_not_chord _ _ _ _ (chord_CD0 s).2.1,
    (chord_CD0 s).2.2]
  simp only [Finset.sum_insert (by decide : (0 : Fin 5) ∉ ({2, 3, 4} : Finset (Fin 5))),
    Finset.sum_insert (by decide : (2 : Fin 5) ∉ ({3, 4} : Finset (Fin 5))),
    Finset.sum_insert (by decide : (3 : Fin 5) ∉ ({4} : Finset (Fin 5))), Finset.sum_singleton,
    externalMomentum_CD0]
  simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, hmom]
  abel

theorem cycle_CD0 : ∀ s x, Equiv.Perm.SameCycle (repCD0 s).1.1 x (.inl 0) := by
  decide +kernel

theorem loopCount_CD0 : ∀ s, loopCount (repCD0 s) = 1 := by
  simp only [loopCount_eq_card]
  decide +kernel

theorem dblCrit_CD0 : ∀ s, DblCrit (lineData (repCD0 s)) kCD0 := by
  decide +kernel

/-- **The class obligation for `CD0`.** -/
theorem classIntA_repCD0 (s : Fin 2) : ClassIntA (repCD0 s) 0 := by
  intro P F _ _ Φ D rep hH pOut pIn kIn hmom αOut βIn μ
  obtain ⟨hs, hfi, hfo, hc, hc0⟩ := data_CD0 s
  exact jointEnergyFirstIntegrable_openCtDbl P Φ D hH.hε (repCD0 s) (cycle_CD0 s)
    (loopCount_CD0 s) (dblCrit_CD0 s) (fiCD0 s) (foCD0 s) hs rfl hfi hfo hc hc0 pOut pIn kIn
    (extPart_CD0 s pOut pIn kIn hmom) αOut βIn μ

/-! ### `CD1` -/

theorem isRight_CD1 : ∀ s, ((repCD1 s).1.1 (.inr (fv kCD1 1))).isRight ∧
    ((repCD1 s).1.1 (.inr (fv kCD1 2))).isRight := by
  decide +kernel

/-- The line `1 → 2` into the counterterm vertex `2`. -/
def fiCD1 (s : Fin 2) : FermionLine (repCD1 s) := ⟨fv kCD1 1, (isRight_CD1 s).1⟩

/-- The line `2 → 3` out of the counterterm vertex `2`. -/
def foCD1 (s : Fin 2) : FermionLine (repCD1 s) := ⟨fv kCD1 2, (isRight_CD1 s).2⟩

theorem data_CD1 : ∀ s, (fiCD1 s).tail = (foCD1 s).1 ∧ (fiCD1 s).1 ≠ (foCD1 s).1 ∧
    (foCD1 s).tail ≠ (foCD1 s).1 ∧
    loopCoeff (repCD1 s) (.inl (fiCD1 s)) 0 = loopCoeff (repCD1 s) (.inl (foCD1 s)) 0 ∧
    loopCoeff (repCD1 s) (.inl (foCD1 s)) 0 ≠ 0 := by
  decide +kernel

theorem chord_CD1 : ∀ s, edgeChord (lineData (repCD1 s)) (edgeOf (.inl (fiCD1 s))) = false ∧
    edgeChord (lineData (repCD1 s)) (edgeOf (.inl (foCD1 s))) = false ∧
    edgeSide (lineData (repCD1 s)) (edgeOf (.inl (fiCD1 s))) = {0, 2, 3, 4} ∧
    edgeSide (lineData (repCD1 s)) (edgeOf (.inl (foCD1 s))) = {0, 3, 4} := by
  decide +kernel

theorem ext_CD1 : ∀ s,
    ((∃ t : Wick.FermionVertex kCD1, t.1 = 2 ∧ (repCD1 s).1.1 (.inr t) = .inl 0) ↔ False) ∧
    ((∃ a : Wick.PhotonSlot kCD1, a.1 = 2 ∧ (repCD1 s).1.2 (.inl 0) = .inr a) ↔ False) ∧
    ((∃ t : Wick.FermionVertex kCD1, t.1 = 2 ∧ (repCD1 s).1.1 (.inl 0) = .inr t) ↔ False) := by
  decide +kernel

theorem extPart_CD1 (s : Fin 2) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) :
    extPart (repCD1 s) pOut pIn kIn (.inl (fiCD1 s)) =
      extPart (repCD1 s) pOut pIn kIn (.inl (foCD1 s)) := by
  rw [extPart_of_not_chord _ _ _ _ (chord_CD1 s).1, extPart_of_not_chord _ _ _ _ (chord_CD1 s).2.1,
    (chord_CD1 s).2.2.1, (chord_CD1 s).2.2.2,
    Finset.sum_insert (by decide : (0 : Fin 5) ∉ ({2, 3, 4} : Finset (Fin 5))),
    Finset.sum_insert (by decide : (2 : Fin 5) ∉ ({3, 4} : Finset (Fin 5))),
    Finset.sum_insert (by decide : (0 : Fin 5) ∉ ({3, 4} : Finset (Fin 5))),
    QED.TwoLoop.Insertion.externalMomentum_one_one (C := repCD1 s) pOut pIn kIn 2]
  simp only [(ext_CD1 s).1, (ext_CD1 s).2.1, (ext_CD1 s).2.2, ite_false, sub_zero, add_zero,
    zero_add]

theorem cycle_CD1 : ∀ s x, Equiv.Perm.SameCycle (repCD1 s).1.1 x (.inl 0) := by
  decide +kernel

theorem loopCount_CD1 : ∀ s, loopCount (repCD1 s) = 1 := by
  simp only [loopCount_eq_card]
  decide +kernel

theorem dblCrit_CD1 : ∀ s, DblCrit (lineData (repCD1 s)) kCD1 := by
  decide +kernel

/-- **The class obligation for `CD1`.** -/
theorem classIntA_repCD1 (s : Fin 2) : ClassIntA (repCD1 s) 0 := by
  intro P F _ _ Φ D rep hH pOut pIn kIn _ αOut βIn μ
  obtain ⟨hs, hfi, hfo, hc, hc0⟩ := data_CD1 s
  exact jointEnergyFirstIntegrable_openCtDbl P Φ D hH.hε (repCD1 s) (cycle_CD1 s)
    (loopCount_CD1 s) (dblCrit_CD1 s) (fiCD1 s) (foCD1 s) hs rfl hfi hfo hc hc0 pOut pIn kIn
    (extPart_CD1 s pOut pIn kIn) αOut βIn μ

end QED.ChainProof.SetCLinkDeg6

end
