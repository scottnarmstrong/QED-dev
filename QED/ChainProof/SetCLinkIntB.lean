/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkIntBCrit0
public import QED.ChainProof.SetCLinkIntBCrit1
public import QED.ChainProof.SetCLinkIntRem

/-!
# Set (c), family `B`: the class obligations

Helper for the Phase 5 Stage 3 goal (HS₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setC`
(decision D-58). `QED.ChainProof.SetCLink.repB i`, `i : Fin 12`, is a two-loop vertex skeleton
with a bubble on one photon line: three loops, seven `gauge` vertices, grading `0`, the closed
fermion loop being the bubble. **`classIntA_repB`**: the class obligations
`QED.ChainProof.SetALink.ClassIntA (repB i) 0` of all twelve orbits, by
`QED.ChainProof.SetALinkV.jef_nsClosed3` (`QED/ChainProof/SetALinkIntVTerm.lean`), at any masses.
`RemainingC.ofB` builds `RemainingC` from its fields other than `hB`.

The kernel checks, for all twelve orbits at once: the loop count, the closed-loop shape, at
most four loop lines (the bubble has two), every line off the bubble carrying loop momentum on
`ℓ₀` or `ℓ₁`, the rows of the lines up to sign (`rowsB i`, five classes, `clsB i`) and the
pattern criterion `AllPatOK3`; the basis criterion for the minimal exponent vectors `esB i`
is checked per orbit (`QED/ChainProof/SetCLinkIntBCrit0.lean`,
`QED/ChainProof/SetCLinkIntBCrit1.lean`).
-/

@[expose] public section

namespace QED.ChainProof.SetCLink

open QED.WickModel QED.GradedProof.X0 QED.ChainProof.SetALink QED.ChainProof.SetALinkV

theorem loopCount_repB (i : Fin 12) : loopCount (repB i) = 3 := by
  rw [QED.TwoLoop.Enumeration.loopCount_eq_card]
  revert i
  decide +kernel

theorem shapeOK_repB : ∀ i, ShapeOK (repB i) (zOf (repB i)) := by decide +kernel

theorem card_zSet_repB : ∀ i, (zSet (repB i)).card ≤ 4 := by decide +kernel

theorem isTree_repB : ∀ i l, isZL (repB i) l = false → isTree (repB i) l = false := by
  decide +kernel

theorem row3_repB : ∀ i l, row3 (repB i) l = rowsB i (clsB i l) ∨
    row3 (repB i) l = -rowsB i (clsB i l) := by
  decide +kernel

theorem allPatOK3_repB : ∀ i, AllPatOK3 (repB i) (clsB i) (esB i) := by decide +kernel

theorem basisCrit_esB (i : Fin 12) : ∀ E ∈ esB i, BasisCrit (rowsB i) E 5 := by
  fin_cases i
  exacts [basisCrit_esB0, basisCrit_esB1, basisCrit_esB2, basisCrit_esB3, basisCrit_esB4,
    basisCrit_esB5, basisCrit_esB6, basisCrit_esB7, basisCrit_esB8, basisCrit_esB9,
    basisCrit_esB10, basisCrit_esB11]

/-- **The class obligations of the family `B`** (twelve orbits). -/
theorem classIntA_repB (i : Fin 12) : ClassIntA (repB i) 0 := by
  intro P F _ _ Φ D rep hH pOut pIn kIn _ αOut βIn μ
  obtain ⟨s1, s2, s3⟩ := shapeOK_repB i
  have hC : ClosedShape (repB i) (zOf (repB i)) := ⟨s1, fun t ht => s2 t ht not_false, s3⟩
  exact jef_nsClosed3 P Φ D rep hH.hrep hH.hPV₁ hH.hPV₂ hH.hε (fun _ => rfl) (repB i)
    (loopCount_repB i) hC (card_zSet_repB i) (isTree_repB i) (clsB i) (esB i) (rowsB i)
    (row3_repB i) (basisCrit_esB i) (allPatOK3_repB i) pOut pIn kIn αOut βIn μ

/-- `RemainingC` from its fields other than the family `B`. -/
theorem RemainingC.ofB (hD : ∀ i s, ClassIntA (repD i s) 0) (hCB0 : ClassIntA repCB0 0)
    (hCB1 : ClassIntA repCB1 0) (hCD0 : ∀ s, ClassIntA (repCD0 s) 0)
    (hCD1 : ∀ s, ClassIntA (repCD1 s) 0) : RemainingC :=
  ⟨classIntA_repB, hD, hCB0, hCB1, hCD0, hCD1⟩

end QED.ChainProof.SetCLink

end
