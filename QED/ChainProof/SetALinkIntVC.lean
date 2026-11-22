/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetALinkIntVTerm
public import QED.ChainProof.SetALinkInt

/-!
# The class obligation of `repVC`

Helper for the Phase 5 Stage 3a goal (HA₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setA`
(decision D-58). `QED.ChainProof.SetALink.repVC` is the two-loop bubble with a self-energy on the
other line, loop `[3, 5, 6, 4]`:
three loops, seven `gauge` vertices, grading `0`. **`classIntA_repVC`**: its class obligation
`QED.ChainProof.SetALink.ClassIntA repVC 0`, by `jef_nsClosed3`
(`QED/ChainProof/SetALinkIntVTerm.lean`), at any masses.

The kernel checks: the closed-loop shape, at most four loop lines, every line off the loop
carrying loop momentum on `ℓ₀` or `ℓ₁`, the rows of the lines up to sign (`rowsVC`, 5
classes, `clsVC`), the basis criterion for each of the 15 minimal exponent vectors
(`esVC`) and the pattern criterion `AllPatOK3`.
-/

@[expose] public section

namespace QED.ChainProof.SetALinkV

open QED.WickModel QED.GradedProof.X0 QED.ChainProof.SetALink

/-- The rows of the line classes of `repVC`. -/
def rowsVC : Fin 5 → Fin 3 → ℤ :=
  ![![1, 0, 0], ![0, 1, 0], ![1, 1, 0], ![0, 0, 1], ![0, -1, 1]]

/-- The class of a line of `repVC`. -/
def clsVC (l : Line repVC) : Fin 5 := clsOf rowsVC (row3 repVC l)

/-- Minimal exponent vectors of `repVC`, part 0. -/
def esVC0 : List (Fin 5 → ℕ) :=
  [![10, 2, 1, 5, 4],
  ![10, 2, 2, 4, 4],
  ![10, 2, 3, 3, 4],
  ![10, 2, 4, 2, 4],
  ![10, 2, 5, 1, 4]]

theorem critB_esVC0 : (esVC0.all fun E => critB rowsVC E 5) = true := by
  decide +kernel

/-- Minimal exponent vectors of `repVC`, part 1. -/
def esVC1 : List (Fin 5 → ℕ) :=
  [![10, 3, 1, 4, 4],
  ![10, 3, 2, 3, 4],
  ![10, 3, 3, 2, 4],
  ![10, 3, 4, 1, 4],
  ![10, 4, 1, 3, 4]]

theorem critB_esVC1 : (esVC1.all fun E => critB rowsVC E 5) = true := by
  decide +kernel

/-- Minimal exponent vectors of `repVC`, part 2. -/
def esVC2 : List (Fin 5 → ℕ) :=
  [![10, 4, 2, 2, 4],
  ![10, 4, 3, 1, 4],
  ![10, 5, 1, 2, 4],
  ![10, 5, 2, 1, 4],
  ![10, 6, 1, 1, 4]]

theorem critB_esVC2 : (esVC2.all fun E => critB rowsVC E 5) = true := by
  decide +kernel

/-- The minimal exponent vectors of `repVC`. -/
def esVC : List (Fin 5 → ℕ) := esVC0 ++ esVC1 ++ esVC2

theorem basisCrit_esVC : ∀ E ∈ esVC, BasisCrit rowsVC E 5 := by
  have h : (esVC.all fun E => critB rowsVC E 5) = true := by
    simp only [esVC, List.all_append, critB_esVC0, critB_esVC1, critB_esVC2, Bool.and_self]
  intro E hE
  exact basisCrit_of_critB (List.all_eq_true.mp h E hE)

theorem shapeOK_repVC : ShapeOK repVC (zOf repVC) := by decide +kernel

theorem card_zSet_repVC : (zSet repVC).card ≤ 4 := by decide +kernel

theorem isTree_repVC : ∀ l, isZL repVC l = false → isTree repVC l = false := by
  decide +kernel

theorem row3_repVC : ∀ l, row3 repVC l = rowsVC (clsVC l) ∨
    row3 repVC l = -rowsVC (clsVC l) := by
  decide +kernel

theorem allPatOK3_repVC : AllPatOK3 repVC clsVC esVC := by decide +kernel

/-- **The class obligation of `repVC`.** -/
theorem classIntA_repVC : ClassIntA repVC 0 := by
  intro P F _ _ Φ D rep hH pOut pIn kIn _ αOut βIn μ
  obtain ⟨s1, s2, s3⟩ := shapeOK_repVC
  have hC : ClosedShape repVC (zOf repVC) := ⟨s1, fun t ht => s2 t ht not_false, s3⟩
  exact jef_nsClosed3 P Φ D rep hH.hrep hH.hPV₁ hH.hPV₂ hH.hε (fun _ => rfl) repVC
    loopCount_repVC hC card_zSet_repVC
    isTree_repVC clsVC esVC rowsVC row3_repVC basisCrit_esVC
    allPatOK3_repVC pOut pIn kIn αOut βIn μ

end QED.ChainProof.SetALinkV

end
