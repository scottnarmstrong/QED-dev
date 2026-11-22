/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetALinkIntVTerm
public import QED.ChainProof.SetALinkInt

/-!
# The class obligation of `repVA`

Helper for the Phase 5 Stage 3a goal (HA₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setA`
(decision D-58). `QED.ChainProof.SetALink.repVA` is the two-loop bubble with a self-energy on one
line, loop `[3, 4, 5, 6]`: three loops, seven `gauge` vertices, grading `0`.
**`classIntA_repVA`**: its class obligation `QED.ChainProof.SetALink.ClassIntA repVA 0`, by
`jef_nsClosed3` (`QED/ChainProof/SetALinkIntVTerm.lean`), at any masses.

The kernel checks: the closed-loop shape, at most four loop lines, every line off the loop
carrying loop momentum on `ℓ₀` or `ℓ₁`, the rows of the lines up to sign (`rowsVA`, 5
classes, `clsVA`), the basis criterion for each of the 15 minimal exponent vectors
(`esVA`) and the pattern criterion `AllPatOK3`.
-/

@[expose] public section

namespace QED.ChainProof.SetALinkV

open QED.WickModel QED.GradedProof.X0 QED.ChainProof.SetALink

/-- The rows of the line classes of `repVA`. -/
def rowsVA : Fin 5 → Fin 3 → ℤ :=
  ![![1, 0, 0], ![0, 1, 0], ![1, 1, 0], ![0, 0, 1], ![-1, -1, 1]]

/-- The class of a line of `repVA`. -/
def clsVA (l : Line repVA) : Fin 5 := clsOf rowsVA (row3 repVA l)

/-- Minimal exponent vectors of `repVA`, part 0. -/
def esVA0 : List (Fin 5 → ℕ) :=
  [![10, 1, 2, 5, 4],
  ![10, 1, 3, 4, 4],
  ![10, 1, 4, 3, 4],
  ![10, 1, 5, 2, 4],
  ![10, 1, 6, 1, 4]]

theorem critB_esVA0 : (esVA0.all fun E => critB rowsVA E 5) = true := by
  decide +kernel

/-- Minimal exponent vectors of `repVA`, part 1. -/
def esVA1 : List (Fin 5 → ℕ) :=
  [![10, 2, 2, 4, 4],
  ![10, 2, 3, 3, 4],
  ![10, 2, 4, 2, 4],
  ![10, 2, 5, 1, 4],
  ![10, 3, 2, 3, 4]]

theorem critB_esVA1 : (esVA1.all fun E => critB rowsVA E 5) = true := by
  decide +kernel

/-- Minimal exponent vectors of `repVA`, part 2. -/
def esVA2 : List (Fin 5 → ℕ) :=
  [![10, 3, 3, 2, 4],
  ![10, 3, 4, 1, 4],
  ![10, 4, 2, 2, 4],
  ![10, 4, 3, 1, 4],
  ![10, 5, 2, 1, 4]]

theorem critB_esVA2 : (esVA2.all fun E => critB rowsVA E 5) = true := by
  decide +kernel

/-- The minimal exponent vectors of `repVA`. -/
def esVA : List (Fin 5 → ℕ) := esVA0 ++ esVA1 ++ esVA2

theorem basisCrit_esVA : ∀ E ∈ esVA, BasisCrit rowsVA E 5 := by
  have h : (esVA.all fun E => critB rowsVA E 5) = true := by
    simp only [esVA, List.all_append, critB_esVA0, critB_esVA1, critB_esVA2, Bool.and_self]
  intro E hE
  exact basisCrit_of_critB (List.all_eq_true.mp h E hE)

theorem shapeOK_repVA : ShapeOK repVA (zOf repVA) := by decide +kernel

theorem card_zSet_repVA : (zSet repVA).card ≤ 4 := by decide +kernel

theorem isTree_repVA : ∀ l, isZL repVA l = false → isTree repVA l = false := by
  decide +kernel

theorem row3_repVA : ∀ l, row3 repVA l = rowsVA (clsVA l) ∨
    row3 repVA l = -rowsVA (clsVA l) := by
  decide +kernel

theorem allPatOK3_repVA : AllPatOK3 repVA clsVA esVA := by decide +kernel

/-- **The class obligation of `repVA`.** -/
theorem classIntA_repVA : ClassIntA repVA 0 := by
  intro P F _ _ Φ D rep hH pOut pIn kIn _ αOut βIn μ
  obtain ⟨s1, s2, s3⟩ := shapeOK_repVA
  have hC : ClosedShape repVA (zOf repVA) := ⟨s1, fun t ht => s2 t ht not_false, s3⟩
  exact jef_nsClosed3 P Φ D rep hH.hrep hH.hPV₁ hH.hPV₂ hH.hε (fun _ => rfl) repVA
    loopCount_repVA hC card_zSet_repVA
    isTree_repVA clsVA esVA rowsVA row3_repVA basisCrit_esVA
    allPatOK3_repVA pOut pIn kIn αOut βIn μ

end QED.ChainProof.SetALinkV

end
