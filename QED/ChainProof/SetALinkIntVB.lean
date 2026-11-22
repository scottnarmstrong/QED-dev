/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetALinkIntVTerm
public import QED.ChainProof.SetALinkInt

/-!
# The class obligation of `repVB`

Helper for the Phase 5 Stage 3a goal (HA₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setA`
(decision D-58). `QED.ChainProof.SetALink.repVB` is the vertex-type bubble, loop `[3, 5, 4, 6]`:
three loops, seven `gauge` vertices, grading `0`. **`classIntA_repVB`**: its class obligation
`QED.ChainProof.SetALink.ClassIntA repVB 0`, by `jef_nsClosed3`
(`QED/ChainProof/SetALinkIntVTerm.lean`), at any masses.

The kernel checks: the closed-loop shape, at most four loop lines, every line off the loop
carrying loop momentum on `ℓ₀` or `ℓ₁`, the rows of the lines up to sign (`rowsVB`, 6
classes, `clsVB`), the basis criterion for each of the 35 minimal exponent vectors
(`esVB`) and the pattern criterion `AllPatOK3`.
-/

@[expose] public section

namespace QED.ChainProof.SetALinkV

open QED.WickModel QED.GradedProof.X0 QED.ChainProof.SetALink

/-- The rows of the line classes of `repVB`. -/
def rowsVB : Fin 6 → Fin 3 → ℤ :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![-1, 0, 1], ![1, 1, 0], ![-1, -1, 1]]

/-- The class of a line of `repVB`. -/
def clsVB (l : Line repVB) : Fin 6 := clsOf rowsVB (row3 repVB l)

/-- Minimal exponent vectors of `repVB`, part 0. -/
def esVB0 : List (Fin 6 → ℕ) :=
  [![10, 1, 1, 1, 5, 4],
  ![10, 1, 1, 2, 4, 4],
  ![10, 1, 1, 3, 3, 4],
  ![10, 1, 1, 4, 2, 4],
  ![10, 1, 1, 5, 1, 4]]

theorem critB_esVB0 : (esVB0.all fun E => critB rowsVB E 5) = true := by
  decide +kernel

/-- Minimal exponent vectors of `repVB`, part 1. -/
def esVB1 : List (Fin 6 → ℕ) :=
  [![10, 1, 2, 1, 4, 4],
  ![10, 1, 2, 2, 3, 4],
  ![10, 1, 2, 3, 2, 4],
  ![10, 1, 2, 4, 1, 4],
  ![10, 1, 3, 1, 3, 4]]

theorem critB_esVB1 : (esVB1.all fun E => critB rowsVB E 5) = true := by
  decide +kernel

/-- Minimal exponent vectors of `repVB`, part 2. -/
def esVB2 : List (Fin 6 → ℕ) :=
  [![10, 1, 3, 2, 2, 4],
  ![10, 1, 3, 3, 1, 4],
  ![10, 1, 4, 1, 2, 4],
  ![10, 1, 4, 2, 1, 4],
  ![10, 1, 5, 1, 1, 4]]

theorem critB_esVB2 : (esVB2.all fun E => critB rowsVB E 5) = true := by
  decide +kernel

/-- Minimal exponent vectors of `repVB`, part 3. -/
def esVB3 : List (Fin 6 → ℕ) :=
  [![10, 2, 1, 1, 4, 4],
  ![10, 2, 1, 2, 3, 4],
  ![10, 2, 1, 3, 2, 4],
  ![10, 2, 1, 4, 1, 4],
  ![10, 2, 2, 1, 3, 4]]

theorem critB_esVB3 : (esVB3.all fun E => critB rowsVB E 5) = true := by
  decide +kernel

/-- Minimal exponent vectors of `repVB`, part 4. -/
def esVB4 : List (Fin 6 → ℕ) :=
  [![10, 2, 2, 2, 2, 4],
  ![10, 2, 2, 3, 1, 4],
  ![10, 2, 3, 1, 2, 4],
  ![10, 2, 3, 2, 1, 4],
  ![10, 2, 4, 1, 1, 4]]

theorem critB_esVB4 : (esVB4.all fun E => critB rowsVB E 5) = true := by
  decide +kernel

/-- Minimal exponent vectors of `repVB`, part 5. -/
def esVB5 : List (Fin 6 → ℕ) :=
  [![10, 3, 1, 1, 3, 4],
  ![10, 3, 1, 2, 2, 4],
  ![10, 3, 1, 3, 1, 4],
  ![10, 3, 2, 1, 2, 4],
  ![10, 3, 2, 2, 1, 4]]

theorem critB_esVB5 : (esVB5.all fun E => critB rowsVB E 5) = true := by
  decide +kernel

/-- Minimal exponent vectors of `repVB`, part 6. -/
def esVB6 : List (Fin 6 → ℕ) :=
  [![10, 3, 3, 1, 1, 4],
  ![10, 4, 1, 1, 2, 4],
  ![10, 4, 1, 2, 1, 4],
  ![10, 4, 2, 1, 1, 4],
  ![10, 5, 1, 1, 1, 4]]

theorem critB_esVB6 : (esVB6.all fun E => critB rowsVB E 5) = true := by
  decide +kernel

/-- The minimal exponent vectors of `repVB`. -/
def esVB : List (Fin 6 → ℕ) := esVB0 ++ esVB1 ++ esVB2 ++ esVB3 ++ esVB4 ++ esVB5 ++ esVB6

theorem basisCrit_esVB : ∀ E ∈ esVB, BasisCrit rowsVB E 5 := by
  have h : (esVB.all fun E => critB rowsVB E 5) = true := by
    simp only [esVB, List.all_append, critB_esVB0, critB_esVB1, critB_esVB2, critB_esVB3,
      critB_esVB4, critB_esVB5, critB_esVB6, Bool.and_self]
  intro E hE
  exact basisCrit_of_critB (List.all_eq_true.mp h E hE)

theorem shapeOK_repVB : ShapeOK repVB (zOf repVB) := by decide +kernel

theorem card_zSet_repVB : (zSet repVB).card ≤ 4 := by decide +kernel

theorem isTree_repVB : ∀ l, isZL repVB l = false → isTree repVB l = false := by
  decide +kernel

theorem row3_repVB : ∀ l, row3 repVB l = rowsVB (clsVB l) ∨
    row3 repVB l = -rowsVB (clsVB l) := by
  decide +kernel

theorem allPatOK3_repVB : AllPatOK3 repVB clsVB esVB := by decide +kernel

/-- **The class obligation of `repVB`.** -/
theorem classIntA_repVB : ClassIntA repVB 0 := by
  intro P F _ _ Φ D rep hH pOut pIn kIn _ αOut βIn μ
  obtain ⟨s1, s2, s3⟩ := shapeOK_repVB
  have hC : ClosedShape repVB (zOf repVB) := ⟨s1, fun t ht => s2 t ht not_false, s3⟩
  exact jef_nsClosed3 P Φ D rep hH.hrep hH.hPV₁ hH.hPV₂ hH.hε (fun _ => rfl) repVB
    loopCount_repVB hC card_zSet_repVB
    isTree_repVB clsVB esVB rowsVB row3_repVB basisCrit_esVB
    allPatOK3_repVB pOut pIn kIn αOut βIn μ

end QED.ChainProof.SetALinkV

end
