/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.SymanzikIntegrabilityQuadratic
public import QED.Integration.SymanzikIntegrabilityClasses

/-!
# The criteria of order four and five for the order-`e⁵` vertex topologies

The criteria `NoSubdivergenceQuadratic` (every direction class leaves at least four lines) and
`NoSubdivergenceQuartic` (at least five) on the loop matrices of the nine classes of
`QED/Integration/SymanzikIntegrabilityClasses.lean`: one denominator per line
(`class5LoopMatrix`), photon lines doubled (`class5LoopMatrixPV`), and the `VP` form with the
photon and bubble lines doubled (`loopMatrixVPBubble`).

Order four, the hypothesis `hA` of the representation with numerators of degree two:

* single lines: only `X` satisfies it (`L`, `C±` have a vertex subgraph of three lines, `S±`
  and `VP` a self-energy or bubble of two, `F±` the fermion triangle of three);
* photons doubled: `L`, `X`, `Cp`, `Cm` satisfy it; `S±` (a self-energy of three lines,
  one fermion and the doubled photon), `VP` (the bubble) and `F±` (the fermion triangle, whose
  three fermion lines are not doubled) violate it;
* `loopMatrixVPBubble` satisfies it.

Order five, the integrability of `tr² A · U⁻⁴` (numerators of degree four): among these forms
only `X` with doubled photons satisfies it.

The Newton-polytope face test and Monte Carlo agree with each decision (a numerical check, not
part of the formal statement; see `QED/Integration/SymanzikIntegrabilityQuadratic.lean`).
-/

@[expose] public section

open Finset

namespace QED.Integration.TwoLoop

open QED.TwoLoop.Enumeration

variable {m : ℕ}

/-- The criterion of order `n` for an integer loop matrix (decidable). -/
def IntNoSubdivergenceOfOrder (n : ℕ) (a : Fin (m + 1) → Fin 2 → ℤ) : Prop :=
  ∀ i, n ≤ (Finset.univ.filter fun j => intPairDet a i j ≠ 0).card

instance (n : ℕ) (a : Fin (m + 1) → Fin 2 → ℤ) : Decidable (IntNoSubdivergenceOfOrder n a) := by
  unfold IntNoSubdivergenceOfOrder; infer_instance

theorem noSubdivergenceOfOrder_castLoopMatrix_iff (n : ℕ) (a : Fin (m + 1) → Fin 2 → ℤ) :
    NoSubdivergenceOfOrder n (castLoopMatrix a) ↔ IntNoSubdivergenceOfOrder n a := by
  have h : ∀ i, (Finset.univ.filter fun j => pairDet (castLoopMatrix a) i j ≠ 0) =
      Finset.univ.filter fun j => intPairDet a i j ≠ 0 := by
    intro i
    refine Finset.filter_congr fun j _ => ?_
    have : pairDet (castLoopMatrix a) i j = ((intPairDet a i j : ℤ) : ℝ) := by
      simp [pairDet, intPairDet, castLoopMatrix]
    rw [this, Int.cast_ne_zero]
  simp only [NoSubdivergenceOfOrder, IntNoSubdivergenceOfOrder, h]

/-! ### Order four -/

theorem intNoSubdivergenceOfOrder_four_loopMatrix :
    ∀ c : Class5, IntNoSubdivergenceOfOrder 4 (class5LoopMatrix c) ↔ c = .X := by
  decide

theorem intNoSubdivergenceOfOrder_four_loopMatrixPV :
    ∀ c : Class5, IntNoSubdivergenceOfOrder 4 (class5LoopMatrixPV c) ↔
      c ∈ ({.L, .X, .Cp, .Cm} : Finset Class5) := by
  decide

theorem intNoSubdivergenceOfOrder_four_loopMatrixVPBubble :
    IntNoSubdivergenceOfOrder 4 loopMatrixVPBubble := by
  decide

theorem noSubdivergenceQuadratic_loopMatrix_iff (c : Class5) :
    NoSubdivergenceQuadratic (castLoopMatrix (class5LoopMatrix c)) ↔ c = .X := by
  rw [NoSubdivergenceQuadratic, noSubdivergenceOfOrder_castLoopMatrix_iff,
    intNoSubdivergenceOfOrder_four_loopMatrix]

/-- With the photon lines doubled, `L`, `X`, `Cp`, `Cm` satisfy the criterion of order four
and `Sp`, `Sm`, `VP`, `Fp`, `Fm` violate it. -/
theorem noSubdivergenceQuadratic_loopMatrixPV_iff (c : Class5) :
    NoSubdivergenceQuadratic (castLoopMatrix (class5LoopMatrixPV c)) ↔
      c ∈ ({.L, .X, .Cp, .Cm} : Finset Class5) := by
  rw [NoSubdivergenceQuadratic, noSubdivergenceOfOrder_castLoopMatrix_iff,
    intNoSubdivergenceOfOrder_four_loopMatrixPV]

theorem noSubdivergenceQuadratic_loopMatrixVPBubble :
    NoSubdivergenceQuadratic (castLoopMatrix loopMatrixVPBubble) :=
  (noSubdivergenceOfOrder_castLoopMatrix_iff 4 _).mpr
    intNoSubdivergenceOfOrder_four_loopMatrixVPBubble

/-! ### Order five -/

theorem intNoSubdivergenceOfOrder_five_loopMatrix :
    ∀ c : Class5, ¬ IntNoSubdivergenceOfOrder 5 (class5LoopMatrix c) := by
  decide

theorem intNoSubdivergenceOfOrder_five_loopMatrixPV :
    ∀ c : Class5, IntNoSubdivergenceOfOrder 5 (class5LoopMatrixPV c) ↔ c = .X := by
  decide

theorem not_intNoSubdivergenceOfOrder_five_loopMatrixVPBubble :
    ¬ IntNoSubdivergenceOfOrder 5 loopMatrixVPBubble := by
  decide

theorem noSubdivergenceQuartic_loopMatrixPV_iff (c : Class5) :
    NoSubdivergenceQuartic (castLoopMatrix (class5LoopMatrixPV c)) ↔ c = .X := by
  rw [NoSubdivergenceQuartic, noSubdivergenceOfOrder_castLoopMatrix_iff,
    intNoSubdivergenceOfOrder_five_loopMatrixPV]

/-! ### `hA` for the classes -/

/-- `tr A · U⁻³` is integrable for `L`, `X`, `Cp`, `Cm` with the photon lines doubled. -/
theorem integrableOn_trace_mul_inv_cube_symanzikU_loopMatrixPV {c : Class5}
    (hc : c ∈ ({.L, .X, .Cp, .Cm} : Finset Class5)) :
    MeasureTheory.IntegrableOn
      (fun x => (symanzikMatrix (castLoopMatrix (class5LoopMatrixPV c))
          (Feynman.simplexPoint x)).trace *
        (symanzikU (castLoopMatrix (class5LoopMatrixPV c)) (Feynman.simplexPoint x) ^ 3)⁻¹)
      (Feynman.simplexSet 7) :=
  integrableOn_trace_mul_inv_cube_symanzikU _ ((noSubdivergenceQuadratic_loopMatrixPV_iff c).mpr hc)

/-- `tr A · U⁻³` is integrable for the `VP` form with the photon and bubble lines doubled. -/
theorem integrableOn_trace_mul_inv_cube_symanzikU_loopMatrixVPBubble :
    MeasureTheory.IntegrableOn
      (fun x => (symanzikMatrix (castLoopMatrix loopMatrixVPBubble)
          (Feynman.simplexPoint x)).trace *
        (symanzikU (castLoopMatrix loopMatrixVPBubble) (Feynman.simplexPoint x) ^ 3)⁻¹)
      (Feynman.simplexSet 9) :=
  integrableOn_trace_mul_inv_cube_symanzikU _ noSubdivergenceQuadratic_loopMatrixVPBubble

end QED.Integration.TwoLoop

end
