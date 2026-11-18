/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.SymanzikIntegrabilityRefined
public import QED.Integration.SymanzikIntegrabilityQuadraticClasses

/-!
# The numerator-aware criterion for the order-`e⁵` vertex topologies

The criterion `NoSubdivergenceRefined 2 E` (`QED/Integration/SymanzikIntegrabilityRefined.lean`)
on the loop matrices of the nine classes (`QED/Integration/SymanzikIntegrabilityClasses.lean`),
with `E = {0, 1, 2, 3}` the four fermion lines, each carrying one factor of its momentum in the
numerator (a fermion propagator numerator `k̸ + m` is affine in its momentum, so a product of
four of them has degree at most `|E ∩ S|` in the loop momentum of a one-loop subgraph `S`). The
doubled rows of `class5LoopMatrixPV` and `loopMatrixVPBubble` repeat denominators only.

* single lines: only `X` satisfies it (`L`, `C±` have a vertex subgraph of three lines with two
  fermions, `S±` a self-energy of two lines, `VP` the bubble, `F±` the fermion triangle);
* photon lines doubled: `L`, `X`, `Cp`, `Cm`, `Sp`, `Sm` satisfy it; `VP` (the bubble: two lines,
  both fermions) and `F±` (the fermion triangle: three lines, all fermions) violate it;
* the `VP` form with the bubble lines doubled too satisfies it.

So under this criterion the weight `U⁻² ∏_{e ∈ E} (1 + Q_e/U)^{1/2}` is integrable for all
classes except `F±` (which cancel by Furry's theorem) in their regulated forms, whereas
`tr² A · U⁻⁴` (the criterion of order five) is integrable only for `X` with doubled photons. The
Newton-polytope test (integer weight vectors with entries up to `4`, up to `3` for ten lines)
agrees with every decision, and Monte Carlo truncated means are consistent with them (a numerical
check, not part of the formal statement).

That the absolute parametric integrand of the class numerators is bounded by this weight is not
formalized, and the representation theorems still assume `tr² A · U⁻⁴` integrable.
-/

@[expose] public section

open Finset

namespace QED.Integration.TwoLoop

open QED.TwoLoop.Enumeration

variable {m : ℕ}

/-- The numerator-aware criterion for an integer loop matrix (decidable). -/
def IntNoSubdivergenceRefined (k : ℕ) (E : Finset (Fin (m + 1)))
    (a : Fin (m + 1) → Fin 2 → ℤ) : Prop :=
  ∀ i, 2 * k + (E.filter fun e => intPairDet a i e ≠ 0).card <
    2 * (Finset.univ.filter fun j => intPairDet a i j ≠ 0).card

instance (k : ℕ) (E : Finset (Fin (m + 1))) (a : Fin (m + 1) → Fin 2 → ℤ) :
    Decidable (IntNoSubdivergenceRefined k E a) := by
  unfold IntNoSubdivergenceRefined; infer_instance

theorem noSubdivergenceRefined_castLoopMatrix_iff (k : ℕ) (E : Finset (Fin (m + 1)))
    (a : Fin (m + 1) → Fin 2 → ℤ) :
    NoSubdivergenceRefined k E (castLoopMatrix a) ↔ IntNoSubdivergenceRefined k E a := by
  have hd : ∀ i j, pairDet (castLoopMatrix a) i j ≠ 0 ↔ intPairDet a i j ≠ 0 := fun i j => by
    have : pairDet (castLoopMatrix a) i j = ((intPairDet a i j : ℤ) : ℝ) := by
      simp [pairDet, intPairDet, castLoopMatrix]
    rw [this, Int.cast_ne_zero]
  have h1 : ∀ i, (Finset.univ.filter fun j => pairDet (castLoopMatrix a) i j ≠ 0) =
      Finset.univ.filter fun j => intPairDet a i j ≠ 0 :=
    fun i => Finset.filter_congr fun j _ => hd i j
  have h2 : ∀ i, (E.filter fun e => pairDet (castLoopMatrix a) i e ≠ 0) =
      E.filter fun e => intPairDet a i e ≠ 0 :=
    fun i => Finset.filter_congr fun e _ => hd i e
  simp only [NoSubdivergenceRefined, IntNoSubdivergenceRefined, h1, h2]

theorem intNoSubdivergenceRefined_two_loopMatrix :
    ∀ c : Class5, IntNoSubdivergenceRefined 2 {0, 1, 2, 3} (class5LoopMatrix c) ↔ c = .X := by
  decide

theorem intNoSubdivergenceRefined_two_loopMatrixPV :
    ∀ c : Class5, IntNoSubdivergenceRefined 2 {0, 1, 2, 3} (class5LoopMatrixPV c) ↔
      c ∈ ({.L, .X, .Cp, .Cm, .Sp, .Sm} : Finset Class5) := by
  decide

theorem intNoSubdivergenceRefined_two_loopMatrixVPBubble :
    IntNoSubdivergenceRefined 2 {0, 1, 2, 3} loopMatrixVPBubble := by
  decide

/-- With one denominator per line, only `X` satisfies the numerator-aware criterion. -/
theorem noSubdivergenceRefined_two_loopMatrix_iff (c : Class5) :
    NoSubdivergenceRefined 2 {0, 1, 2, 3} (castLoopMatrix (class5LoopMatrix c)) ↔ c = .X := by
  rw [noSubdivergenceRefined_castLoopMatrix_iff, intNoSubdivergenceRefined_two_loopMatrix]

/-- With the photon lines doubled, `L`, `X`, `Cp`, `Cm`, `Sp`, `Sm` satisfy the numerator-aware
criterion and `VP`, `Fp`, `Fm` violate it. -/
theorem noSubdivergenceRefined_two_loopMatrixPV_iff (c : Class5) :
    NoSubdivergenceRefined 2 {0, 1, 2, 3} (castLoopMatrix (class5LoopMatrixPV c)) ↔
      c ∈ ({.L, .X, .Cp, .Cm, .Sp, .Sm} : Finset Class5) := by
  rw [noSubdivergenceRefined_castLoopMatrix_iff, intNoSubdivergenceRefined_two_loopMatrixPV]

theorem noSubdivergenceRefined_two_loopMatrixVPBubble :
    NoSubdivergenceRefined 2 {0, 1, 2, 3} (castLoopMatrix loopMatrixVPBubble) :=
  (noSubdivergenceRefined_castLoopMatrix_iff 2 _ _).mpr
    intNoSubdivergenceRefined_two_loopMatrixVPBubble

/-- The weight `U⁻² ∏_{e ∈ E} (1 + Q_e/U)^{1/2}`, `E` the fermion lines, is integrable for `L`,
`X`, `Cp`, `Cm`, `Sp`, `Sm` with the photon lines doubled. -/
theorem integrableOn_refinedWeight_loopMatrixPV {c : Class5}
    (hc : c ∈ ({.L, .X, .Cp, .Cm, .Sp, .Sm} : Finset Class5)) :
    MeasureTheory.IntegrableOn
      (fun x => refinedWeight 2 {0, 1, 2, 3} (castLoopMatrix (class5LoopMatrixPV c))
        (Feynman.simplexPoint x))
      (Feynman.simplexSet 7) :=
  integrableOn_refinedWeight_of_criterion _ 2 _
    ((noSubdivergenceRefined_two_loopMatrixPV_iff c).mpr hc)

/-- The same weight is integrable for the `VP` form with the photon and bubble lines doubled. -/
theorem integrableOn_refinedWeight_loopMatrixVPBubble :
    MeasureTheory.IntegrableOn
      (fun x => refinedWeight 2 {0, 1, 2, 3} (castLoopMatrix loopMatrixVPBubble)
        (Feynman.simplexPoint x))
      (Feynman.simplexSet 9) :=
  integrableOn_refinedWeight_of_criterion _ 2 _ noSubdivergenceRefined_two_loopMatrixVPBubble

end QED.Integration.TwoLoop

end
