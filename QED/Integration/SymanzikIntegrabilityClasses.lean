/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.SymanzikIntegrability
public import QED.TwoLoop.EnumerationGauge5

/-!
# The no-subdivergence criterion for the order-`e⁵` vertex topologies

For each of the nine classes `QED.TwoLoop.Enumeration.Class5` of 1PI vertex graphs with five
gauge vertices (`docs/TWO-LOOP-ENUMERATION.md`), an integer loop matrix of its six internal lines
(`class5LoopMatrix`): rows are the lines, columns the coefficients of two loop momenta. Lines
are listed as the fermion lines along the flow of the class representative (`Class5.rep`),
then the two photon lines in the order of its photon pairing:

| class | lines `0 … 5` |
| --- | --- |
| `L`, `X`, `Cp`, `Cm`, `Sp`, `Sm` | `v₀v₁, v₁v₂, v₂v₃, v₃v₄`, then the photons |
| `VP` | `v₀v₁, v₁v₂, v₃v₄, v₄v₃` (the loop), then the photons `(v₀v₃), (v₂v₄)` |
| `Fp` | `v₀v₁, v₂v₃, v₃v₄, v₄v₂` (the loop), then the photons `(v₀v₃), (v₁v₄)` |
| `Fm` | `v₀v₁, v₂v₄, v₄v₃, v₃v₂` (the loop), then the photons `(v₀v₃), (v₁v₄)` |

Each matrix comes from a spanning tree of the graph: its two chords have unit rows and each
column is the signed incidence vector of a fundamental cycle (checked numerically, not in Lean;
the criterion depends only on which lines are parallel). The criterion
`NoSubdivergence` is invariant under the integer unimodular changes of loop momenta that relate
different routings (O2-5 (ii)) and under permutations of the lines, so it is a property of the
topology.

With one denominator per line (photon propagators uncombined):

* `L`, `X`, `Cp`, `Cm`, `Fp`, `Fm` satisfy the criterion (`noSubdivergence_loopMatrix`), so `U⁻²`
  is integrable;
* `Sp`, `Sm`, `VP` violate it (`not_noSubdivergence_loopMatrix`): each contains a one-loop
  subgraph with two lines (the self-energy, the vacuum-polarization bubble).

With each photon line doubled (the Pauli–Villars pair combined as a product of two denominators
with the same momentum, `class5LoopMatrixPV`), all classes except `VP` satisfy it; `VP` still
violates it (the bubble has two fermion lines), and satisfies it once each bubble line is
doubled too (`loopMatrixVPBubble`, the form produced by the second divided difference of the
regulator-fermion sum, `docs/TWO-LOOP-DERIVATION.md` section 4.1).
-/

@[expose] public section

open Finset

namespace QED.Integration.TwoLoop

open QED.TwoLoop.Enumeration

variable {m : ℕ}

/-! ### Integer loop matrices -/

/-- `det(aᵢ, aⱼ)` for an integer loop matrix. -/
def intPairDet (a : Fin (m + 1) → Fin 2 → ℤ) (i j : Fin (m + 1)) : ℤ :=
  a i 0 * a j 1 - a i 1 * a j 0

/-- The no-subdivergence criterion for an integer loop matrix (decidable). -/
def IntNoSubdivergence (a : Fin (m + 1) → Fin 2 → ℤ) : Prop :=
  ∀ i, 3 ≤ (Finset.univ.filter fun j => intPairDet a i j ≠ 0).card

instance (a : Fin (m + 1) → Fin 2 → ℤ) : Decidable (IntNoSubdivergence a) := by
  unfold IntNoSubdivergence; infer_instance

/-- The real loop matrix of an integer one. -/
def castLoopMatrix (a : Fin (m + 1) → Fin 2 → ℤ) : Fin (m + 1) → Fin 2 → ℝ :=
  fun i s => (a i s : ℝ)

theorem noSubdivergence_castLoopMatrix_iff (a : Fin (m + 1) → Fin 2 → ℤ) :
    NoSubdivergence (castLoopMatrix a) ↔ IntNoSubdivergence a := by
  have h : ∀ i, (Finset.univ.filter fun j => pairDet (castLoopMatrix a) i j ≠ 0) =
      Finset.univ.filter fun j => intPairDet a i j ≠ 0 := by
    intro i
    refine Finset.filter_congr fun j _ => ?_
    have : pairDet (castLoopMatrix a) i j = ((intPairDet a i j : ℤ) : ℝ) := by
      simp [pairDet, intPairDet, castLoopMatrix]
    rw [this, Int.cast_ne_zero]
  simp only [NoSubdivergence, IntNoSubdivergence, h]

/-! ### The nine classes -/

/-- An integer loop matrix of the six internal lines of the representative of each class
(the line order of the module docstring). -/
def class5LoopMatrix : Class5 → Fin 6 → Fin 2 → ℤ
  | .L => ![![0, 1], ![1, 0], ![1, 0], ![0, 1], ![0, -1], ![-1, 1]]
  | .X => ![![1, -1], ![1, 0], ![1, 0], ![0, 1], ![-1, 1], ![0, -1]]
  | .Cp => ![![1, 1], ![1, 1], ![1, 0], ![0, -1], ![-1, -1], ![0, 1]]
  | .Cm => ![![1, -1], ![1, 0], ![0, 1], ![0, 1], ![-1, 1], ![0, -1]]
  | .Sp => ![![1, 1], ![1, 1], ![1, 0], ![1, 1], ![-1, -1], ![0, 1]]
  | .Sm => ![![1, 0], ![1, -1], ![1, 0], ![1, 0], ![-1, 0], ![0, 1]]
  | .VP => ![![0, 1], ![0, 1], ![1, -1], ![1, 0], ![0, -1], ![0, 1]]
  | .Fp => ![![-1, 1], ![0, 1], ![1, 0], ![0, 1], ![1, -1], ![-1, 1]]
  | .Fm => ![![-1, 1], ![1, 0], ![0, 1], ![1, 0], ![1, -1], ![-1, 1]]

/-- The loop matrix with each photon line (rows `4`, `5`) doubled: rows `6`, `7` repeat them
(the Pauli–Villars pair as a product of two denominators with the same momentum). -/
def class5LoopMatrixPV (c : Class5) : Fin 8 → Fin 2 → ℤ :=
  fun i => class5LoopMatrix c (![0, 1, 2, 3, 4, 5, 4, 5] i)

/-- The `VP` loop matrix with the photon lines and the two bubble lines (rows `2`, `3`)
doubled: rows `6, 7, 8, 9` repeat rows `4, 5, 2, 3`. -/
def loopMatrixVPBubble : Fin 10 → Fin 2 → ℤ :=
  fun i => class5LoopMatrix .VP (![0, 1, 2, 3, 4, 5, 4, 5, 2, 3] i)

theorem intNoSubdivergence_loopMatrix :
    ∀ c : Class5,
      IntNoSubdivergence (class5LoopMatrix c) ↔ c ∉ ({.Sp, .Sm, .VP} : Finset Class5) := by
  decide

theorem intNoSubdivergence_loopMatrixPV :
    ∀ c : Class5, IntNoSubdivergence (class5LoopMatrixPV c) ↔ c ≠ .VP := by
  decide

theorem intNoSubdivergence_loopMatrixVPBubble : IntNoSubdivergence loopMatrixVPBubble := by
  decide

/-- `L`, `X`, `C±`, `F±` satisfy the criterion with one denominator per line. -/
theorem noSubdivergence_loopMatrix {c : Class5}
    (hc : c ∉ ({.Sp, .Sm, .VP} : Finset Class5)) :
    NoSubdivergence (castLoopMatrix (class5LoopMatrix c)) :=
  (noSubdivergence_castLoopMatrix_iff _).mpr ((intNoSubdivergence_loopMatrix c).mpr hc)

/-- `S±` and `VP` violate the criterion with one denominator per line. -/
theorem not_noSubdivergence_loopMatrix {c : Class5}
    (hc : c ∈ ({.Sp, .Sm, .VP} : Finset Class5)) :
    ¬ NoSubdivergence (castLoopMatrix (class5LoopMatrix c)) := by
  rw [noSubdivergence_castLoopMatrix_iff, intNoSubdivergence_loopMatrix]
  exact not_not.mpr hc

/-- With the photon lines doubled, every class but `VP` satisfies the criterion. -/
theorem noSubdivergence_loopMatrixPV {c : Class5} (hc : c ≠ .VP) :
    NoSubdivergence (castLoopMatrix (class5LoopMatrixPV c)) :=
  (noSubdivergence_castLoopMatrix_iff _).mpr ((intNoSubdivergence_loopMatrixPV c).mpr hc)

theorem not_noSubdivergence_loopMatrixPV_VP :
    ¬ NoSubdivergence (castLoopMatrix (class5LoopMatrixPV .VP)) := by
  rw [noSubdivergence_castLoopMatrix_iff, intNoSubdivergence_loopMatrixPV]
  exact not_not.mpr rfl

theorem noSubdivergence_loopMatrixVPBubble :
    NoSubdivergence (castLoopMatrix loopMatrixVPBubble) :=
  (noSubdivergence_castLoopMatrix_iff _).mpr intNoSubdivergence_loopMatrixVPBubble

/-! ### Integrability of `U⁻²` for the classes -/

theorem integrableOn_inv_sq_symanzikU_loopMatrix {c : Class5}
    (hc : c ∉ ({.Sp, .Sm, .VP} : Finset Class5)) :
    MeasureTheory.IntegrableOn
      (fun x =>
        (symanzikU (castLoopMatrix (class5LoopMatrix c)) (Feynman.simplexPoint x) ^ 2)⁻¹)
      (Feynman.simplexSet 5) :=
  integrableOn_inv_sq_symanzikU_of_criterion _ (noSubdivergence_loopMatrix hc)

theorem integrableOn_inv_sq_symanzikU_loopMatrixPV {c : Class5} (hc : c ≠ .VP) :
    MeasureTheory.IntegrableOn
      (fun x =>
        (symanzikU (castLoopMatrix (class5LoopMatrixPV c)) (Feynman.simplexPoint x) ^ 2)⁻¹)
      (Feynman.simplexSet 7) :=
  integrableOn_inv_sq_symanzikU_of_criterion _ (noSubdivergence_loopMatrixPV hc)

theorem integrableOn_inv_sq_symanzikU_loopMatrixVPBubble :
    MeasureTheory.IntegrableOn
      (fun x =>
        (symanzikU (castLoopMatrix loopMatrixVPBubble) (Feynman.simplexPoint x) ^ 2)⁻¹)
      (Feynman.simplexSet 9) :=
  integrableOn_inv_sq_symanzikU_of_criterion _ noSubdivergence_loopMatrixVPBubble

end QED.Integration.TwoLoop

end
