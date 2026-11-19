/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0Crit
public import QED.TwoLoop.ParametricBridge

/-!
# (X₀): the denominators of a two-loop contraction as parametric line denominators

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), step X0d.3. In the
frozen routing (T₄) with two loop momenta, a parametric line on a loop (`LoopLine C`), numbered
by `ι : LoopLine C ≃ Fin (m + 1)`, carries the momentum `lineMomentum (castLoopMatrix (pMat ι))
(pVec ι) (ι q) ℓ` (`lineMomentum₂_eq_lineMomentum`), and a line off the loops carries the
constant momentum `extPart` (`lineMomentum₂_eq_extPart`). So the amplitude denominator of any
contraction at any flavoring is a constant (the lines off the loops) times the product of the
parametric line denominators with the masses `pMass` (`amplitudeDenominator_eq`).
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X0

open QED.WickModel QED.TwoLoop.Bridge
open QED.TwoLoop.Enumeration (lineData)
open QED.Integration.TwoLoop (castLoopMatrix lineMomentum lineDenom)

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}

/-- The constant parts of the momenta of the parametric lines on a loop, numbered by `ι`. -/
noncomputable def pVec {m : ℕ} (ι : LoopLine C ≃ Fin (m + 1)) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) : Fin (m + 1) → Fin 4 → ℝ :=
  fun i => extPart C pOut pIn kIn (ι.symm i).1.line

/-- The mass of a parametric line: the flavoring mass on a fermion line, `mγ` and `Λ` on the
two members of a photon pair. -/
def qMass (P : Params) (φ : Flavoring κ) : PLine C → ℝ
  | .inl f => P.mass (φ.1 f.1)
  | .inr (_, 0) => P.mγ
  | .inr (_, 1) => P.Λ

/-- The masses of the parametric lines on a loop, numbered by `ι`. -/
def pMass (P : Params) (φ : Flavoring κ) {m : ℕ} (ι : LoopLine C ≃ Fin (m + 1)) :
    Fin (m + 1) → ℝ :=
  fun i => qMass P φ (ι.symm i).1

theorem lineMomentum₂_eq_lineMomentum {m : ℕ} (ι : LoopLine C ≃ Fin (m + 1))
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ)
    (q : LoopLine C) :
    lineMomentum₂ C pOut pIn kIn ℓ q.1.line =
      lineMomentum (castLoopMatrix (pMat ι)) (pVec ι pOut pIn kIn) (ι q) ℓ := by
  rw [lineMomentum₂_eq_loopCoeff]
  funext μ
  simp [lineMomentum, castLoopMatrix, pMat, pVec]

theorem lineMomentum₂_eq_extPart (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) (l : Line C) (hl : edgeLoop (lineData C) (edgeOf l) = false) :
    lineMomentum₂ C pOut pIn kIn ℓ l = extPart C pOut pIn kIn l := by
  simp only [edgeLoop, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hl
  rw [lineMomentum₂_eq_loopCoeff, Fin.sum_univ_two]
  simp [loopCoeff, hl.1, hl.2]

/-- The denominator of a parametric line at line momenta `k`. -/
noncomputable def qDen (P : Params) (φ : Flavoring κ) (k : Line C → Fin 4 → ℝ) (q : PLine C) : ℂ :=
  (propDenom (qMass P φ q) P.ε (k q.line))⁻¹

theorem amplitudeDenominator_eq_prod (P : Params) (φ : Flavoring κ) (k : Line C → Fin 4 → ℝ) :
    amplitudeDenominator P C φ k = ∏ q : PLine C, qDen P φ k q := by
  rw [amplitudeDenominator, Fintype.prod_sum_type, Fintype.prod_prod_type]
  simp only [Fin.prod_univ_two]
  rfl

open scoped Classical in
/-- The constant factor of the lines off the loops. -/
noncomputable def offLoopFactor (C : Contraction nf nA κ) (P : Params) (φ : Flavoring κ)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) : ℂ :=
  ∏ q : {q : PLine C // ¬ edgeLoop (lineData C) (edgeOf q.line) = true},
    (propDenom (qMass P φ q.1) P.ε (extPart C pOut pIn kIn q.1.line))⁻¹

/-- **The amplitude denominator in the parametric lines**: a constant times the product of the
line denominators of the parametric lines on a loop. -/
theorem amplitudeDenominator_eq (P : Params) (φ : Flavoring κ) {m : ℕ}
    (ι : LoopLine C ≃ Fin (m + 1)) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    amplitudeDenominator P C φ (lineMomentum₂ C pOut pIn kIn ℓ) =
      offLoopFactor C P φ pOut pIn kIn *
        ∏ i, (lineDenom (castLoopMatrix (pMat ι)) (pVec ι pOut pIn kIn) (pMass P φ ι) P.ε i ℓ)⁻¹
    := by
  classical
  rw [amplitudeDenominator_eq_prod, ← Fintype.prod_subtype_mul_prod_subtype
    (fun q : PLine C => edgeLoop (lineData C) (edgeOf q.line) = true), mul_comm]
  congr 1
  · refine Finset.prod_congr rfl fun q _ => ?_
    rw [qDen, lineMomentum₂_eq_extPart _ _ _ _ _ (by simpa using q.2)]
  · refine Fintype.prod_equiv ι _ _ fun q => ?_
    rw [qDen, lineMomentum₂_eq_lineMomentum ι, lineDenom_eq_propDenom]
    simp [pMass]

end QED.GradedProof.X0

end
