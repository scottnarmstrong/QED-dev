/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.LineMomentum
public import QED.Frozen.WickModel.PhotonLineHead
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

open Complex

namespace QED.WickModel

open scoped Classical in
/-- (X₂₄) The momentum flowing into the vertex of the photon field `a` through `a`: `kIn j` if `a`
is contracted with the external `A(zⱼ)`, and otherwise the momentum of its photon line, counted
positively at the line's head and negatively at its tail. -/
noncomputable def photonMomentum {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (ℓ : Fin 4 → ℝ) (a : Wick.PhotonSlot κ) : Fin 4 → ℝ :=
  (∑ j, if C.1.2 (.inl j) = .inr a then kIn j else 0) +
    ∑ g : PhotonLine C, ((if g.head = a then lineMomentum C pOut pIn kIn ℓ (.inr g) else 0)
      - (if g.1 = a then lineMomentum C pOut pIn kIn ℓ (.inr g) else 0))

end QED.WickModel

end
