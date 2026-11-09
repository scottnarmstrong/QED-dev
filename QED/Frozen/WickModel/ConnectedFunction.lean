/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.ContractionValue
public import QED.Frozen.WickModel.FermionSign
public import QED.Frozen.WickModel.ExternalsAttached
public import QED.Frozen.WickModel.VerticesConnected
public import QED.Frozen.Wick.VertexKindOrder
public import QED.Frozen.Wick.VertexKindFintype
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
/-- (X₂₉) **The connected function from the Wick expansion** (decision D-23.1): as (X₂₈), but the
sum is over the contractions whose externals are attached (X₁₆) and whose vertices are connected
(X₁₇). This is the regulated connected part of
`⟨Ψ(x₁) Ψ̄(y₁) ⋯ Ψ(x_nf) Ψ̄(y_nf) A(z₁) ⋯ A(z_nA)⟩` in momentum space, through order `K`, amputated
by the free external propagators; the corrections on the external legs are included.
Source-facing are `nf + nA ≥ 1`, `ε > 0`, momentum conservation `∑ pOut = ∑ pIn + ∑ kIn`, and
`K ≤ 2 nf + nA + 1`, which ensures that every contraction in the sum has at most one loop. A
non-integrable loop integrand contributes `0`; closed fermion loops with at most four vertices need
the Pauli–Villars conditions `∑ c_f = 0` and `∑ c_f M_f² = 0` to be integrable. -/
noncomputable def connectedFunction (P : Params) (nf nA K : ℕ) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  ∑ N ∈ Finset.range (K + 1), (N.factorial : ℂ)⁻¹ *
    ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
        (fun κ => ∑ t, (κ t).order ≤ K),
      ∑ C ∈ (Finset.univ : Finset (Contraction nf nA κ)).filter
          (fun C => ExternalsAttached C ∧ VerticesConnected C),
        ((fermionSign C : ℤ) : ℂ) * contractionValue P C pOut pIn kIn αOut βIn μ

end QED.WickModel

end
