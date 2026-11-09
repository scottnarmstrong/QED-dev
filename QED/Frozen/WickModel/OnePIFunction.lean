/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.ContractionValue
public import QED.Frozen.WickModel.FermionSign
public import QED.Frozen.WickModel.IsOnePI
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
/-- (X₂₈) **The 1PI function from the Wick expansion** (decisions D-8, D-19, D-22, D-23.2): the
regulated, amputated 1PI part of `⟨Ψ(x₁) Ψ̄(y₁) ⋯ Ψ(x_nf) Ψ̄(y_nf) A(z₁) ⋯ A(z_nA)⟩` in momentum
space at fixed `ε`, through order `K` in `e`. It is the sum over the 1PI Wick contractions of the
terms of `exp(i ∫ L₁) = ∑_N (i ∫ L₁)^N / N!` of total order at most `K`, with the fermionic signs;
the regulator fermions are summed inside each value (X₂₇). A term with `N` vertices is a sum over
the sequences `κ` of their kinds, with the factor `1/N!`; every vertex has order at least `1`, so
`N ≤ K`. The intended evaluations are the vertex `i V^μ` of (62.39), as in (Y₁); the self-energy
of (62.27)–(62.28), `[i Σ(p̸)]_{αβ} = onePIFunction P 1 0 2 ![p] ![p] ![] ![α] ![β] ![]`; and the
vacuum polarization of (62.4) and (62.12), its fermion loop regulated by D-22,
`i Π^{μν}(k) = onePIFunction P 0 2 2 ![] ![] ![k, -k] ![] ![] ![μ, ν]`. Source-facing are
`nf + nA ≥ 1`, `ε > 0`, momentum conservation `∑ pOut = ∑ pIn + ∑ kIn`, and `K ≤ 2 nf + nA + 1`,
which ensures that every contraction in the sum has at most one loop. A non-integrable loop
integrand contributes `0`; closed fermion loops with at most four vertices need the Pauli–Villars
conditions `∑ c_f = 0` and `∑ c_f M_f² = 0` to be integrable. -/
noncomputable def onePIFunction (P : Params) (nf nA K : ℕ) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  ∑ N ∈ Finset.range (K + 1), (N.factorial : ℂ)⁻¹ *
    ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
        (fun κ => ∑ t, (κ t).order ≤ K),
      ∑ C ∈ (Finset.univ : Finset (Contraction nf nA κ)).filter IsOnePI,
        ((fermionSign C : ℤ) : ℂ) * contractionValue P C pOut pIn kIn αOut βIn μ

end QED.WickModel

end
