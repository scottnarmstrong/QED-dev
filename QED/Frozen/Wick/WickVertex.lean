/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.ContractionValue
public import QED.Frozen.Wick.FermionSign
public import QED.Frozen.Wick.IsOnePI
public import QED.Frozen.Wick.VertexKindOrder
public import QED.Frozen.Wick.VertexKindFintype
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma

@[expose] public section

namespace QED.Wick

open scoped Classical in
/-- (V₂₂) **The vertex function from the Wick expansion** (decisions D-8 and D-19): the regulated
`i V^μ(p', p)` at fixed `ε` through order `e³` (the source's (62.39)), as the sum over the 1PI
Wick contractions of the terms of `exp(i ∫ L₁) = ∑_N (i ∫ L₁)^N / N!` of total order at most `3`
in `e`, with the fermionic signs. A term with `N` vertices is a sum over the sequences `κ` of
their kinds, with the factor `1/N!`; total order at most `3` forces `N ≤ 3`. The vertex
counterterm is `δ₁ = Z₁ - 1`, and `δ₂, δ_m, δ₃` are the two-point counterterms `Z₂ - 1`,
`Z_m - 1`, `Z₃ - 1`. Only `ε > 0` is source-facing. -/
noncomputable def wickVertex (e δ₁ δ₂ δm δ₃ m mγ Λ ε : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ N ∈ Finset.range 4, ((N.factorial : ℂ)⁻¹) •
    ∑ κ ∈ (Finset.univ : Finset (Fin N → VertexKind)).filter (fun κ => ∑ t, (κ t).order ≤ 3),
      ∑ C ∈ (Finset.univ : Finset (Contraction κ)).filter IsOnePI,
        ((fermionSign C : ℤ) : ℂ) • contractionValue e δ₁ δ₂ δm δ₃ m mγ Λ ε C p' p μ

end QED.Wick

end
