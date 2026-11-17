/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.ContractionValue
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
/-- (T₁₁) **The 1PI function from the Wick expansion, up to two loops** (decisions D-19, D-22,
D-23.2, D-37.3, D-37.6): (X₂₈) with the value (T₁₀). It is the sum over the 1PI Wick contractions
of the terms of `exp(i ∫ L₁) = ∑_N (i ∫ L₁)^N / N!` of total order at most `K` in `e`, with the
fermionic signs, the counterterms counted with the frozen orders (`δ₁ e` of order `3`, `δ₂`, `δm`,
`δ₃` of order `2`; single real numbers, the expansion truncated, D-37.3). Source-facing are
`nf + nA ≥ 1`, `ε > 0`, momentum conservation `∑ pOut = ∑ pIn + ∑ kIn`, and
`K ≤ 2 nf + nA + 3`, which ensures that every contraction in the sum has at most two loops: the
vertex `(nf, nA) = (1, 1)` at `K = 5`, the self-energy and the vacuum polarization at `K = 4`. A
non-integrable integrand contributes `0`; closed fermion loops with at most four vertices need the
Pauli–Villars conditions `∑ c_f = 0` and `∑ c_f M_f² = 0` to be integrable. The intended evaluation
is the vertex `i V^μ = onePIFunction₂ P 1 1 5 ![p'] ![p] ![p' - p] ![i] ![j] ![μ]`. -/
noncomputable def onePIFunction₂ (P : Params) (nf nA K : ℕ) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  ∑ N ∈ Finset.range (K + 1), (N.factorial : ℂ)⁻¹ *
    ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
        (fun κ => ∑ t, (κ t).order ≤ K),
      ∑ C ∈ (Finset.univ : Finset (Contraction nf nA κ)).filter IsOnePI,
        ((fermionSign C : ℤ) : ℂ) * contractionValue₂ P C pOut pIn kIn αOut βIn μ

end QED.WickModel

end
