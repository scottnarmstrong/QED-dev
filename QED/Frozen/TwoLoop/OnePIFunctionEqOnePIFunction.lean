-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.OnePIFunction
public import QED.Frozen.WickModel.OnePIFunction
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
public import QED.Provider.TwoLoop.OnePIFunctionEqOnePIFunction

@[expose] public section

open Complex

namespace QED.WickModel

/-- (T₁₄) **Packet 6a is the special case (packet T1 theorem goal; obligation O2-9).** For all
parameters, external content and momenta, the 1PI function (T₁₁) through order
`K ≤ 2 nf + nA + 1` is packet 6a's (X₂₈): every connected contraction with attached externals of
total order at most `K` then has at most one loop (T₂), and (T₁₃) applies term by term. With (Y₁)
it gives packet 5's vertex at `nf = nA = 1`, `K = 3`; the counterterm data and the predicates of
packets 6b and 6c are unchanged, since `Params` is reused. -/
theorem onePIFunction₂_eq_onePIFunction (P : Params) (nf nA K : ℕ) (hK : K ≤ 2 * nf + nA + 1)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) :
    onePIFunction₂ P nf nA K pOut pIn kIn αOut βIn μ =
      onePIFunction P nf nA K pOut pIn kIn αOut βIn μ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.WickModel

end
-- FROZEN_ANCHOR_SUFFIX_END
