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
import QED.TwoLoop.LoopBound
import QED.TwoLoop.OneLoopEmbedding

/-!
# Provider for `QED.WickModel.onePIFunction₂_eq_onePIFunction`

Proves the frozen theorem goal (T₁₄) of packet T1 (decision D-38) as
`QED.Provider.TwoLoop.onePIFunction₂_eq_onePIFunction`, with the binder convention of decision
D-13. Through order `K ≤ 2 nf + nA + 1` every 1PI contraction in the sum has at most one loop
(`QED.TwoLoop.LoopBound.loopCount_le_one_of_mem_filter`), and such a contraction has its packet 6a value
(`QED.TwoLoop.contractionValue₂_eq_contractionValue_of_loopCount_le_one`); the two sums then agree
term by term. This module must never import the frozen anchor.
-/

@[expose] public section

namespace QED.Provider.TwoLoop

open QED.WickModel in
/-- Packet T1's (T₁₄), with implicit data binders and a `by assumption` hypothesis (decision
D-13). -/
theorem onePIFunction₂_eq_onePIFunction {P : Params} {nf nA K : ℕ}
    (hK : K ≤ 2 * nf + nA + 1 := by assumption)
    {pOut pIn : Fin nf → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ} {αOut βIn : Fin nf → Fin 4}
    {μ : Fin nA → Fin 4} :
    onePIFunction₂ P nf nA K pOut pIn kIn αOut βIn μ =
      onePIFunction P nf nA K pOut pIn kIn αOut βIn μ := by
  rw [onePIFunction₂, onePIFunction]
  refine Finset.sum_congr rfl fun N _ => congrArg (HMul.hMul _) ?_
  refine Finset.sum_congr rfl fun κ hκ => Finset.sum_congr rfl fun C hC => ?_
  exact congrArg (HMul.hMul _)
    (QED.TwoLoop.contractionValue₂_eq_contractionValue_of_loopCount_le_one P C
      (QED.TwoLoop.LoopBound.loopCount_le_one_of_mem_filter hK hκ hC) pOut pIn kIn αOut βIn μ)

end QED.Provider.TwoLoop

end
