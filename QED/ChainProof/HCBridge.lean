/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCValueEnum
public import QED.ChainProof.HCCovClasses

/-!
# The two names of the set (b) class family agree

`QED.ChainProof.HCValue.enumClass` (the value link) and `QED.ChainProof.chainClassX` (the
covariance and mirror links) are the same nine signed class vertices `+BB, −BD₀, −BD₁, −DB₀, −DB₁,
+DD₀₀, +DD₀₁, +DD₁₀, +DD₁₁` at the chain flavours. Results stated for either plug into the other.
-/

@[expose] public section

namespace QED.ChainProof

open Complex Matrix

/-- The value link's class family is the covariance link's class family. -/
theorem enumClass_eq_chainClassX : HCValue.enumClass = chainClassX := by
  funext r P p' p μ
  ext α β
  fin_cases r <;>
    simp [HCValue.enumClass, HCValue.classV, chainClassX, mul_neg]

end QED.ChainProof

end
