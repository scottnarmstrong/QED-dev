/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCCtHalf
public import QED.TwoLoop.UnitSCLimitTotal

/-!
# The `δ₂, δ_m` half discharged

`SCtHalfFormula`, the hypothesis of the conditional `S + C` link, holds: it is
`QED.TwoLoop.UnitSCReduce.sixteen_pi_pow_four_mul_sCtHalf`. The `S + C` link at `m = 1` then
depends only on the joint limit of the corner graph, `CornerPartLimit`.
-/

@[expose] public section

namespace QED.TwoLoop.UnitSCLimit

open QED.TwoLoop.HeadlineAssembly

/-- **The `δ₂, δ_m` half of `S`** in the form consumed by the `S + C` assembly. -/
theorem sCtHalfFormula : SCtHalfFormula :=
  fun P hm hmγ hΛ d₁ d₂ dm d₃ =>
    QED.TwoLoop.UnitSCReduce.sixteen_pi_pow_four_mul_sCtHalf P hm hmγ hΛ d₁ d₂ dm d₃

/-- **The `S + C` link at `m = 1`, given the corner graph's joint limit.** -/
theorem scUnitLimitOne_of_cornerPart (hC : CornerPartLimit) : SCUnitLimitOne :=
  scUnitLimitOne_of_sCtHalf_cornerPart sCtHalfFormula hC

end QED.TwoLoop.UnitSCLimit

end
