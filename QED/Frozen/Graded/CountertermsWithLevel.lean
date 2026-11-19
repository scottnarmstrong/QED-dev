/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.Counterterms

@[expose] public section

namespace QED.Graded

/-- (G₀′) **Replacing one level of the counterterm data**: `D` with its level-`k` coefficients
replaced by `x f = (d₁, d₂, d_m)` for each flavour `f` and `y` for the photon; the other levels are
those of `D`. Used to state that the conditions at one order fix the level they read linearly,
as (Z₆) and (Z₉) replace the counterterms stored in `Params`. -/
def Counterterms.withLevel {F : Type} (D : Counterterms F) (k : ℕ) (x : F → ℝ × ℝ × ℝ)
    (y : ℝ) : Counterterms F where
  d₁ f j := if j = k then (x f).1 else D.d₁ f j
  d₂ f j := if j = k then (x f).2.1 else D.d₂ f j
  dm f j := if j = k then (x f).2.2 else D.dm f j
  d₃ j := if j = k then y else D.d₃ j

end QED.Graded

end
