/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.OnePIPart

@[expose] public section

open Complex
open QED.WickModel (Params)

namespace QED.Graded

/-- (G₈ₛ) **The order-`e^{2n}` self-energy of flavour `f` at fixed `ε`** (Srednicki
(62.27)–(62.28), (G₆′)): `Σ^{(2n)}_ε(p) = (1/i) [i Σ(p)]`, where `[i Σ(p)]_{αβ}` is the
order-`2n` part of the one-fermion 1PI function with external flavour `f` (the flavour data with
`openLine := f`), outgoing index `α` as row and incoming `β` as column, as in (Z₁). It contains
the tree term `-(e^{2n} d₂ f (n-1) p̸ + e^{2n} d_m f (n-1) M_f)` of the level-`(n-1)` counterterm
and the loop graphs with counterterms of lower levels. -/
noncomputable def selfEnergyPart (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (n : ℕ) (p : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun α β =>
    (1 / I) * onePIPart P { Φ with openLine := f } D 1 0 (2 * n) ![p] ![p] ![] ![α] ![β] ![]

end QED.Graded

end
