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

/-- (G₈ₚ) **The order-`e^{2n}` vacuum polarization at fixed `ε`** (Srednicki (62.4), (62.12);
successor of the integrand of (F₁₁)): `Π^{μν}_ε(k) = (1/i) [i Π^{μν}(k)]`, the order-`2n` part of
the two-photon 1PI function with photon momentum `k` flowing in through the first external photon
and out through the second, in the convention of (Z₂). Every flavour enters through its closed
loops, with the counterterms of that flavour on them; the level-`(n-1)` photon counterterm enters
as the tree term `-e^{2n} d₃ (n-1) (k² g^{μν} - k^μ k^ν)`. -/
noncomputable def vacuumPolarizationPart (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (n : ℕ) (k : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  (1 / I) * onePIPart P Φ D 0 2 (2 * n) ![] ![] ![k, -k] ![] ![] ![μ, ν]

end QED.Graded

end
