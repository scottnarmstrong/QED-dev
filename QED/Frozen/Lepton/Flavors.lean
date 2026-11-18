/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace QED.Lepton

/-- (F₀) **Flavour data** (decisions D-22, D-49.4): a finite set `F` of fermion flavours with,
for each flavour `f`, the mass `mass f` of its propagator and the coefficient `coeff f` of a
closed loop of that flavour, and the flavour `openLine` of the external fermion fields and of the
counterterm vertices. Packet T1 is the case `F = Fin 3`, `mass = P.mass` (X₀′),
`coeff = P.loopCoeff` (X₀″), `openLine = 0`. Conditions such as the Pauli–Villars conditions
are hypotheses of later theorems. The vertex factor of the `δ_m` counterterm reads the mass `P.m`
of the parameters (F₅), so a pair `(P, Φ)` is coherent only when `Φ.mass Φ.openLine = P.m`; both
instances (T1's and (L₁)) satisfy this by definition. -/
structure Flavors (F : Type) where
  /-- The mass of the propagator of a fermion of flavour `f`. -/
  mass : F → ℝ
  /-- The coefficient of a closed fermion loop of flavour `f` (`1` for a physical lepton). -/
  coeff : F → ℝ
  /-- The flavour of the external fermion fields and of the counterterm vertices. -/
  openLine : F

end QED.Lepton

end
