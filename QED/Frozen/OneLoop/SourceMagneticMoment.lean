/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.PacketCurrentDensity
public import QED.Frozen.OneLoop.PacketNormSq

@[expose] public section

open MeasureTheory

namespace QED.OneLoop

/-- (W₃) **The magnetic moment, source definition** (64.4)–(64.7) (ruling D-9): with the field
`A = (0, B x, 0)` of p. 383 and `H₁ = -∫ d³x J·A = -B ∫ d³x x¹ J²(x)`, the definition
`μ B ≡ -⟨e|H₁|e⟩ / ⟨e|e⟩` gives `μ = ∫ d³x x¹ ⟨e|J²(x)|e⟩ / ⟨e|e⟩` for the wave packet (W₁).
The position integral is the undamped one; it is meaningful when it converges absolutely
(decision D-17), which theorem (W₄) asserts. -/
noncomputable def sourceMagneticMoment (e Z₁ m mγ Λ : ℝ) (hm : 0 < m) (hmγ : 0 < mγ)
    (hΛ : 0 < Λ) (φ : ℝ → ℝ) (lam : ℝ) : ℂ :=
  (∫ x : Fin 3 → ℝ, (x 0 : ℂ) * packetCurrentDensity e Z₁ m mγ Λ hm hmγ hΛ φ lam x)
    / (packetNormSq m φ lam : ℂ)

end QED.OneLoop

end
