/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

@[expose] public section

namespace QED.Wick

/-- (V₀) The interaction vertices of spinor electrodynamics with counterterms, (62.2)–(62.3)
(decision D-19): `gauge` is `e Ψ̄ A̸ Ψ`; `gaugeCt` is `(Z₁ - 1) e Ψ̄ A̸ Ψ`; `fermionCt` is
`i (Z₂ - 1) Ψ̄ ∂̸ Ψ - (Z_m - 1) m Ψ̄ Ψ`; and `photonCt` is `-¼ (Z₃ - 1) F^{μν} F_{μν}`. -/
inductive VertexKind where
  | gauge
  | gaugeCt
  | fermionCt
  | photonCt
  deriving DecidableEq

end QED.Wick

end
