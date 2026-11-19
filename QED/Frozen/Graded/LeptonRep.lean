/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace QED.Graded

/-- (G₁₂′) **The renormalization blocks of the multi-lepton flavours** (L₁) (finding F1 of the Stage
2 design note; the adopted ruling S2′, D-55 revised): every flavour of the electron block `inl i`
takes its counterterms from the electron `inl 0`, and every flavour of the block `inr (ℓ, i)` of
heavy lepton `ℓ` from that lepton, `inr (ℓ, 0)`. The physical leptons are the fixed points. With
(G₁₂) this is the per-lepton on-shell scheme: each physical lepton is renormalized on shell at its
own mass, and its two regulator fermions share its counterterm coefficients; on a regulator line the
mass counterterm vertex is `d_m · M_f`, with the regulator's own mass (G₃). -/
def leptonRep {n : ℕ} : Fin 3 ⊕ Fin n × Fin 3 → Fin 3 ⊕ Fin n × Fin 3
  | .inl _ => .inl 0
  | .inr x => .inr (x.1, 0)

end QED.Graded

end
