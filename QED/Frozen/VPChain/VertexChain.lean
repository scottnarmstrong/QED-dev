/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.VPChain.IsVPChain
public import QED.Frozen.Lepton.OnePIFamilyFunction

@[expose] public section

open Complex
open QED.WickModel (Params)
open QED.Lepton (Flavors onePIFamilyFunction₂)

namespace QED.VPChain

/-- (C₃) **The 1PI vertex of the vacuum-polarization chains with `n` insertions at fixed `ε`**
(decisions D-37.3, D-37.6, D-49.4; the analogue of (HV₁) and (F₉); plan O3-3): `(1/i)` times the
family 1PI function (C₂) of the chains (C₁), with one external fermion pair (of flavour
`Φ.openLine`) and one external photon, at total order `2n + 3`, outgoing momentum `p'`, incoming
momentum `p` and incoming photon momentum `p' - p`; the row index is outgoing and the column
index incoming, as in (HV₁). Every chain contraction has total order exactly `2n + 3`, so the
filter `≤ 2n + 3` of (C₂) drops nothing and no subtraction of lower orders is needed (theorem
(M₂): it is the part in the family of the order-`e^{2n+3}` terms of (F₈)). For `n = 2` it is the
sixth-order set (b) with its counterterm graphs: the bubble–bubble graphs (three loops), the
bubble–`δ₃` and `δ₃`–bubble graphs (two loops) and the `δ₃`–`δ₃` graphs (one loop), each bubble
summed over the flavours of `Φ` inside one integrand (F₆) and weighted by the loop coefficient
(F₄). The counterterm `δ₃` is that of `P`; when `e ≠ 0` and `δ₃` satisfies the photon condition
(of order `e²`), it is `e²` times a number independent of `e`, so (C₃) is `e^{2n+3}` times a matrix
independent of `e` (obligation O3-7, the analogue of O2-27). It is **not** the sixth-order vertex:
the other sets (a), (c), (e) need counterterms of order `e⁴` that the model does not have (D-37.3;
plan section 1). Source-facing are `ε > 0`, on-shell positive-energy `p`, `p'`, and the coherence
`Φ.mass Φ.openLine = P.m`. -/
noncomputable def vertexChain (n : ℕ) (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Flavors F) (p' p : Fin 4 → ℝ) (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => (1 / I) *
    onePIFamilyFunction₂ P Φ 1 1 (IsVPChain n) (2 * n + 3) (fun _ => p') (fun _ => p)
      (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ)

end QED.VPChain

end
