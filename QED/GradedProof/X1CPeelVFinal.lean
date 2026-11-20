/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CPlumbDyson
public import QED.GradedProof.X1CPeelIn
public import QED.GradedProof.X1CPeelOut
public import QED.GradedProof.X1CPeelTad
public import QED.GradedProof.X1CPeelPSurj
public import QED.GradedProof.X1CPeelV

/-!
# (X₁) piece C: the order-`e⁵` Dyson decomposition

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C. **`peelV_dysonFive`**: under the hypotheses of (X₁) (positive masses
bounded below by `m₀`, positive photon mass and cutoff, the Pauli–Villars conditions of the
flavour regulator `rep`, renormalization through order `2`), `DysonFive` holds at every `ε > 0`.

It is `countDyson_dysonFive_t9` at `T9Hyps.of_x1`, with the classes `G = peelSelG` (attached,
connected, tadpole-free), `RedIn = peelRedIn`, `RedOut = peelRedOut`, `RedP = peelRedP`, and the
graph-theoretic hypotheses: tadpole removal `peelTad_h0`, the in-leg bijection `peel_hmemI`,
`peel_hinjI`, `peel_hsurjI`, the out-leg bijection `peelOut_hmemO`, `peelOut_hinjO`,
`peelOut_hsurjO`, the photon-leg bijection `peelP_hmemP`, `peelP_hinjP`, `peelP_hsurjP`, and
`peelV_hV` (fully peeled ⇔ 1PI).
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Params)
open QED.Graded

/-- **Piece C of (X₁)**: the order-`e⁵` Dyson decomposition at every `ε > 0`. -/
theorem peelV_dysonFive (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F) (m₀ : ℝ) (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : IsRenormalizedThrough P Φ D rep 2) :
    ∀ ε > 0, DysonFive { P with ε := ε } Φ D := fun _ hε =>
  countDyson_dysonFive_t9
    (T9Hyps.of_x1 P Φ D rep m₀ hm₀ hmass hmγ hΛ hrep hPV₁ hPV₂ hD hε)
    peelSelG peelRedIn peelRedOut peelRedP peel_hG (peelTad_h0 _ Φ D)
    peel_hmemI peel_hinjI peel_hsurjI peelOut_hmemO peelOut_hinjO peelOut_hsurjO
    peelP_hmemP peelP_hinjP peelP_hsurjP peelV_hV

end QED.GradedProof.X1C

end
