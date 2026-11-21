/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.SelectedPart

@[expose] public section

open Complex
open QED.WickModel (Params Contraction)

namespace QED.Graded

/-- (Gf₁) **The vertex of a family of graded contractions at fixed `ε`** (decisions D-37.6,
D-49.4, D-54.3; successor of (C₃) in the graded model; ruling S5 of the Stage 2 design note):
`(1/i)` times the part of order exactly `K` (G₆) of the sum over the graded contractions with one
external fermion pair (of flavour `Φ.openLine`) and one external photon that satisfy the selection
`Sel`, at outgoing momentum `p'`, incoming momentum `p` and incoming photon momentum `p' - p`; the
row index is outgoing and the column index incoming, as in (HV₁), (F₉), (C₃) and (G₈ᵥ). The
selection may read the grading (the level of each counterterm vertex). The same `1/N!`, fermionic
signs and values (G₅) as in (G₆): a family vertex is a partial sum of the graded order-`K` terms,
with their coefficients, not a new amplitude. With `Sel C g := IsOnePI C` and `K = 2n + 1` it is
the vertex (G₈ᵥ) at the open-line flavour (theorem (MF₁)). Source-facing for the gauge-invariant
families named in later declarations (sets (a) and (c) at `K = 7`), at `ε > 0`, with momentum
conservation. -/
noncomputable def familyVertex (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F)
    (Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction 1 1 κ → Grading κ → Prop)
    (K : ℕ) (p' p : Fin 4 → ℝ) (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => (1 / I) *
    selectedPart P Φ D 1 1 Sel K (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i)
      (fun _ => j) (fun _ => μ)

end QED.Graded

end
