/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.FamilyVertex

@[expose] public section

open Filter Topology
open QED.WickModel (Params Contraction)

namespace QED.Graded

/-- (Gf₂) **The family vertex as `ε → 0⁺`** (decisions D-5, D-37.5; successor of (C₄)): `V` is
the limit of (Gf₁) as the Feynman prescription `ε` tends to `0⁺`, entry by entry, for every `μ`,
with `Φ`, `D`, the selection and all other parameters of `P` fixed; the `ε` stored in `P` is
replaced. -/
def IsFamilyVertexLimit (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F)
    (Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction 1 1 κ → Grading κ → Prop)
    (K : ℕ) (p' p : Fin 4 → ℝ) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ μ i j, Tendsto (fun ε => familyVertex { P with ε := ε } Φ D Sel K p' p μ i j) (𝓝[>] 0)
    (𝓝 (V μ i j))

end QED.Graded

end
