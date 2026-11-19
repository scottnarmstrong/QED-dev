/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.VacuumPolarizationPart

@[expose] public section

open Filter Topology
open QED.WickModel (Params)

namespace QED.Graded

/-- (G₁₁) **The photon on-shell condition at order `e^{2n}`** (Srednicki (62.11), `Π(0) = 0`,
order by order; successor of (F₁₁)): at every lightlike `k` the order-`2n` vacuum polarization
(G₈ₚ), summed over all flavours with the level-`(n-1)` photon counterterm included, tends to `0` as
`ε → 0⁺`, for all `μ, ν`. Where the transverse form `Π^{(2n) μν}(k) = Π^{(2n)}(k²)
(k² g^{μν} - k^μ k^ν)` holds (theorem (G-Π₂) at `n = 2`), its value at lightlike `k` is
`-Π^{(2n)}(0) k^μ k^ν`, so the condition is `Π^{(2n)}(0) = 0`. At `n = 1` it is (F₁₁) with
`δ₃ = e² d₃ 0` (theorem (E-G₂ₚ)). -/
def IsPhotonOnShellAt (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (n : ℕ) : Prop :=
  ∀ k : Fin 4 → ℝ, Minkowski.dot k k = 0 → ∀ μ ν : Fin 4,
    Tendsto (fun ε : ℝ => vacuumPolarizationPart { P with ε := ε } Φ D n k μ ν) (𝓝[>] 0) (𝓝 0)

end QED.Graded

end
