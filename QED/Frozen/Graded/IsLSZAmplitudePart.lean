/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.ConnectedPart
public import QED.Frozen.Algebra.Bar
public import QED.Frozen.Algebra.Spinor

@[expose] public section

open Matrix Complex Filter Topology
open QED.WickModel (Params)

namespace QED.Graded

/-- (G-L₁) **The order-`e^K` LSZ amplitude of the current of the open-line fermion** (Srednicki
(41.17), (41.25); successor of (L₁)/(L₂) in predicate form, decisions D-23, D-29; ruling S8): the
spin-indexed `M s' s μ` is the iterated limit of the sandwiched order-`K` part of the connected
three-point function (G₆″). Let `m = M_open` be the open-line mass. For on-shell `p'`, `p`, spins
`s'`, `s` and index `μ`: first `ε → 0⁺` in
`(1/i) ū_{s'}(p') G^{μ,(K)}_ε(r', r) u_s(p)` at off-shell `r'`, `r` (photon momentum `r' - r`),
with the spinors (38.7), (38.12) at the limit momenta; then `(r', r) → (p', p)` through off-shell
momenta, along every approach. `G` is amputated by the free external propagators and keeps the
corrections on the external legs, so the limit exists only if the open-line flavour is on shell
through the orders it contains (unit residue (41.25)), as in (L₁). The photon leg is amputated by
the free photon propagator and keeps the vacuum-polarization insertions (D-29). The limit is unique
where it exists. -/
def IsLSZAmplitudePart (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (K : ℕ) (p' p : Fin 4 → ℝ)
    (M : Fin 2 → Fin 2 → Fin 4 → ℂ) : Prop :=
  ∀ (s' s : Fin 2) (μ : Fin 4) (η : ℝ), 0 < η → ∃ δ > 0, ∀ r' r : Fin 4 → ℝ,
    Minkowski.dot r' r' ≠ -Φ.mass Φ.openLine ^ 2 → Minkowski.dot r r ≠ -Φ.mass Φ.openLine ^ 2 →
    dist r' p' < δ → dist r p < δ →
    ∃ G : ℂ, Tendsto (fun ε : ℝ => (1 / I) *
        (Dirac.bar (Dirac.spinor (Φ.mass Φ.openLine) p' s') ⬝ᵥ
          (Matrix.of (fun α β => connectedPart { P with ε := ε } Φ D 1 1 K ![r'] ![r]
            ![r' - r] ![α] ![β] ![μ]) *ᵥ Dirac.spinor (Φ.mass Φ.openLine) p s)))
      (𝓝[>] 0) (𝓝 G) ∧ ‖G - M s' s μ‖ < η

end QED.Graded

end
