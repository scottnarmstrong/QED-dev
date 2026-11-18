/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.OnePIFunction

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)

namespace QED.Lepton

/-- (F₁₁) **The on-shell condition for the photon with the flavours `Φ`**, the successor of (Z₈)
(62.11), `Π(0) = 0`, for the vacuum polarization summed over all flavours with the counterterm
`-δ₃` included. Stated without choosing `Π`: at every lightlike photon momentum `k`, the regulated
order-`e²` two-photon 1PI function `Π^{μν}_ε(k) = (1/i) [i Π^{μν}_ε(k)]` ((62.4), (62.12)), in the
convention of (Z₂), tends to `0` as `ε → 0⁺`, for all `μ, ν`. Where the transverse form
`Π^{μν}(k) = Π(k²) (k² g^{μν} - k^μ k^ν)` of (62.6)–(62.7) holds (the successor of (Z₂), an
obligation), its limit at lightlike `k` is `-Π(0) k^μ k^ν`, so the condition is `Π(0) = 0`. -/
def IsPhotonOnShell (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Flavors F) : Prop :=
  ∀ k : Fin 4 → ℝ, Minkowski.dot k k = 0 → ∀ μ ν : Fin 4,
    Tendsto (fun ε : ℝ => (1 / I) *
        onePIFunction₂ { P with ε := ε } Φ 0 2 2 ![] ![] ![k, -k] ![] ![] ![μ, ν])
      (𝓝[>] 0) (𝓝 0)

end QED.Lepton

end
