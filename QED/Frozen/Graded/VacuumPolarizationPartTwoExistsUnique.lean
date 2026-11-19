-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.VacuumPolarizationPart
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegrable
public import QED.Provider.Graded.VacuumPolarizationPartTwoExistsUnique

@[expose] public section

open Filter Topology
open QED.WickModel (Params Contraction IsOnePI loopCount lineMomentum₂)

namespace QED.Graded

/-- (G-Π₂) **The order-`e⁴` vacuum polarization: genuine integrals and transverse form** (memo
(G-Π₂); the two-loop analogue of (Z₂)). The counterterms are those of a renormalization scheme
`rep` (G₁₂) whose classes are Pauli–Villars blocks: `rep` is idempotent, the level-`0` data are
constant on its classes, and on each class the coefficients satisfy `∑ c_f = 0` and
`∑ c_f M_f² = 0` (for the lepton flavours (L₁) with `leptonRep`: each lepton with its own two
regulator fermions, D-49.4). Let every flavour mass be at least `m₀ > 0` and `m_γ, Λ > 0`. First,
for every `ε > 0` the integrand of every 1PI contraction of the two-photon function of graded
order exactly `4` satisfies (T₉′): the two-loop bubbles with an internal photon, the one-loop
bubbles with one level-`0` counterterm vertex on the loop, and the level-`1` `photonCt` tree. The
block hypotheses are what make the counterterm insertions integrable: a level-`0` counterterm on a
loop of flavour `f` contributes `c_f d_f` times an integrand that decays only like `|ℓ|⁻²`, which
the flavour sum cancels when `d` is constant on a Pauli–Villars block (finding F1 of the design
note; for the adopted ruling S2′, `leptonRep` on (L₁), they are (HM₂)'s conditions, while for the
literal per-flavour scheme `rep = id` they would force every `c_f = 0`). Second, there is
a unique function `Π` of `s = k²` on `s > -4 m₀²`, below every pair threshold, such that
`Π^{(4) μν}_ε(k) → Π(k²) (k² g^{μν} - k^μ k^ν)` as `ε → 0⁺`. -/
theorem vacuumPolarizationPart_two_existsUnique (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F) (m₀ : ℝ)
    (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0) :
    (∀ ε > 0, ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = 4 →
      ∀ C : Contraction 0 2 κ, IsOnePI C → ∀ (k : Fin 4 → ℝ) (μ ν : Fin 4),
        QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
          (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
            regulatedAmplitude { P with ε := ε } Φ D C g ![] ![k, -k]
              (lineMomentum₂ C ![] ![] ![k, -k] ℓ) ![] ![] ![μ, ν]) ∧
    ∃! Pol : {s : ℝ // -(4 * m₀ ^ 2) < s} → ℂ,
      ∀ (k : Fin 4 → ℝ) (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4),
        Tendsto (fun ε : ℝ => vacuumPolarizationPart { P with ε := ε } Φ D 2 k μ ν) (𝓝[>] 0)
          (𝓝 (Pol ⟨_, hk⟩ *
            ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ))) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Graded

end
-- FROZEN_ANCHOR_SUFFIX_END
