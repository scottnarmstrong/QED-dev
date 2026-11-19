/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.VPChain.IsVertexChainLimit
public import QED.Frozen.WickModel.IsPhotonOnShell
public import QED.Frozen.OneLoop.IsFormFactorPair
public import QED.Chain.ChainBOuter
public import QED.Algebra.SandwichReductionMirror

/-!
# The fixed-regulator links of the set (b) headline

Helper level, Phase 5 Stage 1a (decisions D-52, D-53). The proof of the headline (HC₃)
`QED.VPChain.isFormFactorPair_vertexChain_two_pauli_limit` follows the D-37 order: everything at
fixed regulators and counterterms is collected in one proposition, the **fixed link**, and the
regulator limits are then taken on the explicit set (b) functional `QED.Chain.ChainB.chainReg`
(`QED/ChainProof/HCAssembly.lean`). This file states the links; none of them is proved here.

## Objects

* `chainFlavors P`: T1's flavours `⟨![m, M₁, M₂], ![1, c₁, c₂], 0⟩` read off the parameters, the
  flavour data of (HC₃).
* `chainRegMass m m_γ Λ M₁ M₂ = chainReg (m_γ/m) (Λ/m) (M₁/m) (M₂/m)`: the explicit set (b)
  functional in units of the electron mass.
* `ChainFixedLink`: at fixed admissible regulators and a photon counterterm with (Z₈), for every
  `η > 0` there is `q₀ > 0` such that at every on-shell positive-energy pair with `0 < q² < q₀`
  the chain vertex (C₃) with two insertions has an `ε → 0⁺` limit (C₄), every limit has a
  form-factor pair (G₀), and every such pair has `‖64π⁶ F₂/e⁶ - chainRegMass‖ < η`. This is the
  content of obligations O3-5 to O3-10 at fixed regulators: O3-6 (nested equals joint, `ε → 0⁺`),
  O3-7 (the four counterterm types combine to `(Π_loop - δ₃)²`), O3-8 (covariance, no `q^μ`
  term, form factors), O3-9 (`q² → 0⁺` uniformly) and O3-10 (the finite-regulator value,
  `QED.Chain.ChainB.chainModel_eq_chainReg`), together with the mass scaling `m → 1`.
* `ChainLimitLink` (O3-6 at the `ε → 0⁺` level, O3-8): the limits exist at `q² > 0` and every
  limit is little-group covariant and mirror symmetric.
* `ChainPauliLink` (O3-9 with the value): the Pauli projection of every limit tends to
  `e⁶ chainRegMass/(64π⁶)` as `q² → 0⁺`, uniformly over the pairs.

The fixed link follows from the last two (`QED.ChainProof.chainFixedLink_of_links`,
`QED/ChainProof/HCAssembly.lean`).
-/

@[expose] public section

open Complex
open scoped Real
open QED.WickModel (Params IsPhotonOnShell)
open QED.Lepton (Flavors)

namespace QED.ChainProof

/-- T1's flavours read off the parameters: the electron and its two regulator fermions, with loop
coefficients `1, c₁, c₂` and open line `0`. At the parameters of (HC₃) it is the literal
`⟨![m, M₁, M₂], ![1, c₁, c₂], 0⟩` of the headline. -/
abbrev chainFlavors (P : Params) : Flavors (Fin 3) :=
  ⟨![P.m, P.M₁, P.M₂], ![1, P.c₁, P.c₂], 0⟩

/-- The set (b) functional at finite regulators in units of the electron mass `m`:
`chainReg (m_γ/m) (Λ/m) (M₁/m) (M₂/m)` (`QED.Chain.ChainB.chainReg`, electron mass `1`). -/
noncomputable def chainRegMass (m mγ Λ M₁ M₂ : ℝ) : ℝ :=
  QED.Chain.ChainB.chainReg (mγ / m) (Λ / m) (M₁ / m) (M₂ / m)

/-- The admissible parameters of the fixed links: `m, m_γ, Λ > 0`, regulator fermions heavier
than the electron with the two Pauli–Villars conditions, `e ≠ 0`, `m_γ < Λ`, `m_γ < 2m`, and the
photon counterterm fixed by (Z₈). The counterterms `δ₁, δ₂, δ_m` are arbitrary: the chain vertex
does not read them. -/
structure ChainAdmissible (P : Params) : Prop where
  hm : 0 < P.m
  hmγ : 0 < P.mγ
  hΛ : 0 < P.Λ
  hM₁ : P.m < P.M₁
  hM₂ : P.m < P.M₂
  hPV₁ : 1 + P.c₁ + P.c₂ = 0
  hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0
  he : P.e ≠ 0
  hmγΛ : P.mγ < P.Λ
  hmγm : P.mγ < 2 * P.m
  photon : IsPhotonOnShell P hm hM₁ hM₂ hPV₁ hPV₂

/-- **The fixed link** (obligations O3-5 to O3-10 at fixed regulators, with the mass scaling):
for admissible parameters, for every `η > 0` there is `q₀ > 0` such that at every on-shell
positive-energy pair with `0 < q² < q₀` the chain vertex with two insertions has an `ε → 0⁺`
limit, every limit has a form-factor pair, and every such pair satisfies
`‖64π⁶ F₂/e⁶ - chainRegMass m m_γ Λ M₁ M₂‖ < η`. -/
def ChainFixedLink : Prop :=
  ∀ P : Params, ChainAdmissible P →
    ∀ η > 0, ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P.m ^ 2 →
      Minkowski.dot p p = -P.m ^ 2 → 0 < p' 0 → 0 < p 0 →
      0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
      (∃ V, QED.VPChain.IsVertexChainLimit 2 P (chainFlavors P) p' p V) ∧
      ∀ V, QED.VPChain.IsVertexChainLimit 2 P (chainFlavors P) p' p V →
        (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P.e P.m p' p V F) ∧
        ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P.e P.m p' p V F →
          ‖64 * (π : ℂ) ^ 6 * F.2 / (P.e : ℂ) ^ 6 -
            (chainRegMass P.m P.mγ P.Λ P.M₁ P.M₂ : ℂ)‖ < η

/-- **The limit link** (obligation O3-6 at the `ε → 0⁺` level and O3-8): for admissible
parameters and every on-shell positive-energy pair with `q² > 0`, the chain vertex with two
insertions has an `ε → 0⁺` limit, and every limit is little-group covariant and mirror
symmetric (so that it has exactly one form-factor pair,
`QED.OneLoop.existsUnique_isFormFactorPair_of_mirror`). -/
def ChainLimitLink : Prop :=
  ∀ P : Params, ChainAdmissible P →
    ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P.m ^ 2 → Minkowski.dot p p = -P.m ^ 2 →
      0 < p' 0 → 0 < p 0 → 0 < Minkowski.dot (p' - p) (p' - p) →
      (∃ V, QED.VPChain.IsVertexChainLimit 2 P (chainFlavors P) p' p V) ∧
      ∀ V, QED.VPChain.IsVertexChainLimit 2 P (chainFlavors P) p' p V →
        QED.Dirac.IsLittleGroupCovariant p' p V ∧ QED.OneLoop.IsMirrorSymmetric p' p V

/-- **The Pauli link** (obligation O3-9 with the value of O3-6, O3-7, O3-10): for admissible
parameters, the Pauli projection (G₂) of every `ε → 0⁺` limit of the chain vertex tends to
`e⁶ chainRegMass/(64π⁶)` as `q² → 0⁺`, uniformly over on-shell positive-energy pairs. -/
def ChainPauliLink : Prop :=
  ∀ P : Params, ChainAdmissible P →
    ∀ η > 0, ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P.m ^ 2 →
      Minkowski.dot p p = -P.m ^ 2 → 0 < p' 0 → 0 < p 0 →
      0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
      ∀ V, QED.VPChain.IsVertexChainLimit 2 P (chainFlavors P) p' p V →
        ‖QED.OneLoop.formFactorProj₂ P.e P.m p' p V -
          (P.e : ℂ) ^ 6 * (chainRegMass P.m P.mγ P.Λ P.M₁ P.M₂ : ℂ) / (64 * (π : ℂ) ^ 6)‖ < η

end QED.ChainProof

end
