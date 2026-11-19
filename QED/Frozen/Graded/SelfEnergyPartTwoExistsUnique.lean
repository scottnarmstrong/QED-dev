-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.SelfEnergyPart
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegrable
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import QED.Provider.Graded.SelfEnergyPartTwoExistsUnique

@[expose] public section

open Filter Topology
open QED.WickModel (Params Contraction IsOnePI loopCount lineMomentum₂)

namespace QED.Graded

/-- (G-Σ₂) **The order-`e⁴` self-energy of flavour `f`: genuine integrals and covariant form**
(memo (G-Σ₂); the two-loop analogue of (Z₁), decision D-25). Let every flavour mass be at least
`m₀ > 0`, `m_γ, Λ > 0`, and the flavour coefficients satisfy the two Pauli–Villars conditions
(they act on the one-loop bubble inserted in the photon line). First, for every `ε > 0` the
integrand of every 1PI contraction of the one-fermion function with external flavour `f` and
graded order exactly `4`, at any grading, satisfies (T₉′), so every term of (G₈ₛ) at `n = 2` is a
genuine integral; these are the two-loop graphs (rainbow, crossed, bubble insertion), the one-loop
graphs with one level-`0` counterterm and the level-`1` tree. Second, there is a unique pair of
functions `A, B` of `s = p²` on the region `s > -(M_f + μ)²`, `μ = min(m_γ, Λ, 2 m₀)`, below the
lowest threshold (one photon, one Pauli–Villars photon, or a pair of the lightest flavour added
to `f`), such that `Σ^{(4)}_ε(p) → A(p²) p̸ + B(p²) M_f` as `ε → 0⁺`, entry by entry. Third, for
any functions `A, B` on `ℝ` with that limit property on the region, the function
`Σ(z) = A(-z²) z + B(-z²) M_f` of (Z₄) is differentiable at `z = -M_f` (the on-shell point lies
below the thresholds, where the form factors are real-analytic in `s`); this is the analytic input
that (G₉) at `n = 2` and (G-ex₂) need, stated in the form (G₉) quantifies over. No closed loop of
this order carries a counterterm, so the statement holds for all counterterm data. -/
theorem selfEnergyPart_two_existsUnique (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (m₀ : ℝ) (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hPV₁ : ∑ g, Φ.coeff g = 0) (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) :
    (∀ ε > 0, ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = 4 →
      ∀ C : Contraction 1 0 κ, IsOnePI C → ∀ (p : Fin 4 → ℝ) (α β : Fin 4),
        QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
          (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
            regulatedAmplitude { P with ε := ε } { Φ with openLine := f } D C g ![p] ![]
              (lineMomentum₂ C ![p] ![p] ![] ℓ) ![α] ![β] ![]) ∧
    (∃! AB : {s : ℝ // -(Φ.mass f + min (min P.mγ P.Λ) (2 * m₀)) ^ 2 < s} → ℂ × ℂ,
      ∀ (p : Fin 4 → ℝ)
        (hp : -(Φ.mass f + min (min P.mγ P.Λ) (2 * m₀)) ^ 2 < Minkowski.dot p p)
        (α β : Fin 4),
        Tendsto (fun ε : ℝ => selfEnergyPart { P with ε := ε } Φ D f 2 p α β) (𝓝[>] 0)
          (𝓝 (((AB ⟨_, hp⟩).1 • Dirac.slash p
            + ((AB ⟨_, hp⟩).2 * Φ.mass f) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β))) ∧
    ∀ A B : ℝ → ℂ,
      (∀ p : Fin 4 → ℝ,
        -(Φ.mass f + min (min P.mγ P.Λ) (2 * m₀)) ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
        Tendsto (fun ε : ℝ => selfEnergyPart { P with ε := ε } Φ D f 2 p α β) (𝓝[>] 0)
          (𝓝 ((A (Minkowski.dot p p) • Dirac.slash p
            + (B (Minkowski.dot p p) * Φ.mass f) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β))) →
      DifferentiableAt ℝ (fun z : ℝ => A (-z ^ 2) * (z : ℂ) + B (-z ^ 2) * Φ.mass f)
        (-Φ.mass f) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.Graded.selfEnergyPart_two_existsUnique
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Graded

end
-- FROZEN_ANCHOR_SUFFIX_END
